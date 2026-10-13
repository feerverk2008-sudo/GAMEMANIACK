// Лёгкий HTTP и WebSocket сервер: общая арена на шесть игроков.
// Позиции игроков сохраняются в world.json рядом с сервером.
'use strict';
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { EventEmitter } = require('node:events');

const ROOT = __dirname;
const PORT = Number(process.env.PORT || 3000);
// На Railway путь постоянного тома задаётся автоматически; локально сохраняем рядом с сервером.
const DATA_DIR = path.resolve(process.env.DATA_DIR || process.env.RAILWAY_VOLUME_MOUNT_PATH || ROOT);
fs.mkdirSync(DATA_DIR, { recursive: true });
const SAVE_FILE = path.join(DATA_DIR, 'world.json');
// Пять выживших играют против одного маньяка.
const MAX_PLAYERS = 6;
const MAP_W = 96, MAP_H = 64, MAP_CELLS = MAP_W * MAP_H;
const players = new Map();
const generators = Array.from({ length: 11 }, (_, i) => ({ progress: 0, broken: false, spare: i >= 8 }));
let breakCount = 0;
let activeMap = null;
let saved = { players: {}, friends: {}, props: [] };
try { saved = { ...saved, ...JSON.parse(fs.readFileSync(SAVE_FILE, 'utf8')) }; }
catch { /* При первом запуске файла ещё нет. */ }
// Общая пользовательская разметка стен хранится как номера клеток карты.
const collisionTiles = new Set(Array.isArray(saved.collisions)
  ? saved.collisions.filter(n => Number.isInteger(n) && n >= 0 && n < MAP_CELLS)
  : []);
// Поддоны и шкафы сохраняются как отдельные интерактивные объекты карты.
const placedProps = new Map((Array.isArray(saved.props) ? saved.props : [])
  .filter(p => p && Number.isInteger(p.index) && p.index >= 0 && p.index < MAP_CELLS && ['pallet', 'locker'].includes(p.type))
  .map(p => [p.index, { index: p.index, type: p.type, rot: p.rot === 1 ? 1 : 0, down: !!p.down, broken: !!p.broken, hiddenBy: p.hiddenBy || null }]));
function collisionList() { return [...collisionTiles]; }
function propList() { return [...placedProps.values()]; }
function removeProp(index) {
  const old = placedProps.get(index);
  if (old?.hiddenBy) { const hidden = players.get(old.hiddenBy); if (hidden) hidden.invisible = false; }
  placedProps.delete(index);
}
// Проверяем, помещается ли персонаж с учётом границ арены и его радиуса.
function isFreePosition(x, y, radius = 9) {
  const x0 = Math.floor((x - radius) / 32), x1 = Math.floor((x + radius) / 32);
  const y0 = Math.floor((y - radius) / 32), y1 = Math.floor((y + radius) / 32);
  if (x0 < 0 || y0 < 0 || x1 >= MAP_W || y1 >= MAP_H) return false;
  for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) {
    if (collisionTiles.has(ty * MAP_W + tx)) return false;
  }
  for (const prop of placedProps.values()) {
    if (prop.broken) continue;
    const cx = (prop.index % MAP_W) * 32 + 16, cy = Math.floor(prop.index / MAP_W) * 32 + 16;
    let hw = prop.type === 'locker' ? 10 : prop.down ? 14 : 9, hh = prop.type === 'locker' ? 13 : prop.down ? 7 : 12;
    if (prop.rot === 1) [hw, hh] = [hh, hw];
    if (Math.abs(x - cx) < hw + radius && Math.abs(y - cy) < hh + radius) return false;
  }
  return true;
}
// Ищем ближайший свободный тайл обходом соседних клеток.
function nearestFreePosition(x, y, radius = 9) {
  const sx = Math.max(0, Math.min(MAP_W - 1, Math.floor((Number.isFinite(x) ? x : MAP_W * 16) / 32)));
  const sy = Math.max(0, Math.min(MAP_H - 1, Math.floor((Number.isFinite(y) ? y : MAP_H * 16) / 32)));
  const queue = new Int32Array(MAP_CELLS), seen = new Uint8Array(MAP_CELLS);
  let head = 0, tail = 0; const start = sy * MAP_W + sx;
  queue[tail++] = start; seen[start] = 1;
  const dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];
  while (head < tail) {
    const at = queue[head++], tx = at % MAP_W, ty = Math.floor(at / MAP_W);
    const px = tx * 32 + 16, py = ty * 32 + 16;
    if (isFreePosition(px, py, radius)) return { x: px, y: py };
    for (const [dx, dy] of dirs) {
      const nx = tx + dx, ny = ty + dy;
      if (nx < 0 || ny < 0 || nx >= MAP_W || ny >= MAP_H) continue;
      const next = ny * MAP_W + nx;
      if (!seen[next]) { seen[next] = 1; queue[tail++] = next; }
    }
  }
  return null;
}
// Если вся карта случайно перекрыта, оставляем в центре площадку 3×3 тайла.
function ensurePlayableArea() {
  if (nearestFreePosition(MAP_W * 16, MAP_H * 16, 12)) return;
  const cx = Math.floor(MAP_W / 2), cy = Math.floor(MAP_H / 2);
  for (let y = cy - 1; y <= cy + 1; y++) for (let x = cx - 1; x <= cx + 1; x++) collisionTiles.delete(y * MAP_W + x);
  persist();
}
function ejectPlayersFromWalls() {
  ensurePlayableArea();
  for (const player of players.values()) {
    const radius = player.role === 'killer' ? 12 : 9;
    if (isFreePosition(player.x, player.y, radius)) continue;
    const spot = nearestFreePosition(player.x, player.y, radius);
    if (!spot) continue;
    player.x = spot.x; player.y = spot.y; player.moving = false;
    saved.players[player.nick.toLocaleLowerCase('ru')] = { x: player.x, y: player.y, hero: player.hero };
  }
}
let persistTimer = null;
function persist() {
  const data = { players: saved.players, friends: saved.friends, collisions: collisionList(), props: propList(), updatedAt: new Date().toISOString() };
  clearTimeout(persistTimer);
  persistTimer = setTimeout(() => fs.writeFile(SAVE_FILE, JSON.stringify(data, null, 2), err => { if (err) console.error('Не удалось сохранить мир:', err.message); }), 90);
}
function send(ws, data) { if (ws.readyState === 1) ws.send(JSON.stringify(data)); }
function state() { return [...players.values()].map(({ nick, hero, role, map, x, y, hp, down, carried, injured, moving, invisible, hooks, eliminated, cellEndsAt }) => ({ nick, hero, role, map, x, y, hp, down, carried, injured, moving, invisible, hooks, eliminated, cellEndsAt })); }
function broadcast() { const packet = JSON.stringify({ type: 'state', players: state(), generators }); for (const ws of wss.clients) if (ws.readyState === 1 && ws.joined) ws.send(packet); }

// Минимальный WebSocket для JSON-пакетов клиента; реализован на модулях Node.js.
class Peer extends EventEmitter {
  constructor(socket) {
    super(); this.socket = socket; this.readyState = 1; this.buffer = Buffer.alloc(0);
    socket.on('data', chunk => this.read(chunk));
    socket.on('close', () => this.finish()); socket.on('error', () => this.finish());
  }
  frame(opcode, payload) {
    const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
    let head;
    if (data.length < 126) { head = Buffer.from([0x80 | opcode, data.length]); }
    else if (data.length <= 65535) { head = Buffer.alloc(4); head[0] = 0x80 | opcode; head[1] = 126; head.writeUInt16BE(data.length, 2); }
    else { head = Buffer.alloc(10); head[0] = 0x80 | opcode; head[1] = 127; head.writeBigUInt64BE(BigInt(data.length), 2); }
    this.socket.write(Buffer.concat([head, data]));
  }
  send(text) { if (this.readyState === 1) this.frame(1, text); }
  ping() { if (this.readyState === 1) this.frame(9, Buffer.from('keepalive')); }
  read(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (this.buffer.length >= 2) {
      const a = this.buffer[0], b = this.buffer[1], opcode = a & 15, masked = (b & 128) !== 0; let len = b & 127, offset = 2;
      if (len === 126) { if (this.buffer.length < 4) return; len = this.buffer.readUInt16BE(2); offset = 4; }
      else if (len === 127) { if (this.buffer.length < 10) return; const big = this.buffer.readBigUInt64BE(2); if (big > 1048576n) { this.finish(); return; } len = Number(big); offset = 10; }
      const maskBytes = masked ? 4 : 0; if (this.buffer.length < offset + maskBytes + len) return;
      const mask = masked ? this.buffer.subarray(offset, offset + 4) : null; offset += maskBytes;
      const payload = Buffer.from(this.buffer.subarray(offset, offset + len)); this.buffer = this.buffer.subarray(offset + len);
      if (mask) for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
      if (opcode === 8) { this.finish(); return; }
      if (opcode === 9) { this.frame(10, payload); continue; }
      if (opcode === 1) this.emit('message', payload);
    }
  }
  finish() { if (this.readyState === 3) return; this.readyState = 3; this.emit('close'); this.socket.destroy(); }
}
class WebSocketServer extends EventEmitter {
  constructor(server) {
    super(); this.clients = new Set();
    server.on('upgrade', (req, socket) => {
      const key = req.headers['sec-websocket-key'];
      if (!key || req.headers.upgrade?.toLowerCase() !== 'websocket') { socket.destroy(); return; }
      const accept = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
      socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
      const peer = new Peer(socket); this.clients.add(peer);
      peer.on('close', () => this.clients.delete(peer)); this.emit('connection', peer);
    });
  }
}

const server = http.createServer((req, res) => {
  let pathname;
  try { pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); }
  catch { res.writeHead(400).end('Bad request'); return; }
  if (pathname === '/health') { res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8' }).end('{"ok":true}'); return; }
  if (pathname === '/') pathname = '/index.html';
  const file = path.resolve(ROOT, '.' + pathname);
  if (!file.startsWith(ROOT + path.sep) || !['.html', '.css', '.js', '.png'].includes(path.extname(file).toLowerCase())) { res.writeHead(404).end('Not found'); return; }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404).end('Not found'); return; }
    const types = { '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.png': 'image/png' };
    res.writeHead(200, { 'Content-Type': types[path.extname(file).toLowerCase()], 'Cache-Control': 'no-cache' }).end(data);
  });
});
const wss = new WebSocketServer(server);
wss.on('connection', ws => {
  ws.joined = false;
  ws.on('message', raw => {
    let msg;
    try { msg = JSON.parse(raw.toString()); } catch { return; }
    if (!msg || typeof msg.type !== 'string') return;
    if (msg.type === 'editor') {
      ws.editor = true;
      send(ws, { type: 'editorWelcome', tiles: collisionList(), props: propList() });
      return;
    }
    if (msg.type === 'mapSync') {
      ws.mapSync = true;
      ensurePlayableArea();
      send(ws, { type: 'collisionMap', tiles: collisionList(), props: propList() });
      return;
    }
    if (msg.type === 'restoreMap') {
      // Разрешаем вернуть копию браузера только редактору и только на пустую карту.
      if (!ws.editor || collisionTiles.size || placedProps.size) return;
      const tiles = Array.isArray(msg.tiles) ? msg.tiles.filter(n => Number.isInteger(n) && n >= 0 && n < MAP_CELLS) : [];
      const props = Array.isArray(msg.props) ? msg.props.filter(p => p && Number.isInteger(p.index) && p.index >= 0 && p.index < MAP_CELLS && ['pallet', 'locker'].includes(p.type)) : [];
      for (const index of tiles) collisionTiles.add(index);
      for (const p of props) if (!collisionTiles.has(p.index)) placedProps.set(p.index, { index: p.index, type: p.type, rot: p.rot === 1 ? 1 : 0, down: false, broken: false, hiddenBy: null });
      ejectPlayersFromWalls(); persist();
      const packet = JSON.stringify({ type: 'collisionMap', tiles: collisionList(), props: propList() });
      for (const client of wss.clients) if (client.readyState === 1 && (client.joined || client.editor || client.mapSync)) client.send(packet);
      return;
    }
    if (msg.type === 'collision') {
      if (!ws.editor && !ws.joined && !(ws.mapSync && msg.blocked === false)) return;
      const index = Number(msg.index), blocked = msg.blocked === true;
      if (!Number.isInteger(index) || index < 0 || index >= MAP_CELLS) return;
      if (blocked) { collisionTiles.add(index); removeProp(index); }
      else collisionTiles.delete(index);
      ejectPlayersFromWalls();
      persist();
      if (blocked) {
        const removed = JSON.stringify({ type: 'propEdit', index, prop: null });
        for (const client of wss.clients) if (client.readyState === 1) client.send(removed);
      }
      const packet = JSON.stringify({ type: 'collision', index, blocked });
      for (const client of wss.clients) if (client.readyState === 1) client.send(packet);
      broadcast();
      return;
    }
    if (msg.type === 'propEdit') {
      if (!ws.editor) return;
      const index = Number(msg.index);
      if (!Number.isInteger(index) || index < 0 || index >= MAP_CELLS) return;
      const prop = msg.prop && ['pallet', 'locker'].includes(msg.prop.type) && !collisionTiles.has(index)
        ? { index, type: msg.prop.type, rot: msg.prop.rot === 1 ? 1 : 0, down: false, broken: false, hiddenBy: null }
        : null;
      if (prop) placedProps.set(index, prop); else removeProp(index);
      ejectPlayersFromWalls();
      persist();
      const packet = JSON.stringify({ type: 'propEdit', index, prop });
      for (const client of wss.clients) if (client.readyState === 1) client.send(packet);
      return;
    }
    if (msg.type === 'propAction') {
      const joined = !!ws.joined, actor = joined ? ws.player : null;
      const nick = joined ? actor.nick : (ws.mapSync ? String(msg.nick || '') : '');
      const actorRole = joined ? actor.role : (ws.mapSync && msg.role === 'killer' ? 'killer' : 'survivor');
      const x = joined ? actor.x : Number(msg.x), y = joined ? actor.y : Number(msg.y);
      if (!nick || !Number.isFinite(x) || !Number.isFinite(y)) return;
      const index = Number(msg.index), prop = placedProps.get(index);
      if (!prop || Math.hypot((index % MAP_W) * 32 + 16 - x, Math.floor(index / MAP_W) * 32 + 16 - y) > 90) return;
      const action = String(msg.action || '');
      if (action === 'drop' && actorRole === 'survivor' && prop.type === 'pallet' && !prop.down && !prop.broken) prop.down = true;
      else if (action === 'break' && actorRole === 'killer' && prop.type === 'pallet' && prop.down && !prop.broken) { prop.broken = true; prop.down = false; }
      else if (action === 'hide' && actorRole === 'survivor' && prop.type === 'locker' && !prop.broken && (!prop.hiddenBy || prop.hiddenBy === nick)) {
        prop.hiddenBy = nick; if (actor) actor.invisible = true;
      } else if (action === 'leave' && actorRole === 'survivor' && prop.type === 'locker' && prop.hiddenBy === nick) {
        prop.hiddenBy = null; if (actor) actor.invisible = false;
      } else if (action === 'search' && actorRole === 'killer' && prop.type === 'locker' && prop.hiddenBy) {
        const target = players.get(prop.hiddenBy);
        if (target) { target.invisible = false; target.down = true; target.carried = false; target.hp = 0; target.moving = false; target.cellEndsAt = 0; target.x = (index % MAP_W) * 32 + 16; target.y = Math.floor(index / MAP_W) * 32 + 16; }
        prop.hiddenBy = null;
      } else return;
      persist();
      const packet = JSON.stringify({ type: 'propState', prop: { ...prop, action } });
      for (const client of wss.clients) if (client.readyState === 1 && (client.joined || client.mapSync || client.editor)) client.send(packet);
      broadcast();
      return;
    }
    if (msg.type === 'join') {
      const nick = String(msg.nick || '').trim();
      const role = msg.role === 'killer' ? 'killer' : 'survivor';
      const hero = 'survivor';
      const map = ['bunker', 'village', 'temple'].includes(msg.map) ? msg.map : 'bunker';
      if (activeMap && activeMap !== map) { send(ws, { type: 'error', message: 'В этом матче выбрана другая локация.' }); return; }
      if (!/^[\p{L}\p{N}_-]{2,16}$/u.test(nick)) { send(ws, { type: 'error', message: 'Ник должен содержать от 2 до 16 букв или цифр.' }); return; }
      if (players.size >= MAX_PLAYERS) { send(ws, { type: 'error', message: 'Матч заполнен: 5 выживших и 1 маньяк.' }); return; }
      const roleCount = [...players.values()].filter(p => p.role === role).length;
      if (role === 'killer' && roleCount >= 1) { send(ws, { type: 'error', message: 'В матче уже есть маньяк.' }); return; }
      if (role === 'survivor' && roleCount >= 5) { send(ws, { type: 'error', message: 'Все места выживших заняты.' }); return; }
      const key = nick.toLocaleLowerCase('ru');
      if ([...players.keys()].some(n => n.toLocaleLowerCase('ru') === key)) { send(ws, { type: 'error', message: 'Этот никнейм уже занят в мире.' }); return; }
      ensurePlayableArea();
      const requestedX = Number(msg.x) || MAP_W * 16, requestedY = Number(msg.y) || MAP_H * 16;
      const spawn = isFreePosition(requestedX, requestedY, role === 'killer' ? 12 : 9)
        ? { x: requestedX, y: requestedY }
        : nearestFreePosition(requestedX, requestedY, role === 'killer' ? 12 : 9);
      ws.player = { nick, hero, role, map, x: spawn.x, y: spawn.y, hp: 3, down: false, carried: false, injured: false, moving: false, invisible: false, hooks: 0, eliminated: false, cellEndsAt: 0 };
      activeMap = map;
      ws.joined = true; players.set(nick, ws.player);
      send(ws, { type: 'welcome', players: state(), generators, collisionTiles: collisionList(), props: propList() }); broadcast(); return;
    }
    if (!ws.joined) return;
    if (msg.type === 'move') {
      if (ws.player.eliminated || ws.player.down || ws.player.invisible) return;
      const x = Number(msg.x), y = Number(msg.y);
      if (!Number.isFinite(x) || !Number.isFinite(y) || Math.abs(x) > 1e7 || Math.abs(y) > 1e7) return;
      const previousX = ws.player.x, previousY = ws.player.y;
      ws.player.x = x; ws.player.y = y;
      // Здоровье и состояния берутся только с сервера; движение передаёт координаты.
      ws.player.moving = Math.hypot(x - previousX, y - previousY) > 0.5;
      if (!isFreePosition(x, y, ws.player.role === 'killer' ? 12 : 9)) {
        ejectPlayersFromWalls();
        send(ws, { type: 'position', x: ws.player.x, y: ws.player.y });
      }
      if (ws.player.role === 'killer') for (const survivor of players.values()) if (survivor.carried) { survivor.x = ws.player.x - 14; survivor.y = ws.player.y + 4; }
      saved.players[ws.player.nick.toLocaleLowerCase('ru')] = { x: ws.player.x, y: ws.player.y, hero: ws.player.hero };
      return;
    }
    if (msg.type === 'action') {
      if (ws.player.eliminated) return;
      const i = Number(msg.index);
      if (Number.isInteger(i) && i >= 0 && i < generators.length) {
        if (msg.action === 'repair' && ws.player.role === 'survivor') { generators[i].progress = Math.max(generators[i].progress, Math.min(1, Number(msg.progress) || 0)); generators[i].broken = false; }
        if (msg.action === 'break' && ws.player.role === 'killer' && breakCount < 2 && !generators[i].broken && generators[i].progress < 1) { generators[i].progress = Math.max(0, generators[i].progress - 0.25); generators[i].broken = true; breakCount++; }
      }
      if (msg.action === 'hit' && ws.player.role === 'killer') {
        const target = [...players.values()].find(p => p.nick === String(msg.target) && p.role === 'survivor');
        const now = Date.now();
        if (target && now - (ws.player.lastHitAt || 0) >= 450 && !target.invisible && !target.eliminated && Math.hypot(target.x - ws.player.x, target.y - ws.player.y) < 85 && !target.down) {
          // Попадание уменьшает серверное HP, поэтому пакет движения не может его отменить.
          ws.player.lastHitAt = now;
          target.hp = Math.max(0, Math.min(3, target.hp ?? 3) - 1);
          target.down = target.hp === 0;
          target.injured = target.hp === 1;
          if (target.down) target.moving = false;
        }
      }
      if (msg.action === 'pickup' && ws.player.role === 'killer') {
        const target = [...players.values()].find(p => p.nick === String(msg.target) && p.role === 'survivor' && p.hp <= 1 && !p.down && Math.hypot(p.x - ws.player.x, p.y - ws.player.y) < 95);
        if (target) target.carried = true;
      }
      if (msg.action === 'hook' && ws.player.role === 'killer') {
        const target = [...players.values()].find(p => p.nick === String(msg.target) && p.role === 'survivor' && p.down && !p.eliminated && Math.hypot(p.x - ws.player.x, p.y - ws.player.y) < 140);
        if (target) {
          const fromX = target.x, fromY = target.y;
          target.carried = false; target.invisible = false; target.down = true; target.hp = 0;
          target.hooks = (target.hooks || 0) + 1; target.x = 48 * 32 + 16; target.y = 32 * 32 + 16;
          target.eliminated = target.hooks >= 3; target.cellEndsAt = target.eliminated ? 0 : Date.now() + 60000;
          if (target.eliminated) target.down = false;
          const packet = JSON.stringify({ type: 'capture', nick: target.nick, fromX, fromY, x: target.x, y: target.y, hooks: target.hooks, eliminated: target.eliminated, cellEndsAt: target.cellEndsAt });
          for (const client of wss.clients) if (client.readyState === 1 && client.joined) client.send(packet);
          persist();
        }
      }
      if (msg.action === 'rescue' && ws.player.role === 'survivor') {
        const target = [...players.values()].find(p => p.nick === String(msg.target) && p.nick !== ws.player.nick && p.role === 'survivor' && p.down && !p.eliminated && (p.hooks || 0) < 3 && p.cellEndsAt > Date.now() && Math.hypot(p.x - (48 * 32 + 16), p.y - (32 * 32 + 16)) < 90);
        if (target && Math.hypot(ws.player.x - target.x, ws.player.y - target.y) < 110) {
          target.down = false; target.carried = false; target.hp = 1; target.injured = true; target.cellEndsAt = 0;
          target.x = 48 * 32 + 44; target.y = 32 * 32 + 16;
        }
      }
      broadcast(); return;
    }
    if (msg.type === 'friend') {
      const wanted = String(msg.name || '').trim();
      const match = [...players.values()].find(p => p.nick === wanted);
      if (match && match.nick !== ws.player.nick) {
        const owner = ws.player.nick.toLocaleLowerCase('ru');
        saved.friends[owner] ||= [];
        if (!saved.friends[owner].includes(match.nick)) saved.friends[owner].push(match.nick);
        persist(); send(ws, { type: 'friend', ok: true, name: match.nick });
      } else send(ws, { type: 'friend', ok: false });
    }
  });
  ws.on('close', () => {
    if (ws.joined) {
      players.delete(ws.player.nick);
      for (const prop of placedProps.values()) if (prop.hiddenBy === ws.player.nick) {
        prop.hiddenBy = null;
        const packet = JSON.stringify({ type: 'propState', prop: { ...prop, action: 'leave' } });
        for (const client of wss.clients) if (client.readyState === 1 && (client.joined || client.mapSync || client.editor)) client.send(packet);
      }
      saved.players[ws.player.nick.toLocaleLowerCase('ru')] = { x: ws.player.x, y: ws.player.y, hero: ws.player.hero };
      persist(); if (players.size === 0) activeMap = null; broadcast();
    }
  });
});
setInterval(() => {
  let expired = false;
  for (const player of players.values()) if (player.down && !player.eliminated && player.cellEndsAt && Date.now() >= player.cellEndsAt) {
    player.eliminated = true; player.down = false; player.carried = false; player.invisible = false; player.cellEndsAt = 0; expired = true;
  }
  if (expired) persist();
  broadcast();
}, 120);
// Периодический ping помогает держать WebSocket-матчи открытыми на облачном хостинге.
const keepalive = setInterval(() => { for (const peer of wss.clients) peer.ping(); }, 25000);
keepalive.unref();
server.listen(PORT, '0.0.0.0', () => console.log(`Последний сигнал: http://localhost:${PORT}`));

