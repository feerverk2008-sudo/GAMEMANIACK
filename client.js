// Клиент матча: пиксельная арена, анимации референсных персонажей и управление.
(()=>{'use strict';
const c=document.querySelector('#world'),g=c.getContext('2d'),mini=document.querySelector('#minimap'),mg=mini.getContext('2d');
const TILE=32,MW=96,MH=64,MAPS={bunker:['Подземный комплекс','#292a2b','#555250','#191a1b']};
// GitHub Pages отдаёт только файлы: WebSocket можно подключить отдельным URL при наличии сервера.
function getSocketUrl(){const custom=document.querySelector('meta[name="game-server"]')?.content.trim();if(custom)return custom.replace(/^https:/,'wss:').replace(/^http:/,'ws:');if(location.protocol==='file:'||location.hostname==='github.io'||location.hostname.endsWith('.github.io'))return '';return(location.protocol==='https:'?'wss:':'ws:')+'//'+location.host}
const SOCKET_URL=getSocketUrl();
if(!SOCKET_URL){document.querySelectorAll('[data-start="open"],[data-start="friends"]').forEach(b=>{b.disabled=true;b.title='Для онлайн-матча нужен WebSocket-сервер'});const note=document.querySelector('#serverNote');if(note)note.textContent='Автономная версия: играй с ботами. Онлайн-матчи и общая карта требуют отдельный WebSocket-сервер.'}
const survivorImg=new Image(),killerImg=new Image(),arenaImg=new Image();survivorImg.src='assets/survivors/survivor-red.png';killerImg.src='assets/killer/masked-killer.png';arenaImg.src='assets/bunker-map.png';
// Камера держит персонажа крупно в кадре: почти в 3 раза ближе к арене.
const ZOOM=2.8;
const p={x:MW*TILE/2,y:MH*TILE/2+170,nick:'',role:'survivor',hp:3,stamina:100,dir:1,moving:false,injured:false,down:false,carried:false,hooks:0,cellEndsAt:0,eliminated:false,sprint:0,invuln:0,attack:0,invisible:false,hiddenIn:null};
let role='survivor',mapId='bunker',matchMode='play',started=false,editorMode=false,editorReady=false,finishAfterSync=false,showCollision=false,ws=null,online=false,keys={},joy={x:0,y:0},others=new Map(),bots=[],last=performance.now(),toastTimer,networkAt=0,hitAt=0,pickupTime=0,rescueTime=0,rescueTarget=null,broken=0,genDone=0,matchTime=0,gameOver=false,botThinkAt=0,trailTick=0,killerBoost=0;
const gens=[],blood=[],particles=[],walls=[],CELL={x:48*TILE+16,y:32*TILE+16},gate={x:MW*TILE/2,y:2*TILE,progress:0,open:false};
// После удаления тестовой разметки карта начинается чистой. Коллизии хранит сервер,
// а localStorage оставляет редактор рабочим и без сети.
const collisionKey='last-signal-collision-v1',collisionTiles=new Set(),pendingCollisionEdits=new Map();
const propKey='last-signal-props-v1',placedProps=new Map(),pendingPropEdits=new Map();
let editorTool='wall',propRotation=0,propUseCooldown=0,propUseLatched=false,palletBreakTime=0,breakingPallet=-1;
try{const stored=JSON.parse(localStorage.getItem(collisionKey)||'[]');if(Array.isArray(stored))stored.forEach(i=>{if(Number.isInteger(i)&&i>=0&&i<MW*MH)collisionTiles.add(i)})}catch{}
try{const stored=JSON.parse(localStorage.getItem(propKey)||'[]');if(Array.isArray(stored))stored.forEach(o=>{if(o&&Number.isInteger(o.index)&&o.index>=0&&o.index<MW*MH&&['pallet','locker'].includes(o.type))placedProps.set(o.index,{index:o.index,type:o.type,rot:o.rot===1?1:0,down:!!o.down,broken:!!o.broken,hiddenBy:o.hiddenBy||null})})}catch{}
function saveCollisionLocal(){try{localStorage.setItem(collisionKey,JSON.stringify([...collisionTiles]))}catch{}}
function savePropsLocal(){try{localStorage.setItem(propKey,JSON.stringify([...placedProps.values()]))}catch{}}
function loadCollisionList(list){if(!Array.isArray(list))return;collisionTiles.clear();for(const i of list)if(Number.isInteger(i)&&i>=0&&i<MW*MH)collisionTiles.add(i);saveCollisionLocal();ejectActorsFromWalls()}
function loadPropList(list){if(!Array.isArray(list))return;placedProps.clear();for(const o of list)if(o&&Number.isInteger(o.index)&&o.index>=0&&o.index<MW*MH&&['pallet','locker'].includes(o.type))placedProps.set(o.index,{index:o.index,type:o.type,rot:o.rot===1?1:0,down:!!o.down,broken:!!o.broken,hiddenBy:o.hiddenBy||null});savePropsLocal();ejectActorsFromWalls()}
function say(s){const e=document.querySelector('#toast');e.textContent=s;e.classList.add('show');clearTimeout(toastTimer);toastTimer=setTimeout(()=>e.classList.remove('show'),2100)}
// Дым на месте захвата состоит из недорогих квадратных пикселей.
function spawnSmoke(x,y){for(let i=0;i<26;i++){const life=.9+Math.random()*1.1;particles.push({x:x+(Math.random()-.5)*18,y:y+(Math.random()-.5)*14,vx:(Math.random()-.5)*12,vy:-8-Math.random()*22,life,max:life,size:3+Math.floor(Math.random()*5)})}}
function updateParticles(dt){for(let i=particles.length-1;i>=0;i--){const a=particles[i];a.life-=dt;a.x+=a.vx*dt;a.y+=a.vy*dt;a.vy-=5*dt;if(a.life<=0)particles.splice(i,1)}}
function drawParticles(){for(const a of particles){g.globalAlpha=Math.max(0,a.life/a.max)*.58;g.fillStyle='#b7b5b2';g.fillRect(Math.round(a.x-a.size/2),Math.round(a.y-a.size/2),a.size,a.size)}g.globalAlpha=1}
// Звуки синтезируются Web Audio API: игре не нужны внешние аудиофайлы.
const audio=(()=>{
 let ctx=null,master=null,ambience=null,windGain=null,threatGain=null,noiseBuffer=null,enabled=true,active=false,threat=0,lastPressure=-1,nextPulse=0,nextRepair=0,repairCount=0,lastStep=new Map();
 const smooth=(param,value,seconds=.2)=>{if(ctx&&param)param.setTargetAtTime(value,ctx.currentTime,seconds)};
 function setup(){if(ctx)return true;const AC=window.AudioContext||window.webkitAudioContext;if(!AC)return false;ctx=new AC();master=ctx.createGain();master.gain.value=enabled?.62:0;master.connect(ctx.destination);
  ambience=ctx.createGain();ambience.gain.value=0;ambience.connect(master);windGain=ctx.createGain();windGain.gain.value=0;windGain.connect(master);threatGain=ctx.createGain();threatGain.gain.value=.001;threatGain.connect(ambience);
  // Низкие расстроенные ноты создают постоянный тревожный фон.
  [[47,'sine',.13],[63.5,'triangle',.035],[95.2,'sine',.025],[141,'triangle',.006]].forEach(([hz,type,volume])=>{const o=ctx.createOscillator(),v=ctx.createGain();o.type=type;o.frequency.value=hz;v.gain.value=volume;o.connect(v);v.connect(ambience);o.start()});
  const size=ctx.sampleRate*2;noiseBuffer=ctx.createBuffer(1,size,ctx.sampleRate);const data=noiseBuffer.getChannelData(0);for(let i=0;i<size;i++)data[i]=(Math.random()*2-1)*.55;
  const wind=ctx.createBufferSource(),filter=ctx.createBiquadFilter();wind.buffer=noiseBuffer;wind.loop=true;filter.type='lowpass';filter.frequency.value=460;wind.connect(filter);filter.connect(windGain);wind.start();return true}
 function resume(){if(!setup())return;const p=ctx.resume?.();if(p&&p.catch)p.catch(()=>{})}
 function tone(hz,duration=.12,type='sine',volume=.08,when){if(!setup())return;const t=when??ctx.currentTime,o=ctx.createOscillator(),v=ctx.createGain();o.type=type;o.frequency.setValueAtTime(hz,t);v.gain.setValueAtTime(.0001,t);v.gain.exponentialRampToValueAtTime(Math.max(.001,volume),t+.012);v.gain.exponentialRampToValueAtTime(.0001,t+duration);o.connect(v);v.connect(master);o.start(t);o.stop(t+duration+.025)}
 function noise(duration=.1,low=300,high=1200,volume=.05,when){if(!setup())return;const t=when??ctx.currentTime,source=ctx.createBufferSource(),filter=ctx.createBiquadFilter(),v=ctx.createGain();source.buffer=noiseBuffer;filter.type='bandpass';filter.Q.value=.65;filter.frequency.setValueAtTime(Math.max(50,low),t);filter.frequency.exponentialRampToValueAtTime(Math.max(50,high),t+duration);v.gain.setValueAtTime(.0001,t);v.gain.exponentialRampToValueAtTime(Math.max(.001,volume),t+.015);v.gain.exponentialRampToValueAtTime(.0001,t+duration);source.connect(filter);filter.connect(v);v.connect(master);source.start(t);source.stop(t+duration+.03)}
 function start(){resume();active=true;lastPressure=-1;smooth(ambience.gain,.14,.8);smooth(windGain.gain,.022,1);smooth(master.gain,enabled?.62:0,.1)}
 function stop(){if(!active)return;active=false;threat=0;smooth(ambience.gain,0,.8);smooth(windGain.gain,0,.8);smooth(threatGain.gain,.001,.2)}
 function toggle(){enabled=!enabled;resume();smooth(master.gain,enabled?.62:0,.08);const b=document.querySelector('#soundBtn');if(b){b.textContent=enabled?'🔊':'🔇';b.title=enabled?'Выключить звук':'Включить звук';b.setAttribute('aria-label',b.title)}return enabled}
 function step(key,killer=false,sprinting=false,level=1){if(!active||!ctx)return;const now=ctx.currentTime,interval=sprinting?.25:killer?.43:.37;if(now<(lastStep.get(key)||0))return;lastStep.set(key,now+interval);const gain=level*(killer?.8:.52);noise(.07,killer?95:190,killer?390:720,gain*.12);tone(killer?54:82,.075,'sine',gain*.09)}
 function repair(){if(!active||!ctx||ctx.currentTime<nextRepair)return;nextRepair=ctx.currentTime+.34;repairCount++;const t=ctx.currentTime;noise(.105,650,1550,.10,t);tone(repairCount%3===0?610:390,.075,'square',.026,t+.025);tone(180,.105,'triangle',.035,t+.08)}
 function swing(){if(!active)return;const t=ctx.currentTime;noise(.24,1350,170,.18,t);tone(125,.19,'sine',.055,t+.025)}
 function hit(level=1){if(!active)return;const t=ctx.currentTime;noise(.1,260,85,.14*level,t);tone(62,.16,'triangle',.12*level,t)}
 function unlockGate(){if(!active)return;const t=ctx.currentTime;[880,740,1040].forEach((hz,i)=>{tone(hz,.15,'square',.055,t+i*.19);tone(hz/2,.17,'sine',.035,t+i*.19)})}
 function complete(){if(!active)return;const t=ctx.currentTime;[523,659,784].forEach((hz,i)=>tone(hz,.28,'sine',.055,t+i*.11))}
 function setThreat(value){if(!active||!ctx)return;threat=Math.max(0,Math.min(1,value));if(Math.abs(threat-lastPressure)>.025){smooth(threatGain.gain,.001+threat*.19,.35);smooth(ambience.gain,.14+threat*.14,.55);smooth(windGain.gain,.022+threat*.055,.6);lastPressure=threat}if(threat>.08&&ctx.currentTime>=nextPulse){const t=ctx.currentTime;const force=.055+threat*.095;tone(64,.12,'sine',force,t);tone(47,.17,'sine',force*.78,t+.14);nextPulse=t+1.35-threat*.82}}
 return{start,stop,toggle,step,repair,swing,hit,unlockGate,complete,setThreat};
})();
function resize(){const d=Math.min(devicePixelRatio||1,2);c.width=innerWidth*d;c.height=innerHeight*d;g.setTransform(d,0,0,d,0,0)}addEventListener('resize',resize);resize();
function rand(x,y){let n=Math.imul(x|0,374761393)^Math.imul(y|0,668265263);n=Math.imul(n^(n>>>13),1274126177);return((n^(n>>>16))>>>0)/4294967295}
// Базовых стен и столов больше нет: заблокированы только клетки, отмеченные игроком.
function tile(tx,ty){if(tx<0||ty<0||tx>=MW||ty>=MH)return'wall';return collisionTiles.has(ty*MW+tx)?'wall':'floor'}
function editorSummary(message=''){const pallets=[...placedProps.values()].filter(o=>o.type==='pallet').length,lockers=[...placedProps.values()].filter(o=>o.type==='locker').length;const tool=editorTool==='wall'?'СТЕНА':editorTool==='pallet'?'ПОДДОН':'ШКАФ';document.querySelector('#editorStatus').textContent=`Стены ${collisionTiles.size} · поддоны ${pallets} · шкафы ${lockers} · инструмент: ${tool}${message?' · '+message:''}`}
function setEditorTool(tool){if(!['wall','pallet','locker'].includes(tool))return;editorTool=tool;document.querySelectorAll('[data-editor-tool]').forEach(b=>b.classList.toggle('selected',b.dataset.editorTool===tool));const small=document.querySelector('#placeWallButton small');if(small)small.textContent=tool==='wall'?'СТЕНА':tool==='pallet'?'ПОДДОН':'ШКАФ';editorSummary(tool==='pallet'?'R — повернуть':'ПРОБЕЛ — поставить / снять')}
function collisionAtPlayer(){
 const tx=Math.floor(p.x/TILE),ty=Math.floor(p.y/TILE);
 if(tx<0||ty<0||tx>=MW||ty>=MH){say('Вне арены стену поставить нельзя');return}
 const index=ty*MW+tx;if(placedProps.has(index)){say('Сначала убери объект с этой клетки');return}const blockedNow=!collisionTiles.has(index);
 if(blockedNow)collisionTiles.add(index);else collisionTiles.delete(index);
 saveCollisionLocal();
 if(editorMode){pendingCollisionEdits.set(index,blockedNow);if(editorReady)send({type:'collision',index,blocked:blockedNow})}
 editorSummary(blockedNow?'стена поставлена':'стена снята');
 say(blockedNow?'Невидимая стена поставлена':'Стена убрана');
}
function propAtPlayer(){const tx=Math.floor(p.x/TILE),ty=Math.floor(p.y/TILE);if(tx<0||ty<0||tx>=MW||ty>=MH){say('Вне арены объект поставить нельзя');return}const index=ty*MW+tx;if(editorTool==='wall'){collisionAtPlayer();return}if(collisionTiles.has(index)){say('Сначала убери стену с этой клетки');return}const old=placedProps.get(index);let next;if(old?.type===editorTool)next=null;else next={index,type:editorTool,rot:propRotation,down:false,broken:false,hiddenBy:null};if(next)placedProps.set(index,next);else placedProps.delete(index);savePropsLocal();pendingPropEdits.set(index,next?{type:next.type,rot:next.rot}:null);if(editorReady)send({type:'propEdit',index,prop:next?{type:next.type,rot:next.rot}:null});editorSummary(next?`${next.type==='pallet'?'поддон':'шкаф'} поставлен`:old?'объект убран':'');say(next?(next.type==='pallet'?'Поддон поставлен':'Шкаф поставлен'):'Объект убран')}
function propCenter(prop){return{x:(prop.index%MW)*TILE+16,y:Math.floor(prop.index/MW)*TILE+16}}
function applyPropEdit(index,prop){if(!Number.isInteger(index)||index<0||index>=MW*MH)return;const old=placedProps.get(index);if(!prop&&old?.hiddenBy){const hidden=old.hiddenBy;if(hidden===p.nick){p.hiddenIn=null;p.invisible=false}const actor=[...others.values(),...bots].find(q=>q.nick===hidden);if(actor)actor.invisible=false}if(prop&&['pallet','locker'].includes(prop.type))placedProps.set(index,{index,type:prop.type,rot:prop.rot===1?1:0,down:false,broken:false,hiddenBy:null});else placedProps.delete(index);const pending=pendingPropEdits.get(index);if(pending===null&&!prop||pending&&prop&&pending.type===prop.type&&pending.rot===(prop.rot===1?1:0))pendingPropEdits.delete(index);savePropsLocal();ejectActorsFromWalls();if(editorMode)editorSummary('изменения синхронизируются');if(finishAfterSync&&!pendingCollisionEdits.size&&!pendingPropEdits.size)finishEditorNow()}
function applyPropState(prop){if(!prop||!Number.isInteger(prop.index))return;const old=placedProps.get(prop.index);if(!old)return;const wasHiddenBy=old.hiddenBy;Object.assign(old,{down:!!prop.down,broken:!!prop.broken,hiddenBy:prop.hiddenBy||null});if(old.hiddenBy===p.nick){p.hiddenIn=old.index;p.invisible=true}else if(wasHiddenBy===p.nick&&p.hiddenIn===old.index){p.hiddenIn=null;p.invisible=false}if(prop.action==='search'&&wasHiddenBy){const victim=[...others.values(),...bots].find(q=>q.nick===wasHiddenBy);if(victim){victim.invisible=false;victim.down=true;victim.carried=false;victim.hp=0;victim.moving=false}if(wasHiddenBy===p.nick){p.hiddenIn=null;p.invisible=false;p.hp=0;p.down=true}}savePropsLocal();ejectActorsFromWalls()}
function setPropState(prop,change){const local=placedProps.get(prop.index);if(!local)return;const actor=p.nick;switch(change.action){case'drop':local.down=true;break;case'break':local.broken=true;local.down=false;break;case'hide':local.hiddenBy=actor;p.hiddenIn=local.index;p.invisible=true;break;case'leave':local.hiddenBy=null;p.hiddenIn=null;p.invisible=false;break;case'search':{const found=local.hiddenBy,target=[...others.values(),...bots].find(q=>q.nick===found);if(target){target.down=true;target.hp=0;target.invisible=false;target.carried=false;target.moving=false}if(found===p.nick){p.down=true;p.hp=0;p.invisible=false;p.hiddenIn=null}local.hiddenBy=null;break}}
 savePropsLocal();if(ws?.readyState===1)send({type:'propAction',index:prop.index,action:change.action,nick:actor,role,x:p.x,y:p.y});ejectActorsFromWalls()}
function applyRemoteCollision(index,blocked){
 if(!Number.isInteger(index)||index<0||index>=MW*MH)return;
 if(blocked)collisionTiles.add(index);else collisionTiles.delete(index);
 if(pendingCollisionEdits.get(index)===blocked)pendingCollisionEdits.delete(index);
 saveCollisionLocal();ejectActorsFromWalls();
 const status=document.querySelector('#editorStatus');if(status)status.textContent=`${collisionTiles.size} клеток · изменения синхронизируются`;
 if(finishAfterSync&&!pendingCollisionEdits.size&&!pendingPropEdits.size)finishEditorNow();
}
function loadEditorTiles(list,props=[]){
 const localEdits=[...pendingCollisionEdits],localProps=[...pendingPropEdits];loadCollisionList(list);editorReady=true;
 loadPropList(props);
 for(const [index,blocked] of localEdits){if(blocked)collisionTiles.add(index);else collisionTiles.delete(index);send({type:'collision',index,blocked})}
 for(const [index,prop] of localProps){if(prop)placedProps.set(index,{index,...prop,down:false,broken:false,hiddenBy:null});else placedProps.delete(index);send({type:'propEdit',index,prop})}
 saveCollisionLocal();savePropsLocal();document.querySelector('#connection').textContent='● Редактор онлайн · общая карта';editorSummary('ПРОБЕЛ — поставить · R — повернуть');
 if(finishAfterSync&&!pendingCollisionEdits.size&&!pendingPropEdits.size)finishEditorNow();
}
function finishEditorNow(){
 editorMode=false;editorReady=false;finishAfterSync=false;started=false;showCollision=false;pendingCollisionEdits.clear();
 pendingPropEdits.clear();document.querySelector('#editorExit').classList.add('hidden');document.querySelector('#editorStatus').classList.add('hidden');document.querySelector('#editorTools').classList.add('hidden');document.querySelector('#placeWallButton').classList.add('hidden');document.querySelector('#welcome').classList.remove('hidden');
 if(ws){ws.onclose=null;ws.close();ws=null}online=false;document.querySelector('#connection').textContent='○ Локальный матч';
 say('Коллизии сохранены — выбери режим игры');
}
function finishEditor(){
 if(!editorMode)return;
 if(editorReady&&(pendingCollisionEdits.size||pendingPropEdits.size)){finishAfterSync=true;document.querySelector('#editorExit').textContent='СОХРАНЯЮ…';say('Дожидаюсь синхронизации объектов');return}
 if(ws&&(ws.readyState===0||ws.readyState===1&&!editorReady)){finishAfterSync=true;document.querySelector('#editorExit').textContent='СОХРАНЯЮ…';say('Подключаю общую карту — сейчас сохраню разметку');return}
 finishEditorNow();
}
function build(){gens.length=0;walls.length=0;
 const pts=[[68,12],[70,25],[64,50],[31,10],[30,19],[18,32],[34,47],[56,38],[28,51],[82,29],[54,16]];
 pts.forEach((q,i)=>gens.push({x:q[0]*TILE+16,y:q[1]*TILE+16,progress:0,broken:false,spare:i>=8}));
}
function clamp(n,a,b){return Math.max(a,Math.min(b,n))}
// Проверка коллизии не зависит от режима редактора — редактор только разрешает ходить сквозь стены.
function touchesProp(x,y,r=9){for(const prop of placedProps.values()){if(prop.broken)continue;const center=propCenter(prop),dx=Math.abs(x-center.x),dy=Math.abs(y-center.y);let halfW=prop.type==='locker'?10:prop.down?14:9,halfH=prop.type==='locker'?13:prop.down?7:12;if(prop.rot===1)[halfW,halfH]=[halfH,halfW];if(dx<halfW+r&&dy<halfH+r)return true}return false}
function touchesWall(x,y,r=9){const x0=Math.floor((x-r)/TILE),x1=Math.floor((x+r)/TILE),y0=Math.floor((y-r)/TILE),y1=Math.floor((y+r)/TILE);if(x0<0||y0<0||x1>=MW||y1>=MH)return true;for(let ty=y0;ty<=y1;ty++)for(let tx=x0;tx<=x1;tx++)if(tile(tx,ty)==='wall')return true;return touchesProp(x,y,r)}
function blocked(x,y,r=7){return editorMode?x-r<0||y-r<0||x+r>=MW*TILE||y+r>=MH*TILE:touchesWall(x,y,r)}
// Поиск ближайшего свободного центра клетки от исходной позиции.
function nearestFreePosition(x,y,r=9){let sx=clamp(Math.floor(x/TILE),0,MW-1),sy=clamp(Math.floor(y/TILE),0,MH-1);const start=sy*MW+sx,seen=new Uint8Array(MW*MH),queue=new Int32Array(MW*MH);let head=0,tail=0;queue[tail++]=start;seen[start]=1;const dirs=[[1,0],[-1,0],[0,1],[0,-1]];while(head<tail){const at=queue[head++],tx=at%MW,ty=Math.floor(at/MW),px=tx*TILE+TILE/2,py=ty*TILE+TILE/2;if(!touchesWall(px,py,r))return{x:px,y:py};for(const [dx,dy]of dirs){const nx=tx+dx,ny=ty+dy;if(nx<0||ny<0||nx>=MW||ny>=MH)continue;const ni=ny*MW+nx;if(!seen[ni]){seen[ni]=1;queue[tail++]=ni}}}return null}
function openEmergencyArea(){const cx=Math.floor(MW/2),cy=Math.floor(MH/2);for(let y=cy-1;y<=cy+1;y++)for(let x=cx-1;x<=cx+1;x++)collisionTiles.delete(y*MW+x);saveCollisionLocal()}
// Если стена появилась под персонажем, сразу переносим его на ближайшую свободную клетку.
function ejectActorsFromWalls(){if(editorMode)return 0;let moved=0,playerMoved=false;const actors=[p,...others.values(),...bots];for(const q of actors){if(!q||!Number.isFinite(q.x)||!Number.isFinite(q.y))continue;const radius=q.role==='killer'?12:9;if(!touchesWall(q.x,q.y,radius))continue;let spot=nearestFreePosition(q.x,q.y,radius);if(!spot){openEmergencyArea();spot=nearestFreePosition(q.x,q.y,radius)}if(!spot)continue;q.x=spot.x;q.y=spot.y;q.moving=false;moved++;if(q===p)playerMoved=true}if(playerMoved){say('Ты оказался в стене — перемещён на свободную клетку');if(online&&!p.down)send({type:'move',x:p.x,y:p.y,role,nick:p.nick,hp:p.hp,down:p.down,carried:p.carried,injured:p.injured,moving:false,invisible:p.invisible})}return moved}
function move(q,dx,dy,dt,speed){const r=q.role==='killer'?12:9;let nx=q.x+dx*speed*dt,ny=q.y+dy*speed*dt;if(!blocked(nx,q.y,r))q.x=nx;if(!blocked(q.x,ny,r))q.y=ny}
// Стены высокие: проверяем лучом, есть ли прямая видимость между игроками.
function lineOfSight(a,b){const d=Math.hypot(b.x-a.x,b.y-a.y),steps=Math.ceil(d/8);for(let i=1;i<steps;i++){const t=i/steps,kind=tile(Math.floor((a.x+(b.x-a.x)*t)/TILE),Math.floor((a.y+(b.y-a.y)*t)/TILE));if(kind==='wall'||kind==='object')return false}return true}
// Боты ищут путь по свободным клеткам, чтобы не ломиться в бетон.
function findWaypoint(q,target){const sx=Math.floor(q.x/TILE),sy=Math.floor(q.y/TILE),gx=Math.floor(target.x/TILE),gy=Math.floor(target.y/TILE),total=MW*MH,start=sy*MW+sx,goal=gy*MW+gx;if(start===goal)return{x:target.x,y:target.y};const prev=new Int32Array(total);prev.fill(-2);prev[start]=-1;const queue=new Int32Array(total);let head=0,tail=0;queue[tail++]=start;let found=false;const dirs=[[1,0],[-1,0],[0,1],[0,-1]];while(head<tail){const at=queue[head++];if(at===goal){found=true;break}const x=at%MW,y=Math.floor(at/MW);for(const [dx,dy] of dirs){const nx=x+dx,ny=y+dy,ni=ny*MW+nx;if(nx<0||ny<0||nx>=MW||ny>=MH||prev[ni]!==-2||blocked(nx*TILE+16,ny*TILE+16,4))continue;prev[ni]=at;queue[tail++]=ni}}if(!found)return{x:target.x,y:target.y};let node=goal;while(prev[node]!==start&&prev[node]>=0)node=prev[node];return{x:(node%MW)*TILE+16,y:Math.floor(node/MW)*TILE+16}}
function makeBots(mode=matchMode){bots=[];if(role==='survivor'){bots.push({nick:'Маньяк-бот',role:'killer',x:48*TILE+16,y:5*TILE+16,hp:3,bot:true,invuln:0,attack:0,nextThink:0,waypoint:null});if(mode==='bots'){const spawns=[[14,17],[55,16],[13,49],[31,49]];spawns.forEach((s,i)=>bots.push({nick:'Помощник-'+(i+1),role:'survivor',x:s[0]*TILE+16,y:s[1]*TILE+16,hp:3,bot:true,invuln:0,attack:0,injured:false,down:false,carried:false,moving:false,targetGen:[3,4,5,7][i],nextThink:0,waypoint:null}))}}else{for(let i=0;i<4;i++){const spawns=[[14,17],[55,16],[13,49],[31,49]],s=spawns[i];bots.push({nick:'Выживший-'+(i+1),role:'survivor',x:s[0]*TILE+16,y:s[1]*TILE+16,hp:3,bot:true,invuln:0,attack:0,injured:false,down:false,carried:false,moving:false,targetGen:[0,1,3,6][i],nextThink:0,waypoint:null})}}}
function botBrain(dt,now){for(const b of bots){b.attack=Math.max(0,(b.attack||0)-dt);b.invuln=Math.max(0,(b.invuln||0)-dt);let target=null;
 if(b.role==='killer'){const candidates=[p,...others.values(),...bots].filter(q=>q.role==='survivor'&&!q.eliminated&&!q.invisible);target=candidates.sort((a,z)=>Math.hypot(a.x-b.x,a.y-b.y)-Math.hypot(z.x-b.x,z.y-b.y))[0]||null}
 else if(p.down&&!p.eliminated&&p.cellEndsAt>Date.now())target=CELL;
 else target=gens[b.targetGen]||gens[0];
 if(!target)continue;if(now>(b.nextThink||0)){b.waypoint=findWaypoint(b,target);b.nextThink=now+700+Math.random()*200}
 if(b.role==='killer'){const d=Math.hypot(target.x-b.x,target.y-b.y),speed=target.injured?62:39;if(d>32){const waypoint=b.waypoint||target,dx=waypoint.x-b.x,dy=waypoint.y-b.y,l=Math.hypot(dx,dy)||1;b.moving=true;move(b,dx/l,dy/l,dt,speed);b.pickupTime=0}else{b.moving=false;if(target.down){b.pickupTime=(b.pickupTime||0)+dt;if(b.pickupTime>=5){sendVictimToCell(target);b.pickupTime=0}}else if(b.attack<=0&&lineOfSight(b,target)){b.attack=.9;target.hp=Math.max(0,target.hp-1);if(target.hp===2){target.sprint=3;target.stamina=100;say('Маньяк задел тебя — рвань!')}else if(target.hp===1){target.injured=true;say('Ты хромаешь. Следы приведут маньяка.')}else{target.down=true;target.hp=0;say('Ты оглушён. Союзники могут спасти из клетки.')}}}}
 else if(target===CELL){const d=Math.hypot(CELL.x-b.x,CELL.y-b.y);if(d>38){const waypoint=b.waypoint||CELL,dx=waypoint.x-b.x,dy=waypoint.y-b.y,l=Math.hypot(dx,dy)||1;b.moving=true;move(b,dx/l,dy/l,dt,26);b.rescueTime=0}else{b.moving=false;b.rescueTime=(b.rescueTime||0)+dt;if(b.rescueTime>=3){p.down=false;p.carried=false;p.hp=1;p.injured=true;p.cellEndsAt=0;p.x=CELL.x+28;p.y=CELL.y;say(b.nick+' освободил тебя!');b.rescueTime=0}}}
 else if(!b.down&&!b.eliminated){const d=Math.hypot(target.x-b.x,target.y-b.y);if(d>34){const waypoint=b.waypoint||target,dx=waypoint.x-b.x,dy=waypoint.y-b.y,l=Math.hypot(dx,dy)||1;b.moving=true;move(b,dx/l,dy/l,dt,26)}else{b.moving=false;target.progress=clamp(target.progress+dt*.025,0,1);if(target.progress>=1&&!target.counted){target.counted=true;genDone++;say(b.nick+' запустил генератор')}}}}
}
function drawTile(tx,ty,x,y){const t=tile(tx,ty),r=rand(tx,ty);g.fillStyle=t==='floor'?'#3a3937':t==='wall'?'#202020':t==='debris'?'#494441':t==='crate'?'#3a3029':t==='pillar'?'#4e4a43':'#151515';g.fillRect(x,y,TILE,TILE);
 if(t==='floor'){g.fillStyle=r>.5?'#464441':'#343331';g.fillRect(x+1,y+1,30,30);g.fillStyle='#242322';g.fillRect(x+2,y+2,28,1);g.fillRect(x+2,y+29,28,1);g.fillRect(x+2,y+2,1,28);g.fillRect(x+29,y+2,1,28);if(r>.83){g.fillStyle='#66605a';g.fillRect(x+6,y+8,8,2);g.fillRect(x+17,y+20,10,2)}if(r<.07){g.fillStyle='#50201d';g.fillRect(x+9,y+18,8,4);g.fillRect(x+13,y+15,4,11)}if(r>.96){g.fillStyle='#9c342b';g.fillRect(x+2,y+2,3,3)}}
 if(t==='wall'){g.fillStyle='#101112';g.fillRect(x,y-19,TILE,51);g.fillStyle='#55514e';g.fillRect(x,y-18,TILE,4);g.fillStyle='#393837';g.fillRect(x+2,y-14,28,40);g.fillStyle='#4a4642';g.fillRect(x+3,y-13,25,2);g.fillStyle='#252525';g.fillRect(x+5,y-7,22,2);g.fillStyle='#625a52';g.fillRect(x+2,y+26,28,4);g.fillStyle='#171819';g.fillRect(x,y+30,32,4);if(r>.72){g.fillStyle='#786757';g.fillRect(x+7,y+4,2,2);g.fillRect(x+24,y+19,3,2)}if(r<.08){g.fillStyle='#b1322b';g.fillRect(x+5,y-14,3,3)}}
 if(t==='debris'){g.fillStyle='#171819';g.fillRect(x+4,y+24,24,5);g.fillStyle='#77716a';g.fillRect(x+5,y+11,13,12);g.fillStyle='#aca196';g.fillRect(x+8,y+8,11,12);g.fillStyle='#4e4b47';g.fillRect(x+18,y+17,9,9);g.fillStyle='#d34a41';g.fillRect(x+11,y+12,3,2)}
 if(t==='crate'){g.fillStyle='#171515';g.fillRect(x+4,y+25,25,4);g.fillStyle='#60452f';g.fillRect(x+5,y+9,22,17);g.fillStyle='#9a714b';g.fillRect(x+7,y+11,18,13);g.fillStyle='#443326';g.fillRect(x+8,y+12,3,11);g.fillRect(x+20,y+12,3,11);g.fillStyle='#bc9061';g.fillRect(x+12,y+16,7,2)}
 if(t==='pillar'){g.fillStyle='#101112';g.fillRect(x+3,y+25,27,5);g.fillStyle='#77716a';g.fillRect(x+6,y+2,20,24);g.fillStyle='#4c4b48';g.fillRect(x+9,y+4,14,20);g.fillStyle='#aba091';g.fillRect(x+5,y+1,22,4);g.fillStyle='#d4c6ad';g.fillRect(x+11,y+6,2,14)}
}
function drawGenerator(o,now){const x=o.x,y=o.y,pulse=.5+Math.sin(now/110)*.5;g.fillStyle='#100b0b';g.fillRect(x-22,y-7,44,24);g.fillStyle='#8d2528';g.fillRect(x-19,y-18,38,31);g.fillStyle='#d4433d';g.fillRect(x-16,y-23,32,28);g.fillStyle='#f06b50';g.fillRect(x-13,y-22,7,3);g.fillRect(x+8,y-22,6,3);g.fillStyle='#692426';g.fillRect(x-12,y-17,24,16);g.fillStyle='#e35042';g.fillRect(x-9,y-14,18,12);g.fillStyle='#ffcc78';g.fillRect(x-4,y-12,8,8);g.fillStyle='#fff1b0';g.fillRect(x-2,y-10,4,4);g.fillStyle='#171617';g.fillRect(x-21,y+13,42,5);g.fillStyle='#9c8d81';g.fillRect(x-17,y+15,7,6);g.fillRect(x+10,y+15,7,6);g.fillStyle='#ffd17a';g.fillRect(x-8,y-25,16,3);g.fillStyle='#171617';g.fillRect(x-9,y-33,18,6);g.fillStyle=o.broken?'#7c7771':o.progress>=1?'#87d889':`rgb(255,${Math.floor(76+100*pulse)},${Math.floor(52+80*pulse)})`;g.fillRect(x-6,y-32,12,4);g.fillStyle='#e9d5bc';g.fillRect(x-15,y-12,3,2);g.fillRect(x+12,y-12,3,2);g.fillStyle='#302826';for(let i=0;i<3;i++)g.fillRect(x-11+i*10,y+3,5,2);if(o.progress<1){g.fillStyle='#211918';g.fillRect(x-21,y-40,42,4);g.fillStyle='#ffb957';g.fillRect(x-20,y-39,40*o.progress,2)}if(o.broken){g.fillStyle='#aaa';g.fillRect(x+18,y-34-Math.sin(now/90)*3,2,4)}else{g.fillStyle='#ffd37a';g.fillRect(x+18,y-36-Math.sin(now/80)*3,3,3);g.fillRect(x-21,y-29-Math.sin(now/100)*3,2,3)}}
function drawCell(x,y,now){g.fillStyle='#111112';g.fillRect(x-23,y-25,46,52);g.fillStyle='#655c52';g.fillRect(x-20,y-23,4,48);g.fillRect(x+16,y-23,4,48);g.fillStyle='#8e8275';g.fillRect(x-20,y-24,40,3);g.fillRect(x-20,y+22,40,3);for(let i=0;i<6;i++){g.fillStyle='#938171';g.fillRect(x-18+i*7,y-21,2,44)}g.fillStyle='#d7b57a';g.fillRect(x-2,y-29,4,4);if(Math.floor(now/350)%2){g.fillStyle='#ed6054';g.fillRect(x-2,y-29,4,4)}const captive=[p,...others.values(),...bots].find(q=>q.down&&!q.eliminated&&Math.hypot(q.x-x,q.y-y)<75&&q.cellEndsAt);if(captive){g.fillStyle='#f2d7ba';g.font='9px Manrope';g.textAlign='center';g.fillText(Math.max(0,Math.ceil((captive.cellEndsAt-Date.now())/1000))+' СЕК',x,y-34)}}
function drawPlacedProp(prop,now){const at=propCenter(prop),x=at.x,y=at.y;if(prop.type==='locker'){g.fillStyle='#0d0d0e';g.fillRect(x-12,y-15,24,32);g.fillStyle='#625c56';g.fillRect(x-10,y-14,20,28);g.fillStyle='#302c2a';g.fillRect(x-7,y-11,14,21);g.fillStyle='#887c6e';g.fillRect(x-9,y-13,18,2);g.fillRect(x-9,y+9,18,2);g.fillStyle='#d3ad69';g.fillRect(x+5,y-2,2,4);if(prop.hiddenBy){g.fillStyle='#e15c4e';g.fillRect(x-2,y-18,4,2)}}else if(!prop.broken){g.save();g.translate(x,y);if(prop.rot===1)g.rotate(Math.PI/2);g.fillStyle='#141111';g.fillRect(prop.down?-17:-10,prop.down?-6:-15,prop.down?34:20,prop.down?12:30);g.fillStyle='#70462f';g.fillRect(prop.down?-16:-9,prop.down?-5:-14,prop.down?32:18,prop.down?9:27);g.fillStyle='#a4774c';for(let i=0;i<4;i++){if(prop.down)g.fillRect(-13+i*8,-4,3,7);else g.fillRect(-7,-11+i*7,14,3)}g.fillStyle='#453024';if(!prop.down)g.fillRect(-1,-13,2,25);g.restore()}if(editorMode){g.strokeStyle=prop.type==='locker'?'#73d7df':'#e2b365';g.lineWidth=1;g.strokeRect(x-17,y-18,34,36)}}
function drawActor(q,isKiller=false,now=0){if(q.invisible||q.eliminated)return;const img=isKiller?killerImg:survivorImg,walking=!!q.moving,down=q.down||q.carried;let w=isKiller?36:29,h=isKiller?62:48;const bob=down?0:(walking?Math.sin(now/95)*1.3:Math.sin(now/390)*.7),x=q.x,y=q.y;
 g.fillStyle='#08080788';g.beginPath();g.ellipse(x,y+6,7,2.5,0,0,Math.PI*2);g.fill();g.save();g.translate(x,y+bob);if(walking&&!down){g.rotate(Math.sin(now/90)*.035*(q.dir||1));const step=Math.abs(Math.sin(now/90))*.025;g.scale(1+step,1-step)}
 if(down){g.rotate(isKiller?0:-Math.PI/2);w=down?34:w;h=down?17:h}
 if(q.carried&&!isKiller){g.rotate(Math.PI/2);w=29;h=17}
 if(isKiller&&q.attack>0){g.rotate(-Math.sin(q.attack*12)*.22)}
 if(img.complete&&img.naturalWidth){g.imageSmoothingEnabled=false;const iw=img.naturalWidth,ih=img.naturalHeight,scale=Math.min(w/iw,h/ih);g.drawImage(img,-iw*scale/2,-ih*scale+8,iw*scale,ih*scale)}else{g.fillStyle=isKiller?'#34302f':'#a8504a';g.fillRect(-11,-28,22,34)}
 g.globalAlpha=1;g.restore();if(q.injured&&!down){g.fillStyle='#aa3938';g.fillRect(x-17,y+19,3,2);g.fillRect(x+13,y+22,3,2)}if(q.nick){g.font='10px Manrope';g.textAlign='center';g.fillStyle='#f5eee5';g.fillText(q.nick,x,y-(isKiller?56:45))}
}
function draw(now){const w=innerWidth,h=innerHeight,d=Math.min(devicePixelRatio||1,2),actors=[...others.values(),...bots],watchers=actors.filter(q=>q.role==='survivor'&&!q.eliminated&&!q.down),camera=p.eliminated?(watchers[0]||actors.find(q=>!q.eliminated)||p):p;g.setTransform(d,0,0,d,0,0);g.clearRect(0,0,w,h);g.setTransform(d*ZOOM,0,0,d*ZOOM,d*(w/2-camera.x*ZOOM),d*(h/2-camera.y*ZOOM));const ox=0,oy=0;
 // Карта пользователя используется напрямую как подложка всей арены.
 if(arenaImg.complete&&arenaImg.naturalWidth)g.drawImage(arenaImg,0,0,MW*TILE,MH*TILE);else{for(let ty=0;ty<MH;ty++)for(let tx=0;tx<MW;tx++)drawTile(tx,ty,tx*TILE,ty*TILE)}
 // F3 временно подсвечивает клетки коллизий, чтобы сверить проходы с картой.
 if(showCollision||editorMode){
  const cx0=Math.max(0,Math.floor((p.x-innerWidth/(2*ZOOM))/TILE)),cx1=Math.min(MW-1,Math.ceil((p.x+innerWidth/(2*ZOOM))/TILE));
  const cy0=Math.max(0,Math.floor((p.y-innerHeight/(2*ZOOM))/TILE)),cy1=Math.min(MH-1,Math.ceil((p.y+innerHeight/(2*ZOOM))/TILE));
  for(let ty=cy0;ty<=cy1;ty++)for(let tx=cx0;tx<=cx1;tx++){
   const kind=tile(tx,ty);
   if(kind==='wall'){g.fillStyle='rgba(255,35,45,.48)';g.fillRect(tx*TILE,ty*TILE,TILE,TILE)}
  }
 }
 if(editorMode){const tx=Math.floor(p.x/TILE),ty=Math.floor(p.y/TILE),placed=collisionTiles.has(ty*MW+tx);g.fillStyle=placed?'rgba(255,190,70,.22)':'rgba(255,255,255,.12)';g.fillRect(tx*TILE,ty*TILE,TILE,TILE);g.lineWidth=2;g.strokeStyle=placed?'#ffd06c':'#fff5d6';g.strokeRect(tx*TILE+1,ty*TILE+1,TILE-2,TILE-2)}
 // Периметр ограниченной карты: за оградой туман и непроглядная темнота.
 g.fillStyle='#0b0909';g.fillRect(0,0,MW*TILE,2*TILE);g.fillRect(0,0,2*TILE,MH*TILE);g.fillRect((MW-2)*TILE,0,2*TILE,MH*TILE);g.fillRect(0,(MH-2)*TILE,MW*TILE,2*TILE);
 gens.forEach(o=>drawGenerator({...o,x:o.x+ox,y:o.y+oy},now));drawCell(CELL.x+ox,CELL.y+oy,now);for(const prop of placedProps.values())drawPlacedProp(prop,now);
 const gateY=2*TILE+oy;g.fillStyle=gate.open?'#a8c78a':'#6c3b35';g.fillRect(MW*TILE/2-48+ox,gateY-8,96,16);g.fillRect(MW*TILE/2-48+ox,(MH-3)*TILE+oy-8,96,16);g.fillStyle='#d7b57a';g.fillRect(MW*TILE/2-38+ox,gateY-4,76*gate.progress,8);g.fillRect(MW*TILE/2-38+ox,(MH-3)*TILE+oy-4,76*gate.progress,8);g.fillStyle='#ddd2bd';g.font='9px Manrope';g.textAlign='center';g.fillText(gate.open?'ВОРОТА ОТКРЫТЫ':genDone>=8?'E — ДЕШИФРОВАТЬ ПУЛЬТ':'НУЖНО 8 ГЕНЕРАТОРОВ',MW*TILE/2+ox,gateY-15);
 blood.forEach(b=>{g.globalAlpha=b.life/.75;g.fillStyle='#a5252b';g.fillRect(b.x+ox-2,b.y+oy-1,4,3);g.globalAlpha=1});drawParticles();
 const ordered=[...others.values(),...bots].sort((a,b)=>a.y-b.y);ordered.filter(q=>!q.eliminated&&q.role!=='killer'&&lineOfSight(camera,q)).forEach(q=>drawActor({...q,x:q.x+ox,y:q.y+oy},false,now));
 if(role==='killer')drawActor({...p,x:p.x+ox,y:p.y+oy},true,now);else drawActor({...p,x:p.x+ox,y:p.y+oy},false,now);
 ordered.filter(q=>!q.eliminated&&q.role==='killer'&&lineOfSight(camera,q)).forEach(q=>drawActor({...q,x:q.x+ox,y:q.y+oy},true,now));
 // Затемнение с безопасной зоной вокруг игрока для хоррор-атмосферы.
 g.setTransform(d,0,0,d,0,0);const night=.52+Math.sin(matchTime/38)*.15;if(night>.35){const rad=g.createRadialGradient(w/2,h/2,80,w/2,h/2,role==='killer'?520:400);rad.addColorStop(0,`rgba(8,9,12,${night*.16})`);rad.addColorStop(1,`rgba(8,9,12,${night})`);g.fillStyle=rad;g.fillRect(0,0,w,h)}
 drawMini();}
function drawMini(){mg.fillStyle='#120f10';mg.fillRect(0,0,120,120);const mapW=120,mapH=80,top=20,sx=mapW/MW,sy=mapH/MH;if(arenaImg.complete&&arenaImg.naturalWidth)mg.drawImage(arenaImg,0,top,mapW,mapH);else{mg.fillStyle='#454647';mg.fillRect(0,top,mapW,mapH)}gens.forEach(o=>{mg.fillStyle=o.progress>=1?'#8dd687':o.broken?'#d8544a':'#ef5149';mg.fillRect(o.x/TILE*sx-1,o.y/TILE*sy+top-1,3,3)});const actors=[...others.values(),...bots],focus=p.eliminated?(actors.find(q=>q.role==='survivor'&&!q.down&&!q.eliminated)||actors.find(q=>!q.eliminated)||p):p;mg.fillStyle='#fff';mg.fillRect(focus.x/TILE*sx-2,focus.y/TILE*sy+top-2,4,4);for(const q of actors)if(!q.invisible&&!q.eliminated){mg.fillStyle=q.role==='killer'?'#ff514c':'#7bd0c3';mg.fillRect(q.x/TILE*sx-2,q.y/TILE*sy+top-2,4,4)}}
function nearest(arr,dmax,filter=()=>true){let best=null,dist=dmax;for(const q of arr){const d=Math.hypot(q.x-p.x,q.y-p.y);if(d<dist&&filter(q)){best=q;dist=d}}return best}
function nearestProp(dmax,filter=()=>true){let best=null,dist=dmax;for(const prop of placedProps.values()){const at=propCenter(prop),d=Math.hypot(at.x-p.x,at.y-p.y);if(d<dist&&filter(prop)){best=prop;dist=d}}return best}
function usePlaceable(step){if(propUseLatched)return true;if(p.hiddenIn!==null){const locker=placedProps.get(p.hiddenIn);if(locker)setPropState(locker,{action:'leave'});p.hiddenIn=null;p.invisible=false;propUseLatched=true;say('Ты вышел из шкафа');return true}
 const prop=nearestProp(58);if(!prop)return false;const at=propCenter(prop);
 if(prop.type==='locker'&&!prop.broken){if(role==='survivor'){if(prop.hiddenBy&&prop.hiddenBy!==p.nick){say('В шкафу уже кто-то прячется');propUseLatched=true;return true}setPropState(prop,{action:'hide'});propUseLatched=true;say('Ты спрятался в шкафу');return true}
  if(role==='killer'&&prop.hiddenBy){setPropState(prop,{action:'search'});propUseLatched=true;audio.hit(.75);say('Маньяк обыскал шкаф!');return true}}
 if(prop.type==='pallet'&&!prop.broken){if(role==='survivor'&&!prop.down){const hunter=nearest([...others.values(),...bots],155,q=>q.role==='killer');if(!hunter){say('Поддон можно опрокинуть, когда маньяк рядом');propUseLatched=true;return true}setPropState(prop,{action:'drop'});propUseLatched=true;audio.hit(.55);say('Поддон опрокинут — путь перекрыт!');return true}
  if(role==='killer'&&prop.down){if(breakingPallet!==prop.index){breakingPallet=prop.index;palletBreakTime=0}palletBreakTime+=step;document.querySelector('#pickup').classList.remove('hidden');document.querySelector('#pickup span').textContent='ЛОМАЮ ПОДДОН';document.querySelector('#pickupBar').style.width=Math.min(100,palletBreakTime/1.35*100)+'%';if(palletBreakTime>=1.35){setPropState(prop,{action:'break'});breakingPallet=-1;palletBreakTime=0;document.querySelector('#pickup').classList.add('hidden');audio.hit(1.1);say('Поддон сломан')}return true}}
 return false}
function sendVictimToCell(target){const fromX=target.x,fromY=target.y;if(!target.bot&&online&&ws?.readyState===1){send({type:'action',action:'hook',target:target.nick});return}spawnSmoke(fromX,fromY);target.x=CELL.x;target.y=CELL.y;target.down=true;target.carried=false;target.invisible=false;target.moving=false;target.hp=0;target.hooks=(target.hooks||0)+1;target.eliminated=target.hooks>=3;target.cellEndsAt=target.eliminated?0:Date.now()+60000;if(target.eliminated)target.down=false;say(target.eliminated?'Жертва выбыла':'Жертва появилась в клетке · 60 секунд на спасение')}
function interact(step=.6){
 if(!started||gameOver||editorMode)return;
 if(p.eliminated)return;
 if(p.down){rescueTime=0;rescueTarget=null;return}
 if(usePlaceable(step))return;
 if(role==='killer'){const target=nearest([...others.values(),...bots],52,q=>q.role==='survivor'&&q.down&&!q.carried&&!q.eliminated&&lineOfSight(p,q));if(target){pickupTime+=step;document.querySelector('#pickup').classList.remove('hidden');document.querySelector('#pickup span').textContent='ПЕРЕНОШУ В КЛЕТКУ';document.querySelector('#pickupBar').style.width=Math.min(100,pickupTime/5*100)+'%';if(pickupTime>=5){sendVictimToCell(target);pickupTime=0;document.querySelector('#pickup').classList.add('hidden')}return}else{pickupTime=0;document.querySelector('#pickup').classList.add('hidden')}}
 const gen=nearest(gens,70,q=>q.progress<1);if(gen){if(role==='killer'){if(broken<2&&!gen.broken){gen.broken=true;gen.progress=Math.max(0,gen.progress-.25);broken++;audio.hit(.55);say('Генератор повреждён · '+broken+'/2');send({type:'action',action:'break',index:gens.indexOf(gen)})}return}gen.broken=false;gen.progress=clamp(gen.progress+step*.025,0,1);audio.repair();if(gen.progress>=1&&!gen.counted){gen.counted=true;genDone++;audio.complete();say('Генератор запущен · '+genDone+'/8')}send({type:'action',action:'repair',index:gens.indexOf(gen),progress:gen.progress});return}
 if(Math.hypot(p.x-(MW*TILE/2),p.y-(2*TILE))<100&&genDone>=8){const wasOpen=gate.open;gate.progress=clamp(gate.progress+step*.14,0,1);gate.open=gate.progress>=1;if(!wasOpen&&gate.open)audio.unlockGate();return}
 const near=nearest([...others.values(),...bots],74,q=>q.role==='survivor'&&q.down&&!q.eliminated&&(q.hooks||0)<3&&(!q.cellEndsAt||q.cellEndsAt>Date.now())&&Math.hypot(q.x-CELL.x,q.y-CELL.y)<95);
 if(role==='survivor'&&near){if(rescueTarget!==near.nick){rescueTarget=near.nick;rescueTime=0}rescueTime+=step;document.querySelector('#pickup').classList.remove('hidden');document.querySelector('#pickup span').textContent='ОСВОБОЖДАЮ СОЮЗНИКА';document.querySelector('#pickupBar').style.width=Math.min(100,rescueTime/3*100)+'%';if(rescueTime>=3){near.down=false;near.carried=false;near.hp=1;near.injured=true;near.cellEndsAt=0;if(!near.bot)send({type:'action',action:'rescue',target:near.nick});rescueTime=0;rescueTarget=null;document.querySelector('#pickup').classList.add('hidden');say('Союзник освобождён из клетки')}return}else{rescueTime=0;rescueTarget=null}
}
function attack(){if(!started||gameOver||p.eliminated||p.down||p.invisible||p.attack>0)return;p.attack=.45;if(role==='killer'){audio.swing();const q=nearest([...others.values(),...bots],52,x=>x.role==='survivor'&&!x.invisible&&!x.eliminated&&!x.down&&!x.carried&&x.invuln<=0&&lineOfSight(p,x));if(q){audio.hit();q.hp=(q.hp??3)-1;q.injured=q.hp<=1;q.invuln=1.1;if(q.hp<=0){q.down=true;say('Жертва оглушена · союзники могут спасти из клетки')}else if(q.hp===2){q.sprint=3;say('Попадание! Жертва рванула вперёд')}else say('Жертва хромает · кровавый след виден');if(!q.bot)send({type:'action',action:'hit',target:q.nick,hp:q.hp,down:q.down})}else say('Удар в пустоту')}else say('У тебя нет оружия')}
function burst(){if(role!=='survivor'||p.stamina<25||p.down||p.eliminated||p.invisible)return;p.sprint=2.5;p.stamina-=25;say('Рывок!')}
let interactClock=0;
function tick(dt,now){
 if(!started||gameOver){if(gameOver)audio.stop();return}
 matchTime+=dt;if(p.down&&p.cellEndsAt&&Date.now()>=p.cellEndsAt){p.down=false;p.eliminated=true;p.carried=false;p.invisible=false;p.cellEndsAt=0;say('Время спасения вышло · наблюдай за матчем')}
 const hpBefore=p.hp;botBrain(dt,now);if(p.hp<hpBefore)audio.hit(.7);
 p.attack=Math.max(0,p.attack-dt);p.invuln=Math.max(0,p.invuln-dt);p.sprint=Math.max(0,p.sprint-dt);p.stamina=clamp(p.stamina+(p.sprint>0?-25:16)*dt,0,100);
 if(p.eliminated){p.moving=false;updateParticles(dt);blood.forEach(b=>b.life-=dt);while(blood.length&&blood[0].life<=0)blood.shift();document.querySelector('#healthBar').style.width='0%';document.querySelector('#healthText').textContent='ВЫБЫЛ · НАБЛЮДЕНИЕ';document.querySelector('#staminaBar').style.width=p.stamina+'%';document.querySelector('#contextHint').textContent='Ты выбыл · наблюдаешь за оставшимися';document.querySelector('#phase').textContent='◷ '+String(23+Math.floor(matchTime/90)%5).padStart(2,'0')+':'+String(Math.floor(matchTime*60)%60).padStart(2,'0');document.querySelector('#pickup').classList.add('hidden');audio.setThreat(0);return}
 if(keys.KeyE){interactClock-=dt;if(interactClock<=0){interact(dt);interactClock=.12}}else interactClock=0;
 let dx=0,dy=0;if(keys.KeyW||keys.ArrowUp)dy--;if(keys.KeyS||keys.ArrowDown)dy++;if(keys.KeyA||keys.ArrowLeft)dx--;if(keys.KeyD||keys.ArrowRight)dx++;dx+=joy.x;dy+=joy.y;const len=Math.hypot(dx,dy);p.moving=len>.08&&!p.carried&&!p.down&&!p.invisible;
 if(len){dx/=Math.max(len,1);dy/=Math.max(len,1);p.dir=dx<0?-1:1;const speed=role==='killer'?(killerBoost>0?62:36):p.injured?26:30;if(!p.carried&&!p.down&&!p.invisible)move(p,dx,dy,dt,speed+(role==='survivor'&&p.sprint>0?24:0))}
 if(p.down){p.hp=0;if(Math.random()<dt*1.3)blood.push({x:p.x+(Math.random()-.5)*30,y:p.y+(Math.random()-.5)*20,life:.75})}
 if(p.moving)audio.step('local',role==='killer',p.sprint>0,1);
 let pressure=0;if(role==='survivor'&&!p.invisible){for(const q of [...others.values(),...bots])if(q.role==='killer'){const d=Math.hypot(q.x-p.x,q.y-p.y);if(d<620){let level=Math.pow(1-d/620,1.35);if(!lineOfSight(p,q))level*=.48;pressure=Math.max(pressure,level)}}}audio.setThreat(pressure);
 for(const q of [...others.values(),...bots])if(q.moving&&!q.down&&!q.carried&&!q.invisible){const d=Math.hypot(q.x-p.x,q.y-p.y);if(d<420){const visible=lineOfSight(p,q);audio.step('actor:'+q.nick,q.role==='killer',false,(1-d/420)*.42*(visible?1:.35))}}
 if(now-trailTick>260){trailTick=now;if(role==='survivor'&&p.injured&&p.moving)blood.push({x:p.x,y:p.y,life:7});for(const q of others.values())if(q.role==='survivor'&&q.injured&&q.moving)blood.push({x:q.x,y:q.y,life:7})}
 blood.forEach(b=>b.life-=dt);while(blood.length&&blood[0].life<=0)blood.shift();updateParticles(dt);
 if(role==='killer'){if(killerBoost>0)killerBoost=Math.max(0,killerBoost-dt);if(blood.some(b=>b.life>0&&Math.hypot(b.x-p.x,b.y-p.y)<220))killerBoost=1.8}
 if(online&&ws?.readyState===1&&now-networkAt>55&&!p.down&&!p.invisible){networkAt=now;send({type:'move',x:p.x,y:p.y,role,nick:p.nick,hp:p.hp,down:p.down,carried:p.carried,injured:p.injured,moving:p.moving,invisible:p.invisible})}
 const seconds=p.cellEndsAt?Math.max(0,Math.ceil((p.cellEndsAt-Date.now())/1000)):0;document.querySelector('#healthBar').style.width=(p.down?0:p.hp/3*100)+'%';document.querySelector('#healthText').textContent=p.down?(seconds?'КЛЕТКА · '+seconds+' сек':'ОГЛУШЁН'):p.injured?'РАНЕН · следы':'3 удара';document.querySelector('#staminaBar').style.width=p.stamina+'%';document.querySelector('#phase').textContent='◷ '+String(23+Math.floor(matchTime/90)%5).padStart(2,'0')+':'+String(Math.floor(matchTime*60)%60).padStart(2,'0');document.querySelector('#objective').textContent=role==='killer'?'☠ Поломки '+broken+' / 2':'⚡ Генераторы '+genDone+' / 8';document.querySelector('#pickup').classList.toggle('hidden',pickupTime===0&&rescueTime===0&&palletBreakTime===0);const closeGen=nearest(gens,80,q=>q.progress<1),rescuable=nearest([...others.values(),...bots],74,q=>q.role==='survivor'&&q.down&&!q.eliminated&&(q.hooks||0)<3&&(!q.cellEndsAt||q.cellEndsAt>Date.now())&&Math.hypot(q.x-CELL.x,q.y-CELL.y)<95);document.querySelector('#contextHint').textContent=editorMode?'ПРОБЕЛ — ИНСТРУМЕНТ РЕДАКТОРА':p.down?'СОЮЗНИКИ МОГУТ СПАСТИ · '+seconds+' СЕК':rescuable&&role==='survivor'?'E — УДЕРЖИВАТЬ 3 СЕК · СПАСТИ СОЮЗНИКА':role==='killer'?'ПРОБЕЛ — УДАР · E — ДЕЙСТВИЕ':closeGen?'E — РЕМОНТ ГЕНЕРАТОРА':'SHIFT — РЫВОК · НАЙДИ КРАСНЫЙ ГЕНЕРАТОР';if(gate.open&&(p.y<TILE*2||p.y>(MH-4)*TILE)){gameOver=true;say(role==='survivor'?'Побег удался!':'Выживший сбежал')}
}
function send(obj){if(ws?.readyState===1)ws.send(JSON.stringify(obj))}
let frame=0;function loop(now){const dt=Math.min(.05,(now-last)/1000);last=now;tick(dt,now);if(now-frame>33){draw(now);frame=now}requestAnimationFrame(loop)}requestAnimationFrame(loop);
addEventListener('keydown',e=>{keys[e.code]=true;if(['ArrowUp','ArrowDown','ArrowLeft','ArrowRight','Space'].includes(e.code))e.preventDefault();if(e.repeat)return;if(e.code==='KeyE')interact(.6);if(e.code==='F3'){if(editorMode){say('В редакторе все поставленные клетки всегда подсвечены')}else{showCollision=!showCollision;say(showCollision?'F3: красное — коллизии':'Подсветка стен выключена')}}if(e.code==='Space'){if(editorMode)propAtPlayer();else attack()}if(e.code==='KeyR'&&editorMode&&editorTool==='pallet'){propRotation=1-propRotation;editorSummary(propRotation?'поддон повёрнут':'поддон прямо')}if(e.code==='ShiftLeft'||e.code==='ShiftRight')burst();if(e.code==='Escape')document.querySelector('#pause').classList.remove('hidden')});addEventListener('keyup',e=>{keys[e.code]=false;if(e.code==='KeyE'){propUseLatched=false;interactClock=0;rescueTime=0;rescueTarget=null;palletBreakTime=0;breakingPallet=-1;if(!pickupTime)document.querySelector('#pickup').classList.add('hidden')}});
const joyEl=document.querySelector('#joystick');joyEl.addEventListener('pointerdown',e=>{joyEl.setPointerCapture(e.pointerId);joyMove(e)});joyEl.addEventListener('pointermove',e=>{if(e.buttons)joyMove(e)});joyEl.addEventListener('pointerup',()=>{joy={x:0,y:0};document.querySelector('.stick').style.transform='translate(-50%,-50%)'});function joyMove(e){const r=joyEl.getBoundingClientRect(),x=e.clientX-r.left-r.width/2,y=e.clientY-r.top-r.height/2,l=Math.hypot(x,y),m=Math.min(1,l/42);joy={x:l?x/l*m:0,y:l?y/l*m:0};document.querySelector('.stick').style.transform=`translate(calc(-50% + ${joy.x*30}px),calc(-50% + ${joy.y*30}px))`}
 document.querySelectorAll('[data-action]').forEach(b=>{if(b.dataset.action==='interact'){b.addEventListener('pointerdown',()=>keys.KeyE=true);const release=()=>{keys.KeyE=false;propUseLatched=false;rescueTime=0;rescueTarget=null;palletBreakTime=0;breakingPallet=-1;if(!pickupTime)document.querySelector('#pickup').classList.add('hidden')};b.addEventListener('pointerup',release);b.addEventListener('pointercancel',release);b.addEventListener('pointerleave',release)}else b.addEventListener('pointerdown',()=>({sprint:burst,attack}[b.dataset.action])())});document.querySelector('#editorExit').onclick=finishEditor;document.querySelector('#placeWallButton').addEventListener('pointerdown',e=>{e.preventDefault();if(editorMode)propAtPlayer()});document.querySelectorAll('[data-editor-tool]').forEach(b=>b.onclick=()=>setEditorTool(b.dataset.editorTool));document.querySelector('#menuBtn').onclick=()=>document.querySelector('#pause').classList.remove('hidden');document.querySelector('#soundBtn').onclick=()=>audio.toggle();document.querySelectorAll('[data-close]').forEach(b=>b.onclick=()=>document.querySelector('#'+b.dataset.close).classList.add('hidden'));document.querySelector('#friendsBtn').onclick=()=>document.querySelector('#friendsPanel').classList.toggle('hidden');document.querySelector('#addFriend').onclick=()=>{const n=document.querySelector('#friendName').value.trim();send({type:'friend',name:n})};
// Захватываем касание на экранных кнопках, чтобы удержание действия не терялось при небольшом сдвиге пальца.
document.addEventListener('pointerdown',e=>{const button=e.target.closest('.touch-actions button');if(!button)return;e.preventDefault();try{button.setPointerCapture(e.pointerId)}catch{}},true);
const mobileStick=document.querySelector('#joystick');mobileStick.addEventListener('pointercancel',()=>{joy={x:0,y:0};document.querySelector('.stick').style.transform='translate(-50%,-50%)'});
document.querySelectorAll('[data-start]').forEach(b=>b.onclick=()=>{document.querySelectorAll('[data-start]').forEach(x=>x.classList.remove('mode-selected'));b.classList.add('mode-selected')});document.querySelectorAll('[data-role]').forEach(b=>b.onclick=()=>{document.querySelectorAll('[data-role]').forEach(a=>a.classList.remove('selected'));b.classList.add('selected');role=b.dataset.role});
function startMatch(mode){
 const edit=mode==='edit',n=document.querySelector('#nickname').value.trim();
 if(!edit&&!/^[\p{L}\p{N}_-]{2,16}$/u.test(n)){say('Имя: 2–16 букв или цифр');return}
  matchMode=mode;editorMode=edit;editorReady=false;finishAfterSync=false;pendingCollisionEdits.clear();pendingPropEdits.clear();
 if(edit)role='survivor';p.nick=n||(edit?'Редактор':'Игрок');p.role=role;p.x=42*TILE+16;p.y=31*TILE+16;p.hp=3;p.stamina=100;p.injured=false;p.down=false;p.carried=false;p.hooks=0;p.cellEndsAt=0;p.eliminated=false;p.invisible=false;p.hiddenIn=null;p.sprint=0;
 document.querySelector('#playerLabel').textContent=p.nick+' · '+(edit?'Настройка карты':role==='killer'?'Маньяк':'Выживший');
 document.querySelector('#roleTag').textContent=edit?'РЕДАКТОР':role==='killer'?'МАНЬЯК':'ВЫЖИВШИЙ';
 document.querySelector('#welcome').classList.add('hidden');started=true;gameOver=false;matchTime=0;build();
  const exit=document.querySelector('#editorExit'),place=document.querySelector('#placeWallButton');
  if(edit){bots=[];showCollision=true;exit.textContent='СОХРАНИТЬ И ВЫЙТИ';exit.classList.remove('hidden');place.classList.remove('hidden');document.querySelector('#editorTools').classList.remove('hidden');document.querySelector('#editorStatus').classList.remove('hidden');setEditorTool('wall');editorSummary('ПРОБЕЛ — поставить / снять');connectEditor();say('Редактор: выбери инструмент и ставь его по клеткам');return}
 audio.start();
  exit.classList.add('hidden');place.classList.add('hidden');document.querySelector('#editorTools').classList.add('hidden');document.querySelector('#editorStatus').classList.add('hidden');showCollision=false;
 document.querySelector('#connection').textContent='○ Локальный матч';
 if(mode==='play'||mode==='bots'){makeBots(mode);ejectActorsFromWalls();connectMapSync()}else{bots=[];ejectActorsFromWalls()}
 if(mode==='open'||mode==='friends'){p.nick=n;connect()}
 if(mode==='friends'){document.querySelector('#pause').classList.remove('hidden');document.querySelector('#friendsPanel').classList.remove('hidden')}
 say(mode==='open'?'Ищем открытый матч':mode==='friends'?'Комната для друзей открыта':mode==='bots'?'Тренировка с ботами':'Быстрая игра начинается');
}
document.querySelectorAll('[data-start]').forEach(b=>b.addEventListener('click',()=>startMatch(b.dataset.start)));
function connectEditor(){
 if(!SOCKET_URL){document.querySelector('#connection').textContent='○ Локально · разметка в этом браузере';return}
 try{ws=new WebSocket(SOCKET_URL)}catch{document.querySelector('#connection').textContent='○ Локальная настройка';return}
 ws.onopen=()=>ws.send(JSON.stringify({type:'editor'}));
 ws.onmessage=e=>{let m;try{m=JSON.parse(e.data)}catch{return}if(m.type==='editorWelcome')loadEditorTiles(m.tiles,m.props);else if(m.type==='collisionMap'){loadCollisionList(m.tiles);loadPropList(m.props)}else if(m.type==='collision')applyRemoteCollision(m.index,m.blocked);else if(m.type==='propEdit')applyPropEdit(m.index,m.prop);else if(m.type==='propState')applyPropState(m.prop);else if(m.type==='error')say(m.message)};
 ws.onclose=()=>{editorReady=false;if(finishAfterSync)finishEditorNow();else if(editorMode){document.querySelector('#connection').textContent='○ Локально · карта сохранена в браузере';say('Сервер недоступен — локальная разметка останется в этом браузере')}};
 ws.onerror=()=>{online=false};
}
function connectMapSync(){
 if(!SOCKET_URL)return;
 try{ws=new WebSocket(SOCKET_URL)}catch{return}
 ws.onopen=()=>{send({type:'mapSync'});document.querySelector('#connection').textContent='● Загружаю общую карту'};
 ws.onmessage=e=>{let m;try{m=JSON.parse(e.data)}catch{return}if(m.type==='collisionMap'){loadCollisionList(m.tiles);loadPropList(m.props);document.querySelector('#connection').textContent='● Общая карта · объекты синхронизированы'}else if(m.type==='collision')applyRemoteCollision(m.index,m.blocked);else if(m.type==='propEdit')applyPropEdit(m.index,m.prop);else if(m.type==='propState')applyPropState(m.prop)};
 ws.onclose=()=>{if(!online)document.querySelector('#connection').textContent='○ Локальная карта'};
 ws.onerror=()=>{};
}
function connect(){
 if(!SOCKET_URL)return;
 try{ws=new WebSocket(SOCKET_URL)}catch{return}
 ws.onopen=()=>ws.send(JSON.stringify({type:'join',nick:p.nick,role,map:mapId,x:p.x,y:p.y}));
 ws.onmessage=e=>{let m;try{m=JSON.parse(e.data)}catch{return}
  if(m.type==='collisionMap'){loadCollisionList(m.tiles);loadPropList(m.props);return}
  if(m.type==='collision'){applyRemoteCollision(m.index,m.blocked);return}
  if(m.type==='propEdit'){applyPropEdit(m.index,m.prop);return}
  if(m.type==='propState'){applyPropState(m.prop);return}
  if(m.type==='capture'){spawnSmoke(m.fromX,m.fromY);if(m.nick===p.nick){p.x=m.x;p.y=m.y;p.down=!m.eliminated;p.carried=false;p.invisible=false;p.hp=0;p.hooks=m.hooks||p.hooks;p.cellEndsAt=m.cellEndsAt||0;p.eliminated=!!m.eliminated;if(p.eliminated)say('Третья клетка · наблюдай за матчем');else say('Ты в клетке · союзники должны успеть за минуту')}else{const target=[...others.values(),...bots].find(q=>q.nick===m.nick);if(target){target.x=m.x;target.y=m.y;target.down=!m.eliminated;target.carried=false;target.invisible=false;target.hp=0;target.hooks=m.hooks||target.hooks||0;target.cellEndsAt=m.cellEndsAt||0;target.eliminated=!!m.eliminated}}return}
  if(m.type==='position'){if(Number.isFinite(m.x)&&Number.isFinite(m.y)){p.x=m.x;p.y=m.y;p.moving=false}return}
  if(m.type==='welcome'||m.type==='state'){
   if(m.collisionTiles)loadCollisionList(m.collisionTiles);if(m.props)loadPropList(m.props);
   online=true;const own=m.players.find(q=>q.nick===p.nick);
   if(own&&m.type==='welcome'){if(Number.isFinite(own.x))p.x=own.x;if(Number.isFinite(own.y))p.y=own.y;p.hooks=own.hooks||0;p.cellEndsAt=own.cellEndsAt||0;p.eliminated=!!own.eliminated}
   if(own&&m.type==='state'){const oldHp=p.hp,wasDown=p.down;p.hp=own.hp??p.hp;if(p.hp<oldHp){audio.hit(.8);if(p.hp===2){p.sprint=3;p.stamina=100;say('Попадание! Рвань!')}}p.down=!!own.down;p.carried=!!own.carried;p.injured=!!own.injured;p.invisible=!!own.invisible;if(!own.invisible)p.hiddenIn=null;p.hooks=own.hooks||0;p.cellEndsAt=own.cellEndsAt||0;p.eliminated=!!own.eliminated;if(wasDown&&!p.down&&!p.eliminated){if(Number.isFinite(own.x))p.x=own.x;if(Number.isFinite(own.y))p.y=own.y;say('Тиммейт освободил тебя!')}if(p.eliminated){p.down=false;p.invisible=false}}
   others=new Map(m.players.filter(q=>q.nick!==p.nick).map(q=>[q.nick,q]));document.querySelector('#connection').textContent='● Онлайн · '+m.players.length+'/6';document.querySelector('#players').innerHTML=m.players.map(q=>'<span class="player-chip">'+(q.role==='killer'?'☠':'✦')+' '+q.nick+'</span>').join('');
   if(m.generators){m.generators.forEach((q,i)=>{if(gens[i])Object.assign(gens[i],q)});genDone=gens.filter(q=>q.progress>=1).length;broken=gens.filter(q=>q.broken).length}
  }else if(m.type==='error'){say(m.message);started=false;document.querySelector('#welcome').classList.remove('hidden')}
  else if(m.type==='friend')document.querySelector('#friendList').textContent=m.ok?'Друг добавлен: '+m.name:'Игрок не найден по точному нику';
 };
 ws.onclose=()=>{online=false;others.clear();document.querySelector('#connection').textContent='○ Локальный матч';if(matchMode==='open'||matchMode==='friends'){makeBots('play');say('Сервер не ответил — запущены боты')}};
 ws.onerror=()=>{online=false};
}
build();
})();

