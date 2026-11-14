(function(){
'use strict';
/* Host desk (admin.html) and player page (index.html) share this script.
   The host desk keeps the tournament in this browser and publishes it to
   xtacle/state.json in the repo through the GitHub API, using a token only
   the host has. The player page only reads state.json and never writes. */
const MODE=document.documentElement.dataset.mode==='admin'?'admin':'view';
const ADMIN=MODE==='admin';
const GH={owner:'lavieboflip',repo:'brunch-league',branch:'main',path:'xtacle/state.json'};
const API='https://api.github.com/repos/'+GH.owner+'/'+GH.repo+'/contents/'+GH.path;
const KEY='xtacle-2026-state',TOKEN_KEY='xtacle-2026-token',ME_KEY='xtacle-2026-me';
const EXPECTED=18,POLL_MS=20000;
const $=s=>document.querySelector(s);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const lsGet=k=>{try{return localStorage.getItem(k)}catch(e){return null}};
const lsSet=(k,v)=>{try{v==null?localStorage.removeItem(k):localStorage.setItem(k,v)}catch(e){}};

function blank(){return {v:1,updatedAt:0,roster:'',drawMode:'random',players:[],pools:null,poolRes:{},advance:'all',bracket:null};}
function normalize(d){return Object.assign(blank(),d||{});}
function loadLocal(){try{const s=lsGet(KEY);return s?normalize(JSON.parse(s)):null}catch(e){return null}}
function saveLocal(){if(ADMIN)lsSet(KEY,JSON.stringify(state));}
let state=(ADMIN&&loadLocal())||blank();

/* ---------- tournament math ---------- */
function planPools(n){
  if(n<2)return [];
  const k=n<6?1:Math.max(2,Math.ceil(n/4-0.5));
  const base=Math.floor(n/k),extra=n%k;
  return Array.from({length:k},(_,i)=>base+(i<extra?1:0));
}
const pow2=n=>{let b=2;while(b<n)b*=2;return b};
const rrRounds=s=>s%2?s:s-1;
function planFacts(n){
  const sizes=planPools(n);
  const matches=sizes.reduce((t,s)=>t+s*(s-1)/2,0);
  const rounds=Math.max(0,...sizes.map(rrRounds));
  const tables=sizes.reduce((t,s)=>t+Math.floor(s/2),0);
  const each=[...new Set(sizes.map(s=>s-1))].sort((a,b)=>b-a);
  const B=pow2(n);
  return {sizes,matches,rounds,tables,each,B,byes:B-n,brRounds:Math.log2(B)};
}
function rr(ids){
  const a=ids.slice();if(a.length%2)a.push(null);
  const n=a.length,out=[];
  for(let r=0;r<n-1;r++){
    const ms=[];let bye=null;
    for(let i=0;i<n/2;i++){const x=a[i],y=a[n-1-i];if(x===null||y===null)bye=x===null?y:x;else ms.push([x,y]);}
    out.push({ms,bye});a.splice(1,0,a.pop());
  }
  return out;
}
const pk=(a,b)=>a<b?a+'|'+b:b+'|'+a;
const P=id=>state.players.find(p=>p.id===id)||{name:'?',coin:1};
const poolTotal=()=>state.pools?state.pools.reduce((t,p)=>t+p.length*(p.length-1)/2,0):0;
const poolDone=()=>Object.keys(state.poolRes).length;
function standings(ids){
  const S={};ids.forEach(id=>S[id]={id,w:0,l:0,gw:0,gl:0,p:0,mini:0});
  for(let i=0;i<ids.length;i++)for(let j=i+1;j<ids.length;j++){
    const a=ids[i],b=ids[j],r=state.poolRes[pk(a,b)];if(!r)continue;
    const ga=r[a],gb=r[b];S[a].p++;S[b].p++;S[a].gw+=ga;S[a].gl+=gb;S[b].gw+=gb;S[b].gl+=ga;
    if(ga>gb){S[a].w++;S[b].l++}else{S[b].w++;S[a].l++}
  }
  const groups={};ids.forEach(id=>(groups[S[id].w]=groups[S[id].w]||[]).push(id));
  Object.values(groups).forEach(g=>{if(g.length<2)return;
    for(let i=0;i<g.length;i++)for(let j=i+1;j<g.length;j++){const r=state.poolRes[pk(g[i],g[j])];if(r)S[r[g[i]]>r[g[j]]?g[i]:g[j]].mini++;}});
  return ids.map(id=>S[id]).sort((x,y)=>y.w-x.w||y.mini-x.mini||(y.gw-y.gl)-(x.gw-x.gl)||y.gw-x.gw||P(x.id).coin-P(y.id).coin);
}
function overallSeeds(){
  if(!state.pools)return [];
  const all=[];
  state.pools.forEach((ids,pi)=>standings(ids).forEach((s,pos)=>all.push(Object.assign({},s,{pos,pool:pi,pct:s.p?s.w/s.p:0,gdpm:s.p?(s.gw-s.gl)/s.p:0}))));
  return all.sort((x,y)=>x.pos-y.pos||y.pct-x.pct||y.gdpm-x.gdpm||P(x.id).coin-P(y.id).coin);
}
function seedOrder(B){let o=[1,2];while(o.length<B){const n=o.length*2;o=o.flatMap(s=>[s,n+1-s]);}return o;}
function advancingCount(){const n=state.players.length;return state.advance==='all'?n:Math.min(n,+state.advance);}
function buildBracket(){
  const seeds=overallSeeds(),A=advancingCount(),B=pow2(A);
  const slots=seedOrder(B).map(s=>s<=A?seeds[s-1].id:null);
  const seedOf={};seeds.slice(0,A).forEach((s,i)=>seedOf[s.id]=i+1);
  return {size:B,slots,seedOf,res:{}};
}
function bracketRounds(br){
  const rounds=[];let pairs=[];
  for(let m=0;m<br.size/2;m++)pairs.push([br.slots[2*m],br.slots[2*m+1]]);
  let r=0;
  while(true){
    const ms=pairs.map(([a,b],m)=>{
      const o={r,m,a,b,winner:undefined,res:null,bye:false};
      if(a===undefined||b===undefined)return o;
      if(a===null&&b===null){o.winner=null;o.bye=true;return o}
      if(a===null||b===null){o.winner=a===null?b:a;o.bye=true;return o}
      const res=br.res[r+'-'+m];
      if(res&&res.a===a&&res.b===b){o.res=res;o.winner=res.ga>res.gb?a:b;}
      return o;
    });
    rounds.push(ms);
    if(ms.length===1)break;
    const next=[];for(let i=0;i<ms.length;i+=2)next.push([ms[i].winner,ms[i+1].winner]);
    pairs=next;r++;
  }
  return rounds;
}
const roundName=(count,idx,total)=>{const left=total-idx;return left===1?'Final':left===2?'Semifinals':left===3?'Quarterfinals':'Round of '+count*2;};
const currentRound=ids=>{const rs=rr(ids);const i=rs.findIndex(rd=>rd.ms.some(([a,b])=>!state.poolRes[pk(a,b)]));return i;};

/* ---------- status pill ---------- */
const STATUS={
  local:'Saved on this device',notoken:'Not publishing · add token',pending:'Unpublished changes',saving:'Publishing…',
  published:'Published',error:'Publish failed',loading:'Loading…',live:'Live',stale:'Can’t refresh right now'};
function setStatus(s,extra){const el=$('#status');el.dataset.s=(s==='published'||s==='live')?'synced':(s==='error'||s==='stale')?'error':s;el.textContent=(STATUS[s]||s)+(extra?' · '+extra:'');}
const ago=t=>{if(!t)return '';const s=Math.round((Date.now()-t)/1000);return s<60?'just now':s<3600?Math.round(s/60)+' min ago':new Date(t).toLocaleTimeString([],{hour:'numeric',minute:'2-digit'});};

/* ---------- host: publish to GitHub ---------- */
let token=ADMIN?lsGet(TOKEN_KEY):null,sha,pubTimer=null,publishing=false,again=false,lastPub=0,pubErr='';
const ghHeaders=()=>({'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'});
const b64=s=>{const bytes=new TextEncoder().encode(s);let bin='';bytes.forEach(b=>bin+=String.fromCharCode(b));return btoa(bin);};
async function ghErr(r){
  if(r.status===401)return 'GitHub rejected the token. Paste a new one on the Publish tab.';
  if(r.status===403||r.status===404)return 'The token can’t write to '+GH.owner+'/'+GH.repo+'. It needs Contents: Read and write on that repository.';
  let m='';try{m=(await r.json()).message||''}catch(e){}
  return 'GitHub said '+r.status+(m?': '+m:'')+'.';
}
async function fetchSha(){
  const r=await fetch(API+'?ref='+GH.branch+'&t='+Date.now(),{headers:ghHeaders(),cache:'no-store'});
  if(r.status===404)return null;
  if(!r.ok)throw new Error(await ghErr(r));
  return (await r.json()).sha;
}
async function putState(retry){
  if(sha===undefined)sha=await fetchSha();
  const body={message:'Xtacle Invitational: update tournament',content:b64(JSON.stringify(state)),branch:GH.branch};
  if(sha)body.sha=sha;
  const r=await fetch(API,{method:'PUT',headers:Object.assign({'Content-Type':'application/json'},ghHeaders()),body:JSON.stringify(body)});
  if((r.status===409||r.status===422)&&retry){sha=undefined;return putState(false);}
  if(!r.ok)throw new Error(await ghErr(r));
  sha=(await r.json()).content.sha;
}
function schedulePublish(delay){
  if(!token){setStatus('notoken');return}
  setStatus('pending');clearTimeout(pubTimer);pubTimer=setTimeout(publish,delay==null?2500:delay);
}
async function publish(){
  if(!token){setStatus('notoken');return}
  if(publishing){again=true;return}
  publishing=true;clearTimeout(pubTimer);setStatus('saving');
  try{await putState(true);lastPub=Date.now();pubErr='';setStatus('published',ago(lastPub));}
  catch(e){pubErr=e.message||'Network error. Check the connection.';setStatus('error');}
  publishing=false;
  if(tab()==='publish')render();
  if(again){again=false;publish();}
}
function commit(){state.updatedAt=Date.now();saveLocal();render();schedulePublish();}
window.addEventListener('beforeunload',e=>{if(ADMIN&&(publishing||pubTimer&&$('#status').dataset.s==='pending')){e.preventDefault();e.returnValue='';}});

/* ---------- both: read the published copy ---------- */
async function fetchPublished(){
  const r=await fetch('state.json?t='+Date.now(),{cache:'no-store'});
  if(!r.ok)throw new Error('HTTP '+r.status);
  return normalize(await r.json());
}
let lastFetch=0;
async function poll(){
  try{const d=await fetchPublished();lastFetch=Date.now();
    if((d.updatedAt||0)!==(state.updatedAt||0)){state=d;render();}
    setStatus('live',state.updatedAt?'updated '+ago(state.updatedAt):'');
  }catch(e){setStatus('stale');}
}

/* ---------- host actions ---------- */
function parseRoster(t){const seen=new Set(),out=[],dups=[];
  t.split(/\n/).map(s=>s.trim()).filter(Boolean).forEach(n=>{const k=n.toLowerCase();if(seen.has(k))dups.push(n);else{seen.add(k);out.push(n)}});
  return {names:out,dups};}
function draw(){
  const {names}=parseRoster(state.roster);if(names.length<2)return;
  const players=names.map((name,i)=>({id:'p'+(i+1)+'-'+Math.random().toString(36).slice(2,6),name,coin:Math.random()}));
  const order=players.map(p=>p.id);
  if(state.drawMode==='random'){for(let i=order.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[order[i],order[j]]=[order[j],order[i]]}}
  const k=planPools(order.length).length,pools=Array.from({length:k},()=>[]);
  order.forEach((id,i)=>{const row=Math.floor(i/k),c=i%k;pools[row%2?k-1-c:c].push(id)});
  Object.assign(state,{players,pools,poolRes:{},bracket:null});
  if(state.advance!=='all'&&+state.advance>=players.length)state.advance='all';
  location.hash='pools';commit();
}
const armed=new WeakMap();
function twoStep(btn,label,fn){
  if(armed.get(btn)){armed.delete(btn);fn();return}
  armed.set(btn,true);const orig=btn.textContent;btn.textContent=label;btn.classList.add('armed');
  setTimeout(()=>{if(armed.get(btn)){armed.delete(btn);btn.textContent=orig;btn.classList.remove('armed')}},3500);
}

/* ---------- views ---------- */
const TABS=ADMIN?['setup','pools','bracket','plans','publish']:['me','pools','bracket'];
function tab(){const t=(location.hash||'').slice(1);if(TABS.includes(t))return t;return ADMIN?(state.pools?'pools':'setup'):'me';}
function render(){
  const t=tab();
  document.querySelectorAll('#tabs a').forEach(a=>{if(a.dataset.tab===t)a.setAttribute('aria-current','page');else a.removeAttribute('aria-current')});
  if(ADMIN&&t==='setup'&&document.activeElement&&document.activeElement.id==='roster'){updateSetupSide();return}
  const views={setup:viewSetup,pools:viewPools,bracket:viewBracket,plans:viewPlans,publish:viewPublish,me:viewMe};
  $('#view').innerHTML=views[t]();
}
function factsHTML(n){
  const f=planFacts(n);
  return `<div class="facts">
    <div class="fact"><b>${f.sizes.length} pools</b><span>sizes ${f.sizes.join(', ')}</span></div>
    <div class="fact"><b>${f.each.join(' or ')}</b><span>pool matches per player</span></div>
    <div class="fact"><b>${f.matches}</b><span>pool matches total</span></div>
    <div class="fact"><b>${f.rounds} rounds</b><span>of pool play</span></div>
    <div class="fact"><b>${f.tables} tables</b><span>to play a full round at once</span></div>
    <div class="fact"><b>${f.B}-slot</b><span>bracket if all advance · ${f.byes} byes</span></div>
  </div>`;
}
function setupSide(){
  const {names,dups}=parseRoster(state.roster),n=names.length,shown=n||EXPECTED;
  const changed=state.pools&&names.join('\n')!==state.players.map(p=>p.name).join('\n');
  return `<div class="note">${n?'Players entered':'Nobody entered yet · showing the plan for the expected '+EXPECTED}</div>
    <div class="big">${shown}</div>
    ${n>=2?factsHTML(n):n===0?factsHTML(EXPECTED):'<p class="note">Add at least 2 players.</p>'}
    ${dups.length?`<p class="note warn">Duplicate name skipped: ${esc(dups.join(', '))}. Add a last initial to tell them apart.</p>`:''}
    ${changed?'<p class="note warn">The list changed since pools were drawn. Draw again to apply it (this clears pool scores).</p>':''}
    ${n>28?'<p class="note">More than 28 is fine. The same rule applies: pools of 4, with some 5s or 3s.</p>':''}`;
}
function updateSetupSide(){const el=$('#setup-side');if(el)el.innerHTML=setupSide();const b=$('#draw');if(b)b.disabled=parseRoster(state.roster).names.length<2;}
function viewSetup(){
  const hasResults=poolDone()>0;
  return `<h2>Players</h2><p class="lede">Type everyone who showed up, one per line. The pool plan updates as you type. Draw when the list is final.</p>
  ${token?'':'<p class="note warn">Publishing is off, so players won’t see anything yet. Add your GitHub token on the Publish tab.</p>'}
  <div class="setup">
    <div class="panel">
      <label class="lbl" for="roster">Roster</label>
      <textarea id="roster" placeholder="Joe Warth&#10;…one name per line">${esc(state.roster)}</textarea>
      <div class="radios" role="radiogroup" aria-label="How to place players">
        <label><input type="radio" name="dm" id="dm-random" value="random" ${state.drawMode==='random'?'checked':''}><span>Random draw<small>Shuffle everyone into pools.</small></span></label>
        <label><input type="radio" name="dm" id="dm-snake" value="snake" ${state.drawMode==='snake'?'checked':''}><span>Spread the list order<small>Put the strongest players first. They go into different pools (snake order).</small></span></label>
      </div>
      <div class="row"><button class="primary" id="draw" ${parseRoster(state.roster).names.length<2?'disabled':''}>${state.pools?'Draw pools again':'Draw pools'}</button>
      ${state.pools&&hasResults?'<span class="note">Drawing again clears pool scores and the bracket.</span>':''}</div>
    </div>
    <div class="panel" id="setup-side">${setupSide()}</div>
  </div>`;
}
const OPTS=[[3,0],[3,1],[3,2],[2,3],[1,3],[0,3]];
const meId=()=>{const id=lsGet(ME_KEY);return id&&state.players.some(p=>p.id===id)?id:null};
function notStarted(what){
  return ADMIN?`<div class="panel empty"><h3>No ${what} yet</h3><p>Enter players and draw pools on the Players tab.</p><button id="go-setup">Go to Players</button></div>`
    :`<div class="panel empty"><h3>Pools haven’t been drawn yet</h3><p>This page updates on its own once the host draws pools. Keep it open.</p></div>`;
}
function viewPools(){
  if(!state.pools)return notStarted('pools');
  return `<div class="bar"><div><h2>Pool play</h2><p class="lede" style="margin:0">${poolDone()} of ${poolTotal()} matches played. Each match is best of 5.${ADMIN?' Pick the score as left player vs. right player.':''}</p></div></div>
  <div class="pools">${state.pools.map((ids,pi)=>poolCard(ids,pi)).join('')}</div>
  <p class="legend">Standings order: match wins, then head-to-head among the tied players, then game difference, then games won, then a coin toss (drawn randomly when the pools were made). Seeding ranks every pool winner first, then every runner-up, and so on. Within each place, players are ordered by win rate, then game difference per match.</p>`;
}
function matchRow(a,b){
  const key=pk(a,b),r=state.poolRes[key],val=r?r[a]+'-'+r[b]:'',me=meId();
  const mid=ADMIN?`<select id="pm-${esc(key)}" data-pool="${esc(a)}|${esc(b)}" class="${r?'done':''}" aria-label="${esc(P(a).name)} vs ${esc(P(b).name)}">
      <option value="">vs</option>${OPTS.map(([x,y])=>`<option value="${x}-${y}" ${val===x+'-'+y?'selected':''}>${x}–${y}</option>`).join('')}</select>`
    :`<span class="score ${r?'done':''}">${r?r[a]+'–'+r[b]:'vs'}</span>`;
  return `<div class="m ${!ADMIN&&me&&(a===me||b===me)?'me':''}"><span class="p a ${r&&r[a]>r[b]?'w':''}">${esc(P(a).name)}</span>${mid}<span class="p ${r&&r[b]>r[a]?'w':''}">${esc(P(b).name)}</span></div>`;
}
function poolCard(ids,pi){
  const st=standings(ids),rounds=rr(ids),L=String.fromCharCode(65+pi),cur=currentRound(ids),me=meId();
  const rows=st.map((s,i)=>`<tr><td><span class="rank">${i+1}</span></td><td class="name ${!ADMIN&&s.id===me?'me':''}">${esc(P(s.id).name)}</td><td class="num">${s.w}–${s.l}</td><td class="num">${s.gw}–${s.gl}</td><td class="num">${s.gw-s.gl>0?'+':''}${s.gw-s.gl}</td></tr>`).join('');
  const rds=rounds.map((rd,ri)=>`<div class="rnd"><div class="rnd-h"><span>Round ${ri+1}${ri===cur?' · now':''}</span>${rd.bye?`<span>Sits out: ${esc(P(rd.bye).name)}</span>`:''}</div>
    ${rd.ms.map(([a,b])=>matchRow(a,b)).join('')}</div>`).join('');
  return `<section class="pool"><div class="pool-h"><h3>Pool ${L}</h3><span>${ids.length} players · ${cur<0?'done':'round '+(cur+1)+' of '+rounds.length}</span></div>
    <div class="scroll"><table><thead><tr><th></th><th>Player</th><th class="num">W–L</th><th class="num">Games</th><th class="num">Diff</th></tr></thead><tbody>${rows}</tbody></table></div>
    <div class="rounds">${rds}</div></section>`;
}
function viewBracket(){
  if(!state.pools)return notStarted('bracket');
  const n=state.players.length,locked=!!state.bracket,br=locked?state.bracket:buildBracket();
  const rounds=bracketRounds(br),total=poolTotal(),done=poolDone();
  const fin=rounds[rounds.length-1][0],champ=fin.winner&&fin.res?fin.winner:null;
  const A=Object.keys(br.seedOf).length;
  const advBtns=[['all','Everyone'],['16','Top 16'],['8','Top 8']].filter(([v])=>v==='all'||+v<n)
    .map(([v,l])=>`<button data-adv="${v}" aria-pressed="${state.advance===v}" ${locked?'disabled':''}>${l}</button>`).join('');
  const cols=rounds.map((ms,ri)=>`<div class="col"><div class="col-h">${roundName(ms.length,ri,rounds.length)}</div><div class="col-b">${ms.map(o=>matchCard(o,br,locked)).join('')}</div></div>`).join('');
  const lede=locked?`${A} players, ${br.size}-slot bracket.${ADMIN?' Seeds are locked. Pick each score as top player vs. bottom player.':''}`
    :`Projected from current standings (${done} of ${total} pool matches played). ${ADMIN?'Lock the seeds when pool play ends.':'Seeds can still change until pool play ends.'}`;
  return `${champ?`<div class="champ"><div><div class="eyebrow">Champion</div><div class="big">${esc(P(champ).name)}</div></div></div>`:''}
  <div class="bar"><div><h2>Bracket</h2><p class="lede" style="margin:0">${lede}</p></div>
    ${ADMIN?`<div class="row"><span class="note">Who advances</span><span class="seg">${advBtns}</span>
    ${locked?'<button id="unlock">Re-seed</button>':'<button class="primary" id="lock">Lock seeds &amp; start</button>'}</div>`:''}</div>
  ${ADMIN&&!locked&&done<total?'<p class="note warn">Pool play isn’t finished, so these seeds may still change.</p>':''}
  <div class="scroll"><div class="bracket">${cols}</div></div>
  <p class="legend">Seeds go into a standard bracket, so 1 and 2 can only meet in the final. When the field isn’t a power of two, the top seeds get byes into round two.</p>`;
}
function matchCard(o,br,locked){
  const me=meId();
  const side=(id,score,win)=>{
    if(id===null)return `<div class="bp tbd"><span class="sd"></span><span class="nm">bye</span><span class="sc"></span></div>`;
    if(id===undefined)return `<div class="bp tbd"><span class="sd"></span><span class="nm">TBD</span><span class="sc"></span></div>`;
    return `<div class="bp ${win?'w':''}"><span class="sd">${br.seedOf[id]||''}</span><span class="nm" title="${esc(P(id).name)}">${esc(P(id).name)}</span><span class="sc">${score==null?'':score}</span></div>`;};
  const r=o.res;let sel='';
  if(ADMIN&&locked&&!o.bye&&o.a&&o.b){const val=r?r.ga+'-'+r.gb:'';
    sel=`<select id="bm-${o.r}-${o.m}" data-br="${o.r}-${o.m}" class="${r?'done':''}" aria-label="${esc(P(o.a).name)} vs ${esc(P(o.b).name)}"><option value="">Enter score</option>${OPTS.map(([x,y])=>`<option value="${x}-${y}" ${val===x+'-'+y?'selected':''}>${x}–${y}</option>`).join('')}</select>`;}
  const mine=!ADMIN&&me&&(o.a===me||o.b===me);
  return `<div class="bm ${o.bye?'bye':''} ${mine?'me':''}">${side(o.a,r?r.ga:null,o.winner&&o.winner===o.a&&!o.bye)}${side(o.b,r?r.gb:null,o.winner&&o.winner===o.b&&!o.bye)}${sel}</div>`;
}
function viewPlans(){
  const cur=parseRoster(state.roster).names.length||EXPECTED;
  const rows=[];for(let n=8;n<=28;n++){const f=planFacts(n);
    rows.push(`<tr class="${n===cur?'hl':''}"><td><b>${n}</b></td><td>${f.sizes.length} <small>(${f.sizes.join('-')})</small></td><td class="num">${f.each.join(' / ')}</td><td class="num">${f.matches}</td><td class="num">${f.rounds}</td><td class="num">${f.tables}</td><td>${f.B} <small>· ${f.byes} byes · ${f.brRounds} rounds</small></td><td>${n>16?'16 · '+(n-16)+' cut':'—'}</td><td>${n>8?'8 · '+(n-8)+' cut':'—'}</td></tr>`);}
  return `<h2>Pool plans for 8–28 players</h2><p class="lede">Pools of 4 where possible, with a few 5s or 3s to absorb the remainder. Everyone in a pool plays everyone else once. The highlighted row is ${parseRoster(state.roster).names.length?'your current count':'the expected '+EXPECTED}.</p>
  <div class="panel scroll"><table class="plans"><thead><tr><th>Players</th><th>Pools</th><th class="num">Matches each</th><th class="num">Pool matches</th><th class="num">Rounds</th><th class="num">Tables / round</th><th>Bracket, all advance</th><th>Top 16</th><th>Top 8</th></tr></thead><tbody>${rows.join('')}</tbody></table></div>
  <p class="legend">"Rounds" is the number of pool rounds if every pool plays at the same time. "Tables / round" is how many tables that takes. Pools of 5 and 3 need one more round than pools of 4, because one player sits out each round. With 17–20 players, "everyone advances" means a 32-slot bracket where most top seeds get byes. Cutting to the top 16 is cleaner and saves a round.</p>`;
}
function viewPublish(){
  const site='https://'+GH.owner+'.github.io/'+GH.repo+'/xtacle/';
  return `<h2>Publish to the player page</h2>
  <p class="lede">Every change you make here is saved in this browser and pushed to <code>${esc(GH.path)}</code> in <code>${esc(GH.owner+'/'+GH.repo)}</code>. The player page reads that file. Players can see it but can’t change it, because only your token can write.</p>
  <div class="setup">
    <div class="panel">
      <h3>Player page</h3>
      <p><b>${esc(site)}</b></p>
      <p class="note">Share that link or turn it into a QR code. Changes show up there about a minute after you make them, once GitHub Pages rebuilds.</p>
      <h3 style="margin-top:18px">Status</h3>
      <p>${!token?'No token yet. Nothing is being published.':pubErr?`<span class="note warn">${esc(pubErr)}</span>`:lastPub?'Last published '+ago(lastPub)+'.':'Ready. The next change will publish.'}</p>
      <div class="row"><button class="primary" id="pub-now" ${token?'':'disabled'}>Publish now</button><button id="pull">Load the published copy</button></div>
      <p class="note">Use “Load the published copy” when you switch to a different phone or laptop. It replaces what’s in this browser.</p>
    </div>
    <div class="panel">
      <h3>GitHub token</h3>
      <ol class="steps">
        <li>On GitHub, go to Settings → Developer settings → Personal access tokens → <b>Fine-grained tokens</b> → Generate new token.</li>
        <li>Repository access: <b>Only select repositories</b> → <code>${esc(GH.repo)}</code>.</li>
        <li>Permissions → Repository → <b>Contents: Read and write</b>. Set it to expire in a few days.</li>
        <li>Paste it below. It stays in this browser and is only sent to api.github.com.</li>
      </ol>
      <div class="field"><label class="lbl" for="tok">Token</label><input id="tok" type="password" autocomplete="off" placeholder="${token?'Saved · paste to replace':'github_pat_…'}"></div>
      <div class="row"><button class="primary" id="tok-save">Save token &amp; publish</button>${token?'<button id="tok-clear">Remove token</button>':''}</div>
    </div>
  </div>`;
}
/* ---------- player page: my matches ---------- */
function myStatus(id){
  const out={pool:[],next:null,line:''};
  const pi=state.pools.findIndex(p=>p.includes(id));if(pi<0)return out;
  rr(state.pools[pi]).forEach((rd,ri)=>{
    rd.ms.forEach(([a,b])=>{if(a===id||b===id){const opp=a===id?b:a,r=state.poolRes[pk(a,b)];out.pool.push({ri,opp,r:r?[r[id],r[opp]]:null});}});
    if(rd.bye===id)out.pool.push({ri,bye:true});
  });
  out.poolName='Pool '+String.fromCharCode(65+pi);
  const nextPool=out.pool.find(x=>!x.bye&&!x.r);
  if(nextPool){out.next={big:'vs '+P(nextPool.opp).name,sub:out.poolName+' · round '+(nextPool.ri+1)};return out;}
  if(!state.bracket){out.next={big:'Pool play done',sub:'Waiting for the bracket. Seeds lock when every pool finishes.'};return out;}
  const br=state.bracket;
  if(!br.seedOf[id]){out.next={big:'Out of the bracket',sub:'Only the top '+Object.keys(br.seedOf).length+' advanced.'};return out;}
  const rounds=bracketRounds(br);
  for(let r=0;r<rounds.length;r++)for(const o of rounds[r]){
    if(o.a!==id&&o.b!==id)continue;
    const label=roundName(rounds[r].length,r,rounds.length);
    if(o.winner===undefined){
      const opp=o.a===id?o.b:o.a;
      if(opp!==undefined){out.next={big:'vs '+P(opp).name,sub:label+' · seed '+br.seedOf[id]+' vs '+br.seedOf[opp]};return out;}
      const feed=rounds[r-1]&&rounds[r-1][o.a===id?2*o.m+1:2*o.m];
      out.next={big:'Waiting',sub:label+': you’ll play the winner of '+(feed&&feed.a&&feed.b?P(feed.a).name+' vs '+P(feed.b).name:'an earlier match')+'.'};return out;
    }
    if(o.winner!==id){out.next={big:'Eliminated',sub:'Lost in the '+label.toLowerCase()+(o.res?' '+Math.max(o.res.ga,o.res.gb)+'–'+Math.min(o.res.ga,o.res.gb):'')+'.'};return out;}
  }
  out.next={big:'Champion',sub:'You won the Xtacle Invitational.'};return out;
}
function onDeck(){
  const cards=[];
  if(state.bracket){
    const rounds=bracketRounds(state.bracket);
    const r=rounds.findIndex(ms=>ms.some(o=>o.winner===undefined&&o.a&&o.b));
    if(r>=0){const ms=rounds[r].filter(o=>o.winner===undefined&&o.a&&o.b);
      cards.push(`<div class="panel"><h3>${roundName(rounds[r].length,r,rounds.length)}</h3>${ms.map(o=>`<div class="m"><span class="p a">${esc(P(o.a).name)}</span><span class="score">vs</span><span class="p">${esc(P(o.b).name)}</span></div>`).join('')}</div>`);}
  }else{
    state.pools.forEach((ids,pi)=>{const cur=currentRound(ids);if(cur<0)return;const rd=rr(ids)[cur];
      const open=rd.ms.filter(([a,b])=>!state.poolRes[pk(a,b)]);
      cards.push(`<div class="panel"><h3>Pool ${String.fromCharCode(65+pi)} · round ${cur+1}</h3>${open.map(([a,b])=>`<div class="m"><span class="p a">${esc(P(a).name)}</span><span class="score">vs</span><span class="p">${esc(P(b).name)}</span></div>`).join('')}${rd.bye?`<p class="note">Sits out: ${esc(P(rd.bye).name)}</p>`:''}</div>`);});
  }
  return cards.length?`<h2 style="margin-top:28px">Playing now</h2><div class="ondeck">${cards.join('')}</div>`:'';
}
function viewMe(){
  if(!state.pools)return notStarted();
  const me=meId(),names=state.players.slice().sort((a,b)=>a.name.localeCompare(b.name));
  const picker=`<div class="picker"><label class="lbl" for="me-pick" style="margin:0">I am</label><select id="me-pick"><option value="">Pick your name…</option>${names.map(p=>`<option value="${esc(p.id)}" ${p.id===me?'selected':''}>${esc(p.name)}</option>`).join('')}</select></div>`;
  if(!me)return `<h2>My matches</h2>${picker}<p class="lede">Pick your name to see who you play next and how you’re doing.</p>${onDeck()}`;
  const s=myStatus(me),pi=state.pools.findIndex(p=>p.includes(me)),st=standings(state.pools[pi]),rank=st.findIndex(x=>x.id===me),mine=st[rank];
  const list=s.pool.map(x=>x.bye?`<div class="li"><span class="when">Round ${x.ri+1}</span><span class="note">Sit out</span><span></span></div>`
    :`<div class="li"><span class="when">Round ${x.ri+1}</span><span>vs ${esc(P(x.opp).name)}</span><span class="res ${x.r?(x.r[0]>x.r[1]?'W':'L'):''}">${x.r?(x.r[0]>x.r[1]?'W ':'L ')+x.r[0]+'–'+x.r[1]:'—'}</span></div>`).join('');
  return `<h2>My matches</h2>${picker}
  <div class="me-grid">
    <div class="next"><div class="eyebrow">Next up</div><div class="big">${esc(s.next.big)}</div><p>${esc(s.next.sub)}</p></div>
    <div class="panel"><h3>${esc(s.poolName)} · ${rank+1}${['st','nd','rd'][rank]||'th'} place</h3><p class="note" style="margin:4px 0 8px">${mine.w}–${mine.l} in matches · ${mine.gw}–${mine.gl} in games${state.bracket&&state.bracket.seedOf[me]?' · bracket seed '+state.bracket.seedOf[me]:''}</p><div class="list">${list}</div></div>
  </div>${onDeck()}`;
}

/* ---------- events ---------- */
let rosterTimer=null;
document.addEventListener('input',e=>{
  if(ADMIN&&e.target.id==='roster'){state.roster=e.target.value;updateSetupSide();clearTimeout(rosterTimer);
    rosterTimer=setTimeout(()=>{state.updatedAt=Date.now();saveLocal();schedulePublish(5000)},700);}
});
document.addEventListener('change',e=>{
  const t=e.target;
  if(t.id==='me-pick'){lsSet(ME_KEY,t.value||null);render();return}
  if(!ADMIN)return;
  if(t.name==='dm'){state.drawMode=t.value;commit();return}
  if(t.dataset.pool){const [a,b]=t.dataset.pool.split('|'),key=pk(a,b);
    if(!t.value)delete state.poolRes[key];else{const [x,y]=t.value.split('-').map(Number);state.poolRes[key]={[a]:x,[b]:y};}
    commit();return}
  if(t.dataset.br){const br=state.bracket;if(!br)return;const [r,m]=t.dataset.br.split('-').map(Number);
    const o=bracketRounds(br)[r][m];
    if(!t.value)delete br.res[r+'-'+m];else{const [x,y]=t.value.split('-').map(Number);br.res[r+'-'+m]={a:o.a,b:o.b,ga:x,gb:y};}
    commit();}
});
document.addEventListener('focusout',e=>{if(e.target.id==='roster')render();});
document.addEventListener('click',e=>{
  const b=e.target.closest('button');if(!b||b.disabled||!ADMIN)return;
  if(b.id==='draw'){if(parseRoster(state.roster).names.length<2)return;
    if(state.pools&&poolDone())twoStep(b,'Tap again: clears pool scores',draw);else draw();return}
  if(b.id==='go-setup'){location.hash='setup';return}
  if(b.dataset.adv){state.advance=b.dataset.adv;commit();return}
  if(b.id==='lock'){const go=()=>{state.bracket=buildBracket();commit()};
    if(poolDone()<poolTotal())twoStep(b,'Pool play not done. Tap to lock anyway',go);else go();return}
  if(b.id==='unlock'){const go=()=>{state.bracket=null;commit()};
    if(state.bracket&&Object.keys(state.bracket.res).length)twoStep(b,'Tap again: clears bracket scores',go);else go();return}
  if(b.id==='pub-now'){publish();return}
  if(b.id==='tok-save'){const v=$('#tok').value.trim();if(!v)return;token=v;lsSet(TOKEN_KEY,v);sha=undefined;pubErr='';render();publish();return}
  if(b.id==='tok-clear'){token=null;lsSet(TOKEN_KEY,null);setStatus('notoken');render();return}
  if(b.id==='pull'){twoStep(b,'Tap again: replaces this browser’s copy',async()=>{
    try{state=await fetchPublished();saveLocal();render();setStatus(token?'published':'notoken');}catch(err){pubErr='Couldn’t load the published copy. Check the connection.';render();}});return}
});
window.addEventListener('hashchange',render);

/* ---------- start ---------- */
render();
if(ADMIN){
  setStatus(token?'published':'notoken');
  if(!state.updatedAt)fetchPublished().then(d=>{if(d.updatedAt&&!state.updatedAt){state=d;saveLocal();render();}}).catch(()=>{});
}else{
  setStatus('loading');poll();setInterval(()=>{if(!document.hidden)poll()},POLL_MS);
  document.addEventListener('visibilitychange',()=>{if(!document.hidden)poll()});
}
})();
