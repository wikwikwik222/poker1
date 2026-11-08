'use strict';
// Pokerkvällen – cashgame-server. Kör: npm install && npm start
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const TURN=+process.env.TURN_MS||30000,SHOW=+process.env.SHOW_MS||6000;
const FILE=process.env.DATA_FILE||path.join(__dirname,'tables.json');
const CAT=["Högt kort","Par","Två par","Triss","Stege","Färg","Kåk","Fyrtal","Straight flush"];
let S; // aktivt bord (all spellogik arbetar på S)
const cr=c=>2+c%13,cs=c=>Math.floor(c/13),int=x=>{x=Math.floor(+x);return Number.isFinite(x)&&x>0?Math.min(x,1e9):0};
const ct=c=>"23456789TJQKA"[cr(c)-2].replace('T','10')+"♠♥♦♣"[cs(c)],lg=x=>{S.lg.push(x);if(S.lg.length>80)S.lg.shift()},rec=e=>{if(S.cur)S.cur.ev.push(e)},lgr=(id,x)=>{lg(x);rec({k:'vs',id,tx:x})};
function ev5(c){const r=c.map(cr).sort((a,b)=>b-a),fl=c.every(x=>cs(x)==cs(c[0])),n={};r.forEach(x=>n[x]=(n[x]||0)+1);
 const g=Object.keys(n).map(Number).sort((a,b)=>n[b]-n[a]||b-a);let st=0;
 if(g.length==5){if(r[0]-r[4]==4)st=r[0];else if(r[0]==14&&r[1]==5)st=5}
 const k=n[g[0]],cat=st&&fl?8:k==4?7:k==3&&n[g[1]]==2?6:fl?5:st?4:k==3?3:k==2&&n[g[1]]==2?2:k==2?1:0;
 return cat*1e6+(st?[st]:g).reduce((a,x)=>a*15+x,0)}
function comb(a,k){const o=[];(function f(i,p){if(p.length==k){o.push(p);return}for(let j=i;j<a.length;j++)f(j+1,[...p,a[j]])})(0,[]);return o}
function best(h,b,v){let m=0;const t=x=>{const s=ev5(x);if(s>m)m=s};
 if(['omaha','omaha5','donk','sviten','o8'].includes(v))comb(h,2).forEach(a=>comb(b,3).forEach(c=>t(a.concat(c))));else comb(h.concat(b),5).forEach(t);return m}
function nxt(i,fn){const n=S.pl.length;for(let k=1;k<=n;k++){const j=(i+k)%n;if(fn(S.pl[j]))return j}return -1}
function post(p,a){a=Math.min(a,p.c);p.c-=a;p.b+=a;p.t+=a}
function remove(p){const i=S.pl.indexOf(p);if(i<0)return;const L=S.led[p.k];if(L)L.out+=p.c;S.pl.splice(i,1);if(i<=S.d)S.d--}
function cleanup(){S.pl.filter(p=>p.lv).forEach(remove)}
const DP={pine:0,crazy:3,lazy:4,sviten:3},HC={omaha5:5,omaha:4,donk:4,sviten:5,pine:3,crazy:3,lazy:3,o8:4,stud:3,razz:3};
const TB_N=3,TB_MS=+process.env.TB_MS||30000,RO_MS=+process.env.RO_MS||2500,RV_MS=+process.env.RV_MS||8000,EQ_MS=+process.env.EQ_MS||200;
function shuf(a){for(let i=a.length-1;i>0;i--){const j=crypto.randomInt(i+1);[a[i],a[j]]=[a[j],a[i]]}return a}
function applyPb(){S.sb=S.pb.sb;S.bb=S.pb.bb;S.ante=Math.max(1,Math.round(S.bb/5));S.bri=Math.max(1,Math.round(S.bb/2));S.min=Math.max(S.min,S.bb*2);S.max=Math.max(S.max,S.min);S.pb=null}
const isStud=()=>S.v=='stud'||S.v=='razz',seatsMax=t=>t.v=='sviten'?6:(t.v=='stud'||t.v=='razz')?8:9;
const lr=c=>{const r=cr(c);return r==14?1:r},rn=x=>({1:'A',11:'J',12:'Q',13:'K'}[x]||x);
function evP(c){if(c.length==5)return ev5(c);const n={};c.map(cr).forEach(x=>n[x]=(n[x]||0)+1);const g=Object.keys(n).map(Number).sort((a,b)=>n[b]-n[a]||b-a),k=n[g[0]];
 return(k==4?7:k==3?3:k==2&&n[g[1]]==2?2:k==2?1:0)*1e6+g.reduce((a,x)=>a*15+x,0)}
function bestHi(c){if(c.length<5)return evP(c);let m=0;comb(c,5).forEach(x=>{const v=ev5(x);if(v>m)m=v});return m}
function lowSc(r){return(r.length-new Set(r).size)*1e8+r.slice().sort((a,b)=>b-a).reduce((a,x)=>a*14+x,0)} // A–5 lowball: lägre = bättre
function bestLowC(c){const r=c.map(lr);if(r.length<=5)return r.sort((a,b)=>b-a);let b=null,bs=null;comb(r,5).forEach(x=>{const v=lowSc(x);if(bs==null||v<bs){bs=v;b=x}});return b.slice().sort((a,c)=>c-a)}
function lowO8(h,b){let m=null;comb(h,2).forEach(a=>comb(b,3).forEach(c=>{const l=a.concat(c).map(lr);if(Math.max(...l)>8||new Set(l).size<5)return;const v=l.sort((x,y)=>y-x).reduce((s,x)=>s*9+x,0);if(m==null||v<m)m=v}));return m}
function lowTxt(v){const o=[];while(v>0){o.unshift(v%9);v=Math.floor(v/9)}return o.map(rn).join('-')}
function studBringIdx(){let bi=-1,bk=null;S.pl.forEach((p,i)=>{if(p.f)return;const c=S.hands[p.id][2],su=[3,2,1,0][cs(c)],k=S.v=='razz'?-(lr(c)*10+su):cr(c)*10+su;if(bk==null||k<bk){bk=k;bi=i}});return bi}
function studFirst(){const n=S.pl.length;let best=null,bs=null;
 for(let k=1;k<=n;k++){const p=S.pl[(S.d+k)%n];if(p.f||p.c<=0)continue;const ups=S.hands[p.id].filter((_,i)=>i>=2&&i<=5),sc=S.v=='razz'?-lowSc(ups.map(lr)):evP(ups);if(bs==null||sc>bs){bs=sc;best=p}}
 return S.pl.indexOf(best)}
function setRt(){if(!isStud()){S.rt=0;return}S.rt=(S.nb>=4&&S.pl.filter(p=>!p.f).length>2)?0:(S.cb<S.ub?S.ub:S.cb+S.ub)}
function studStart(){
 S.ante=Math.max(1,Math.round(S.bb/5));S.bri=Math.max(1,Math.round(S.bb/2));S.st=3;S.ub=S.bb;S.nb=0;S.cb=0;S.mr=S.bb;
 S.pl.forEach(p=>{if(!p.f){const a=Math.min(S.ante,p.c);post(p,S.ante);p.b=0;rec({k:'an',id:p.id,d:a,tx:p.n+' ante '+a})}});
 lg('Ante '+S.ante+' från alla');
 const up={},ac=S.pl.filter(p=>!p.f);ac.forEach(p=>up[p.id]=S.hands[p.id][2]);
 lg('Tredje gatan: '+ac.map(p=>p.n+' '+ct(up[p.id])).join(', '));rec({k:'dl',st:3,up,tx:'Tredje gatan: '+ac.map(p=>p.n+' '+ct(up[p.id])).join(', ')});
 const bi=studBringIdx(),p=S.pl[bi],a=Math.min(S.bri,p.c);post(p,S.bri);S.cb=p.b;p.h=true;
 lg(p.n+' bring-in '+a);rec({k:'bl',id:p.id,d:a,tx:p.n+' bring-in '+a});
 S.turn=nxt(bi,q=>!q.f&&q.c>0);setRt()}
function studProceed(){
 const ac=S.pl.filter(p=>!p.f&&p.c>0);
 S.pl.forEach(p=>{p.b=0;p.h=false});S.cb=0;S.nb=0;S.mr=S.bb;
 if(S.st>=7)return showdown();
 S.st++;const act=S.pl.filter(p=>!p.f),up={};
 if(S.st==7&&S.deck.length<act.length){const c=S.deck.shift();S.board=[c];lg('Sjunde gatan: gemensamt kort '+ct(c));rec({k:'bd',b:S.board.slice(),tx:'Sjunde gatan: gemensamt kort '+ct(c)})}
 else{act.forEach(p=>{const c=S.deck.shift();S.hands[p.id].push(c);if(S.st<7)up[p.id]=c});
  const tx=['','','','Tredje','Fjärde','Femte','Sjätte','Sjunde'][S.st]+' gatan'+(S.st<7?': '+act.map(p=>p.n+' '+ct(up[p.id])).join(', '):' (dolda kort)');lg(tx);rec({k:'dl',st:S.st,up,tx})}
 S.ub=S.st>=5?S.bb*2:S.bb;
 if(ac.length<=1){S.ro=true;S.te=0;S.turn=-1;setRt();calcEq();return}
 S.ro=false;S.turn=studFirst();S.te=Date.now()+TURN;setRt()}
function newHand(){
 if(S.lg.length){S.hist.push({h:S.hn,l:S.lg});S.hist=S.hist.slice(-5)}S.lg=[];
 if(S.pb)applyPb();
 S.sub=null;S.dd=false;S.dc={};S.muck=[];S.fm=0;S.wins=[];S.sh={};S.ro=false;S.eq=null;S.rvo=null;S.rit=0;S.rvd=0;S.b1=null;S.rb=null;
 S.pl.forEach(p=>{p.b=0;p.t=0;p.h=false;p.f=p.c<=0||!!p.so});
 const lv=S.pl.filter(p=>!p.f);S.hands={};S.board=[];S.sd=false;
 if(lv.length<2){S.phase='wait';S.msg='';S.te=0;return}
 S.d=nxt(S.d,p=>!p.f);let sb,bb;
 if(lv.length==2){sb=S.d;bb=nxt(S.d,p=>!p.f)}else{sb=nxt(S.d,p=>!p.f);bb=nxt(sb,p=>!p.f)}
 const dk=shuf([...Array(52).keys()]),n=HC[S.v]||2;S.pl.forEach(p=>{if(!p.f)S.hands[p.id]=dk.splice(0,n)});
 S.deck=dk;S.hn=(S.hn||0)+1;S.phase='play';S.msg='';S.te=Date.now()+TURN;lg('Giv #'+S.hn+' · dealer '+S.pl[S.d].n);
 S.cur={hn:S.hn,v:S.v,sb:S.sb,bb:S.bb,d:S.pl[S.d].n,pl:S.pl.filter(p=>!p.f).map(p=>({id:p.id,n:p.n,c:p.c})),ev:[],h0:JSON.parse(JSON.stringify(S.hands))};
 if(isStud())studStart();
 else if(S.bomb>0&&(S.bq||(S.bn>0&&S.hn%S.bn==0))){ // bomb pot: ante från alla, ingen preflop, floppen delas direkt
  S.bq=false;S.pl.forEach(p=>{if(!p.f){const a=Math.min(S.bomb,p.c);post(p,S.bomb);p.b=0;rec({k:'an',id:p.id,d:a,tx:p.n+' ante '+a})}});S.cb=0;S.mr=S.bb;
  S.turn=nxt(S.d,p=>!p.f&&p.c>0);S.msg='💣 Bomb pot! Alla la '+S.bomb;lg(S.msg);
  if(DP[S.v]===0)enterDis();else{S.board=S.deck.splice(0,S.v=='donk'?2:3);lg('Flopp: '+S.board.map(ct).join(' '));rec({k:'bd',b:S.board.slice(),tx:'Flopp: '+S.board.map(ct).join(' ')})}}
 else{lg(S.pl[sb].n+' small blind '+S.sb+', '+S.pl[bb].n+' big blind '+S.bb);rec({k:'bl',id:S.pl[sb].id,d:Math.min(S.sb,S.pl[sb].c),tx:S.pl[sb].n+' small blind '+Math.min(S.sb,S.pl[sb].c)});rec({k:'bl',id:S.pl[bb].id,d:Math.min(S.bb,S.pl[bb].c),tx:S.pl[bb].n+' big blind '+Math.min(S.bb,S.pl[bb].c)});post(S.pl[sb],S.sb);post(S.pl[bb],S.bb);S.cb=S.bb;S.mr=S.bb;S.turn=nxt(bb,p=>!p.f&&p.c>0)}
 check()}
function check(){
 const al=S.pl.filter(p=>!p.f);
 if(al.length==1){const w=al[0],pot=S.pl.reduce((s,p)=>s+p.t,0);w.c+=pot;S.msg=w.n+' vinner '+pot+' (alla andra la ner)';lg(S.msg);S.wins=[{id:w.id,a:pot}];
  S.phase='show';S.sd=false;S.te=0;S.sub=null;S.ro=false;S.eq=null;S.rvo=null;rec({k:'w',w:S.wins,tx:S.msg});endRec();return}
 if(S.sub=='dis')return;
 if(S.ro){calcEq();return}
 const ac=al.filter(p=>p.c>0);
 const done=ac.length==0||ac.every(p=>p.h&&p.b==S.cb)||(ac.length==1&&ac[0].b>=S.cb);
 if(!done)return;
 if(!S.dd&&DP[S.v]===S.board.length)return enterDis();
 if(ac.length<=1)return startRo();
 proceed()}
function proceed(){
 if(isStud())return studProceed();
 const ac=S.pl.filter(p=>!p.f&&p.c>0),dn=S.v=='donk';
 S.pl.forEach(p=>{p.b=0;p.h=false});S.cb=0;S.mr=S.bb;
 if(S.board.length==5){if(dn){const c6=S.deck.shift();S.board.push(c6);lg('Superriver: '+ct(c6));rec({k:'bd',b:S.board.slice(),tx:'Superriver: '+ct(c6)})} // DonkEm: superriver utan satsning
  if(S.rit==2&&!S.b1){S.b1=S.board.slice();S.board=S.rb.slice();lg('Run 2');rec({k:'bd',b:S.board.slice(),r:2,tx:'Run 2 börjar'});S.ro=true;S.te=0;calcEq();return}
  return showdown()}
 S.board.push(...draw(S.board.length==0?(dn?2:3):(S.board.length==2&&dn?2:1)));
 {const tx=(S.b1?'Run 2 · ':S.rit==2?'Run 1 · ':'')+{2:'Flopp',3:'Flopp',4:'Turn',5:'River'}[S.board.length]+': '+S.board.map(ct).join(' ');lg(tx);rec({k:'bd',b:S.board.slice(),tx})}
 if(ac.length<=1){S.ro=true;S.te=0;calcEq();offerVote();return}
 S.ro=false;S.turn=nxt(S.d,p=>!p.f&&p.c>0);S.te=Date.now()+TURN}
// all-in-utspel: korten visas, vinstchans räknas och nästa gata delas av en timer
function startRo(){S.ro=true;S.te=0;calcEq();offerVote()}
function roStep(){if(!S.dd&&DP[S.v]===S.board.length){enterDis();return}proceed()}
function roGo(){if(S.phase!='play'||!S.ro||S.sub)return;if(S.rvo)closeVote();roStep()}
function offerVote(){if(S.eq&&!S.rit&&!S.rvd&&S.board.length<5&&S.v!='sviten'&&S.v!='donk'){S.rvd=1;S.rvo={};S.rte=Date.now()+RV_MS}}
function closeVote(){const need=S.pl.filter(p=>!p.f&&S.hands[p.id]),yes=need.every(p=>S.rvo[p.id]===true);S.rit=yes?2:1;if(yes){S.rb=S.board.slice();lg('Run it twice!');rec({k:'ri',tx:'Run it twice!'})}else{lg('Körs en gång');rec({k:'ri',tx:'Körs en gång'})}S.rvo=null}
function calcEq(){
 S.eq=null;const al=S.pl.filter(p=>!p.f&&S.hands[p.id]);if(al.length<2||isStud()||(DP[S.v]!==undefined&&!S.dd))return;
 const fin=S.v=='donk'?6:5,need=fin-S.board.length,sv=S.v=='sviten',res={};al.forEach(p=>res[p.id]=0);let n=0;const t0=Date.now();
 const d2=sv?al.map(p=>ev5(S.hands[p.id])):null;
 const share=a=>{const m=Math.max(...a),w=a.filter(x=>x==m).length;return a.map(x=>x==m?1/w:0)};
 const run=bd=>{const a=share(al.map(p=>best(S.hands[p.id],bd,S.v)));let b=a;if(sv)b=share(d2);else if(S.v=='o8'){const lw=al.map(p=>{const m=lowO8(S.hands[p.id],bd);return m==null?-1e9:-m});if(Math.max(...lw)>-1e9)b=share(lw)}al.forEach((p,i)=>res[p.id]+=(a[i]+b[i])/2);n++};
 if(need<=0)run(S.board);
 else if(need==1)S.deck.forEach(c=>run(S.board.concat(c)));
 else{const pool=S.deck.slice();do{for(let i=0;i<need;i++){const j=i+crypto.randomInt(pool.length-i);[pool[i],pool[j]]=[pool[j],pool[i]]}run(S.board.concat(pool.slice(0,need)))}while((Date.now()-t0<EQ_MS||n<100)&&Date.now()-t0<700)}
 S.eq={};al.forEach(p=>S.eq[p.id]=Math.round(res[p.id]/n*100));
 {const tx='Chanser: '+al.map(p=>p.n+' '+S.eq[p.id]+'%').join(', ');lg(tx);rec({k:'eq',eq:Object.assign({},S.eq),tx})}}
// kasta/byta kort (Pineapple, Sviten Special): alla som är kvar väljer samtidigt
function enterDis(){S.sub='dis';S.dc={};S.te=Date.now()+TURN;lg(S.v=='sviten'?'Byte av kort':'Alla kastar ett kort')}
function draw(n){const o=[];while(o.length<n){if(!S.deck.length){if(!S.fm){S.fm=1;S.pl.forEach(p=>{if(p.f&&S.hands[p.id])S.muck.push(...S.hands[p.id])})}
 if(!S.muck.length)break;S.deck=shuf(S.muck.splice(0))}o.push(S.deck.shift())}return o}
function discDone(){
 const need=S.pl.filter(p=>!p.f);if(S.sub!='dis'||!need.every(p=>S.dc[p.id]))return false;
 const sv=S.v=='sviten',n=S.pl.length;
 for(let k=1;k<=n;k++){const p=S.pl[(S.d+k)%n];if(p.f)continue;const idx=S.dc[p.id],h=S.hands[p.id];
  if(sv){const nw=draw(idx.length),used=idx.slice(0,nw.length);S.muck.push(...h.filter((_,i)=>used.includes(i)));S.hands[p.id]=h.filter((_,i)=>!used.includes(i)).concat(nw);lg(p.n+' byter '+nw.length+' kort');rec({k:'dc',id:p.id,tx:p.n+' byter '+nw.length+' kort'})}
  else{S.hands[p.id]=h.filter((_,i)=>!idx.includes(i));lg(p.n+' kastar ett kort');rec({k:'dc',id:p.id,tx:p.n+' kastar ett kort'})}}
 S.sub=null;S.dd=true;S.dc={};S.te=Date.now()+TURN;proceed();return true}
function autoDisc(){S.pl.filter(p=>!p.f&&!S.dc[p.id]).forEach(p=>{const h=S.hands[p.id];S.dc[p.id]=S.v=='sviten'?[]:[h.map(cr).indexOf(Math.min(...h.map(cr)))]});discDone()}
function showdown(){
 const al=S.pl.filter(p=>!p.f),sv=S.v=='sviten',stu=isStud(),razz=S.v=='razz',o8=S.v=='o8',s2={},wm={},lt={},bs=S.b1?[S.b1,S.board]:[S.board];
 const cardsOf=p=>S.hands[p.id].concat(S.board);
 const scs=bs.map(b=>{const o={};al.forEach(p=>{o[p.id]=stu?(razz?(lt[p.id]=bestLowC(cardsOf(p)),-lowSc(lt[p.id])):bestHi(cardsOf(p))):best(S.hands[p.id],b,S.v)});return o}),sc=scs[scs.length-1];
 const lo={};if(o8)al.forEach(p=>{const m=lowO8(S.hands[p.id],S.board);if(m!=null)lo[p.id]=-m});
 if(sv)al.forEach(p=>s2[p.id]=ev5(S.hands[p.id]));
 const nameOf=(p,v)=>razz?'Låg '+lt[p.id].map(rn).join('-'):CAT[Math.floor(v/1e6)];
 al.forEach(p=>lgr(p.id,p.n+' visar '+(stu?cardsOf(p):S.hands[p.id]).map(ct).join(' ')+' – '+scs.map(o=>nameOf(p,o[p.id])).join(' / ')+(sv?' / draw: '+CAT[Math.floor(s2[p.id]/1e6)]:'')+(o8?(lo[p.id]!=null?' / låg '+lowTxt(-lo[p.id]):' / ingen låg'):'')));
 const lv=[...new Set(al.map(p=>p.t))].sort((a,b)=>a-b);lv[lv.length-1]=1e12;let prev=0;const out=[];
 lv.forEach(L=>{let pot=0;S.pl.forEach(p=>pot+=Math.max(0,Math.min(p.t,L)-prev));
  const el=al.filter(p=>p.t>prev);prev=L;if(!pot||!el.length)return;
  const q=o8?el.filter(p=>p.id in lo):[];
  const parts=sv?[[Math.ceil(pot/2),sc,'Omaha: '],[Math.floor(pot/2),s2,'Draw: ']]:o8&&q.length?[[Math.ceil(pot/2),sc,'Hög: '],[Math.floor(pot/2),lo,'Låg: ',q]]:bs.map((b,k)=>[k==0?Math.ceil(pot/bs.length):Math.floor(pot/bs.length),scs[k],bs.length>1?'Run '+(k+1)+': ':'']);
  parts.forEach(([pt,sm,lab,lst])=>{if(!pt)return;const E=lst||el,m=Math.max(...E.map(p=>sm[p.id])),w=E.filter(p=>sm[p.id]==m),sh=Math.floor(pt/w.length);
   w.forEach(p=>{p.c+=sh;wm[p.id]=(wm[p.id]||0)+sh});w[0].c+=pt-sh*w.length;wm[w[0].id]+=pt-sh*w.length;out.push(w.map(p=>p.n).join(' & ')+' vinner '+pt+' ('+lab+(lab=='Låg: '?lowTxt(-m):nameOf(w[0],m))+')')})});
 S.sd=true;S.phase='show';S.te=0;S.sub=null;S.ro=false;S.eq=null;S.rvo=null;S.msg=out.join(' · ');out.forEach(lg);S.wins=Object.entries(wm).map(([id,a])=>({id,a}));rec({k:'w',w:S.wins,tx:S.msg});endRec()}
function act(p,a){
 const i=S.pl.indexOf(p);if(S.phase!='play'||S.sub||S.ro||i!=S.turn)return false;S.ac=(S.ac||0)+1;
 if(a.type=='fold'){p.f=true;lg(p.n+' lägger ner');rec({k:'ac',id:p.id,t:'f',d:0,tx:p.n+' lägger ner'})}
 else if(a.type=='call'){const nd=Math.min(S.cb-p.b,p.c);post(p,S.cb-p.b);{const tx=nd>0?p.n+' synar '+nd+(p.c==0?' (all-in)':''):p.n+' checkar';lg(tx);rec({k:'ac',id:p.id,t:'c',d:nd,tx})}}
 else if(a.type=='raise'){let X;if(isStud()){if(!S.rt||p.c<=S.cb-p.b)return false;X=Math.min(S.rt,p.b+p.c)}else X=Math.min(Math.max(+a.amt||0,S.cb+S.mr),p.b+p.c);
  if(S.lim)X=Math.min(X,S.cb+S.pl.reduce((s,q)=>s+q.t,0)+(S.cb-p.b)); // pot limit: max = potten efter syning
  const b0=p.b;post(p,X-p.b);{const tx=p.n+(S.cb==0?' satsar ':' höjer till ')+p.b+(p.c==0?' (all-in)':'');lg(tx);rec({k:'ac',id:p.id,t:'r',d:p.b-b0,tx})}
  if(p.b>S.cb){const inc=p.b-S.cb;if(inc>=S.mr)S.mr=inc;S.cb=p.b;if(isStud())S.nb++;S.pl.forEach(q=>{if(q!==p)q.h=false})}}
 else return false;
 p.h=true;S.turn=nxt(i,q=>!q.f&&q.c>0);S.te=Date.now()+TURN;setRt();check();return true}
function endRec(){if(!S.cur)return;S.cur.hc1=JSON.parse(JSON.stringify(S.hands));S.cur.fd=S.pl.filter(p=>p.f&&S.hands[p.id]).map(p=>p.id);S.cur.sd=S.sd;S.cur.shown=S.sh;S.cur.fb=S.board.slice();S.cur.b1=S.b1;S.last=S.cur;S.cur=null}
function leaveSeat(t,p){S=t;if(t.phase=='play'){if(!p.f){if(t.sub!='dis'&&!t.ro&&t.pl[t.turn]===p)act(p,{type:'fold'});else{p.f=true;check();if(t.sub=='dis')discDone()}}p.lv=true}else remove(p)}
const hpw=(c,x)=>crypto.createHash('sha256').update(c+':'+String(x||'').slice(0,40)).digest('hex');

// ---- bord, nätverk, sparning ----
const tables={};
const ready=t=>t.pl.filter(p=>p.c>0&&!p.so).length>=2;
function mk(code,o){o=o||{};const sb=int(o.sb)||5,bb=Math.max(sb,int(o.bb)||sb*2),min=Math.max(bb*2,int(o.min)||bb*20),max=Math.max(min,int(o.max)||min*5);
 return{code,v:['omaha','omaha5','donk','sviten','pine','crazy','lazy','o8','stud','razz'].includes(o.v)?o.v:'holdem',lim:o.lim===true||o.lim=='true'||o.lim==1||o.v=='donk'||o.v=='sviten'||o.v=='o8',bomb:int(o.bomb),bn:int(o.bn),hn:0,ac:0,fl:o.v=='stud'||o.v=='razz',ante:Math.max(1,Math.round(bb/5)),bri:Math.max(1,Math.round(bb/2)),st:0,ub:0,nb:0,rt:0,wins:[],sh:{},cur:null,last:null,pb:null,ro:false,eq:null,rvo:null,rit:0,rvd:0,b1:null,rb:null,owner:'',pwh:'',led:{},lg:[],hist:[],bq:false,sb,bb,min,max,pl:[],phase:'wait',d:-1,deck:[],board:[],hands:{},turn:-1,cb:0,mr:bb,msg:'',sd:false,te:0,cx:new Set(),tm:null}}
function adv(t){S=t;t.tk=null;cleanup();newHand();after(t)}
function after(t){S=t;
 const want=t.phase=='play'?(t.ro&&!t.sub?'ro':'play'):t.phase=='show'||(t.phase=='wait'&&ready(t))?t.phase:null;
 if(want!=t.tk||want=='play'){clearTimeout(t.tm);t.tk=want;
  if(want=='play')t.tm=setTimeout(()=>{S=t;t.tk=null;if(S.phase=='play'&&S.sub=='dis'){autoDisc();return after(t)}const p=S.pl[S.turn];
   if(p&&S.phase=='play'){act(p,{type:S.cb-p.b>0?'fold':'call'});p.to=(p.to||0)+1;if(p.to>=2)p.so=true}after(t)},Math.max(0,t.te-Date.now()));
  else if(want=='ro')t.tm=setTimeout(()=>{S=t;t.tk=null;roGo();after(t)},t.rvo?Math.max(0,t.rte-Date.now()):RO_MS);
  else if(want)t.tm=setTimeout(()=>adv(t),want=='show'?SHOW:2000)}
 bcast(t);save()}
function view(t,k){const me=t.pl.find(p=>p.k==k),s=JSON.parse(JSON.stringify(t,(key,v)=>['deck','tm','cx','led','dc','muck','owner','pwh','cur','last'].includes(key)?undefined:v)),sh=(t.phase=='show'&&t.sd)||(t.phase=='play'&&!!t.eq);
 s.pl.forEach((q,i)=>{const o=t.pl[i];q.off=![...t.cx].some(w=>w.k==o.k&&w.readyState==1);q.ow=!!t.owner&&o.k==t.owner;delete q.k});s.isOwner=!!t.owner&&t.owner==k;s.pw=!!t.pwh;
 for(const id in s.hands){const p=t.pl.find(q=>q.id==id),pubA=(me&&me.id==id)||(sh&&p&&!p.f),shw=t.sh[id]||[];s.hands[id]=s.hands[id].map((c,i)=>pubA||shw.includes(i)||((t.v=='stud'||t.v=='razz')&&p&&!p.f&&i>=2&&i<=5)?c:null)}
 s.res=Object.entries(t.led).map(([k,L])=>{const p=t.pl.find(q=>q.k==k);return{n:L.n,bi:L.bi,now:L.out+(p?p.c+(t.phase=='play'&&!p.f?p.t:0):0),seated:!!p&&!p.lv}});
 s.seats=seatsMax(t);s.turnMs=TURN;
 s.dn=Object.fromEntries(Object.entries(t.dc||{}).map(([k,v])=>[k,v.length]));
 if(t.last){const L=t.last,fin={};for(const id in L.hc1){const sdv=L.sd&&!L.fd.includes(id),shw=(L.shown&&L.shown[id])||[],stu=(L.v=='stud'||L.v=='razz')&&!L.fd.includes(id);fin[id]=L.hc1[id].map((c,i)=>(me&&me.id==id)||sdv||shw.includes(i)||(stu&&i>=2&&i<=5)?c:null)}
  s.last={hn:L.hn,v:L.v,sb:L.sb,bb:L.bb,d:L.d,pl:L.pl,ev:L.ev,fin,mine:me&&L.h0[me.id]||null,me:me?me.id:null,fb:L.fb,b1:L.b1}}
 s.you=me?me.id:null;s.now=Date.now();return s}
const send=(ws,o)=>{if(ws.readyState==1)ws.send(JSON.stringify(o))};
const bcast=t=>t.cx.forEach(ws=>send(ws,{s:view(t,ws.k)}));
let sv=null;function ledCopy(t){const L=JSON.parse(JSON.stringify(t.led));t.pl.forEach(p=>{if(p.lv&&L[p.k])L[p.k].out+=p.c+(t.phase=='play'?p.t:0)});return L} // spelare som är på väg att lämna får sina marker utbetalda vid omstart
function saveNow(){try{fs.writeFileSync(FILE,JSON.stringify(Object.values(tables).map(t=>({code:t.code,owner:t.owner,pwh:t.pwh,v:t.v,lim:t.lim,bomb:t.bomb,bn:t.bn,sb:t.sb,bb:t.bb,min:t.min,max:t.max,
 led:ledCopy(t),pl:t.pl.filter(p=>!p.lv).map(p=>({k:p.k,id:p.id,n:p.n,c:p.c+(t.phase=='play'?p.t:0),bi:p.bi,tb:p.tb}))}))))}catch(e){console.error('save',e.message)}}
function save(){if(sv)return;sv=setTimeout(()=>{sv=null;saveNow()},500)}
try{JSON.parse(fs.readFileSync(FILE,'utf8')).forEach(o=>{const t=tables[o.code]=mk(o.code,o);t.owner=o.owner||'';t.pwh=o.pwh||'';t.led=o.led||{};t.pl=o.pl.map(p=>({...p,b:0,t:0,h:false,f:true}));t.pl.forEach(p=>{if(!t.led[p.k])t.led[p.k]={n:p.n,bi:p.bi,out:0}})})}catch(e){}

function handle(ws,m){
 if(m.t=='join'){const code=String(m.code||'').toLowerCase().replace(/[^a-z0-9åäö]/g,'').slice(0,20);if(!code||!m.token)return;
  let t=tables[code];
  const tok=String(m.token).slice(0,40);
  if(!t){if(!m.create)return send(ws,{err:'Bordet finns inte. Använd "Skapa bord" för att starta ett nytt.'});if(Object.keys(tables).length>=200)return;t=tables[code]=mk(code,m.create);t.owner=tok;if(m.create.pw)t.pwh=hpw(code,m.create.pw);save()}
  else if(t.pwh&&tok!=t.owner&&!t.pl.some(q=>q.k==tok)&&hpw(code,m.pw)!=t.pwh)return send(ws,{err:m.pw?'Fel lösenord.':'Bordet har lösenord. Skriv det i rutan.'});
  ws.t=t;ws.k=tok;t.cx.add(ws);return bcast(t)}
 const t=ws.t;if(!t)return;S=t;const p=t.pl.find(q=>q.k==ws.k);
 if(m.t=='cfg'||m.t=='kick'||m.t=='pw'||m.t=='close'){if(!t.owner||ws.k!=t.owner)return;
  if(m.t=='cfg'){const sb=int(m.sb),bb=int(m.bb);if(!sb||!bb)return;t.pb={sb,bb:Math.max(sb,bb)};if(t.phase!='play')applyPb();return after(t)}
  if(m.t=='pw'){t.pwh=m.pw?hpw(t.code,m.pw):'';send(ws,{note:t.pwh?'Lösenord sparat.':'Lösenord borttaget.'});return after(t)}
  if(m.t=='kick'){const q=t.pl.find(x=>x.id==m.id);if(!q||q.k==ws.k)return;t.cx.forEach(w=>{if(w.k==q.k)send(w,{note:'Du blev utkastad av bordsägaren.'})});leaveSeat(t,q);return after(t)}
  if(m.t=='close'){t.cx.forEach(w=>{send(w,{closed:'Bordet stängdes av bordsägaren.'});w.t=null});clearTimeout(t.tm);delete tables[t.code];save();return}}
 if(m.t=='sit'&&!p&&t.pl.length<seatsMax(t)){const buy=Math.min(t.max,Math.max(t.min,int(m.buy)));
  let nm=String(m.name||'Spelare').replace(/[<>&"'`]/g,'').slice(0,14).trim()||'Spelare',k=2;const bs=nm.slice(0,12);
  while(t.pl.some(q=>q.n.toLowerCase()==nm.toLowerCase()))nm=bs+' '+k++;
  const L=t.led[ws.k]||(t.led[ws.k]={n:nm,bi:0,out:0});L.n=nm;L.bi+=buy;if(L.tb==null)L.tb=TB_N;
  t.pl.push({id:crypto.randomBytes(4).toString('hex'),k:ws.k,n:nm,c:buy,bi:buy,b:0,t:0,h:false,f:true,tb:L.tb});return after(t)}
 if(!p)return;
 if(m.t=='tb'){if(t.phase!='play'||(p.tb||0)<=0)return;const mine=!t.sub&&!t.ro&&t.pl[t.turn]===p,dis=t.sub=='dis'&&!p.f&&!t.dc[p.id];if(!mine&&!dis)return;
  p.tb--;const L=t.led[p.k];if(L)L.tb=p.tb;t.te+=TB_MS;lg(p.n+' tar tidsbank ('+p.tb+' kvar)');return after(t)}
 if(m.t=='show'){if(t.phase!='show'||!t.hands[p.id]||(t.sd&&!p.f))return;const n=t.hands[p.id].length;
  const idx=Array.isArray(m.idx)?[...new Set(m.idx.map(Number).filter(i=>Number.isInteger(i)&&i>=0&&i<n))]:[...Array(n).keys()],cur=t.sh[p.id]||[],nw=idx.filter(i=>!cur.includes(i));
  if(!nw.length)return;t.sh[p.id]=[...cur,...nw].sort();lgr(p.id,p.n+' visar '+nw.map(i=>ct(t.hands[p.id][i])).join(' '));return after(t)}
 if(m.t=='out'){p.so=true;return after(t)}
 if(m.t=='rit'){if(!t.rvo||t.phase!='play'||p.f||!t.hands[p.id])return;t.rvo[p.id]=!!m.yes;
  if(t.pl.filter(q=>!q.f&&t.hands[q.id]).every(q=>q.id in t.rvo)){t.rte=Date.now();t.tk=null}return after(t)}
 if(m.t=='act'&&act(p,m)){p.to=0;p.so=false;return after(t)}
 if(m.t=='top'){if(t.phase=='play'&&!p.f)return;const a=Math.min(int(m.amt),t.max-p.c);if(a>0){const L=t.led[p.k]||(t.led[p.k]={n:p.n,bi:p.bi,out:0});L.bi+=a;p.c+=a;p.bi+=a;p.so=false;after(t)}return}
 if(m.t=='disc'){if(t.phase!='play'||t.sub!='dis'||p.f||t.dc[p.id])return;const h=t.hands[p.id]||[];
  const idx=[...new Set((Array.isArray(m.idx)?m.idx:[]).map(Number).filter(i=>Number.isInteger(i)&&i>=0&&i<h.length))];
  if(t.v!='sviten'&&idx.length!=1)return;t.dc[p.id]=idx;discDone();return after(t)}
 if(m.t=='bomb'&&t.bomb>0){t.bq=!t.bq;return after(t)}
 if(m.t=='back'){p.so=false;p.to=0;return after(t)}
 if(m.t=='leave'){
  send(ws,{note:`Du lämnade bordet med ${p.c} marker (${p.c-p.bi>=0?'+':''}${p.c-p.bi} mot dina köp-in).`});
  leaveSeat(t,p);return after(t)}}

const zlib=require('zlib'),_png={};
function crc(b){const T=crc.t||(crc.t=Array.from({length:256},(_,n)=>{let c=n;for(let k=0;k<8;k++)c=c&1?0xEDB88320^(c>>>1):c>>>1;return c>>>0}));let c=0xFFFFFFFF;for(const x of b)c=T[(c^x)&255]^(c>>>8);return(c^0xFFFFFFFF)>>>0}
function chunk(t,d){const l=Buffer.alloc(4);l.writeUInt32BE(d.length);const td=Buffer.concat([Buffer.from(t),d]),c=Buffer.alloc(4);c.writeUInt32BE(crc(td));return Buffer.concat([l,td,c])}
function png(n){const raw=Buffer.alloc(n*(n*3+1));
 for(let y=0;y<n;y++)for(let x=0;x<n;x++){const dx=(x+.5)/n-.5,dy=(y+.5)/n-.5,r=Math.hypot(dx,dy),a=Math.atan2(dy,dx);let c=[20,32,27];
  if(r<.4){c=[200,55,45];if(r>.31)c=Math.floor((a+Math.PI)/(Math.PI/8))%2?[245,242,232]:[200,55,45];else if(r<.24&&r>.18)c=[245,242,232]}
  const o=y*(n*3+1)+1+x*3;raw[o]=c[0];raw[o+1]=c[1];raw[o+2]=c[2]}
 const ih=Buffer.alloc(13);ih.writeUInt32BE(n,0);ih.writeUInt32BE(n,4);ih[8]=8;ih[9]=2;
 return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),chunk('IHDR',ih),chunk('IDAT',zlib.deflateSync(raw)),chunk('IEND',Buffer.alloc(0))])}
const server=http.createServer((req,res)=>{
 const u=req.url.split('?')[0];
 if(u=='/healthz'){res.end('ok');return}
 if(u=='/manifest.webmanifest'){res.writeHead(200,{'Content-Type':'application/manifest+json'});res.end(JSON.stringify({name:'Pokerkvällen',short_name:'Poker',lang:'sv',start_url:'/',display:'standalone',orientation:'portrait',background_color:'#14201b',theme_color:'#14201b',icons:[{src:'/icon-192.png',sizes:'192x192',type:'image/png'},{src:'/icon-512.png',sizes:'512x512',type:'image/png',purpose:'any maskable'}]}));return}
 const mi=u.match(/^\/icon-(180|192|512)\.png$/);if(mi){const n=+mi[1];res.writeHead(200,{'Content-Type':'image/png','Cache-Control':'public, max-age=86400'});res.end(_png[n]||(_png[n]=png(n)));return}
 try{res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});res.end(fs.readFileSync(path.join(__dirname,'index.html')))}catch(e){res.writeHead(500);res.end('index.html saknas')}});
if(require.main===module){
 process.on('SIGTERM',()=>{saveNow();process.exit(0)});process.on('SIGINT',()=>{saveNow();process.exit(0)});
 const {WebSocketServer}=require('ws'),wss=new WebSocketServer({server,maxPayload:2048});
 wss.on('connection',ws=>{ws.on('message',r=>{let m;try{m=JSON.parse(r)}catch(e){return}try{handle(ws,m)}catch(e){console.error(e)}});
  ws.on('close',()=>{if(ws.t){ws.t.cx.delete(ws);bcast(ws.t)}});ws.on('error',()=>{})});
 const iv=setInterval(()=>wss.clients.forEach(ws=>{if(ws.dead)return ws.terminate();ws.dead=true;ws.ping()}),30000);
 wss.on('connection',ws=>{ws.on('pong',()=>ws.dead=false)});
 Object.values(tables).forEach(after);
 server.listen(process.env.PORT||3000,()=>console.log('Pokerkvällen kör på port '+(process.env.PORT||3000)))}
module.exports={tables,handle,view,png,server,saveNow,ev:{bestHi,bestLowC,lowSc,lowO8,lowTxt,evP}};
