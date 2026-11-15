/* TEI CNC cloud sync (Firebase). Loaded only when firebase-config.js provides a config.
   Data layout: workshops/main/{orders,finance,sessions,invoices,members,meta}.
   Money fields of an order live in finance/{orderId}, readable by manager and accounts only. */
import {initializeApp} from './vendor/firebase-app.js';
import {getAuth,onAuthStateChanged,signInWithEmailAndPassword,createUserWithEmailAndPassword,signOut,updateProfile,sendPasswordResetEmail,connectAuthEmulator} from './vendor/firebase-auth.js';
import {initializeFirestore,persistentLocalCache,persistentMultipleTabManager,collection,doc,onSnapshot,setDoc,updateDoc,deleteField,writeBatch,getDoc,serverTimestamp,connectFirestoreEmulator} from './vendor/firebase-firestore.js';

const FIN=['pricing','price','payTerms','advance','payments','voidedPayments'];
const META=['updatedAt','updatedBy'];
const W='workshops/main';
const clean=o=>JSON.parse(JSON.stringify(o??null));
const strip=d=>{const x={...d};META.forEach(k=>delete x[k]);return x};

export function start(cfg,app){
  const fb=initializeApp(cfg.firebase||cfg);
  const auth=getAuth(fb);
  const db=initializeFirestore(fb,{localCache:persistentLocalCache({tabManager:persistentMultipleTabManager()}),ignoreUndefinedProperties:true});
  if(cfg.emulator){connectAuthEmulator(auth,'http://127.0.0.1:'+(cfg.emulator.auth||9099),{disableWarnings:true});connectFirestoreEmulator(db,'127.0.0.1',cfg.emulator.firestore||8080)}

  let me=null,unsubs=[],memberUnsub=null;
  // Last known server state per document path; the diff baseline for pushes.
  const remote=new Map();
  const cols={orders:new Map(),finance:new Map(),sessions:new Map(),invoices:new Map(),members:new Map()};
  let settings=null,loaded=new Set(),expected=new Set(),pending=new Set(),applyTimer=0;
  const ref=p=>doc(db,W+'/'+p);

  const status=()=>app.setSyncStatus({online:navigator.onLine,pending:pending.size>0,ready:expected.size>0&&[...expected].every(x=>loaded.has(x))});
  addEventListener('online',status);addEventListener('offline',status);

  let gen=0;
  function stopData(){gen++;unsubs.forEach(u=>u());unsubs=[];Object.values(cols).forEach(m=>m.clear());remote.clear();settings=null;loaded=new Set();expected=new Set();pending=new Set()}
  function listen(name,isDoc=false,tries=0){expected.add(name);const myGen=gen;
    const target=isDoc?ref(name):collection(db,W+'/'+name);
    unsubs.push(onSnapshot(target,{includeMetadataChanges:true},snap=>{
      if(isDoc){const d=snap.exists()?strip(snap.data()):null;settings=d;remote.set(name,d?clean(d):null)}
      else{const m=cols[name];if(snap.metadata.fromCache&&!loaded.has(name)&&snap.empty){/* wait for server */}
        snap.docChanges().forEach(c=>{const p=name+'/'+c.doc.id;if(c.type==='removed'){m.delete(c.doc.id);remote.delete(p)}else{const d=strip(c.doc.data());m.set(c.doc.id,d);remote.set(p,clean(d))}})}
      if(snap.metadata.hasPendingWrites)pending.add(name);else pending.delete(name);
      if(!snap.metadata.fromCache||snap.size>0||isDoc)loaded.add(name);
      clearTimeout(applyTimer);applyTimer=setTimeout(apply,40);status();
    },err=>{
      // A membership written a moment ago may not be visible to the rules yet: retry before reporting.
      if(myGen===gen&&tries<6){setTimeout(()=>{if(myGen===gen)listen(name,isDoc,tries+1)},1000*(tries+1));return}
      app.toast('تعذر قراءة '+name+' من السيرفر: '+(err.code||err.message))}))}

  function apply(){
    const fin=cols.finance;
    const orders=[...cols.orders.values()].map(o=>({...o,...(fin.get(o.id)||{})}));
    app.applyRemote({orders,sessions:[...cols.sessions.values()],invoices:[...cols.invoices.values()],dayCapacity:settings?.dayCapacity||{},planOrder:settings?.planOrder||[]},{members:[...cols.members.values()],ready:[...expected].every(x=>loaded.has(x))});
  }

  function subscribeData(role){stopData();
    listen('orders');listen('sessions');listen('meta/settings',true);
    if(role==='manager'||role==='finance'){listen('finance');listen('invoices')}
    if(role==='manager')listen('members');
  }

  onAuthStateChanged(auth,user=>{
    memberUnsub?.();memberUnsub=null;stopData();me=null;
    if(!user){app.showLogin();return}
    const email=(user.email||'').toLowerCase();
    memberUnsub=onSnapshot(ref('members/'+email),{includeMetadataChanges:true},async snap=>{
      if(snap.metadata.hasPendingWrites)return; // wait until the server has confirmed the membership
      const m=snap.exists()?snap.data():null;
      if(!m||m.active===false){stopData();me=null;let ownerExists=true;try{ownerExists=(await getDoc(ref('meta/owner'))).exists()}catch(e){}
        app.showNoAccess({email,name:user.displayName||'',canBootstrap:!ownerExists,disabled:!!m});return}
      const prevRole=me?.role;me={email,name:m.name||user.displayName||email,role:m.role};
      app.setIdentity(me);
      if(prevRole!==me.role)subscribeData(me.role);
    },err=>app.toast('تعذر التحقق من الحساب: '+(err.code||err.message)));
  });

  // ---------- writes: diff local state against the last server state, send only changed fields ----------
  function docsFrom(state){const out=new Map(),role=me?.role;
    for(const o of state.orders||[]){const base={},fin={};for(const [k,v] of Object.entries(o))(FIN.includes(k)?fin:base)[k]=v;out.set('orders/'+o.id,clean(base));if(role!=='operator'&&Object.keys(fin).length)out.set('finance/'+o.id,clean(fin))}
    for(const s of state.sessions||[])out.set('sessions/'+s.id,clean(s));
    if(role!=='operator')for(const i of state.invoices||[])out.set('invoices/'+i.id,clean(i));
    if(role==='manager')out.set('meta/settings',clean({dayCapacity:state.dayCapacity||{},planOrder:state.planOrder||[]}));
    return out}
  const allowed=p=>{const r=me?.role,c=p.split('/')[0];if(r==='manager')return true;if(r==='operator')return c==='orders'||c==='sessions';if(r==='finance')return c==='finance'||c==='invoices';return false};
  const ready=()=>expected.size>0&&[...expected].every(x=>loaded.has(x));
  // Never push before the server state has loaded: a stale local cache must not overwrite the workshop.
  function push(state){if(!me||!ready())return;
    for(const [p,d] of docsFrom(state)){if(!allowed(p))continue;
      const before=remote.get(p),stamp={updatedAt:serverTimestamp(),updatedBy:me.name};
      let w;
      if(!before){if(me.role==='operator'&&p.startsWith('orders/'))continue;w=setDoc(ref(p),{...d,...stamp})}
      else{const patch={};const keys=new Set([...Object.keys(d),...Object.keys(before)]);
        for(const k of keys){if(JSON.stringify(d[k])!==JSON.stringify(before[k]))patch[k]=k in d?d[k]:deleteField()}
        if(!Object.keys(patch).length)continue;w=updateDoc(ref(p),{...patch,...stamp})}
      remote.set(p,d);
      w.catch(err=>{remote.delete(p);app.toast(err.code==='permission-denied'?'السيرفر رفض التعديل: الدور ده مش مسموح له بيه':'تعذر حفظ التعديل على السيرفر: '+(err.code||err.message));setTimeout(apply,50)});
    }}

  async function batchAll(entries){for(let i=0;i<entries.length;i+=400){const b=writeBatch(db);for(const [p,d] of entries.slice(i,i+400))b.set(ref(p),{...d,updatedAt:serverTimestamp(),updatedBy:me?.name||''});await b.commit()}}

  const api={
    push,
    get me(){return me},
    get debug(){return {expected:[...expected],loaded:[...loaded],pending:[...pending]}},
    signIn:(e,p)=>signInWithEmailAndPassword(auth,e.trim(),p),
    async signUp(name,e,p){const c=await createUserWithEmailAndPassword(auth,e.trim(),p);if(name)await updateProfile(c.user,{displayName:name});return c},
    signOut:()=>signOut(auth),
    resetPassword:e=>sendPasswordResetEmail(auth,e.trim()),
    async bootstrap(name){const u=auth.currentUser;if(!u)throw Error('no user');const email=u.email.toLowerCase();const b=writeBatch(db);
      b.set(ref('meta/owner'),{email,at:serverTimestamp()});b.set(ref('members/'+email),{email,name:name||u.displayName||email,role:'manager',active:true,addedAt:serverTimestamp(),addedBy:email});await b.commit()},
    addMember:({email,name,role})=>setDoc(ref('members/'+email.trim().toLowerCase()),{email:email.trim().toLowerCase(),name,role,active:true,addedAt:serverTimestamp(),addedBy:me?.email||''}),
    updateMember:(email,patch)=>updateDoc(ref('members/'+email),patch),
    async uploadAll(state){const entries=[...docsFrom(state)].filter(([p])=>allowed(p));await batchAll(entries);return entries.length},
  };
  window.TEI_SYNC=api;app.syncReady(api);
  return api;
}
