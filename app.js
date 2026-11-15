/* TEI CNC mobile PWA. Engine ported from TEI CNC Lite V3.9; storage keys and backup format unchanged. */
(()=>{'use strict';
const KEY='tei_cnc_single_machine_v3',DB='tei_cnc_v3_drawings',PREF='tei_cnc_mobile_prefs',MS_H=3600000,APP_VERSION='4.2.0';
const $=id=>document.getElementById(id);
const esc=x=>String(x??'').replace(/[&<>"']/g,s=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[s]));
const pad=n=>String(n).padStart(2,'0');
const localDay=ts=>{const d=new Date(ts);return [d.getFullYear(),pad(d.getMonth()+1),pad(d.getDate())].join('-')};
const localTime=ts=>{const d=new Date(ts);return pad(d.getHours())+':'+pad(d.getMinutes())};
const dayBounds=day=>{const [y,m,d]=day.split('-').map(Number);return[new Date(y,m-1,d).getTime(),new Date(y,m-1,d+1).getTime()]};
const now=()=>Date.now();
const humanMs=ms=>{const minutes=Math.round(Math.max(0,ms)/60000);return Math.floor(minutes/60)+'س '+pad(minutes%60)+'د'};
const decimalHours=ms=>(Math.max(0,ms)/MS_H).toFixed(2);
const money=n=>(Number(n)||0).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2})+' ج';
const unique=a=>[...new Set(a)];
const nextId=(prefix,items)=>prefix+'-'+String(items.reduce((n,x)=>Math.max(n,Number((x.id||'').split('-').pop())||0),0)+1).padStart(4,'0');
const makeId=()=>crypto?.randomUUID?crypto.randomUUID():'s'+now()+'-'+Math.random().toString(36).slice(2);
const hrs=h=>String(+(Math.round(h*100)/100).toFixed(2));
const DATE_FMT='ar-EG-u-nu-latn';
const toDate=day=>{const[y,m,d]=day.split('-').map(Number);return new Date(y,m-1,d)};
const prettyDay=(day,weekday=false)=>day?toDate(day).toLocaleDateString(DATE_FMT,weekday?{weekday:'long',day:'numeric',month:'long'}:{day:'numeric',month:'short',year:'numeric'}):'';
const ic=(name,cls='')=>`<svg class="ic ${cls}" aria-hidden="true"><use href="#i-${name}"/></svg>`;

/* ================= State & engine (V3.9 logic) ================= */
let state={version:3,orders:[],sessions:[],invoices:[],tentatives:[],planOrder:[],dayCapacity:{}};
let role='manager',tab='machine',idb=null;
const order=id=>state.orders.find(o=>o.id===id),invoiceOf=id=>state.invoices.find(i=>i.orderId===id),live=()=>state.sessions.find(s=>!s.endAt);
const closeSeg=(s,t)=>{const seg=s.segments[s.segments.length-1];if(!seg||seg.endAt!=null)throw Error('فترة التشغيل غير صحيحة');if(t<seg.startAt)throw Error('وقت النهاية قبل البداية');seg.endAt=t};
const handling=g=>g.working===true||(g.working==null&&g.present===true);
function totals(s,at=now()){let run=0,stop=0,operator=0,repair=0;for(const g of s.segments){const d=Math.max(0,(g.endAt??at)-g.startAt);if(g.type==='run'){run+=d;operator+=d}else{stop+=d;if(handling(g)){operator+=d;repair+=d}}}return {run,stop,repair,idle:stop-repair,operator,total:run+stop}}
function sumOrder(id){return state.sessions.filter(s=>s.orderId===id).reduce((n,s)=>n+totals(s).run,0)}
function orderTotals(id){return state.sessions.filter(s=>s.orderId===id).reduce((a,s)=>{const t=totals(s);a.run+=t.run;a.stop+=t.stop;a.repair+=t.repair;a.operator+=t.operator;return a},{run:0,stop:0,repair:0,operator:0})}
function bill(o){const h=sumOrder(o.id)/MS_H;return Math.round((o.pricing==='hour'?h*o.price:o.price*o.qty)*100)/100}

/* ================= Payments (stored on the work order; advance allowed before the invoice) ================= */
const PAY_METHODS=['كاش','تحويل بنكي','شيك','محفظة إلكترونية'];
const r2=n=>Math.round((Number(n)||0)*100)/100;
const paymentsOf=o=>Array.isArray(o?.payments)?o.payments:[];
const paidOf=o=>r2(paymentsOf(o).reduce((n,p)=>n+(Number(p.amount)||0),0));
function expectedValue(o){if(o.pricing==='hour')return r2(Math.max(sumOrder(o.id)/MS_H,Number(o.estimate)||0)*o.price);return r2(o.price*o.qty)}
function payState(o){const inv=invoiceOf(o.id),paid=paidOf(o);
  if(!inv)return {invoiced:false,paid,due:expectedValue(o),balance:null,status:paid>0?'advance':'none'};
  const due=r2(inv.amount??invoiceFigure(inv,o).total),balance=r2(due-paid);
  return {invoiced:true,paid,due,balance,status:balance>0.004?(paid>0?'partial':'unpaid'):(balance<-0.004?'over':'paid')}}
function nextReceiptNumber(){const year=new Date().getFullYear(),all=state.orders.flatMap(paymentsOf).map(p=>String(p.number||'').toLowerCase());let n=1,v='';do{v='TEI-RCV-'+year+'-'+String(n++).padStart(4,'0')}while(all.includes(v.toLowerCase()));return v}
const outstandingOrders=()=>state.orders.filter(o=>{const p=payState(o);return p.invoiced&&p.balance>0.004});

/* ================= Role PINs (light lock on one device, not real security) ================= */
const sec=()=>{if(!state.security||typeof state.security!=='object')state.security={};if(!state.security.pins)state.security.pins={};return state.security};
const hasPin=r=>!!state.security?.pins?.[r];
async function hashPin(pin){const s=sec();if(!s.salt)s.salt=makeId();const text=s.salt+':'+pin;
  if(crypto?.subtle){const buf=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(text));return 'sha256:'+[...new Uint8Array(buf)].map(b=>b.toString(16).padStart(2,'0')).join('')}
  let h=2166136261;for(const c of text){h^=c.charCodeAt(0);h=Math.imul(h,16777619)>>>0}return 'fnv:'+h.toString(16)}
function splitDay(s,day,at=now()){const[a,b]=dayBounds(day);let run=0,stop=0,operator=0,repair=0,min=Infinity,max=-Infinity;const reasons={};for(const g of s.segments){const x=Math.max(a,g.startAt),y=Math.min(b,g.endAt??at);if(y<=x)continue;const d=y-x;min=Math.min(min,x);max=Math.max(max,y);if(g.type==='run'){run+=d;operator+=d}else{stop+=d;if(handling(g)){operator+=d;repair+=d}const key=g.reason||'غير محدد';reasons[key]=(reasons[key]||0)+d}}return run+stop>0?{sessionId:s.id,day,operatorName:s.operator,orderId:s.orderId,start:min,end:max,run,stop,repair,idle:stop-repair,operator,reasons}:null}
function dayRows(day,at=now()){return state.sessions.map(s=>splitDay(s,day,at)).filter(Boolean).sort((a,b)=>a.start-b.start)}
function overlap(start,end,exclude=''){return state.sessions.some(s=>s.id!==exclude&&start<(s.endAt??now())&&end>s.startAt)}
function activeOption(o){return !!o&&(o.status==='معلق'||o.status==='بدء')}
function canFinish(o){return !!o&&o.status==='بدء'&&sumOrder(o.id)>0&&!(live()?.orderId===o.id)&&!invoiceOf(o.id)}
function canInvoice(o){return !!o&&o.status==='تسليم'&&!!o.deliveredAt&&!!o.completedAt&&!(live()?.orderId===o.id)&&sumOrder(o.id)>0&&!invoiceOf(o.id)}
function canDeliver(o){return !!o&&o.status==='انتهاء'&&!!o.completedAt&&sumOrder(o.id)>0&&!(live()?.orderId===o.id)}
function priorities(o){return ({'عاجل':0,'عالي':1,'عادي':2}[o.priority]??2)}
window.TEI_ENGINE={totals,handling,orderTotals,splitDay,dayRows,bill,canDeliver,canInvoice,canFinish,overlap,sumOrder,localDay,dayBounds};

function save(){try{localStorage.setItem(KEY,JSON.stringify(state));return true}catch(e){$('storeError').classList.remove('hidden');toast('تعذر حفظ البيانات');return false}}
function load(){try{const s=JSON.parse(localStorage.getItem(KEY)||'null');if(s&&s.version===3&&Array.isArray(s.orders)&&Array.isArray(s.sessions)&&Array.isArray(s.invoices)){state=s;state.tentatives=Array.isArray(s.tentatives)?s.tentatives:[];state.planOrder=Array.isArray(s.planOrder)?s.planOrder:[];state.dayCapacity=(s.dayCapacity&&typeof s.dayCapacity==='object')?s.dayCapacity:{}}}catch(e){$('storeError').classList.remove('hidden')}}

/* ================= Planning engine ================= */
const DAYS=['الأحد','الاثنين','الثلاثاء','الأربعاء','الخميس','الجمعة','السبت'];
let weekAnchor=null,calendarView='month',selectedDay=null;
const addDays=(day,n)=>{const[y,m,d]=day.split('-').map(Number);return localDay(new Date(y,m-1,d+n).getTime())};
const dayName=day=>DAYS[toDate(day).getDay()];
const weekStart=day=>{const w=toDate(day).getDay();return addDays(day,-((w+1)%7))};
function capacity(day){const v=state.dayCapacity?.[day];if(v!=null&&Number.isFinite(+v))return Math.max(0,Math.min(24,+v));return 24}
function queueItems(){
  const items=state.orders.filter(activeOption).map(o=>({...o,potential:false,remaining:Math.max(0,Number(o.estimate)-sumOrder(o.id)/MS_H)}));
  const ranks=state.planOrder||[];
  const known=items.filter(x=>ranks.includes(x.id)).sort((a,b)=>ranks.indexOf(a.id)-ranks.indexOf(b.id));
  const other=items.filter(x=>!ranks.includes(x.id)).sort((a,b)=>priorities(a)-priorities(b)||(a.due||'9999').localeCompare(b.due||'9999'));
  return [...known,...other];
}
function planEngine(extra=null,start=localDay(now()),horizon=180,until=now()){
  const queue=queueItems().map(x=>({...x}));
  if(extra)queue.push({...extra,id:extra.id||'WHATIF',remaining:Number(extra.estimate),potential:true});
  const days={},finish={};
  for(let i=0;i<horizon;i++){
    const d=addDays(start,i),cap=capacity(d),used=dayRows(d,until).reduce((n,r)=>n+(r.run+r.stop)/MS_H,0);
    let left=Math.max(0,cap-used);const tasks=[];
    for(const item of queue){
      if(left<1e-7)break;
      if(item.remaining<=1e-7)continue;
      if(item.planStart&&d<item.planStart)continue;
      const h=Math.min(item.remaining,left);
      tasks.push({id:item.id,name:item.name,client:item.client,hours:h,potential:!!item.potential,status:item.status});
      item.remaining-=h;left-=h;
      if(item.remaining<1e-7)finish[item.id]=d;
    }
    days[d]={date:d,cap,used,tasks,free:left};
  }
  return {days,finish,queue,notPlanned:queue.filter(x=>x.remaining>1e-7).map(x=>x.id),warnings:queueItems().filter(x=>x.remaining<=1e-7&&activeOption(order(x.id))).map(x=>x.id)};
}
function plannedFinish(id){return planEngine().finish[id]||''}
function movePlan(id,step){if(role!=='manager')return;const arr=queueItems().map(x=>x.id),i=arr.indexOf(id),j=i+step;if(i<0||j<0||j>=arr.length)return;[arr[i],arr[j]]=[arr[j],arr[i]];state.planOrder=arr;save();render()}
Object.assign(window.TEI_ENGINE,{planEngine,queueItems,capacity,plannedFinish,movePlan});

/* ================= Labels ================= */
const STATUS={'معلق':{label:'معلق',cls:'pending',icon:'clock'},'بدء':{label:'قيد التشغيل',cls:'running',icon:'play'},'انتهاء':{label:'جاهز للتسليم',cls:'done',icon:'flag-checkered'},'تسليم':{label:'استلمه العميل',cls:'delivered',icon:'package'}};
const statusLabel=s=>STATUS[s]?.label||s||'';
const pill=s=>{const x=STATUS[s]||{label:s,cls:'pending',icon:'info'};return `<span class="pill ${x.cls}">${ic(x.icon)}${esc(x.label)}</span>`};
const ROLES={manager:{label:'مدير الورشة',icon:'user',home:'orders',desc:'الأوامر، الخطة، استلام العميل، إذن التسليم'},operator:{label:'المشغّل',icon:'wrench',home:'machine',desc:'العداد، الأعطال، تغيير المشغّل، إنهاء الأمر'},finance:{label:'الحسابات',icon:'receipt',home:'orders',desc:'إصدار الفواتير وتعديلها وطباعتها'}};
const TITLES={machine:['الماكينة','ماكينة CNC واحدة'],orders:['أوامر الشغل','الشغل والاستلام والفواتير'],plan:['خطة التشغيل','حتى 24 ساعة يوميًا'],reports:['التقارير','من سجل التشغيل مباشرة'],more:['المزيد','الدور والنسخ الاحتياطي']};

/* ================= Prefs ================= */
let prefs={theme:'auto',role:'manager'};
try{prefs={...prefs,...JSON.parse(localStorage.getItem(PREF)||'{}')}}catch(e){}
const savePrefs=()=>{try{localStorage.setItem(PREF,JSON.stringify(prefs))}catch(e){}};

/* ================= Toast ================= */
function toast(text,opt={}){const x=$('toast');x.innerHTML=`<span style="flex:1">${esc(text)}</span>${opt.label?`<button class="btn sm" type="button" id="toastAct">${esc(opt.label)}</button>`:''}`;x.classList.add('on');if(opt.label)$('toastAct').onclick=()=>{x.classList.remove('on');opt.action()};clearTimeout(toast.t);toast.t=setTimeout(()=>x.classList.remove('on'),opt.ms||(opt.label?9000:3800))}

/* ================= Bottom sheets (Android back closes) ================= */
let sheet=null,ignorePop=false;
function openSheet({title,sub='',body,foot='',onClose=null,focus=null,locked=false}){
  const host=$('sheetHost');
  if(!sheet){
    host.innerHTML=`<div class="scrim" ${locked?'':'data-close'}></div><div class="sheet" role="dialog" aria-modal="true" aria-labelledby="sheetTitle" tabindex="-1"></div>`;
    sheet={el:host.querySelector('.sheet'),scrim:host.querySelector('.scrim'),onClose,locked,lastFocus:document.activeElement};
    history.pushState({sheet:1},'');
    requestAnimationFrame(()=>requestAnimationFrame(()=>{sheet?.el.classList.add('on');sheet?.scrim.classList.add('on')}));
  }else{sheet.onClose?.();sheet.onClose=onClose;sheet.locked=locked;if(locked)sheet.scrim.removeAttribute('data-close');else sheet.scrim.setAttribute('data-close','')}
  sheet.el.innerHTML=`<div class="sheet-grip" aria-hidden="true"></div><div class="sheet-head"><div class="t"><h2 id="sheetTitle">${esc(title)}</h2>${sub?`<p>${sub}</p>`:''}</div>${locked?'':`<button class="iconbtn" type="button" data-close aria-label="إغلاق">${ic('x')}</button>`}</div><div class="sheet-body">${body}<div class="form-error hidden" id="sheetErr" role="alert"></div></div>${foot?`<div class="sheet-foot">${foot}</div>`:''}`;
  setTimeout(()=>{const f=focus?sheet?.el.querySelector(focus):null;(f||sheet?.el)?.focus({preventScroll:true})},60);
}
function teardown(){if(!sheet)return;const s=sheet;sheet=null;s.onClose?.();s.el.classList.remove('on');s.scrim.classList.remove('on');setTimeout(()=>{if(!sheet)$('sheetHost').innerHTML=''},260);try{s.lastFocus?.focus({preventScroll:true})}catch(e){}}
function closeSheet(force=false){if(!sheet||(sheet.locked&&!force))return;teardown();if(history.state&&history.state.sheet){ignorePop=true;history.back()}}
window.addEventListener('popstate',()=>{if(ignorePop){ignorePop=false;return}if(sheet?.locked){history.pushState({sheet:1},'');return}if(sheet)teardown()});
document.addEventListener('keydown',e=>{if(!sheet)return;if(e.key==='Escape'){e.preventDefault();closeSheet()}if(e.key==='Tab'){const f=[...sheet.el.querySelectorAll('button,input,select,textarea,[tabindex]:not([tabindex="-1"])')].filter(x=>!x.disabled&&x.offsetParent!==null);if(!f.length)return;const a=f[0],b=f[f.length-1];if(e.shiftKey&&document.activeElement===a){e.preventDefault();b.focus()}else if(!e.shiftKey&&document.activeElement===b){e.preventDefault();a.focus()}}});
function sheetErr(msg,field){const box=$('sheetErr');if(!box){toast(msg);return}box.innerHTML=ic('warning','sm')+`<span>${esc(msg)}</span>`;box.classList.remove('hidden');sheet?.el.querySelectorAll('[aria-invalid]').forEach(x=>x.removeAttribute('aria-invalid'));if(field){field.setAttribute('aria-invalid','true');field.focus()}box.scrollIntoView({block:'nearest',behavior:'smooth'})}
function ask({title,body,ok='تأكيد',danger=false}){return new Promise(res=>{let done=false;openSheet({title,body:`<p class="help" style="font-size:15px;color:var(--ink)">${body}</p>`,foot:`<div class="row"><button class="btn" type="button" data-close>إلغاء</button><button class="btn ${danger?'danger':'primary'}" type="button" id="askOk">${esc(ok)}</button></div>`,onClose:()=>{if(!done)res(false)}});$('askOk').onclick=()=>{done=true;closeSheet();res(true)}})}
$('sheetHost').addEventListener('click',e=>{if(e.target.closest('[data-close]'))closeSheet()});

/* ================= PIN pad & role switching ================= */
let pinFails=0,pinLockUntil=0;
function pinPad({title,sub='',confirmLabel='دخول',locked=false,extra='',onSubmit}){
  let val='';
  openSheet({title,sub,locked,body:`<div class="pinwrap"><div class="pindots" id="pinDots" aria-live="polite"></div><div class="pinpad" id="pinPad">${[1,2,3,4,5,6,7,8,9].map(n=>`<button type="button" data-k="${n}">${n}</button>`).join('')}<button type="button" data-k="back" aria-label="مسح آخر رقم">${ic('backspace')}</button><button type="button" data-k="0">0</button><button type="button" data-k="ok" class="ok" aria-label="${esc(confirmLabel)}">${ic('check')}</button></div>${extra}</div>`});
  const dots=()=>{$('pinDots').innerHTML=Array.from({length:Math.max(4,val.length)},(_,i)=>`<i class="${i<val.length?'on':''}"></i>`).join('')+`<span class="sr">تم إدخال ${val.length} أرقام</span>`};dots();
  const shake=()=>{const d=$('pinDots');if(!d)return;d.classList.remove('err');void d.offsetWidth;d.classList.add('err')};
  const submit=async()=>{if(now()<pinLockUntil){val='';dots();return sheetErr(`محاولات كثيرة. انتظر ${Math.ceil((pinLockUntil-now())/1000)} ثانية`)}if(val.length<4){shake();return sheetErr('الرقم من 4 إلى 6 أرقام')}const v=val;val='';dots();if(await onSubmit(v)===false)shake()};
  const press=k=>{$('sheetErr')?.classList.add('hidden');if(k==='back')val=val.slice(0,-1);else if(k==='ok')return submit();else if(val.length<6)val+=k;dots();if(val.length===6)submit()};
  $('pinPad').onclick=e=>{const b=e.target.closest('[data-k]');if(b)press(b.dataset.k)};
  pinPad.press=press;
}
document.addEventListener('keydown',e=>{if(!sheet||!$('pinPad')||!pinPad.press)return;if(/^\d$/.test(e.key))pinPad.press(e.key);else if(e.key==='Backspace')pinPad.press('back');else if(e.key==='Enter'){e.preventDefault();pinPad.press('ok')}});
async function verifyPin(r,v){if(now()<pinLockUntil)return false;if(await hashPin(v)===state.security?.pins?.[r]){pinFails=0;return true}if(++pinFails>=5){pinLockUntil=now()+30000;pinFails=0}return false}
const pinFailMsg=()=>now()<pinLockUntil?'محاولات كثيرة خاطئة. انتظر 30 ثانية':'الرقم غير صحيح';
function requestRole(r){if(!ROLES[r])return;
  if(r===role){if(sheet)closeSheet();return}
  if(!hasPin(r)){closeSheet(true);roleSet(r,true);toast('الدور الحالي: '+ROLES[r].label);return}
  pinPad({title:'رقم '+ROLES[r].label,sub:'أدخل الرقم السري لهذا الدور',onSubmit:async v=>{if(!await verifyPin(r,v)){sheetErr(pinFailMsg());return false}closeSheet(true);roleSet(r,true);toast('الدور الحالي: '+ROLES[r].label)}})}
function lockScreen(){const free=Object.keys(ROLES).filter(k=>!hasPin(k));
  pinPad({title:'رقم '+ROLES[role].label,sub:'التطبيق مقفول على هذا الدور',locked:true,
    extra:free.length?`<div style="display:flex;flex-direction:column;gap:8px;align-items:center"><p class="help">أو ادخل بدور بدون رقم:</p><div class="namechips" style="justify-content:center">${free.map(k=>`<button type="button" class="chip" data-unlock-as="${k}">${ic(ROLES[k].icon,'sm')}${esc(ROLES[k].label)}</button>`).join('')}</div></div>`:'',
    onSubmit:async v=>{if(!await verifyPin(role,v)){sheetErr(pinFailMsg());return false}closeSheet(true);render()}});
  sheet.el.querySelectorAll('[data-unlock-as]').forEach(b=>b.onclick=()=>{closeSheet(true);roleSet(b.dataset.unlockAs,true)})}
function roleListHTML(){return Object.entries(ROLES).map(([k,r])=>`<button type="button" class="litem roleopt" role="radio" aria-checked="${role===k}" data-role="${k}">${ic(hasPin(k)?'lock-simple':r.icon)}<span class="t">${esc(r.label)}<span>${esc(r.desc)}${hasPin(k)?' · محمي برقم سري':''}</span></span>${role===k?ic('check'):''}</button>`).join('')}
function managePins(){if(role!=='manager')return toast('الأرقام السرية يديرها المدير فقط');
  openSheet({title:'الأرقام السرية للأدوار',sub:'قفل خفيف على هذا الجهاز',body:`<div class="card list" style="box-shadow:none">${Object.entries(ROLES).map(([k,r])=>`<div class="litem">${ic(hasPin(k)?'lock-simple':r.icon)}<span class="t">${esc(r.label)}<span>${hasPin(k)?'محمي برقم سري':'بدون رقم'}</span></span><button type="button" class="btn sm" data-pinset="${k}">${hasPin(k)?'تغيير':'تعيين'}</button>${hasPin(k)?`<button type="button" class="iconbtn" data-pindel="${k}" aria-label="إلغاء رقم ${esc(r.label)}">${ic('x')}</button>`:''}</div>`).join('')}</div>
    <p class="help">ابدأ برقم المدير، لأن المدير هو اللي بيغيّر الأرقام. الرقم من 4 لـ 6 أرقام، وبيتحفظ مشفّر. لو نسيت رقم المدير، الحل استعادة نسخة احتياطية أقدم أو مسح بيانات الموقع من المتصفح.</p>`});
  sheet.el.querySelectorAll('[data-pinset]').forEach(b=>b.onclick=()=>setPinFlow(b.dataset.pinset));
  sheet.el.querySelectorAll('[data-pindel]').forEach(b=>b.onclick=()=>{const k=b.dataset.pindel;if(k==='manager'&&Object.keys(ROLES).some(x=>x!=='manager'&&hasPin(x)))return sheetErr('ألغِ أرقام الأدوار الأخرى قبل رقم المدير');delete sec().pins[k];save();toast('تم إلغاء رقم '+ROLES[k].label);managePins()})}
function setPinFlow(k){if(k!=='manager'&&!hasPin('manager'))return sheetErr('عيّن رقم المدير أولًا');
  pinPad({title:'رقم جديد: '+ROLES[k].label,sub:'من 4 إلى 6 أرقام، ثم اضغط ✓',confirmLabel:'التالي',onSubmit:async first=>{
    pinPad({title:'أكّد الرقم',sub:ROLES[k].label,confirmLabel:'حفظ',onSubmit:async second=>{if(second!==first){sheetErr('الرقمين مش متطابقين. جرّب تاني');setTimeout(()=>{if(sheet)setPinFlow(k)},1200);return false}
      sec().pins[k]=await hashPin(first);if(!save())return false;toast('تم حفظ رقم '+ROLES[k].label);managePins()}})}})}

/* ================= Navigation ================= */
function tabSet(k,opts={}){tab=k;document.querySelectorAll('.tab').forEach(b=>{if(b.dataset.tab===k)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current')});['machine','orders','plan','reports','more'].forEach(x=>$('scr-'+x).classList.toggle('hidden',x!==k));if(!opts.keepScroll)window.scrollTo({top:0});render()}
function roleSet(r,goHome=false){role=r;prefs.role=r;savePrefs();if(r==='finance'&&goHome)orderFilter='pending_invoice';else if(goHome)orderFilter='all';if(goHome)tabSet(ROLES[r].home);else render()}
function renderChrome(){
  const [t,s]=TITLES[tab];$('screenTitle').textContent=t;$('screenSub').textContent=s;$('roleLabel').textContent=ROLES[role].label;
  $('fabNew').classList.toggle('hidden',!(tab==='orders'&&role==='manager'));
  const due=role==='operator'?state.orders.filter(canFinish).length:state.orders.filter(o=>(role==='manager'&&canDeliver(o))||canInvoice(o)).length;
  $('ordersBadge').textContent=due;$('ordersBadge').classList.toggle('hidden',!due);
  if(due)$('ordersBadge').setAttribute('aria-label',due+' بانتظار إجراء');
  renderLiveStrip();
}
function renderLiveStrip(){const s=live(),show=!!s&&tab!=='machine';document.body.classList.toggle('has-live',show);$('liveStrip').classList.toggle('hidden',!show);if(!show){$('liveStrip').innerHTML='';return}
  const o=order(s.orderId),seg=s.segments.at(-1),on=seg.type==='run';
  $('liveStrip').innerHTML=`<button type="button" data-action="goMachine" aria-label="فتح عداد الماكينة">${miniDial()}<span class="t"><b>${esc(o?.name||s.orderId)}</b><span>${on?'شغل جارٍ':'عطل على الورشة'} · ${esc(s.operator)}</span></span><span class="clock" id="liveStripClock">${clockText(now()-s.startAt)}</span></button>`;tickLive()}
function render(){renderChrome();({machine:renderMachine,orders:renderOrders,plan:renderPlan,reports:renderReport,more:renderMore})[tab]()}

/* ================= Dial indicator ================= */
function buildDial(){const C=150,s=[];
  s.push(`<circle class="bezel" cx="150" cy="150" r="147" stroke-width="1"/><circle class="face" cx="150" cy="150" r="138"/>`);
  for(let i=0;i<60;i++){const a=i*Math.PI/30,maj=i%5===0,r1=134,r2=maj?119:127;s.push(`<line class="tk${maj?' maj':''}" x1="${(C+r1*Math.sin(a)).toFixed(2)}" y1="${(C-r1*Math.cos(a)).toFixed(2)}" x2="${(C+r2*Math.sin(a)).toFixed(2)}" y2="${(C-r2*Math.cos(a)).toFixed(2)}"/>`);if(maj)s.push(`<text class="lbl" x="${(C+105*Math.sin(a)).toFixed(2)}" y="${(C-105*Math.cos(a)).toFixed(2)}">${i}</text>`)}
  s.push(`<circle class="sub" cx="150" cy="98" r="22" stroke-width="1"/>`);
  for(let i=0;i<12;i++){const a=i*Math.PI/6,maj=i%3===0,r2=maj?14:17;s.push(`<line class="subtk" x1="${(150+21*Math.sin(a)).toFixed(2)}" y1="${(98-21*Math.cos(a)).toFixed(2)}" x2="${(150+r2*Math.sin(a)).toFixed(2)}" y2="${(98-r2*Math.cos(a)).toFixed(2)}"/>`)}
  s.push(`<g class="cneedle" id="cneedle"><path d="M149 98 L150 81 L151 98 Z"/><circle cx="150" cy="98" r="2.6"/></g>`);
  s.push(`<text class="unit" x="150" y="206">دقيقة</text><text class="unit" x="150" y="68">ساعة</text>`);
  s.push(`<g class="needle" id="needle"><path d="M148.4 172 L149.3 24 Q150 19 150.7 24 L151.6 172 Z"/><circle cx="150" cy="172" r="4.5"/></g><circle class="cap" cx="150" cy="150" r="9"/><circle class="cap2" cx="150" cy="150" r="3"/>`);
  $('dial').insertAdjacentHTML('beforeend',s.join(''));
}
function miniDial(){let t='';for(let i=0;i<12;i++){const a=i*Math.PI/6;t+=`<line x1="${(20+17*Math.sin(a)).toFixed(1)}" y1="${(20-17*Math.cos(a)).toFixed(1)}" x2="${(20+(i%3?14.5:12.5)*Math.sin(a)).toFixed(1)}" y2="${(20-(i%3?14.5:12.5)*Math.cos(a)).toFixed(1)}" stroke="currentColor" stroke-width="1"/>`}
  const s=live(),fault=s&&s.segments.at(-1).type==='stop';
  return `<svg class="mini-dial" viewBox="0 0 40 40" aria-hidden="true" style="color:var(--ink-2)"><circle cx="20" cy="20" r="19" fill="var(--face-2)" stroke="var(--rule)"/>${t}<g id="miniNeedle" style="transform-origin:20px 20px;transition:transform .7s var(--ease)"><path d="M19.1 22 L20 5 L20.9 22 Z" fill="${fault?'var(--fault)':'var(--accent)'}" stroke="var(--ink)" stroke-width=".6" stroke-linejoin="round"/></g><circle cx="20" cy="20" r="2.5" fill="var(--ink)"/></svg>`}
function clockText(ms){const t=Math.max(0,Math.floor(ms/1000)),h=Math.floor(t/3600),m=Math.floor(t%3600/60);return `${h}:${pad(m)}`}
let dialPrimed=false;
function setDial(ms,stateCls){const d=$('dial');d.classList.remove('idle','fault');if(stateCls)d.classList.add(stateCls);
  const n=$('needle'),c=$('cneedle');if(!n)return;
  if(!dialPrimed){n.style.transition='none';c.style.transition='none'}
  n.style.transform=`rotate(${(ms/60000*6).toFixed(2)}deg)`;c.style.transform=`rotate(${(ms/MS_H*30).toFixed(2)}deg)`;
  if(!dialPrimed){requestAnimationFrame(()=>{n.style.transition='';c.style.transition=''});dialPrimed=true}
  const t=Math.max(0,Math.floor(ms/1000));$('clock').innerHTML=`<b>${clockText(ms)}</b><span>:${pad(t%60)}</span>`}
function tickLive(){const s=live();if(!s)return;const ms=now()-s.startAt;
  if(tab==='machine')setDial(ms,s.segments.at(-1).type==='stop'?'fault':'');
  const lc=$('liveStripClock');if(lc)lc.textContent=clockText(ms);
  const mn=$('miniNeedle');if(mn)mn.style.transform=`rotate(${(ms/60000*6).toFixed(1)}deg)`}

/* ================= Machine screen ================= */
const draft={operator:'',orderId:'',editTime:false};
function ro(label,value,em=''){return `<div class="ro"><small>${esc(label)}</small><b>${esc(value)}</b>${em?`<em>${esc(em)}</em>`:''}</div>`}
function renderMachine(){
  const s=live(),today=localDay(now());
  $('machineIdle').classList.toggle('hidden',!!s);$('machineActive').classList.toggle('hidden',!s);
  if(s){
    const o=order(s.orderId),p=s.segments.at(-1),sum=totals(s),on=p.type==='run';
    $('machineState').innerHTML=`<span class="stateplate ${on?'run':'fault'}"><i aria-hidden="true"></i>${on?'شغل جارٍ: تجهيز أو تشغيل':'متوقفة: عطل على الورشة'}</span>`;
    $('clockCap').textContent=`مدة الفترة منذ ${localTime(s.startAt)} · ${prettyDay(localDay(s.startAt))}`;
    setDial(now()-s.startAt,on?'':'fault');
    $('activeReadouts').innerHTML=`<div class="readouts">${ro('وقت الشغل',humanMs(sum.run))}${ro('عطل الورشة',humanMs(sum.stop))}${ro('وقت المشغّل',humanMs(sum.operator),'منها معالجة '+humanMs(sum.repair))}</div>`;
    $('machineActive').innerHTML=`<div class="card card-pad" style="display:flex;flex-direction:column;gap:14px">
      <div><h2 style="font-size:19px;font-weight:600;line-height:1.4">${esc(o?.name||'')}</h2><p class="help">${esc(o?.client||'')} · ${esc(s.operator)} · <span class="idtxt">${esc(o?.id||'')}</span></p></div>
      ${!on?`<div class="note">${ic('warning')}<div>عطل غير محمّل على العميل: <b>${esc(p.reason||'')}</b><br>${handling(p)?'المشغّل يعالج العطل ويُحسب له الوقت.':'لا تُحسب ساعات للمشغّل أثناء التوقف.'}</div></div>`:''}
      ${role==='finance'?'<p class="help">شاشة متابعة فقط. التحكم في العداد للمشغّل والمدير.</p>':`<div class="keys">
        ${on?`<button class="btn fault xl wide" type="button" id="pauseBtn">${ic('pause')}تسجيل عطل</button>`:`<button class="btn primary xl wide" type="button" id="resumeBtn">${ic('play')}استكمال الشغل</button>`}
        <button class="btn" type="button" id="handoffBtn">${ic('arrows-left-right')}تغيير المشغّل</button>
        <button class="btn ink" type="button" id="endBtn">${ic('stop')}إنهاء الفترة</button></div>`}
    </div>`;
    const pb=$('pauseBtn'),rb=$('resumeBtn');if(pb)pb.onclick=pauseSession;if(rb)rb.onclick=resumeSession;if($('endBtn'))$('endBtn').onclick=endSession;if($('handoffBtn'))$('handoffBtn').onclick=handoffSession;
  }else{
    $('machineState').innerHTML=`<span class="stateplate"><i aria-hidden="true"></i>الماكينة متاحة</span>`;
    $('clockCap').textContent=role==='finance'?'لا يوجد تشغيل الآن.':'اختر أمر الشغل والمشغّل للبدء.';
    setDial(0,'idle');$('activeReadouts').innerHTML='';
    const names=unique(state.sessions.map(x=>x.operator)).filter(Boolean);
    $('operatorList').innerHTML=names.map(x=>`<option value="${esc(x)}">`).join('');
    const recent=unique([...state.sessions].sort((a,b)=>b.startAt-a.startAt).map(x=>x.operator)).filter(Boolean).slice(0,4);
    $('operatorChips').innerHTML=recent.map(n=>`<button type="button" class="chip" data-op="${esc(n)}" aria-pressed="${draft.operator===n}">${esc(n)}</button>`).join('');
    if($('operator').value!==draft.operator&&document.activeElement!==$('operator'))$('operator').value=draft.operator;
    const opts=state.orders.filter(activeOption).sort((a,b)=>priorities(a)-priorities(b)||a.due.localeCompare(b.due));
    if(!opts.some(o=>o.id===draft.orderId))draft.orderId=opts[0]?.id||'';
    $('orderPick').innerHTML=opts.length?opts.map(o=>{const left=Math.max(0,o.estimate-sumOrder(o.id)/MS_H);return `<button type="button" class="pick" role="radio" aria-checked="${draft.orderId===o.id}" data-pick="${esc(o.id)}"><span class="radio" aria-hidden="true"></span><span class="t"><b>${esc(o.name)}</b><span>${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span></span></span><span class="tag ${o.priority==='عاجل'?'urgent':''}"><span class="num">${hrs(left)}</span>&nbsp;س متبقية</span></button>`}).join(''):`<div class="empty" style="padding:16px">${ic('clipboard-text','lg')}<b>لا توجد أوامر مفتوحة</b><p>${role==='manager'?'أنشئ أمر شغل من تبويب «الأوامر».':'اطلب من مدير الورشة فتح أمر شغل.'}</p></div>`;
    $('startBtn').disabled=!opts.length||role==='finance';
    $('startBtn').classList.toggle('hidden',role==='finance');
    if(!draft.editTime){$('workDay').value=today;$('workStart').value=localTime(now())}
    $('startSummary').innerHTML=draft.editTime?'وقت بدء مخصص':`يبدأ الآن · <span class="num">${localTime(now())}</span>`;
    $('startFields').classList.toggle('hidden',!draft.editTime);$('editStart').setAttribute('aria-expanded',draft.editTime);
  }
  const rows=dayRows(today),t=rows.reduce((a,x)=>({run:a.run+x.run,stop:a.stop+x.stop,repair:a.repair+x.repair,operator:a.operator+x.operator}),{run:0,stop:0,repair:0,operator:0});
  $('todayTotals').innerHTML=ro('وقت الشغل',humanMs(t.run))+ro('عطل الورشة',humanMs(t.stop))+ro('وقت المشغّلين',humanMs(t.operator),'منه معالجة '+humanMs(t.repair));
}
function startSession(){
  if(role==='finance')return toast('غير مسموح للحسابات بتسجيل تشغيل');if(live())return toast('يوجد تشغيل مفتوح على الماكينة');
  const operatorName=$('operator').value.trim(),orderId=draft.orderId,o=order(orderId);
  const day=draft.editTime?$('workDay').value:localDay(now()),time=draft.editTime?$('workStart').value:localTime(now());
  if(!operatorName){$('operator').focus();return toast('اكتب اسم المشغّل')}
  if(!o||!activeOption(o))return toast('اختر أمر شغل مفتوح');if(!day||!time)return toast('حدد وقت البداية');
  const start=draft.editTime?new Date(day+'T'+time+':00').getTime():now();
  if(!Number.isFinite(start)||start>now()+60000||now()-start>48*MS_H)return toast('وقت البداية يجب أن يكون خلال آخر 48 ساعة وليس في المستقبل');
  if(overlap(start,now()+1))return toast('تعارض مع تشغيل مسجل للماكينة في نفس الوقت');
  state.sessions.push({id:makeId(),orderId,operator:operatorName,startAt:start,endAt:null,segments:[{type:'run',startAt:start,endAt:null}],createdAt:now()});
  o.status='بدء';if(!o.startedAt)o.startedAt=start;draft.editTime=false;draft.operator=operatorName;save();render();window.scrollTo({top:0,behavior:'smooth'});toast('بدأ تشغيل '+o.id);
}
function pauseSession(){const s=live();if(!s||s.segments.at(-1)?.type!=='run')return toast('لا يوجد تشغيل حالي لإيقافه');
  openSheet({title:'تسجيل عطل على الورشة',sub:'للأعطال والصيانة التي لا يتحملها العميل فقط',body:`<div class="note info">${ic('info')}<div>التجهيز والضبط والقياس العادي يظل ضمن وقت الشغل.</div></div>
    <div class="field"><span class="label" id="reasonLbl">سبب العطل</span><div class="pickgroup" role="radiogroup" aria-labelledby="reasonLbl" id="reasonPick">${['عطل ماكينة','كسر أو تلف عدة القطع','صيانة / إصلاح','مشكلة كهرباء أو تبريد','سبب آخر على الورشة'].map(r=>`<button type="button" class="pick" role="radio" aria-checked="false" data-reason="${esc(r)}"><span class="radio" aria-hidden="true"></span><span class="t"><b>${esc(r)}</b></span></button>`).join('')}</div></div>
    <div class="field"><label for="stopNote">توضيح إضافي (اختياري)</label><input id="stopNote" maxlength="120" placeholder="وصف مختصر للسبب"></div>
    <label class="check"><input id="present" type="checkbox"> المشغّل يصلح العطل الآن (يُحسب له الوقت)</label>`,
    foot:`<button class="btn fault xl block" type="button" id="pauseConfirm">${ic('pause')}حفظ العطل وإيقاف العداد</button>`});
  let reason='';$('reasonPick').onclick=e=>{const b=e.target.closest('[data-reason]');if(!b)return;reason=b.dataset.reason;$('reasonPick').querySelectorAll('[data-reason]').forEach(x=>x.setAttribute('aria-checked',x===b))};
  $('pauseConfirm').onclick=()=>{if(!reason)return sheetErr('اختر سبب العطل',$('reasonPick').querySelector('button'));const t=now();try{closeSeg(s,t)}catch(e){return sheetErr(e.message)}const note=$('stopNote').value.trim();s.segments.push({type:'stop',startAt:t,endAt:null,reason:reason+(note?' - '+note:''),working:$('present').checked});save();closeSheet();render();toast('تم تسجيل العطل. مدته لا تُحمّل على العميل')}}
function resumeSession(){const s=live();if(!s||s.segments.at(-1)?.type!=='stop')return toast('الماكينة ليست في حالة توقف');const t=now();try{closeSeg(s,t)}catch(e){return toast(e.message)}s.segments.push({type:'run',startAt:t,endAt:null});save();render();toast('تم استكمال الشغل')}
function endSession(){const s=live();if(!s)return toast('لا توجد فترة مفتوحة');const t=now(),o=order(s.orderId),tt=totals(s,t);if(t<=s.startAt)return toast('وقت النهاية يجب أن يكون بعد بداية العمل');
  openSheet({title:'إنهاء فترة التشغيل',sub:`${esc(o?.name||'')} · ${esc(s.operator)}`,body:`<div class="card" style="box-shadow:none"><div class="readouts two" style="border-top:0">${ro('وقت الشغل',humanMs(tt.run),'يشمل التجهيز')}${ro('التوقفات',humanMs(tt.stop),'منها معالجة '+humanMs(tt.repair))}</div><div class="readouts two">${ro('ساعات المشغّل',humanMs(tt.operator))}${ro('إجمالي الأمر حتى الآن',humanMs(sumOrder(o.id)))}</div></div><p class="help">إنهاء الفترة لا يعني انتهاء أمر الشغل. يمكن استكمال نفس الأمر في يوم آخر.</p>`,
    foot:`<button class="btn primary block" type="button" id="confirmPeriod">${ic('check')}حفظ الفترة فقط</button><button class="btn ink block" type="button" id="confirmFinishToo">${ic('flag-checkered')}حفظ الفترة وإنهاء أمر الشغل</button>`});
  function commit(finish){const tm=now();try{closeSeg(s,tm)}catch(e){return sheetErr(e.message)}s.endAt=tm;if(finish){if(totals(s).run+sumOrder(o.id)<=0){s.endAt=null;s.segments.at(-1).endAt=null;return sheetErr('لا يمكن إنهاء الأمر بدون تشغيل فعلي')}o.status='انتهاء';o.completedAt=tm}save();closeSheet();render();toast(finish?'تم إنهاء الشغل. الأمر جاهز للتسليم':'تم حفظ الفترة. أمر الشغل ما زال مفتوحًا')}
  $('confirmPeriod').onclick=()=>commit(false);$('confirmFinishToo').onclick=()=>commit(true)}
function handoffSession(){const s=live();if(!s)return toast('لا يوجد أمر جارٍ لتسليمه');const last=s.segments.at(-1),latest=last.startAt;const options=unique(state.sessions.map(x=>x.operator).filter(x=>x&&x!==s.operator));
  openSheet({title:'تغيير المشغّل',sub:'بدون إيقاف عداد الماكينة',body:`<div class="calc">الأمر: <b style="font-family:var(--font-ui)">${esc(order(s.orderId)?.name||s.orderId)}</b><br>المشغّل الحالي: <b style="font-family:var(--font-ui)">${esc(s.operator)}</b><br>إجمالي ساعات أمر الشغل لن يتكرر.</div>
    <div class="field"><label for="nextOperator">اسم المشغّل الجديد</label><input id="nextOperator" list="handoffNames" placeholder="اكتب اسم المشغّل" maxlength="80"><datalist id="handoffNames">${options.map(x=>`<option value="${esc(x)}">`).join('')}</datalist>${options.length?`<div class="namechips">${options.slice(0,4).map(n=>`<button type="button" class="chip" data-fill="${esc(n)}">${esc(n)}</button>`).join('')}</div>`:''}</div>
    <div class="fgrid"><div class="field"><label for="handoffDay">تاريخ الاستلام</label><input id="handoffDay" type="date" value="${localDay(now())}"></div><div class="field"><label for="handoffTime">وقت الاستلام</label><input id="handoffTime" type="time" value="${localTime(now())}"></div></div>
    ${last.type==='stop'?'<label class="check"><input type="checkbox" id="handoffRepair"> المشغّل الجديد يعالج العطل (تُحسب له ساعات معالجة)</label>':''}
    <p class="help">لو نسيت التغيير، سجّل وقت الاستلام الحقيقي. لا يمكن الرجوع لما قبل آخر تغيير تشغيل أو توقف مسجل.</p>`,
    foot:`<button class="btn primary block" type="button" id="confirmHandoff">${ic('arrows-left-right')}تأكيد تغيير المشغّل</button>`,focus:'#nextOperator'});
  sheet.el.querySelectorAll('[data-fill]').forEach(b=>b.onclick=()=>{$('nextOperator').value=b.dataset.fill});
  $('confirmHandoff').onclick=()=>{const next=$('nextOperator').value.trim();if(!next||next===s.operator)return sheetErr('اكتب اسم مشغّل مختلف',$('nextOperator'));const d=$('handoffDay').value,t=$('handoffTime').value;if(!d||!t)return sheetErr('اختر وقت الاستلام');const[y,m,dd]=d.split('-').map(Number),[h,mm]=t.split(':').map(Number),at=(d===localDay(now())&&t===localTime(now()))?now():new Date(y,m-1,dd,h,mm).getTime();
    if(!Number.isFinite(at)||at<=s.startAt||at<latest)return sheetErr('وقت الاستلام يجب أن يكون بعد بداية الفترة وآخر حركة مسجلة',$('handoffTime'));
    if(role!=='manager'&&(d!==localDay(now())||t!==localTime(now())))return sheetErr('تصحيح وقت قديم يحتاج مدير الورشة',$('handoffTime'));
    if(at>now()+60000)return sheetErr('وقت الاستلام لا يمكن أن يكون في المستقبل',$('handoffTime'));
    if(overlap(at,now(),s.id))return sheetErr('وقت الاستلام يتداخل مع فترة تشغيل أخرى',$('handoffTime'));
    const oldType=last.type,oldReason=last.reason;try{closeSeg(s,at)}catch(e){return sheetErr(e.message)}s.endAt=at;
    const g=oldType==='run'?{type:'run',startAt:at,endAt:null}:{type:'stop',startAt:at,endAt:null,reason:oldReason,working:!!$('handoffRepair')?.checked};
    state.sessions.push({id:makeId(),orderId:s.orderId,operator:next,startAt:at,endAt:null,segments:[g],handoffFrom:s.operator});save();closeSheet();render();toast('تم تسليم الوردية إلى '+next+' دون إيقاف أمر الشغل')}}

/* ================= Orders ================= */
let orderFilter='all';
const FILTERS=[['all','الكل',()=>true],['open','مفتوحة',o=>activeOption(o)],['معلق','معلق',o=>o.status==='معلق'],['بدء','قيد التشغيل',o=>o.status==='بدء'],['انتهاء','جاهز للتسليم',o=>o.status==='انتهاء'],['تسليم','استلمه العميل',o=>o.status==='تسليم'],['pending_invoice','فاتورة مطلوبة',o=>o.status==='تسليم'&&!invoiceOf(o.id)],['invoiced','صدرت الفاتورة',o=>!!invoiceOf(o.id)],['balance_due','متبقي على العميل',o=>{const p=payState(o);return p.invoiced&&p.balance>0.004}],['paid','مدفوعة بالكامل',o=>['paid','over'].includes(payState(o).status)]];
const MONEY_FILTERS=['balance_due','paid'];
function scaleHTML(o){const est=Math.max(0,Number(o.estimate)||0),act=sumOrder(o.id)/MS_H,R=Math.max(est,act,.25);
  const steps=[.25,.5,1,2,5,10,20,50,100];const step=steps.find(s=>R/s<=24)||200;const majEvery=step<1?Math.round(1/step):5;
  let t='';for(let v=0,i=0;v<=R+1e-9;v+=step,i++){t+=`<i class="${i%majEvery===0?'maj':''}" style="inset-inline-start:${(v/R*100).toFixed(2)}%"></i>`}
  const runningNow=live()?.orderId===o.id,fillW=Math.min(act,est)/R*100;
  const over=act>est+1e-6?`<span class="over" style="inset-inline-start:${(est/R*100).toFixed(2)}%;width:${((act-est)/R*100).toFixed(2)}%"></span>`:'';
  const label=`${act.toFixed(2)} من ${hrs(est)} س`;
  return `<div class="scale" role="img" aria-label="الساعات الفعلية ${act.toFixed(2)} من المقدر ${hrs(est)} ساعة"><span class="base"></span>${t}<i class="end" style="inset-inline-start:${(est/R*100).toFixed(2)}%"></i><span class="fill ${runningNow?'live':''}" style="inset-inline-start:0;width:${fillW.toFixed(2)}%"></span>${over}<span class="lab s">${label}</span>${act>est+1e-6?`<span class="lab e" style="color:var(--accent-text)">زيادة ${(act-est).toFixed(2)} س عن المقدر</span>`:''}</div>`}
function nextAction(o){const inv=invoiceOf(o.id),runningHere=live()?.orderId===o.id;
  const owes=inv&&payState(o).balance>0.004;
  if(role==='manager'){if(canDeliver(o))return['deliver','استلام العميل','package','primary'];if(canInvoice(o))return['invoice','إصدار فاتورة','receipt','primary'];if(canFinish(o))return['finish','إنهاء الأمر','flag-checkered','ink'];if(activeOption(o))return runningHere?['goMachine','عرض العداد','gauge','']:['work','تشغيل','play',''];if(owes)return['pay','تسجيل دفعة','money','primary'];if(inv&&inv.issuedInternally)return['editInvoice','الفاتورة','receipt',''];if(o.status==='تسليم')return['dispatch','إذن تسليم','printer','']}
  if(role==='operator'){if(canFinish(o))return['finish','إنهاء الأمر','flag-checkered','ink'];if(activeOption(o))return runningHere?['goMachine','عرض العداد','gauge','']:['work','تشغيل','play','primary']}
  if(role==='finance'){if(canInvoice(o))return['invoice','إصدار فاتورة','receipt','primary'];if(owes)return['pay','تسجيل دفعة','money','primary'];if(inv&&inv.issuedInternally)return['editInvoice','الفاتورة / طباعة','printer','']}
  return null}
function invoicePill(o){const inv=invoiceOf(o.id);if(inv)return `<span class="pill billed">${ic('check')}فاتورة <span class="idtxt" style="color:inherit">${esc(inv.number)}</span></span>`;if(o.status==='تسليم')return `<span class="pill billdue">${ic('receipt')}فاتورة مطلوبة</span>`;return ''}
function payPill(o){const p=payState(o);
  if(p.invoiced){if(p.status==='paid')return `<span class="pill billed">${ic('check')}مدفوعة بالكامل</span>`;if(p.status==='over')return `<span class="pill done">${ic('info')}مدفوع زيادة <span class="num">${money(-p.balance)}</span></span>`;return `<span class="pill billdue">${ic('money')}متبقي <span class="num">${money(p.balance)}</span></span>`}
  if(p.paid>0)return `<span class="pill pending">${ic('money')}مقدم مدفوع <span class="num">${money(p.paid)}</span></span>`;
  if(o.payTerms==='split'&&o.advance>0)return `<span class="pill pending">${ic('money')}مقدم مطلوب <span class="num">${money(o.advance)}</span></span>`;
  return ''}
function paymentsBlock(o){const p=payState(o),list=paymentsOf(o),left=Math.max(0,r2(p.due-p.paid));
  const terms=o.payTerms==='split'?`مقدم وباقي${o.advance>0?` · المقدم المتفق عليه <span class="num">${money(o.advance)}</span>`:''}`:'دفعة واحدة';
  return `<div class="card" style="box-shadow:none"><div class="card-pad" style="padding-bottom:10px"><div class="section-h" style="margin:0;align-items:flex-start"><div><h2 style="font-size:16px">المدفوعات</h2><p class="help">${terms}</p></div>${payPill(o)}</div></div>
    <div class="readouts money">${ro(p.invoiced?'قيمة الفاتورة':'القيمة التقديرية',money(p.due))}${ro('المدفوع',money(p.paid))}${ro(p.invoiced?'المتبقي':'المتبقي تقديريًا',money(left))}</div>
    ${list.length?`<div class="paylist">${[...list].sort((a,b)=>b.date.localeCompare(a.date)||b.at-a.at).map(x=>`<div class="payrow"><div class="t"><b class="num">${money(x.amount)}</b><span>${esc(x.kind||'دفعة')} · ${esc(x.method)} · ${esc(prettyDay(x.date))}</span><span><span class="idtxt">${esc(x.number||'')}</span>${x.note?` · ${esc(x.note)}`:''}</span></div><button type="button" class="iconbtn" data-action="receipt" data-id="${esc(o.id)}" data-pid="${esc(x.id)}" aria-label="طباعة إيصال ${esc(x.number||'')}">${ic('printer')}</button><button type="button" class="iconbtn" data-action="voidPay" data-id="${esc(o.id)}" data-pid="${esc(x.id)}" aria-label="إلغاء الدفعة ${esc(x.number||'')}">${ic('x')}</button></div>`).join('')}</div>`:`<p class="help" style="padding:12px 16px;border-top:1px solid var(--rule-soft)">لا توجد دفعات مسجلة بعد.</p>`}</div>`}
function renderOrders(){
  const data=state.orders,open=data.filter(activeOption).length,finished=data.filter(o=>o.status==='انتهاء').length,missing=data.filter(o=>o.status==='تسليم'&&!invoiceOf(o.id)).length,h=state.sessions.reduce((n,s)=>n+totals(s).run,0);
  const statBtn=(f,label,value,sub)=>`<button type="button" class="ro" data-filter="${f}" aria-pressed="${orderFilter===f}"><small>${label}</small><b>${value}</b><em>${sub}</em></button>`;
  if(role==='operator'&&MONEY_FILTERS.includes(orderFilter))orderFilter='all';
  const out=outstandingOrders();
  $('orderStats').innerHTML=statBtn('open','أوامر مفتوحة',open,'معلق + قيد التشغيل')+statBtn('انتهاء','جاهز للتسليم',finished,'انتهى التشغيل')+statBtn('pending_invoice','استلام بلا فاتورة',missing,'مطلوبة من الحسابات')+(role==='operator'?`<div class="ro"><small>وقت شغل مسجّل</small><b>${humanMs(h)}</b><em>شامل التجهيز</em></div>`:statBtn('balance_due','مستحق على العملاء',money(out.reduce((n,o)=>n+payState(o).balance,0)),out.length+' فاتورة غير مسددة'));
  $('orderChips').innerHTML=FILTERS.filter(([k])=>role!=='operator'||!MONEY_FILTERS.includes(k)).map(([k,l,f])=>`<button type="button" class="chip" data-filter="${esc(k)}" aria-pressed="${orderFilter===k}">${esc(l)}<span class="n">${data.filter(f).length}</span></button>`).join('');
  const search=$('search').value.trim().toLowerCase(),fn=(FILTERS.find(x=>x[0]===orderFilter)||FILTERS[0])[2];
  const rows=data.filter(o=>fn(o)&&[o.name,o.client,o.id].some(x=>String(x).toLowerCase().includes(search))).sort((a,b)=>(a.status==='تسليم'&&!invoiceOf(a.id)?0:1)-(b.status==='تسليم'&&!invoiceOf(b.id)?0:1)||priorities(a)-priorities(b)||a.due.localeCompare(b.due));
  const today=localDay(now());
  $('orderList').innerHTML=rows.length?rows.map(o=>{const overdue=o.due<today&&activeOption(o),act=nextAction(o);
    return `<article class="ocard"><button type="button" class="ocard-head" data-action="openOrder" data-id="${esc(o.id)}"><span class="ocard-title"><b>${esc(o.name)}</b><span>${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span></span></span>${pill(o.status)}</button>
      <div class="ocard-body">${scaleHTML(o)}<div class="meta"><span class="tag ${overdue?'late':''}">${ic(overdue?'warning':'calendar-blank','sm')}${overdue?'متأخر · ':''}${esc(prettyDay(o.due))}</span><span class="tag ${o.priority==='عاجل'?'urgent':''}">${esc(o.priority)}</span>${role!=='operator'?`<span class="tag"><span class="num">${money(o.price)}</span>&nbsp;${o.pricing==='hour'?'للساعة':'للقطعة'}</span>`:''}${invoicePill(o)}${role!=='operator'?payPill(o):''}</div></div>
      <div class="ocard-foot">${act?`<button type="button" class="btn sm ${act[3]}" data-action="${act[0]}" data-id="${esc(o.id)}">${ic(act[2],'sm')}${esc(act[1])}</button>`:''}<button type="button" class="btn sm quiet" data-action="openOrder" data-id="${esc(o.id)}" ${act?'':'style="flex:1"'}>التفاصيل${ic('caret-left','sm')}</button></div></article>`}).join('')
    :data.length?`<div class="card empty">${ic('magnifying-glass','lg')}<b>لا توجد أوامر بهذا البحث</b><p>غيّر التصفية أو كلمة البحث.</p><button type="button" class="btn sm" data-filter="all" id="clearFilter">عرض الكل</button></div>`
    :`<div class="card empty">${ic('clipboard-text','lg')}<b>لا توجد أوامر بعد</b><p>المسار: أمر شغل، ثم تشغيل على الماكينة، ثم انتهاء، ثم استلام العميل، ثم الفاتورة.</p>${role==='manager'?`<div class="keys" style="width:100%"><button type="button" class="btn primary" data-action="newOrder">${ic('plus')}أمر شغل</button><button type="button" class="btn" data-action="demo">بيانات للتجربة</button></div>`:'<p>مدير الورشة يفتح أوامر الشغل.</p>'}</div>`;
}
function rulerHTML(o){const inv=invoiceOf(o.id);const st=[['أمر شغل',o.createdAt,true],['تشغيل',o.startedAt,o.status!=='معلق'],['انتهاء',o.completedAt,['انتهاء','تسليم'].includes(o.status)],['استلام العميل',o.deliveredAt,o.status==='تسليم'],['فاتورة',inv?toDate(inv.date).getTime():null,!!inv]];
  const cur=st.reduce((n,x,i)=>x[2]?i:n,0);
  return `<div class="ruler" role="list" aria-label="مسار أمر الشغل"><span class="jaw" style="width:${(cur*20)}%"></span>${st.map((x,i)=>`<div class="st ${x[2]?'on':''} ${i===cur?'cur':''}" role="listitem">${esc(x[0])}${x[1]?`<small>${(d=>d.getDate()+'/'+(d.getMonth()+1))(new Date(x[1]))}</small>`:''}</div>`).join('')}</div>`}
function openOrder(id){const o=order(id);if(!o)return;const tt=orderTotals(id),inv=invoiceOf(id),f=activeOption(o)?plannedFinish(id):'',a=[];
  const A=(act,label,icon,cls='')=>a.push(`<button type="button" class="btn sm ${cls}" data-action="${act}" data-id="${esc(id)}">${ic(icon,'sm')}${esc(label)}</button>`);
  const runningHere=live()?.orderId===id;
  if(role==='manager'){if(canDeliver(o))A('deliver','استلام العميل','package','primary');if(activeOption(o))A('edit','تعديل الأمر','pencil-simple');if(activeOption(o))A('planEdit','تعديل الخطة','calendar-blank');if(o.status==='تسليم')A('dispatch','إذن تسليم','printer')}
  if(role!=='finance'){if(canFinish(o))A('finish','إنهاء الأمر','flag-checkered','ink');if(activeOption(o))A(runningHere?'goMachine':'work',runningHere?'عرض العداد':'تشغيل','play')}
  if(role!=='operator'){if(canInvoice(o))A('invoice','إصدار فاتورة','receipt','primary');A('pay','تسجيل دفعة','money',inv&&payState(o).balance>0.004?'primary':'');if(inv&&inv.issuedInternally)A('editInvoice','الفاتورة / طباعة','printer')}
  if(o.fileName)A('file','الرسم المرفق','paperclip');
  openSheet({title:o.name,sub:`${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span>`,body:`${rulerHTML(o)}
    <div class="card" style="box-shadow:none">${scaleHTML(o).replace('class="scale"','class="scale" style="margin:14px 14px 6px"')}<div class="readouts">${ro('ساعات الشغل',humanMs(tt.run))}${ro('أعطال الورشة',humanMs(tt.stop))}${ro('المشغّلين',humanMs(tt.operator))}</div></div>
    <div class="infolist">
      <div><small>الحالة</small>${pill(o.status)}</div>
      <div><small>موعد العميل</small><span>${esc(prettyDay(o.due))}</span></div>
      ${f?`<div><small>الانتهاء حسب الخطة</small><span>${esc(prettyDay(f))}</span></div>`:''}
      <div><small>الأولوية</small><span>${esc(o.priority)}</span></div>
      ${role!=='operator'?`<div><small>التسعير</small><span>${o.pricing==='hour'?'بالساعة':'بالقطعة'} · <span class="num">${money(o.price)}</span></span></div>${o.pricing!=='hour'?`<div><small>الكمية</small><span class="num">${esc(o.qty)} قطعة</span></div>`:''}`:''}
      <div><small>الخامة</small><span>${esc(o.material||'')}</span></div>
      ${o.receivedBy?`<div><small>المستلم</small><span>${esc(o.receivedBy)}</span></div>`:''}
      ${inv?`<div><small>الفاتورة</small><span class="idtxt" style="color:var(--ink)">${esc(inv.number)}</span>${inv.revision>1?`<small>مراجعة ${Number(inv.revision)}</small>`:''}</div>`:''}
    </div>
    ${role!=='operator'?paymentsBlock(o):''}
    ${a.length?`<div class="actgrid">${a.join('')}</div>`:'<p class="help">لا توجد إجراءات متاحة لهذا الدور على الأمر الآن.</p>'}`})}
function openOrderForm(id){if(role!=='manager')return;const o=order(id);if(o&&!activeOption(o))return toast('الأمر منتهٍ أو مُسلّم؛ لا يمكن تعديل بياناته');
  const f=o||{name:'',client:'',estimate:'',priority:'عادي',due:localDay(now()),pricing:'fixed',price:'',qty:1,material:'حسب الأمر',fileName:'',payTerms:'single',advance:''};
  openSheet({title:o?'تعديل أمر الشغل':'أمر شغل جديد',sub:o?`<span class="idtxt">${esc(o.id)}</span>`:'',body:`<form id="orderForm" class="fgrid" novalidate>
    <div class="field full"><label for="f-name">اسم الشغلانة</label><input id="f-name" name="name" required maxlength="180" value="${esc(f.name)}"></div>
    <div class="field full"><label for="f-client">اسم العميل</label><input id="f-client" name="client" required maxlength="150" value="${esc(f.client)}" autocomplete="off" list="clientList"><datalist id="clientList">${unique(state.orders.map(x=>x.client)).map(c=>`<option value="${esc(c)}">`).join('')}</datalist></div>
    <div class="field"><label for="f-est">الوقت المقدر (ساعة)</label><input id="f-est" name="estimate" type="number" inputmode="decimal" step="0.25" min="0.25" required value="${esc(f.estimate)}"></div>
    <div class="field"><label for="f-pri">الأولوية</label><select id="f-pri" name="priority">${['عادي','عالي','عاجل'].map(x=>`<option ${f.priority===x?'selected':''}>${x}</option>`).join('')}</select></div>
    <div class="field full"><label for="f-due">اليوم المتوقع للانتهاء</label><input id="f-due" name="due" type="date" required value="${esc(f.due)}"></div>
    <div class="field"><label for="pricing">التسعير</label><select name="pricing" id="pricing"><option value="fixed" ${f.pricing==='fixed'?'selected':''}>بالقطعة</option><option value="hour" ${f.pricing==='hour'?'selected':''}>بالساعة</option></select></div>
    <div class="field"><label for="f-price" id="priceLbl">سعر القطعة (جنيه)</label><input id="f-price" name="price" type="number" inputmode="decimal" step="0.01" min="0" required value="${esc(f.price)}"></div>
    <div class="field" id="qtyBlock"><label for="f-qty">الكمية (قطعة)</label><input id="f-qty" name="qty" type="number" inputmode="numeric" min="1" step="1" required value="${esc(f.qty)}"></div>
    <div class="field"><label for="f-mat">الخامة</label><select id="f-mat" name="material">${['حسب الأمر','خامة العميل','خامة الورشة'].map(x=>`<option ${f.material===x?'selected':''}>${x}</option>`).join('')}</select></div>
    <div class="field"><label for="f-terms">طريقة الدفع</label><select id="f-terms" name="payTerms"><option value="single" ${f.payTerms!=='split'?'selected':''}>دفعة واحدة</option><option value="split" ${f.payTerms==='split'?'selected':''}>مقدم وباقي</option></select></div>
    <div class="field" id="advBlock"><label for="f-adv">قيمة المقدم (جنيه)</label><input id="f-adv" name="advance" type="number" inputmode="decimal" min="0" step="0.01" value="${esc(f.advance||'')}"><span class="hint">اختياري. المتفق عليه مع العميل</span></div>
    <div class="field full"><label for="f-file">ملف الرسم (اختياري)</label><input id="f-file" name="file" type="file" accept=".pdf,.dwg,.dxf,.step,.stp,.igs,.iges,.sldprt,.png,.jpg,.jpeg,.zip,.rar"><span class="hint">${f.fileName?'المرفق الحالي: '+esc(f.fileName):'PDF أو DWG أو DXF أو STEP وغيرها، حتى 25 ميجابايت'}</span></div>
  </form>`,foot:`<button class="btn primary block" type="button" id="saveOrder">${ic('check')}حفظ الأمر</button>`,focus:o?null:'#f-name'});
  const form=$('orderForm'),type=$('pricing'),qty=$('qtyBlock');
  const toggle=()=>{qty.style.display=type.value==='hour'?'none':'';form.querySelector('[name=qty]').required=type.value!=='hour';$('priceLbl').textContent=type.value==='hour'?'سعر الساعة (جنيه)':'سعر القطعة (جنيه)'};type.onchange=toggle;toggle();
  const advToggle=()=>{$('advBlock').style.display=$('f-terms').value==='split'?'':'none'};$('f-terms').onchange=advToggle;advToggle();
  $('saveOrder').onclick=async()=>{const bad=[...form.elements].find(x=>x.willValidate&&!x.checkValidity());if(bad){const l=form.querySelector(`label[for="${bad.id}"]`)?.textContent||'الحقل';return sheetErr(`راجع «${l}»: ${bad.validationMessage}`,bad)}
    const v=Object.fromEntries(new FormData(form).entries()),file=form.querySelector('[name=file]').files[0];
    if(file&&file.size>25*1024*1024)return sheetErr('حجم الرسم الأقصى 25 ميجابايت',form.querySelector('[name=file]'));
    const obj={...f,id:o?.id||nextId('CNC',state.orders),name:v.name.trim(),client:v.client.trim(),estimate:Number(v.estimate),priority:v.priority,due:v.due,pricing:v.pricing,price:Number(v.price),qty:v.pricing==='hour'?1:Number(v.qty),material:v.material,payTerms:v.payTerms==='split'?'split':'single',advance:v.payTerms==='split'?Math.max(0,r2(v.advance)):0,createdAt:f.createdAt||now(),status:o?.status||'معلق',fileName:file?file.name:f.fileName};
    if(!obj.name||!obj.client||obj.estimate<=0||obj.qty<1||!Number.isFinite(obj.price))return sheetErr('راجع بيانات الأمر');
    try{if(file)await putDrawing(obj.id,file)}catch(e){return sheetErr('فشل حفظ الرسم؛ لم يتم حفظ الأمر')}
    const idx=state.orders.findIndex(a=>a.id===obj.id);if(idx>=0)state.orders[idx]=obj;else state.orders.push(obj);save();closeSheet();render();toast('تم حفظ أمر '+obj.id)}}
function finishOrder(id){const o=order(id);if(!canFinish(o))return toast('أنهِ فترة التشغيل وسجّل ساعات فعلية قبل إنهاء الأمر');
  openSheet({title:'إنهاء أمر الشغل',sub:esc(o.name),body:`<div class="calc">إجمالي التشغيل: <b>${humanMs(sumOrder(id))}</b><br>تاريخ الانتهاء الفعلي: <b>${esc(prettyDay(localDay(now())))}</b></div><p class="help">بعد الإنهاء يصبح الأمر جاهزًا لاستلام العميل.</p>`,foot:`<button class="btn ink block" type="button" id="confirmFinish">${ic('flag-checkered')}تأكيد الانتهاء</button>`});
  $('confirmFinish').onclick=()=>{if(!canFinish(o))return sheetErr('تعذر إنهاء الأمر أثناء التشغيل');o.status='انتهاء';o.completedAt=now();save();closeSheet();render();toast('انتهى التشغيل. الأمر جاهز للتسليم')}}
function deliverOrder(id){const o=order(id);if(role!=='manager'||!canDeliver(o))return toast('يجب إنهاء التشغيل أولًا قبل تأكيد التسليم');
  openSheet({title:'استلام العميل للمنتج',sub:`${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span>`,body:`<div class="calc"><b style="font-family:var(--font-ui)">${esc(o.name)}</b><br>تاريخ الانتهاء: <b>${esc(prettyDay(localDay(o.completedAt)))}</b><br>ساعات الشغل: <b>${humanMs(sumOrder(id))}</b></div>
    <div class="field"><label for="receivedBy">اسم المستلم (اختياري)</label><input id="receivedBy" placeholder="اسم مندوب العميل" maxlength="120"></div><p class="help">بعد الحفظ يظهر زر «إصدار فاتورة» على نفس الأمر للحسابات.</p>`,
    foot:`<button class="btn primary block" type="button" id="confirmDelivery">${ic('package')}تأكيد استلام العميل</button>`});
  $('confirmDelivery').onclick=()=>{if(!canDeliver(o))return sheetErr('الأمر غير جاهز للتسليم');o.status='تسليم';o.deliveredAt=now();o.receivedBy=$('receivedBy').value.trim();save();closeSheet();render();toast('تم استلام العميل. الفاتورة متاحة من أمر الشغل')}}
function nextInvoiceNumber(){const year=new Date().getFullYear();let n=1,v='';do{v='TEI-INV-'+year+'-'+String(n++).padStart(4,'0')}while(state.invoices.some(i=>String(i.number).toLowerCase()===v.toLowerCase()));return v}
function invoiceFigure(i,o){const unit=i.unit||(i.pricing==='hour'?'ساعة CNC':'قطعة');const qty=Number(i.quantity??(i.pricing==='hour'?sumOrder(o.id)/MS_H:o.qty));const rate=Number(i.unitPrice??o.price);return {unit,qty,rate,total:Math.round(qty*rate*100)/100}}
function printNow(html){$('printRoot').innerHTML=html;setTimeout(()=>window.print(),350)}
function printInvoice(id){const o=order(id),i=invoiceOf(id);if(!o||!i||!['manager','finance'].includes(role)||!i.issuedInternally)return toast('لا توجد فاتورة داخلية قابلة للطباعة لهذا الأمر');const f=invoiceFigure(i,o);
  printNow(`<img src="icons/logo.png" alt="TEI توليرنس للصناعات الهندسية" style="height:22mm;display:block;margin-bottom:4mm"><h2 style="margin-top:7px">فاتورة تشغيل داخلية</h2><div class="printdate">رقم الفاتورة: <b>${esc(i.number)}</b> &nbsp;&nbsp; التاريخ: <b>${esc(i.date)}</b>${i.revision>1?` &nbsp;&nbsp; مراجعة: ${Number(i.revision)}`:''}</div>
  <table><tbody><tr><th>العميل</th><td>${esc(i.client||o.client)}</td><th>أمر الشغل</th><td>${esc(o.id)}</td></tr><tr><th>تاريخ استلام العميل</th><td>${esc(i.deliveredDate||localDay(o.deliveredAt))}</td><th>نوع التسعير</th><td>${i.pricing==='hour'?'بالساعة':'بالقطعة'}</td></tr></tbody></table>
  <table><thead><tr><th>بيان الأعمال</th><th>الوحدة</th><th>الكمية</th><th>سعر الوحدة (جنيه)</th><th>الإجمالي (جنيه)</th></tr></thead><tbody><tr><td>${esc(i.description||o.name)}</td><td>${esc(f.unit)}</td><td>${esc(f.qty.toFixed(i.pricing==='hour'?4:2))}</td><td>${money(f.rate)}</td><td>${money(f.total)}</td></tr></tbody></table>
  <div class="print-total"><strong>الإجمالي: ${money(f.total)}</strong></div>${(()=>{const st=payState(o),l=paymentsOf(o);return l.length?`<table><thead><tr><th>المدفوعات</th><th>رقم الإيصال</th><th>التاريخ</th><th>الطريقة</th><th>المبلغ (جنيه)</th></tr></thead><tbody>${l.map(x=>`<tr><td>${esc(x.kind||'دفعة')}</td><td>${esc(x.number||'')}</td><td>${esc(x.date)}</td><td>${esc(x.method)}</td><td>${money(x.amount)}</td></tr>`).join('')}</tbody></table><p class="print-total" style="font-size:12pt">المدفوع: ${money(st.paid)} &nbsp;&nbsp; المتبقي: ${money(Math.max(0,st.balance))}</p>`:''})()}${i.notes?`<p style="margin-top:14px">ملاحظات: ${esc(i.notes)}</p>`:''}
  <p style="margin-top:26px">إعداد الحسابات: ____________________ &nbsp;&nbsp; اعتماد الإدارة: ____________________</p><p style="margin-top:16px;font-size:10pt">فاتورة داخلية لأعمال التشغيل؛ ليست فاتورة إلكترونية ضريبية. الضرائب أو الخصومات غير مُدرجة إلا إذا وُضحت ضمن البيان.</p>`)}
function invoiceEditor(id){const o=order(id),original=invoiceOf(id),isEdit=!!original;
  if(!['finance','manager'].includes(role))return toast('الفواتير للحسابات أو الإدارة فقط');
  if(!o||(!isEdit&&!canInvoice(o)))return toast('إصدار الفاتورة متاح بعد الانتهاء واستلام العميل');
  if(isEdit&&!original.issuedInternally)return toast('هذه فاتورة من نسخة قديمة؛ لا يمكن تعديل أصلها من هنا');
  const defaultQuantity=o.pricing==='hour'?Number((sumOrder(o.id)/MS_H).toFixed(4)):o.qty;
  const f=original||{number:nextInvoiceNumber(),date:localDay(now()),client:o.client,description:o.name,pricing:o.pricing,unit:o.pricing==='hour'?'ساعة CNC':'قطعة',quantity:defaultQuantity,unitPrice:o.price,notes:''};
  openSheet({title:isEdit?'مراجعة الفاتورة':'إصدار فاتورة',sub:`${esc(o.name)} · <span class="idtxt">${esc(o.id)}</span>`,body:`<div class="calc">استلام العميل: <b>${esc(prettyDay(localDay(o.deliveredAt)))}</b> · ساعات التشغيل: <b>${humanMs(sumOrder(o.id))}</b></div>
    <div class="fgrid">
      <div class="field"><label for="invoiceNumber">رقم الفاتورة</label><input id="invoiceNumber" maxlength="100" value="${esc(f.number)}" dir="ltr" style="text-align:right;font-family:var(--font-num)"></div>
      <div class="field"><label for="invoiceDate">تاريخ الفاتورة</label><input id="invoiceDate" type="date" value="${esc(f.date)}"></div>
      <div class="field"><label for="invoiceClient">اسم العميل</label><input id="invoiceClient" maxlength="150" value="${esc(f.client||o.client)}"></div>
      <div class="field"><label for="invoiceUnit">الوحدة</label><input id="invoiceUnit" maxlength="50" value="${esc(f.unit||'قطعة')}"></div>
      <div class="field full"><label for="invoiceDescription">بيان الأعمال</label><textarea id="invoiceDescription" rows="2" maxlength="500">${esc(f.description||o.name)}</textarea></div>
      <div class="field"><label for="invoiceQuantity">الكمية</label><input id="invoiceQuantity" type="number" inputmode="decimal" min="0.0001" max="100000000" step="any" value="${Number(f.quantity)}"></div>
      <div class="field"><label for="invoicePrice">سعر الوحدة (جنيه)</label><input id="invoicePrice" type="number" inputmode="decimal" min="0" max="1000000000" step="0.01" value="${Number(f.unitPrice)}"></div>
      <div class="field full"><label for="invoiceNotes">ملاحظات (اختياري)</label><textarea id="invoiceNotes" rows="2" maxlength="700">${esc(f.notes||'')}</textarea></div>
    </div>
    <div class="total-line"><span>الإجمالي</span><b id="liveInvoiceAmount">${money(invoiceFigure(f,o).total)}</b></div>
    <p class="help">التعديل هنا لا يغيّر أمر الشغل أو ساعات التشغيل. أي تعديل على فاتورة صادرة يُحفظ كمراجعة جديدة مع القيم السابقة.</p>`,
    foot:`<button class="btn primary block" type="button" id="savePrintInvoice">${ic('printer')}${isEdit?'حفظ وطباعة':'إصدار وطباعة'}</button><button class="btn block" type="button" id="saveInvoice">${ic('check')}${isEdit?'حفظ التعديلات':'إصدار وحفظ فقط'}</button>`});
  const quantity=$('invoiceQuantity'),price=$('invoicePrice');
  quantity.oninput=price.oninput=()=>{const q=Number(quantity.value),r=Number(price.value);$('liveInvoiceAmount').textContent=Number.isFinite(q)&&Number.isFinite(r)&&q>0&&r>=0?money(Math.round(q*r*100)/100):'راجع القيم'};
  function commit(doPrint){if(!isEdit&&!canInvoice(o))return sheetErr('الأمر ليس جاهزًا لإصدار فاتورة');
    const number=$('invoiceNumber').value.trim(),date=$('invoiceDate').value,client=$('invoiceClient').value.trim(),description=$('invoiceDescription').value.trim(),unit=$('invoiceUnit').value.trim(),notes=$('invoiceNotes').value.trim(),qty=Number(quantity.value),rate=Number(price.value);
    const req=[[number,'invoiceNumber'],[date,'invoiceDate'],[client,'invoiceClient'],[unit,'invoiceUnit'],[description,'invoiceDescription']].find(x=>!x[0]);if(req)return sheetErr('أكمل البيانات المطلوبة',$(req[1]));
    if(date<localDay(o.deliveredAt))return sheetErr('تاريخ الفاتورة لا يسبق استلام العميل',$('invoiceDate'));
    if(!Number.isFinite(qty)||qty<=0||qty>1e8)return sheetErr('راجع الكمية',quantity);if(!Number.isFinite(rate)||rate<0||rate>1e9)return sheetErr('راجع سعر الوحدة',price);
    if(state.invoices.some(x=>x.id!==original?.id&&String(x.number).trim().toLowerCase()===number.toLowerCase()))return sheetErr('رقم الفاتورة مستخدم بالفعل',$('invoiceNumber'));
    const amount=Math.round(qty*rate*100)/100,details={number,date,client,description,unit,quantity:qty,unitPrice:rate,amount,notes};
    const draftCopy=original?JSON.parse(JSON.stringify(original)):null,differs=original&&Object.keys(details).some(k=>String(original[k]??'')!==String(details[k]));
    if(original){if(differs){original.history=Array.isArray(original.history)?original.history:[];original.history.push({at:now(),previous:{number:original.number,date:original.date,client:original.client,description:original.description,unit:original.unit,quantity:original.quantity,unitPrice:original.unitPrice,amount:original.amount,notes:original.notes||''}});original.revision=(original.revision||1)+1;original.editedAt=now()}Object.assign(original,details)}
    else state.invoices.push({id:makeId(),orderId:o.id,createdAt:now(),issuedInternally:true,pricing:o.pricing,deliveredDate:localDay(o.deliveredAt),revision:1,history:[],...details});
    if(!save()){if(original){Object.keys(original).forEach(k=>delete original[k]);Object.assign(original,draftCopy)}else state.invoices.pop();return sheetErr('تعذر حفظ الفاتورة؛ لم يتم اعتماد التغيير')}
    closeSheet();render();toast(isEdit?'تم حفظ الفاتورة'+(differs?' كمراجعة جديدة':''):'تم إصدار الفاتورة وحفظها');if(doPrint)printInvoice(o.id)}
  $('saveInvoice').onclick=()=>commit(false);$('savePrintInvoice').onclick=()=>commit(true)}
function printDispatch(id){const o=order(id),i=invoiceOf(id);if(!o||o.status!=='تسليم'||!['manager','finance'].includes(role))return toast('إذن التسليم للأوامر المُسلّمة فقط');
  const h=sumOrder(id)/MS_H,qty=o.pricing==='hour'?h:o.qty,unit=o.pricing==='hour'?'ساعة CNC':'قطعة',total=bill(o);
  printNow(`<img src="icons/logo.png" alt="TEI توليرنس للصناعات الهندسية" style="height:22mm;display:block;margin-bottom:4mm"><h2>إذن تسليم شغل CNC، شامل الأسعار</h2><div class="printdate">أمر الشغل: <b>${esc(o.id)}</b> &nbsp;&nbsp; تاريخ التسليم: ${esc(localDay(o.deliveredAt||now()))}</div>
  <table><tbody><tr><th>اسم العميل</th><td>${esc(o.client)}</td><th>اسم المستلم</th><td>${esc(o.receivedBy||'________________')}</td></tr><tr><th>رقم الفاتورة</th><td colspan="3">${i?esc(i.number):'لم تصدر بعد، مطلوب إصدارها من الحسابات'}</td></tr></tbody></table>
  <table><thead><tr><th>بيان الشغل</th><th>الوحدة</th><th>الكمية</th><th>سعر الوحدة (جنيه)</th><th>القيمة (جنيه)</th></tr></thead><tbody><tr><td>${esc(o.name)}</td><td>${unit}</td><td>${o.pricing==='hour'?qty.toFixed(4):qty}</td><td>${money(o.price)}</td><td>${money(total)}</td></tr></tbody></table>
  <p class="print-total"><strong>إجمالي قيمة الأعمال: ${money(total)}</strong></p><p style="margin-top:30px">توقيع مسؤول التسليم: __________________ &nbsp;&nbsp;&nbsp; توقيع المستلم: __________________</p><p style="margin-top:12px;font-size:10pt">إذن تسليم أعمال مع بيان الأسعار، وليس مستندًا ضريبيًا. حالة الفاتورة: ${i?'صدرت':'قيد الإصدار'}.</p>`)}

/* ================= Payments UI ================= */
function paySheet(id){const o=order(id);if(!o||role==='operator')return toast('تسجيل المدفوعات للمدير أو الحسابات');const p=payState(o);
  let suggest='';if(p.invoiced)suggest=p.balance>0.004?p.balance:'';else if(o.payTerms==='split'&&o.advance>0&&p.paid<o.advance)suggest=r2(o.advance-p.paid);
  if(p.invoiced&&p.balance<=0.004)return toast('الفاتورة مدفوعة بالكامل');
  let method=PAY_METHODS[0];
  openSheet({title:'تسجيل دفعة',sub:`${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span>`,body:`<div class="card" style="box-shadow:none"><div class="readouts money" style="border-top:0">${ro(p.invoiced?'قيمة الفاتورة':'القيمة التقديرية',money(p.due))}${ro('المدفوع',money(p.paid))}${ro('المتبقي',money(Math.max(0,r2(p.due-p.paid))))}</div></div>
    ${p.invoiced?'':`<div class="note info">${ic('info')}<div>الفاتورة لسه ما صدرتش، فالدفعة دي هتتسجل «مقدم» وتتخصم من الفاتورة لما تصدر.</div></div>`}
    <div class="fgrid"><div class="field"><label for="payAmount">المبلغ (جنيه)</label><input id="payAmount" type="number" inputmode="decimal" min="0.01" step="0.01" value="${suggest}"></div><div class="field"><label for="payDate">التاريخ</label><input id="payDate" type="date" max="${localDay(now())}" value="${localDay(now())}"></div></div>
    <div class="field"><span class="label" id="payMLbl">طريقة الدفع</span><div class="namechips" role="radiogroup" aria-labelledby="payMLbl" id="payMethod">${PAY_METHODS.map((m,i)=>`<button type="button" class="chip" role="radio" aria-checked="${i===0}" data-m="${esc(m)}">${esc(m)}</button>`).join('')}</div></div>
    <div class="field"><label for="payNote">ملاحظة أو رقم مرجع (اختياري)</label><input id="payNote" maxlength="120" placeholder="مثال: رقم الشيك أو التحويل"></div>`,
    foot:`<button class="btn primary block" type="button" id="paySavePrint">${ic('printer')}حفظ وطباعة إيصال</button><button class="btn block" type="button" id="paySave">${ic('check')}حفظ الدفعة فقط</button>`,focus:'#payAmount'});
  $('payMethod').onclick=e=>{const b=e.target.closest('[data-m]');if(!b)return;method=b.dataset.m;$('payMethod').querySelectorAll('[data-m]').forEach(x=>x.setAttribute('aria-checked',x===b))};
  const commit=print=>{const amount=r2($('payAmount').value),date=$('payDate').value,note=$('payNote').value.trim();
    if(!(amount>0)||amount>1e9)return sheetErr('اكتب مبلغ صحيح',$('payAmount'));if(!date)return sheetErr('حدد التاريخ',$('payDate'));if(date>localDay(now()))return sheetErr('تاريخ الدفعة ما ينفعش يكون في المستقبل',$('payDate'));
    const st=payState(o);if(st.invoiced&&amount>st.balance+0.004)return sheetErr(`المبلغ أكبر من المتبقي (${money(Math.max(0,st.balance))})`,$('payAmount'));
    const kind=!st.invoiced?'مقدم':(st.paid===0&&amount>=st.due-0.004?'دفعة واحدة':(r2(st.balance-amount)<=0.004?'الباقي':'دفعة'));
    const pay={id:makeId(),number:nextReceiptNumber(),date,amount,method,note,kind,at:now(),by:ROLES[role].label};
    o.payments=[...paymentsOf(o),pay];if(!save()){o.payments=o.payments.filter(x=>x!==pay);return sheetErr('تعذر حفظ الدفعة')}
    closeSheet();render();toast(`تم تسجيل ${kind}: ${money(amount)}`);if(print)printReceipt(o.id,pay.id)};
  $('paySave').onclick=()=>commit(false);$('paySavePrint').onclick=()=>commit(true)}
async function voidPayment(id,pid){const o=order(id),p=paymentsOf(o).find(x=>x.id===pid);if(!o||!p||role==='operator')return;
  if(!await ask({title:'إلغاء الدفعة؟',body:`${esc(p.number||'')}: ${esc(money(p.amount))} بتاريخ ${esc(prettyDay(p.date))}. هتتشال من حساب العميل، وتفضل محفوظة في سجل الإلغاءات جوه النسخة الاحتياطية.`,ok:'إلغاء الدفعة',danger:true}))return;
  o.payments=paymentsOf(o).filter(x=>x.id!==pid);o.voidedPayments=[...(Array.isArray(o.voidedPayments)?o.voidedPayments:[]),{...p,voidedAt:now(),voidedBy:ROLES[role].label}];save();render();toast('تم إلغاء الدفعة')}
function printReceipt(id,pid){const o=order(id),p=paymentsOf(o).find(x=>x.id===pid),inv=invoiceOf(id);if(!o||!p)return;const st=payState(o);
  printNow(`<img src="icons/logo.png" alt="TEI توليرنس للصناعات الهندسية" style="height:22mm;display:block;margin-bottom:4mm"><h2>إيصال استلام نقدية</h2><div class="printdate">رقم الإيصال: <b>${esc(p.number||'')}</b> &nbsp;&nbsp; التاريخ: <b>${esc(p.date)}</b></div>
  <table><tbody><tr><th>استلمنا من</th><td>${esc(inv?.client||o.client)}</td><th>المبلغ</th><td><b>${money(p.amount)}</b></td></tr><tr><th>طريقة الدفع</th><td>${esc(p.method)}${p.note?' · '+esc(p.note):''}</td><th>نوع الدفعة</th><td>${esc(p.kind||'دفعة')}</td></tr><tr><th>أمر الشغل</th><td>${esc(o.id)} · ${esc(o.name)}</td><th>رقم الفاتورة</th><td>${inv?esc(inv.number):'لم تصدر بعد'}</td></tr></tbody></table>
  <table><tbody><tr><th>${st.invoiced?'قيمة الفاتورة':'القيمة التقديرية'}</th><td>${money(st.due)}</td><th>إجمالي المدفوع</th><td>${money(st.paid)}</td><th>المتبقي</th><td>${money(Math.max(0,r2(st.due-st.paid)))}</td></tr></tbody></table>
  <p style="margin-top:30px">توقيع المستلم (الحسابات): ____________________ &nbsp;&nbsp; توقيع العميل: ____________________</p><p style="margin-top:12px;font-size:10pt">إيصال داخلي لاستلام دفعة؛ ليس مستندًا ضريبيًا.</p>`)}

/* ================= Plan ================= */
const monthBegin=a=>weekStart(a.slice(0,7)+'-01');
const monthEnd=a=>{const[y,m]=a.slice(0,7).split('-').map(Number);return localDay(new Date(y,m,0).getTime())};
const shiftMonth=(d,n)=>{const[y,m]=d.split('-').map(Number);return localDay(new Date(y,m-1+n,1).getTime())};
const niceMonth=d=>toDate(d.slice(0,7)+'-01').toLocaleDateString(DATE_FMT,{year:'numeric',month:'long'});
function renderPlan(){const today=localDay(now());if(!selectedDay)selectedDay=today;if(!weekAnchor)weekAnchor=today;
  const p=planEngine(null,today),queue=queueItems();
  const first=calendarView==='week'?weekStart(weekAnchor):monthBegin(weekAnchor);
  const last=calendarView==='week'?addDays(first,6):addDays(monthEnd(weekAnchor),6);
  const count=calendarView==='week'?7:Math.round((dayBounds(last)[0]-dayBounds(first)[0])/86400000/7)*7;
  const dates=Array.from({length:count},(_,i)=>addDays(first,i));
  $('periodTitle').textContent=calendarView==='week'?`${prettyDay(first)} إلى ${prettyDay(addDays(first,6))}`:niceMonth(weekAnchor);
  $('weekView').setAttribute('aria-pressed',calendarView==='week');$('monthView').setAttribute('aria-pressed',calendarView==='month');
  const eventFor=d=>(p.days[d]?.tasks||[]).filter(t=>!t.potential&&activeOption(order(t.id)));
  $('calendar').innerHTML=dates.map(d=>{const ev=eventFor(d),day=p.days[d],cap=day?day.cap:capacity(d),load=(day?day.used:0)+ev.reduce((n,t)=>n+t.hours,0),out=calendarView==='month'&&d.slice(0,7)!==weekAnchor.slice(0,7),isLive=ev.some(t=>t.status==='بدء');
    const w=cap>0?Math.min(100,load/cap*100):0,label=`${prettyDay(d,true)}: ${ev.length?ev.length+' أمر، '+hrs(load)+' ساعة':'لا توجد أوامر'}`;
    return `<button type="button" class="cday ${d===today?'today':''} ${out?'out':''}" data-action="selectDay" data-date="${d}" aria-pressed="${d===selectedDay}" aria-label="${esc(label)}"><span class="d">${Number(d.slice(8))}</span><span class="load">${w>0?`<b class="${isLive?'live':''} ${w>=99.9?'full':''}" style="width:${w.toFixed(1)}%"></b>`:''}</span></button>`}).join('');
  const day=p.days[selectedDay]||{cap:capacity(selectedDay),used:0,tasks:[],free:capacity(selectedDay)};
  const tasks=eventFor(selectedDay),reserved=tasks.reduce((n,t)=>n+t.hours,0),free=Math.max(0,day.cap-day.used-reserved);
  let bar='';if(day.cap>0){const pc=h=>(h/day.cap*100).toFixed(2);let ticks='';for(let h=0;h<=day.cap+1e-9;h++){const maj=h%6===0;ticks+=`<i class="${maj?'maj':''}" style="inset-inline-start:${pc(h)}%"></i>${maj?`<span style="inset-inline-start:${pc(h)}%">${h}</span>`:''}`}
    bar=`<div class="daybar" role="img" aria-label="${esc(`مسجل ${hrs(day.used)} ساعة، محجوز ${hrs(reserved)} ساعة، متاح ${hrs(free)} من ${hrs(day.cap)}`)}"><div class="track">${day.used>0?`<span class="seg-used" style="width:${pc(day.used)}%"></span>`:''}${tasks.map((t,i)=>`<span class="seg-job ${t.status==='بدء'?'live':i%2?'alt':''}" style="width:${pc(t.hours)}%"></span>`).join('')}</div><div class="ticks">${ticks}</div></div>`}
  const unfunded=queue.filter(x=>x.remaining<=1e-7);
  $('agenda').innerHTML=`<div class="card-pad" style="padding-bottom:12px"><div class="section-h" style="margin:0"><div><h2>${esc(prettyDay(selectedDay,true))}</h2><p class="help">${day.cap>0?`طاقة اليوم <span class="num">${hrs(day.cap)}</span> ساعة`:'إجازة: لا توجد ساعات تشغيل'}</p></div>${role==='manager'?`<button class="btn sm" type="button" data-action="dayCap" data-date="${selectedDay}">${ic('sliders-horizontal','sm')}ساعات اليوم</button>`:''}</div>${bar}</div>
    <div class="readouts">${ro('مسجّل فعليًا',hrs(day.used)+' س')}${ro('محجوز أوامر',hrs(reserved)+' س')}${ro('متاح لشغل جديد',hrs(free)+' س')}</div>
    <div class="agenda">${tasks.length?tasks.map(t=>{const o=order(t.id),late=o.due&&selectedDay>o.due;return `<div class="aitem"><div class="hrs"><b>${hrs(t.hours)}</b><span>ساعة</span></div><div class="t"><b>${esc(o.name)}</b><span class="help">${esc(o.client)} · <span class="idtxt">${esc(o.id)}</span></span><div class="meta" style="margin-top:6px">${pill(o.status)}<span class="tag ${o.priority==='عاجل'?'urgent':''}">${esc(o.priority)}</span>${late?`<span class="tag late">${ic('warning','sm')}بعد موعد العميل</span>`:''}</div></div>${role==='manager'?`<button class="iconbtn" type="button" data-action="planEdit" data-id="${esc(o.id)}" aria-label="تعديل خطة ${esc(o.name)}">${ic('pencil-simple')}</button>`:''}</div>`}).join(''):`<div class="empty" style="border-top:1px solid var(--rule-soft)">${ic('calendar-blank','lg')}<b>لا يوجد أمر مخطط لهذا اليوم</b><p>اختر يومًا آخر، أو افتح أمر شغل جديد من «الأوامر».</p></div>`}
    ${selectedDay===today&&unfunded.length?`<div class="card-pad" style="border-top:1px solid var(--rule-soft)"><div class="note">${ic('warning')}<div>${unfunded.length} أمر مفتوح استهلك الساعات المقدرة بدون إنهاء. راجع تقديره قبل تحديد موعد جديد.</div></div></div>`:''}</div>`}
function editPlan(id){if(role!=='manager')return toast('تعديل الخطة للمدير فقط');const o=order(id);if(!o||!activeOption(o))return toast('الأمر ليس مفتوحًا');const today=localDay(now()),f=plannedFinish(id);
  openSheet({title:'تعديل خطة أمر الشغل',sub:`${esc(o.name)} · <span class="idtxt">${esc(o.id)}</span>`,body:`<div class="fgrid"><div class="field"><label for="pStart">أول يوم للتخطيط</label><input id="pStart" type="date" min="${today}" value="${esc(o.planStart&&o.planStart>=today?o.planStart:today)}"></div><div class="field"><label for="pHours">الوقت المقدر (ساعة)</label><input id="pHours" type="number" inputmode="decimal" min="0.25" step="0.25" value="${esc(o.estimate)}"></div><div class="field"><label for="pPriority">الأولوية</label><select id="pPriority">${['عادي','عالي','عاجل'].map(x=>`<option ${o.priority===x?'selected':''}>${x}</option>`).join('')}</select></div><div class="field"><label for="pDue">موعد تسليم العميل</label><input id="pDue" type="date" value="${esc(o.due)}"></div></div>
    <p class="help">الانتهاء الحالي حسب الخطة: <b>${esc(f?prettyDay(f):'يحتاج تقديرًا')}</b>. الساعات المسجلة لن تُمسح، والخطة تعيد حساب الأيام تلقائيًا.</p>`,foot:`<button class="btn primary block" type="button" id="savePlan">${ic('check')}حفظ وتحديث التقويم</button>`});
  $('savePlan').onclick=()=>{const date=$('pStart').value,estimate=+$('pHours').value,due=$('pDue').value;if(!date||date<today)return sheetErr('أول يوم للتخطيط لا يسبق اليوم',$('pStart'));if(!Number.isFinite(estimate)||estimate<=0)return sheetErr('راجع الساعات',$('pHours'));if(!due)return sheetErr('حدد موعد التسليم',$('pDue'));if(live()?.orderId===id&&date>today)return sheetErr('الأمر يعمل الآن؛ لا يؤجل حتى انتهاء فترة التشغيل');
    o.planStart=date;o.estimate=estimate;o.due=due;o.priority=$('pPriority').value;if(!save())return;closeSheet();render();toast('تم حفظ الخطة وتحديث موعد الانتهاء المتوقع')}}
function editDayCapacity(day){if(role!=='manager')return;openSheet({title:'ساعات تشغيل اليوم',sub:esc(prettyDay(day,true)),body:`<div class="field"><label for="dayCapHours">الساعات المتاحة</label><input id="dayCapHours" type="number" inputmode="decimal" min="0" max="24" step="0.5" value="${capacity(day)}"></div><div class="namechips">${[0,8,12,16,24].map(h=>`<button type="button" class="chip" data-cap="${h}">${h===0?'إجازة':h+' ساعة'}</button>`).join('')}</div><p class="help">الافتراضي 24 ساعة يوميًا. اضبط 0 لو اليوم إجازة. التعديل يحدّث الخطة.</p>`,foot:`<button class="btn primary block" type="button" id="saveDayCap">${ic('check')}حفظ اليوم</button>`,focus:'#dayCapHours'});
  sheet.el.querySelectorAll('[data-cap]').forEach(b=>b.onclick=()=>{$('dayCapHours').value=b.dataset.cap});
  $('saveDayCap').onclick=()=>{const val=+$('dayCapHours').value;if(!Number.isFinite(val)||val<0||val>24)return sheetErr('أدخل عدد ساعات من 0 إلى 24',$('dayCapHours'));state.dayCapacity[day]=val;if(!save())return;closeSheet();render();toast('تم تعديل طاقة يوم '+prettyDay(day))}}

/* ================= Reports ================= */
let reportType='daily';
const REPORT_TYPES=[['daily','اليومي للماكينة'],['productivity','الإنتاجية'],['orders','ساعات الأوامر'],['operators','ساعات المشغّلين'],['stops','الأعطال'],['payments','التحصيل']];
const reportTypesFor=()=>REPORT_TYPES.filter(([k])=>k!=='payments'||role!=='operator');
function reportPeriod(){const type=reportType,day=$('reportDate').value||localDay(now()),from=type==='daily'?day:($('reportFrom').value||day.slice(0,7)+'-01'),to=type==='daily'?day:($('reportTo').value||day);
  if(from>to)return {type,from,to,error:'تاريخ البداية بعد تاريخ النهاية'};const days=Math.round((dayBounds(to)[0]-dayBounds(from)[0])/86400000)+1;if(days>800)return {type,from,to,error:'اختر فترة لا تتجاوز 800 يوم'};return {type,from,to,days}}
function periodRows(from,to){let rows=[];for(let d=from;d<=to;d=addDays(d,1))rows.push(...dayRows(d));return rows}
function stopsByReason(from,to){const [a]=dayBounds(from),[,b]=dayBounds(to),group=new Map();for(const s of state.sessions)for(const g of s.segments){if(g.type!=='stop')continue;const x=Math.max(a,g.startAt),y=Math.min(b,g.endAt??now());if(y<=x)continue;const key=g.reason||'غير محدد',k=group.get(key)||{reason:key,stop:0,repair:0,count:0};k.stop+=y-x;if(handling(g))k.repair+=y-x;k.count++;group.set(key,k)}return [...group.values()].sort((a,b)=>b.stop-a.stop)}
function reportData(){const p=reportPeriod();if(p.error)return {...p,headers:[],rows:[],cards:[],hint:p.error};
  const rows=periodRows(p.from,p.to),run=rows.reduce((n,r)=>n+r.run,0),stop=rows.reduce((n,r)=>n+r.stop,0),opH=rows.reduce((n,r)=>n+r.operator,0);
  let headers=[],body=[],title='',cards=[],hint='الساعات محسوبة مباشرة من سجل التشغيل، دون إدخال جديد.';
  if(p.type==='daily'){title='التقرير اليومي للماكينة';headers=['المشغّل','أمر الشغل','بداية ونهاية','وقت الشغل','أعطال الورشة','وقت المشغّل','سبب التوقف'];
    body=rows.map(r=>[r.operatorName,(order(r.orderId)?.name||r.orderId)+' · '+r.orderId,localTime(r.start)+' → '+(r.end===dayBounds(p.from)[1]?'24:00':localTime(r.end)),humanMs(r.run),humanMs(r.stop),humanMs(r.operator),Object.keys(r.reasons).join('، ')||'لا يوجد']);
    cards=[['وقت الشغل',humanMs(run),'يشمل التجهيز'],['أعطال الورشة',humanMs(stop),'لا تُحمّل للعميل'],['ساعات المشغّلين',humanMs(opH),'تشغيل + إصلاح']];hint='الساعات التي تعبر منتصف الليل تُوزّع على اليومين.'}
  else if(p.type==='orders'){title='تقرير ساعات أوامر الشغل';const map=new Map();for(const r of rows){let v=map.get(r.orderId)||{id:r.orderId,run:0,stop:0,operator:0,repair:0};v.run+=r.run;v.stop+=r.stop;v.operator+=r.operator;v.repair+=r.repair;map.set(r.orderId,v)}
    headers=['الشغلانة / العميل','رقم الأمر','المقدّر (ساعة)','ساعات الشغل','أعطال الورشة','ساعات المشغّلين','حالة الطلب'];
    body=[...map.values()].sort((a,b)=>b.run-a.run).map(v=>{const o=order(v.id);return[(o?.name||'غير محدد')+' · '+(o?.client||''),v.id,o?String(o.estimate):'غير محدد',humanMs(v.run),humanMs(v.stop),humanMs(v.operator),statusLabel(o?.status)||'غير محدد']});
    cards=[['أوامر منفّذة',String(map.size),'داخل الفترة'],['ساعات الأوامر',humanMs(run),'تجهيز + تشغيل'],['أعطال الورشة',humanMs(stop),'مستبعدة من البيع']];hint='الساعات تخص الفترة المختارة، والمقدّر هو إجمالي تقدير الأمر.'}
  else if(p.type==='operators'){title='تقرير ساعات المشغّلين';const map=new Map();for(const r of rows){const k=r.operatorName,v=map.get(k)||{name:k,run:0,operator:0,orders:new Set()};v.run+=r.run;v.operator+=r.operator;v.orders.add(r.orderId);map.set(k,v)}
    headers=['المشغّل','عدد الأوامر','وقت الشغل','ساعات العمل الإجمالية'];body=[...map.values()].sort((a,b)=>b.operator-a.operator).map(v=>[v.name,String(v.orders.size),humanMs(v.run),humanMs(v.operator)]);
    cards=[['عدد المشغّلين',String(map.size),'داخل الفترة'],['ساعات عملهم',humanMs(opH),'شغل + إصلاح'],['شغل الماكينة',humanMs(run),'محمّل للعميل']];hint='وقت توقف الورشة يُحسب للمشغّل فقط إذا كان يعالج العطل. تغيير المشغّل لا يضاعف ساعات الأمر.'}
  else if(p.type==='productivity'){title='تقرير الإنتاجية';const today=localDay(now());let avail=0;
    for(let d=p.from;d<=p.to&&d<=today;d=addDays(d,1)){const cap=capacity(d);avail+=d===today?Math.min(cap,(now()-dayBounds(d)[0])/MS_H):cap}
    const util=avail>0?run/MS_H/avail*100:0,faultPct=run+stop>0?stop/(run+stop)*100:0;
    const [a]=dayBounds(p.from),[,b]=dayBounds(p.to),done=state.orders.filter(o=>o.completedAt&&o.completedAt>=a&&o.completedAt<b).sort((x,y)=>x.completedAt-y.completedAt);
    let estSum=0,actSum=0;headers=['الشغلانة / العميل','رقم الأمر','المقدّر (ساعة)','الفعلي (ساعة)','الفرق','الحالة'];
    body=done.map(o=>{const est=Number(o.estimate)||0,act=sumOrder(o.id)/MS_H;estSum+=est;actSum+=act;const diff=est>0?(act-est)/est*100:0;return[o.name+' · '+o.client,o.id,hrs(est),act.toFixed(2),Math.abs(diff)<0.5?'مطابق للتقدير':(diff>0?'أطول ':'أسرع ')+Math.abs(diff).toFixed(0)+'%',statusLabel(o.status)]});
    cards=[['نسبة تشغيل الماكينة',util.toFixed(1)+'%',`${hrs(run/MS_H)} من ${hrs(avail)} س متاحة`],['نسبة الأعطال',faultPct.toFixed(1)+'%','من وقت الماكينة'],['الفعلي ÷ المقدّر',estSum>0?(actSum/estSum*100).toFixed(0)+'%':'لا يوجد',`${done.length} أمر انتهى`]];
    if(role!=='operator'){const issued=state.invoices.filter(i=>i.date>=p.from&&i.date<=p.to);cards.push(['قيمة الفواتير',money(issued.reduce((n,i)=>n+(Number(i.amount)||0),0)),`${issued.length} فاتورة صدرت`])}
    hint='نسبة التشغيل = ساعات الشغل ÷ الساعات المتاحة حسب طاقة كل يوم في الخطة، لحد النهارده. الفعلي ÷ المقدّر أقل من 100% يعني الشغل خلص أسرع من التقدير. الجدول للأوامر اللي خلصت في الفترة.'}
  else if(p.type==='payments'){title='تقرير التحصيل والمستحقات';const list=state.orders.flatMap(o=>paymentsOf(o).filter(x=>x.date>=p.from&&x.date<=p.to).map(x=>({...x,o})));
    headers=['العميل','أمر الشغل','رقم الإيصال','التاريخ','الطريقة','النوع','المبلغ'];body=list.sort((x,y)=>x.date.localeCompare(y.date)).map(x=>[x.o.client,x.o.id+' · '+x.o.name,x.number||'',x.date,x.method,x.kind||'دفعة',money(x.amount)]);
    const out=outstandingOrders();cards=[['المحصّل في الفترة',money(list.reduce((n,x)=>n+x.amount,0)),`${list.length} دفعة`],['مستحق على العملاء',money(out.reduce((n,o)=>n+payState(o).balance,0)),`${out.length} فاتورة غير مسددة`]];
    hint='«مستحق على العملاء» رقم حالي لكل الفواتير، مش للفترة بس. المقدم المدفوع قبل الفاتورة بيتخصم منها تلقائيًا.'}
  else{title='تقرير الأعطال والتوقفات';const reasons=stopsByReason(p.from,p.to);headers=['سبب العطل','عدد فترات العطل','إجمالي التوقف'];body=reasons.map(v=>[v.reason,String(v.count),humanMs(v.stop)]);
    cards=[['إجمالي الأعطال',humanMs(stop),'كلها على الورشة'],['أسباب العطل',String(reasons.length),'أنواع مسجلة']];hint='لا يدخل أي عطل هنا ضمن ساعات محاسبة العميل.'}
  return {...p,title,headers,rows:body,cards,hint}}
function renderReport(){if(!reportTypesFor().some(x=>x[0]===reportType))reportType='daily';$('reportTypes').innerHTML=reportTypesFor().map(([k,l])=>`<button type="button" class="chip" role="radio" data-rtype="${k}" aria-checked="${reportType===k}">${esc(l)}</button>`).join('');
  const isDay=reportType==='daily';$('reportDayFilter').classList.toggle('hidden',!isDay);$('reportPeriodFilter').classList.toggle('hidden',isDay);
  const d=reportData();const nc=d.cards.length;$('reportStats').style.gridTemplateColumns=`repeat(${nc>3||(nc===2)?2:Math.max(1,nc)},1fr)`;$('reportStats').classList.toggle('grid2',nc>3);$('reportStats').innerHTML=d.cards.map(([l,v,s])=>ro(l,v,s)).join('');$('reportStats').parentElement.classList.toggle('hidden',!d.cards.length);
  $('reportRows').innerHTML=d.error?`<div class="empty">${ic('warning','lg')}<b>${esc(d.error)}</b></div>`:d.rows.length?`<div class="card-pad" style="padding-bottom:4px"><h2 style="font-size:16px;font-weight:600">${esc(d.title)}</h2><p class="help">${esc(d.from===d.to?prettyDay(d.from,true):prettyDay(d.from)+' إلى '+prettyDay(d.to))}</p></div>`+d.rows.map(r=>`<div class="rrow"><h3>${esc(r[0])}</h3><div class="kv">${r.slice(1).map((c,i)=>`<div><small>${esc(d.headers[i+1])}</small><span class="${/^[\d:.\sسد→ ]+$/.test(c)?'n':''}">${esc(c).replace(/(CNC-\d+)/g,'<span class="idtxt">$1</span>').replace(/(\d+(?:\.\d+)?%)/g,'<span class="ltr num">$1</span>')}</span></div>`).join('')}</div></div>`).join(''):`<div class="empty">${ic('chart-bar','lg')}<b>لا توجد بيانات في هذه الفترة</b><p>غيّر اليوم أو الفترة، أو سجّل تشغيلًا من تبويب «الماكينة».</p></div>`;
  $('reportHint').textContent=d.hint||''}
function csvReport(){const r=reportData();if(r.error)return toast(r.error);const cells=[[r.title+' من '+r.from+' إلى '+r.to],r.headers,...r.rows];const csv='﻿'+cells.map(row=>row.map(v=>'"'+String(v).replaceAll('"','""')+'"').join(',')).join('\r\n');downloadFile(new Blob([csv],{type:'text/csv;charset=utf-8'}),'TEI_CNC_Report_'+r.type+'_'+r.from+'_'+r.to+'.csv');toast('تم تصدير '+r.title)}
function printReport(){const r=reportData();if(r.error)return toast(r.error);printNow(`<img src="icons/logo.png" alt="TEI توليرنس للصناعات الهندسية" style="height:22mm;display:block;margin-bottom:4mm"><h2>${esc(r.title)}</h2><div class="printdate">الفترة: ${esc(r.from)} إلى ${esc(r.to)}</div><table><thead><tr>${r.headers.map(x=>`<th>${esc(x)}</th>`).join('')}</tr></thead><tbody>${r.rows.map(row=>`<tr>${row.map(x=>`<td>${esc(x)}</td>`).join('')}</tr>`).join('')||`<tr><td colspan="${r.headers.length}">لا توجد بيانات</td></tr>`}</tbody></table><div style="margin-top:15px">${r.cards.map(x=>`<span style="display:inline-block;margin:6px 12px">${esc(x[0])}: <b>${esc(x[1])}</b></span>`).join('')}</div><p style="margin-top:32px">توقيع الإدارة: ____________________</p>`)}

/* ================= More ================= */
let installEvt=null;
function renderMore(){const isIOS=/iphone|ipad|ipod/i.test(navigator.userAgent),standalone=matchMedia('(display-mode: standalone)').matches||navigator.standalone;
  $('scr-more').innerHTML=`
  <div class="section-h" style="margin-top:0"><h2>الدور الحالي</h2></div>
  <div class="card list" role="radiogroup" aria-label="الدور">${roleListHTML()}</div>
  <p class="help">الدور المحمي برقم سري بيطلب الرقم عند التبديل له. ده قفل خفيف على الجهاز، مش نظام حسابات مستخدمين.</p>
  ${role==='manager'?`<div class="section-h"><h2>الأمان</h2></div>
  <div class="card list"><button type="button" class="litem" data-action="pins">${ic('shield-check')}<span class="t">الأرقام السرية للأدوار<span>${Object.keys(ROLES).filter(hasPin).length?Object.keys(ROLES).filter(hasPin).map(k=>ROLES[k].label).join('، ')+': محمي':'لا يوجد دور محمي برقم'}</span></span>${ic('caret-left')}</button></div>`:''}
  <div class="section-h"><h2>البيانات</h2></div>
  <div class="card list">
    <button type="button" class="litem" data-action="backup">${ic('download-simple')}<span class="t">نسخة احتياطية<span>ملف JSON بالبيانات والرسومات المرفقة</span></span></button>
    ${role==='manager'||!Object.keys(ROLES).some(hasPin)?`<button type="button" class="litem" data-action="restore">${ic('upload-simple')}<span class="t">استعادة من نسخة<span>تستبدل كل البيانات الحالية على هذا الجهاز</span></span></button>`:''}
    ${role==='manager'?`<button type="button" class="litem" data-action="demo">${ic('flask')}<span class="t">بيانات للتجربة<span>تضيف أمرين تجريبيين</span></span></button>`:''}
  </div>
  <p class="help">البيانات محفوظة على هذا الهاتف فقط. خذ نسخة احتياطية بانتظام، وخاصة قبل تغيير الجهاز أو مسح بيانات المتصفح. ملفات V3.9 الاحتياطية تعمل هنا مباشرة.</p>
  <div class="card card-pad" style="display:grid;place-items:center;padding:24px 16px;margin-top:8px"><img src="icons/logo.png" alt="TEI توليرنس للصناعات الهندسية" width="560" height="312" style="width:min(240px,70%);height:auto"></div>
  <div class="section-h"><h2>التطبيق</h2></div>
  <div class="card list">
    ${standalone?`<div class="litem">${ic('device-mobile')}<span class="t">مثبّت على الشاشة الرئيسية<span>يعمل بدون إنترنت</span></span>${ic('check')}</div>`:installEvt?`<button type="button" class="litem" data-action="install">${ic('device-mobile')}<span class="t">تثبيت التطبيق<span>أيقونة على الشاشة الرئيسية ويعمل بدون إنترنت</span></span></button>`:`<div class="litem">${ic('device-mobile')}<span class="t">تثبيت التطبيق<span>${isIOS?'من Safari: زر المشاركة، ثم «إضافة إلى الشاشة الرئيسية».':'من قائمة المتصفح: «تثبيت التطبيق» أو «إضافة إلى الشاشة الرئيسية».'}</span></span></div>`}
    <div class="litem">${ic('info')}<span class="t">مسار واحد بلا تكرار<span>أمر شغل، خطة تشغيل، تسجيل الفني، انتهاء، استلام العميل، ثم الفاتورة. الفاتورة داخلية وليست فاتورة إلكترونية ضريبية.</span></span></div>
    <div class="litem">${ic('gauge')}<span class="t">TEI CNC <span class="num" style="display:inline">${APP_VERSION}</span><span>توليرنس للصناعات الهندسية · متوافق مع بيانات V3.9</span></span></div>
  </div>`}

/* ================= Drawings (IndexedDB), backup ================= */
function fileDB(){if(idb)return Promise.resolve(idb);return new Promise((resolve,reject)=>{if(!window.indexedDB)return reject(Error('No IndexedDB'));const req=indexedDB.open(DB,1);req.onupgradeneeded=()=>req.result.createObjectStore('drawings',{keyPath:'id'});req.onsuccess=()=>{idb=req.result;resolve(idb)};req.onerror=()=>reject(req.error)})}
async function putDrawing(id,file){const db=await fileDB();return new Promise((res,rej)=>{const tx=db.transaction('drawings','readwrite');tx.objectStore('drawings').put({id,name:file.name,type:file.type,blob:file});tx.oncomplete=res;tx.onerror=()=>rej(tx.error)})}
async function getDrawing(id){const db=await fileDB();return new Promise((res,rej)=>{const req=db.transaction('drawings','readonly').objectStore('drawings').get(id);req.onsuccess=()=>res(req.result);req.onerror=()=>rej(req.error)})}
function downloadFile(blob,name){const u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download=name;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),3000)}
async function openDrawing(id){const o=order(id);if(!o?.fileName)return toast('لا يوجد رسم مرفق');try{const x=await getDrawing(id);if(!x?.blob)return toast('المرفق غير موجود على هذا الجهاز');downloadFile(x.blob,x.name)}catch(e){toast('لم يمكن فتح المرفق')}}
async function backup(){const files=[];for(const o of state.orders){if(!o.fileName)continue;try{const x=await getDrawing(o.id);if(!x?.blob)continue;const data=await new Promise((res,rej)=>{const r=new FileReader();r.onload=()=>res(String(r.result).split(',')[1]);r.onerror=()=>rej(r.error);r.readAsDataURL(x.blob)});files.push({id:o.id,name:x.name,type:x.type,data})}catch(e){toast('لم يُدرج أحد الرسومات في النسخة')}}
  downloadFile(new Blob([JSON.stringify({type:'TEI_CNC_V3',state,files,at:now()})],{type:'application/json'}),'TEI_CNC_Backup_'+localDay(now())+'.json');toast('تم تجهيز النسخة الاحتياطية')}
async function restore(file){if(!file)return;if(role!=='manager'&&Object.keys(ROLES).some(hasPin))return toast('الاستعادة للمدير فقط');try{const b=JSON.parse(await file.text());if(b.type!=='TEI_CNC_V3'||b.state?.version!==3||!Array.isArray(b.state?.orders)||!Array.isArray(b.state?.sessions)||!Array.isArray(b.state?.invoices))return toast('ملف النسخة الاحتياطية غير صحيح');
  if(!await ask({title:'استبدال كل البيانات؟',body:`النسخة فيها ${b.state.orders.length} أمر شغل. ستُستبدل كل البيانات الحالية على هذا الجهاز. خذ نسخة احتياطية أولًا لو تحتاجها.`,ok:'استعادة',danger:true}))return;
  for(const f of b.files||[]){const raw=atob(f.data),arr=new Uint8Array(raw.length);for(let i=0;i<raw.length;i++)arr[i]=raw.charCodeAt(i);await putDrawing(f.id,new File([arr],f.name,{type:f.type}))}
  state=b.state;state.tentatives=Array.isArray(state.tentatives)?state.tentatives:[];state.planOrder=Array.isArray(state.planOrder)?state.planOrder:[];state.dayCapacity=state.dayCapacity||{};save();render();toast('تمت الاستعادة بنجاح')}catch(e){toast('تعذر استعادة النسخة: تحقق من الملف ومساحة التخزين')}}
async function demoData(){if(state.orders.length&&!await ask({title:'إضافة أمثلة؟',body:'سيُضاف أمران تجريبيان إلى أوامرك الحالية.',ok:'إضافة'}))return;
  if(live())return toast('أنهِ التشغيل الجاري أولًا قبل إضافة أمثلة');
  const date=localDay(now()),ids=['CNC-'+String(state.orders.length+1).padStart(4,'0'),'CNC-'+String(state.orders.length+2).padStart(4,'0')];
  const samples=[{id:ids[0],name:'تفريز كرسي بلي',client:'العميل الرئيسي (تجريبي)',estimate:6,priority:'عاجل',due:date,pricing:'hour',price:650,qty:1,material:'خامة العميل',createdAt:now(),status:'بدء',fileName:''},{id:ids[1],name:'تجهيز 4 بلات تثبيت',client:'مصنع تجريبي',estimate:5,priority:'عادي',due:date,pricing:'fixed',price:850,qty:4,material:'خامة الورشة',createdAt:now(),status:'انتهاء',completedAt:now(),fileName:''}];
  const b=now();state.orders.push(...samples);
  state.sessions.push({id:makeId(),orderId:ids[0],operator:'أحمد (تجريبي)',startAt:b-6*MS_H,endAt:b-2*MS_H,segments:[{type:'run',startAt:b-6*MS_H,endAt:b-4*MS_H},{type:'stop',startAt:b-4*MS_H,endAt:b-3.5*MS_H,reason:'كسر أو تلف عدة القطع',present:true},{type:'run',startAt:b-3.5*MS_H,endAt:b-2*MS_H}]});
  state.sessions.push({id:makeId(),orderId:ids[1],operator:'محمود (تجريبي)',startAt:b-30*MS_H,endAt:b-25*MS_H,segments:[{type:'run',startAt:b-30*MS_H,endAt:b-25*MS_H}]});
  save();render();toast('تمت إضافة أمرين للتجربة')}

/* ================= Events ================= */
document.addEventListener('click',e=>{
  const t=e.target;
  const tb=t.closest('.tab');if(tb){if(sheet)closeSheet();tabSet(tb.dataset.tab);return}
  const f=t.closest('[data-filter]');if(f&&f.closest('#scr-orders')){orderFilter=orderFilter===f.dataset.filter&&f.classList.contains('ro')?'all':f.dataset.filter;if(f.id==='clearFilter')$('search').value='';renderOrders();return}
  const pk=t.closest('[data-pick]');if(pk){draft.orderId=pk.dataset.pick;renderMachine();return}
  const op=t.closest('[data-op]');if(op){draft.operator=op.dataset.op;$('operator').value=draft.operator;renderMachine();return}
  const rt=t.closest('[data-rtype]');if(rt){reportType=rt.dataset.rtype;renderReport();return}
  const rl=t.closest('[data-role]');if(rl){requestRole(rl.dataset.role);return}
    const btn=t.closest('[data-action]');if(!btn)return;const a=btn.dataset.action,id=btn.dataset.id;
  const needsClose=['edit','work','finish','deliver','invoice','editInvoice','dispatch','planEdit','goMachine','file'].includes(a)&&sheet;
  if(needsClose&&!['edit','finish','deliver','invoice','editInvoice','planEdit'].includes(a))closeSheet();
  ({pay:()=>paySheet(id),receipt:()=>printReceipt(id,btn.dataset.pid),voidPay:()=>voidPayment(id,btn.dataset.pid),pins:managePins,openOrder:()=>openOrder(id),edit:()=>openOrderForm(id),newOrder:()=>openOrderForm(),finish:()=>finishOrder(id),deliver:()=>deliverOrder(id),invoice:()=>invoiceEditor(id),editInvoice:()=>invoiceEditor(id),dispatch:()=>printDispatch(id),file:()=>openDrawing(id),planEdit:()=>editPlan(id),
    work:()=>{const s=live();if(s&&s.orderId!==id)return toast('يوجد تشغيل مفتوح على أمر آخر. أنهِ فترته أولًا');draft.orderId=id;tabSet('machine');if(!s)setTimeout(()=>$('operator').focus(),250)},
    goMachine:()=>tabSet('machine'),selectDay:()=>{selectedDay=btn.dataset.date;if(calendarView==='month'&&selectedDay.slice(0,7)!==weekAnchor.slice(0,7))weekAnchor=selectedDay;renderPlan()},dayCap:()=>editDayCapacity(btn.dataset.date),
    backup,restore:()=>$('restore').click(),demo:demoData,install:async()=>{if(!installEvt)return;installEvt.prompt();const r=await installEvt.userChoice;installEvt=null;if(r.outcome==='accepted')toast('تم تثبيت التطبيق');renderMore()}}[a]||(()=>{}))();
});
$('roleChip').onclick=()=>openSheet({title:'اختر الدور',sub:'الشاشة الرئيسية والإجراءات تتغير حسب الدور',body:`<div class="card list" role="radiogroup" aria-label="الدور" style="box-shadow:none">${roleListHTML()}</div>`});
$('fabNew').onclick=()=>openOrderForm();
$('search').oninput=renderOrders;
$('operator').oninput=e=>{draft.operator=e.target.value;$('operatorChips').querySelectorAll('[data-op]').forEach(c=>c.setAttribute('aria-pressed',c.dataset.op===draft.operator.trim()))};
$('editStart').onclick=()=>{draft.editTime=!draft.editTime;renderMachine();if(draft.editTime)$('workStart').focus()};
$('startBtn').onclick=startSession;
$('goReport').onclick=()=>{reportType='daily';$('reportDate').value=localDay(now());tabSet('reports')};
$('prevPeriod').onclick=()=>{weekAnchor=calendarView==='week'?addDays(weekAnchor,-7):shiftMonth(weekAnchor,-1);selectedDay=calendarView==='week'?weekStart(weekAnchor):weekAnchor.slice(0,7)+'-01';renderPlan()};
$('nextPeriod').onclick=()=>{weekAnchor=calendarView==='week'?addDays(weekAnchor,7):shiftMonth(weekAnchor,1);selectedDay=calendarView==='week'?weekStart(weekAnchor):weekAnchor.slice(0,7)+'-01';renderPlan()};
$('thisWeek').onclick=()=>{const t=localDay(now());selectedDay=t;weekAnchor=t;renderPlan()};
$('weekView').onclick=()=>{calendarView='week';weekAnchor=selectedDay||localDay(now());renderPlan()};
$('monthView').onclick=()=>{calendarView='month';weekAnchor=selectedDay||localDay(now());renderPlan()};
['reportDate','reportFrom','reportTo'].forEach(x=>$(x).onchange=renderReport);
$('printReport').onclick=printReport;$('csv').onclick=csvReport;
$('restore').onchange=e=>{restore(e.target.files[0]);e.target.value=''};
let swipeX=null;$('calendar').addEventListener('touchstart',e=>{swipeX=e.touches[0].clientX},{passive:true});$('calendar').addEventListener('touchend',e=>{if(swipeX==null)return;const dx=e.changedTouches[0].clientX-swipeX;swipeX=null;if(Math.abs(dx)>60)(dx>0?$('nextPeriod'):$('prevPeriod')).click()},{passive:true});
window.addEventListener('storage',e=>{if(e.key===KEY){load();render()}});
window.addEventListener('beforeinstallprompt',e=>{e.preventDefault();installEvt=e;if(tab==='more')renderMore()});
window.addEventListener('appinstalled',()=>{installEvt=null;toast('تم تثبيت التطبيق على الشاشة الرئيسية')});
let hiddenAt=0;
document.addEventListener('visibilitychange',()=>{if(document.hidden){hiddenAt=now();return}render();
  if(hasPin(role)&&hiddenAt&&now()-hiddenAt>5*60000&&!sheet?.locked){if(sheet)closeSheet(true);lockScreen()}});

/* ================= PWA ================= */
if('serviceWorker' in navigator&&/^https?:$/.test(location.protocol)){navigator.serviceWorker.register('sw.js').then(reg=>{
  const offer=w=>toast('نسخة جديدة من التطبيق جاهزة',{label:'تحديث',action:()=>w.postMessage('skipWaiting')});
  if(reg.waiting&&navigator.serviceWorker.controller)offer(reg.waiting);
  reg.addEventListener('updatefound',()=>{const w=reg.installing;w?.addEventListener('statechange',()=>{if(w.state==='installed'&&navigator.serviceWorker.controller)offer(w)})});
}).catch(()=>{});let reloaded=false;navigator.serviceWorker.addEventListener('controllerchange',()=>{if(reloaded)return;reloaded=true;location.reload()})}

/* ================= Init ================= */
load();buildDial();
role=ROLES[prefs.role]?prefs.role:'manager';if(role==='finance')orderFilter='pending_invoice';
$('reportDate').value=localDay(now());$('reportFrom').value=localDay(now()).slice(0,7)+'-01';$('reportTo').value=localDay(now());
const qTab=new URLSearchParams(location.search).get('tab');
tabSet(['machine','orders','plan','reports','more'].includes(qTab)?qTab:(live()?'machine':ROLES[role].home));
if(hasPin(role))lockScreen();
setInterval(tickLive,1000);
setInterval(()=>{if(document.hidden)return;if(tab==='machine')renderMachine();renderChrome()},30000);
fileDB().catch(()=>toast('ملفات الرسومات تحتاج تخزينًا متاحًا في المتصفح'));
})();
