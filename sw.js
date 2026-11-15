/* TEI CNC service worker: app shell cached for full offline use. Bump VERSION on every release. */
const VERSION='tei-cnc-4.0.1';
const SHELL=['./','index.html','app.css','app.js','manifest.webmanifest','icons/icon-192.png','icons/icon-512.png','icons/maskable-512.png','icons/apple-touch-icon.png','fonts/readex-arabic.woff2','fonts/readex-latin.woff2','fonts/barlow-sc-500.woff2','fonts/barlow-sc-600.woff2','fonts/barlow-sc-700.woff2'];
self.addEventListener('install',e=>{e.waitUntil(caches.open(VERSION).then(c=>c.addAll(SHELL)))});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k!==VERSION).map(k=>caches.delete(k)))).then(()=>self.clients.claim()))});
self.addEventListener('message',e=>{if(e.data==='skipWaiting')self.skipWaiting()});
self.addEventListener('fetch',e=>{
  const req=e.request;if(req.method!=='GET'||new URL(req.url).origin!==location.origin)return;
  if(req.mode==='navigate'){e.respondWith(caches.match('index.html').then(r=>r||fetch(req)).catch(()=>caches.match('index.html')));return}
  e.respondWith(caches.match(req,{ignoreSearch:true}).then(hit=>hit||fetch(req).then(res=>{if(res.ok){const copy=res.clone();caches.open(VERSION).then(c=>c.put(req,copy))}return res})));
});
