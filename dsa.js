/* dsa.js - PART 1: data structures, algorithms and scheduling engine (no DOM code).
   PART 2 (at the bottom): the user interface that connects this logic to index.html. */
(function (root) {
// ---------- 1. Hash table (separate chaining) ----------
class HashTable {
  constructor(n = 16) { this.b = Array.from({ length: n }, () => []); this.size = 0; }
  hash(k) { let h = 5381; for (const c of String(k)) h = ((h << 5) + h + c.charCodeAt(0)) >>> 0; return h % this.b.length; }
  set(k, v) { const bk = this.b[this.hash(k)], e = bk.find(x => x[0] === k);
    if (e) e[1] = v; else { bk.push([k, v]); this.size++; if (this.size > this.b.length * 2) this.grow(); } }
  get(k) { const e = this.b[this.hash(k)].find(x => x[0] === k); return e ? e[1] : undefined; }
  has(k) { return this.get(k) !== undefined; }
  delete(k) { const bk = this.b[this.hash(k)], i = bk.findIndex(x => x[0] === k); if (i < 0) return false; bk.splice(i, 1); this.size--; return true; }
  grow() { const items = this.b.flat(); this.b = Array.from({ length: this.b.length * 2 }, () => []); this.size = 0; items.forEach(([k, v]) => this.set(k, v)); }
}
// ---------- 2. Singly linked list ----------
class LinkedList {
  constructor() { this.head = null; this.tail = null; this.size = 0; }
  append(data) { const n = { data, next: null }; if (!this.head) this.head = this.tail = n; else { this.tail.next = n; this.tail = n; } this.size++; }
  removeWhere(fn) { let prev = null, cur = this.head;
    while (cur) { if (fn(cur.data)) { if (prev) prev.next = cur.next; else this.head = cur.next; if (cur === this.tail) this.tail = prev; this.size--; return true; } prev = cur; cur = cur.next; } return false; }
  toArray() { const o = []; for (let c = this.head; c; c = c.next) o.push(c.data); return o; }
}
// ---------- 3. Queue (FIFO) and 4. Priority queue (binary min-heap) ----------
class Queue {
  constructor() { this.a = []; this.h = 0; }
  enqueue(x) { this.a.push(x); }
  dequeue() { return this.h < this.a.length ? this.a[this.h++] : undefined; }
  get size() { return this.a.length - this.h; }
  toArray() { return this.a.slice(this.h); }
}
class PriorityQueue {
  constructor(cmp) { this.cmp = cmp; this.h = []; }
  get size() { return this.h.length; }
  push(x) { const h = this.h; h.push(x); let i = h.length - 1;
    while (i > 0) { const p = (i - 1) >> 1; if (this.cmp(h[i], h[p]) >= 0) break; [h[i], h[p]] = [h[p], h[i]]; i = p; } }
  pop() { const h = this.h; if (!h.length) return undefined; const top = h[0], last = h.pop();
    if (h.length) { h[0] = last; let i = 0;
      for (;;) { let l = 2 * i + 1, r = l + 1, m = i;
        if (l < h.length && this.cmp(h[l], h[m]) < 0) m = l; if (r < h.length && this.cmp(h[r], h[m]) < 0) m = r;
        if (m === i) break; [h[i], h[m]] = [h[m], h[i]]; i = m; } }
    return top; }
  toArray() { return this.h.slice().sort(this.cmp); }
}
// ---------- Sorting (each returns a new array and counts comparisons in st.c) ----------
function mergeSort(a, cmp, st = { c: 0 }) {
  if (a.length < 2) return a.slice();
  const m = a.length >> 1, l = mergeSort(a.slice(0, m), cmp, st), r = mergeSort(a.slice(m), cmp, st), o = []; let i = 0, j = 0;
  while (i < l.length && j < r.length) { st.c++; o.push(cmp(l[i], r[j]) <= 0 ? l[i++] : r[j++]); }
  return o.concat(l.slice(i), r.slice(j));
}
function quickSort(a, cmp, st = { c: 0 }) {
  if (a.length < 2) return a.slice();
  const p = a[a.length >> 1], L = [], E = [], G = [];
  for (const x of a) { st.c++; const r = cmp(x, p); (r < 0 ? L : r > 0 ? G : E).push(x); }
  return [...quickSort(L, cmp, st), ...E, ...quickSort(G, cmp, st)];
}
function insertionSort(a, cmp, st = { c: 0 }) {
  const o = a.slice();
  for (let i = 1; i < o.length; i++) { const k = o[i]; let j = i - 1; while (j >= 0 && (st.c++, cmp(o[j], k) > 0)) { o[j + 1] = o[j]; j--; } o[j + 1] = k; }
  return o;
}
// ---------- Searching ----------
function linearSearch(arr, fn) { let c = 0; for (let i = 0; i < arr.length; i++) { c++; if (fn(arr[i])) return { index: i, comps: c }; } return { index: -1, comps: c }; }
function binarySearch(sorted, target, key = x => x) {
  let lo = 0, hi = sorted.length - 1; const steps = [];
  while (lo <= hi) { const mid = (lo + hi) >> 1, v = key(sorted[mid]); steps.push(`low=${lo}, high=${hi}, mid=${mid} -> ${v}`);
    if (v === target) return { index: mid, steps }; if (v < target) lo = mid + 1; else hi = mid - 1; }
  return { index: -1, steps };
}
// ---------- Tree and graph ----------
class TreeNode { constructor(name, kind) { this.name = name; this.kind = kind; this.children = []; }
  add(c) { this.children.push(c); return c; }
  dfs(o = []) { o.push(this.name); this.children.forEach(c => c.dfs(o)); return o; }
  bfs() { const o = [], q = [this]; while (q.length) { const n = q.shift(); o.push(n.name); q.push(...n.children); } return o; } }
class Graph {
  constructor() { this.adj = new Map(); }
  node(n) { if (!this.adj.has(n)) this.adj.set(n, new Set()); }
  edge(a, b) { this.node(a); this.node(b); this.adj.get(a).add(b); this.adj.get(b).add(a); }
  bfs(start) { const seen = new Map([[start, 0]]), q = [start];
    while (q.length) { const n = q.shift(); for (const m of this.adj.get(n) || []) if (!seen.has(m)) { seen.set(m, seen.get(n) + 1); q.push(m); } } return seen; }
}
// ---------- Date helpers and constants ----------
const PR = { Emergency: 0, Urgent: 1, Normal: 2 };
const SPEC_DEPT = { Cardiology: 'Medical Sciences', Neurology: 'Medical Sciences', 'General Medicine': 'Medical Sciences', Dermatology: 'Medical Sciences',
  Orthopedics: 'Surgical Sciences', ENT: 'Surgical Sciences', Pediatrics: 'Women & Child Care', Gynecology: 'Women & Child Care' };
const pad = n => String(n).padStart(2, '0');
const iso = d => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
const addDays = (s, n) => { const d = new Date(s + 'T00:00:00'); d.setDate(d.getDate() + n); return iso(d); };
const dow = s => new Date(s + 'T00:00:00').getDay();
const toMin = t => +t.slice(0, 2) * 60 + +t.slice(3);
const fromMin = m => pad(Math.floor(m / 60)) + ':' + pad(m % 60);
const slotTimes = d => { const o = []; for (let m = toMin(d.start); m + 30 <= toMin(d.end); m += 30) o.push(fromMin(m)); return o; };
const works = (d, date) => d.days.includes(dow(date));
const slotKey = a => `${a.did}|${a.date}|${a.time}`;

// ---------- Scheduling engine ----------
class Engine {
  constructor(S) { this.S = S; this.index(); }
  index() { const S = this.S;
    this.P = new HashTable(); S.patients.forEach(p => this.P.set(p.id, p));
    this.D = new HashTable(); S.doctors.forEach(d => this.D.set(d.id, d));
    this.A = new HashTable(); this.slots = new HashTable(); this.LL = new LinkedList();
    S.appointments.forEach(a => { this.A.set(a.id, a); this.LL.append(a); if (a.status !== 'Cancelled') this.slots.set(slotKey(a), a.id); });
    this.PQ = new PriorityQueue((x, y) => PR[x.prio] - PR[y.prio] || x.ts - y.ts); this.FQ = new Queue();
    S.waiting.forEach(w => (w.prio === 'Normal' ? this.FQ : this.PQ)[w.prio === 'Normal' ? 'enqueue' : 'push'](w)); }
  today() { return iso(new Date()); }
  nowMin() { const d = new Date(); return d.getHours() * 60 + d.getMinutes(); }
  note(msg) { this.S.notes.unshift({ msg, at: new Date().toLocaleString() }); this.S.notes.length = Math.min(this.S.notes.length, 30); }
  isPast(date, time) { const t = this.today(); return date < t || (date === t && toMin(time) <= this.nowMin()); }
  valid(doc, date, time) { return works(doc, date) && slotTimes(doc).includes(time) && !this.isPast(date, time); }
  isFree(doc, date, time) { return this.valid(doc, date, time) && !this.slots.has(`${doc.id}|${date}|${time}`); }
  load(doc, date) { return this.S.appointments.filter(a => a.did === doc.id && a.date === date && a.status !== 'Cancelled').length; }
  // Greedy: scan days in order, collect free slots, keep the earliest k (ties -> least busy doctor).
  greedy(docs, date, time, k = 5, days = 21) { const res = [];
    for (let i = 0; i < days && res.length < k; i++) { const d = addDays(date, i), day = [];
      docs.forEach(doc => { if (!works(doc, d)) return; slotTimes(doc).forEach(t => { if ((i > 0 || t >= time) && this.isFree(doc, d, t)) day.push({ doc, date: d, time: t }); }); });
      day.sort((a, b) => a.time.localeCompare(b.time) || this.load(a.doc, d) - this.load(b.doc, d)); res.push(...day); }
    return res.slice(0, k); }
  nextId() { return 'APT-' + (1000 + ++this.S.seq); }
  create(pid, doc, date, time, prio, reason) {
    const a = { id: this.nextId(), pid, did: doc.id, date, time, prio, status: 'Pending', reason: reason || '', created: Date.now() };
    this.S.appointments.push(a); this.A.set(a.id, a); this.LL.append(a); this.slots.set(slotKey(a), a.id);
    this.note(`${a.id} booked: ${this.P.get(pid).name} with ${doc.name} on ${date} at ${time} (${prio}).`); return a; }
  clash(pid, date, time, skipId) { return this.S.appointments.some(a => a.id !== skipId && a.pid === pid && a.date === date && a.time === time && a.status !== 'Cancelled'); }
  book({ pid, did, spec, date, time, prio, reason }) {
    if (!this.P.get(pid)) return { ok: false, error: 'Select a registered patient.' };
    if (!date || !time) return { ok: false, error: 'Choose a date and time.' };
    if (this.isPast(date, time)) return { ok: false, error: 'That date and time has already passed.' };
    const docs = did ? [this.D.get(did)] : this.S.doctors.filter(d => d.spec === spec);
    if (!docs.length || !docs[0]) return { ok: false, error: 'No doctor found for this selection.' };
    if (this.clash(pid, date, time)) return { ok: false, error: 'This patient already has an appointment at that time.' };
    const free = docs.filter(d => this.isFree(d, date, time)).sort((a, b) => this.load(a, date) - this.load(b, date));
    if (free.length) return { ok: true, appt: this.create(pid, free[0], date, time, prio, reason) };
    if (prio === 'Emergency') for (const doc of docs) { const id = this.slots.get(`${doc.id}|${date}|${time}`), a = id && this.A.get(id);
      if (a && a.prio === 'Normal' && a.status === 'Pending' && this.valid(doc, date, time)) {
        const alt = this.greedy(docs, date, time, 1)[0]; if (!alt) continue;
        this.slots.delete(slotKey(a)); a.did = alt.doc.id; a.date = alt.date; a.time = alt.time; this.slots.set(slotKey(a), a.id);
        this.note(`Emergency priority: ${a.id} was moved to ${alt.date} ${alt.time} to free the slot.`);
        return { ok: true, appt: this.create(pid, doc, date, time, prio, reason), bumped: a }; } }
    return { ok: false, error: 'The requested slot is not available.', alts: this.greedy(docs, date, time, 5) };
  }
  reschedule(id, date, time) { const a = this.A.get(id), doc = this.D.get(a.did);
    if (this.isPast(date, time)) return { ok: false, error: 'That date and time has already passed.' };
    if (this.clash(a.pid, date, time, id)) return { ok: false, error: 'Patient already has an appointment at that time.' };
    if (!this.isFree(doc, date, time)) return { ok: false, error: `${doc.name} is not available then.`, alts: this.greedy([doc], date, time, 5) };
    this.slots.delete(slotKey(a)); a.date = date; a.time = time; this.slots.set(slotKey(a), a.id);
    this.note(`${a.id} rescheduled to ${date} at ${time}.`); return { ok: true, appt: a }; }
  setStatus(id, st) { const a = this.A.get(id); a.status = st; if (st === 'Cancelled') this.slots.delete(slotKey(a)); else this.slots.set(slotKey(a), a.id);
    this.note(`${id} marked ${st}.`); }
  addWaiting(pid, spec, prio) { const w = { id: 'W-' + (++this.S.seq), pid, spec, prio, ts: Date.now() }; this.S.waiting.push(w);
    (prio === 'Normal' ? this.FQ.enqueue(w) : this.PQ.push(w)); return w; }
  // Serve urgent/emergency requests (heap) first, then normal requests (FIFO queue).
  processWaiting() { const log = [], keep = [];
    const serve = (w, via) => { const p = this.P.get(w.pid), docs = this.S.doctors.filter(d => d.spec === w.spec);
      const alt = this.greedy(docs, this.today(), '00:00', 8).find(s => !this.clash(w.pid, s.date, s.time));
      if (!alt) { keep.push(w); log.push(`${via}: ${w.prio} ${p.name} (${w.spec}) - no free slot, kept waiting.`); return; }
      const a = this.create(w.pid, alt.doc, alt.date, alt.time, w.prio, 'From waiting list');
      log.push(`${via}: ${w.prio} ${p.name} -> ${a.id} with ${alt.doc.name}, ${alt.date} ${alt.time}`); };
    while (this.PQ.size) serve(this.PQ.pop(), 'Priority queue');
    while (this.FQ.size) serve(this.FQ.dequeue(), 'FIFO queue');
    this.S.waiting = keep; this.index(); return log; }
  freeSlotCount(days = 7) { let n = 0; const t = this.today();
    for (let i = 0; i < days; i++) { const d = addDays(t, i); this.S.doctors.forEach(doc => slotTimes(doc).forEach(s => { if (this.isFree(doc, d, s)) n++; })); } return n; }
}
// ---------- Sample data ----------
function seed() {
  const t = iso(new Date()), M = [1, 2, 3, 4, 5];
  const doctors = [['Dr. Ananya Sharma', 'Cardiology', M, '09:00', '16:00'], ['Dr. Rohan Mehta', 'Cardiology', [1, 3, 5], '10:00', '17:00'],
    ['Dr. Priya Nair', 'General Medicine', [1, 2, 3, 4, 5, 6], '09:00', '17:00'], ['Dr. Vikram Singh', 'Orthopedics', M, '10:00', '16:00'],
    ['Dr. Kavita Rao', 'Pediatrics', [1, 2, 4, 5, 6], '09:00', '15:00'], ['Dr. Sameer Khan', 'Neurology', [2, 3, 4], '11:00', '17:00'],
    ['Dr. Neha Kapoor', 'Dermatology', M, '10:00', '15:00'], ['Dr. Arjun Verma', 'ENT', [1, 2, 3, 4, 5], '09:30', '14:30'],
    ['Dr. Meera Iyer', 'Gynecology', [1, 3, 5, 6], '09:00', '15:00']]
    .map((d, i) => ({ id: 'DOC-' + pad(i + 1), name: d[0], spec: d[1], days: d[2], start: d[3], end: d[4] }));
  const patients = [['Rahul Gupta', 45, '9810012345', 'Chest pain'], ['Sneha Joshi', 29, '9899001122', 'Migraine'], ['Aarav Malhotra', 7, '9811122233', 'Fever and cough'],
    ['Pooja Yadav', 33, '9873345566', 'Routine check-up'], ['Imran Ali', 52, '9958887766', 'Knee pain'], ['Divya Menon', 26, '9818899001', 'Skin allergy'],
    ['Karan Bhatia', 38, '9871100223', 'Ear infection'], ['Sunita Devi', 61, '9910022334', 'High blood pressure'], ['Mohit Saxena', 41, '9899955544', 'Back pain'],
    ['Anjali Thakur', 31, '9818123456', 'Prenatal check-up'], ['Rhea Kapoor', 5, '9811567890', 'Vaccination'], ['Deepak Chauhan', 58, '9953344556', 'Dizziness']]
    .map((p, i) => ({ id: 'PAT-' + (1001 + i), name: p[0], age: p[1], contact: p[2], issue: p[3] }));
  const S = { patients, doctors, appointments: [], waiting: [], notes: [], seq: 0, seeded: t };
  const E = new Engine(S);
  const plan = [[0, 0, 1, '10:00', 'Normal'], [1, 5, 2, '11:30', 'Urgent'], [2, 4, 1, '09:30', 'Normal'], [3, 2, 1, '09:00', 'Normal'], [4, 3, 2, '10:30', 'Normal'],
    [5, 6, 3, '11:00', 'Normal'], [6, 7, 1, '10:00', 'Normal'], [7, 1, 2, '10:30', 'Urgent'], [8, 3, 3, '12:00', 'Normal'], [9, 8, 2, '09:30', 'Normal'],
    [10, 4, 3, '10:00', 'Normal'], [11, 5, 4, '12:00', 'Urgent'], [0, 0, 4, '14:00', 'Normal'], [3, 2, 5, '10:00', 'Normal'],
    [1, 5, -2, '11:00', 'Normal', 'Completed'], [4, 3, -3, '11:00', 'Normal', 'Completed'], [7, 1, -1, '12:00', 'Emergency', 'Completed'], [2, 4, -4, '10:00', 'Normal', 'Completed'],
    [6, 7, -2, '09:30', 'Normal', 'Cancelled'], [8, 2, -5, '14:00', 'Normal', 'Completed']];
  plan.forEach(([p, d, off, time, prio, st]) => { const doc = doctors[d]; let date = t; const step = off < 0 ? -1 : 1; let n = Math.abs(off);
    while (n > 0) { date = addDays(date, step); if (works(doc, date)) n--; }
    const a = { id: E.nextId(), pid: patients[p].id, did: doc.id, date, time, prio, status: st || 'Pending', reason: patients[p].issue, created: 1e12 + E.S.seq };
    if (!E.slots.has(slotKey(a))) { S.appointments.push(a); E.index(); } });
  S.notes = [{ msg: 'Welcome! Sample hospital data has been loaded.', at: new Date().toLocaleString() }];
  return S;
}
const API = { HashTable, LinkedList, Queue, PriorityQueue, mergeSort, quickSort, insertionSort, linearSearch, binarySearch, TreeNode, Graph, Engine, seed,
  PR, SPEC_DEPT, pad, iso, addDays, slotTimes, works, toMin, fromMin };
if (typeof module !== 'undefined') module.exports = API; else root.DSA = API;
})(this);


/* ===== PART 2: user interface (renders into <main id="view">, handles all events) ===== */
if (typeof document !== 'undefined') (function () {
const { Engine, seed, HashTable, mergeSort, quickSort, insertionSort, linearSearch, binarySearch, TreeNode, Graph, PR, SPEC_DEPT, slotTimes, works, addDays } = DSA;
const KEY = 'medislot_v1';
let S = null; try { S = JSON.parse(localStorage.getItem(KEY)); } catch (e) {}
if (!S || !S.patients || !S.doctors) S = seed();
const E = new Engine(S);
const $ = (s, e = document) => e.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = d => new Date(d + 'T00:00:00').toLocaleDateString('en-IN', { day: 'numeric', month: 'short', year: 'numeric' });
const pn = id => E.P.get(id)?.name || '(removed)', dn = id => E.D.get(id)?.name || '(removed)';
const badge = t => `<span class="badge b-${t}">${t}</span>`;
const SPECS = Object.keys(SPEC_DEPT), DAYS = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
const UI = { ps: '', ds: '', dspec: '', af: { q: '', date: '', doc: '', pat: '', prio: '', status: '' }, sort: 'date', alg: 'merge' };
const save = () => { try { localStorage.setItem(KEY, JSON.stringify(S)); } catch (e) {} updBell(); };
let tt; const toast = m => { const t = $('#toast'); t.textContent = m; t.classList.add('show'); clearTimeout(tt); tt = setTimeout(() => t.classList.remove('show'), 2800); };
const opts = (list, sel, first) => (first !== undefined ? `<option value="">${first}</option>` : '') + list.map(([v, l]) => `<option value="${esc(v)}" ${v === sel ? 'selected' : ''}>${esc(l)}</option>`).join('');
const patOpts = sel => opts(S.patients.map(p => [p.id, `${p.name} (${p.id})`]), sel);

// ---------- modal + generic form ----------
const openModal = (title, html) => { $('#mt').textContent = title; $('#mb').innerHTML = html; $('#modal').hidden = false; };
const closeModal = () => { $('#modal').hidden = true; };
function fld(f, v) { const val = v[f.n] ?? ''; let i;
  if (f.t === 'select') i = `<select name="${f.n}">${opts(f.o, val)}</select>`;
  else if (f.t === 'textarea') i = `<textarea name="${f.n}" rows="2">${esc(val)}</textarea>`;
  else if (f.t === 'days') i = `<div class="days">${DAYS.map((d, k) => `<label><input type="checkbox" name="days" value="${k}" ${(v.days || []).includes(k) ? 'checked' : ''}>${d}</label>`).join('')}</div>`;
  else i = `<input name="${f.n}" type="${f.t}" value="${esc(val)}" ${f.min !== undefined ? `min="${f.min}"` : ''} ${f.max !== undefined ? `max="${f.max}"` : ''} ${f.step ? `step="${f.step}"` : ''}>`;
  return `<div class="fld"><label>${f.l}</label>${i}</div>`; }
const form = (name, title, fields, v = {}, btn = 'Save') => openModal(title, `<form data-form="${name}" novalidate>${fields.map(f => fld(f, v)).join('')}<div class="ferr"></div><button class="btn" type="submit">${btn}</button></form>`);
const FORMS = {};
document.addEventListener('submit', e => { e.preventDefault(); const f = e.target, v = {}; new FormData(f).forEach((x, k) => v[k] = x);
  v.days = [...f.querySelectorAll('[name=days]:checked')].map(x => +x.value);
  const r = FORMS[f.dataset.form](v); if (r) f.querySelector('.ferr').innerHTML = `<div class="msg err">${r.err || r}</div>${r.html || ''}`; else closeModal(); });

// ---------- shared pieces ----------
const apptRows = (list, acts) => list.length ? `<table><tr><th>ID</th><th>Patient</th><th>Doctor</th><th>Date</th><th>Time</th><th>Priority</th><th>Status</th>${acts ? '<th>Actions</th>' : ''}</tr>` +
  list.map(a => `<tr><td><b>${a.id}</b></td><td>${esc(pn(a.pid))}</td><td>${esc(dn(a.did))}</td><td>${fmt(a.date)}</td><td>${a.time}</td><td>${badge(a.prio)}</td><td>${badge(a.status)}</td>` +
    (acts ? `<td class="acts">${a.status === 'Pending' ? `<button class="btn sm ghost" data-act="done" data-id="${a.id}">Complete</button><button class="btn sm ghost" data-act="resch" data-id="${a.id}">Reschedule</button><button class="btn sm red" data-act="cancel" data-id="${a.id}">Cancel</button>` : '-'}</td>` : '') + '</tr>').join('') + '</table>'
  : '<div class="empty">No appointments match.</div>';
const altBtns = (alts, act, extra = '') => alts.length ? `<p>Suggested alternative slots (earliest first):</p><div class="alts">${alts.map(s => `<button class="btn sm" data-act="${act}" data-doc="${s.doc.id}" data-date="${s.date}" data-time="${s.time}" ${extra}>${fmt(s.date)} ${s.time} - ${esc(s.doc.name)}</button>`).join('')}</div>` : '<p>No free slots in the next 3 weeks.</p>';
const bars = (rows, color) => { const m = Math.max(1, ...rows.map(r => r[1])); return `<div class="bars">${rows.map(([l, n]) => `<div class="b"><span>${esc(l)}</span><div class="t"><i style="width:${n / m * 100}%;${color ? 'background:' + color : ''}"></i></div><b>${n}</b></div>`).join('')}</div>`; };
const active = () => S.appointments.filter(a => a.status !== 'Cancelled');

// ---------- pages ----------
const PAGES = {};
PAGES.home = () => `<section class="hero"><div><h1>Appointments scheduled by algorithms, not guesswork.</h1><p>MediSlot checks every doctor's availability, ranks patients by urgency and books the earliest conflict-free slot - built on hash tables, heaps, queues, linked lists, trees and graphs.</p>
<div class="actions"><button class="btn" data-act="go" data-to="book">Book appointment</button><button class="btn ghost" data-act="go" data-to="dsa">See the DSA in action</button></div></div>
<div class="slots-demo"><h3>Dr. Priya Nair - General Medicine</h3><div class="s"><span>09:00</span><span>Booked</span></div><div class="s x"><span>09:30</span><span>Emergency</span></div><div class="s n"><span>10:00</span><span>Urgent</span></div><div class="s"><span>10:30</span><span>Free - suggested</span></div></div></section>
<h2>What it does</h2><div class="grid g3">${[['&#129489;&#8205;&#9877;&#65039;', 'Patient & doctor records', 'Register patients, manage doctor profiles and weekly availability.'], ['&#9889;', 'Priority scheduling', 'Emergency and urgent patients are served before normal requests.'], ['&#128197;', 'Conflict-free booking', 'A hash table makes double booking impossible for any doctor and time.'], ['&#128260;', 'Alternative slots', 'If a slot is taken, a greedy search suggests the nearest free ones.'], ['&#128202;', 'Live dashboard', 'Counts, charts and free slots update with every booking.'], ['&#127891;', 'DSA lab', 'Run each data structure and algorithm on the real hospital data.']].map(f => `<div class="card feat"><i>${f[0]}</i><h3>${f[1]}</h3><p>${f[2]}</p></div>`).join('')}</div>
<h2>How scheduling works</h2><div class="card grid g2">${['Patient and doctor are validated through hash-table lookups.', 'The requested slot is checked in the slot hash table.', 'If it is taken, an emergency may move a normal booking; otherwise the greedy search finds the nearest free slots.', 'Requests without a slot wait in the priority queue (urgent) or FIFO queue (normal) until processed.'].map((t, i) => `<div class="step"><b>${i + 1}</b><p>${t}</p></div>`).join('')}</div>`;

PAGES.dashboard = () => { const A = S.appointments, st = k => A.filter(a => a.status === k).length, t = E.today();
  const stat = (i, n, l) => `<div class="card stat"><i>${i}</i><div><b>${n}</b><span>${l}</span></div></div>`;
  const c = [st('Pending'), st('Completed'), st('Cancelled')], tot = Math.max(1, A.length), p1 = c[0] / tot * 100, p2 = p1 + c[1] / tot * 100;
  const week = [...Array(7)].map((_, i) => { const d = addDays(t, i); return [DAYS[new Date(d + 'T00:00').getDay()] + ' ' + d.slice(8), active().filter(a => a.date === d).length]; });
  return `<div class="head"><div><h2>Dashboard</h2><p>Live overview of the hospital schedule</p></div><button class="btn" data-act="go" data-to="book">+ New appointment</button></div>
<div class="grid g6">${stat('&#129489;', S.patients.length, 'Total patients')}${stat('&#129658;', S.doctors.length, 'Total doctors')}${stat('&#128197;', A.length, 'Total appointments')}${stat('&#9203;', c[0], 'Pending')}${stat('&#9989;', c[1], 'Completed')}${stat('&#128994;', E.freeSlotCount(), 'Free slots (next 7 days)')}</div><br>
<div class="grid g2"><div class="card"><h3>Appointments by status</h3><div class="donut" style="background:conic-gradient(#e69500 0 ${p1}%,#1f9d63 ${p1}% ${p2}%,#d93a3a ${p2}% 100%)"></div><div class="legend"><span><i style="background:#e69500"></i>Pending ${c[0]}</span><span><i style="background:#1f9d63"></i>Completed ${c[1]}</span><span><i style="background:#d93a3a"></i>Cancelled ${c[2]}</span></div></div>
<div class="card"><h3>Active appointments by priority</h3>${bars(['Emergency', 'Urgent', 'Normal'].map(p => [p, active().filter(a => a.prio === p).length]))}<h3 style="margin-top:16px">Next 7 days</h3>${bars(week)}</div></div>
<div class="grid g2"><div class="card"><h3>Pending appointments per doctor</h3>${bars(S.doctors.map(d => [d.name, A.filter(a => a.did === d.id && a.status === 'Pending').length]), '#4aa3f0')}</div>
<div class="card"><h3>Recent appointments</h3><div class="tw">${apptRows([...A].sort((a, b) => b.created - a.created).slice(0, 6))}</div></div></div>`; };

PAGES.patients = () => `<div class="head"><div><h2>Patient Management</h2><p id="pinfo"></p></div><button class="btn" data-act="addPatient">+ Add patient</button></div><div class="card"><div class="row"><input data-in="ps" placeholder="Search by name or patient ID (e.g. PAT-1003)" value="${esc(UI.ps)}"></div><div class="tw" id="ptbl"></div></div>`;
function drawPatients() { const q = UI.ps.trim(); let list = S.patients, info = `${list.length} registered patients (stored in an array)`;
  if (q) { const hit = E.P.get(q.toUpperCase()); if (hit) { list = [hit]; info = 'Exact ID found with a hash-table lookup - O(1)'; } else { const ql = q.toLowerCase(), st = { c: 0 };
    list = S.patients.filter(p => { st.c++; return p.name.toLowerCase().includes(ql) || p.id.toLowerCase().includes(ql); }); info = `Linear search checked ${st.c} records - ${list.length} match`; } }
  $('#pinfo').textContent = info;
  $('#ptbl').innerHTML = list.length ? `<table><tr><th>ID</th><th>Name</th><th>Age</th><th>Contact</th><th>Medical issue</th><th>Actions</th></tr>${list.map(p => `<tr><td><b>${p.id}</b></td><td>${esc(p.name)}</td><td>${p.age}</td><td>${p.contact}</td><td>${esc(p.issue)}</td><td class="acts"><button class="btn sm ghost" data-act="editPatient" data-id="${p.id}">Edit</button><button class="btn sm red" data-act="delPatient" data-id="${p.id}">Delete</button></td></tr>`).join('')}</table>` : '<div class="empty">No patient found. Try another name or ID.</div>'; }
const patFields = [{ n: 'name', l: 'Full name', t: 'text' }, { n: 'age', l: 'Age', t: 'number', min: 0, max: 120 }, { n: 'contact', l: 'Contact number (10 digits)', t: 'tel' }, { n: 'issue', l: 'Medical issue', t: 'textarea' }];
function patCheck(v) { if (!/^[A-Za-z][A-Za-z .'-]{1,}$/.test(v.name.trim())) return 'Enter a valid name (letters only, at least 2 characters).';
  if (!/^\d+$/.test(v.age) || +v.age > 120) return 'Age must be a whole number between 0 and 120.';
  if (!/^[6-9]\d{9}$/.test(v.contact.trim())) return 'Contact must be a 10-digit mobile number starting with 6-9.';
  if (v.issue.trim().length < 3) return 'Describe the medical issue (at least 3 characters).'; }
FORMS.patient = v => { const e = patCheck(v); if (e) return e; const id = v.id;
  if (id) { Object.assign(E.P.get(id), { name: v.name.trim(), age: +v.age, contact: v.contact.trim(), issue: v.issue.trim() }); toast('Patient updated'); }
  else { const n = Math.max(1000, ...S.patients.map(p => +p.id.slice(4))) + 1; S.patients.push({ id: 'PAT-' + n, name: v.name.trim(), age: +v.age, contact: v.contact.trim(), issue: v.issue.trim() }); E.index(); toast('Patient PAT-' + n + ' added'); }
  save(); refresh(); };

PAGES.doctors = () => `<div class="head"><div><h2>Doctor Management</h2><p id="dinfo"></p></div><button class="btn" data-act="addDoctor">+ Add doctor</button></div>
<div class="row"><input data-in="ds" placeholder="Search by doctor name or ID" value="${esc(UI.ds)}"><select data-in="dspec">${opts(SPECS.map(s => [s, s]), UI.dspec, 'All specializations')}</select></div><div class="grid g3" id="dgrid"></div>`;
function drawDoctors() { const q = UI.ds.trim().toLowerCase(); const list = S.doctors.filter(d => (!UI.dspec || d.spec === UI.dspec) && (!q || d.name.toLowerCase().includes(q) || d.id.toLowerCase().includes(q)));
  $('#dinfo').textContent = `${list.length} of ${S.doctors.length} doctors shown`;
  $('#dgrid').innerHTML = list.length ? list.map(d => `<div class="card doc"><div class="av">${d.name.split(' ').slice(-1)[0][0]}</div><h3>${esc(d.name)}</h3><p>${d.spec} - ${SPEC_DEPT[d.spec]}<br><small>${d.id} - ${d.start} to ${d.end}</small></p>${DAYS.map((x, i) => `<span class="chip ${d.days.includes(i) ? '' : 'off'}">${x}</span>`).join('')}<div class="row" style="margin:12px 0 0"><button class="btn sm ghost" data-act="sched" data-id="${d.id}">Schedule</button><button class="btn sm ghost" data-act="editDoctor" data-id="${d.id}">Edit</button><button class="btn sm red" data-act="delDoctor" data-id="${d.id}">Delete</button></div></div>`).join('') : '<div class="empty">No doctors match.</div>'; }
const docFields = [{ n: 'name', l: 'Doctor name', t: 'text' }, { n: 'spec', l: 'Specialization', t: 'select', o: SPECS.map(s => [s, s]) }, { n: 'days', l: 'Available days', t: 'days' }, { n: 'start', l: 'Shift starts', t: 'time' }, { n: 'end', l: 'Shift ends', t: 'time' }];
FORMS.doctor = v => { const nm = v.name.trim().replace(/^Dr\.?\s*/i, '');
  if (!/^[A-Za-z][A-Za-z .'-]{1,}$/.test(nm)) return 'Enter a valid doctor name.'; if (!v.days.length) return 'Select at least one available day.';
  if (!v.start || !v.end || v.start >= v.end) return 'Shift end time must be after the start time.'; if (DSA.toMin(v.end) - DSA.toMin(v.start) < 30) return 'A shift needs at least one 30-minute slot.';
  if (v.id) { const d = E.D.get(v.id); Object.assign(d, { name: 'Dr. ' + nm, spec: v.spec, days: v.days, start: v.start, end: v.end });
    const bad = S.appointments.filter(a => a.did === d.id && a.status === 'Pending' && !works(d, a.date) || a.did === d.id && a.status === 'Pending' && !slotTimes(d).includes(a.time));
    if (bad.length) { E.note(`${d.name}'s new schedule conflicts with ${bad.length} pending appointment(s): ${bad.map(a => a.id).join(', ')}. Please reschedule them.`); toast('Saved - some appointments need rescheduling'); } else toast('Doctor updated'); }
  else { const n = Math.max(0, ...S.doctors.map(d => +d.id.slice(4))) + 1; S.doctors.push({ id: 'DOC-' + DSA.pad(n), name: 'Dr. ' + nm, spec: v.spec, days: v.days, start: v.start, end: v.end }); E.index(); toast('Doctor added'); }
  save(); refresh(); };

PAGES.book = () => `<div class="head"><div><h2>Book Appointment</h2><p>Slots are checked against doctor availability and existing bookings before anything is saved.</p></div></div>
<div class="grid g2"><div class="card"><div class="fld"><label>Patient</label><select id="bp">${patOpts(UI.last?.pid)}</select></div>
<div class="row"><div><label>Specialization</label><select id="bs" data-in="bspec">${opts(SPECS.map(s => [s, s]), UI.last?.spec || 'General Medicine')}</select></div><div><label>Doctor</label><select id="bd"></select></div></div>
<div class="row"><div><label>Preferred date</label><input type="date" id="bdate" min="${E.today()}" value="${UI.last?.date || addDays(E.today(), 1)}"></div><div><label>Preferred time</label><input type="time" id="btime" step="1800" value="${UI.last?.time || '10:00'}"></div></div>
<div class="row"><div><label>Priority</label><select id="bpr">${opts(['Normal', 'Urgent', 'Emergency'].map(p => [p, p]), UI.last?.prio)}</select></div><div><label>Reason (optional)</label><input id="br" placeholder="e.g. follow-up visit"></div></div>
<div class="row"><button class="btn" data-act="doBook">Book appointment</button><button class="btn ghost" data-act="check">Check availability</button><button class="btn ghost" data-act="toWait">Add to waiting list</button></div></div>
<div class="card"><h3>Result</h3><div id="bres"><div class="msg info">Pick a patient, doctor and time, then choose <b>Check availability</b> or <b>Book appointment</b>. If your slot is taken, the nearest free slots appear here.</div></div></div></div>`;
function fillDocs(sel) { const sp = $('#bs').value; $('#bd').innerHTML = opts(S.doctors.filter(d => d.spec === sp).map(d => [d.id, `${d.name} (${d.start}-${d.end})`]), sel, 'Any available doctor (auto-match)'); }
const bv = () => ({ pid: $('#bp').value, spec: $('#bs').value, did: $('#bd').value, date: $('#bdate').value, time: $('#btime').value, prio: $('#bpr').value, reason: $('#br').value.trim() });
function showBook(r, f) { UI.last = f; const el = $('#bres');
  if (r.ok) { const a = r.appt; el.innerHTML = `<div class="confirm"><h3>Appointment confirmed</h3><p><b>${a.id}</b></p><p>${esc(pn(a.pid))} with ${esc(dn(a.did))}<br>${fmt(a.date)} at ${a.time} - ${badge(a.prio)}</p>${r.bumped ? `<div class="msg info">Emergency priority: ${r.bumped.id} (${esc(pn(r.bumped.pid))}) was moved to ${fmt(r.bumped.date)} ${r.bumped.time}.</div>` : ''}</div>`; toast('Booked ' + a.id); save(); }
  else el.innerHTML = `<div class="msg err">${r.error}</div>${r.alts ? altBtns(r.alts, 'bookAlt') : ''}`; }

PAGES.scheduler = () => `<div class="head"><div><h2>Smart Scheduler</h2><p>Waiting requests are served by priority, then arrival order.</p></div></div>
<div class="card"><h3>How the engine decides</h3><div class="grid g2"><div><p><b>1. Availability check</b> - the doctor must work that weekday, the time must fall inside the shift and on a 30-minute slot, and it must not be in the past.</p><p><b>2. Conflict check</b> - slot key <code>doctor|date|time</code> is looked up in a hash table (O(1)). A patient also cannot hold two appointments at the same time.</p></div>
<div><p><b>3. Matching</b> - with "any doctor", all doctors of the specialization are tried and the least busy one that day is chosen.</p><p><b>4. Priority and alternatives</b> - an Emergency request can move a Normal booking to its next free slot. Otherwise the greedy search returns the earliest free slots.</p></div></div></div>
<div class="grid g2"><div class="card"><h3>Add a waiting request</h3><div class="fld"><label>Patient</label><select id="wp">${patOpts()}</select></div><div class="row"><div><label>Specialization</label><select id="ws">${opts(SPECS.map(s => [s, s]))}</select></div><div><label>Priority</label><select id="wpr">${opts(['Normal', 'Urgent', 'Emergency'].map(p => [p, p]))}</select></div></div><button class="btn" data-act="addWait">Add to queue</button> <button class="btn ghost" data-act="process">Process queue</button><pre id="wlog">Process queue assigns the earliest free slot to each waiting request.</pre></div>
<div class="card"><h3>Priority queue (Urgent / Emergency)</h3>${waitList(E.PQ.toArray())}<h3 style="margin-top:14px">FIFO queue (Normal)</h3>${waitList(E.FQ.toArray())}</div></div>`;
const waitList = l => l.length ? `<table><tr><th>Patient</th><th>Needs</th><th>Priority</th><th></th></tr>${l.map(w => `<tr><td>${esc(pn(w.pid))}</td><td>${w.spec}</td><td>${badge(w.prio)}</td><td><button class="btn sm red" data-act="rmWait" data-id="${w.id}">Remove</button></td></tr>`).join('')}</table>` : '<div class="empty">Queue is empty.</div>';

PAGES.appointments = () => { const f = UI.af; return `<div class="head"><div><h2>Appointments</h2><p id="ainfo"></p></div><button class="btn" data-act="go" data-to="book">+ New appointment</button></div>
<div class="card"><div class="row"><input data-in="af" data-k="q" placeholder="Search ID, patient or doctor" value="${esc(f.q)}"><input type="date" data-in="af" data-k="date" value="${f.date}" title="Date"><select data-in="af" data-k="doc">${opts(S.doctors.map(d => [d.id, d.name]), f.doc, 'All doctors')}</select><select data-in="af" data-k="pat">${opts(S.patients.map(p => [p.id, p.name]), f.pat, 'All patients')}</select></div>
<div class="row"><select data-in="af" data-k="prio">${opts(['Emergency', 'Urgent', 'Normal'].map(p => [p, p]), f.prio, 'All priorities')}</select><select data-in="af" data-k="status">${opts(['Pending', 'Completed', 'Cancelled'].map(p => [p, p]), f.status, 'All statuses')}</select>
<select data-in="sort">${opts([['date', 'Sort: date & time'], ['prio', 'Sort: priority'], ['pat', 'Sort: patient'], ['doc', 'Sort: doctor']], UI.sort)}</select><select data-in="alg">${opts([['merge', 'Merge sort'], ['quick', 'Quick sort'], ['ins', 'Insertion sort']], UI.alg)}</select><button class="btn ghost" data-act="clearF">Clear filters</button></div><div class="tw" id="atbl"></div></div>`; };
const CMP = { date: (a, b) => (a.date + a.time).localeCompare(b.date + b.time), prio: (a, b) => PR[a.prio] - PR[b.prio] || CMP.date(a, b), pat: (a, b) => pn(a.pid).localeCompare(pn(b.pid)) || CMP.date(a, b), doc: (a, b) => dn(a.did).localeCompare(dn(b.did)) || CMP.date(a, b) };
function drawAppts() { const f = UI.af, q = f.q.trim().toLowerCase();
  const list = S.appointments.filter(a => (!f.date || a.date === f.date) && (!f.doc || a.did === f.doc) && (!f.pat || a.pid === f.pat) && (!f.prio || a.prio === f.prio) && (!f.status || a.status === f.status) && (!q || a.id.toLowerCase().includes(q) || pn(a.pid).toLowerCase().includes(q) || dn(a.did).toLowerCase().includes(q)));
  const st = { c: 0 }, sorted = { merge: mergeSort, quick: quickSort, ins: insertionSort }[UI.alg](list, CMP[UI.sort], st);
  $('#ainfo').textContent = `${sorted.length} of ${S.appointments.length} shown - ${{ merge: 'merge sort', quick: 'quick sort', ins: 'insertion sort' }[UI.alg]} used ${st.c} comparisons`; $('#atbl').innerHTML = apptRows(sorted, true); }

// ---------- DSA lab ----------
const dcard = (t, use, ctl, id) => `<div class="card"><h3>${t}</h3><p>${use}</p>${ctl}<div class="flow" id="o-${id}"></div></div>`;
const out = (id, html) => { $('#o-' + id).innerHTML = html; };
const flow = (items, sep = '&rarr;') => items.map(x => `<span class="node">${esc(x)}</span>`).join(`<span class="arrow">${sep}</span>`);
const pre = t => `<pre style="width:100%">${esc(t)}</pre>`;
function buildTree() { const r = new TreeNode('MediSlot Hospital', 'root'), dep = {};
  S.doctors.forEach(d => { const dn_ = SPEC_DEPT[d.spec]; const D = dep[dn_] || (dep[dn_] = r.add(new TreeNode(dn_, 'dept'))); let sp = D.children.find(c => c.name === d.spec) || D.add(new TreeNode(d.spec, 'spec')); sp.add(new TreeNode(d.name, 'doc')); }); return r; }
const treeHtml = n => `<li>${esc(n.name)}<span class="k">${n.kind}</span>${n.children.length ? `<ul>${n.children.map(treeHtml).join('')}</ul>` : ''}</li>`;
function buildGraph() { const g = new Graph(), L = {};
  S.patients.forEach(p => { L['P:' + p.id] = 'Patient ' + p.name; }); S.doctors.forEach(d => { L['D:' + d.id] = d.name; g.edge('D:' + d.id, 'S:' + d.spec); L['S:' + d.spec] = d.spec; g.edge('S:' + d.spec, 'T:' + SPEC_DEPT[d.spec]); L['T:' + SPEC_DEPT[d.spec]] = SPEC_DEPT[d.spec] + ' dept'; });
  active().forEach(a => g.edge('P:' + a.pid, 'D:' + a.did)); return { g, L }; }
PAGES.dsa = () => `<div class="head"><div><h2>DSA Implementation Lab</h2><p>Every demo below runs on your live hospital data - the same structures that power booking.</p></div></div><div class="grid g2">
${dcard('1. Arrays', 'Used for: patients, doctors and appointments are arrays; every table is a loop over them and index access is O(1).', '<button class="btn sm" data-act="d" data-d="array">Inspect arrays</button>', 'array')}
${dcard('2. Hash table', 'Used for: patient, doctor and appointment lookup by ID, and the slot table that blocks double booking. Separate chaining, djb2 hash.', `<div class="row"><input id="hid" value="${S.patients[0]?.id || ''}" placeholder="Patient ID"><button class="btn sm" data-act="d" data-d="hash">Lookup</button></div>`, 'hash')}
${dcard('3. Linked list', 'Used for: the appointment chain. Booking appends a node at the tail in O(1) with a tail pointer.', '<button class="btn sm" data-act="d" data-d="ll">Traverse list</button>', 'll')}
${dcard('4. Queue and priority queue', 'Used for: the waiting list. Normal requests leave a FIFO queue; Urgent and Emergency leave a binary min-heap.', '<button class="btn sm" data-act="d" data-d="queue">Show queues</button> <button class="btn sm ghost" data-act="go" data-to="scheduler">Open scheduler</button>', 'queue')}
${dcard('5. Searching', 'Used for: patient search (linear scan) and ID lookup. Binary search works on a sorted ID array.', `<div class="row"><input id="sid" value="${S.appointments.at(-1)?.id || 'APT-1001'}"><button class="btn sm" data-act="d" data-d="search">Compare searches</button></div>`, 'search')}
${dcard('6. Sorting', 'Used for: the Appointments page. Compare merge, quick and insertion sort on your real appointments.', `<div class="row"><select id="sk">${opts([['date', 'Date & time'], ['prio', 'Priority'], ['pat', 'Patient'], ['doc', 'Doctor']])}</select><button class="btn sm" data-act="d" data-d="sort">Run sorts</button></div>`, 'sort')}
${dcard('7. Tree', 'Used for: hierarchy Hospital > Department > Specialization > Doctor, built from the doctor array.', '<button class="btn sm" data-act="d" data-d="dfs">DFS order</button> <button class="btn sm ghost" data-act="d" data-d="bfs">BFS order</button><ul class="tree" style="margin-top:10px">' + treeHtml(buildTree()) + '</ul>', 'tree')}
${dcard('8. Graph', 'Used for: patient - doctor - specialization - department relationships. BFS finds everything connected to a patient.', `<div class="row"><select id="gp">${patOpts()}</select><button class="btn sm" data-act="d" data-d="graph">Run BFS</button></div>`, 'graph')}
${dcard('9. Greedy algorithm', 'Used for: slot suggestions. Always pick the earliest free slot, preferring the least busy doctor on ties.', `<div class="row"><select id="gs2">${opts(SPECS.map(s => [s, s]))}</select><input type="date" id="gd" min="${E.today()}" value="${E.today()}"><button class="btn sm" data-act="d" data-d="greedy">Find slots</button></div>`, 'greedy')}</div>`;
const DEMO = {
  array: () => out('array', pre(`patients.length     = ${S.patients.length}\ndoctors.length      = ${S.doctors.length}\nappointments.length = ${S.appointments.length}\n\nappointments[0] = ${JSON.stringify(S.appointments[0], null, 1)}`)),
  hash: () => { const id = $('#hid').value.trim().toUpperCase(), i = E.P.hash(id), chain = E.P.b[i], hit = E.P.get(id);
    out('hash', pre(`hash("${id}") mod ${E.P.b.length} = bucket ${i}\nchain in bucket: [${chain.map(c => c[0]).join(', ') || 'empty'}]\ncomparisons: ${chain.length || 0}\nresult: ${hit ? hit.name + ' (age ' + hit.age + ')' : 'not found'}\n\nBucket load: ${E.P.b.map((b, k) => k + ':' + '#'.repeat(b.length)).join('  ')}\nSlot hash table keys stored: ${E.slots.size}`)); },
  ll: () => { const a = E.LL.toArray(); out('ll', flow(a.slice(0, 10).map(x => x.id)) + `<span class="arrow">&rarr;</span><span class="node">${a.length > 10 ? '... ' + (a.length - 10) + ' more' : 'null'}</span>` + pre(`nodes: ${E.LL.size}\nhead: ${a[0]?.id}   tail: ${a.at(-1)?.id}\nTraversal = O(n), append at tail = O(1)`)); },
  queue: () => out('queue', pre(`FIFO queue (front -> back):\n  ${E.FQ.toArray().map(w => pn(w.pid)).join(' -> ') || 'empty'}\n\nPriority queue - service order:\n  ${E.PQ.toArray().map(w => `${w.prio}:${pn(w.pid)}`).join(' -> ') || 'empty'}\nHeap array (internal): [${E.PQ.h.map(w => w.prio[0] + ':' + pn(w.pid).split(' ')[0]).join(', ')}]\n\nPush/pop = O(log n); enqueue/dequeue = O(1)`)),
  search: () => { const id = $('#sid').value.trim().toUpperCase(), arr = S.appointments.map(a => a.id), lin = linearSearch(arr, x => x === id), sorted = [...arr].sort(), bin = binarySearch(sorted, id);
    out('search', pre(`Linear search: ${lin.index >= 0 ? 'found at index ' + lin.index : 'not found'} after ${lin.comps} comparisons\nBinary search on sorted IDs: ${bin.index >= 0 ? 'found' : 'not found'} in ${bin.steps.length} steps\n${bin.steps.join('\n')}\nHash lookup: ${E.A.has(id) ? 'found' : 'not found'} in 1 bucket probe`)); },
  sort: () => { const c = CMP[$('#sk').value], A = S.appointments, rs = [['Merge sort O(n log n)', mergeSort], ['Quick sort O(n log n) avg', quickSort], ['Insertion sort O(n^2)', insertionSort]].map(([n, f]) => { const st = { c: 0 }, r = f(A, c, st); return [n, st.c, r]; });
    out('sort', pre(`n = ${A.length}\n${rs.map(r => `${r[0].padEnd(28)} ${r[1]} comparisons`).join('\n')}\n\nFirst 5 sorted: ${rs[0][2].slice(0, 5).map(a => a.id).join(', ')}`)); },
  dfs: () => out('tree', pre('DFS (depth first): ' + buildTree().dfs().join(' > '))), bfs: () => out('tree', pre('BFS (level by level): ' + buildTree().bfs().join(' > '))),
  graph: () => { const { g, L } = buildGraph(), s = 'P:' + $('#gp').value, m = g.bfs(s), lv = {}; m.forEach((d, n) => (lv[d] = lv[d] || []).push(L[n]));
    out('graph', pre(`BFS from ${L[s]}\n` + Object.keys(lv).map(d => `Level ${d}: ${lv[d].join(', ')}`).join('\n') + `\n\nLevel 1 = doctors booked, level 2 = specializations and other patients, level 3 = departments.`)); },
  greedy: () => { const sp = $('#gs2').value, d = $('#gd').value || E.today(), r = E.greedy(S.doctors.filter(x => x.spec === sp), d, '00:00', 5);
    out('greedy', pre(`Earliest free slots for ${sp} from ${d}:\n${r.map((s, i) => `${i + 1}. ${s.date} ${s.time}  ${s.doc.name}  (load that day: ${E.load(s.doc, s.date)})`).join('\n') || 'none'}\n\nGreedy choice: always take the earliest slot; break ties by least busy doctor.`)); } };

PAGES.info = () => { const sec = (t, h) => `<div class="card"><h3>${t}</h3>${h}</div>`, ul = a => '<ul>' + a.map(x => `<li>${x}</li>`).join('') + '</ul>';
  return `<div class="head"><div><h2>Project Information</h2><p>AI-Based Hospital Appointment Scheduling System - DSA II (CCSE0301), BTech CSE-DS</p></div></div>` +
  sec('Problem statement', '<p>Hospitals struggle to manage appointments because doctor availability, slots and patient urgency keep changing. Manual scheduling causes double bookings, long waits and poor use of doctors\' time.</p>') +
  sec('Objectives', ul(['Store and retrieve patient, doctor and appointment data efficiently.', 'Check doctor availability and prevent double booking.', 'Serve emergency and urgent patients first.', 'Suggest the nearest alternative slots when a slot is taken.', 'Demonstrate data structures and algorithms in a working system.'])) +
  sec('Proposed solution', '<p>A browser-based scheduler. Records live in arrays and hash tables, each booking passes a slot-conflict check, waiting requests go through a FIFO queue and a priority queue, and a greedy search suggests the earliest free slots. "AI-based" here means rule-based, priority-driven decision making - not machine learning.</p>') +
  sec('Data structures used', ul(['<b>Array</b> - records and tables', '<b>Hash table</b> - ID lookup, slot conflict table', '<b>Linked list</b> - appointment chain', '<b>Queue</b> - normal waiting requests', '<b>Priority queue (heap)</b> - urgent and emergency requests', '<b>Tree</b> - hospital hierarchy', '<b>Graph</b> - patient-doctor-department relations'])) +
  sec('Algorithms used', ul(['<b>Linear and binary search</b> - O(n), O(log n)', '<b>Merge, quick and insertion sort</b> - appointment ordering', '<b>Greedy earliest-slot selection</b> with least-busy tie-break', '<b>Priority preemption</b> - emergency moves a normal booking', '<b>DFS / BFS</b> - tree and graph traversal', '<b>Hashing</b> - djb2 with chaining'])) +
  sec('Advantages', ul(['No double bookings; O(1) conflict checks.', 'Urgent cases are served first, normal cases stay fair (FIFO).', 'Works offline; data persists in localStorage.', 'Every algorithm can be demonstrated on live data.'])) +
  sec('Future scope', ul(['Backend database and multi-user login.', 'SMS / email reminders.', 'Machine-learning prediction of no-shows and consultation length.', 'Bipartite matching and ageing to prevent starvation of normal requests.', 'Doctor leave management and multi-hospital support.'])); };

// ---------- router ----------
const NAV = [['home', '&#127968;', 'Home'], ['dashboard', '&#128202;', 'Dashboard'], ['patients', '&#129489;', 'Patients'], ['doctors', '&#129658;', 'Doctors'], ['book', '&#128197;', 'Book appointment'], ['scheduler', '&#9889;', 'Smart scheduler'], ['appointments', '&#128203;', 'Appointments'], ['dsa', '&#127891;', 'DSA lab'], ['info', '&#128214;', 'Project info']];
const AFTER = { patients: drawPatients, doctors: drawDoctors, appointments: drawAppts, book: () => fillDocs(UI.last?.did) };
const route = () => location.hash.replace('#/', '') || 'home';
function render(keep) { const r = PAGES[route()] ? route() : 'home'; const y = scrollY;
  $('#nav').innerHTML = NAV.map(n => `<a href="#/${n[0]}" class="${n[0] === r ? 'on' : ''}"><span>${n[1]}</span>${n[2]}</a>`).join('');
  $('#view').innerHTML = `<div class="${keep ? '' : 'view-in'}">${PAGES[r]()}</div>`; AFTER[r]?.(); $('#side').classList.remove('open'); scrollTo(0, keep ? y : 0); }
const refresh = () => render(true);
const go = to => { if (route() === to) refresh(); else location.hash = '#/' + to; };
window.addEventListener('hashchange', () => render());

// ---------- notifications and global search ----------
const unread = () => { const i = S.notes.findIndex(n => n.at + n.msg === S.seen); return i < 0 ? S.notes.length : i; };
function updBell() { const n = unread(), b = $('#bellN'); b.textContent = n; b.style.display = n ? '' : 'none'; }
function gsearch(q) { q = q.trim(); const box = $('#gres'); if (!q) { box.hidden = true; return; } const ql = q.toLowerCase(), r = [], U = q.toUpperCase();
  const ph = E.P.get(U), dh = E.D.get(U), ah = E.A.get(U);
  if (ph) r.push(['patients', ph.id, 'Patient: ' + ph.name]); if (dh) r.push(['doctors', dh.id, 'Doctor: ' + dh.name]); if (ah) r.push(['appointments', ah.id, `Appointment ${ah.id}: ${pn(ah.pid)}`]);
  S.patients.filter(p => p.name.toLowerCase().includes(ql) && p !== ph).slice(0, 3).forEach(p => r.push(['patients', p.name, 'Patient: ' + p.name + ' (' + p.id + ')']));
  S.doctors.filter(d => (d.name + d.spec).toLowerCase().includes(ql) && d !== dh).slice(0, 3).forEach(d => r.push(['doctors', d.name, 'Doctor: ' + d.name + ' - ' + d.spec]));
  S.appointments.filter(a => a !== ah && pn(a.pid).toLowerCase().includes(ql)).slice(0, 3).forEach(a => r.push(['appointments', a.id, `Appointment ${a.id}: ${pn(a.pid)}, ${a.date}`]));
  box.innerHTML = r.length ? r.map(x => `<div data-act="gopage" data-to="${x[0]}" data-q="${esc(x[1])}">${esc(x[2])}</div>`).join('') : '<div>No results found</div>'; box.hidden = false; }

// ---------- actions ----------
const ACT = {
  go: d => go(d.to), menu: () => $('#side').classList.toggle('open'), closeModal,
  gopage: d => { $('#gres').hidden = true; $('#gs').value = ''; if (d.to === 'patients') UI.ps = d.q; if (d.to === 'doctors') UI.ds = d.q; if (d.to === 'appointments') UI.af.q = d.q; go(d.to); },
  bell: () => { const p = $('#notes'); p.hidden = !p.hidden; if (!p.hidden) { p.innerHTML = S.notes.length ? S.notes.slice(0, 12).map(n => `<p>${esc(n.msg)}<small>${n.at}</small></p>`).join('') : '<p>No notifications</p>'; S.seen = S.notes[0] ? S.notes[0].at + S.notes[0].msg : ''; save(); } },
  addPatient: () => form('patient', 'Add patient', patFields),
  editPatient: d => form('patient', 'Edit patient ' + d.id, [{ n: 'id', l: '', t: 'hidden' }, ...patFields], E.P.get(d.id)),
  delPatient: d => { const n = S.appointments.filter(a => a.pid === d.id && a.status === 'Pending').length; if (!confirm(`Delete ${pn(d.id)}?` + (n ? ` ${n} pending appointment(s) will be cancelled.` : ''))) return;
    S.appointments.filter(a => a.pid === d.id && a.status === 'Pending').forEach(a => E.setStatus(a.id, 'Cancelled')); S.waiting = S.waiting.filter(w => w.pid !== d.id); S.patients = S.patients.filter(p => p.id !== d.id); E.index(); save(); toast('Patient deleted'); refresh(); },
  addDoctor: () => form('doctor', 'Add doctor', docFields, { days: [1, 2, 3, 4, 5], start: '09:00', end: '16:00' }),
  editDoctor: d => form('doctor', 'Edit doctor / availability', [{ n: 'id', l: '', t: 'hidden' }, ...docFields], E.D.get(d.id)),
  delDoctor: d => { if (S.appointments.some(a => a.did === d.id && a.status === 'Pending')) return toast('Cannot delete: this doctor has pending appointments. Cancel or reschedule them first.');
    if (!confirm('Delete ' + dn(d.id) + '?')) return; S.doctors = S.doctors.filter(x => x.id !== d.id); E.index(); save(); toast('Doctor deleted'); refresh(); },
  sched: d => { const doc = E.D.get(d.id), t = E.today(); openModal(doc.name + ' - next 7 days', [...Array(7)].map((_, i) => { const day = addDays(t, i);
    return `<p><b>${DAYS[new Date(day + 'T00:00').getDay()]} ${fmt(day)}</b><br>` + (works(doc, day) ? slotTimes(doc).map(s => { const id = E.slots.get(`${doc.id}|${day}|${s}`); return `<span class="chip ${id ? 'off' : ''}" title="${id ? 'Booked: ' + id : 'Free'}">${s}${id ? ' x' : ''}</span>`; }).join('') : '<span class="k">Not working</span>') + '</p>'; }).join('') + '<p class="k">Grey slots with x are booked.</p>'); },
  done: d => { E.setStatus(d.id, 'Completed'); save(); refresh(); toast('Marked completed'); },
  cancel: d => { if (!confirm('Cancel ' + d.id + '? The slot becomes free.')) return; E.setStatus(d.id, 'Cancelled'); save(); refresh(); toast('Appointment cancelled'); },
  resch: d => { const a = E.A.get(d.id); form('resch', 'Reschedule ' + a.id, [{ n: 'id', l: '', t: 'hidden' }, { n: 'date', l: 'New date', t: 'date', min: E.today() }, { n: 'time', l: 'New time', t: 'time', step: 1800 }], a, 'Reschedule'); },
  reschAlt: d => { const id = $('#mb input[name=id]').value, r = E.reschedule(id, d.date, d.time); if (r.ok) { save(); closeModal(); refresh(); toast('Rescheduled'); } else toast(r.error); },
  clearF: () => { UI.af = { q: '', date: '', doc: '', pat: '', prio: '', status: '' }; refresh(); },
  check: () => { const f = bv(), el = $('#bres'); if (!f.date) return void (el.innerHTML = '<div class="msg err">Choose a date first.</div>');
    const docs = f.did ? [E.D.get(f.did)] : S.doctors.filter(d => d.spec === f.spec);
    el.innerHTML = docs.map(d => { if (!works(d, f.date)) return `<p><b>${esc(d.name)}</b>: not working on ${fmt(f.date)}.</p>`; const fr = slotTimes(d).filter(t => E.isFree(d, f.date, t));
      return `<p><b>${esc(d.name)}</b> (${d.start}-${d.end}): ${fr.length ? '<div class="alts">' + fr.map(t => `<button class="btn sm" data-act="pickTime" data-doc="${d.id}" data-time="${t}">${t}</button>`).join('') + '</div>' : 'no free slots on this date.'}</p>`; }).join('') + '<div class="msg info">Click a time to select it.</div>'; },
  pickTime: d => { $('#btime').value = d.time; $('#bd').value = d.doc; toast('Selected ' + d.time); },
  doBook: () => { const f = bv(); showBook(E.book(f), f); },
  bookAlt: d => { const f = { ...bv(), did: d.doc, date: d.date, time: d.time }; $('#bd').value = d.doc; $('#bdate').value = d.date; $('#btime').value = d.time; showBook(E.book(f), f); },
  toWait: () => { const f = bv(); if (!f.pid) return toast('Select a patient first'); E.addWaiting(f.pid, f.spec, f.prio); E.note(`${pn(f.pid)} added to the ${f.prio === 'Normal' ? 'FIFO' : 'priority'} queue for ${f.spec}.`); save(); toast('Added to waiting list - see Smart scheduler'); },
  addWait: () => { const pid = $('#wp').value; if (!pid) return toast('Register a patient first'); const p = $('#wpr').value; E.addWaiting(pid, $('#ws').value, p); E.note(`${pn(pid)} added to the ${p === 'Normal' ? 'FIFO' : 'priority'} queue.`); save(); refresh(); toast('Added to queue'); },
  rmWait: d => { S.waiting = S.waiting.filter(w => w.id !== d.id); E.index(); save(); refresh(); },
  process: () => { if (!E.PQ.size && !E.FQ.size) return toast('The waiting list is empty'); const log = E.processWaiting(); save(); refresh(); $('#wlog').textContent = log.join('\n'); toast('Queue processed'); },
  d: d => DEMO[d.d]() };
FORMS.resch = v => { if (!v.date || !v.time) return 'Choose a new date and time.'; const r = E.reschedule(v.id, v.date, v.time);
  if (!r.ok) return { err: r.error, html: r.alts ? altBtns(r.alts, 'reschAlt') : '' }; save(); toast('Appointment rescheduled'); refresh(); };

const IN = { ps: e => { UI.ps = e.value; drawPatients(); }, ds: e => { UI.ds = e.value; drawDoctors(); }, dspec: e => { UI.dspec = e.value; drawDoctors(); },
  af: e => { UI.af[e.dataset.k] = e.value; drawAppts(); }, sort: e => { UI.sort = e.value; drawAppts(); }, alg: e => { UI.alg = e.value; drawAppts(); }, bspec: () => fillDocs() };
document.addEventListener('click', e => { const a = e.target.closest('[data-act]'); if (a) ACT[a.dataset.act]?.(a.dataset, a);
  if (!e.target.closest('.gsearch')) $('#gres').hidden = true; if (!e.target.closest('#notes,[data-act=bell]')) $('#notes').hidden = true; if (e.target.id === 'modal') closeModal(); });
document.addEventListener('input', e => { const n = e.target.dataset.in; if (n) IN[n](e.target); if (e.target.id === 'gs') gsearch(e.target.value); });
document.addEventListener('keydown', e => { if (e.key === 'Escape') closeModal(); });
if (S.seen === undefined) S.seen = '';
updBell(); render(); save();
})();
