#!/usr/bin/env node
/*
 * GAME 24 MULTIPLAYER
 * Satu file, tanpa dependensi. Jalankan:  node game24.js
 * Buka http://localhost:3000  (PORT bisa diatur lewat environment variable PORT)
 */
'use strict';
const http = require('http');
const os = require('os');
const crypto = require('crypto');

// ---------------------------------------------------------------
// Konfigurasi
// ---------------------------------------------------------------
const MAX_PLAYERS = 4;
const COUNTDOWN_MS = 3000;
const REVEAL_MS = 6000;
const PENALTY_WRONG_MS = 4000;   // salah hitung / angka tidak pas
const PENALTY_SYNTAX_MS = 1500;  // format ekspresi salah
const COLORS = ['#ef4444', '#3b82f6', '#22c55e', '#f59e0b'];
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
const MAX_ROOMS = 300;

// ---------------------------------------------------------------
// Parser ekspresi (fungsi ini juga dikirim ke browser untuk pratinjau).
// Harus berdiri sendiri: tidak boleh memakai variabel di luar fungsi.
// Hasil: {err} atau {v:[pembilang,penyebut], used:[angka terpakai, terurut]}
// ---------------------------------------------------------------
function parseExpr(src) {
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function fr(n, d) { if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return [n / g, d / g]; }
  var s = String(src).replace(/\s+/g, '')
    .replace(/[×xX]/g, '*').replace(/÷/g, '/').replace(/[−–—]/g, '-');
  if (!s || s.length > 60) return { err: 'syntax' };
  if (!/^[0-9+\-*\/()]+$/.test(s)) return { err: 'syntax' };
  var tk = s.match(/\d+|[+\-*\/()]/g) || [];
  var used = [], divzero = false, pos = 0, depth = 0;
  for (var i = 0; i < tk.length; i++) {
    if (/^\d/.test(tk[i])) {
      if (tk[i].length > 3 || /^0\d/.test(tk[i])) return { err: 'syntax' };
      used.push(+tk[i]);
    }
  }
  if (used.length > 4) return { err: 'count' };
  function factor() {
    var t = tk[pos];
    if (t === undefined) return null;
    if (/^\d/.test(t)) { pos++; return [+t, 1]; }
    if (t === '(') {
      if (++depth > 8) return null;
      pos++;
      var v = expr();
      if (v === null || tk[pos] !== ')') return null;
      pos++; depth--;
      return v;
    }
    return null;
  }
  function term() {
    var l = factor();
    if (l === null) return null;
    while (tk[pos] === '*' || tk[pos] === '/') {
      var op = tk[pos++], r = factor();
      if (r === null) return null;
      if (op === '*') l = fr(l[0] * r[0], l[1] * r[1]);
      else { if (r[0] === 0) { divzero = true; return null; } l = fr(l[0] * r[1], l[1] * r[0]); }
    }
    return l;
  }
  function expr() {
    var l = term();
    if (l === null) return null;
    while (tk[pos] === '+' || tk[pos] === '-') {
      var op = tk[pos++], r = term();
      if (r === null) return null;
      l = op === '+' ? fr(l[0] * r[1] + r[0] * l[1], l[1] * r[1]) : fr(l[0] * r[1] - r[0] * l[1], l[1] * r[1]);
    }
    return l;
  }
  var v = expr();
  if (divzero) return { err: 'div0' };
  if (v === null || pos !== tk.length) return { err: 'syntax' };
  return { v: v, used: used.slice().sort(function (a, b) { return a - b; }) };
}

// ---------------------------------------------------------------
// Pembuat soal: hanya angka yang DIJAMIN bisa menjadi 24
// ---------------------------------------------------------------
function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }
function frac(n, d) { if (d < 0) { n = -n; d = -d; } const g = gcd(n, d) || 1; return [n / g, d / g]; }

function solve24(nums) {
  function rec(items) {
    if (items.length === 1) return items[0].v[0] === 24 * items[0].v[1] ? items[0].e : null;
    for (let i = 0; i < items.length; i++) {
      for (let j = i + 1; j < items.length; j++) {
        const a = items[i], b = items[j];
        const rest = items.filter((_, k) => k !== i && k !== j);
        const c = [
          { v: frac(a.v[0] * b.v[1] + b.v[0] * a.v[1], a.v[1] * b.v[1]), e: '(' + a.e + '+' + b.e + ')' },
          { v: frac(a.v[0] * b.v[0], a.v[1] * b.v[1]), e: '(' + a.e + '×' + b.e + ')' },
          { v: frac(a.v[0] * b.v[1] - b.v[0] * a.v[1], a.v[1] * b.v[1]), e: '(' + a.e + '−' + b.e + ')' },
          { v: frac(b.v[0] * a.v[1] - a.v[0] * b.v[1], a.v[1] * b.v[1]), e: '(' + b.e + '−' + a.e + ')' },
        ];
        if (b.v[0] !== 0) c.push({ v: frac(a.v[0] * b.v[1], a.v[1] * b.v[0]), e: '(' + a.e + '÷' + b.e + ')' });
        if (a.v[0] !== 0) c.push({ v: frac(b.v[0] * a.v[1], b.v[1] * a.v[0]), e: '(' + b.e + '÷' + a.e + ')' });
        for (const x of c) {
          const r = rec(rest.concat([x]));
          if (r) return r;
        }
      }
    }
    return null;
  }
  const out = rec(nums.map((n) => ({ v: [n, 1], e: String(n) })));
  return out ? out.slice(1, -1) : null;
}

function makePuzzle(usedKeys) {
  for (let tries = 0; tries < 500; tries++) {
    const nums = [0, 0, 0, 0].map(() => 1 + Math.floor(Math.random() * 10));
    const key = nums.slice().sort((a, b) => a - b).join(',');
    if (usedKeys && usedKeys.has(key)) continue;
    const solution = solve24(nums);
    if (solution) { if (usedKeys) usedKeys.add(key); return { numbers: nums, solution }; }
  }
  return { numbers: [3, 3, 8, 8], solution: '8÷(3−8÷3)' };
}

// ---------------------------------------------------------------
// Ruangan & logika permainan
// ---------------------------------------------------------------
const rooms = new Map();
const now = () => Date.now();

function newCode() {
  for (;;) {
    let c = '';
    for (let i = 0; i < 4; i++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
}
function cleanName(n) {
  n = String(n || '').replace(/[\u0000-\u001f\u007f<>&"']/g, '').trim().slice(0, 12);
  return n || 'Pemain';
}
function uniqueName(room, name) {
  const taken = new Set([...room.players.values()].map((p) => p.name.toLowerCase()));
  if (!taken.has(name.toLowerCase())) return name;
  for (let i = 2; i < 10; i++) {
    const cand = (name.slice(0, 10) + ' ' + i);
    if (!taken.has(cand.toLowerCase())) return cand;
  }
  return name.slice(0, 8) + ' ' + crypto.randomInt(10, 99);
}

function addPlayer(room, name) {
  const usedColors = new Set([...room.players.values()].map((p) => p.color));
  const color = COLORS.find((c) => !usedColors.has(c)) || COLORS[0];
  const p = {
    id: crypto.randomBytes(4).toString('hex'),
    token: crypto.randomBytes(12).toString('hex'),
    name: uniqueName(room, name), color, score: 0,
    connected: false, res: null, lastSeen: now(),
    lockedUntil: 0, gaveUp: false,
  };
  room.players.set(p.id, p);
  if (!room.hostId) room.hostId = p.id;
  return p;
}

function createRoom() {
  const room = {
    code: newCode(), players: new Map(), hostId: null,
    phase: 'lobby', target: 5, roundSec: 90, roundNo: 0,
    puzzle: null, startAt: 0, endsAt: 0, reveal: null,
    usedKeys: new Set(), timer: null, lastActive: now(),
  };
  rooms.set(room.code, room);
  return room;
}

function setTimer(room, ms, fn) {
  clearTimeout(room.timer);
  room.timer = setTimeout(fn, ms);
}

function publicState(room) {
  const showNums = room.phase === 'playing' || room.phase === 'reveal' || room.phase === 'finished';
  return {
    type: 'state', now: now(), code: room.code, phase: room.phase, hostId: room.hostId,
    target: room.target, roundSec: room.roundSec, roundNo: room.roundNo,
    numbers: showNums && room.puzzle ? room.puzzle.numbers : null,
    startAt: room.startAt, endsAt: room.endsAt, nextAt: room.nextAt || 0, reveal: room.reveal,
    players: [...room.players.values()].map((p) => ({
      id: p.id, name: p.name, color: p.color, score: p.score,
      connected: p.connected, lockedUntil: p.lockedUntil, gaveUp: p.gaveUp,
    })),
  };
}

function send(p, obj) {
  if (p.res && !p.res.writableEnded) {
    try { p.res.write('data: ' + JSON.stringify(obj) + '\n\n'); } catch (e) { /* diabaikan */ }
  }
}
function broadcast(room) {
  room.lastActive = now();
  const st = publicState(room);
  for (const p of room.players.values()) send(p, st);
}

function startGame(room) {
  for (const p of room.players.values()) { p.score = 0; }
  room.roundNo = 0;
  room.usedKeys = new Set();
  nextRound(room);
}

function nextRound(room) {
  room.roundNo++;
  for (const p of room.players.values()) { p.gaveUp = false; p.lockedUntil = 0; }
  room.puzzle = makePuzzle(room.usedKeys);
  room.phase = 'countdown';
  room.reveal = null;
  room.startAt = now() + COUNTDOWN_MS;
  room.endsAt = room.startAt + room.roundSec * 1000;
  broadcast(room);
  setTimer(room, COUNTDOWN_MS, () => {
    room.phase = 'playing';
    broadcast(room);
    setTimer(room, room.roundSec * 1000, () => endRound(room, null, null, 0));
  });
}

function endRound(room, winner, expr, ms) {
  if (room.phase !== 'playing') return;
  let finished = false;
  if (winner) { winner.score++; finished = winner.score >= room.target; }
  room.phase = finished ? 'finished' : 'reveal';
  room.reveal = {
    winnerId: winner ? winner.id : null, expr: expr || null, ms: ms || 0,
    solution: room.puzzle.solution,
  };
  room.nextAt = finished ? 0 : now() + REVEAL_MS;
  broadcast(room);
  if (!finished) setTimer(room, REVEAL_MS, () => nextRound(room));
  else clearTimeout(room.timer);
}

function checkAllGaveUp(room) {
  if (room.phase !== 'playing') return;
  const active = [...room.players.values()].filter((p) => p.connected);
  if (active.length && active.every((p) => p.gaveUp)) endRound(room, null, null, 0);
}

function handleSubmit(room, p, expr) {
  const t = now();
  if (room.phase !== 'playing' || t < room.startAt) return;
  if (p.lockedUntil > t) { send(p, { type: 'fb', ok: false, msg: 'Kamu masih terkunci sebentar.' }); return; }
  const r = parseExpr(expr);
  const wrong = (msg, pen) => {
    p.lockedUntil = t + pen;
    send(p, { type: 'fb', ok: false, msg });
    broadcast(room);
  };
  if (r.err) return wrong(r.err === 'div0' ? 'Tidak boleh membagi dengan 0.' : 'Ekspresi belum lengkap atau salah format.', PENALTY_SYNTAX_MS);
  const want = room.puzzle.numbers.slice().sort((a, b) => a - b).join(',');
  if (r.used.join(',') !== want) return wrong('Pakai keempat angka, masing-masing tepat satu kali.', PENALTY_SYNTAX_MS);
  if (r.v[0] !== 24 * r.v[1]) {
    const val = r.v[1] === 1 ? String(r.v[0]) : r.v[0] + '/' + r.v[1];
    return wrong('Hasilnya ' + val + ', bukan 24.', PENALTY_WRONG_MS);
  }
  const shown = String(expr).replace(/\s+/g, '').replace(/\*/g, '×').replace(/\//g, '÷').replace(/-/g, '−').slice(0, 60);
  endRound(room, p, shown, t - room.startAt);
}

function removePlayer(room, p) {
  room.players.delete(p.id);
  if (p.res) { try { p.res.end(); } catch (e) { /* */ } }
  if (room.hostId === p.id) {
    const next = [...room.players.values()].find((x) => x.connected) || [...room.players.values()][0];
    room.hostId = next ? next.id : null;
  }
  if (!room.players.size) { clearTimeout(room.timer); rooms.delete(room.code); return; }
  broadcast(room);
  checkAllGaveUp(room);
}

function handleAction(room, p, body) {
  const isHost = room.hostId === p.id;
  switch (body.type) {
    case 'settings':
      if (isHost && (room.phase === 'lobby' || room.phase === 'finished')) {
        if ([3, 5, 7, 10].includes(+body.target)) room.target = +body.target;
        if ([60, 90, 120, 180].includes(+body.roundSec)) room.roundSec = +body.roundSec;
        broadcast(room);
      }
      break;
    case 'start':
      if (isHost && (room.phase === 'lobby' || room.phase === 'finished')) startGame(room);
      break;
    case 'submit':
      handleSubmit(room, p, String(body.expr || '').slice(0, 80));
      break;
    case 'giveup':
      if (room.phase === 'playing' && !p.gaveUp) { p.gaveUp = true; broadcast(room); checkAllGaveUp(room); }
      break;
    case 'leave':
      removePlayer(room, p);
      break;
    default:
  }
}

// ---------------------------------------------------------------
// Server HTTP (halaman + SSE + API JSON)
// ---------------------------------------------------------------
const HTML_TEMPLATE = "<!DOCTYPE html>\n<html lang=\"id\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,viewport-fit=cover\">\n<meta name=\"theme-color\" content=\"#0b1120\">\n<title>Game 24 ⚡ Adu Cepat</title>\n<style>\n:root{--bg:#0b1120;--card:#162033;--card2:#1e2b44;--txt:#e8eefc;--mut:#8ea0c4;--acc:#38bdf8;--ok:#22c55e;--bad:#ef4444;--gold:#fbbf24}\n*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}\nhtml,body{margin:0;background:var(--bg);color:var(--txt);font-family:system-ui,-apple-system,\"Segoe UI\",Roboto,sans-serif}\nbody{min-height:100dvh;display:flex;justify-content:center}\n#app{width:100%;max-width:520px;padding:14px 14px calc(18px + env(safe-area-inset-bottom))}\n.screen{display:none}.screen.on{display:block}\nh1{font-size:64px;line-height:1;margin:18px 0 4px;text-align:center;font-weight:900;letter-spacing:-2px}\nh1 span{color:var(--gold)}\n.sub{text-align:center;color:var(--mut);margin:0 0 22px}\nlabel{display:block;color:var(--mut);font-size:13px;margin:12px 0 6px}\ninput,select{width:100%;padding:14px;border-radius:12px;border:2px solid #2a3a5c;background:#0f1a30;color:var(--txt);font-size:17px;outline:none}\ninput:focus,select:focus{border-color:var(--acc)}\n#inCode{text-transform:uppercase;letter-spacing:6px;text-align:center;font-weight:800}\nbutton{font:inherit;cursor:pointer;border:0;border-radius:12px;touch-action:manipulation;user-select:none;-webkit-user-select:none;color:var(--txt)}\n.btn{padding:15px 18px;font-weight:800;font-size:17px;background:var(--acc);color:#04202e;width:100%}\n.btn.sec{background:var(--card2);color:var(--txt)}\n.btn.warn{background:transparent;color:var(--mut);font-weight:600;font-size:14px;padding:10px}\n.btn:disabled{opacity:.4}\n.btn:active:not(:disabled){transform:scale(.98)}\n.row{display:flex;gap:10px;align-items:stretch}.row .btn{width:auto}\n.or{text-align:center;color:var(--mut);margin:20px 0 4px;font-size:14px}\ndetails{margin-top:22px;background:var(--card);border-radius:12px;padding:12px 16px;color:var(--mut)}\ndetails summary{cursor:pointer;color:var(--txt);font-weight:700}\ndetails ul{padding-left:18px;margin:10px 0 2px;line-height:1.55}\n#lobCode{font-size:60px;font-weight:900;letter-spacing:10px;text-align:center;margin:6px 0 0;color:var(--gold)}\n.hint{text-align:center;color:var(--mut);font-size:14px;margin:0 0 12px}\n#lobLink{word-break:break-all;text-align:center;font-size:13px;color:var(--acc);margin:6px 0 12px}\n.slots{display:grid;gap:8px;margin:14px 0}\n.slot{display:flex;align-items:center;gap:10px;background:var(--card);border-radius:12px;padding:12px 14px;border-left:6px solid var(--c,#334155);font-weight:700}\n.slot.empty{color:var(--mut);font-weight:500;border-left-color:#334155;border-style:dashed}\n.slot.off{opacity:.5}\n.slot small{margin-left:auto;color:var(--mut);font-weight:500}\n.set{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:14px}\n#board{display:grid;grid-template-columns:repeat(auto-fit,minmax(72px,1fr));gap:8px;margin-bottom:10px}\n.chip{background:var(--card);border-radius:12px;padding:8px 6px;text-align:center;border-top:5px solid var(--c);position:relative;min-height:74px}\n.chip.me{outline:2px solid var(--acc)}\n.chip.off{opacity:.45}\n.chip .cn{font-size:12px;font-weight:700;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}\n.chip .cs{font-size:30px;font-weight:900;line-height:1.1}\n.chip .ci{font-size:12px;height:14px}\n#info{display:flex;justify-content:space-between;color:var(--mut);font-size:13px;margin:2px 2px 6px}\n#timeLeft{font-variant-numeric:tabular-nums;color:var(--txt);font-weight:700}\n#bar{height:10px;background:var(--card2);border-radius:6px;overflow:hidden;margin-bottom:12px}\n#bar i{display:block;height:100%;width:100%;background:var(--acc);transition:width .12s linear}\n#bar.low i{background:var(--bad)}\n#play{position:relative}\n#cards{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}\n.card{aspect-ratio:1/1.1;font-size:clamp(34px,11vw,54px);font-weight:900;background:linear-gradient(160deg,#2563eb,#1d4ed8);border-radius:16px;box-shadow:0 4px 0 #1e3a8a}\n.card:active:not(:disabled){transform:translateY(3px);box-shadow:0 1px 0 #1e3a8a}\n.card.used{opacity:.25;box-shadow:none}\n.card:disabled:not(.used){background:var(--card2);box-shadow:none;color:var(--mut)}\n#exprBox{margin:12px 0 8px;background:#0f1a30;border:2px solid #2a3a5c;border-radius:14px;min-height:64px;padding:10px 14px;display:flex;align-items:center;justify-content:center;text-align:center;font-size:clamp(24px,7vw,32px);font-weight:800;position:relative;word-break:break-all}\n#exprBox.ph{font-size:15px;font-weight:500;color:var(--mut)}\n#exprBox.shake{animation:shake .35s;border-color:var(--bad)}\n@keyframes shake{20%{transform:translateX(-8px)}40%{transform:translateX(8px)}60%{transform:translateX(-6px)}80%{transform:translateX(6px)}}\n#lockMsg{position:absolute;inset:0;border-radius:12px;background:rgba(127,29,29,.92);display:none;align-items:center;justify-content:center;font-size:20px;font-weight:800}\n#pad{display:grid;grid-template-columns:repeat(6,1fr);gap:8px}\n#pad button{padding:15px 0;font-size:26px;font-weight:800;background:var(--card2)}\n#pad button.op{background:#334155}\n#pad .w2{grid-column:span 2}#pad .w3{grid-column:span 3}\n#pad #btnSend{background:var(--ok);color:#052e14;font-size:20px}\n#pad #btnSend:disabled{background:var(--card2);color:var(--mut)}\n#pad #btnClear,#pad #btnBack{font-size:20px}\n#btnGive{margin-top:6px}\n#ov{position:absolute;inset:-4px;display:none;background:#0b1120;border-radius:16px;align-items:center;justify-content:center;text-align:center;padding:14px;z-index:5}\n#ov.on{display:flex}\n#ovBig{font-size:130px;font-weight:900;line-height:1;color:var(--gold)}\n#ovLabel{color:var(--mut);margin-bottom:6px;font-size:18px}\n#ovTitle{font-size:24px;font-weight:900;margin:0 0 8px}\n#ovLine{font-size:20px;font-weight:700;color:var(--ok);margin-bottom:8px;word-break:break-all}\n#ovSol{color:var(--mut);font-size:15px;margin-bottom:10px;word-break:break-all}\n#ovNext{color:var(--acc);font-weight:700}\n#ovRank{display:grid;gap:6px;margin:10px 0 14px;text-align:left}\n#ovRank div{background:var(--card);border-radius:10px;padding:9px 12px;display:flex;gap:8px;font-weight:700}\n#ovRank div b{margin-left:auto}\n#ovBtns{display:grid;gap:8px}\n#toast{position:fixed;left:50%;bottom:calc(24px + env(safe-area-inset-bottom));transform:translate(-50%,30px);background:#0f172a;border:2px solid var(--acc);padding:12px 18px;border-radius:14px;font-weight:700;opacity:0;pointer-events:none;transition:.2s;max-width:90vw;text-align:center;z-index:20}\n#toast.on{opacity:1;transform:translate(-50%,0)}\n#toast.bad{border-color:var(--bad)}\n#conn{position:fixed;top:0;left:0;right:0;background:var(--bad);text-align:center;padding:6px;font-size:13px;font-weight:700;display:none;z-index:30}\n#conn.on{display:block}\n#mute{position:fixed;bottom:calc(10px + env(safe-area-inset-bottom));right:10px;background:var(--card);width:40px;height:40px;font-size:18px;z-index:10;border-radius:50%;opacity:.85}\n.boot{text-align:center;color:var(--mut);margin-top:30vh}\n</style>\n</head>\n<body>\n<div id=\"conn\">Menghubungkan ulang…</div>\n<button id=\"mute\" title=\"Suara\">🔊</button>\n<div id=\"app\">\n\n  <section id=\"boot\" class=\"screen\"><p class=\"boot\">Menghubungkan…</p></section>\n\n  <section id=\"home\" class=\"screen on\">\n    <h1>24<span>⚡</span></h1>\n    <p class=\"sub\">Adu cepat menghitung bareng teman!<br>Susun 4 angka sampai hasilnya <b>24</b>.</p>\n    <label for=\"inName\">Nama kamu</label>\n    <input id=\"inName\" maxlength=\"12\" placeholder=\"mis. Agus\" autocomplete=\"off\">\n    <div style=\"height:14px\"></div>\n    <button id=\"btnCreate\" class=\"btn\">Buat Ruangan Baru</button>\n    <div class=\"or\">atau gabung ke ruangan teman</div>\n    <div class=\"row\">\n      <input id=\"inCode\" maxlength=\"4\" placeholder=\"KODE\" autocomplete=\"off\" autocapitalize=\"characters\">\n      <button id=\"btnJoin\" class=\"btn sec\">Gabung</button>\n    </div>\n    <details>\n      <summary>Cara main</summary>\n      <ul>\n        <li>Semua pemain melihat <b>4 angka yang sama</b> (1–10).</li>\n        <li>Susun dengan <b>+ − × ÷</b> dan kurung sampai hasilnya <b>24</b>. Pakai tiap angka <b>tepat sekali</b>.</li>\n        <li>Pemain <b>tercepat</b> yang menjawab benar dapat <b>1 poin</b>.</li>\n        <li>Jawaban salah = <b>terkunci beberapa detik</b>.</li>\n        <li>Semua buntu? Tekan <b>Menyerah</b>. Kalau semua menyerah, solusi ditampilkan.</li>\n        <li>Siapa duluan sampai target poin, dia juara 🏆</li>\n      </ul>\n    </details>\n  </section>\n\n  <section id=\"lobby\" class=\"screen\">\n    <p class=\"hint\" style=\"margin-top:20px\">Kode ruangan</p>\n    <div id=\"lobCode\">----</div>\n    <div id=\"lobLink\"></div>\n    <div class=\"row\">\n      <button id=\"btnCopy\" class=\"btn sec\">📋 Salin tautan</button>\n      <a id=\"btnWa\" class=\"btn sec\" style=\"text-decoration:none;text-align:center;border-radius:12px;display:block;width:auto\" target=\"_blank\" rel=\"noopener\">WhatsApp</a>\n    </div>\n    <div class=\"slots\" id=\"slots\"></div>\n    <div class=\"set\">\n      <div><label for=\"selTarget\">Target poin</label>\n        <select id=\"selTarget\"><option value=\"3\">3 poin</option><option value=\"5\">5 poin</option><option value=\"7\">7 poin</option><option value=\"10\">10 poin</option></select></div>\n      <div><label for=\"selTime\">Waktu per ronde</label>\n        <select id=\"selTime\"><option value=\"60\">60 detik</option><option value=\"90\">90 detik</option><option value=\"120\">2 menit</option><option value=\"180\">3 menit</option></select></div>\n    </div>\n    <button id=\"btnStart\" class=\"btn\">Mulai Game</button>\n    <p id=\"waitHost\" class=\"hint\" style=\"display:none\">Menunggu host memulai game…</p>\n    <button id=\"btnLeave1\" class=\"btn warn\">Keluar ruangan</button>\n  </section>\n\n  <section id=\"game\" class=\"screen\">\n    <div id=\"board\"></div>\n    <div id=\"info\"><span id=\"roundInfo\"></span><span id=\"timeLeft\"></span></div>\n    <div id=\"bar\"><i id=\"barI\"></i></div>\n    <div id=\"play\">\n      <div id=\"cards\"></div>\n      <div id=\"exprBox\" class=\"ph\"><span id=\"expr\"></span><div id=\"lockMsg\"></div></div>\n      <div id=\"pad\">\n        <button class=\"op\" data-k=\"+\">+</button><button class=\"op\" data-k=\"−\">−</button>\n        <button class=\"op\" data-k=\"×\">×</button><button class=\"op\" data-k=\"÷\">÷</button>\n        <button class=\"op\" data-k=\"(\">(</button><button class=\"op\" data-k=\")\">)</button>\n        <button id=\"btnBack\" class=\"w2\">⌫</button><button id=\"btnClear\">C</button>\n        <button id=\"btnSend\" class=\"w3\">Kirim ✔</button>\n      </div>\n      <button id=\"btnGive\" class=\"btn warn\">🏳️ Menyerah ronde ini</button>\n      <div id=\"ov\">\n        <div style=\"width:100%\">\n          <div id=\"ovCount\"><div id=\"ovLabel\"></div><div id=\"ovBig\">3</div><div style=\"color:var(--mut)\">Bersiap…</div></div>\n          <div id=\"ovRes\" style=\"display:none\">\n            <div id=\"ovTitle\"></div><div id=\"ovLine\"></div><div id=\"ovSol\"></div>\n            <div id=\"ovNext\"></div>\n            <div id=\"ovRank\"></div>\n            <div id=\"ovBtns\"></div>\n          </div>\n        </div>\n      </div>\n    </div>\n    <button id=\"btnLeave2\" class=\"btn warn\" style=\"margin-top:8px\">Keluar</button>\n  </section>\n\n</div>\n<div id=\"toast\"></div>\n\n<script>\n(function () {\n'use strict';\n/*__PARSER__*/\n\nvar $ = function (id) { return document.getElementById(id); };\nvar S = null, me = null, es = null, offset = 0, tokens = [], curKey = null, lastCount = null, muted = false, busyFlag = false;\n\nfunction sNow() { return Date.now() + offset; }\nfunction el(tag, cls, txt) { var e = document.createElement(tag); if (cls) e.className = cls; if (txt != null) e.textContent = txt; return e; }\nfunction store(k, v) { try { if (v == null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) {} }\nfunction load(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }\n/* sesi disimpan per tab (sessionStorage) supaya dua tab di satu browser tidak saling mengambil alih */\nfunction sstore(k, v) { try { if (v == null) sessionStorage.removeItem(k); else sessionStorage.setItem(k, v); } catch (e) {} }\nfunction sload(k) { try { return sessionStorage.getItem(k); } catch (e) { return null; } }\nfunction fmt(ms) { var s = Math.ceil(ms / 1000); return Math.floor(s / 60) + ':' + ('0' + (s % 60)).slice(-2); }\nfunction meP() { return S && me ? S.players.filter(function (p) { return p.id === me.id; })[0] : null; }\nfunction isHost() { return S && me && S.hostId === me.id; }\n\nfunction toast(msg, bad) {\n  var t = $('toast'); t.textContent = msg; t.className = 'on' + (bad ? ' bad' : '');\n  clearTimeout(toast._t); toast._t = setTimeout(function () { t.className = ''; }, 2400);\n}\n\n/* ---------- suara ---------- */\nvar AC = null;\nfunction ac() {\n  try { if (!AC) AC = new (window.AudioContext || window.webkitAudioContext)(); if (AC.state === 'suspended') AC.resume(); } catch (e) {}\n  return AC;\n}\nfunction beep(f, d, type, vol, delay) {\n  if (muted) return; var c = ac(); if (!c) return;\n  try {\n    var t = c.currentTime + (delay || 0), o = c.createOscillator(), g = c.createGain();\n    o.type = type || 'sine'; o.frequency.value = f;\n    g.gain.setValueAtTime(vol || 0.15, t); g.gain.exponentialRampToValueAtTime(0.0001, t + d);\n    o.connect(g); g.connect(c.destination); o.start(t); o.stop(t + d + 0.02);\n  } catch (e) {}\n}\nfunction sfx(n) {\n  if (n === 'tick') beep(520, 0.12);\n  else if (n === 'go') beep(880, 0.3, 'square', 0.1);\n  else if (n === 'bad') beep(160, 0.25, 'sawtooth', 0.12);\n  else if (n === 'win') [523, 659, 784, 1047].forEach(function (f, i) { beep(f, 0.22, 'triangle', 0.16, i * 0.1); });\n  else if (n === 'lose') { beep(330, 0.18, 'sine', 0.1); beep(262, 0.28, 'sine', 0.1, 0.15); }\n  else if (n === 'none') beep(300, 0.3, 'sine', 0.1);\n}\n$('mute').onclick = function () { muted = !muted; $('mute').textContent = muted ? '🔇' : '🔊'; ac(); };\n\n/* ---------- jaringan ---------- */\nfunction api(path, body) {\n  return fetch(path, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) })\n    .then(function (r) { return r.json().then(function (j) { return { ok: r.ok, j: j }; }); })\n    .catch(function () { return { ok: false, j: { error: 'Tidak bisa terhubung ke server.' } }; });\n}\nfunction act(type, extra) {\n  if (!me) return Promise.resolve();\n  return api('/api/action', Object.assign({ code: me.code, id: me.id, token: me.token, type: type }, extra || {}));\n}\nfunction show(name) {\n  ['boot', 'home', 'lobby', 'game'].forEach(function (n) { $(n).className = 'screen' + (n === name ? ' on' : ''); });\n}\nfunction leaveLocal(msg) {\n  if (es) { es.close(); es = null; }\n  me = null; S = null; tokens = []; curKey = null; sstore('g24', null);\n  $('conn').className = ''; show('home');\n  if (msg) toast(msg, true);\n}\nfunction connect() {\n  if (es) { es.close(); es = null; }\n  es = new EventSource('/api/events?code=' + encodeURIComponent(me.code) + '&id=' + me.id + '&token=' + me.token);\n  es.onopen = function () { $('conn').className = ''; };\n  es.onmessage = function (ev) {\n    var m; try { m = JSON.parse(ev.data); } catch (e) { return; }\n    if (m.type === 'state') onState(m); else if (m.type === 'fb') onFb(m);\n  };\n  es.onerror = function () {\n    if (unloading) return;\n    $('conn').className = 'on';\n    if (es && es.readyState === 2) recover();   /* browser menyerah menyambung: cek sesi lalu sambungkan lagi */\n  };\n}\nvar unloading = false;\nwindow.addEventListener('pagehide', function () { unloading = true; });\nwindow.addEventListener('beforeunload', function () { unloading = true; });\nwindow.addEventListener('pageshow', function (e) { if (e.persisted) { unloading = false; if (me) connect(); } });\nfunction recover() {\n  var cur = es;\n  setTimeout(function () {\n    if (!me || es !== cur) return;\n    fetch('/api/check?code=' + encodeURIComponent(me.code) + '&id=' + me.id + '&token=' + me.token, { cache: 'no-store' })\n      .then(function (r) {\n        if (!me || es !== cur) return;\n        if (r.status === 404) leaveLocal('Ruangan sudah tidak tersedia.'); else connect();\n      })\n      .catch(function () { if (me && es === cur) recover(); });\n  }, 1500);\n}\nfunction startSession(j) {\n  me = { code: j.code, id: j.id, token: j.token };\n  sstore('g24', JSON.stringify(me));\n  show('boot'); connect();\n}\n\n/* ---------- state dari server ---------- */\nfunction onState(m) {\n  var old = S;\n  offset = m.now - Date.now();\n  S = m;\n  if (!meP()) { leaveLocal('Kamu sudah keluar dari ruangan.'); return; }\n  if (old && old.phase !== m.phase) {\n    if (m.phase === 'reveal' || m.phase === 'finished') {\n      var r = m.reveal;\n      if (r && r.winnerId) sfx(r.winnerId === me.id ? 'win' : 'lose'); else sfx('none');\n    } else if (m.phase === 'playing') sfx('go');\n  }\n  var key = m.startAt + ':' + m.roundNo;\n  if (key !== curKey) { curKey = key; tokens = []; }\n  render();\n}\nfunction onFb(m) {\n  toast(m.msg, !m.ok); sfx('bad');\n  try { if (navigator.vibrate) navigator.vibrate(150); } catch (e) {}\n  var b = $('exprBox'); b.classList.remove('shake'); void b.offsetWidth; b.classList.add('shake');\n}\n\n/* ---------- tampilan ---------- */\nfunction render() {\n  if (!S) return;\n  if (S.phase === 'lobby') { show('lobby'); renderLobby(); }\n  else { show('game'); renderGame(); }\n}\n\nfunction renderLobby() {\n  var link = location.origin + '/?r=' + S.code;\n  $('lobCode').textContent = S.code;\n  $('lobLink').textContent = link;\n  $('btnWa').href = 'https://wa.me/?text=' + encodeURIComponent('Ayo main Game 24 bareng! Buka ' + link + ' (kode ruangan: ' + S.code + ')');\n  var slots = $('slots'); slots.textContent = '';\n  for (var i = 0; i < 4; i++) {\n    var p = S.players[i], d;\n    if (p) {\n      d = el('div', 'slot' + (p.connected ? '' : ' off'));\n      d.style.setProperty('--c', p.color);\n      d.appendChild(el('span', '', p.name + (p.id === S.hostId ? ' 👑' : '')));\n      if (p.id === me.id) d.appendChild(el('small', '', 'kamu'));\n      else if (!p.connected) d.appendChild(el('small', '', 'terputus'));\n    } else d = el('div', 'slot empty', 'Menunggu teman…');\n    slots.appendChild(d);\n  }\n  var host = isHost();\n  $('selTarget').value = String(S.target); $('selTime').value = String(S.roundSec);\n  $('selTarget').disabled = !host; $('selTime').disabled = !host;\n  $('btnStart').style.display = host ? 'block' : 'none';\n  $('waitHost').style.display = host ? 'none' : 'block';\n  $('btnStart').textContent = S.players.length === 1 ? 'Mulai Latihan (sendirian)' : 'Mulai Game (' + S.players.length + ' pemain)';\n}\n\nfunction renderBoard() {\n  var b = $('board'); b.textContent = '';\n  var t = sNow();\n  S.players.forEach(function (p) {\n    var c = el('div', 'chip' + (p.id === me.id ? ' me' : '') + (p.connected ? '' : ' off'));\n    c.style.setProperty('--c', p.color);\n    c.appendChild(el('div', 'cn', p.name + (p.id === S.hostId ? ' 👑' : '')));\n    c.appendChild(el('div', 'cs', String(p.score)));\n    c.appendChild(el('div', 'ci', p.lockedUntil > t ? '🔒' : (p.gaveUp ? '🏳️' : (p.connected ? '' : '💤'))));\n    b.appendChild(c);\n  });\n}\n\nfunction renderCards() {\n  var c = $('cards'); c.textContent = '';\n  for (var i = 0; i < 4; i++) {\n    var v = S.numbers ? S.numbers[i] : null;\n    var used = tokens.some(function (t) { return t.t === 'n' && t.i === i; });\n    var b = el('button', 'card' + (used ? ' used' : ''), v == null ? '?' : String(v));\n    b.dataset.i = i; b.disabled = v == null || used || S.phase !== 'playing';\n    c.appendChild(b);\n  }\n}\n$('cards').addEventListener('click', function (e) {\n  var b = e.target.closest ? e.target.closest('button.card') : null;\n  if (!b || b.disabled || !S || !S.numbers) return;\n  var i = +b.dataset.i; ac();\n  add({ t: 'n', i: i, v: S.numbers[i] });\n});\n\nfunction exprStr() { return tokens.map(function (t) { return t.v; }).join(''); }\nfunction lastTok() { return tokens[tokens.length - 1]; }\nfunction openCount() { var n = 0; tokens.forEach(function (t) { if (t.v === '(') n++; else if (t.v === ')') n--; }); return n; }\nfunction canAdd(t) {\n  var l = lastTok(), afterVal = l && (l.t === 'n' || l.v === ')');\n  if (t.t === 'n' || t.v === '(') return !afterVal;\n  if (t.v === ')') return !!afterVal && openCount() > 0;\n  return !!afterVal;\n}\nfunction add(t) {\n  if (!S || S.phase !== 'playing') return;\n  if (!canAdd(t)) { var b = $('exprBox'); b.classList.remove('shake'); void b.offsetWidth; b.classList.add('shake'); return; }\n  tokens.push(t); refresh();\n}\nfunction addOp(ch) { add({ t: (ch === '(' || ch === ')') ? 'p' : 'o', v: ch }); }\nfunction canSubmit() {\n  var usedN = tokens.filter(function (t) { return t.t === 'n'; }).length;\n  if (usedN !== 4 || openCount() !== 0) return false;\n  var r = parseExpr(exprStr());\n  return !r.err && !!r.v;\n}\nfunction submit() {\n  if (!S || S.phase !== 'playing' || !canSubmit()) return;\n  var p = meP(); if (p && p.lockedUntil > sNow()) return;\n  act('submit', { expr: exprStr() });\n}\nfunction refresh() { renderCards(); renderExpr(); }\n\nfunction renderExpr() {\n  var box = $('exprBox'), e = $('expr');\n  if (!tokens.length) { e.textContent = 'Ketuk angka lalu tanda hitung'; box.classList.add('ph'); }\n  else { e.textContent = tokens.map(function (t) { return t.v; }).join(' '); box.classList.remove('ph'); }\n  var p = meP(), locked = p && p.lockedUntil > sNow();\n  $('btnSend').disabled = S.phase !== 'playing' || locked || !canSubmit();\n  var g = $('btnGive');\n  g.disabled = S.phase !== 'playing' || (p && p.gaveUp);\n  g.textContent = p && p.gaveUp ? '🏳️ Kamu menyerah, menunggu pemain lain…' : '🏳️ Menyerah ronde ini';\n}\n\nfunction renderGame() {\n  renderBoard();\n  $('roundInfo').textContent = 'Ronde ' + S.roundNo + ' · Target ' + S.target + ' poin';\n  refresh();\n  renderOverlay();\n  tick();\n}\n\nfunction renderOverlay() {\n  var ov = $('ov'), ph = S.phase;\n  if (ph === 'playing') { ov.className = ''; return; }\n  ov.className = 'on';\n  $('ovCount').style.display = ph === 'countdown' ? 'block' : 'none';\n  $('ovRes').style.display = (ph === 'reveal' || ph === 'finished') ? 'block' : 'none';\n  if (ph === 'countdown') { lastCount = null; $('ovLabel').textContent = 'Ronde ' + S.roundNo; return; }\n  var r = S.reveal || {};\n  var w = S.players.filter(function (p) { return p.id === r.winnerId; })[0];\n  var fin = ph === 'finished';\n  var title;\n  if (fin) title = '🎉 ' + (w ? w.name : 'Seseorang') + (w && w.id === me.id ? ' (kamu!)' : '') + ' juara!';\n  else if (w) title = '🏆 ' + w.name + (w.id === me.id ? ' (kamu!)' : '') + ' tercepat!';\n  else title = 'Tidak ada yang berhasil';\n  $('ovTitle').textContent = title;\n  $('ovLine').textContent = w ? (r.expr + ' = 24  ·  ' + (r.ms / 1000).toFixed(1) + ' dtk') : '';\n  $('ovLine').style.display = w ? 'block' : 'none';\n  $('ovSol').textContent = 'Contoh solusi: ' + r.solution + ' = 24';\n  $('ovNext').style.display = fin ? 'none' : 'block';\n  var rank = $('ovRank'); rank.textContent = '';\n  var btns = $('ovBtns'); btns.textContent = '';\n  if (fin) {\n    var medals = ['🥇', '🥈', '🥉', '4️⃣'];\n    S.players.slice().sort(function (a, b) { return b.score - a.score; }).forEach(function (p, i) {\n      var d = el('div'); d.appendChild(el('span', '', (medals[i] || '') + ' ' + p.name)); d.appendChild(el('b', '', p.score + ' poin')); rank.appendChild(d);\n    });\n    if (isHost()) {\n      var again = el('button', 'btn', 'Main Lagi 🔄'); again.onclick = function () { act('start'); }; btns.appendChild(again);\n    } else btns.appendChild(el('div', 'hint', 'Menunggu host memulai ulang…'));\n    var out = el('button', 'btn warn', 'Keluar'); out.onclick = leave; btns.appendChild(out);\n  } else rank.textContent = '';\n}\n\nfunction tick() {\n  if (!S || !me || S.phase === 'lobby') return;\n  var t = sNow();\n  if (S.phase === 'countdown') {\n    var left = Math.ceil((S.startAt - t) / 1000), txt = left > 0 ? String(left) : 'GO!';\n    if (txt !== lastCount) { lastCount = txt; $('ovBig').textContent = txt; if (left > 0) sfx('tick'); }\n    $('barI').style.width = '100%'; $('bar').className = '';\n    $('timeLeft').textContent = fmt(S.roundSec * 1000);\n  } else if (S.phase === 'playing') {\n    var rem = Math.max(0, S.endsAt - t), tot = S.roundSec * 1000;\n    $('barI').style.width = (rem / tot * 100) + '%';\n    $('bar').className = rem < 10000 ? 'low' : '';\n    $('timeLeft').textContent = fmt(rem);\n    var p = meP(), lm = $('lockMsg');\n    if (p && p.lockedUntil > t) { lm.style.display = 'flex'; lm.textContent = '🔒 Terkunci ' + ((p.lockedUntil - t) / 1000).toFixed(1) + ' dtk'; }\n    else if (lm.style.display !== 'none') { lm.style.display = 'none'; renderExpr(); }\n  } else if (S.phase === 'reveal') {\n    $('ovNext').textContent = 'Ronde berikutnya dalam ' + Math.max(0, Math.ceil((S.nextAt - t) / 1000)) + ' dtk';\n    $('timeLeft').textContent = '';\n  } else $('timeLeft').textContent = '';\n  if (S.players.some(function (p) { return p.lockedUntil > t - 400; })) renderBoard();\n}\nsetInterval(tick, 100);\n\nfunction leave() {\n  if (!me) return;\n  act('leave'); leaveLocal();\n}\n\n/* ---------- tombol ---------- */\nfunction setBusy(b) { busyFlag = b; $('btnCreate').disabled = b; $('btnJoin').disabled = b; }\n$('btnCreate').onclick = function () {\n  ac();\n  var name = $('inName').value.trim();\n  if (!name) { toast('Isi nama dulu ya', true); $('inName').focus(); return; }\n  store('g24name', name); setBusy(true);\n  api('/api/create', { name: name }).then(function (r) {\n    setBusy(false);\n    if (!r.ok) { toast(r.j.error || 'Gagal membuat ruangan', true); return; }\n    startSession(r.j);\n  });\n};\n$('btnJoin').onclick = function () {\n  ac();\n  var name = $('inName').value.trim(), code = $('inCode').value.trim().toUpperCase();\n  if (!name) { toast('Isi nama dulu ya', true); $('inName').focus(); return; }\n  if (code.length !== 4) { toast('Kode ruangan terdiri dari 4 huruf', true); $('inCode').focus(); return; }\n  store('g24name', name); setBusy(true);\n  api('/api/join', { name: name, code: code }).then(function (r) {\n    setBusy(false);\n    if (!r.ok) { toast(r.j.error || 'Gagal bergabung', true); return; }\n    startSession(r.j);\n  });\n};\n$('inCode').addEventListener('input', function () { this.value = this.value.toUpperCase().replace(/[^A-Z]/g, ''); });\n$('inCode').addEventListener('keydown', function (e) { if (e.key === 'Enter') $('btnJoin').click(); });\n$('inName').addEventListener('keydown', function (e) { if (e.key === 'Enter') ($('inCode').value.length === 4 ? $('btnJoin') : $('btnCreate')).click(); });\n\n$('btnStart').onclick = function () { ac(); act('start'); };\n$('selTarget').onchange = function () { act('settings', { target: +this.value, roundSec: +$('selTime').value }); };\n$('selTime').onchange = function () { act('settings', { target: +$('selTarget').value, roundSec: +this.value }); };\n$('btnLeave1').onclick = leave;\n$('btnLeave2').onclick = function () { if (confirm('Keluar dari permainan?')) leave(); };\n$('btnGive').onclick = function () { act('giveup'); };\n$('btnSend').onclick = submit;\n$('btnBack').onclick = function () { tokens.pop(); if (S) refresh(); };\n$('btnClear').onclick = function () { tokens = []; if (S) refresh(); };\n$('pad').addEventListener('click', function (e) {\n  var b = e.target.closest ? e.target.closest('button[data-k]') : null;\n  if (b) addOp(b.dataset.k);\n});\n$('btnCopy').onclick = function () {\n  var text = location.origin + '/?r=' + (S ? S.code : '');\n  function fallback() {\n    var ta = document.createElement('textarea'); ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';\n    document.body.appendChild(ta); ta.select();\n    try { document.execCommand('copy'); toast('Tautan disalin ✓'); } catch (e) { toast(text); }\n    document.body.removeChild(ta);\n  }\n  if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(function () { toast('Tautan disalin ✓'); }, fallback);\n  else fallback();\n};\n\ndocument.addEventListener('keydown', function (e) {\n  if (!S || S.phase !== 'playing') return;\n  var tg = e.target && e.target.tagName; if (tg === 'INPUT' || tg === 'SELECT') return;\n  var k = e.key;\n  if (k === 'Enter') { submit(); e.preventDefault(); return; }\n  if (k === 'Backspace') { tokens.pop(); refresh(); e.preventDefault(); return; }\n  if (k === 'Escape') { tokens = []; refresh(); return; }\n  var map = { '+': '+', '-': '−', '*': '×', 'x': '×', '/': '÷', '(': '(', ')': ')' };\n  if (map[k]) { addOp(map[k]); e.preventDefault(); return; }\n  if (/^[0-9]$/.test(k) && S.numbers) {\n    var want = k === '0' ? 10 : +k;\n    for (var i = 0; i < 4; i++) {\n      if (S.numbers[i] === want && !tokens.some(function (t) { return t.t === 'n' && t.i === i; })) { add({ t: 'n', i: i, v: want }); break; }\n    }\n  }\n});\n\n/* ---------- awal ---------- */\n(function init() {\n  var q = new URLSearchParams(location.search), rc = (q.get('r') || '').toUpperCase().replace(/[^A-Z]/g, '').slice(0, 4);\n  $('inName').value = load('g24name') || '';\n  if (rc) $('inCode').value = rc;\n  var saved = sload('g24');\n  if (saved) {\n    try {\n      var s = JSON.parse(saved);\n      if (s && s.code && s.id && s.token && (!rc || rc === s.code)) { me = s; show('boot'); connect(); return; }\n    } catch (e) {}\n    sstore('g24', null);\n  }\n  show('home');\n  if (rc && $('inName').value) $('btnJoin').focus(); else if (rc) $('inName').focus();\n})();\n})();\n</script>\n</body>\n</html>\n";
const PAGE = HTML_TEMPLATE.replace('/*__PARSER__*/', () => parseExpr.toString());

function readJson(req, cb) {
  let size = 0; const chunks = [];
  req.on('data', (c) => { size += c.length; if (size > 4096) { req.destroy(); } else chunks.push(c); });
  req.on('end', () => { try { cb(null, JSON.parse(Buffer.concat(chunks).toString() || '{}')); } catch (e) { cb(e); } });
}
function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}
function auth(code, id, token) {
  const room = rooms.get(String(code || '').toUpperCase());
  const p = room && room.players.get(String(id || ''));
  if (!room || !p || p.token !== token) return null;
  return { room, p };
}

function handler(req, res) {
  const url = new URL(req.url, 'http://x');
  if (req.method === 'GET' && url.pathname === '/') {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
    return res.end(PAGE);
  }
  if (req.method === 'GET' && url.pathname === '/healthz') { res.writeHead(200); return res.end('ok'); }
  if (req.method === 'GET' && url.pathname === '/favicon.ico') { res.writeHead(204); return res.end(); }

  if (req.method === 'GET' && url.pathname === '/api/check') {
    const a = auth(url.searchParams.get('code'), url.searchParams.get('id'), url.searchParams.get('token'));
    res.writeHead(a ? 200 : 404, { 'Cache-Control': 'no-store' });
    return res.end(a ? 'ok' : 'tidak ada');
  }

  if (req.method === 'GET' && url.pathname === '/api/events') {
    const a = auth(url.searchParams.get('code'), url.searchParams.get('id'), url.searchParams.get('token'));
    if (!a) { res.writeHead(404); return res.end('room tidak ditemukan'); }
    res.writeHead(200, {
      'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform',
      'Connection': 'keep-alive', 'X-Accel-Buffering': 'no',
    });
    res.write('retry: 1500\n\n');
    const { room, p } = a;
    if (p.res && p.res !== res) { try { p.res.end(); } catch (e) { /* */ } }
    p.res = res; p.connected = true; p.lastSeen = now();
    broadcast(room);
    req.on('close', () => {
      if (p.res === res) {
        p.res = null; p.connected = false; p.lastSeen = now();
        if (room.hostId === p.id) {
          const next = [...room.players.values()].find((x) => x.connected);
          if (next) room.hostId = next.id;
        }
        broadcast(room);
        checkAllGaveUp(room);
      }
    });
    return;
  }

  if (req.method === 'POST' && url.pathname.startsWith('/api/')) {
    return readJson(req, (err, body) => {
      if (err) return json(res, 400, { error: 'Permintaan tidak valid.' });
      if (url.pathname === '/api/create') {
        if (rooms.size >= MAX_ROOMS) return json(res, 503, { error: 'Server penuh, coba lagi nanti.' });
        const room = createRoom();
        const p = addPlayer(room, cleanName(body.name));
        return json(res, 200, { code: room.code, id: p.id, token: p.token, name: p.name });
      }
      if (url.pathname === '/api/join') {
        const room = rooms.get(String(body.code || '').toUpperCase().trim());
        if (!room) return json(res, 404, { error: 'Kode ruangan tidak ditemukan.' });
        if (room.players.size >= MAX_PLAYERS) return json(res, 409, { error: 'Ruangan sudah penuh (maks. 4 pemain).' });
        const p = addPlayer(room, cleanName(body.name));
        broadcast(room);
        return json(res, 200, { code: room.code, id: p.id, token: p.token, name: p.name });
      }
      if (url.pathname === '/api/action') {
        const a = auth(body.code, body.id, body.token);
        if (!a) return json(res, 404, { error: 'Sesi tidak ditemukan.' });
        handleAction(a.room, a.p, body);
        return json(res, 200, { ok: true });
      }
      json(res, 404, { error: 'Tidak ada.' });
    });
  }
  res.writeHead(404); res.end('Tidak ada.');
}

// Pembersihan berkala: keepalive SSE, hapus pemain/ruangan yang sudah lama pergi
function sweep() {
  const t = now();
  for (const room of [...rooms.values()]) {
    for (const p of [...room.players.values()]) {
      if (p.res) { try { p.res.write(': ping\n\n'); } catch (e) { /* */ } }
      const limit = room.phase === 'lobby' ? 60000 : 300000;
      if (!p.connected && t - p.lastSeen > limit) removePlayer(room, p);
    }
  }
  for (const room of [...rooms.values()]) {
    if (t - room.lastActive > 30 * 60000 && ![...room.players.values()].some((p) => p.connected)) {
      clearTimeout(room.timer); rooms.delete(room.code);
    }
  }
}

function createGameServer() {
  const server = http.createServer(handler);
  const iv = setInterval(sweep, 15000);
  iv.unref();
  server.on('close', () => { clearInterval(iv); for (const r of rooms.values()) clearTimeout(r.timer); rooms.clear(); });
  return server;
}

module.exports = { createGameServer, parseExpr, solve24, makePuzzle, rooms };

if (require.main === module) {
  const PORT = +process.env.PORT || 3000;
  createGameServer().listen(PORT, '0.0.0.0', () => {
    console.log('\nGame 24 berjalan!');
    console.log('  Di perangkat ini : http://localhost:' + PORT);
    for (const list of Object.values(os.networkInterfaces())) {
      for (const n of list || []) {
        if (n.family === 'IPv4' && !n.internal) console.log('  Satu WiFi/LAN    : http://' + n.address + ':' + PORT);
      }
    }
    console.log('\nTekan Ctrl+C untuk berhenti.\n');
  });
}
