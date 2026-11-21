import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']], M = 250000;
function P(t: string) {
  const r = t.split('\n').filter((x) => x.length), h = r.length, w = Math.max(...r.map((x) => x.length)), a = new Uint8Array(w * h).fill(1), g: number[] = [], b: number[] = [];
  let p = -1;
  r.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x], i = y * w + x; if (c === '#') continue; a[i] = 0; if ('.*+'.includes(c)) g.push(i); if ('$*'.includes(c)) b.push(i); if ('@+'.includes(c)) p = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (!x || !y || x === w - 1 || y === h - 1) a[y * w + x] = 1;
  return { w, h, wall: a, goals: g, boxes: b.sort((x, y) => x - y), player: p };
}
function V(L: any) {
  const { w, wall, goals } = L, v = new Uint8Array(wall.length), q = [...goals];
  for (const g of goals) v[g] = 1;
  for (let i = 0; i < q.length; i++) { const x = q[i]!; for (const [dx, dy] of D) { const d = dy * w + dx, y = x - d; if (!wall[y] && !wall[y - d] && !v[y]) { v[y] = 1; q.push(y); } } }
  return v;
}
function R(L: any, o: Uint8Array, f: number, s: Int32Array, t: number, k: Int32Array) {
  const { w, wall } = L;
  let l = f, n = 0;
  k[n++] = f; s[f] = t;
  while (n) { const p = k[--n]!; if (p < l) l = p; for (let j = 0; j < 4; j++) { const q = j === 0 ? p - w : j === 1 ? p + w : j === 2 ? p - 1 : p + 1; if (!wall[q] && !o[q] && s[q] !== t) { s[q] = t; k[n++] = q; } } }
  return l;
}
function F(L: any, o: Uint8Array, g: Uint8Array, t: number) {
  const { w, wall } = L;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || o[a]) || !(wall[b] || o[b]) || !(wall[c] || o[c]) || !(wall[d] || o[d])) continue;
    if ((o[a] && !g[a]) || (o[b] && !g[b]) || (o[c] && !g[c]) || (o[d] && !g[d])) return true;
  }
  return false;
}
function W(L: any, o: Uint8Array, f: number, t: number) {
  const { w, wall } = L;
  if (f === t) return '';
  const v = new Int32Array(wall.length).fill(-1), h: string[] = [], q = [f];
  v[f] = f;
  for (let i = 0; i < q.length; i++) { const p = q[i]!; if (p === t) break; for (const [dx, dy, l] of D) { const s = p + dy * w + dx; if (wall[s] || o[s] || v[s] !== -1) continue; v[s] = p; h[s] = l; q.push(s); } }
  if (v[t] === -1) throw new Error('unreachable');
  let s = '';
  for (let p = t; p !== f; p = v[p]!) s = h[p]! + s;
  return s;
}
function S(L: any, m = M) {
  const { w, wall, goals } = L, z = wall.length, g = new Uint8Array(z);
  for (const x of goals) g[x] = 1;
  const v = V(L), o = new Uint8Array(z), a = new Int32Array(z), b = new Int32Array(z), k = new Int32Array(z);
  let n = 0;
  const ok = (x: number[]) => x.every((y) => g[y]);
  if (L.boxes.some((x) => !v[x])) return null;
  const B = [L.boxes], Y = [L.player], Q = [-1], X = new Map<number, number>();
  for (const x of L.boxes) o[x] = 1;
  X.set(((l: number, s: number[]) => { let c = l; for (const y of s) c = c * z + y; return c; })(R(L, o, L.player, a, ++n, k), L.boxes), 0);
  for (const x of L.boxes) o[x] = 0;
  let f = ok(L.boxes) ? 0 : -1;
  const key = (s: number[], l: number) => { let c = l; for (const y of s) c = c * z + y; return c; };
  for (let h = 0; f < 0 && h < B.length; h++) {
    const x = B[h]!;
    for (const y of x) o[y] = 1;
    R(L, o, Y[h]!, a, ++n, k);
    const e = n;
    for (let i = 0; i < x.length && f < 0; i++) {
      const c = x[i]!;
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = c + d;
        if (a[c - d] !== e || wall[t] || o[t] || !v[t]) continue;
        o[c] = 0; o[t] = 1;
        const fr = F(L, o, g, t);
        let K = -1, N: number[] | null = null;
        if (!fr) { N = x.slice(); N[i] = t; N.sort((p, q) => p - q); K = key(N, R(L, o, c, b, ++n, k)); }
        o[t] = 0; o[c] = 1;
        if (fr || X.has(K)) continue;
        if (B.length >= m) { for (const y of x) o[y] = 0; return null; }
        X.set(K, B.length); B.push(N!); Y.push(c); Q.push(h);
        if (ok(N!)) { f = B.length - 1; break; }
      }
    }
    for (const y of x) o[y] = 0;
  }
  if (f < 0) return null;
  const path: number[] = [];
  for (let s = f; s > 0; s = Q[s]!) path.push(s);
  path.reverse();
  let mv = '', p = L.player, x = L.boxes;
  for (const s of path) {
    const nb = B[s]!, from = x.find((y) => !nb.includes(y))!, to = nb.find((y) => !x.includes(y))!, d = to - from, dir = D.find(([dx, dy]) => dy * w + dx === d)!;
    for (const y of x) o[y] = 1;
    mv += W(L, o, p, from - d);
    for (const y of x) o[y] = 0;
    mv += dir[3]; p = from; x = nb;
  }
  return { pushes: path.length, moves: mv };
}
function G(L: any) {
  const { w, wall, goals, boxes, player } = L, v = V(L), row = Math.floor(player / w), c = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !v[i]) c[i] = 1;
  if (boxes.some((x) => c[x])) return null;
  const q = new Int32Array(wall.length).fill(-1), r: { boxes: number[]; goals: number[]; done?: boolean }[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || c[s] || q[s] >= 0) continue;
    const sq = [s];
    q[s] = r.length;
    for (let i = 0; i < sq.length; i++) for (const [dx, dy] of D) { const y = sq[i]! + dy * w + dx; if (!wall[y] && !c[y] && q[y] < 0) { q[y] = r.length; sq.push(y); } }
    r.push({ boxes: [], goals: [] });
  }
  for (const b of boxes) r[q[b]!]!.boxes.push(b);
  for (const g of goals) if (q[g]! >= 0) r[q[g]!]!.goals.push(g);
  if (goals.some((g) => q[g]! < 0) || r.some((x) => x.boxes.length !== x.goals.length)) return null;
  return r.filter((x) => x.boxes.length);
}
function solve(t: string) {
  const L = P(t), r = G(L);
  if (r === null) return S(L)?.moves ?? '';
  let p = L.player, mv = '';
  for (const room of r) {
    const wall = L.wall.slice();
    for (const o of r) if (o !== room) for (const b of o.done ? o.goals : o.boxes) wall[b] = 1;
    const s = S({ w: L.w, h: L.h, wall, goals: room.goals.slice().sort((a, b) => a - b), boxes: room.boxes.slice().sort((a, b) => a - b), player: p });
    if (s === null) return '';
    mv += s.moves;
    for (const c of s.moves.toLowerCase()) p += c === 'u' ? -L.w : c === 'd' ? L.w : c === 'l' ? -1 : 1;
    room.done = true;
  }
  return mv;
}
for (const id of readdirSync(I).sort()) {
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${solve(readFileSync(join(I, id, 'level.txt'), 'utf8'))}\n`);
}
