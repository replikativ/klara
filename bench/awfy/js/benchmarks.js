// Are We Fast Yet? (Marr et al., DLS 2016) Mandelbrot, Sieve, Towers and List,
// written after the suite's JavaScript versions, with the same harness
// shape as bench/klara/awfy.clj: run until a second has passed, report the
// mean of the second half.
'use strict';

function mandelbrot(size) {
  let sum = 0, byteAcc = 0, bitNum = 0, y = 0;
  while (y < size) {
    const ci = (2.0 * y / size) - 1.0;
    let x = 0;
    while (x < size) {
      let zrzr = 0.0, zi = 0.0, zizi = 0.0;
      const cr = (2.0 * x / size) - 1.5;
      let z = 0, notDone = true, escape = 0;
      while (notDone && z < 50) {
        const zr = zrzr - zizi + cr;
        zi = 2.0 * zr * zi + ci;
        zrzr = zr * zr;
        zizi = zi * zi;
        if (zrzr + zizi > 4.0) { notDone = false; escape = 1; }
        z += 1;
      }
      byteAcc = (byteAcc << 1) + escape;
      bitNum += 1;
      if (bitNum === 8) { sum ^= byteAcc; byteAcc = 0; bitNum = 0; }
      else if (x === size - 1) { byteAcc <<= (8 - bitNum); sum ^= byteAcc; byteAcc = 0; bitNum = 0; }
      x += 1;
    }
    y += 1;
  }
  return sum;
}

function sieve(size) {
  const flags = new Array(size).fill(true);
  let primeCount = 0;
  for (let i = 2; i <= size; i++) {
    if (flags[i - 1]) {
      primeCount++;
      for (let k = i + i; k <= size; k += i) flags[k - 1] = false;
    }
  }
  return primeCount;
}

class Disk { constructor(size) { this.size = size; this.next = null; } }
function towers() {
  const piles = [null, null, null];
  let moves = 0;
  function push(disk, pile) {
    const top = piles[pile];
    if (top && disk.size >= top.size) throw new Error('Cannot put a big disk on a smaller one');
    disk.next = top; piles[pile] = disk;
  }
  function pop(pile) {
    const top = piles[pile];
    if (top === null) throw new Error('Attempting to remove a disk from an empty pile');
    piles[pile] = top.next; top.next = null; return top;
  }
  function moveTop(from, to) { push(pop(from), to); moves++; }
  function moveDisks(disks, from, to) {
    if (disks === 1) { moveTop(from, to); return; }
    const other = 3 - from - to;
    moveDisks(disks - 1, from, other); moveTop(from, to); moveDisks(disks - 1, other, to);
  }
  for (let i = 13; i >= 0; i--) push(new Disk(i), 0);
  moveDisks(13, 0, 1);
  return moves;
}

class Element { constructor(v) { this.val = v; this.next = null; } }
function makeList(n) { if (n === 0) return null; const e = new Element(n); e.next = makeList(n - 1); return e; }
function isShorterThan(x, y) {
  let xt = x, yt = y;
  while (yt !== null) { if (xt === null) return true; xt = xt.next; yt = yt.next; }
  return false;
}
function tail(x, y, z) {
  if (isShorterThan(y, x)) return tail(tail(x.next, y, z), tail(y.next, z, x), tail(z.next, x, y));
  return z;
}
function length(x) { let n = 0; while (x !== null) { n++; x = x.next; } return n; }
function list() { return length(tail(makeList(15), makeList(10), makeList(6))); }

const benchmarks = {
  mandelbrot: [() => mandelbrot(500), 191],
  sieve: [() => sieve(5000), 669],
  towers: [towers, 8191],
  list: [list, 10],
};

function measure(f) {
  const times = [];
  const start = process.hrtime.bigint();
  while (Number(process.hrtime.bigint() - start) < 1e9) {
    const t = process.hrtime.bigint(); f(); times.push(Number(process.hrtime.bigint() - t) / 1e6);
  }
  const half = times.slice(Math.floor(times.length / 2));
  return half.reduce((a, b) => a + b, 0) / half.length;
}

const out = {};
for (const [name, [f, expected]] of Object.entries(benchmarks)) {
  const ok = f() === expected;
  out[name] = { ok, ms: measure(f) };
}
console.log(JSON.stringify(out));
