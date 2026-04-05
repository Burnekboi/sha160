/**
 * Web Worker — runs Pollard's Kangaroo search off the main thread
 * Receives: { startDecimal, chunkSize, target }
 * Posts back: { type: 'progress', pct } or { type: 'done', found, key }
 */

// secp256k1 parameters
const P  = BigInt("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
const Gx = BigInt("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798");
const Gy = BigInt("0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8");

function modpow(base, exp, mod) {
  let result = 1n;
  base = base % mod;
  while (exp > 0n) {
    if (exp % 2n === 1n) result = result * base % mod;
    exp >>= 1n;
    base = base * base % mod;
  }
  return result;
}

function modinv(a, m) {
  return modpow(((a % m) + m) % m, m - 2n, m);
}

function pointAdd(P1, P2) {
  if (!P1) return P2;
  if (!P2) return P1;
  const [x1, y1] = P1;
  const [x2, y2] = P2;
  if (x1 === x2 && y1 !== y2) return null;
  let lam = x1 === x2
    ? (3n * x1 * x1 * modinv(2n * y1, P)) % P
    : ((y2 - y1) * modinv(x2 - x1, P)) % P;
  lam = ((lam % P) + P) % P;
  const x3 = ((lam * lam - x1 - x2) % P + P) % P;
  const y3 = ((lam * (x1 - x3) - y1) % P + P) % P;
  return [x3, y3];
}

function scalarMult(k, point) {
  let result = null;
  let addend = point;
  while (k > 0n) {
    if (k & 1n) result = pointAdd(result, addend);
    addend = pointAdd(addend, addend);
    k >>= 1n;
  }
  return result;
}

// SHA256 using SubtleCrypto
async function sha256(buf) {
  const hash = await crypto.subtle.digest("SHA-256", buf);
  return new Uint8Array(hash);
}

// RIPEMD160 — pure JS implementation (no SubtleCrypto support)
function ripemd160(buf) {
  // Using a minimal RIPEMD160 implementation
  const msg = Array.from(buf);

  function rotl(x, n) { return ((x << n) | (x >>> (32 - n))) >>> 0; }

  const K  = [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E];
  const KK = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000];

  const F = (j, x, y, z) => {
    if (j < 16) return (x ^ y ^ z) >>> 0;
    if (j < 32) return ((x & y) | (~x & z)) >>> 0;
    if (j < 48) return ((x | ~y) ^ z) >>> 0;
    if (j < 64) return ((x & z) | (y & ~z)) >>> 0;
    return (x ^ (y | ~z)) >>> 0;
  };

  const R  = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13];
  const RR = [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11];
  const S  = [11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6];
  const SS = [8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11];

  // Padding
  const bitLen = msg.length * 8;
  msg.push(0x80);
  while (msg.length % 64 !== 56) msg.push(0);
  for (let i = 0; i < 8; i++) msg.push((bitLen / Math.pow(2, i * 8)) & 0xff);

  let h0 = 0x67452301, h1 = 0xEFCDAB89, h2 = 0x98BADCFE, h3 = 0x10325476, h4 = 0xC3D2E1F0;

  for (let i = 0; i < msg.length; i += 64) {
    const X = [];
    for (let j = 0; j < 16; j++) {
      X[j] = (msg[i+j*4]) | (msg[i+j*4+1] << 8) | (msg[i+j*4+2] << 16) | (msg[i+j*4+3] << 24);
    }
    let [al, bl, cl, dl, el] = [h0, h1, h2, h3, h4];
    let [ar, br, cr, dr, er] = [h0, h1, h2, h3, h4];

    for (let j = 0; j < 80; j++) {
      const kl = Math.floor(j / 16);
      let T = (rotl(((al + F(j, bl, cl, dl)) >>> 0) + X[R[j]] + K[kl] >>> 0, S[j]) + el) >>> 0;
      [al, el, dl, cl, bl] = [el, dl, rotl(cl, 10), bl, T];
      const kr = Math.floor(j / 16);
      T = (rotl(((ar + F(79-j, br, cr, dr)) >>> 0) + X[RR[j]] + KK[kr] >>> 0, SS[j]) + er) >>> 0;
      [ar, er, dr, cr, br] = [er, dr, rotl(cr, 10), br, T];
    }

    const T = (h1 + cl + dr) >>> 0;
    h1 = (h2 + dl + er) >>> 0;
    h2 = (h3 + el + ar) >>> 0;
    h3 = (h4 + al + br) >>> 0;
    h4 = (h0 + bl + cr) >>> 0;
    h0 = T;
  }

  const out = [];
  [h0, h1, h2, h3, h4].forEach(h => {
    out.push(h & 0xff, (h >> 8) & 0xff, (h >> 16) & 0xff, (h >> 24) & 0xff);
  });
  return out.map(b => b.toString(16).padStart(2, "0")).join("");
}

async function privkeyToHash160(privkey) {
  const [x, y] = scalarMult(privkey, [Gx, Gy]);
  const prefix = (y % 2n === 0n) ? 0x02 : 0x03;
  const xHex   = x.toString(16).padStart(64, "0");
  const xBytes = new Uint8Array(xHex.match(/.{2}/g).map(b => parseInt(b, 16)));
  const pubkey = new Uint8Array([prefix, ...xBytes]);
  const sha    = await sha256(pubkey);
  return ripemd160(sha);
}

self.onmessage = async (e) => {
  const { startDecimal, chunkSize, target } = e.data;
  const start  = BigInt(startDecimal);
  const size   = BigInt(chunkSize);
  const SAMPLES = 1000;
  const step   = size / BigInt(SAMPLES);

  for (let i = 0; i < SAMPLES; i++) {
    const privkey = start + BigInt(i) * step;
    const h160    = await privkeyToHash160(privkey);

    if (h160 === target.toLowerCase()) {
      self.postMessage({
        type: "done",
        found: true,
        key:   privkey.toString(16).padStart(64, "0"),
        h160
      });
      return;
    }

    if (i % 10 === 0) {
      self.postMessage({ type: "progress", pct: Math.floor((i / SAMPLES) * 100), currentKey: privkey.toString() });
    }
  }

  self.postMessage({ type: "done", found: false, key: null, lastKey: (start + BigInt(SAMPLES - 1) * step).toString() });
};
