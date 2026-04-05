/**
 * Hash Point Worker — sequential key search, all synchronous
 * Decimal → secp256k1 → compressed pubkey → SHA256 → RIPEMD160 → Hash160
 * Reports progress every N keys so the UI bar stays live
 */

const P  = BigInt("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
const Gx = BigInt("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798");
const Gy = BigInt("0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8");

function modpow(b,e,m){let r=1n;b=b%m;while(e>0n){if(e&1n)r=r*b%m;e>>=1n;b=b*b%m;}return r;}
function modinv(a,m){return modpow(((a%m)+m)%m,m-2n,m);}
function pointAdd(A,B){
  if(!A)return B;if(!B)return A;
  const[x1,y1]=A,[x2,y2]=B;
  if(x1===x2&&y1!==y2)return null;
  let lam=x1===x2?(3n*x1*x1*modinv(2n*y1,P))%P:((y2-y1)*modinv(x2-x1,P))%P;
  lam=((lam%P)+P)%P;
  const x3=((lam*lam-x1-x2)%P+P)%P;
  return[x3,((lam*(x1-x3)-y1)%P+P)%P];
}
function scalarMult(k,G){let R=null,A=G;while(k>0n){if(k&1n)R=pointAdd(R,A);A=pointAdd(A,A);k>>=1n;}return R;}

// ── Pure-JS SHA256 (synchronous) ─────────────────────────────────────────────
function sha256(data) {
  const K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
  ];
  const msg = Array.from(data);
  const bl  = msg.length * 8;
  msg.push(0x80);
  while (msg.length % 64 !== 56) msg.push(0);
  for (let i = 7; i >= 0; i--) msg.push((bl / Math.pow(2, i*8)) & 0xff);
  let [h0,h1,h2,h3,h4,h5,h6,h7] = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const rotr = (x,n) => ((x>>>n)|(x<<(32-n)))>>>0;
  for (let i = 0; i < msg.length; i += 64) {
    const w = [];
    for (let j=0;j<16;j++) w[j]=(msg[i+j*4]<<24)|(msg[i+j*4+1]<<16)|(msg[i+j*4+2]<<8)|msg[i+j*4+3];
    for (let j=16;j<64;j++){
      const s0=(rotr(w[j-15],7)^rotr(w[j-15],18)^(w[j-15]>>>3))>>>0;
      const s1=(rotr(w[j-2],17)^rotr(w[j-2],19)^(w[j-2]>>>10))>>>0;
      w[j]=(w[j-16]+s0+w[j-7]+s1)>>>0;
    }
    let [a,b,c,d,e,f,g,h]=[h0,h1,h2,h3,h4,h5,h6,h7];
    for (let j=0;j<64;j++){
      const S1=(rotr(e,6)^rotr(e,11)^rotr(e,25))>>>0;
      const ch=((e&f)^(~e&g))>>>0;
      const t1=(h+S1+ch+K[j]+w[j])>>>0;
      const S0=(rotr(a,2)^rotr(a,13)^rotr(a,22))>>>0;
      const maj=((a&b)^(a&c)^(b&c))>>>0;
      const t2=(S0+maj)>>>0;
      [h,g,f,e,d,c,b,a]=[g,f,e,(d+t1)>>>0,c,b,a,(t1+t2)>>>0];
    }
    h0=(h0+a)>>>0;h1=(h1+b)>>>0;h2=(h2+c)>>>0;h3=(h3+d)>>>0;
    h4=(h4+e)>>>0;h5=(h5+f)>>>0;h6=(h6+g)>>>0;h7=(h7+h)>>>0;
  }
  const out=[];
  [h0,h1,h2,h3,h4,h5,h6,h7].forEach(h=>{out.push((h>>>24)&0xff,(h>>>16)&0xff,(h>>>8)&0xff,h&0xff);});
  return out;
}

// ── Pure-JS RIPEMD160 (synchronous) ──────────────────────────────────────────
function ripemd160(data) {
  const msg = Array.from(data);
  const rotl = (x,n) => ((x<<n)|(x>>>(32-n)))>>>0;
  const K  = [0x00000000,0x5A827999,0x6ED9EBA1,0x8F1BBCDC,0xA953FD4E];
  const KK = [0x50A28BE6,0x5C4DD124,0x6D703EF3,0x7A6D76E9,0x00000000];
  const F  = (j,x,y,z) => j<16?(x^y^z)>>>0:j<32?((x&y)|(~x&z))>>>0:j<48?((x|~y)^z)>>>0:j<64?((x&z)|(y&~z))>>>0:(x^(y|~z))>>>0;
  const R  = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13];
  const RR = [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11];
  const S  = [11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6];
  const SS = [8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11];
  const bl = msg.length*8;
  msg.push(0x80);
  while(msg.length%64!==56)msg.push(0);
  for(let i=0;i<8;i++)msg.push((bl/Math.pow(2,i*8))&0xff);
  let h0=0x67452301,h1=0xEFCDAB89,h2=0x98BADCFE,h3=0x10325476,h4=0xC3D2E1F0;
  for(let i=0;i<msg.length;i+=64){
    const X=[];
    for(let j=0;j<16;j++)X[j]=(msg[i+j*4])|(msg[i+j*4+1]<<8)|(msg[i+j*4+2]<<16)|(msg[i+j*4+3]<<24);
    let[al,bl2,cl,dl,el]=[h0,h1,h2,h3,h4],[ar,br,cr,dr,er]=[h0,h1,h2,h3,h4];
    for(let j=0;j<80;j++){
      const kl=Math.floor(j/16);
      let T=(rotl(((al+F(j,bl2,cl,dl))>>>0)+X[R[j]]+K[kl]>>>0,S[j])+el)>>>0;
      [al,el,dl,cl,bl2]=[el,dl,rotl(cl,10),bl2,T];
      T=(rotl(((ar+F(79-j,br,cr,dr))>>>0)+X[RR[j]]+KK[kl]>>>0,SS[j])+er)>>>0;
      [ar,er,dr,cr,br]=[er,dr,rotl(cr,10),br,T];
    }
    const T=(h1+cl+dr)>>>0;
    h1=(h2+dl+er)>>>0;h2=(h3+el+ar)>>>0;h3=(h4+al+br)>>>0;h4=(h0+bl2+cr)>>>0;h0=T;
  }
  const out=[];
  [h0,h1,h2,h3,h4].forEach(h=>{out.push(h&0xff,(h>>8)&0xff,(h>>16)&0xff,(h>>24)&0xff);});
  return out.map(b=>b.toString(16).padStart(2,"0")).join("");
}

function toHash160(privkey) {
  const [x,y] = scalarMult(privkey,[Gx,Gy]);
  const prefix = (y%2n===0n)?0x02:0x03;
  const xHex   = x.toString(16).padStart(64,"0");
  const xBytes = xHex.match(/.{2}/g).map(b=>parseInt(b,16));
  const pubkey = [prefix,...xBytes];
  const s      = sha256(pubkey);
  return ripemd160(s);
}

// Self-test
function selfTest() {
  const got = toHash160(BigInt("1770887431106183748773"));
  return got === "4ceae6529f5d65d87cb6fbf5ae3b9b834204be54";
}

// ── Main search loop ──────────────────────────────────────────────────────────
// Uses chunked setTimeout to yield to the event loop and keep progress live
self.onmessage = (e) => {
  const { startDecimal, endDecimal, target, workerId } = e.data;

  if (!selfTest()) {
    self.postMessage({ type: "error", msg: "Self-test failed — crypto broken" });
    return;
  }

  const start = BigInt(startDecimal);
  const end   = BigInt(endDecimal);
  const total = end - start;
  const tgt   = target.toLowerCase().trim();

  // Process BATCH_SIZE keys per tick, then yield so progress messages get through
  const BATCH = 500n;
  let   key   = start;

  function processBatch() {
    const batchEnd = key + BATCH < end ? key + BATCH : end;

    while (key < batchEnd) {
      const h160 = toHash160(key);
      if (h160 === tgt) {
        self.postMessage({
          type:    "found",
          key:     key.toString(16).padStart(64,"0"),
          decimal: key.toString(),
          h160,
          workerId
        });
        return; // stop
      }
      key++;
    }

    // Report progress
    const checked = key - start;
    const pct     = Number(checked * 100n / total);
    self.postMessage({ type: "progress", pct, currentKey: key.toString(), workerId });

    if (key < end) {
      setTimeout(processBatch, 0); // yield then continue
    } else {
      self.postMessage({ type: "done", workerId, checked: checked.toString() });
    }
  }

  processBatch();
};
