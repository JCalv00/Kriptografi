"""SecureVote - prototipe kecil mekanisme kunci online voting (bukan implementasi produksi)."""
import os, hashlib, struct, math
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes, serialization as S
from cryptography.exceptions import InvalidSignature, InvalidTag

raw = lambda k: k.public_bytes(S.Encoding.Raw, S.PublicFormat.Raw)
enc = lambda *parts: b"".join(struct.pack(">I", len(p)) + p for p in parts)      # canonical_encode
H = lambda *b: hashlib.sha256(b"".join(b)).digest()
i2b = lambda x: x.to_bytes((x.bit_length() + 7) // 8 or 1, "big")
fingerprint = lambda pub: hashlib.sha256(pub).hexdigest()[:32]

# ---------- RSA blind signature (Chaum) dengan Full-Domain Hash ----------
def fdh(msg, n):
    k, out, i = (n.bit_length() + 7) // 8, b"", 0
    while len(out) < k + 8:
        out += H(struct.pack(">I", i), msg); i += 1
    return int.from_bytes(out, "big") % n

def blind(msg, n, e):
    m = fdh(msg, n)
    while True:
        r = int.from_bytes(os.urandom((n.bit_length() + 7) // 8), "big") % n
        if r > 1 and math.gcd(r, n) == 1: break
    return (m * pow(r, e, n)) % n, r, m                     # m' = m * r^e mod n

def unblind(s_blind, r, n, e, m):
    s = (s_blind * pow(r, -1, n)) % n                       # s = s' * r^-1 mod n
    if pow(s, e, n) != m: raise ValueError("blind signature tidak valid")
    return s

# ---------- Pihak-pihak ----------
class Panitia:                                              # trust anchor (PA)
    def __init__(self): self.sk = Ed25519PrivateKey.generate(); self.pub = raw(self.sk.public_key())

class Voter:
    def __init__(self, vid): self.id = vid; self.ik = Ed25519PrivateKey.generate(); self.ik_pub = raw(self.ik.public_key())

class Registrar:
    def __init__(self, election_id, roll, bits=3072):
        self.eid, self.roll, self.issued, self.log = election_id, roll, set(), []
        key = rsa.generate_private_key(65537, bits); nums = key.private_numbers()
        self.n, self.e, self._d = nums.public_numbers.n, nums.public_numbers.e, nums.d
    def issue(self, voter_id, blinded, sig):
        if voter_id not in self.roll: raise ValueError("bukan pemilih terdaftar")
        Ed25519PublicKey.from_public_bytes(self.roll[voter_id]).verify(
            sig, enc(b"credreq-v1", self.eid, voter_id.encode(), i2b(blinded)))
        if voter_id in self.issued: raise ValueError("kredensial sudah pernah diterbitkan")
        if not (1 < blinded < self.n): raise ValueError("nilai blinded tidak valid")
        self.issued.add(voter_id); self.log.append(blinded)
        return pow(blinded, self._d, self.n)

def params_body(p):
    return enc(b"params-v1", p["eid"], i2b(p["n"]), i2b(p["e"]), p["T_pub"], p["B_pub"],
               b"|".join(c.encode() for c in p["candidates"]), struct.pack(">Q", p["close"]))

def make_params(panitia, eid, reg, tally_pub, board_pub, candidates, close):
    p = dict(eid=eid, n=reg.n, e=reg.e, T_pub=tally_pub, B_pub=board_pub, candidates=candidates, close=close)
    p["sig"] = panitia.sk.sign(params_body(p)); return p

def verify_params(p, pa_pub_pinned):
    """Tanda tangan diperiksa terhadap isi parameter yang DIPAKAI (dihitung ulang), bukan isi yang dikirim."""
    Ed25519PublicKey.from_public_bytes(pa_pub_pinned).verify(p["sig"], params_body(p)); return p

# ---------- Pemilih: kredensial anonim ----------
def get_credential(voter, reg, params):
    sk = Ed25519PrivateKey.generate(); vk = raw(sk.public_key())
    msg = enc(b"cred-v1", params["eid"], vk)
    blinded, r, m = blind(msg, params["n"], params["e"])
    req = voter.ik.sign(enc(b"credreq-v1", params["eid"], voter.id.encode(), i2b(blinded)))
    s = unblind(reg.issue(voter.id, blinded, req), r, params["n"], params["e"], m)
    return dict(sk=sk, vk=vk, sigR=s)

# ---------- Pemilih: surat suara terenkripsi ----------
def ballot_ctx(eid, ek_pub, t_pub): return H(enc(eid, ek_pub, t_pub))
def wkey(shared, eid, ek_pub, t_pub): return HKDF(hashes.SHA256(), 32, salt=ballot_ctx(eid, ek_pub, t_pub), info=b"securevote-v1/ballot").derive(shared)

def cast(cred, params, choice):
    eid = params["eid"]
    ek = X25519PrivateKey.generate(); ek_pub = raw(ek.public_key())
    kb = wkey(ek.exchange(X25519PublicKey.from_public_bytes(params["T_pub"])), eid, ek_pub, params["T_pub"])
    nonce = os.urandom(12)
    pt = enc(b"ballot-v1", eid, bytes([choice]), os.urandom(16))
    C = AESGCM(kb).encrypt(nonce, pt, enc(eid, cred["vk"]))
    entry = dict(eid=eid, vk=cred["vk"], sigR=cred["sigR"], ek_pub=ek_pub, nonce=nonce, C=C, kc=H(b"kc-v1", kb))
    entry["sig"] = cred["sk"].sign(body_of(entry)); del ek, kb
    return entry

def body_of(e): return enc(b"entry-v1", e["eid"], e["vk"], i2b(e["sigR"]), e["ek_pub"], e["nonce"], e["C"], e["kc"])

# ---------- Bulletin board: hash chain + resi bertanda tangan ----------
class Board:
    def __init__(self, params):
        self.sk = Ed25519PrivateKey.generate(); self.pub = raw(self.sk.public_key())
        self.p, self.entries, self.seen, self.head, self.chain = params, [], set(), b"\0" * 32, []
    def post(self, e, now):
        p = self.p
        if now > p["close"]: raise ValueError("pemilu sudah ditutup")
        if pow(e["sigR"], p["e"], p["n"]) != fdh(enc(b"cred-v1", p["eid"], e["vk"]), p["n"]): raise ValueError("kredensial tidak sah")
        Ed25519PublicKey.from_public_bytes(e["vk"]).verify(e["sig"], body_of(e))
        if e["vk"] in self.seen: raise ValueError("kredensial sudah dipakai (suara ganda)")
        self.seen.add(e["vk"]); self.head = H(self.head, body_of(e), e["sig"])
        self.entries.append(e); self.chain.append(self.head); i = len(self.entries) - 1
        return dict(index=i, h=self.head, sig=self.sk.sign(enc(b"receipt-v1", p["eid"], struct.pack(">Q", i), self.head)))

def verify_log(entries, receipts, b_pub, eid):
    """Auditor / pemilih: hitung ulang rantai hash dan cocokkan dengan resi bertanda tangan Board."""
    h, chain = b"\0" * 32, []
    for e in entries: h = H(h, body_of(e), e["sig"]); chain.append(h)
    for r in receipts:
        Ed25519PublicKey.from_public_bytes(b_pub).verify(r["sig"], enc(b"receipt-v1", eid, struct.pack(">Q", r["index"]), r["h"]))
        if r["index"] >= len(chain) or chain[r["index"]] != r["h"]: raise ValueError("log tidak cocok dengan resi (suara dihapus/diubah)")
    return True

# ---------- Tally ----------
def tally(t_priv, entries, params):
    out = []
    for e in entries:
        kb = wkey(t_priv.exchange(X25519PublicKey.from_public_bytes(e["ek_pub"])), e["eid"], e["ek_pub"], params["T_pub"])
        out.append(dict(vk=e["vk"], kb=kb, choice=open_ballot(e, kb)))
    return out

def open_ballot(e, kb):
    if H(b"kc-v1", kb) != e["kc"]: raise ValueError("key commitment tidak cocok")
    pt = AESGCM(kb).decrypt(e["nonce"], e["C"], enc(e["eid"], e["vk"]))
    return _choice(pt)

def _choice(pt):
    parts, i = [], 0
    while i < len(pt): L = struct.unpack(">I", pt[i:i+4])[0]; parts.append(pt[i+4:i+4+L]); i += 4 + L
    return parts[2][0]

def audit(entries, published, n_cand):
    """Siapa pun: verifikasi tiap kunci yang dipublikasikan, lalu hitung ulang."""
    counts = [0] * n_cand
    for e, rec in zip(entries, published):
        if rec["vk"] != e["vk"]: raise ValueError("urutan/vk tidak cocok")
        counts[open_ballot(e, rec["kb"])] += 1
    return counts
