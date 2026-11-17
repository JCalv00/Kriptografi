import time, copy
from evote import *
res = []
def check(name, cond): res.append(cond); print(("[LULUS] " if cond else "[GAGAL] ") + name)
def rejected(name, fn, exc=Exception):
    try: fn()
    except exc as e: check(f"{name:62s} -> ditolak ({type(e).__name__})", True); return
    check(name + " -> TIDAK ditolak", False)

now = int(time.time()); close = now + 3600; eid = b"BEM-2026"; cands = ["Calon A", "Calon B", "Calon C"]
PA = Panitia()
voters = [Voter(f"v{i}") for i in range(5)]
roll = {v.id: v.ik_pub for v in voters}
reg = Registrar(eid, roll)
T = X25519PrivateKey.generate(); T_pub = raw(T.public_key())
bsk = Ed25519PrivateKey.generate()
params = make_params(PA, eid, reg, T_pub, raw(bsk.public_key()), cands, close)
board = Board(params); board.sk = bsk; board.pub = raw(bsk.public_key())
print("fingerprint PA:", fingerprint(PA.pub))
verify_params(params, PA.pub)                       # pemilih memverifikasi parameter (Fase 0)

# 1. pemilu normal
votes = [0, 1, 1, 2, 1]; creds, receipts = [], []
for v, c in zip(voters, votes):
    cr = get_credential(v, reg, params); creds.append(cr)
    receipts.append(board.post(cast(cr, params, c), now))
pub = tally(T, board.entries, params)
counts = audit(board.entries, pub, 3)
check(f"1. pemilu normal: hasil {counts} sesuai suara {[votes.count(i) for i in range(3)]}", counts == [votes.count(i) for i in range(3)])
check("1b. rantai hash + semua resi pemilih terverifikasi", verify_log(board.entries, receipts, board.pub, eid))
check("1c. pemilih menemukan suaranya sendiri di hasil publik", all(next(p for p in pub if p["vk"] == cr["vk"])["choice"] == c for cr, c in zip(creds, votes)))
check("1d. ciphertext tidak memuat pilihan terbaca (suara terenkripsi sebelum penutupan)", all(b"Calon" not in e["C"] for e in board.entries))

# 2-4 pendaftaran
eve = Voter("eve")
rejected("2. Orang tak terdaftar meminta kredensial", lambda: get_credential(eve, reg, params), ValueError)
rejected("3. Pemilih meminta kredensial kedua kali", lambda: get_credential(voters[0], reg, params), ValueError)
def t4():
    v = Voter("v9"); roll["v9"] = v.ik_pub
    blinded, r, m = blind(enc(b"cred-v1", eid, b"x" * 32), params["n"], params["e"])
    req = v.ik.sign(enc(b"credreq-v1", eid, b"v9", i2b(blinded)))
    reg.issue("v9", blinded + 1, req)                # Eve mengubah nilai blinded di jaringan
rejected("4. Eve mengubah nilai blinded pada permintaan pemilih", t4, InvalidSignature)

# 5-9 pemungutan suara
nv = Voter("late"); roll["late"] = nv.ik_pub; ncred = get_credential(nv, reg, params)
rejected("5a. Kredensial palsu (tanda tangan acak)", lambda: board.post(cast(dict(ncred, sigR=12345), params, 0), now), ValueError)
rsa2 = Registrar(eid, {}, bits=2048)
def t5b():
    sk = Ed25519PrivateKey.generate(); vk = raw(sk.public_key()); m = fdh(enc(b"cred-v1", eid, vk), rsa2.n)
    board.post(cast(dict(sk=sk, vk=vk, sigR=pow(m, rsa2._d, rsa2.n)), params, 0), now)
rejected("5b. Kredensial ditandatangani registrar palsu milik Eve", t5b, ValueError)
rejected("6. Eve memutar ulang surat suara korban (vk sama)", lambda: board.post(board.entries[0], now), ValueError)
def t7():
    e = cast(ncred, params, 0); stolen = dict(sk=Ed25519PrivateKey.generate(), vk=ncred["vk"], sigR=ncred["sigR"])
    board.post(cast(stolen, params, 2), now)         # Eve memakai kredensial yang terlihat, tapi tak punya sk
rejected("7. Eve memakai (vk, sigR) yang terlihat untuk suara sendiri", t7, InvalidSignature)
def t8():
    e = cast(ncred, params, 0); e["C"] = e["C"][:-1] + bytes([e["C"][-1] ^ 1]); board.post(e, now)
rejected("8. Eve mengubah ciphertext surat suara saat transit", t8, InvalidSignature)
rejected("9. Surat suara dikirim setelah pemilu ditutup", lambda: board.post(cast(ncred, params, 0), close + 1), ValueError)

# 10 parameter dipalsukan
def t10():
    fake = copy.deepcopy(params); fake["T_pub"] = raw(X25519PrivateKey.generate().public_key()); verify_params(fake, PA.pub)
rejected("10. Eve mengganti kunci Tally pada parameter pemilu", t10, InvalidSignature)
# 11 Board menghapus suara
rejected("11. Board menghapus suara pemilih ke-2 dari log", lambda: verify_log(board.entries[:1] + board.entries[2:], receipts, board.pub, eid), Exception)
# 12 Board mengubah suara
def t12():
    es = copy.deepcopy(board.entries); es[1]["C"] = es[3]["C"]; verify_log(es, receipts, board.pub, eid)
rejected("12. Board mengganti isi suara yang sudah diberi resi", t12, ValueError)
# 13 Tally curang
def t13():
    bad = copy.deepcopy(pub); bad[1]["kb"] = os.urandom(32); audit(board.entries, bad, 3)
rejected("13. Tally mempublikasikan kunci per surat suara yang salah", t13, ValueError)
# 14 unlinkability: setiap pasangan (blinded_j, kredensial_k) konsisten dengan suatu faktor r
ok = True; n = params["n"]
for j, bl in enumerate(reg.log[:5]):
    for cr in creds:
        m = fdh(enc(b"cred-v1", eid, cr["vk"]), n); r = (bl * pow(m, -1, n)) % n
        ok &= math.gcd(r, n) == 1       # r valid (unit mod n) -> pasangan (j, k) dapat dijelaskan
check("14. Registrar tidak dapat mengaitkan nilai blinded dengan kredensial (semua pasangan konsisten)", ok)
# 15 batas jaminan: parameter Eve diterima karena fingerprint PA tidak diverifikasi
EvePA = Panitia(); eT = X25519PrivateKey.generate()
fake = make_params(EvePA, eid, reg, raw(eT.public_key()), params["B_pub"], cands, close)
verify_params(fake, EvePA.pub)                       # pemilih salah mem-pin PA milik Eve
e = cast(creds[1], fake, 2)                          # surat suara dienkripsi ke kunci Eve
kb = wkey(eT.exchange(X25519PublicKey.from_public_bytes(e["ek_pub"])), eid, e["ek_pub"], fake["T_pub"])
leak = open_ballot(e, kb) == 2
check("15. [BATAS] PA palsu tidak diverifikasi -> Eve membaca pilihan: " + str(leak), leak)
print("\nSEMUA UJI SESUAI EKSPEKTASI" if all(res) else "\nADA YANG GAGAL")
