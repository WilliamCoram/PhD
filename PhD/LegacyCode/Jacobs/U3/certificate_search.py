#!/usr/bin/env python3
"""Search for the nine certificates of [Jacobs, Lemmas 2.4/2.5], left-handed convention.

Solves, for each (i,t) in Fin 3 x Fin 3:

    classRep i * etaRep t = d * classRep sigma * u,   u in U1(9),

where u := (d * classRep sigma)^{-1} * classRep i * etaRep t is defined by the equation,
d is a Hurwitz quaternion of reduced norm 3 (forced by the determinant bookkeeping),
and the whole content is the side condition u in U1(9).

Conventions verified against the Lean sources:
  * theta (U3/Setting.lean, theta_tmul_one):
        theta(r,x,y,z) = [[r + x nu + z,  x - y - z nu],
                          [x + y - z nu,  r - x nu - z]]
  * classRep (U3/ClassSet.lean, toMatrix_classRep): diag(1,1), diag(5,2), diag(7,4)
  * etaRep (U3/EtaDecomposition.lean, toMatrix_etaRep): [[1,0],[9t,3]]
  * U1(9) at 3 (PROGRESS.md sec.4): entries 3-integral, a == 1 mod 9, c == 0 mod 9,
    det a 3-unit  (this makes M and M^{-1} both Sigma1(9))
  * away from 3: u_l = d_l^{-1}, so need d, d^{-1} integral away from 3
    <=> d in Hurwitz order with nrd(d) = 3  (automatic for the candidate set)
  * nu = 2695 mod 3^10  (2695^2 + 2 = 3^11 * 41), sign pinned by nu == 1 mod 3
  * adjParams (U3/KappaAction.lean): g -> [[g11, -g01], [-g10, g00]]

Validation stages:
  1. exactly one hit (sigma, d) per pair (uniqueness = Lemma 2.2 stabilizer + Thm 2.1)
  2. sigma(i,t) != i for all nine (trace U3 = 0)
  3. row multisets of sigma match the block multiplicities of (2.1.4)-(2.1.9)
  4. acting matrices adjParams(theta(c_i^{-1} d c_sigma)) reproduce the transcribed
     eps-matrices of U3Data.lean (E1-corrected) -- the B15 identification, exact in Q(nu)

Run:  python3 certificate_search.py   (pure stdlib, < 1 s)

Feeds:  sigmaTable / dTable / uTable in PhD/Jacobs/U3/Factorisations.lean
        (ticket B12 on the qmf board); provenance section in that file's header.

Results (computed 2026-08-05; all four validation stages passed, unique hit per pair):

    i, t, sigma(i,t), d(i,t) = (r, x, y, z)
    0, 0, 2, (-1, -1, 1, 0)
    0, 1, 1, (-1/2, 1/2, 3/2, 1/2)
    0, 2, 1, (-1/2, -3/2, -1/2, -1/2)
    1, 0, 0, (1, 1, -1, 0)
    1, 1, 2, (-1/2, 1/2, 3/2, 1/2)
    1, 2, 2, (-1/2, -3/2, -1/2, -1/2)
    2, 0, 1, (1, 1, -1, 0)
    2, 1, 0, (1/2, -1/2, -3/2, -1/2)
    2, 2, 0, (1/2, 3/2, 1/2, 1/2)

i.e. three quaternions up to sign: a = 1+i-j, b = (-1+i+3j+k)/2, c = -(1+3i+j+k)/2,
with d(0,.) = (-a, b, c), d(1,.) = (a, b, c), d(2,.) = (a, -b, -c).

Cross-checks against the thesis: sigma-table = (2,1,1),(0,2,2),(1,0,0), the thesis's
table on the nose; d(0,0) = 3 * d_thesis and u(0,0) is literally the printed third
factor of the p. 26 example.  The eps-identification closes EXACTLY in the form

    eps_{i,j}(t') = theta3( c_j^{-1} * conj(d(i,t')) * c_i )     (quaternion conjugate)

for all nine summands -- confirming the E1-corrected eps12M2 (the misprinted
-15/14 value does not occur).  Handedness normalisation found:
adjParams(theta3(w_t' u^{-1})) = (det c_j / det c_i) * eps_{i,j}(t'), a 1-unit
scalar (det c_i in {1,10,28}, all == 1 mod 9), so sum_weightGenFun_eq_h (B15) must
carry the kappa(s) s^{-2} factor via weightGenFun_smul, s = det c_i / det c_j.
"""
from fractions import Fraction as F
from itertools import product
from collections import Counter

NU = 2695          # nu mod 3^10
CAP = 8            # valuations >= CAP reported as CAP (checks only need thresholds 0, 2)

# ---------- Q(nu) arithmetic: x = (p, q) represents p + q*nu, nu^2 = -2 ----------
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def sub(x, y): return (x[0] - y[0], x[1] - y[1])
def mul(x, y): return (x[0]*y[0] - 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def neg(x): return (-x[0], -x[1])
def qinv(x):
    n = x[0]*x[0] + 2*x[1]*x[1]          # (p+q nu)(p-q nu) = p^2 + 2 q^2
    return (F(x[0], 1)/n, F(-x[1], 1)/n)
def scal(c, x): return (c*x[0], c*x[1])

def v3_rat(r):
    r = F(r)
    if r == 0: return CAP
    v, n, d = 0, r.numerator, r.denominator
    while n % 3 == 0: n //= 3; v += 1
    while d % 3 == 0: d //= 3; v -= 1
    return min(v, CAP)

def v3(x):
    """3-adic valuation of p + q*nu via nu == 2695 mod 3^10 (exact below CAP)."""
    return v3_rat(F(x[0]) + F(x[1]) * NU)

# ---------- 2x2 matrices over Q(nu) ----------
def mmul(A, B):
    return [[add(mul(A[0][0], B[0][0]), mul(A[0][1], B[1][0])),
             add(mul(A[0][0], B[0][1]), mul(A[0][1], B[1][1]))],
            [add(mul(A[1][0], B[0][0]), mul(A[1][1], B[1][0])),
             add(mul(A[1][0], B[0][1]), mul(A[1][1], B[1][1]))]]
def mdet(A): return sub(mul(A[0][0], A[1][1]), mul(A[0][1], A[1][0]))
def minv(A):
    di = qinv(mdet(A))
    return [[mul(di, A[1][1]), mul(di, neg(A[0][1]))],
            [mul(di, neg(A[1][0])), mul(di, A[0][0])]]
def adjParams(G):
    return [[G[1][1], neg(G[0][1])], [neg(G[1][0]), G[0][0]]]

def theta(d):
    r, x, y, z = d
    return [[(r + z, x), (x - y, -z)],
            [(x + y, -z), (r - z, -x)]]

def nrd(d): return sum(c*c for c in d)

def c_(p, q=0): return (F(p), F(q))

# ---------- fixed data ----------
C = [[[c_(1), c_(0)], [c_(0), c_(1)]],
     [[c_(5), c_(0)], [c_(0), c_(2)]],
     [[c_(7), c_(0)], [c_(0), c_(4)]]]
W = [[[c_(1), c_(0)], [c_(9*t), c_(3)]] for t in range(3)]

def in_U19(M):
    """entries 3-integral, M00 == 1 mod 9, M10 == 0 mod 9, det a 3-unit."""
    for row in M:
        for e in row:
            if v3(e) < 0: return False
    if v3(sub(M[0][0], c_(1))) < 2: return False
    if v3(M[1][0]) < 2: return False
    return v3(mdet(M)) == 0

# ---------- Hurwitz quaternions of reduced norm 3 (the 96) ----------
def hurwitz_norm3():
    out = []
    for pos0 in range(4):                       # integer: perms of (+-1,+-1,+-1,0)
        for signs in product([1, -1], repeat=3):
            coords, k = [], 0
            for m in range(4):
                if m == pos0: coords.append(F(0))
                else: coords.append(F(signs[k])); k += 1
            out.append(tuple(coords))
    for pos3 in range(4):                       # half-int: (+-1,+-1,+-1,+-3)/2
        for signs in product([1, -1], repeat=4):
            out.append(tuple(F(3 if m == pos3 else 1) * signs[m] / 2 for m in range(4)))
    assert len(out) == 96 and all(nrd(d) == 3 for d in out)
    return out

CANDS = hurwitz_norm3()

# ---------- the search ----------
def search_pair(i, t):
    A = mmul(C[i], W[t])
    hits = []
    for sg in range(3):
        pre = minv(C[sg])
        for d in CANDS:
            M = mmul(mmul(pre, minv(theta(d))), A)
            if in_U19(M):
                hits.append((sg, d, M))
    return hits

def fmt_q(x):
    p, q = F(x[0]), F(x[1])
    if q == 0: return f"{p}"
    if p == 0: return f"{q}v"
    return f"{p} {'+' if q > 0 else '-'} {abs(q)}v"

def fmt_mat(M):
    return "[[" + ", ".join(fmt_q(e) for e in M[0]) + "], [" \
                + ", ".join(fmt_q(e) for e in M[1]) + "]]"

results = {}
print("=" * 78)
print("SEARCH: classRep i * etaRep t = d * classRep sigma * u,  u in U1(9)")
print("=" * 78)
for i in range(3):
    for t in range(3):
        hits = search_pair(i, t)
        if len(hits) != 1:
            print(f"(i,t)=({i},{t}): {len(hits)} hits -- "
                  + ("EXTEND SEARCH" if not hits else "NON-UNIQUE (bug?)"))
            for sg, d, M in hits:
                print(f"    sigma={sg}  d={tuple(map(str, d))}")
            continue
        sg, d, M = hits[0]
        results[(i, t)] = (sg, d, M)
        kind = "int " if all(x.denominator == 1 for x in d) else "half"
        print(f"i={i} t={t}:  sigma={sg}  d=({', '.join(str(x) for x in d)})"
              f"  [{kind}, nrd={nrd(d)}]")

assert len(results) == 9, "search incomplete -- extend candidate set"

# ---------- validation 2+3: sigma-table shape ----------
print("-" * 78)
sig = {k: v[0] for k, v in results.items()}
print("sigma-table (rows i, cols t):")
for i in range(3):
    print(f"    sigma({i},.) = ({sig[(i,0)]}, {sig[(i,1)]}, {sig[(i,2)]})")
diag_ok = all(sig[(i, t)] != i for i in range(3) for t in range(3))
print(f"sigma(i,t) != i for all nine: {diag_ok}   (trace U3 = 0)")
expected_rows = {0: Counter({1: 2, 2: 1}), 1: Counter({2: 2, 0: 1}),
                 2: Counter({0: 2, 1: 1})}
rows_ok = all(Counter(sig[(i, t)] for t in range(3)) == expected_rows[i]
              for i in range(3))
print(f"row multiplicities match block structure of (2.1.4)-(2.1.9): {rows_ok}")

# ---------- validation 4: the eps-matrix identification (B15) ----------
eps = {
    (0, 1): [("eps01M1", [[c_(0, F(3,10)),  c_(F(1,5), F(-1,10))],
                          [c_(1, F(-1,4)),  c_(F(-1,2), F(-3,4))]]),
             ("eps01M2", [[c_(F(-1,5), F(-1,10)), c_(F(1,5), F(1,10))],
                          [c_(-1, F(1,4)),        c_(0, F(1,4))]])],
    (0, 2): [("eps02M",  [[c_(F(-1,7), F(1,7)), c_(F(2,7))],
                          [c_(0),               c_(F(-1,4), F(-1,4))]])],
    (1, 0): [("eps10M",  [[c_(5, -5), c_(-4)],
                          [c_(0),     c_(2, 2)]])],
    (1, 2): [("eps12M1", [[c_(0, F(15,14)),      c_(F(2,7), F(-1,7))],
                          [c_(F(5,2), F(-5,8)),  c_(F(-1,2), F(-3,4))]]),
             ("eps12M2", [[c_(F(-5,7), F(-5,14)), c_(F(2,7), F(1,7))],
                          [c_(F(-5,2), F(5,8)),   c_(0, F(1,4))]])],
    (2, 0): [("eps20M1", [[c_(0, F(-21,2)), c_(-4, 2)],
                          [c_(-14, F(7,2)), c_(4, 6)]]),
             ("eps20M2", [[c_(7, F(7,2)),  c_(-4, -2)],
                          [c_(14, F(-7,2)), c_(0, -2)]])],
    (2, 1): [("eps21M",  [[c_(F(7,5), F(-7,5)), c_(F(-8,5))],
                          [c_(0),               c_(2, 2)]])],
}
# the thesis's misprinted a-entry, to confirm it does NOT occur
eps12M2_misprint = [[c_(F(-5,7), F(-15,14)), c_(F(2,7), F(1,7))],
                    [c_(F(-5,2), F(5,8)),    c_(0, F(1,4))]]

def key(M):
    return tuple((F(e[0]), F(e[1])) for row in M for e in row)

print("-" * 78)
print("B15 check: adjParams(theta(c_i^-1 d c_sigma)) vs the transcribed eps-matrices")
acting = {}          # (i,j) -> list of (t, adjParams matrix)
for (i, t), (sg, d, M) in sorted(results.items()):
    G = mmul(mmul(minv(C[i]), theta(d)), C[sg])
    acting.setdefault((i, sg), []).append((t, adjParams(G)))

all_exact = True
for (i, j), lst in sorted(acting.items()):
    got = Counter(key(A) for _, A in lst)
    want = Counter(key(E) for _, E in eps[(i, j)])
    exact = got == want
    all_exact &= exact
    names = ", ".join(n for n, _ in eps[(i, j)])
    print(f"block ({i},{j})  [{names}]  t's={sorted(t for t,_ in lst)}: "
          f"{'EXACT MATCH' if exact else 'MISMATCH'}")
    if not exact:
        for t, A in lst:
            # diagnose: scalar multiple?
            for n, E in eps[(i, j)]:
                nz = next(e for e in [A[0][0], A[0][1], A[1][0], A[1][1]]
                          if e != (0, 0))
                idx = [A[0][0], A[0][1], A[1][0], A[1][1]].index(nz)
                Eflat = [E[0][0], E[0][1], E[1][0], E[1][1]]
                s = mul(Eflat[idx], qinv(nz))
                if all(mul(s, a) == (F(e[0]), F(e[1]))
                       for a, e in zip([A[0][0], A[0][1], A[1][0], A[1][1]], Eflat)):
                    print(f"    t={t}: equals {n} up to scalar s = {fmt_q(s)}")
                    break
            else:
                print(f"    t={t}: adjParams = {fmt_mat(A)}")
print(f"ALL BLOCKS EXACT: {all_exact}")

mis = any(key(A) == key(eps12M2_misprint) for lst in acting.values() for _, A in lst)
print(f"misprinted eps12M2 (a = -15/14 nu - 5/7) occurs: {mis}  (expected False)")

# ---------- the handback format of PROGRESS.md sec.4 ----------
print("=" * 78)
print("CERTIFICATES (i, t, sigma(i,t), d(i,t) = (r, x, y, z) in basis 1,i,j,k):")
for (i, t), (sg, d, M) in sorted(results.items()):
    print(f"    {i}, {t}, {sg}, d = ({', '.join(str(x) for x in d)})")
print("-" * 78)
print("u(i,t) at 3, for the record (entries as p + q*nu, all 3-integral):")
for (i, t), (sg, d, M) in sorted(results.items()):
    print(f"    u({i},{t}) = {fmt_mat(M)}")

# ---------- emit Lean-ready literals for the B12 transcription ----------
def v3_int(n):
    n = abs(int(n)); v = 0
    if n == 0: return 99
    while n % 3 == 0: n //= 3; v += 1
    return v

def lin_data(e):
    """entry (p,q) = (x + y*nu)/m with x,y,m integers, m>0."""
    p, q = F(e[0]), F(e[1])
    from math import lcm
    m = lcm(p.denominator, q.denominator)
    return int(p*m), int(q*m), m

def lean_entry(e):
    p, q = F(e[0]), F(e[1])
    def rat(f, lead):
        f = abs(F(f)); s = f"{f.numerator}" if f.denominator == 1 else f"{f.numerator} / {f.denominator}"
        return s
    terms = []
    if q != 0:
        c = "" if abs(q) == 1 else rat(q, True) + " * "
        terms.append(("-" if q < 0 else "") + c + "ν₃")
    if p != 0:
        if terms: terms.append((" - " if p < 0 else " + ") + rat(p, False))
        else: terms.append(("-" if p < 0 else "") + rat(p, False))
    return "".join(terms) if terms else "0"

def lean_mat(M):
    return ("!![" + lean_entry(M[0][0]) + ", " + lean_entry(M[0][1]) + "; "
            + lean_entry(M[1][0]) + ", " + lean_entry(M[1][1]) + "]]")

CD = [1, 10, 28]
print("=" * 78)
print("LEAN LITERALS (B12 transcription aid)")
for (i, t), (sg, d, M) in sorted(results.items()):
    G = mmul(mmul(minv(C[i]), theta(d)), C[sg])
    detE = mdet(M); detG = mdet(G)
    assert detE[1] == 0 and detG[1] == 0
    print(f"-- (i,t)=({i},{t})  sigma={sg}  d=({', '.join(str(x) for x in d)})")
    print(f"--   E := toMatrix u = {lean_mat(M)}")
    print(f"--   det E = {detE[0]}  (= classDet {i}/classDet {sg})")
    for nm, e in [("a", M[0][0]), ("b", M[0][1]), ("c", M[1][0]), ("d", M[1][1])]:
        x, y, m = lin_data(e)
        s = x + 22*y
        print(f"--     {nm} = ({x} + {y}nu)/{m}; x+22y = {s} = 3^{v3_int(s)}*{s//3**v3_int(s) if s else 0}; v3(m)={v3_int(m)}")
    xa, ya, ma = lin_data(M[0][0])
    s1 = (xa - ma) + 22*ya
    print(f"--     a-1: num = ({xa - ma} + {ya}nu)/{ma}; x+22y = {s1} = 3^{v3_int(s1)}*{s1//3**v3_int(s1) if s1 else 0}")
    print(f"--   G := toMatrix (w_t u^-1) = {lean_mat(G)}")
    print(f"--   det G = {detG[0]}  (= 3 * classDet {sg}/classDet {i})")
    xg, yg, mg = lin_data(G[0][0]); sg1 = (xg - mg) + 22*yg
    print(f"--     G a-1: num = ({xg - mg} + {yg}nu)/{mg}; x+22y = {sg1} = 3^{v3_int(sg1)}*{sg1//3**v3_int(sg1) if sg1 else 0}")
    xgc, ygc, mgc = lin_data(G[1][0]); sgc = xgc + 22*ygc
    print(f"--     G c: num = ({xgc} + {ygc}nu)/{mgc}; x+22y = {sgc} = 3^{v3_int(sgc) if sgc else 0}*{sgc//3**max(v3_int(sgc),0) if sgc else 0}")
