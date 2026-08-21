#!/usr/bin/env python3
"""Thesis-orientation certificate search for the JacobsSlash fork ([Jacobs, Lemmas
2.4/2.5 + §B.1], RIGHT-handed convention — the thesis's own factorisation problem).

Solves, for each (i,t) in Fin 3 x Fin 3:

    classRep i * (etaRep t)^{-1} = d * classRep sigma * u,   u in U1(9)-fork,

where etaRep t has 3-component V_t = [[3,0],[9t,1]] (the thesis's matrices), the
fork's U1(9) is the d-form (entries 3-integral, M11 == 1 mod 9, M10 == 0 mod 9,
det a 3-unit), u := (d * classRep sigma)^{-1} * classRep i * (etaRep t)^{-1} is
defined by the equation, and d = h/3 with h a Hurwitz quaternion of reduced norm 3
(so nrd(d) = 1/3, forced by det bookkeeping: det(c_i v_t^{-1}) = CD_i/3).

Relation to the left library's search (PhD/Jacobs/U3/certificate_search.py): the
left factorises classRep i * etaRep-left t with a-form U1(9); its d's are 3 * (the
d's here) — "d(0,0) = 3 * d_thesis" in its own cross-check notes.

RESULTS (computed 2026-08-06; unique hit per pair; all validations passed):

    i, t, sigma(i,t), d(i,t) = (r, x, y, z)
    0, 0, 2, (-1/3, -1/3, 1/3, 0)
    0, 1, 1, (-1/6, -1/2, -1/6, -1/6)
    0, 2, 1, (-1/6, 1/6, 1/2, 1/6)
    1, 0, 0, (1/3, 1/3, -1/3, 0)
    1, 1, 2, (-1/6, -1/2, -1/6, -1/6)
    1, 2, 2, (-1/6, 1/6, 1/2, 1/6)
    2, 0, 1, (1/3, 1/3, -1/3, 0)
    2, 1, 0, (1/6, 1/2, 1/6, 1/6)
    2, 2, 0, (1/6, -1/6, -1/2, -1/6)

sigma-table = (2,1,1), (0,2,2), (1,0,0) — the thesis's table, same as the left's.

**THE HEADLINE (P06 acceptance criterion, oracle level): the fork's
eps-identification is TWIST-FREE.**  The acting matrix of the S11 sum,

    G' := theta3-params of (u(i,t) * etaRep t) = C_sigma^{-1} * theta(d)^{-1} * C_i,

equals the transcribed eps_{i,sigma} matrices of U3Data EXACTLY for all nine
summands — NO adjParams, NO classWeight coboundary (the left library's B15
`kappa(s) s^{-2}` factor vanishes identically in the thesis orientation).
Hence the fork's sum_weightGenFun_eq_h carries NO scalar, and
"the matrix of U3 has the form A = (eps_{i,j})" [Jac p. 28] will hold on the nose.

Feeds: sigmaTable / dTable / uTable in PhD/JacobsSlash/U3/5_Factorisations.lean.
Run:  python3 certificate_search.py   (pure stdlib, < 5 s)
"""
from fractions import Fraction as F
from itertools import product
from collections import Counter

NU = 2695          # nu mod 3^10
CAP = 8

def add(x, y): return (x[0] + y[0], x[1] + y[1])
def sub(x, y): return (x[0] - y[0], x[1] - y[1])
def mul(x, y): return (x[0]*y[0] - 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def neg(x): return (-x[0], -x[1])
def qinv(x):
    n = x[0]*x[0] + 2*x[1]*x[1]
    return (F(x[0], 1)/n, F(-x[1], 1)/n)

def v3_rat(r):
    r = F(r)
    if r == 0: return CAP
    v, n, d = 0, r.numerator, r.denominator
    while n % 3 == 0: n //= 3; v += 1
    while d % 3 == 0: d //= 3; v -= 1
    return min(v, CAP)

def v3(x): return v3_rat(F(x[0]) + F(x[1]) * NU)

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

def theta(d):
    r, x, y, z = d
    return [[(r + z, x), (x - y, -z)],
            [(x + y, -z), (r - z, -x)]]

def nrd(d): return sum(c*c for c in d)
def c_(p, q=0): return (F(p), F(q))

C = [[[c_(1), c_(0)], [c_(0), c_(1)]],
     [[c_(5), c_(0)], [c_(0), c_(2)]],
     [[c_(7), c_(0)], [c_(0), c_(4)]]]
# the fork's etaRep 3-components: V_t = [[3,0],[9t,1]] (thesis matrices)
V = [[[c_(3), c_(0)], [c_(9*t), c_(1)]] for t in range(3)]

def in_U19_fork(M):
    """entries 3-integral, M11 == 1 mod 9, M10 == 0 mod 9, det a 3-unit."""
    for row in M:
        for e in row:
            if v3(e) < 0: return False
    if v3(sub(M[1][1], c_(1))) < 2: return False
    if v3(M[1][0]) < 2: return False
    return v3(mdet(M)) == 0

def hurwitz_norm3():
    out = []
    for pos0 in range(4):
        for signs in product([1, -1], repeat=3):
            coords, k = [], 0
            for m in range(4):
                if m == pos0: coords.append(F(0))
                else: coords.append(F(signs[k])); k += 1
            out.append(tuple(coords))
    for pos3 in range(4):
        for signs in product([1, -1], repeat=4):
            out.append(tuple(F(3 if m == pos3 else 1) * signs[m] / 2 for m in range(4)))
    assert len(out) == 96 and all(nrd(d) == 3 for d in out)
    return out

CANDS = [tuple(x/3 for x in h) for h in hurwitz_norm3()]   # d = h/3, nrd(d) = 1/3

results = {}
print("=" * 78)
print("SEARCH: classRep i * (etaRep t)^-1 = d * classRep sigma * u,  u in U1(9)-fork")
print("=" * 78)
for i in range(3):
    for t in range(3):
        A = mmul(C[i], minv(V[t]))
        hits = []
        for sg in range(3):
            pre = minv(C[sg])
            for d in CANDS:
                M = mmul(mmul(pre, minv(theta(d))), A)
                if in_U19_fork(M):
                    hits.append((sg, d, M))
        assert len(hits) == 1, f"(i,t)=({i},{t}): {len(hits)} hits"
        sg, d, M = hits[0]
        results[(i, t)] = (sg, d, M)
        print(f"i={i} t={t}:  sigma={sg}  d=({', '.join(str(x) for x in d)})  nrd={nrd(d)}")

sig = {k: v[0] for k, v in results.items()}
print("-" * 78)
print("sigma-table:", [[sig[(i, t)] for t in range(3)] for i in range(3)])
assert all(sig[(i, t)] != i for i in range(3) for t in range(3))
print("sigma(i,t) != i: True   (trace U3 = 0)")

# the fork eps-identification: G' = C_sigma^-1 theta(d)^-1 C_i vs eps (NO adjParams)
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
def key(M): return tuple((F(e[0]), F(e[1])) for row in M for e in row)
acting = {}
for (i, t), (sg, d, M) in sorted(results.items()):
    Gp = mmul(mmul(minv(C[sg]), minv(theta(d))), C[i])
    acting.setdefault((i, sg), []).append((t, Gp))
all_exact = True
print("-" * 78)
print("FORK B15: G' = C_sigma^-1 theta(d)^-1 C_i  vs the transcribed eps (no adjParams)")
for (i, j), lst in sorted(acting.items()):
    got = Counter(key(A) for _, A in lst)
    want = Counter(key(E) for _, E in eps[(i, j)])
    exact = got == want
    all_exact &= exact
    print(f"block ({i},{j})  t's={sorted(t for t, _ in lst)}: "
          f"{'EXACT MATCH' if exact else 'MISMATCH'}")
assert all_exact
print("ALL BLOCKS EXACT — twist-free identification (no classWeight coboundary).")
print("-" * 78)
print("u(i,t) 3-components (entries p + q*nu):")
for (i, t), (sg, d, M) in sorted(results.items()):
    print(f"    u({i},{t}) =", [[f"{e[0]} + {e[1]}v" for e in row] for row in M],
          " det:", mdet(M))

# ---------- emit Lean-ready literals for the 5_Factorisations transcription ----------
def v3_int(n):
    n = abs(int(n)); v = 0
    if n == 0: return 99
    while n % 3 == 0: n //= 3; v += 1
    return v

def lin_data(e):
    p, q = F(e[0]), F(e[1])
    from math import lcm
    m = lcm(p.denominator, q.denominator)
    return int(p*m), int(q*m), m

def lean_entry_frac(e):
    x, y, m = lin_data(e)
    return f"((({x} : ℤ) : K₃) + (({y} : ℤ) : K₃) * ν₃) / (({m} : ℕ) : K₃)"

print("=" * 78)
print("LEAN LITERALS (5_Factorisations transcription aid; fork orientation)")
for (i, t), (sg, d, M) in sorted(results.items()):
    h = tuple(3*x for x in d)      # the Hurwitz quaternion, d = h/3
    Gp = mmul(mmul(minv(C[sg]), minv(theta(d))), C[i])
    detE = mdet(M); detG = mdet(Gp)
    print(f"-- (i,t)=({i},{t})  sigma={sg}  d = h/3, h = ({', '.join(str(x) for x in h)})")
    print(f"--   E := toMatrix (uCand {i} {t}) entries (X+Y*nu)/M:")
    for nm, e in [("a", M[0][0]), ("b", M[0][1]), ("c", M[1][0]), ("dd", M[1][1])]:
        x, y, m = lin_data(e)
        sxy = x + 22*y
        print(f"--     {nm} = ({x} + {y}nu)/{m}; x+22y = {sxy} = 3^{v3_int(sxy)}*rest; v3(m) = {v3_int(m)}")
    xd, yd, md = lin_data(M[1][1])
    s1 = (xd - md) + 22*yd
    print(f"--     dd-1: ({xd - md} + {yd}nu)/{md}; x+22y = {s1} = 3^{v3_int(s1)}*rest")
    print(f"--   det E = {detE[0]}")
    print(f"--   E-literal: !![{lean_entry_frac(M[0][0])}, {lean_entry_frac(M[0][1])}; "
          f"{lean_entry_frac(M[1][0])}, {lean_entry_frac(M[1][1])}]]")
    print(f"--   G' := toMatrix params of (u * etaRep {t}) = C_sigma^-1 theta(d)^-1 C_i; det = {detG[0]}")
