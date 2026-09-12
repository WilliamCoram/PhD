#!/usr/bin/env python3
"""Fork AG-W-ID search: certificates for W = [U1(9) mu U1(9)], mu = diag(1,4) at 3,
in the JacobsSlash (thesis/right-handed, d-form) conventions.

RIGHT-COSET factorisation (the S11 heckeOperatorSlash_apply_rep shape), for each i:

    classRep i * mu^{-1} = d * classRep sigma * u,   u in U1(9)-fork (d-form),

with mu the THESIS'S OWN diag(1,4) — the fork handedness flip: in the fork's d-form
U1(9) the trap element is diag(4,1) (d-entry 1 => lies in U1(9) => trivial coset),
while diag(1,4) has v3(4-1) = 1 < 2 so it is NOT in U1(9).  (Mirror of the left
oracle's finding, where the roles were exactly reversed.)

d-candidates: nrd d = 1 bookkeeping (det(c_i mu^{-1}) is a 3-unit; away from 3
u_l = d_l^{-1} forces d integral at every place != 3): 24 Hurwitz units plus y/3
for Hurwitz y with nrd y = 9 (312 candidates, as in the left oracle).

Validation:
  0. handedness trap: diag(1,4) not in U19-fork; diag(4,1) in U19-fork.
  1. exactly one hit per i (uniqueness = Lemma 2.2 + Thm 2.1).
  2. sigma_W = the 3-cycle (1, 2, 0) (same cycle as the left, NOT inverted: the
     acting product C_sigma^{-1} theta(d)^{-1} C_i cancels mu entirely).
  3. acting matrices theta3(u(i) * mu) = C_sigma^{-1} * theta(d)^{-1} * C_i are
     DIAGONAL diag(a,d), rational (nu-free), with a/d in {2/5, 10/7, 7/4}
     matching delta01/delta12/delta20's D-arguments.
  4. TWIST VERDICT: acting (a,d) equals the THESIS pairs
     (-1/5,-1/2), (-5/7,-1/2), (7,4) EXACTLY (twist-free, the AG-B outcome)
     or differs by the classDet coboundary (the left outcome).

RESULTS (computed 2026-08-06; run: python3 certificate_search_w.py, < 5 s;
all validations passed, unique hit per class over 312 deduped candidates):

  0. trap check: diag(1,4) NOT in U19-fork (v3(4-1)=1 < 2); diag(4,1) IS in
     U19-fork -- the fork handedness flip confirmed.
  1. sigma_W = (1, 2, 0)   (the SAME 3-cycle as the left, not inverted: the
     acting product cancels mu entirely, so the cycle direction survives the
     mu -> mu^{-1} coset flip).
  2. d_W = (-1, -1, +1)    (central signs; nrd = 1).
  3. u(i) 3-components (rational DIAGONAL, nu-free; d-form + det checks pass):
        u(0) = diag(-1/5, -1/8)    det = 1/40   (v3 = 0)
        u(1) = diag(-5/7, -1/8)    det = 5/56   (v3 = 0)
        u(2) = diag(7, 1)          det = 7      (v3 = 0)
  4. acting matrices theta3(u(i) * mu) = C_sigma^{-1} theta(d)^{-1} C_i:
        i=0: diag(-1/5, -1/2)  -> delta01 thesis pair, EXACT
        i=1: diag(-5/7, -1/2)  -> delta12 thesis pair, EXACT
        i=2: diag(7, 4)        -> delta20 thesis pair, EXACT
  5. **TWIST VERDICT: TWIST-FREE.**  The acting matrices are the thesis's
     delta-data ON THE NOSE -- the left library's classWeight coboundary
     (4k(-1/2), 4k(-1/2), (1/16)k(4)) vanishes identically in the fork
     orientation, exactly as it did for the AG-B eps-identification.
     BINDING for W06: the identification statement carries NO scalar
     (kappaSlashWide(acting i) = deltaOf i exactly).

Conventions identical to certificate_search.py (same theta/classRep/in_U19_fork).
Feeds: sigmaTableW / dTableW / uTableW in PhD/JacobsSlash/U3/7_DiamondHecke.lean
(tickets W05-W06) and the twist verdict binding W06's statement form.
"""
from fractions import Fraction as F
from itertools import product, permutations

NU = 2695
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
MU = [[c_(1), c_(0)], [c_(0), c_(4)]]
MUinv = minv(MU)
TRAP = [[c_(4), c_(0)], [c_(0), c_(1)]]

def in_U19_fork(M):
    """entries 3-integral, M11 == 1 mod 9, M10 == 0 mod 9, det a 3-unit."""
    for row in M:
        for e in row:
            if v3(e) < 0: return False
    if v3(sub(M[1][1], c_(1))) < 2: return False
    if v3(M[1][0]) < 2: return False
    return v3(mdet(M)) == 0

def hurwitz_units():
    out = []
    for pos in range(4):
        for s in (1, -1):
            out.append(tuple(F(s) if m == pos else F(0) for m in range(4)))
    for signs in product([1, -1], repeat=4):
        out.append(tuple(F(signs[m], 2) for m in range(4)))
    assert len(out) == 24 and all(nrd(d) == 1 for d in out)
    return out

def norm9_over3():
    out = set()
    ints = set()
    for b in [(3, 0, 0, 0), (2, 2, 1, 0)]:
        for p in set(permutations(b)):
            for signs in product([1, -1], repeat=4):
                ints.add(tuple(F(p[m]*signs[m]) for m in range(4)))
    halves = set()
    for b in [(3, 3, 3, 3), (5, 3, 1, 1)]:
        for p in set(permutations(b)):
            for signs in product([1, -1], repeat=4):
                halves.add(tuple(F(p[m]*signs[m], 2) for m in range(4)))
    allq = {q for q in ints | halves if nrd(q) == 9}
    for q in allq:
        out.add(tuple(x/3 for x in q))
    return sorted(out)

CANDS = list(dict.fromkeys(hurwitz_units() + norm9_over3()))
print(f"candidate d's: {len(CANDS)} (24 units + norm-9/3, deduped — the norm-9 set "
      f"contains 3*(unit)/3 overlaps)")

# Validation 0: the handedness trap.
print(f"trap check: diag(1,4) in U19-fork = {in_U19_fork(MU)} (expect False); "
      f"diag(4,1) in U19-fork = {in_U19_fork(TRAP)} (expect True)")

results = {}
for i in range(3):
    A = mmul(C[i], MUinv)
    hits = []
    for sg in range(3):
        pre = minv(C[sg])
        for d in CANDS:
            M = mmul(mmul(pre, minv(theta(d))), A)
            if in_U19_fork(M):
                hits.append((sg, d, M))
    print(f"i={i}: {len(hits)} hit(s)")
    for sg, d, M in hits:
        print(f"    sigma={sg}  d=({', '.join(str(x) for x in d)})  nrd={nrd(d)}")
    if len(hits) == 1:
        results[i] = hits[0]

if len(results) == 3:
    print("-" * 70)
    sig = {i: results[i][0] for i in results}
    print(f"sigma_W-table: ({sig[0]}, {sig[1]}, {sig[2]})  "
          f"3-cycle (1,2,0): {sig == {0: 1, 1: 2, 2: 0}}")
    print("acting matrices theta3(u(i) * mu)  [= C_sigma^-1 theta(d)^-1 C_i; "
          "should be diagonal, rational]:")
    DELTA = {F(2, 5): ("delta01", (F(-1, 5), F(-1, 2))),
             F(10, 7): ("delta12", (F(-5, 7), F(-1, 2))),
             F(7, 4): ("delta20", (F(7), F(4)))}
    twist_free = True
    for i, (sg, d, M) in sorted(results.items()):
        G = mmul(M, MU)                       # acting = u * mu at 3, right-handed
        Galt = mmul(mmul(minv(C[sg]), minv(theta(d))), C[i])
        assert G == Galt, "mu-cancellation identity failed"
        diag_ok = G[0][1] == (0, 0) and G[1][0] == (0, 0)
        a, dd = G[0][0], G[1][1]
        line = f"  i={i}: G = diag({a}, {dd})  offdiag0={diag_ok}"
        if a[1] == 0 and dd[1] == 0 and dd[0] != 0:
            r = F(a[0]) / F(dd[0])
            name, pair = DELTA.get(r, ("NO-MATCH", None))
            exact = pair is not None and (a[0], dd[0]) == pair
            twist_free = twist_free and exact
            line += (f"  a/d = {r} -> {name}; thesis pair {pair}; "
                     f"EXACT = {exact}")
        else:
            line += "  NON-RATIONAL/ZERO"
            twist_free = False
        print(line)
    print("-" * 70)
    print(f"TWIST VERDICT: {'TWIST-FREE (acting = thesis delta data ON THE NOSE)' if twist_free else 'COBOUNDARY PRESENT (record scalars above)'}")
    print("-" * 70)
    print("u(i) matrices at 3 (entries p + q*nu)  [for W05 toMatrix literals]:")
    for i, (sg, d, M) in sorted(results.items()):
        print(f"  u({i}) = {[[str(e) for e in row] for row in M]}")
        print(f"    det u = {mdet(M)}   v3(det) = {v3(mdet(M))}")
    print("  (d-form checks: v3(u11 - 1) >= 2 and v3(u10) >= 2 verified by in_U19_fork)")
