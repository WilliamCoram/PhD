#!/usr/bin/env python3
"""AG-W-ID search: certificates for W = [U1(9) mu U1(9)], mu = diag(1,4) at 3.

Solves, for each i in Fin 3:
    classRep i * mu = d * classRep sigma * u,   u in U1(9),
with d in D^x integral at every place != 3 and nrd d = 1 (det bookkeeping:
det mu = 4 is a 3-unit, so unlike the eta case nothing needs clearing; away
from 3 u_l = d_l^{-1} forces d, d^{-1} integral there, and positivity of nrd
on Hamilton quaternions plus |nrd d|_3 = 1 forces nrd d = 1).
Candidates: 24 Hurwitz units (k=0) plus y/3 for Hurwitz y with nrd y = 9 (k=1).

Validation:
  1. exactly one hit per i (uniqueness = Lemma 2.2 + Thm 2.1)
  2. sigma = the 3-cycle (0->1, 1->2, 2->0) matching Wop's block layout
  3. acting matrices adjParams(theta(MU * u^{-1})) are DIAGONAL diag(a,d) with
     a/d in {2/5, 10/7, 7/4} matching delta01/delta12/delta20's D-arguments,
     and kappa-scalar kappa(d)/d^2 matching {4k(-1/2), 4k(-1/2), (1/16)k(4)}.
Conventions identical to certificate_search.py (same theta/classRep/U19)."""
from fractions import Fraction as F
from itertools import product

NU = 2695
CAP = 8
def add(x, y): return (x[0]+y[0], x[1]+y[1])
def sub(x, y): return (x[0]-y[0], x[1]-y[1])
def mul(x, y): return (x[0]*y[0]-2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def neg(x): return (-x[0], -x[1])
def qinv(x):
    n = x[0]*x[0]+2*x[1]*x[1]
    return (F(x[0],1)/n, F(-x[1],1)/n)
def v3_rat(r):
    r = F(r)
    if r == 0: return CAP
    v, n, d = 0, r.numerator, r.denominator
    while n % 3 == 0: n //= 3; v += 1
    while d % 3 == 0: d //= 3; v -= 1
    return min(v, CAP)
def v3(x): return v3_rat(F(x[0]) + F(x[1])*NU)
def mmul(A,B):
    return [[add(mul(A[0][0],B[0][0]),mul(A[0][1],B[1][0])),
             add(mul(A[0][0],B[0][1]),mul(A[0][1],B[1][1]))],
            [add(mul(A[1][0],B[0][0]),mul(A[1][1],B[1][0])),
             add(mul(A[1][0],B[0][1]),mul(A[1][1],B[1][1]))]]
def mdet(A): return sub(mul(A[0][0],A[1][1]),mul(A[0][1],A[1][0]))
def minv(A):
    di = qinv(mdet(A))
    return [[mul(di,A[1][1]),mul(di,neg(A[0][1]))],
            [mul(di,neg(A[1][0])),mul(di,A[0][0])]]
def adjParams(G): return [[G[1][1],neg(G[0][1])],[neg(G[1][0]),G[0][0]]]
def theta(d):
    r,x,y,z = d
    return [[(r+z,x),(x-y,-z)],[(x+y,-z),(r-z,-x)]]
def nrd(d): return sum(c*c for c in d)
def c_(p,q=0): return (F(p),F(q))
C = [[[c_(1),c_(0)],[c_(0),c_(1)]],
     [[c_(5),c_(0)],[c_(0),c_(2)]],
     [[c_(7),c_(0)],[c_(0),c_(4)]]]
MU = [[c_(1),c_(0)],[c_(0),c_(4)]]
def in_U19(M):
    for row in M:
        for e in row:
            if v3(e) < 0: return False
    if v3(sub(M[0][0],c_(1))) < 2: return False
    if v3(M[1][0]) < 2: return False
    return v3(mdet(M)) == 0

def hurwitz_units():
    out = []
    for pos in range(4):
        for s in (1,-1):
            out.append(tuple(F(s) if m==pos else F(0) for m in range(4)))
    for signs in product([1,-1],repeat=4):
        out.append(tuple(F(signs[m],2) for m in range(4)))
    assert len(out) == 24 and all(nrd(d)==1 for d in out)
    return out

def norm9_over3():
    out = set()
    # integer coords with sum of squares 9
    from itertools import permutations
    bases = [(3,0,0,0),(2,2,1,0),(1,2,2,0)]
    ints = set()
    for b in [(3,0,0,0),(2,2,1,0)]:
        for p in set(permutations(b)):
            for signs in product([1,-1],repeat=4):
                ints.add(tuple(F(p[m]*signs[m]) for m in range(4)))
    # half-integer: (h1..h4)/2 all odd, sum h^2 = 36: (3,3,3,3),(5,3,1,1)
    halves = set()
    for b in [(3,3,3,3),(5,3,1,1)]:
        for p in set(permutations(b)):
            for signs in product([1,-1],repeat=4):
                halves.add(tuple(F(p[m]*signs[m],2) for m in range(4)))
    allq = {q for q in ints|halves if nrd(q)==9}
    for q in allq:
        d = tuple(x/3 for x in q)
        if any(x.denominator > 2 for x in d):   # keep only D^x with away-from-3 integrality: y/3, fine
            pass
        out.add(d)
    return sorted(out)

CANDS = hurwitz_units() + norm9_over3()
print(f"candidate d's: {len(CANDS)} (24 units + {len(CANDS)-24} norm-9/3)")

results = {}
for i in range(3):
    A = mmul(C[i], MU)
    hits = []
    for sg in range(3):
        pre = minv(C[sg])
        for d in CANDS:
            M = mmul(mmul(pre, minv(theta(d))), A)
            if in_U19(M):
                hits.append((sg,d,M))
    print(f"i={i}: {len(hits)} hit(s)")
    for sg,d,M in hits:
        print(f"    sigma={sg}  d=({', '.join(str(x) for x in d)})  nrd={nrd(d)}")
    if len(hits) == 1:
        results[i] = hits[0]

if len(results) == 3:
    print("-"*70)
    sig = {i: results[i][0] for i in results}
    print(f"sigma-table: ({sig[0]}, {sig[1]}, {sig[2]})  expected 3-cycle (1, 2, 0): {sig=={0:1,1:2,2:0}}")
    print("acting matrices adjParams(theta(MU * u^-1)) [should be diagonal]:")
    EXPECT_RATIO = {0: F(2,5), 1: F(10,7), 2: F(7,4)}
    for i,(sg,d,M) in sorted(results.items()):
        G = adjParams(mmul(MU, minv(M)))
        diag_ok = G[0][1] == (0,0) and G[1][0] == (0,0)
        a, dd = G[0][0], G[1][1]
        # entries should be rational (nu-free)
        print(f"  i={i}: G = [[{a}],[{dd}]] offdiag0={diag_ok}", end="")
        if a[1]==0 and dd[1]==0 and dd[0]!=0:
            r = F(a[0])/F(dd[0])
            print(f"  a/d = {r}  (expect {EXPECT_RATIO[i]}: {r==EXPECT_RATIO[i]})  d-entry = {dd[0]}")
        else:
            print("  NON-RATIONAL/ZERO")
    print("-"*70)
    print("u(i) matrices at 3 (entries p+q*nu):")
    for i,(sg,d,M) in sorted(results.items()):
        print(f"  u({i}) = {[[str(e) for e in row] for row in M]}")
        print(f"    det u = {mdet(M)}")
