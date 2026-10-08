# usage: python3 axioms.py <Module> ; prints a Lean file printing axioms of every public theorem/def in it
import re,sys
mod=sys.argv[1]
p='PhD/TauCeti/Code/PadicFunctionalAnalysis/%s.lean'%mod
L=open(p).read().split('\n')
ns=[]; out=[]
for l in L:
    m=re.match(r'^namespace (\S+)',l)
    if m: ns.append(m.group(1)); continue
    m=re.match(r'^end (\S+)',l)
    if m and ns and ns[-1]==m.group(1): ns.pop(); continue
    m=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance)\s+([^\s:[({]+)',l)
    if m:
        n=m.group(1)
        out.append('.'.join(ns+[n]))
print('import PhD.TauCeti.Code.PadicFunctionalAnalysis.%s'%mod)
for n in out: print('#print axioms %s'%n)
