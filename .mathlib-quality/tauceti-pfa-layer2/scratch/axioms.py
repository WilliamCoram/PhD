#!/usr/bin/env python3
"""Print the axioms of every named declaration of an Operator/*.lean module.
Usage: axioms.py <Module> (e.g. Norm). Reports declarations with non-standard axioms."""
import re, sys, subprocess, pathlib
ROOT = pathlib.Path("/Users/nkw24xru/Desktop/Lean/PhD")
mod = sys.argv[1]
src = (ROOT / f"PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/{mod}.lean").read_text().split("\n")
ns = []
names = []
incomment = False
for l in src:
    if incomment:
        if "-/" in l: incomment = False
        continue
    if l.lstrip().startswith("/-") and "-/" not in l:
        incomment = True
        continue
    m = re.match(r"^namespace\s+(\S+)", l)
    if m: ns.append(m.group(1)); continue
    m = re.match(r"^end\s+(\S+)", l)
    if m and ns and ns[-1] == m.group(1): ns.pop(); continue
    m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|scoped|protected|private|nonrec)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)", l)
    if m and "private " not in l.split("theorem")[0].split("def")[0]:
        n = m.group(1)
        if n.startswith("_root_."): names.append(n[len("_root_."):])
        else: names.append(".".join(ns + [n]) if ns else n)
out = ROOT / ".mathlib-quality/tauceti-pfa-layer1/scratch/ax_tmp.lean"
out.write_text(f"import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.{mod}\n" +
               "\n".join(f"#print axioms {n}" for n in names) + "\n")
r = subprocess.run(["lake", "env", "lean", str(out)], cwd=ROOT, capture_output=True, text=True)
txt = r.stdout + r.stderr
bad = [b for b in re.split(r"\n(?='|\S+\.lean:)", txt) if ("sorryAx" in b or "error" in b)]
print(f"{len(names)} declarations checked")
for b in bad: print("PROBLEM:", b[:400])
std = {"propext", "Classical.choice", "Quot.sound"}
others = set(re.findall(r"\b([A-Za-z_][\w.]*)\b", " ".join(re.findall(r"\[([^\]]*)\]", txt)))) - std
if others: print("non-standard axioms seen:", sorted(others))
if not bad and not others: print("all standard (propext, Classical.choice, Quot.sound)")
