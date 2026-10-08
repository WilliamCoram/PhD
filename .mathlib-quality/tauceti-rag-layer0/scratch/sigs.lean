import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples
open Lean Meta in
run_meta do
  let env ← getEnv
  let mut out : Array (String × String × String) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if n.isInternalDetail then continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      let isRAG := (`PhD.TauCeti.Code.RigidAnalyticGeometry).isPrefixOf m &&
        !(`PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted).isPrefixOf m
      if isRAG || m == `PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal then
        let s := n.toString
        if s.endsWith ".eq_1" || s.endsWith ".sizeOf_spec" || s.endsWith ".injEq" ||
            (s.splitOn ".").any (fun p => p.startsWith "_") || s.endsWith ".rec" ||
            s.endsWith ".recOn" || s.endsWith ".casesOn" || s.endsWith ".noConfusion" ||
            s.endsWith ".noConfusionType" || s.endsWith ".mk" || s.endsWith ".congr_simp" then
          continue
        let ty ← withOptions (fun o => o.setBool `pp.proofs false) do
          ppExpr ci.type
        let usesSorry := ci.value?.map (fun v => v.hasSorry) |>.getD false
        out := out.push (m.toString, s, s!"{if usesSorry then "[sorry] " else ""}{ty}")
    | none => pure ()
  let sorted := out.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  let mut txt := ""
  let mut cur := ""
  for (m, n, t) in sorted do
    if m != cur then
      txt := txt ++ s!"\n===== {m}\n"
      cur := m
    txt := txt ++ s!"{n} :\n    {t.replace "\n" "\n    "}\n"
  IO.FS.writeFile ".mathlib-quality/tauceti-rag-layer0/scratch/signatures.txt" txt
