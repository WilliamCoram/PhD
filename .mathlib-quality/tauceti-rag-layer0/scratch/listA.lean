import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples
open Lean in
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`PhD.TauCeti.Code.RigidAnalyticGeometry).isPrefixOf m ||
          m == `PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal then
        out := out.push s!"{n} {m}"
    | none => pure ()
  IO.FS.writeFile ".mathlib-quality/tauceti-rag-layer0/scratch/port_names.txt" (String.intercalate "\n" out.toList)
