import Mathlib
open Lean in
run_cmd do
  let env ← getEnv
  let txt ← IO.FS.readFile ".mathlib-quality/tauceti-rag-layer0/scratch/port_names.txt"
  for line in txt.splitOn "\n" do
    match line.splitOn " " with
    | [n, m] =>
      let name := n.toName
      if env.contains name then
        match env.getModuleIdxFor? name with
        | some idx => IO.println s!"CLASH {n} (port: {m}) (mathlib: {env.header.moduleNames[idx.toNat]!})"
        | none => pure ()
    | _ => pure ()
