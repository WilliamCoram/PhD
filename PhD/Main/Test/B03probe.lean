import PhD.Jacobs.U3.Setting
open Quaternion IsDedekindDomain NumberField QMF Jacobs.U3
open scoped TensorProduct

example : Module.finrank K₃ (Matrix (Fin 2) (Fin 2) K₃) = 4 := by
  rw [Module.finrank_matrix]
  simp
