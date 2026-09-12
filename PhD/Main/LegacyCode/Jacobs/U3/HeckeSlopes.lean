/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Fredholm
import PhD.Jacobs.BaseChange
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The eigenblock factorisation and slopes of `det(1 − T·U₃)`

The extension-field endgame (board `.mathlib-quality/jacobs-endgame/`).  `K₃ = ℚ₃`
contains no primitive cube root of unity (`x² + x + 1 ≡ (x+2)² mod 3`, discriminant of
odd valuation), so the eigenblock factorisation of [Jacobs, (2.1.14) + Lemma 1.15] —
whose blocks `M₁,₁, M₂,₂, M₃,₃` carry `ω`-scalars — lives over an extension.  This file
states it in maximal generality and then witnesses it concretely:

* **Abstract layer** — for any complete ultrametric `NontriviallyNormedField L`, any
  isometric embedding `f : K₃ →+* L` and any `ω ∈ L` with `ω² + ω + 1 = 0`:
  `map_charPowerSeriesU3` (base change of `det(1 − T·U₃)` to the transcribed matrix over
  `L`) and `charPowerSeriesU3_factorisation` — the thesis chain

    `det(1 − T·U₃) = det(1 − T·M₁,₁) · det(1 − T·M₂,₂) · det(1 − T·M₃,₃)`

  as a statement about the genuine Hecke operator.  The slope reading of the middle
  factor is the (proved) `Jacobs.unitSlope_newtonPolygon₀OfPowerSeries_M22op` at `L`:
  its Newton polygon has unit slopes `1/2, 3/2, 5/2, …` — [Jacobs, Cor 2.16] about `U₃`.
  (A "Newton polygon of a product" merge theorem is deliberately NOT stated: the thesis
  proves no such result, stopping at the per-factor statement.)

* **Concrete layer** — the minimal admissible extension `L₃ := K₃(ζ₃) = ℚ₃(√−3)`,
  realised as `CyclotomicField 3 K₃` with the spectral norm
  (`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`; the instances are `letI`-style by
  mathlib design and are installed here on the local wrapper `L₃`).  The embedding
  `algebraMap K₃ L₃` is isometric (`norm_algebraMap'`), `ω₃ := ζ₃` satisfies the cube
  relation, and `charPowerSeriesU3_factorisation_L₃` instantiates the abstract layer.

`hcn : HClassNumberOne` appears nowhere: the factorisation is about the certificate
block operator (unconditional); `hcn` is only needed to read the model as *all* of
`L(U₁(9), A₃)` (`kappaFormsModelEquiv`).
-/

open TateFredholm

namespace Jacobs.U3

section Abstract

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharZero L]

omit [IsUltrametricDist L] [CompleteSpace L] [CharZero L] in
/-- The residue-characteristic hypothesis transports along an isometric embedding:
`(3 : L) = f (3 : K₃)` has the same norm. -/
theorem norm_three_lt_one_of_isometry (f : K₃ →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    ‖(3 : L)‖ < 1 := by
  rw [← map_ofNat f 3, hf]
  exact norm_three_lt_one

omit [IsUltrametricDist L] [CompleteSpace L] [CharZero L] in
/-- The weight disc transports along an isometric embedding. -/
theorem norm_map_weight_lt_one (f : K₃ →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) {t : K₃}
    (ht : ‖t‖ < 1) : ‖f t‖ < 1 :=
  (hf t).trans_lt ht

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The location `ν ≡ 2695 mod 3¹⁰` transports along an isometric embedding. -/
theorem map_ν₃_near (f : K₃ →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    ‖f ν₃ - 2695‖ ≤ ‖(3 : L)‖ ^ 10 := by
  calc ‖f ν₃ - 2695‖ = ‖f (ν₃ - 2695)‖ := by rw [map_sub, map_ofNat]
    _ = ‖ν₃ - 2695‖ := hf _
    _ ≤ ‖(3 : K₃)‖ ^ 10 := ν₃_near
    _ = ‖(3 : L)‖ ^ 10 := by rw [← map_ofNat f 3, hf]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The defining identity `ν² = −2` transports along any ring homomorphism. -/
theorem map_sq_ν₃ (f : K₃ →+* L) : f ν₃ ^ 2 = -2 := by
  rw [← map_pow, sq_ν₃, map_neg, map_ofNat]

/-- **Base change of `det(1 − T·U₃)`**: along an isometric embedding `f : K₃ →+* L`, the
Fredholm determinant of `U₃` is computed by the transcribed Jacobs matrix over `L` at
the image parameters `(f t, f ν₃)`.  Chain: `charPowerSeriesU3_eq_U3MatrixOp` (the
`K₃`-headline), `TateFredholm.charPowerSeries_map` (matrix-level base change,
`isCompactoid_U3MatrixOp` supplying summability) and the `map_h` layer of
`PhD.Jacobs.BaseChange` (the six generating functions map entrywise). -/
theorem map_charPowerSeriesU3 (f : K₃ →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t : K₃)
    (ht : ‖t‖ < 1) :
    PowerSeries.map f (charPowerSeriesU3 t ht)
      = charPowerSeries (Jacobs.U3MatrixOp (norm_three_lt_one_of_isometry f hf)
          (norm_map_weight_lt_one f hf ht) (map_ν₃_near f hf)) := by
  rw [charPowerSeriesU3_eq_U3MatrixOp]
  refine (TateFredholm.charPowerSeries_map f hf
    (Jacobs.isCompactoid_U3MatrixOp norm_three_lt_one ht ν₃_near) fun ji bi => ?_).symm
  obtain ⟨a, j⟩ := ji
  obtain ⟨b, i⟩ := bi
  simp only [Jacobs.U3MatrixOp, _root_.TateFredholm.matrixCoeff_blockOp]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact (map_zero f).symm
  · rw [Jacobs.matrixCoeff_epsOp01, Jacobs.matrixCoeff_epsOp01, ← Jacobs.map_h01 f hf,
      MvPowerSeries.coeff_map]
  · rw [Jacobs.matrixCoeff_epsOp02, Jacobs.matrixCoeff_epsOp02, ← Jacobs.map_h02 f hf,
      MvPowerSeries.coeff_map]
  · rw [Jacobs.matrixCoeff_epsOp10, Jacobs.matrixCoeff_epsOp10, ← Jacobs.map_h10 f hf,
      MvPowerSeries.coeff_map]
  · exact (map_zero f).symm
  · rw [Jacobs.matrixCoeff_epsOp12, Jacobs.matrixCoeff_epsOp12, ← Jacobs.map_h12 f hf,
      MvPowerSeries.coeff_map]
  · rw [Jacobs.matrixCoeff_epsOp20, Jacobs.matrixCoeff_epsOp20, ← Jacobs.map_h20 f hf,
      MvPowerSeries.coeff_map]
  · rw [Jacobs.matrixCoeff_epsOp21, Jacobs.matrixCoeff_epsOp21, ← Jacobs.map_h21 f hf,
      MvPowerSeries.coeff_map]
  · exact (map_zero f).symm

/-- **The eigenblock factorisation of `det(1 − T·U₃)`** ([Jacobs, (2.1.14) + Lemma 1.15],
now about the genuine Hecke operator): over any complete ultrametric extension containing
a primitive cube root of unity,

  `det(1 − T·U₃) = det(1 − T·M₁,₁) · det(1 − T·M₂,₂) · det(1 − T·M₃,₃)`.

The middle factor's Newton polygon has unit slopes `1/2, 3/2, 5/2, …` — the proved
`Jacobs.unitSlope_newtonPolygon₀OfPowerSeries_M22op` at `L` — so this theorem is
[Jacobs, Cor 2.16] as a statement about `U₃`.  Assembly: `map_charPowerSeriesU3` +
`Jacobs.charPowerSeries_U3MatrixOp` (the AG-W milestone) at `L`. -/
theorem charPowerSeriesU3_factorisation (f : K₃ →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (ω : L) (hω : ω ^ 2 + ω + 1 = 0) (t : K₃) (ht : ‖t‖ < 1) :
    PowerSeries.map f (charPowerSeriesU3 t ht)
      = charPowerSeries (Jacobs.M11op (norm_three_lt_one_of_isometry f hf)
            (norm_map_weight_lt_one f hf ht) (map_ν₃_near f hf)) *
          (charPowerSeries (Jacobs.M22op ω hω (norm_three_lt_one_of_isometry f hf)
              (norm_map_weight_lt_one f hf ht) (map_ν₃_near f hf)) *
            charPowerSeries (Jacobs.M33op ω hω (norm_three_lt_one_of_isometry f hf)
              (norm_map_weight_lt_one f hf ht) (map_ν₃_near f hf))) :=
  (map_charPowerSeriesU3 f hf t ht).trans <|
    Jacobs.charPowerSeries_U3MatrixOp (ω := ω) (hω := hω)
      (h3 := norm_three_lt_one_of_isometry f hf) (ht := norm_map_weight_lt_one f hf ht)
      (hνc := map_ν₃_near f hf)

end Abstract

noncomputable section Cyclotomic

/-- The minimal admissible coefficient extension `L₃ = K₃(ζ₃) = ℚ₃(√−3)`, as the
cyclotomic field `CyclotomicField 3 K₃` wrapped in a local definition so that the
spectral-norm structures below can be installed as honest instances without clashing
with mathlib's (deliberately instance-free) design. -/
def L₃ : Type := CyclotomicField 3 K₃

instance : Field L₃ := inferInstanceAs (Field (CyclotomicField 3 K₃))

instance : Algebra K₃ L₃ := inferInstanceAs (Algebra K₃ (CyclotomicField 3 K₃))

instance : CharZero L₃ := inferInstanceAs (CharZero (CyclotomicField 3 K₃))

instance : IsCyclotomicExtension {3} K₃ L₃ :=
  inferInstanceAs (IsCyclotomicExtension {3} K₃ (CyclotomicField 3 K₃))

instance : FiniteDimensional K₃ L₃ :=
  IsCyclotomicExtension.finiteDimensional {3} K₃ L₃

/-- The spectral norm of `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, installed as
the normed-field structure of `L₃` (mathlib ships it `@[instance_reducible]` by design;
on the local wrapper it is safe as a global instance). -/
instance : NormedField L₃ := spectralNorm.normedField K₃ L₃

instance : NontriviallyNormedField L₃ := spectralNorm.nontriviallyNormedField K₃ L₃

instance : NormedAlgebra K₃ L₃ := spectralNorm.normedAlgebra K₃ L₃

instance : IsUltrametricDist L₃ :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (fun x y => isNonarchimedean_spectralNorm (K := K₃) x y)

instance : CompleteSpace L₃ := FiniteDimensional.complete K₃ L₃

/-- The embedding `K₃ ↪ L₃`. -/
def ι₃ : K₃ →+* L₃ := algebraMap K₃ L₃

/-- The spectral norm extends the norm of `K₃`: `ι₃` is isometric
(`spectralNorm_extends` / `norm_algebraMap'`). -/
theorem norm_ι₃ (x : K₃) : ‖ι₃ x‖ = ‖x‖ := norm_algebraMap' L₃ x

/-- A primitive cube root of unity in `L₃`. -/
def ω₃ : L₃ := IsCyclotomicExtension.zeta 3 K₃ L₃

/-- `ω₃` satisfies the cube relation (`Φ₃ = X² + X + 1` and `ω₃` is a primitive root). -/
theorem ω₃_sq_add_ω₃_add_one : ω₃ ^ 2 + ω₃ + 1 = 0 := by
  have h : ∑ i ∈ Finset.range 3, ω₃ ^ i = 0 :=
    (IsCyclotomicExtension.zeta_spec 3 K₃ L₃).geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
  linear_combination h

/-- **The eigenblock factorisation of `det(1 − T·U₃)`, witnessed over
`L₃ = ℚ₃(ζ₃) = ℚ₃(√−3)`** — the minimal admissible extension, where the ramification
(`v₃(L₃ˣ) = ½ℤ`) is exactly what expresses the half-integer slopes `1/2, 3/2, 5/2, …`
of the `M₂,₂` factor. -/
theorem charPowerSeriesU3_factorisation_L₃ (t : K₃) (ht : ‖t‖ < 1) :
    PowerSeries.map ι₃ (charPowerSeriesU3 t ht)
      = charPowerSeries (Jacobs.M11op (norm_three_lt_one_of_isometry ι₃ norm_ι₃)
            (norm_map_weight_lt_one ι₃ norm_ι₃ ht) (map_ν₃_near ι₃ norm_ι₃)) *
          (charPowerSeries (Jacobs.M22op ω₃ ω₃_sq_add_ω₃_add_one
              (norm_three_lt_one_of_isometry ι₃ norm_ι₃)
              (norm_map_weight_lt_one ι₃ norm_ι₃ ht) (map_ν₃_near ι₃ norm_ι₃)) *
            charPowerSeries (Jacobs.M33op ω₃ ω₃_sq_add_ω₃_add_one
              (norm_three_lt_one_of_isometry ι₃ norm_ι₃)
              (norm_map_weight_lt_one ι₃ norm_ι₃ ht) (map_ν₃_near ι₃ norm_ι₃))) :=
  charPowerSeriesU3_factorisation ι₃ norm_ι₃ ω₃ ω₃_sq_add_ω₃_add_one t ht

end Cyclotomic

end Jacobs.U3
