/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«00_HaloRing»
import PhD.Main.LWX.«02_TiltedDegree»
import PhD.Main.TateFredholm.«04_Matrix»

/-!
# The integral `U_p`-matrix — SKELETON (lwx-halo board)

[LWX, Prop 3.1] presents `U_p` on the integral model as a `t × t` matrix of operators
`‖_δ` with `δ ∈ (pℤ_p, ℤ_p; qℤ_p, ℤ_p^×)`, `p` summands per row.  [LWX, Prop 3.4]
computes the matrix of a single `‖_δ` in the Mahler basis:
`P_{m,n}(δ) = Δ̃^m( binom((az+b)/(cz+d), n) · [cz+d] )|_{z=0}`, and the
[LWX, Prop 3.14] proof expands `[cz+d] = [d₀]·(1+T)^{g(z)}`,
`g(z) = log((cz+d)/d₀)/q`, giving the `T`-coefficient stream
`r ↦ [d₀]·Δ̃^m( binom(f(z),n)·binom(g(z),r) )|_{z=0}`.

In this development the stream **is the definition** of the entry (a `HaloInt p`
element supported in `ℕ`); that it computes the `‖_δ`-action on the integral model is
the deferred model-identification seam (see the board's plan.md).  [LWX, Prop 3.14(1)]
becomes the norm bound `‖entry δ m n‖ ≤ p^{−(m − ⌊n/p⌋)}` via the tilted-degree
calculus, and a `UpDatum` (targets + local matrices, `p` summands per block-row)
assembles the full matrix on `ι × ℕ` and, via cofinite column decay, a continuous
operator on `c(ι × ℕ, HaloInt p)`.
-/

open Filter Topology Finset TateFredholm
open scoped fwdDiff

noncomputable section

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]

/-- The monoid `M₁` of [LWX, (2.3.3)] in record form (`q = p` odd):
`δ = (a b; c d) ∈ M₂(ℤ_p)` with `p | c` and `d ∈ ℤ_p^×` (`a`, `b` free).  The
`U_p`-shape of [LWX, Prop 3.1(3)] — additionally `a ∈ pℤ_p` — is the refinement
`IsUpShape` below; [LWX, Prop 3.14] proves a bound in each case, and both are needed
(case (2) for stability of the rescaled model, case (1) for the halo estimate). -/
structure LocalMat where
  /-- Top-left entry. -/
  a : ℤ_[p]
  /-- Top-right entry. -/
  b : ℤ_[p]
  /-- Bottom-left entry, in `qℤ_p = pℤ_p`. -/
  c : ℤ_[p]
  /-- Bottom-right entry, a unit. -/
  d : ℤ_[p]ˣ
  hc : ‖c‖ ≤ (p : ℝ)⁻¹

namespace LocalMat

variable {p}

/-- The `U_p`-shape of [LWX, Prop 3.1(3)]: additionally `a ∈ pℤ_p`.  This is what
upgrades [LWX, Prop 3.14(2)]'s tilted-degree `n` to (1)'s `⌊n/p⌋`. -/
def IsUpShape (δ : LocalMat p) : Prop := ‖δ.a‖ ≤ (p : ℝ)⁻¹

/-- The Möbius function `z ↦ (az+b)/(cz+d)` of a local matrix; the denominator is a
unit for every `z ∈ ℤ_p` since `‖c‖ < 1` and `d` is a unit. -/
def mobiusFun (δ : LocalMat p) (z : ℤ_[p]) : ℤ_[p] :=
  (δ.a * z + δ.b) * Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))

/-- `cz + d` is a unit for `z ∈ ℤ_p`. -/
theorem isUnit_c_mul_add (δ : LocalMat p) (z : ℤ_[p]) :
    IsUnit (δ.c * z + (δ.d : ℤ_[p])) := by
  rw [PadicInt.isUnit_iff]
  have hd : ‖(δ.d : ℤ_[p])‖ = 1 := PadicInt.norm_units δ.d
  have hcz : ‖δ.c * z‖ < 1 := by
    calc ‖δ.c * z‖ ≤ ‖δ.c‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul δ.hc (PadicInt.norm_le_one z) (norm_nonneg _) (by positivity)
      _ = (p : ℝ)⁻¹ := mul_one _
      _ < 1 := by
          rw [inv_lt_one_iff₀]
          right
          exact_mod_cast hp.out.one_lt
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hd]; exact hcz.ne),
    hd, max_eq_right hcz.le]

/-- Transfer of `HasSum` along the isometric inclusion `ℤ_p ⊆ ℚ_p`. -/
private theorem hasSum_coe_iff {f : ℕ → ℤ_[p]} {a : ℤ_[p]} :
    HasSum (fun n => (f n : ℚ_[p])) (a : ℚ_[p]) ↔ HasSum f a := by
  constructor
  · intro h
    rw [HasSum, tendsto_iff_dist_tendsto_zero]
    rw [HasSum, tendsto_iff_dist_tendsto_zero] at h
    convert h using 2 with s
    rw [dist_eq_norm, dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub]
    congr 2
    exact map_sum (PadicInt.Coe.ringHom (p := p)) f s
  · intro h
    exact h.map (PadicInt.Coe.ringHom (p := p)).toAddMonoidHom
      continuous_subtype_val

/-- The geometric coefficient stream of the Möbius function:
`f(z) = (az+b)·d⁻¹·∑ (ez)^k` with `e := −d⁻¹c`, collected as
`a₀ = b·d⁻¹`, `a_{k+1} = d⁻¹·eᵏ·(b·e + a)`. -/
private def mobiusStream (δ : LocalMat p) : ℕ → ℤ_[p]
  | 0 => δ.b * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  | (k + 1) => ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k
      * (δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a)

private theorem norm_e_le (δ : LocalMat p) :
    ‖-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul, norm_neg, PadicInt.norm_units, one_mul]
  exact δ.hc

private theorem hasSum_mobiusStream (δ : LocalMat p) (z : ℤ_[p]) :
    HasSum (fun k => mobiusStream δ k * z ^ k) (δ.mobiusFun z) := by
  rw [← hasSum_coe_iff]
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  set eZ : ℤ_[p] := -((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c with heZ
  set e : ℚ_[p] := ((eZ : ℤ_[p]) : ℚ_[p]) with he
  set dv : ℚ_[p] := ((((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p]) with hdv
  have hez : ‖e * (z : ℚ_[p])‖ < 1 := by
    rw [norm_mul]
    calc ‖e‖ * ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · rw [he, PadicInt.padic_norm_e_of_padicInt]
            exact norm_e_le δ
          · rw [PadicInt.padic_norm_e_of_padicInt]
            exact PadicInt.norm_le_one z
      _ = (p : ℝ)⁻¹ := mul_one _
      _ < 1 := hpinv1
  have hgeo := hasSum_geometric_of_norm_lt_one hez
  -- coe-arithmetic: `↑d · e = −↑c` and the inverse identifications
  have hdd : ((δ.d : ℤ_[p]) : ℚ_[p]) * dv = 1 := by
    rw [hdv, ← PadicInt.coe_mul, Units.mul_inv]
    simp
  have hdinv : dv = (((δ.d : ℤ_[p]) : ℚ_[p]))⁻¹ := eq_inv_of_mul_eq_one_right hdd
  have hde : ((δ.d : ℤ_[p]) : ℚ_[p]) * e = -((δ.c : ℤ_[p]) : ℚ_[p]) := by
    rw [he, heZ]
    push_cast
    have h1 : ((δ.d : ℤ_[p]) : ℚ_[p]) * (((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := hdd
    calc ((δ.d : ℤ_[p]) : ℚ_[p])
          * (-(((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((δ.c : ℤ_[p]) : ℚ_[p]))
        = -((((δ.d : ℤ_[p]) : ℚ_[p]) * (((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))
            * ((δ.c : ℤ_[p]) : ℚ_[p])) := by ring
      _ = -((δ.c : ℤ_[p]) : ℚ_[p]) := by rw [h1, one_mul]
  have hfactor : ((δ.c * z + (δ.d : ℤ_[p]) : ℤ_[p]) : ℚ_[p])
      = ((δ.d : ℤ_[p]) : ℚ_[p]) * (1 - e * (z : ℚ_[p])) := by
    push_cast
    rw [mul_sub, mul_one, ← mul_assoc, hde]
    ring
  have hd0 : ((δ.d : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro hcon
    exact δ.d.ne_zero (Subtype.coe_injective hcon)
  have h1ez : (1 : ℚ_[p]) - e * (z : ℚ_[p]) ≠ 0 := by
    intro hcon
    have h1 : ‖e * (z : ℚ_[p])‖ = 1 := by
      rw [← sub_eq_zero.mp hcon, norm_one]
    exact hez.ne h1
  have hinv : ((Ring.inverse (δ.c * z + (δ.d : ℤ_[p])) : ℤ_[p]) : ℚ_[p])
      = (((δ.c * z + (δ.d : ℤ_[p]) : ℤ_[p]) : ℚ_[p]))⁻¹ := by
    obtain ⟨u, hu⟩ := isUnit_c_mul_add δ z
    rw [← hu, Ring.inverse_unit]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← PadicInt.coe_mul, Units.mul_inv]
    simp
  have hmob : ((δ.mobiusFun z : ℤ_[p]) : ℚ_[p])
      = (((δ.a : ℤ_[p]) : ℚ_[p]) * (z : ℚ_[p]) + ((δ.b : ℤ_[p]) : ℚ_[p])) * dv
        * (1 - e * (z : ℚ_[p]))⁻¹ := by
    rw [mobiusFun, PadicInt.coe_mul, hinv, hfactor, mul_inv, ← hdinv]
    push_cast
    ring
  -- normalise the goal's coercions
  rw [show (fun k => ((mobiusStream δ k * z ^ k : ℤ_[p]) : ℚ_[p]))
      = fun k => ((mobiusStream δ k : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ k from
    funext fun k => by push_cast; ring]
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.range_one, Finset.sum_singleton]
  -- the shifted stream is the scaled geometric series
  have hC := hgeo.mul_left
    (((((δ.b : ℤ_[p]) : ℚ_[p]) * e + ((δ.a : ℤ_[p]) : ℚ_[p])) * dv) * (z : ℚ_[p]))
  have hfun : (fun n : ℕ =>
      (((((δ.b : ℤ_[p]) : ℚ_[p]) * e + ((δ.a : ℤ_[p]) : ℚ_[p])) * dv) * (z : ℚ_[p]))
        * (e * (z : ℚ_[p])) ^ n)
      = fun n : ℕ => ((mobiusStream δ (n + 1) : ℤ_[p]) : ℚ_[p])
          * ((z : ℚ_[p])) ^ (n + 1) := by
    funext n
    show _ = ((((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * eZ ^ n * (δ.b * eZ + δ.a) : ℤ_[p]) : ℚ_[p])
        * ((z : ℚ_[p])) ^ (n + 1)
    rw [he, hdv]
    push_cast
    ring
  rw [hfun] at hC
  have hval : ((δ.mobiusFun z : ℤ_[p]) : ℚ_[p])
      - ((mobiusStream δ 0 : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ 0
      = (((((δ.b : ℤ_[p]) : ℚ_[p]) * e + ((δ.a : ℤ_[p]) : ℚ_[p])) * dv) * (z : ℚ_[p]))
        * (1 - e * (z : ℚ_[p]))⁻¹ := by
    rw [hmob]
    show _ - ((δ.b * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ 0 = _
    rw [pow_zero, mul_one]
    have hkey : ((1 : ℚ_[p]) - e * (z : ℚ_[p]))⁻¹ * (1 - e * (z : ℚ_[p])) = 1 :=
      inv_mul_cancel₀ h1ez
    push_cast [← hdv]
    linear_combination (dv * ((δ.b : ℤ_[p]) : ℚ_[p])) * hkey
  show HasSum
    (fun n => ((mobiusStream δ (n + 1) : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ (n + 1))
    (((δ.mobiusFun z : ℤ_[p]) : ℚ_[p])
      - ((mobiusStream δ 0 : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ 0)
  rw [hval]
  exact hC

/-- Under the `U_p`-shape the Möbius function has `k`-th coefficient in `p^k ℤ_p` —
the hypothesis of [LWX, Lemma 3.12] ("in case (1), we have `f(z) ∈ ℤ_p⟦pz⟧`").
Geometric expansion of `(cz+d)^{−1}`; both `a` and `c` contribute a factor of `p`. -/
theorem exists_hasSum_mobiusFun (δ : LocalMat p) (hδ : δ.IsUpShape) :
    ∃ a : ℕ → ℤ_[p], (∀ k, ‖a k‖ ≤ (p : ℝ) ^ (-(k : ℤ))) ∧
      ∀ z, HasSum (fun k => a k * z ^ k) (δ.mobiusFun z) := by
  refine ⟨mobiusStream δ, fun k => ?_, hasSum_mobiusStream δ⟩
  match k with
  | 0 =>
      show ‖δ.b * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ ≤ _
      calc ‖δ.b * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
        _ = (p : ℝ) ^ (-((0 : ℕ) : ℤ)) := by simp
  | (k + 1) =>
      show ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k
          * (δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a)‖ ≤ _
      have h1 : ‖(-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖ ≤ ((p : ℝ)⁻¹) ^ k := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_e_le δ) k
      have h2 : ‖δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a‖ ≤ (p : ℝ)⁻¹ := by
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hδ)
        calc ‖δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c)‖
            ≤ ‖δ.b‖ * ‖-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c‖ := norm_mul_le _ _
          _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul (PadicInt.norm_le_one _) (norm_e_le δ)
              (norm_nonneg _) zero_le_one
          _ = (p : ℝ)⁻¹ := one_mul _
      calc ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k
            * (δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a)‖
          ≤ ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖
            * ‖δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a‖ := norm_mul_le _ _
        _ ≤ (1 * ((p : ℝ)⁻¹) ^ k) * (p : ℝ)⁻¹ := by
            refine mul_le_mul ?_ h2 (norm_nonneg _) (by positivity)
            calc ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖
                ≤ ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖
                  * ‖(-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖ := norm_mul_le _ _
              _ ≤ 1 * ((p : ℝ)⁻¹) ^ k := by
                  rw [PadicInt.norm_units]
                  exact mul_le_mul le_rfl h1 (norm_nonneg _) zero_le_one
        _ = (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
            rw [one_mul, zpow_neg, ← inv_zpow, zpow_natCast, pow_succ]

/-- For a general `δ ∈ M₁` the Möbius function is still of [LWX, Lemma 3.13]'s shape
("in case (2), note that `f(z)` is of the form considered in Lemma 3.13"): only `c`
contributes a factor of `p`, giving `v(coeff_k) ≥ k − 1 ≥ (k−1) − v(k)`. -/
theorem exists_hasSum_mobiusFun_logShape (δ : LocalMat p) :
    ∃ A : ℕ → ℚ_[p], IsLogShape A ∧
      ∀ z : ℤ_[p], HasSum (fun k => A k * (z : ℚ_[p]) ^ k) (δ.mobiusFun z : ℚ_[p]) := by
  refine ⟨fun k => ((mobiusStream δ k : ℤ_[p]) : ℚ_[p]), ?_, fun z => ?_⟩
  · constructor
    · show ‖((mobiusStream δ 0 : ℤ_[p]) : ℚ_[p])‖ ≤ 1
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact PadicInt.norm_le_one _
    · intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      show ‖((mobiusStream δ (k + 1) : ℤ_[p]) : ℚ_[p])‖ * ‖((k + 1 : ℕ) : ℚ_[p])‖ ≤ _
      have hstream : ‖mobiusStream δ (k + 1)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
        show ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k
            * (δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a)‖ ≤ _
        calc ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k
              * (δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a)‖
            ≤ ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖
              * ‖δ.b * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) + δ.a‖ := norm_mul_le _ _
          _ ≤ (1 * ((p : ℝ)⁻¹) ^ k) * 1 := by
              refine mul_le_mul ?_ (PadicInt.norm_le_one _) (norm_nonneg _)
                (by positivity)
              calc ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖
                  ≤ ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖
                    * ‖(-((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * δ.c) ^ k‖ := norm_mul_le _ _
                _ ≤ 1 * ((p : ℝ)⁻¹) ^ k := by
                    rw [PadicInt.norm_units, norm_pow]
                    exact mul_le_mul le_rfl
                      (pow_le_pow_left₀ (norm_nonneg _) (norm_e_le δ) k)
                      (by positivity) zero_le_one
          _ = ((p : ℝ)⁻¹) ^ k := by rw [one_mul, mul_one]
      calc ‖((mobiusStream δ (k + 1) : ℤ_[p]) : ℚ_[p])‖ * ‖((k + 1 : ℕ) : ℚ_[p])‖
          ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
            refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
            · rw [PadicInt.padic_norm_e_of_padicInt]
              exact hstream
            · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
        _ = (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ) + 1) := by
            rw [mul_one]
            rw [show (-((k + 1 : ℕ) : ℤ) + 1) = -(k : ℤ) by push_cast; ring,
              zpow_neg, ← inv_zpow, zpow_natCast]
  · have h := (hasSum_coe_iff (p := p)).mpr (hasSum_mobiusStream δ z)
    rw [show (fun k => ((mobiusStream δ k * z ^ k : ℤ_[p]) : ℚ_[p]))
        = fun k => ((mobiusStream δ k : ℤ_[p]) : ℚ_[p]) * ((z : ℚ_[p])) ^ k from
      funext fun k => by push_cast; ring] at h
    exact h


/-- The linear coefficient `w = c·d⁻¹` of the denominator's `1`-unit part. -/
def wCoeff (δ : LocalMat p) : ℤ_[p] := δ.c * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])

/-- `‖w‖ ≤ p⁻¹`, from `p ∣ c`. -/
theorem norm_wCoeff_le (δ : LocalMat p) : ‖δ.wCoeff‖ ≤ (p : ℝ)⁻¹ := by
  calc ‖δ.c * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖
      ≤ ‖δ.c‖ * ‖((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ := norm_mul_le _ _
    _ ≤ (p : ℝ)⁻¹ * 1 := by
        rw [PadicInt.norm_units]
        exact mul_le_mul δ.hc le_rfl zero_le_one (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

/-- The additive bound `‖qlog u‖ ≤ p⁻¹` on the disc, `p ≠ 2`-free (via the general
`norm_padicLog_le`, whose margin does not need the odd-`p` sharpening). -/
private theorem norm_qlog_le' {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖qlog u‖ ≤ (p : ℝ)⁻¹ := by
  have hnp : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p, inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  have h1 : ‖(u : ℚ_[p]) - 1‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [Padic.norm_p,
      show ((u : ℚ_[p]) - 1) = ((u - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring,
      PadicInt.padic_norm_e_of_padicInt]
    exact hu
  have h2 := PadicExpLog.norm_padicLog_le hnp h1
  rw [Padic.norm_p] at h2
  exact h2

private theorem norm_one_add_wCoeff_mul_sub_one (δ : LocalMat p) (z : ℤ_[p]) :
    ‖(1 + δ.wCoeff * z) - 1‖ ≤ (p : ℝ)⁻¹ := by
  rw [add_sub_cancel_left]
  calc ‖δ.wCoeff * z‖ ≤ ‖δ.wCoeff‖ * ‖z‖ := norm_mul_le _ _
    _ ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul (norm_wCoeff_le δ) (PadicInt.norm_le_one z)
        (norm_nonneg _) (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

private theorem norm_gFun_num_le (δ : LocalMat p) (z : ℤ_[p]) :
    ‖qlog (oneUnitPart δ.d) + qlog (1 + δ.wCoeff * z)‖ ≤ (p : ℝ)⁻¹ :=
  (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (norm_qlog_le' (norm_oneUnitPart_sub_one_le δ.d))
      (norm_qlog_le' (norm_one_add_wCoeff_mul_sub_one δ z)))

/-- The exponent function `g(z) = log((cz+d)/d₀)/p` of the [LWX, Prop 3.14] proof:
with `⟨d⟩ = d·ωT(d)⁻¹` and `w = c·d⁻¹`, `g(z) = (qlog⟨d⟩ + qlog(1 + wz))/p`, valued in
`ℤ_p`. -/
def gFun (δ : LocalMat p) (z : ℤ_[p]) : ℤ_[p] :=
  ⟨(qlog (oneUnitPart δ.d) + qlog (1 + δ.wCoeff * z)) / (p : ℚ_[p]), by
    rw [norm_div, Padic.norm_p,
      div_le_one (inv_pos.mpr (by exact_mod_cast hp.out.pos))]
    exact norm_gFun_num_le δ z⟩

/-- The coefficient stream of `gFun`: constant `qlog⟨d⟩/p` plus the linear-composite
log stream; of [LWX, Lemma 3.13]'s shape after the additivity split. -/
def gCoeff (δ : LocalMat p) : ℕ → ℚ_[p]
  | 0 => (qlog (oneUnitPart δ.d) + qlogLinearCoeff δ.wCoeff 0) / (p : ℚ_[p])
  | (k + 1) => qlogLinearCoeff δ.wCoeff (k + 1) / (p : ℚ_[p])

theorem coe_gFun (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.gFun z : ℤ_[p]) : ℚ_[p])
      = (qlog (oneUnitPart δ.d) + qlog (1 + δ.wCoeff * z)) / (p : ℚ_[p]) := rfl

theorem isLogShape_gCoeff (hp2 : p ≠ 2) (δ : LocalMat p) : IsLogShape δ.gCoeff := by
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  constructor
  · show ‖(qlog (oneUnitPart δ.d) + qlogLinearCoeff δ.wCoeff 0) / (p : ℚ_[p])‖ ≤ 1
    rw [norm_div, Padic.norm_p, div_le_one hp0,
      show qlogLinearCoeff δ.wCoeff 0 = 0 from rfl, add_zero]
    exact (norm_qlog_le hp2 (norm_oneUnitPart_sub_one_le δ.d)).trans
      (norm_oneUnitPart_sub_one_le δ.d)
  · intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show ‖qlogLinearCoeff δ.wCoeff (k + 1) / (p : ℚ_[p])‖ * ‖((k + 1 : ℕ) : ℚ_[p])‖ ≤ _
    -- the sharp product: `‖qlc w (k+1)‖·‖k+1‖ = ‖w‖^{k+1}`
    have hcast : ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
    have hne : (((k + 1 : ℕ)) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hsharp : ‖qlogLinearCoeff δ.wCoeff (k + 1)‖ * ‖((k + 1 : ℕ) : ℚ_[p])‖
        = ‖(δ.wCoeff : ℚ_[p])‖ ^ (k + 1) := by
      show ‖(-1 : ℚ_[p]) ^ k * ((δ.wCoeff : ℤ_[p]) : ℚ_[p]) ^ (k + 1) / ((k : ℚ_[p]) + 1)‖
          * ‖((k + 1 : ℕ) : ℚ_[p])‖ = _
      rw [norm_div, hcast, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hne), norm_mul,
        norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [norm_div, Padic.norm_p, div_mul_eq_mul_div, div_le_iff₀ hp0, hsharp]
    have hwQ : ‖((δ.wCoeff : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact norm_wCoeff_le δ
    calc ‖((δ.wCoeff : ℤ_[p]) : ℚ_[p])‖ ^ (k + 1) ≤ ((p : ℝ)⁻¹) ^ (k + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hwQ _
      _ = (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by rw [zpow_neg, ← inv_zpow, zpow_natCast]
      _ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ) + 1) * (p : ℝ)⁻¹ := by
          rw [← zpow_neg_one, ← zpow_add₀ hppos.ne']
          refine le_of_eq ?_
          congr 1
          push_cast
          ring

theorem hasSum_gCoeff (_hp2 : p ≠ 2) (δ : LocalMat p) (z : ℤ_[p]) :
    HasSum (fun k => δ.gCoeff k * (z : ℚ_[p]) ^ k) (δ.gFun z : ℚ_[p]) := by
  have h1 := (hasSum_qlogLinearCoeff (norm_wCoeff_le δ) z).div_const (p : ℚ_[p])
  have h2 : HasSum
      (fun k : ℕ => if k = 0 then qlog (oneUnitPart δ.d) / (p : ℚ_[p]) else 0)
      (qlog (oneUnitPart δ.d) / (p : ℚ_[p])) := hasSum_ite_eq 0 _
  have h3 := h2.add h1
  rw [coe_gFun δ z, add_div]
  have hfeq : (fun k : ℕ =>
      (if k = 0 then qlog (oneUnitPart δ.d) / (p : ℚ_[p]) else 0)
        + qlogLinearCoeff δ.wCoeff k * (z : ℚ_[p]) ^ k / (p : ℚ_[p]))
      = fun k => δ.gCoeff k * (z : ℚ_[p]) ^ k := by
    funext k
    match k with
    | 0 =>
        show qlog (oneUnitPart δ.d) / (p : ℚ_[p])
            + qlogLinearCoeff δ.wCoeff 0 * (z : ℚ_[p]) ^ 0 / (p : ℚ_[p])
          = (qlog (oneUnitPart δ.d) + qlogLinearCoeff δ.wCoeff 0) / (p : ℚ_[p])
            * (z : ℚ_[p]) ^ 0
        ring
    | (k + 1) =>
        show (0 : ℚ_[p])
            + qlogLinearCoeff δ.wCoeff (k + 1) * (z : ℚ_[p]) ^ (k + 1) / (p : ℚ_[p])
          = qlogLinearCoeff δ.wCoeff (k + 1) / (p : ℚ_[p]) * (z : ℚ_[p]) ^ (k + 1)
        ring
  rw [hfeq] at h3
  exact h3

end LocalMat

variable {p}

/-- The `T`-coefficient stream of the matrix entry `P_{m,n}(δ)` ([LWX, Prop 3.4] as
expanded in the [LWX, Prop 3.14] proof): coefficient of `T^r` is
`ω(d mod p) · Δ̃^m( binom(f(z), n) · binom(g(z), r) )|_{z=0}`; `0` for `r < 0`. -/
def entryCoeff (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p) (m n : ℕ) (r : ℤ) : ℤ_[p] :=
  if _hr : 0 ≤ r then
    (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p]) *
      Δ_[1]^[m] (fun z => Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat) 0
  else 0

/-- The entry as a halo-ring element (supported in `ℕ`, coefficients integral). -/
def entry (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p) (m n : ℕ) : HaloInt p :=
  ⟨entryCoeff ω δ m n, fun j => by
    rw [entryCoeff]
    split_ifs with h
    · calc ‖(ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p]) *
            Δ_[1]^[m] (fun z => Ring.choose (δ.mobiusFun z) n
              * Ring.choose (δ.gFun z) j.toNat) 0‖
          ≤ 1 := PadicInt.norm_le_one _
        _ = (p : ℝ) ^ (min 0 j) := by rw [min_eq_left h, zpow_zero]
    · rw [norm_zero]
      exact (zpow_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p) _).le⟩

@[simp] theorem coeff_entry (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p) (m n : ℕ)
    (r : ℤ) : (entry ω δ m n) r = entryCoeff ω δ m n r := rfl

/-- The shared tilted-degree evaluation behind both cases of [LWX, Prop 3.14]. -/
private theorem norm_entryCoeff_le_aux (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (δ : LocalMat p) (m n : ℕ) {dF : ℕ}
    (hf : TiltedDeg dF fun z => Ring.choose (δ.mobiusFun z) n) (r : ℤ) (hr : 0 ≤ r) :
    ‖entryCoeff ω δ m n r‖ ≤ (p : ℝ) ^ ((dF : ℤ) + r - m) := by
  have hg : TiltedDeg r.toNat fun z => Ring.choose (δ.gFun z) r.toNat :=
    tiltedDeg_choose_of_logShape hp2 (LocalMat.isLogShape_gCoeff hp2 δ)
      (LocalMat.hasSum_gCoeff hp2 δ) r.toNat
  have heval := (hf.mul hg) m 0
  rw [entryCoeff, dif_pos hr, norm_mul, PadicInt.norm_units, one_mul]
  refine heval.trans (le_of_eq ?_)
  congr 1
  omega

/-- The tilted-degree bounds packaged into the halo norm, shared by both cases. -/
private theorem norm_entry_le_aux (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p)
    (m n : ℕ) {dF : ℕ}
    (hbound : ∀ r : ℤ, 0 ≤ r → ‖entryCoeff ω δ m n r‖ ≤ (p : ℝ) ^ ((dF : ℤ) + r - m)) :
    ‖entry ω δ m n‖ ≤ (p : ℝ) ^ (-((m - dF : ℕ) : ℤ)) := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [HaloInt.norm_le_zpow_iff]
  intro j
  rcases lt_or_ge j 0 with hj | hj
  · rw [coeff_entry, entryCoeff, dif_neg (by omega), norm_zero]
    exact (zpow_pos (by positivity : (0 : ℝ) < p) _).le
  · rcases le_or_gt dF m with hmn | hmn
    · refine (hbound j hj).trans (zpow_le_zpow_right₀ hp1R.le ?_)
      omega
    · calc ‖(entry ω δ m n) j‖ ≤ 1 := by
            rw [coeff_entry, entryCoeff, dif_pos hj]
            exact PadicInt.norm_le_one _
        _ ≤ (p : ℝ) ^ (j - ((m - dF : ℕ) : ℤ)) := by
            rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
            exact zpow_le_zpow_right₀ hp1R.le (by omega)

/-- **[LWX, Prop 3.14(1)]**, coefficientwise: under the `U_p`-shape the
`T^r`-coefficient of `P_{m,n}(δ)` has valuation `≥ m − ⌊n/p⌋ − r` — from tilted
degrees `⌊n/p⌋` for `binom(f, n)` (Lemma 3.12) and `r` for `binom(g, r)`
(Lemma 3.13), added by Lemma 3.10(2), evaluated by Def-Prop 3.8(1) at `z = 0`. -/
theorem norm_entryCoeff_le (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {δ : LocalMat p}
    (hδ : δ.IsUpShape) (m n : ℕ) (r : ℤ) (hr : 0 ≤ r) :
    ‖entryCoeff ω δ m n r‖ ≤ (p : ℝ) ^ (((n / p : ℕ) : ℤ) + r - m) := by
  obtain ⟨aS, haS, hsum⟩ := LocalMat.exists_hasSum_mobiusFun δ hδ
  exact norm_entryCoeff_le_aux hp2 ω δ m n
    (tiltedDeg_choose_of_pMul haS hsum n) r hr

/-- **[LWX, Prop 3.14(1)]**, packaged: `‖P_{m,n}(δ)‖ ≤ p^{−(m − ⌊n/p⌋)}` in the halo
ring (`𝔪^{max(m−⌊n/p⌋,0)}`-membership). -/
theorem norm_entry_le (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {δ : LocalMat p}
    (hδ : δ.IsUpShape) (m n : ℕ) :
    ‖entry ω δ m n‖ ≤ (p : ℝ) ^ (-((m - n / p : ℕ) : ℤ)) :=
  norm_entry_le_aux ω δ m n (norm_entryCoeff_le hp2 ω hδ m n)

/-- **[LWX, Prop 3.14(2)]**, coefficientwise: for any `δ ∈ M₁` the
`T^r`-coefficient of `P_{m,n}(δ)` has valuation `≥ m − n − r` — Lemma 3.13 applied to
`binom(f, n)` as well (via `exists_hasSum_mobiusFun_logShape`). -/
theorem norm_entryCoeff_le_M1 (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p)
    (m n : ℕ) (r : ℤ) (hr : 0 ≤ r) :
    ‖entryCoeff ω δ m n r‖ ≤ (p : ℝ) ^ ((n : ℤ) + r - m) := by
  obtain ⟨A, hA, hsum⟩ := LocalMat.exists_hasSum_mobiusFun_logShape δ
  exact norm_entryCoeff_le_aux hp2 ω δ m n
    (tiltedDeg_choose_of_logShape hp2 hA hsum n) r hr

/-- **[LWX, Prop 3.14(2)]**, packaged: `‖P_{m,n}(δ)‖ ≤ p^{−(m − n)}` for any
`δ ∈ M₁` — what the stability of the rescaled model (tranche H) consumes. -/
theorem norm_entry_le_M1 (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p)
    (m n : ℕ) : ‖entry ω δ m n‖ ≤ (p : ℝ) ^ (-((m - n : ℕ) : ℤ)) :=
  norm_entry_le_aux ω δ m n (norm_entryCoeff_le_M1 hp2 ω δ m n)

variable (p)

/-- The combinatorial datum of [LWX, Prop 3.1] (the parts Theorem 3.16 consumes):
a class set `ι`, and for each `i : ι` exactly `p` summands, each a target index and a
local matrix of the required shape.  (Prop 3.1(2)'s column count is not used.) -/
structure UpDatum (ι : Type*) where
  /-- The target block of the `j`-th summand in row `i` (`γ_{λ_{i,j}}` in
  [LWX, Prop 3.1]). -/
  tgt : ι → Fin p → ι
  /-- The local matrix `δ_{i,j,p}` of the `j`-th summand in row `i`. -/
  mat : ι → Fin p → LocalMat p
  /-- Every local matrix has the `U_p`-shape of [LWX, Prop 3.1(3)]. -/
  hshape : ∀ i j, (mat i j).IsUpShape

variable {p} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full matrix of the integral `U_p` on `ι × ℕ` ([LWX, Prop 3.1 + Prop 3.4]):
row `(i, m)`, column `(i', n)` entry `= ∑_{j : tgt i j = i'} P_{m,n}(δ_{i,j})`. -/
def UpDatum.matrix (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ι × ℕ → ι × ℕ → HaloInt p := fun a b =>
  ∑ j ∈ Finset.univ.filter (fun j : Fin p => D.tgt a.1 j = b.1),
    entry ω (D.mat a.1 j) a.2 b.2

omit [Fintype ι] in
/-- The two-sided weight bound for the full matrix ([LWX, (3.16.2)] blockwise):
`‖M_{(i,m),(i',n)}‖ ≤ p^{−(m − ⌊n/p⌋)}` — an ultrametric max over `≤ p` entry bounds. -/
theorem UpDatum.norm_matrix_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a b : ι × ℕ) :
    ‖D.matrix ω a b‖ ≤ (p : ℝ) ^ (-((a.2 - b.2 / p : ℕ) : ℤ)) := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (zpow_nonneg (Nat.cast_nonneg p) _) fun j _ => ?_
  exact norm_entry_le hp2 ω (D.hshape a.1 j) a.2 b.2

/-- Columns of the full matrix vanish cofinitely (rows at fixed column decay), so the
matrix defines a continuous operator on the model space. -/
theorem UpDatum.tendsto_matrix_cofinite (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (b : ι × ℕ) :
    Tendsto (fun a => D.matrix ω a b) cofinite (𝓝 0) := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1R
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hpinv1
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    ((Set.finite_univ (α := ι)).prod (Set.finite_Iio (b.2 / p + N))) ?_
  intro a ha
  rw [Set.mem_ofPred_eq, not_lt] at ha
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra hcon
  rw [Set.mem_Iio, not_lt] at hcon
  have h1 := D.norm_matrix_le hp2 ω a b
  have h2 : (p : ℝ) ^ (-((a.2 - b.2 / p : ℕ) : ℤ)) ≤ ((p : ℝ)⁻¹) ^ N := by
    rw [show ((p : ℝ)⁻¹) ^ N = (p : ℝ) ^ (-(N : ℤ)) by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]]
    exact zpow_le_zpow_right₀ hp1R.le (by omega)
  linarith

section op

variable (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

omit [Fintype ι] in
/-- Uniform integrality of the matrix entries. -/
private theorem norm_matrix_le_one (a b : ι × ℕ) : ‖D.matrix ω a b‖ ≤ 1 :=
  HaloInt.norm_le_one _

omit [Fintype ι] in
private theorem tendsto_row_mul (φ : c(ι × ℕ, HaloInt p)) (a : ι × ℕ) :
    Tendsto (fun b => D.matrix ω a b * φ b) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (a := fun b => ‖φ b‖) (fun b => ?_) ?_
  · calc ‖D.matrix ω a b * φ b‖ ≤ ‖D.matrix ω a b‖ * ‖φ b‖ := norm_mul_le _ _
      _ ≤ 1 * ‖φ b‖ := mul_le_mul_of_nonneg_right (norm_matrix_le_one D ω a b)
          (norm_nonneg _)
      _ = ‖φ b‖ := one_mul _
  · simpa using (cSpace.tendsto_cofinite φ).norm

omit [Fintype ι] in
private theorem norm_tsum_row_le (φ : c(ι × ℕ, HaloInt p)) (a : ι × ℕ) :
    ‖∑' b, D.matrix ω a b * φ b‖ ≤ ‖φ‖ := by
  refine (norm_tsum_le_iSup (tendsto_row_mul D ω φ a)).trans
    (Real.iSup_le (fun b => ?_) (norm_nonneg _))
  calc ‖D.matrix ω a b * φ b‖ ≤ ‖D.matrix ω a b‖ * ‖φ b‖ := norm_mul_le _ _
    _ ≤ 1 * ‖φ‖ := mul_le_mul (norm_matrix_le_one D ω a b) (cSpace.norm_apply_le φ b)
        (norm_nonneg _) zero_le_one
    _ = ‖φ‖ := one_mul _

private theorem mul_le_of_le_div_add_one' {a b t δ : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (ha : a ≤ δ / (t + 1)) (hbt : b ≤ t) : a * b ≤ δ := by
  have ht : 0 ≤ t := hb.trans hbt
  calc a * b ≤ (δ / (t + 1)) * (t + 1) :=
        mul_le_mul ha (by linarith) hb (by positivity)
    _ = δ := div_mul_cancel₀ δ (by positivity)

/-- Rows of the image vanish cofinitely: the [LWX] analogue of the `GenFun` row-decay
argument, over `ι × ℕ` and the halo ring. -/
private theorem tendsto_tsum_row (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloInt p)) :
    Tendsto (fun a => ∑' b, D.matrix ω a b * φ b) cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ, 0 < δ ∧ δ < ε := ⟨ε / 2, by linarith, by linarith⟩
  have hev : ∀ᶠ b in cofinite, ‖φ b‖ < δ / (1 + 1) :=
    NormedAddGroup.tendsto_nhds_zero.1 (cSpace.tendsto_cofinite φ) _ (by positivity)
  set S := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hout : ∀ b ∉ S, ‖φ b‖ ≤ δ / (1 + 1) := by
    intro b hb
    rw [hS, Set.Finite.mem_toFinset] at hb
    exact (not_not.1 hb).le
  have hin : ∀ᶠ a in cofinite, ∀ b ∈ S, ‖D.matrix ω a b‖ ≤ δ / (‖φ‖ + 1) :=
    (Filter.eventually_all_finset S).2 fun b _ =>
      (NormedAddGroup.tendsto_nhds_zero.1 (D.tendsto_matrix_cofinite hp2 ω b) _
        (by positivity)).mono fun _ h => h.le
  filter_upwards [hin] with a ha
  refine lt_of_le_of_lt ?_ hδε
  refine (norm_tsum_le_iSup (tendsto_row_mul D ω φ a)).trans
    (Real.iSup_le (fun b => ?_) hδ.le)
  refine (norm_mul_le _ _).trans ?_
  by_cases hb : b ∈ S
  · exact mul_le_of_le_div_add_one' hδ.le (norm_nonneg _) (ha b hb)
      (cSpace.norm_apply_le φ b)
  · rw [mul_comm]
    exact mul_le_of_le_div_add_one' hδ.le (norm_nonneg _) (hout b hb)
      (norm_matrix_le_one D ω a b)

private noncomputable def opFun (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloInt p)) :
    c(ι × ℕ, HaloInt p) :=
  ⟨⟨fun a : Ix (ι × ℕ) => ∑' b, D.matrix ω a b * φ b, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    exact tendsto_tsum_row D ω hp2 φ⟩

private theorem opFun_apply (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloInt p)) (a : ι × ℕ) :
    opFun D ω hp2 φ a = ∑' b, D.matrix ω a b * φ b := rfl

private noncomputable def opLinear (hp2 : p ≠ 2) :
    c(ι × ℕ, HaloInt p) →ₗ[HaloInt p] c(ι × ℕ, HaloInt p) where
  toFun := opFun D ω hp2
  map_add' φ ψ := by
    refine DFunLike.ext _ _ fun a => ?_
    show (∑' b, D.matrix ω a b * (φ + ψ) b)
        = (∑' b, D.matrix ω a b * φ b) + ∑' b, D.matrix ω a b * ψ b
    rw [← ((TateFredholm.summable_of_tendsto_cofinite
        (tendsto_row_mul D ω φ a)).hasSum.add
      (TateFredholm.summable_of_tendsto_cofinite
        (tendsto_row_mul D ω ψ a)).hasSum).tsum_eq]
    exact tsum_congr fun b => mul_add (D.matrix ω a b) (φ b) (ψ b)
  map_smul' r φ := by
    refine DFunLike.ext _ _ fun a => ?_
    show (∑' b, D.matrix ω a b * (r • φ) b) = r * ∑' b, D.matrix ω a b * φ b
    rw [← Summable.tsum_mul_left r
      (TateFredholm.summable_of_tendsto_cofinite (tendsto_row_mul D ω φ a))]
    refine tsum_congr fun b => ?_
    show D.matrix ω a b * (r * φ b) = r * (D.matrix ω a b * φ b)
    rw [mul_left_comm]

end op

/-- The integral `U_p` operator on `c(ι × ℕ, Λ^{>1/p})` recovered from the matrix.
(Statement-protected signature carries no `p ≠ 2`; at `p = 2` the operator is the
same row-sum construction, still bounded — only the *column-decay* input needs
`p ≠ 2` through Prop 3.14, so the junk-free construction threads a case split.) -/
noncomputable def UpDatum.op (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    c(ι × ℕ, HaloInt p) →L[HaloInt p] c(ι × ℕ, HaloInt p) :=
  if hp2 : p ≠ 2 then
    LinearMap.mkContinuous (opLinear D ω hp2) 1 fun φ => by
      rw [one_mul, cSpace.norm_eq_iSup]
      exact Real.iSup_le (fun a => norm_tsum_row_le D ω φ a) (norm_nonneg _)
  else 0

/-- The operator's rows, at odd `p`: the matrix-times-coordinates sum. -/
theorem UpDatum.op_apply (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (φ : c(ι × ℕ, HaloInt p)) (a : ι × ℕ) :
    D.op ω φ a = ∑' b, D.matrix ω a b * φ b := by
  rw [UpDatum.op, dif_pos hp2]
  rfl

/-- The operator's matrix is the datum's matrix. -/
theorem UpDatum.matrixCoeff_op (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a b : ι × ℕ) :
    matrixCoeff (D.op ω) a b = D.matrix ω a b := by
  rw [UpDatum.op, dif_pos hp2]
  show (∑' b', D.matrix ω a b' * cSpace.single b (1 : HaloInt p) b') = D.matrix ω a b
  rw [tsum_eq_single b (fun b' hb' => by
    rw [cSpace.single_apply_of_ne hb', mul_zero]), cSpace.single_apply_self, mul_one]

end LWX
