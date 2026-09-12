/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«03_UpMatrix»
import PhD.Main.TateFredholm.«06_TwoSidedBound»
import PhD.Main.NewtonPolygons.OfSlopes
import PhD.Main.NewtonPolygons.CoeffVal
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The halo estimate: [LWX] Theorem 3.16 and Corollary 3.18 — SKELETON (lwx-halo board)

The headline of the board.  For any `UpDatum` on a class set `ι` with `t = |ι|`:

* **Theorem 3.16**: the characteristic power series `∑ c_n Xⁿ` of the integral `U_p`
  is well defined over `Λ^{>1/p}` and `c_n ∈ T^{λ(n)}·Λ^{>1/p}`, where
  `λ(n) = ∑_{k<n} (⌊k/t⌋ − ⌊k/pt⌋)`.  Here as the norm bound
  `‖c_n‖ ≤ p^{−λ(n)}` plus the `T`-power reading.
* **Corollary 3.18**: at every specialization `T₀` with `p⁻¹ < ‖T₀‖ < 1` in a complete
  ultrametric field, the Newton polygon of the specialized series lies on or above the
  polygon with `k`-th unit slope `(⌊k/t⌋ − ⌊k/pt⌋)·v(T₀)`.

The quaternionic feed ([LWX, Prop 3.1]'s local shape): products `u·v_j` of an Iwahori
matrix `u` with the coset representative `v_j = (p 0; jp 1)` land in `LocalMat`.
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The exponent `λ` -/

/-- [LWX, Thm 3.16]'s exponent: `λ(n) = ∑_{k<n} (⌊k/t⌋ − ⌊k/pt⌋)` (the increments are
`λ(i+1) − λ(i) = ⌊i/t⌋ − ⌊i/pt⌋`). -/
def lwxLambda (p t n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (k / t - k / (p * t))

/-- The increment form of `λ` ([LWX, Thm 3.16]). -/
theorem lwxLambda_succ (p t n : ℕ) :
    lwxLambda p t (n + 1) = lwxLambda p t n + (n / t - n / (p * t)) :=
  Finset.sum_range_succ _ n

/-- Below the block size `λ` vanishes: every term `k/t − k/(pt)` with `k < t` is `0`. -/
theorem lwxLambda_eq_zero_of_le {p t n : ℕ} (hn : n ≤ t) : lwxLambda p t n = 0 :=
  Finset.sum_eq_zero fun k hk => by
    have h : k / t = 0 := Nat.div_eq_of_lt ((Finset.mem_range.1 hk).trans_le hn)
    rw [h, Nat.zero_sub]

/-- The net weight `m ↦ m − ⌊m/p⌋` is monotone. -/
theorem monotone_sub_div (p : ℕ) : Monotone fun m : ℕ => m - m / p := by
  intro a b hab
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [Nat.div_zero, Nat.sub_zero]
    exact hab
  · have h2 : b / p ≤ a / p + (b - a) := by
      calc b / p ≤ (a + (b - a) * p) / p := Nat.div_le_div_right (by
            have h : (b - a) * 1 ≤ (b - a) * p := Nat.mul_le_mul le_rfl hp
            omega)
        _ = a / p + (b - a) := by rw [Nat.add_mul_div_right _ _ hp]
    have h1 : a / p ≤ a := Nat.div_le_self a p
    show a - a / p ≤ b - b / p
    omega

/-- `λ` through the block weight: `∑_{k<n} v(⌊k/t⌋)` for `v(m) = m − ⌊m/p⌋` equals
`λ(n)`, via `⌊⌊k/t⌋/p⌋ = ⌊k/(pt)⌋`. -/
theorem lwxLambda_eq_sum_comp (p t : ℕ) (n : ℕ) :
    lwxLambda p t n = ∑ k ∈ Finset.range n, (k / t - (k / t) / p) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm t p]

/-! ### Theorem 3.16 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entrywise two-sided weight bound for the integral `U_p`, in the form the
Hadamard machine consumes: `‖u_{(i,m),(j,n)}‖ ≤ (p⁻¹)^{m − ⌊n/p⌋}`. -/
private theorem hdiv_upOp (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ∀ a b : ι × ℕ, ‖matrixCoeff (D.op ω) a b‖ ≤ ((p : ℝ)⁻¹) ^ (a.2 - b.2 / p) := by
  intro a b
  rw [D.matrixCoeff_op hp2 ω a b]
  refine (D.norm_matrix_le hp2 ω a b).trans (le_of_eq ?_)
  rw [zpow_neg, ← inv_zpow, zpow_natCast]

omit [DecidableEq ι] in
/-- The net weight `m − ⌊m/p⌋` grows cofinitely on `ι × ℕ`. -/
theorem tendsto_weight_cofinite_atTop :
    Tendsto (fun a : ι × ℕ => a.2 - a.2 / p) cofinite atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    ((Set.finite_univ (α := ι)).prod (Set.finite_Iio (2 * B + 2))) ?_
  intro a ha
  rw [Set.mem_ofPred_eq, not_le] at ha
  refine ⟨Set.mem_univ _, ?_⟩
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  have h2 : a.2 / p ≤ a.2 / 2 := Nat.div_le_div_left hp.out.two_le zero_lt_two
  omega

omit hp in
/-- The initial-segment weight minimum: `λ(n)` bounds the net weight sum of every
`n`-element index set. -/
private theorem lwxLambda_le_sum_sub (S : Finset (ι × ℕ)) (n : ℕ) (hS : S.card = n) :
    lwxLambda p (Fintype.card ι) n ≤ (∑ a ∈ S, a.2) - ∑ a ∈ S, a.2 / p := by
  have h1 : ∑ a ∈ S, (a.2 - a.2 / p) = (∑ a ∈ S, a.2) - ∑ a ∈ S, a.2 / p :=
    Finset.sum_tsub_distrib S fun x _ => Nat.div_le_self _ _
  rw [← h1, lwxLambda_eq_sum_comp]
  exact sum_comp_div_le_sum_monotone (monotone_sub_div p) hS

/-- Well-definedness of the characteristic power series ([LWX, Thm 3.16, "is well
defined"]): the `n`-element minors of the integral `U_p` are summable. -/
theorem summable_minor_upOp (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    Summable fun S : {S : Finset (ι × ℕ) // S.card = n} =>
      minor (D.op ω) (S : Finset (ι × ℕ)) := by
  refine summable_minor_of_two_sided (by positivity) ?_ (fun a => a.2)
    (fun b => b.2 / p) (hdiv_upOp hp2 D ω) tendsto_weight_cofinite_atTop n
  rw [inv_lt_one_iff₀]
  right
  exact_mod_cast hp.out.one_lt

/-- **[LWX, Theorem 3.16]** (norm form): `‖c_n‖ ≤ p^{−λ(n)}` with `t = |ι|`. -/
theorem norm_charCoeff_upOp_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    ‖charCoeff (D.op ω) n‖ ≤ (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) n : ℤ)) := by
  have hσ1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  refine (norm_charCoeff_le_pow_two_sided (by positivity) hσ1 (fun a : ι × ℕ => a.2)
    (fun b : ι × ℕ => b.2 / p) (hdiv_upOp hp2 D ω) tendsto_weight_cofinite_atTop
    (f := lwxLambda p (Fintype.card ι)) lwxLambda_le_sum_sub n).trans (le_of_eq ?_)
  rw [zpow_neg, ← inv_zpow, zpow_natCast]

/-- **[LWX, Theorem 3.16]** (`T`-divisibility form): `c_n ∈ T^{λ(n)}·Λ^{>1/p}`. -/
theorem exists_charCoeff_upOp_eq_T_pow_mul (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    ∃ g : HaloInt p,
      charCoeff (D.op ω) n = HaloInt.T ^ lwxLambda p (Fintype.card ι) n * g :=
  HaloInt.exists_T_pow_mul_of_norm_le (norm_charCoeff_upOp_le hp2 D ω n)

/-- [LWX, Cor 3.18]'s coefficient reading: writing `c_n = ∑_m b_{n,m} T^m`,
`v(b_{n,m}) ≥ max(λ(n) − m, 0)` — i.e. `‖b_{n,m}‖ ≤ p^{m − λ(n)}` (the intrinsic
`‖b_{n,m}‖ ≤ 1` supplies the other branch of the max). -/
theorem norm_coeff_charCoeff_upOp_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) (m : ℤ) :
    ‖(charCoeff (D.op ω) n) m‖ ≤
      (p : ℝ) ^ (m - (lwxLambda p (Fintype.card ι) n : ℤ)) :=
  (HaloInt.norm_le_zpow_iff _ _).mp (norm_charCoeff_upOp_le hp2 D ω n) m

/-! ### Corollary 3.18 -/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The specialized characteristic series `∑_n c_n(T₀) Xⁿ ∈ K⟦X⟧` at a halo point. -/
def specCharSeries (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K)
    (T₀ : K) : PowerSeries K :=
  PowerSeries.mk fun n => HaloInt.specialize ψ T₀ (charCoeff (D.op ω) n)

/-- The specialized coefficient bound ([LWX, Cor 3.18], displayed inequality):
`v(c_n(T₀)) ≥ λ(n)·v(T₀)`. -/
theorem norm_specCharSeries_coeff_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by
  rw [specCharSeries, PowerSeries.coeff_mk]
  exact HaloInt.norm_specialize_le ψ hψ h0 h1 (norm_charCoeff_upOp_le hp2 D ω n)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The constant term of the specialized series is `1` (`c₀ = 1`), anchoring the
polygon at the origin. -/
theorem specCharSeries_coeff_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (ψ : ℤ_[p] →+* K) (T₀ : K) :
    PowerSeries.coeff 0 (specCharSeries D ω ψ T₀) = 1 := by
  rw [specCharSeries, PowerSeries.coeff_mk, charCoeff_zero, HaloInt.specialize_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The slope sequence of the lower-bound polygon:
`k ↦ (⌊k/t⌋ − ⌊k/pt⌋)·v(T₀)` in `negLogNorm` units (`v(T₀) = −log‖T₀‖`). -/
def lwxSlopes (p t : ℕ) (T₀ : K) : ℕ → ℝ :=
  fun k => ((k / t - k / (p * t) : ℕ) : ℝ) * (-Real.log ‖T₀‖)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem monotone_lwxSlopes (p t : ℕ) {T₀ : K} (h1 : ‖T₀‖ < 1) (h0 : 0 < ‖T₀‖) :
    Monotone (lwxSlopes p t T₀ : ℕ → ℝ) := by
  intro a b hab
  have hlog : 0 ≤ -Real.log ‖T₀‖ := by
    have := Real.log_neg h0 h1
    linarith
  refine mul_le_mul_of_nonneg_right ?_ hlog
  have h2 : a / t - a / t / p ≤ b / t - b / t / p :=
    monotone_sub_div p (Nat.div_le_div_right hab)
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm t p] at h2
  exact_mod_cast h2

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The partial-sum identity `∑_{i<k} lwxSlopes i = λ(k)·(−log‖T₀‖)`. -/
theorem sum_lwxSlopes (p t : ℕ) (T₀ : K) (k : ℕ) :
    ∑ i ∈ Finset.range k, lwxSlopes p t T₀ i
      = ((lwxLambda p t k : ℕ) : ℝ) * (-Real.log ‖T₀‖) := by
  simp only [lwxSlopes, lwxLambda]
  rw [← Finset.sum_mul, Nat.cast_sum]

/-- **[LWX, Corollary 3.18]**: at every halo specialization the Newton polygon of the
characteristic series lies on or above the polygon with vertices
`(n, λ(n)·v(T₀))`. -/
theorem isBelow_newtonPolygon_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) :
    (NewtonPolygon₀.ofSlopes (lwxSlopes p (Fintype.card ι) T₀)
        (monotone_lwxSlopes _ _ h1
          ((inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0)) 0).IsBelow
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)) := by
  have hT0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  set f := specCharSeries D ω ψ T₀ with hfdef
  have hc0 : PowerSeries.coeff 0 f = 1 := specCharSeries_coeff_zero D ω ψ T₀
  have hex : ∃ i, coeffVal f i ≠ ⊤ :=
    ⟨0, (coeffVal_zero_of_coeff_zero_eq_one hc0).trans_ne WithTop.coe_ne_top⟩
  have hbound : ∀ k, ‖PowerSeries.coeff k f‖
      ≤ ‖T₀‖ ^ lwxLambda p (Fintype.card ι) k := fun k =>
    norm_specCharSeries_coeff_le hp2 D ω ψ hψ h0 h1 k
  have hlog : ∀ k, PowerSeries.coeff k f ≠ 0 →
      ∑ i ∈ Finset.range k, lwxSlopes p (Fintype.card ι) T₀ i
        ≤ -Real.log ‖PowerSeries.coeff k f‖ := by
    intro k hk
    have h2 := Real.log_le_log (norm_pos_iff.2 hk) (hbound k)
    rw [Real.log_pow] at h2
    rw [sum_lwxSlopes]
    linarith
  have hadm : IsAdmissible (coeffVal f) := by
    refine isAdmissible_of_affine_bound (coeffVal f) (m := 0) (b := 0) fun k a hva => ?_
    have hk : PowerSeries.coeff k f ≠ 0 := fun hcz =>
      WithTop.coe_ne_top (hva.symm.trans (coeffVal_eq_top_iff.mpr hcz))
    have haeq : a = -Real.log ‖PowerSeries.coeff k f‖ :=
      WithTop.coe_inj.mp (hva.symm.trans (coeffVal_of_ne_zero hk))
    have hle1 : ‖PowerSeries.coeff k f‖ ≤ 1 :=
      (hbound k).trans (pow_le_one₀ hT0.le h1.le)
    have := Real.log_nonpos (norm_nonneg _) hle1
    simp only [Algebra.algebraMap_self, RingHom.id_apply, haeq]
    linarith
  refine (isNewtonPolygonOf_powerSeries negLogNorm f hex hadm).isGreatest _ ?_ ?_
  · rw [NewtonPolygon₀.ofSlopes_starting_point,
      newtonPolygon₀_starting_point_of_coeff_zero_eq_one hc0]
  · intro k
    rw [show coeffSeq negLogNorm f = coeffVal f from rfl,
      NewtonPolygon₀.height_ofSlopes, zero_add]
    by_cases hk : PowerSeries.coeff k f = 0
    · rw [pointHeight_eq_top_iff.2 (coeffVal_eq_top_iff.2 hk)]
      exact le_top
    · rw [pointHeight_coe (coeffVal_of_ne_zero hk), Algebra.algebraMap_self_apply]
      exact WithBotTop.coe_le_coe.2 (hlog k hk)

/-! ### The quaternionic shape ([LWX, Prop 3.1(3)], local half) -/

/-- The Iwahori coset representative `v_j = (p 0; jp 1)` of [LWX, §2.5] at `q = p`. -/
def iwahoriRep (j : Fin p) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  !![(p : ℤ_[p]), 0; ((j : ℕ) : ℤ_[p]) * (p : ℤ_[p]), 1]

/-- **[LWX, Prop 3.1, proof]**: a product `u · v_j` with `u` Iwahori-shaped
(`u₀₀, u₁₁` units, `‖u₁₀‖ ≤ p⁻¹`) lands in the `LocalMat` shape
`(pℤ_p, ℤ_p; pℤ_p, ℤ_p^×)`: `δ_{i,j,p} = u_{i,j,p}·v_j ∈ Iw_q (p 0; 0 1) Iw_q`, which is
contained in `(pℤ_p ℤ_p; qℤ_p ℤ_p^×)`. -/
theorem exists_localMat_iwahori_mul (_hp2 : p ≠ 2) (u : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (_h00 : IsUnit (u 0 0)) (h11 : IsUnit (u 1 1)) (_h10 : ‖u 1 0‖ ≤ (p : ℝ)⁻¹)
    (j : Fin p) :
    ∃ δ : LocalMat p, δ.IsUpShape ∧
      (δ.a = (u * iwahoriRep j) 0 0 ∧ δ.b = (u * iwahoriRep j) 0 1) ∧
      (δ.c = (u * iwahoriRep j) 1 0 ∧ (δ.d : ℤ_[p]) = (u * iwahoriRep j) 1 1) := by
  have h00e : (u * iwahoriRep j) 0 0
      = u 0 0 * (p : ℤ_[p]) + u 0 1 * (((j : ℕ) : ℤ_[p]) * p) := by
    simp [iwahoriRep, Matrix.mul_apply, Fin.sum_univ_two]
  have h10e : (u * iwahoriRep j) 1 0
      = u 1 0 * (p : ℤ_[p]) + u 1 1 * (((j : ℕ) : ℤ_[p]) * p) := by
    simp [iwahoriRep, Matrix.mul_apply, Fin.sum_univ_two]
  have h11e : (u * iwahoriRep j) 1 1 = u 1 1 := by
    simp [iwahoriRep, Matrix.mul_apply, Fin.sum_univ_two]
  have hjp : ‖((j : ℕ) : ℤ_[p]) * (p : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    calc ‖((j : ℕ) : ℤ_[p]) * (p : ℤ_[p])‖
        ≤ ‖((j : ℕ) : ℤ_[p])‖ * ‖(p : ℤ_[p])‖ := norm_mul_le _ _
      _ ≤ 1 * (p : ℝ)⁻¹ :=
          mul_le_mul (PadicInt.norm_le_one _) (le_of_eq PadicInt.norm_p)
            (norm_nonneg _) zero_le_one
      _ = (p : ℝ)⁻¹ := one_mul _
  have hnorm : ∀ x y : ℤ_[p],
      ‖x * (p : ℤ_[p]) + y * (((j : ℕ) : ℤ_[p]) * p)‖ ≤ (p : ℝ)⁻¹ := by
    intro x y
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc ‖x * (p : ℤ_[p])‖ ≤ ‖x‖ * ‖(p : ℤ_[p])‖ := norm_mul_le _ _
        _ ≤ 1 * (p : ℝ)⁻¹ :=
            mul_le_mul (PadicInt.norm_le_one x) (le_of_eq PadicInt.norm_p)
              (norm_nonneg _) zero_le_one
        _ = (p : ℝ)⁻¹ := one_mul _
    · calc ‖y * (((j : ℕ) : ℤ_[p]) * p)‖
          ≤ ‖y‖ * ‖((j : ℕ) : ℤ_[p]) * (p : ℤ_[p])‖ := norm_mul_le _ _
        _ ≤ 1 * (p : ℝ)⁻¹ :=
            mul_le_mul (PadicInt.norm_le_one y) hjp (norm_nonneg _) zero_le_one
        _ = (p : ℝ)⁻¹ := one_mul _
  have hd : IsUnit ((u * iwahoriRep j) 1 1) := h11e ▸ h11
  refine ⟨⟨(u * iwahoriRep j) 0 0, (u * iwahoriRep j) 0 1, (u * iwahoriRep j) 1 0,
    hd.unit, ?_⟩, ?_, ⟨rfl, rfl⟩, rfl, hd.unit_spec⟩
  · rw [h10e]
    exact hnorm _ _
  · show ‖(u * iwahoriRep j) 0 0‖ ≤ (p : ℝ)⁻¹
    rw [h00e]
    exact hnorm _ _

/-- Assemble a `UpDatum` from class-set coset data: targets plus Iwahori-shaped
`u`-parts, one per `(i, j)`, matrices `δ i j := u i j · v_j` ([LWX, Prop 3.1]). -/
def UpDatum.ofCosets (hp2 : p ≠ 2) {ι : Type*} (tgt : ι → Fin p → ι)
    (u : ι → Fin p → Matrix (Fin 2) (Fin 2) ℤ_[p])
    (h00 : ∀ i j, IsUnit (u i j 0 0)) (h11 : ∀ i j, IsUnit (u i j 1 1))
    (h10 : ∀ i j, ‖u i j 1 0‖ ≤ (p : ℝ)⁻¹) : UpDatum p ι where
  tgt := tgt
  mat i j := (exists_localMat_iwahori_mul hp2 (u i j) (h00 i j) (h11 i j) (h10 i j) j).choose
  hshape i j :=
    (exists_localMat_iwahori_mul hp2 (u i j) (h00 i j) (h11 i j) (h10 i j) j).choose_spec.1

end LWX
