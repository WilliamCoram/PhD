/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.Finsupp.Weight
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Eval
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Units

/-!
# Möbius series on the Tate algebra

For a *multi-matrix* `γ : ι → M₂(K)` — one matrix per variable, Buzzard's `γ_i := i(γ)` — the
linear factors `L_{γ,i} = c_i z_i + d_i`, the numerators `N_{γ,i} = a_i z_i + b_i`, the inverse
`L_{γ,i}^{-1} = d_i^{-1} ∑ (−c_i/d_i)^m z_i^m` and the Möbius series
`w_{γ,i} = N_{γ,i} L_{γ,i}^{-1}` in the Tate algebra
`K⟨z_i : i ∈ ι⟩ = MvPowerSeries.Restricted K 1`, under the level bounds `‖γ_{i,jk}‖ ≤ 1`,
`‖c_i‖ ≤ ρ`, `‖d_i‖ = 1`, `ρ < 1`. The substitution `f ↦ f ∘ w_γ` is the algebra homomorphism
`mobiusSubst`; Möbius composition `w_{δγ} = w_δ ∘ w_γ` and the automorphy-factor identity
`L_{δγ} = L_γ · (L_δ ∘ w_γ)` are proved as identities of restricted series, and the pointwise
formula `w_γ(x) = (a x + b)/(c x + d)` on the closed unit polydisc. The row-decay predicate
`RowBound σ f` (`‖coeff_t f‖ ≤ σ^{|t|}`) and its closure properties are the bounds that the
compactness of `U_𝔭` consumes.

[Buz07, Lemma 8.1, p. 59]: "Let `γ = ((a b), (c d))` be an element of `M₂(𝒪)` with `|c| < 1`,
`|d| = 1` and `det(γ) ≠ 0`. […] (a) There is a map of rigid spaces `B_r → B^×_{r|π^t|}` which on
points sends `(z_i)` to `(c_i z_i + d_i)` […] (b) There is a map of rigid spaces
`B_r → B_{rm}` which on points sends `(z_i)` to `((a_i z_i + b_i)/(c_i z_i + d_i))`."

## Main definitions

* `AutomorphicForm.MultiBounds ρ γ`: the level bounds of a multi-matrix.
* `AutomorphicForm.lin`, `AutomorphicForm.num`, `AutomorphicForm.linInv`, `AutomorphicForm.mobius`.
* `AutomorphicForm.mobiusSubst hγ`: substitution of the Möbius series, `f ↦ f ∘ w_γ`.
* `AutomorphicForm.RowBound σ f`: `‖coeff t f‖ ≤ σ ^ t.degree` for every multi-index `t`.

## Main results

* `AutomorphicForm.lin_mul_linInv`, `AutomorphicForm.isUnit_lin`: `L_{γ,i}` is a unit with the
  geometric-series inverse.
* `AutomorphicForm.norm_mobius_le_one`: the Möbius series lie in the unit ball.
* `AutomorphicForm.lin_mul`, `AutomorphicForm.mobius_mul`, `AutomorphicForm.mobiusSubst_mul`:
  Möbius composition.
* `AutomorphicForm.aeval_mobius`: the pointwise formula.
* `AutomorphicForm.rowBound_mobius`: `‖coeff_l w_{γ,i}‖ ≤ σ^l` when `‖a_i‖ ≤ σ` and `ρ ≤ σ`.
* `MvPowerSeries.Restricted.aeval_aeval`: composition of substitutions.

Roadmap: §1.2.1, §1.2.4 (the bounds), §1.2.5 (the pointwise formula). Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Mobius.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted Filter Topology

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ : Type*}
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [NormOneClass B] [IsUltrametricDist B]
  [CompleteSpace B]

/-- **Composition of substitutions**: substituting `x` into `f ∘ y` is substituting `y(x)` into
`f`. Source: BGR 5.1.3/5 (uniqueness of continuous homomorphisms out of the Tate algebra). -/
theorem aeval_aeval {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ 1) {y : σ → Restricted K (1 : σ → ℝ)}
    (hy : ∀ i, ‖y i‖ ≤ 1) (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 x hx (aeval 1 y hy f) =
      aeval 1 (fun i => aeval 1 x hx (y i)) (fun i => (norm_aeval_le hx (y i)).trans (hy i)) f := by
  have h : (aeval 1 x hx).comp (aeval 1 y hy) =
      aeval 1 (fun i => aeval 1 x hx (y i)) (fun i => (norm_aeval_le hx (y i)).trans (hy i)) :=
    algHom_ext_of_continuous ((continuous_aeval hx).comp (continuous_aeval hy))
      (continuous_aeval _) fun i => by simp only [AlgHom.comp_apply, aeval_X]
  exact DFunLike.congr_fun h f

omit [CompleteSpace K] in
/-- Evaluation fixes the constants. -/
theorem aeval_C {c : σ → ℝ} {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ c i) (a : K) :
    aeval c x hx (C c a) = algebraMap K B a := by
  rw [← algebraMap_apply]
  exact (aeval c x hx).commutes a

/-- The identity substitution. -/
theorem aeval_X_eq_self (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 (fun i => X K (1 : σ → ℝ) i) (fun i => by simp [norm_X]) f = f := by
  have h : aeval 1 (fun i => X K (1 : σ → ℝ) i) (fun i => by simp [norm_X]) = AlgHom.id K _ :=
    algHom_ext_of_continuous (continuous_aeval _) continuous_id fun i => by
      rw [aeval_X, AlgHom.id_apply]
  exact DFunLike.congr_fun h f

omit [CompleteSpace K] in
/-- Evaluation of a monomial. -/
theorem aeval_monomial {c : σ → ℝ} {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ c i) (t : σ →₀ ℕ) (a : K) :
    aeval c x hx (monomial c t a) = algebraMap K B a * t.prod fun i k => x i ^ k :=
  eval₂_monomial (norm_algebraMap_le_one_mul (B := B)) (norm_prod_pow_le_of_norm_le c x hx) t a

/-- A monomial of the Tate algebra is a constant times a product of powers of the variables. -/
theorem monomial_eq_C_mul_prod (t : σ →₀ ℕ) (a : K) :
    monomial (1 : σ → ℝ) t a = C 1 a * t.prod fun i k => X K 1 i ^ k := by
  have h := aeval_monomial (c := (1 : σ → ℝ)) (x := fun i => X K (1 : σ → ℝ) i)
    (fun i => by simp [norm_X]) t a
  rw [aeval_X_eq_self, algebraMap_apply] at h
  exact h

omit [CompleteSpace K] in
/-- The coefficient functionals of the Tate algebra commute with sums: they are continuous,
`‖a_t‖ ≤ ‖f‖`. -/
theorem hasSum_coeff {α : Type*} {f : α → Restricted K (1 : σ → ℝ)}
    {a : Restricted K (1 : σ → ℝ)} (h : HasSum f a) (t : σ →₀ ℕ) :
    HasSum (fun x => coeff t (f x).1) (coeff t a.1) := by
  let L : Restricted K (1 : σ → ℝ) →+ K :=
    { toFun := fun g => coeff t g.1
      map_zero' := by simp
      map_add' := fun f g => by simp }
  exact h.map L (AddMonoidHomClass.continuous_of_bound L 1 fun g => by
    rw [one_mul]
    exact norm_coeff_le g t)

end MvPowerSeries.Restricted

namespace AutomorphicForm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {ι : Type*}

/-! ### Level bounds of a multi-matrix -/

/-- **The level bounds of a multi-matrix** `γ : ι → M₂(K)`: integral entries, `‖c_i‖ ≤ ρ`,
`‖d_i‖ = 1`, with `0 ≤ ρ < 1`. The image of a level `S ⊆ M₂(L)` under isometric embeddings
satisfies them (`Embeddings.multiBounds_toMulti`). Source: roadmap §1.2 preamble, §1.1.1. -/
structure MultiBounds (ρ : ℝ) (γ : ι → Matrix (Fin 2) (Fin 2) K) : Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  integral : ∀ i j k, ‖γ i j k‖ ≤ 1
  c_le : ∀ i, ‖γ i 1 0‖ ≤ ρ
  d_unit : ∀ i, ‖γ i 1 1‖ = 1

variable {ρ : ℝ} {γ δ : ι → Matrix (Fin 2) (Fin 2) K}

omit [CompleteSpace K] in
theorem MultiBounds.mul (hδ : MultiBounds ρ δ) (hγ : MultiBounds ρ γ) : MultiBounds ρ (δ * γ) := by
  have hsum : ∀ i j k, (δ * γ) i j k = δ i j 0 * γ i 0 k + δ i j 1 * γ i 1 k := fun i j k => by
    rw [Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hγ.rho_nonneg, hγ.rho_lt_one, fun i j k => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hsum]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
      exact (norm_mul_le _ _).trans
        (mul_le_one₀ (hδ.integral _ _ _) (norm_nonneg _) (hγ.integral _ _ _))
  · rw [hsum]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (hγ.integral i 0 0)).trans (hδ.c_le i))
    · rw [norm_mul, hδ.d_unit i, one_mul]
      exact hγ.c_le i
  · have hlt : ‖δ i 1 0 * γ i 0 1‖ < ‖δ i 1 1 * γ i 1 1‖ := by
      rw [norm_mul, norm_mul, hδ.d_unit i, hγ.d_unit i, mul_one]
      exact ((mul_le_of_le_one_right (norm_nonneg _) (hγ.integral i 0 1)).trans
        (hδ.c_le i)).trans_lt hγ.rho_lt_one
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le,
      norm_mul, hδ.d_unit i, hγ.d_unit i, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem MultiBounds.one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    MultiBounds ρ (1 : ι → Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨hρ0, hρ, fun i j k => ?_, fun i => by simpa using hρ0, fun i => by simp⟩
  rcases eq_or_ne j k with rfl | hjk <;> simp [Matrix.one_apply_ne, *]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem MultiBounds.mono {σ : ℝ} (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (hσ : σ < 1) :
    MultiBounds σ γ :=
  ⟨hγ.rho_nonneg.trans hρσ, hσ, hγ.integral, fun i => (hγ.c_le i).trans hρσ, hγ.d_unit⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem MultiBounds.d_ne_zero (hγ : MultiBounds ρ γ) (i : ι) : γ i 1 1 ≠ 0 := fun h => by
  simpa [h] using hγ.d_unit i

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem MultiBounds.norm_c_div_d_lt_one (hγ : MultiBounds ρ γ) (i : ι) :
    ‖γ i 1 0 / γ i 1 1‖ < 1 := by
  rw [norm_div, hγ.d_unit i, div_one]
  exact (hγ.c_le i).trans_lt hγ.rho_lt_one

/-! ### The linear factors, their inverses and the Möbius series -/

variable (γ) in
/-- The linear factor `L_{γ,i} = c_i z_i + d_i`. Source: roadmap §1.2 preamble. -/
noncomputable def lin (i : ι) : Restricted K (1 : ι → ℝ) :=
  C 1 (γ i 1 1) + C 1 (γ i 1 0) * X K 1 i

variable (γ) in
/-- The numerator `N_{γ,i} = a_i z_i + b_i`. Source: roadmap §1.2 preamble. -/
noncomputable def num (i : ι) : Restricted K (1 : ι → ℝ) :=
  C 1 (γ i 0 1) + C 1 (γ i 0 0) * X K 1 i

variable (γ) in
/-- The inverse of the linear factor as a geometric series,
`L_{γ,i}^{-1} = d_i^{-1} ∑_m (−c_i/d_i)^m z_i^m`. Source: roadmap §1.2 preamble ("a restricted
series with `‖coeff_m‖ ≤ ‖c‖^m` because `‖d‖ = 1 > ‖c‖`"). -/
noncomputable def linInv (i : ι) : Restricted K (1 : ι → ℝ) :=
  ∑' m : ℕ, monomial 1 (Finsupp.single i m) ((γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m)

variable (γ) in
/-- **The Möbius series** `w_{γ,i} = (a_i z_i + b_i) · L_{γ,i}^{-1}`. Source: roadmap §1.2 preamble;
[Buz07, Lemma 8.1(b)]. -/
noncomputable def mobius (i : ι) : Restricted K (1 : ι → ℝ) := num γ i * linInv γ i

omit [CompleteSpace K] in
theorem coeff_lin [DecidableEq ι] (i : ι) (t : ι →₀ ℕ) :
    coeff t (lin γ i).1 =
      if t = 0 then γ i 1 1 else if t = Finsupp.single i 1 then γ i 1 0 else 0 := by
  simp only [lin, val_add, val_mul, val_C, val_X, map_add, MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h0 h1 h1
  · exact absurd (h0.symm.trans h1) (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  · simp
  · simp
  · simp

omit [CompleteSpace K] in
theorem coeff_num [DecidableEq ι] (i : ι) (t : ι →₀ ℕ) :
    coeff t (num γ i).1 =
      if t = 0 then γ i 0 1 else if t = Finsupp.single i 1 then γ i 0 0 else 0 := by
  simp only [num, val_add, val_mul, val_C, val_X, map_add, MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h0 h1 h1
  · exact absurd (h0.symm.trans h1) (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  · simp
  · simp
  · simp

omit [CompleteSpace K] in
/-- `a q^m z_i^m = C a · (C q · z_i)^m`. -/
private theorem monomial_single_eq_C_mul_pow (a q : K) (i : ι) (m : ℕ) :
    monomial (1 : ι → ℝ) (Finsupp.single i m) (a * q ^ m) = C 1 a * (C 1 q * X K 1 i) ^ m := by
  apply Subtype.ext
  simp only [val_monomial, val_mul, val_pow, val_C, val_X]
  rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul, MvPowerSeries.X_pow_eq,
    ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial, zero_add,
    mul_one]

omit [CompleteSpace K] in
/-- The geometric ratio `(−c_i/d_i) z_i` has norm less than one. -/
private theorem norm_ratio_lt_one (hγ : MultiBounds ρ γ) (i : ι) :
    ‖C (1 : ι → ℝ) (-(γ i 1 0 / γ i 1 1)) * X K 1 i‖ < 1 := by
  rw [norm_mul, norm_C, norm_X, norm_neg]
  simpa using hγ.norm_c_div_d_lt_one i

omit [CompleteSpace K] in
/-- `c_i z_i + d_i = d_i (1 − (−c_i/d_i) z_i)`. -/
private theorem lin_eq (hγ : MultiBounds ρ γ) (i : ι) :
    lin γ i = C 1 (γ i 1 1) * (1 - C 1 (-(γ i 1 0 / γ i 1 1)) * X K 1 i) := by
  have hq : γ i 1 1 * (-(γ i 1 0 / γ i 1 1)) = -γ i 1 0 := by
    rw [mul_neg, mul_div_cancel₀ _ (hγ.d_ne_zero i)]
  rw [lin, mul_sub, mul_one, ← mul_assoc, ← map_mul, hq, map_neg, neg_mul, sub_neg_eq_add]

/-- The inverse as `d_i^{-1}` times a geometric series. -/
private theorem linInv_eq (hγ : MultiBounds ρ γ) (i : ι) :
    linInv γ i = C 1 (γ i 1 1)⁻¹ * ∑' m : ℕ, (C 1 (-(γ i 1 0 / γ i 1 1)) * X K 1 i) ^ m :=
  (tsum_congr fun m => monomial_single_eq_C_mul_pow _ _ i m).trans
    ((summable_geometric_of_norm_lt_one (norm_ratio_lt_one hγ i)).tsum_mul_left _)

theorem hasSum_linInv (hγ : MultiBounds ρ γ) (i : ι) :
    HasSum (fun m : ℕ => monomial 1 (Finsupp.single i m)
      ((γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m)) (linInv γ i) := by
  have hs : Summable fun m : ℕ => monomial (1 : ι → ℝ) (Finsupp.single i m)
      ((γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m) :=
    ((summable_geometric_of_norm_lt_one (norm_ratio_lt_one hγ i)).mul_left
      (C 1 (γ i 1 1)⁻¹)).congr fun m => (monomial_single_eq_C_mul_pow _ _ i m).symm
  exact hs.hasSum

theorem coeff_linInv [DecidableEq ι] (hγ : MultiBounds ρ γ) (i : ι) (t : ι →₀ ℕ) :
    coeff t (linInv γ i).1 =
      if t = Finsupp.single i (t i) then (γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ (t i) else 0 := by
  have h := hasSum_coeff (hasSum_linInv hγ i) t
  simp only [val_monomial, MvPowerSeries.coeff_monomial] at h
  split_ifs with ht
  · have h2 := hasSum_single (f := fun m : ℕ => if t = Finsupp.single i m then
        (γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m else 0) (t i) fun m hm =>
      if_neg fun htm => hm (by rw [htm, Finsupp.single_eq_same])
    rw [h.unique h2]
    exact if_pos ht
  · have hz : ∀ m : ℕ, (if t = Finsupp.single i m then
        (γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m else (0 : K)) = 0 :=
      fun m => if_neg fun htm => ht (by rw [htm, Finsupp.single_eq_same])
    simp only [hz] at h
    exact h.unique hasSum_zero

theorem lin_mul_linInv (hγ : MultiBounds ρ γ) (i : ι) : lin γ i * linInv γ i = 1 := by
  rw [lin_eq hγ i, linInv_eq hγ i, mul_mul_mul_comm, ← map_mul, mul_inv_cancel₀ (hγ.d_ne_zero i),
    map_one, one_mul]
  exact mul_neg_geom_series _ (norm_ratio_lt_one hγ i)

theorem isUnit_lin (hγ : MultiBounds ρ γ) (i : ι) : IsUnit (lin γ i) :=
  IsUnit.of_mul_eq_one (linInv γ i) (lin_mul_linInv hγ i)

theorem inverse_lin (hγ : MultiBounds ρ γ) (i : ι) : Ring.inverse (lin γ i) = linInv γ i := by
  rw [Ring.inverse_of_isUnit (isUnit_lin hγ i)]
  exact Units.inv_eq_of_mul_eq_one_right (lin_mul_linInv hγ i)

omit [CompleteSpace K] in
theorem norm_lin_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖lin γ i‖ ≤ 1 := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_C]
    exact hγ.integral i 1 1
  · rw [norm_mul, norm_C, norm_X]
    simpa using hγ.integral i 1 0

omit [CompleteSpace K] in
theorem norm_num_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖num γ i‖ ≤ 1 := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_C]
    exact hγ.integral i 0 1
  · rw [norm_mul, norm_C, norm_X]
    simpa using hγ.integral i 0 0

theorem norm_linInv_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖linInv γ i‖ ≤ 1 := by
  classical
  refine (norm_le_iff_forall_norm_coeff_le _).mpr fun t => ?_
  rw [coeff_linInv hγ i t]
  split_ifs
  · rw [norm_mul, norm_inv, hγ.d_unit i, inv_one, one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ((norm_neg _).le.trans (hγ.norm_c_div_d_lt_one i).le)
  · simp

/-- The Möbius series lie in the unit ball, so they can be substituted. Source: roadmap §1.2.1
("the coefficients of `w_γ` lie in the unit ball, so `w_γ` maps the closed unit polydisc to
itself"). -/
theorem norm_mobius_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖mobius γ i‖ ≤ 1 :=
  (norm_mul_le _ _).trans (mul_le_one₀ (norm_num_le_one hγ i) (norm_nonneg _)
    (norm_linInv_le_one hγ i))

/-- **Substitution of the Möbius series**, `f ↦ f ∘ w_γ`, a `K`-algebra endomorphism of the Tate
algebra of norm at most `1`. Source: roadmap §1.2.1 (the substitution of PFA §4.1.4). -/
noncomputable def mobiusSubst (hγ : MultiBounds ρ γ) :
    Restricted K (1 : ι → ℝ) →ₐ[K] Restricted K (1 : ι → ℝ) :=
  aeval 1 (mobius γ) (norm_mobius_le_one hγ)

theorem mobiusSubst_apply (hγ : MultiBounds ρ γ) (f : Restricted K (1 : ι → ℝ)) :
    mobiusSubst hγ f = aeval 1 (mobius γ) (norm_mobius_le_one hγ) f :=
  rfl

@[simp] theorem mobiusSubst_X (hγ : MultiBounds ρ γ) (i : ι) :
    mobiusSubst hγ (X K 1 i) = mobius γ i :=
  aeval_X _ i

theorem norm_mobiusSubst_le (hγ : MultiBounds ρ γ) (f : Restricted K (1 : ι → ℝ)) :
    ‖mobiusSubst hγ f‖ ≤ ‖f‖ :=
  norm_aeval_le _ f

theorem continuous_mobiusSubst (hγ : MultiBounds ρ γ) : Continuous (mobiusSubst hγ) :=
  continuous_aeval _

/-! ### Möbius composition -/

/-- Substitution fixes the constants. -/
private theorem mobiusSubst_C (hγ : MultiBounds ρ γ) (a : K) :
    mobiusSubst hγ (C (1 : ι → ℝ) a) = C 1 a := by
  have h := (mobiusSubst hγ).commutes a
  rwa [algebraMap_apply] at h

/-- `L_{γ,i} · w_{γ,i} = N_{γ,i}`. -/
private theorem lin_mul_mobius (hγ : MultiBounds ρ γ) (i : ι) : lin γ i * mobius γ i = num γ i := by
  rw [mobius, mul_left_comm, lin_mul_linInv hγ i, mul_one]

/-- **The automorphy-factor identity** `L_{δγ} = L_γ · (L_δ ∘ w_γ)`, i.e. the cocycle
`j(δγ, z) = j(γ, z) j(δ, γz)` for `j(γ, z) = cz + d`. Source: roadmap §1.2.1. -/
theorem lin_mul (hγ : MultiBounds ρ γ) (δ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    lin (δ * γ) i = lin γ i * mobiusSubst hγ (lin δ i) := by
  have hsub : mobiusSubst hγ (lin δ i) = C 1 (δ i 1 1) + C 1 (δ i 1 0) * mobius γ i := by
    rw [lin, map_add, map_mul, mobiusSubst_C, mobiusSubst_C, mobiusSubst_X]
  rw [hsub, mul_add, ← mul_assoc, mul_comm (lin γ i) (C 1 (δ i 1 0)), mul_assoc,
    lin_mul_mobius hγ i]
  simp only [lin, num, Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

theorem num_mul (hγ : MultiBounds ρ γ) (δ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    num (δ * γ) i = lin γ i * mobiusSubst hγ (num δ i) := by
  have hsub : mobiusSubst hγ (num δ i) = C 1 (δ i 0 1) + C 1 (δ i 0 0) * mobius γ i := by
    rw [num, map_add, map_mul, mobiusSubst_C, mobiusSubst_C, mobiusSubst_X]
  rw [hsub, mul_add, ← mul_assoc, mul_comm (lin γ i) (C 1 (δ i 0 0)), mul_assoc,
    lin_mul_mobius hγ i]
  simp only [lin, num, Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

/-- **Möbius composition** `w_{δγ} = w_δ ∘ w_γ`. Source: roadmap §1.2.1. -/
theorem mobius_mul (hγ : MultiBounds ρ γ) (hδ : MultiBounds ρ δ) (i : ι) :
    mobius (δ * γ) i = mobiusSubst hγ (mobius δ i) := by
  have h1 : lin (δ * γ) i * linInv (δ * γ) i = 1 := lin_mul_linInv (hδ.mul hγ) i
  have h2 : mobiusSubst hγ (lin δ i) * mobiusSubst hγ (linInv δ i) = 1 := by
    rw [← map_mul, lin_mul_linInv hδ i, map_one]
  rw [mobius, mobius, map_mul, num_mul hγ δ i]
  calc lin γ i * mobiusSubst hγ (num δ i) * linInv (δ * γ) i
      = lin γ i * mobiusSubst hγ (num δ i) * linInv (δ * γ) i *
          (mobiusSubst hγ (lin δ i) * mobiusSubst hγ (linInv δ i)) := by rw [h2, mul_one]
    _ = mobiusSubst hγ (num δ i) * mobiusSubst hγ (linInv δ i) *
          (lin (δ * γ) i * linInv (δ * γ) i) := by
        rw [lin_mul hγ δ i]
        ring
    _ = mobiusSubst hγ (num δ i) * mobiusSubst hγ (linInv δ i) := by rw [h1, mul_one]

theorem mobius_one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (i : ι) :
    mobius (1 : ι → Matrix (Fin 2) (Fin 2) K) i = X K 1 i := by
  have hl : lin (1 : ι → Matrix (Fin 2) (Fin 2) K) i = 1 := by
    simp [lin]
  have hli : linInv (1 : ι → Matrix (Fin 2) (Fin 2) K) i = 1 := by
    simpa [hl] using lin_mul_linInv (MultiBounds.one (K := K) (ι := ι) hρ0 hρ) i
  simp [mobius, hli, num]

/-- Substitution is contravariant: `f ∘ w_{δγ} = (f ∘ w_δ) ∘ w_γ`. Source: roadmap §1.2.1. -/
theorem mobiusSubst_mul (hγ : MultiBounds ρ γ) (hδ : MultiBounds ρ δ) :
    mobiusSubst (hδ.mul hγ) = (mobiusSubst hγ).comp (mobiusSubst hδ) :=
  algHom_ext_of_continuous (continuous_mobiusSubst _)
    ((continuous_mobiusSubst hγ).comp (continuous_mobiusSubst hδ)) fun i => by
      rw [mobiusSubst_X, AlgHom.comp_apply, mobiusSubst_X, mobius_mul hγ hδ i]

theorem mobiusSubst_one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    mobiusSubst (MultiBounds.one (K := K) (ι := ι) hρ0 hρ) = AlgHom.id K _ :=
  algHom_ext_of_continuous (continuous_mobiusSubst _) continuous_id fun i => by
    rw [mobiusSubst_X, mobius_one hρ0 hρ i, AlgHom.id_apply]

/-! ### The pointwise formula on the closed unit polydisc -/

/-- Evaluation fixes the constants. -/
theorem aeval_C_self {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (a : K) :
    aeval 1 x hx (C (1 : ι → ℝ) a) = a := by
  simpa [algebraMap_apply] using (aeval 1 x hx).commutes a

theorem aeval_lin {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (lin γ i) = γ i 1 0 * x i + γ i 1 1 := by
  rw [lin, map_add, map_mul, aeval_C_self, aeval_C_self, aeval_X, add_comm]

theorem aeval_num {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (num γ i) = γ i 0 0 * x i + γ i 0 1 := by
  rw [num, map_add, map_mul, aeval_C_self, aeval_C_self, aeval_X, add_comm]

theorem norm_aeval_lin (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    ‖aeval 1 x hx (lin γ i)‖ = 1 := by
  rw [aeval_lin]
  have hlt : ‖γ i 1 0 * x i‖ < ‖γ i 1 1‖ := by
    rw [hγ.d_unit i, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hx i)).trans_lt
      ((hγ.c_le i).trans_lt hγ.rho_lt_one)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le, hγ.d_unit i]

/-- **The pointwise formula** `w_{γ,i}(x) = (a_i x_i + b_i)/(c_i x_i + d_i)` on the closed unit
polydisc. Source: roadmap §1.2.5; [Buz07, Lemma 8.1(b)]. -/
theorem aeval_mobius (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (mobius γ i) = (γ i 0 0 * x i + γ i 0 1) / (γ i 1 0 * x i + γ i 1 1) := by
  have h1 : aeval 1 x hx (lin γ i) * aeval 1 x hx (linInv γ i) = 1 := by
    rw [← map_mul, lin_mul_linInv hγ i, map_one]
  rw [aeval_lin] at h1
  rw [mobius, map_mul, aeval_num, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

theorem norm_aeval_mobius_le_one (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1)
    (i : ι) : ‖aeval 1 x hx (mobius γ i)‖ ≤ 1 :=
  (norm_aeval_le hx _).trans (norm_mobius_le_one hγ i)

/-- Evaluating a substituted series: `(f ∘ w_γ)(x) = f(w_γ(x))`. Source: roadmap §1.2.5. -/
theorem aeval_mobiusSubst (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : Restricted K (1 : ι → ℝ)) :
    aeval 1 x hx (mobiusSubst hγ f) =
      aeval 1 (fun i => aeval 1 x hx (mobius γ i)) (norm_aeval_mobius_le_one hγ hx) f :=
  aeval_aeval hx _ f

/-! ### Row bounds -/

variable (σ : ℝ) in
/-- **Row decay at rate `σ`**: `‖coeff_t f‖ ≤ σ^{|t|}` for every multi-index `t`, `|t| = t.degree`
the total degree. The bound the compactness of `U_𝔭` consumes (roadmap §1.2.4, §3.5.1; [Jac03,
Lemma 2.7]: "every coefficient of `x` is divisible by `3`"). -/
def RowBound (f : Restricted K (1 : ι → ℝ)) : Prop :=
  ∀ t : ι →₀ ℕ, ‖coeff t f.1‖ ≤ σ ^ t.degree

variable {σ : ℝ}

omit [CompleteSpace K] in
theorem RowBound.norm_le_one (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {f : Restricted K (1 : ι → ℝ)}
    (hf : RowBound σ f) : ‖f‖ ≤ 1 :=
  (norm_le_iff_forall_norm_coeff_le f).mpr fun t => (hf t).trans (pow_le_one₀ hσ0 hσ1)

omit [CompleteSpace K] in
theorem RowBound.mono {σ' : ℝ} (hσ0 : 0 ≤ σ) (hσσ' : σ ≤ σ') {f : Restricted K (1 : ι → ℝ)}
    (hf : RowBound σ f) : RowBound σ' f :=
  fun t => (hf t).trans (pow_le_pow_left₀ hσ0 hσσ' _)

omit [CompleteSpace K] in
theorem rowBound_C (hσ0 : 0 ≤ σ) {a : K} (ha : ‖a‖ ≤ 1) : RowBound σ (C (1 : ι → ℝ) a) := by
  classical
  intro t
  rw [val_C, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h
    simpa using ha
  · simpa using pow_nonneg hσ0 _

omit [CompleteSpace K] in
theorem rowBound_one (hσ0 : 0 ≤ σ) : RowBound σ (1 : Restricted K (1 : ι → ℝ)) :=
  rowBound_C hσ0 (by simp)

omit [CompleteSpace K] in
theorem RowBound.smul {f : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f) {a : K} (ha : ‖a‖ ≤ 1) :
    RowBound σ (a • f) := fun t => by
  rw [val_smul, MvPowerSeries.coeff_smul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hf t)

omit [CompleteSpace K] in
/-- Row bounds are closed under products: the ultrametric convolution with `|t₁| + |t₂| = |t|`.
Source: roadmap §1.2.4 ("products of series with this property have it"). -/
theorem RowBound.mul (hσ0 : 0 ≤ σ) {f g : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f)
    (hg : RowBound σ g) : RowBound σ (f * g) := by
  classical
  intro t
  rw [val_mul, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hσ0 _) fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [norm_mul, ← hp, map_add, pow_add]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (pow_nonneg hσ0 _)

omit [CompleteSpace K] in
theorem RowBound.pow (hσ0 : 0 ≤ σ) {f : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f) (n : ℕ) :
    RowBound σ (f ^ n) := by
  induction n with
  | zero => simpa using rowBound_one hσ0
  | succ n ih => simpa [pow_succ] using ih.mul hσ0 hf

omit [CompleteSpace K] in
theorem RowBound.prod (hσ0 : 0 ≤ σ) {κ : Type*} (s : Finset κ) {f : κ → Restricted K (1 : ι → ℝ)}
    (hf : ∀ k ∈ s, RowBound σ (f k)) : RowBound σ (∏ k ∈ s, f k) :=
  Finset.prod_induction _ (RowBound σ) (fun _ _ ha hb => ha.mul hσ0 hb) (rowBound_one hσ0) hf

omit [CompleteSpace K] in
theorem rowBound_lin (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (i : ι) : RowBound σ (lin γ i) := by
  classical
  intro t
  rw [coeff_lin]
  split_ifs with h0 h1
  · subst h0
    simp [hγ.d_unit i]
  · subst h1
    simpa using (hγ.c_le i).trans hρσ
  · simpa using pow_nonneg (hγ.rho_nonneg.trans hρσ) _

theorem rowBound_linInv (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (i : ι) :
    RowBound σ (linInv γ i) := by
  classical
  intro t
  rw [coeff_linInv hγ i t]
  split_ifs with ht
  · have hdeg : t.degree = t i :=
      calc t.degree = (Finsupp.single i (t i)).degree := by rw [← ht]
        _ = t i := Finsupp.degree_single _ _
    rw [hdeg, norm_mul, norm_inv, hγ.d_unit i, inv_one, one_mul, norm_pow, norm_neg, norm_div,
      hγ.d_unit i, div_one]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hγ.c_le i).trans hρσ) _
  · simpa using pow_nonneg (hγ.rho_nonneg.trans hρσ) _

omit [CompleteSpace K] in
theorem rowBound_num (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) {i : ι} (ha : ‖γ i 0 0‖ ≤ σ) :
    RowBound σ (num γ i) := by
  classical
  intro t
  rw [coeff_num]
  split_ifs with h0 h1
  · subst h0
    simpa using hγ.integral i 0 1
  · subst h1
    simpa using ha
  · simpa using pow_nonneg (hγ.rho_nonneg.trans hρσ) _

/-- **The row bound of the Möbius series**: `‖coeff_l w_{γ,i}‖ ≤ σ^l` when `‖a_i‖ ≤ σ` and `ρ ≤ σ`
(the constant term `b_i/d_i` only needs `≤ 1 = σ^0`). Source: roadmap §1.2.4. -/
theorem rowBound_mobius (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) {i : ι} (ha : ‖γ i 0 0‖ ≤ σ) :
    RowBound σ (mobius γ i) :=
  (rowBound_num hγ hρσ ha).mul (hγ.rho_nonneg.trans hρσ) (rowBound_linInv hγ hρσ i)

end AutomorphicForm
