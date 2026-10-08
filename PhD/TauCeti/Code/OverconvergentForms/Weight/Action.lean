/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Module.LinearMap.End
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Sum
import PhD.TauCeti.Code.OverconvergentForms.Weight.Mobius

/-!
# The weight action on the Tate algebra: the engine

A *weight datum* on a monoid `S` is a multi-matrix representation `S →* (ι → M₂(K))` with level
bounds `ρ` together with an *automorphy factor* `j : S → K⟨z⟩` of row decay `ρ` satisfying
`j(1) = 1` and the cocycle `j(δγ) = j(γ) · (j(δ) ∘ w_γ)`. It defines the operators
`f ∣ γ := j(γ) · (f ∘ w_γ)` on the Tate algebra `K⟨z_i : i ∈ ι⟩`, which are `K`-linear of norm at
most `1`, satisfy `f ∣ 1 = f` and `(f ∣ δ) ∣ γ = f ∣ (δγ)`, send the monomial `z^r` to
`j(γ) ∏ w_{γ,i}^{r_i}` (the matrix of the action is the coefficient array of this family, Jacobs's
Proposition 2.6), and have the row bound `‖coeff_t (z^r ∣ γ)‖ ≤ σ^{|t|}` as soon as `‖a_i‖ ≤ σ` and
`ρ ≤ σ` (Jacobs's Lemma 2.7). The right action is packaged as `DistribMulAction Sᵐᵒᵖ A` (README
convention 2). Twisting by a norm-one character, pulling back along a monoid homomorphism (the
single-place instance of §1.4.2) and the product over finitely many places (§1.4.1) are weight
data again.

The weights of the roadmap (`AnalyticWeight`, `Weight/Expansion.lean`) *produce* weight data, the
cocycle being derived from multiplicativity and the identity theorem; this file never looks at a
character.

[Buz07, §10, pp. 71–72]: "if `t` is good for `(κ, r)` then we can define a right action of `M_t` on
`A_{κ,r}` […] `(h.γ)(z, x) := n(cz + d, x) (v(det(γ))(x)) h((az + b)/(cz + d), x)`. […] It is
elementary to check that for fixed `γ ∈ M_t`, the map `A_{κ,r} → A_{κ,r}` defined by `h ↦ h.γ` is a
continuous `𝒪(X)`-module homomorphism […]. The fact that `n` and `v` take values in elements of
`𝒪(X)^×` with supremum norm `1` easily implies that `γ : A_{κ,r} → A_{κ,r}` is norm-decreasing."
[Jac03, Proposition 2.6, p. 29]: "The generating function of the operator `∥_κ ((a b), (c d))` is
given by `κ(cx + d) / ((cx + d)(cx + d − axy − by))`."

## Main definitions

* `AutomorphicForm.WeightData S K ι ρ`: the engine record.
* `AutomorphicForm.WeightData.kappaSlash W γ`: the operator `f ↦ j(γ) · (f ∘ w_γ)`.
* `AutomorphicForm.WeightData.kappaSlashAction`: the right action `DistribMulAction Sᵐᵒᵖ A`.
* `AutomorphicForm.WeightData.twist`, `comap`, `restrictRadius`, `pi`.

## Main results

* `AutomorphicForm.WeightData.kappaSlash_one`, `kappaSlash_mul`: the action laws.
* `AutomorphicForm.WeightData.norm_kappaSlash_apply_le`: norm at most one (the operator norm
  itself is the `p`-adic-functional-analysis roadmap's §1.1 and is not stated here).
* `AutomorphicForm.WeightData.kappaSlash_monomial`: `z^r ∣ γ = j(γ) ∏ w_{γ,i}^{r_i}`.
* `AutomorphicForm.WeightData.norm_coeff_kappaSlash_monomial_le`: the row bound.

Roadmap: §1.2.4–§1.2.6, §1.2.8, §1.4. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Action.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted Filter Topology

namespace AutomorphicForm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {ι : Type*}

/-- `mobiusSubst` depends only on the multi-matrix, not on the bounds used to build it. -/
theorem mobiusSubst_congr {ρ ρ' : ℝ} {γ γ' : ι → Matrix (Fin 2) (Fin 2) K} (h : γ = γ')
    (hγ : MultiBounds ρ γ) (hγ' : MultiBounds ρ' γ') : mobiusSubst hγ = mobiusSubst hγ' := by
  subst h
  rfl

/-- **A weight datum** on a monoid `S`: a multi-matrix representation with level bounds `ρ` and an
automorphy factor of row decay `ρ` satisfying the cocycle `j(δγ) = j(γ) · (j(δ) ∘ w_γ)`. The
engine from which the action and its laws are proved once; `AnalyticWeight.toWeightData` derives
the cocycle from a character. Source: roadmap §1.2.4 (`j_κ(γ)`), §1.2.6 (the cocycle). -/
structure WeightData (S : Type*) [Monoid S] (K : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (ι : Type*) (ρ : ℝ) where
  /-- The multi-matrix of `γ`: Buzzard's `(γ_i)_{i ∈ I}`. -/
  toMulti : S →* (ι → Matrix (Fin 2) (Fin 2) K)
  /-- The level bounds. -/
  bounds : ∀ γ, MultiBounds ρ (toMulti γ)
  /-- The automorphy factor `j(γ)`. -/
  autFactor : S → Restricted K (1 : ι → ℝ)
  /-- Row decay of the automorphy factor at the level. -/
  rowBound_autFactor : ∀ γ, RowBound ρ (autFactor γ)
  autFactor_one : autFactor 1 = 1
  /-- The cocycle `j(δγ) = j(γ) · (j(δ) ∘ w_γ)`. -/
  autFactor_mul : ∀ γ δ, autFactor (δ * γ) = autFactor γ * mobiusSubst (bounds γ) (autFactor δ)

namespace WeightData

variable {S : Type*} [Monoid S] {ρ : ℝ}

theorem rho_nonneg (W : WeightData S K ι ρ) : 0 ≤ ρ := (W.bounds 1).rho_nonneg

theorem rho_lt_one (W : WeightData S K ι ρ) : ρ < 1 := (W.bounds 1).rho_lt_one

variable (W : WeightData S K ι ρ)

theorem norm_autFactor_le (γ : S) : ‖W.autFactor γ‖ ≤ 1 :=
  (W.rowBound_autFactor γ).norm_le_one W.rho_nonneg W.rho_lt_one.le

/-- **The weight action** of `γ` on the Tate algebra: `f ∣ γ := j(γ) · (f ∘ w_γ)`, a bounded
`K`-linear operator. Source: roadmap §1.2.5; [Buz07, §10, p. 72]; [Jac03, Definition 1.27]. -/
noncomputable def kappaSlash (γ : S) : Restricted K (1 : ι → ℝ) →L[K] Restricted K (1 : ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => W.autFactor γ * mobiusSubst (W.bounds γ) f
      map_add' := fun f g => by rw [map_add, mul_add]
      map_smul' := fun a f => by rw [map_smul, mul_smul_comm, RingHom.id_apply] }
    1 fun f => by
      change ‖W.autFactor γ * mobiusSubst (W.bounds γ) f‖ ≤ 1 * ‖f‖
      rw [norm_mul, one_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_autFactor_le γ)).trans
        (norm_mobiusSubst_le _ f)

theorem kappaSlash_apply (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    W.kappaSlash γ f = W.autFactor γ * mobiusSubst (W.bounds γ) f :=
  rfl

/-- The action is norm-decreasing. Source: [Buz07, §10, p. 72]. -/
theorem norm_kappaSlash_apply_le (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    ‖W.kappaSlash γ f‖ ≤ ‖f‖ := by
  rw [kappaSlash_apply, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_autFactor_le γ)).trans
    (norm_mobiusSubst_le _ f)

/-- `f ∣ 1 = f`. Source: roadmap §1.2.6. -/
theorem kappaSlash_one : W.kappaSlash 1 = ContinuousLinearMap.id K _ := by
  ext f
  rw [kappaSlash_apply, W.autFactor_one, one_mul,
    mobiusSubst_congr (map_one W.toMulti) (W.bounds 1) (MultiBounds.one W.rho_nonneg W.rho_lt_one),
    mobiusSubst_one W.rho_nonneg W.rho_lt_one]
  rfl

/-- `(f ∣ δ) ∣ γ = f ∣ (δγ)`: the weight action is a right action. Source: roadmap §1.2.6; [Jac03,
Definition 1.27] ("It is an easy check that `Σ_α` is a monoid and that `∥_κ` is a right action"). -/
theorem kappaSlash_mul (γ δ : S) :
    W.kappaSlash (δ * γ) = (W.kappaSlash γ).comp (W.kappaSlash δ) := by
  ext f
  simp only [ContinuousLinearMap.comp_apply, kappaSlash_apply]
  rw [W.autFactor_mul γ δ, mobiusSubst_congr (map_mul W.toMulti δ γ) (W.bounds (δ * γ))
    ((W.bounds δ).mul (W.bounds γ)), mobiusSubst_mul (W.bounds γ) (W.bounds δ), AlgHom.comp_apply,
    map_mul, mul_assoc]

/-- **The action on monomials**: `z^r ∣ γ = j(γ) ∏_i w_{γ,i}^{r_i}` — the columns of the matrix of
the action, Jacobs's generating function read off column by column. Source: roadmap §1.2.5;
[Jac03, Proposition 2.6]. -/
theorem kappaSlash_monomial (γ : S) (r : ι →₀ ℕ) :
    W.kappaSlash γ (monomial 1 r 1) =
      W.autFactor γ * r.prod fun i k => mobius (W.toMulti γ) i ^ k := by
  rw [kappaSlash_apply, mobiusSubst_apply, aeval_monomial, map_one, one_mul]

/-- **The row bound**: if `‖a_i‖ ≤ σ` for every `i` and `ρ ≤ σ`, then every matrix coefficient of
the action satisfies `‖coeff_t (z^r ∣ γ)‖ ≤ σ^{|t|}`. Source: roadmap §1.2.4; [Jac03, Lemma 2.7]
("it suffices to prove that every entry in `D(1/3) ε_{k,l}` is in `𝒪_3`"). -/
theorem norm_coeff_kappaSlash_monomial_le (γ : S) {σ : ℝ} (hρσ : ρ ≤ σ)
    (ha : ∀ i, ‖W.toMulti γ i 0 0‖ ≤ σ) (t r : ι →₀ ℕ) :
    ‖coeff t (W.kappaSlash γ (monomial 1 r 1)).1‖ ≤ σ ^ t.degree := by
  have hσ0 : 0 ≤ σ := W.rho_nonneg.trans hρσ
  rw [kappaSlash_monomial]
  exact ((W.rowBound_autFactor γ).mono W.rho_nonneg hρσ).mul hσ0
    (RowBound.prod hσ0 r.support fun i _ => (rowBound_mobius (W.bounds γ) hρσ (ha i)).pow hσ0 (r i))
    t

/-- Every matrix coefficient of the action lies in the unit ball. Source: roadmap §1.2.4 ("the
coefficients of `H_γ` lie in the unit ball"). -/
theorem norm_coeff_kappaSlash_monomial_le_one (γ : S) (t r : ι →₀ ℕ) :
    ‖coeff t (W.kappaSlash γ (monomial 1 r 1)).1‖ ≤ 1 :=
  (W.norm_coeff_kappaSlash_monomial_le γ W.rho_lt_one.le (fun i => (W.bounds γ).integral i 0 0)
    t r).trans_eq (one_pow _)

/-- The columns of the matrix tend to zero. Source: roadmap §1.2.4 ("for fixed `r` they tend to `0`
in `m`"). -/
theorem tendsto_norm_coeff_kappaSlash_monomial (γ : S) (r : ι →₀ ℕ) :
    Tendsto (fun t : ι →₀ ℕ => ‖coeff t (W.kappaSlash γ (monomial 1 r 1)).1‖) cofinite (𝓝 0) :=
  tendsto_norm_coeff_cofinite _

/-- The action as a monoid homomorphism from the opposite monoid into the endomorphisms. -/
noncomputable def kappaSlashHom : Sᵐᵒᵖ →* Module.End K (Restricted K (1 : ι → ℝ)) where
  toFun γ := (W.kappaSlash γ.unop : Restricted K (1 : ι → ℝ) →ₗ[K] Restricted K (1 : ι → ℝ))
  map_one' := by
    rw [MulOpposite.unop_one, kappaSlash_one]
    rfl
  map_mul' γ δ := by
    rw [MulOpposite.unop_mul, kappaSlash_mul]
    rfl

/-- **The right action** of `S` on the Tate algebra, as a `MulOpposite` action (README convention
2). A definition, not an instance: several weights act on the same algebra. -/
@[instance_reducible]
noncomputable def kappaSlashAction : DistribMulAction Sᵐᵒᵖ (Restricted K (1 : ι → ℝ)) :=
  DistribMulAction.compHom _ W.kappaSlashHom

theorem op_smul_def (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    letI := W.kappaSlashAction
    MulOpposite.op γ • f = W.kappaSlash γ f :=
  rfl

theorem smulCommClass :
    letI := W.kappaSlashAction
    SMulCommClass K Sᵐᵒᵖ (Restricted K (1 : ι → ℝ)) := by
  letI := W.kappaSlashAction
  exact ⟨fun a γ f => ((W.kappaSlash γ.unop).map_smul a f).symm⟩

/-! ### Restriction of the radius, twists and pullbacks -/

/-- A weight datum at level `ρ` is one at every `ρ ≤ ρ' < 1`. Source: roadmap §1.2.8. -/
noncomputable def restrictRadius {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) : WeightData S K ι ρ' where
  toMulti := W.toMulti
  bounds γ := (W.bounds γ).mono hρρ' hρ'
  autFactor := W.autFactor
  rowBound_autFactor γ := (W.rowBound_autFactor γ).mono W.rho_nonneg hρρ'
  autFactor_one := W.autFactor_one
  autFactor_mul := W.autFactor_mul

theorem restrictRadius_kappaSlash {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) (γ : S) :
    (W.restrictRadius hρρ' hρ').kappaSlash γ = W.kappaSlash γ :=
  rfl

/-- **The twist** by a norm-one character `χ : S →* Kˣ`: `f ↦ χ(γ) • (f ∣ γ)`. The character
`γ ↦ v(det γ)` and a nebentypus pulled back through `d` are the instances. Source: roadmap
§1.2.8. -/
noncomputable def twist (χ : S →* Kˣ) (hχ : ∀ γ, ‖(χ γ : K)‖ = 1) : WeightData S K ι ρ where
  toMulti := W.toMulti
  bounds := W.bounds
  autFactor γ := (χ γ : K) • W.autFactor γ
  rowBound_autFactor γ := (W.rowBound_autFactor γ).smul (hχ γ).le
  autFactor_one := by rw [map_one, Units.val_one, one_smul, W.autFactor_one]
  autFactor_mul γ δ := by
    simp only [map_mul, Units.val_mul, W.autFactor_mul, map_smul]
    rw [smul_mul_smul_comm (χ γ : K) (W.autFactor γ) (χ δ : K)
      (mobiusSubst (W.bounds γ) (W.autFactor δ)), mul_comm (χ δ : K) (χ γ : K)]

theorem twist_kappaSlash (χ : S →* Kˣ) (hχ : ∀ γ, ‖(χ γ : K)‖ = 1) (γ : S) :
    (W.twist χ hχ).kappaSlash γ = (χ γ : K) • W.kappaSlash γ := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [smul_apply, kappaSlash_apply, kappaSlash_apply]
  exact smul_mul_assoc (χ γ : K) (W.autFactor γ) _

/-- **Pullback** along a monoid homomorphism `φ : S' →* S`. The single-place instance of §1.4.2
(`S_𝔮` acting trivially for `𝔮 ≠ 𝔭`) is the pullback along the projection `∏_𝔮 S_𝔮 → S_𝔭`, and
Layer 2 pulls the action back along `θ_𝔭 : Δ_t → S`. -/
noncomputable def comap {S' : Type*} [Monoid S'] (φ : S' →* S) : WeightData S' K ι ρ where
  toMulti := W.toMulti.comp φ
  bounds γ := W.bounds (φ γ)
  autFactor γ := W.autFactor (φ γ)
  rowBound_autFactor γ := W.rowBound_autFactor (φ γ)
  autFactor_one := by rw [map_one]; exact W.autFactor_one
  autFactor_mul γ δ := by rw [map_mul]; exact W.autFactor_mul (φ γ) (φ δ)

theorem comap_kappaSlash {S' : Type*} [Monoid S'] (φ : S' →* S) (γ : S') :
    (W.comap φ).kappaSlash γ = W.kappaSlash (φ γ) :=
  rfl

end WeightData

/-! ### Several places: the product of weight data -/

section Rename

variable {σ τ : Type*}

/-- Renaming a monomial along an injection renames its exponent. -/
theorem renameHom_monomial {e : σ → τ} (he : Function.Injective e) (s : σ →₀ ℕ) (a : K) :
    renameHom K e (monomial 1 s a) = monomial 1 (s.mapDomain e) a := by
  rw [monomial_eq_C_mul_prod, monomial_eq_C_mul_prod, map_mul, renameHom_C, map_finsuppProd,
    Finsupp.prod_mapDomain_index_inj he]
  simp only [map_pow, renameHom_X]

/-- The coefficients of a renamed series, as a sum over the original exponents. -/
private theorem hasSum_coeff_renameHom [DecidableEq τ] {e : σ → τ} (he : Function.Injective e)
    (f : Restricted K (1 : σ → ℝ)) (t : τ →₀ ℕ) :
    HasSum (fun s : σ →₀ ℕ => if t = s.mapDomain e then coeff s f.1 else 0)
      (coeff t (renameHom K e f).1) := by
  have h := hasSum_coeff ((hasSum_monomial (1 : σ → ℝ) f).map (renameHom K e)
    (continuous_renameHom e)) t
  simpa only [Function.comp_apply, renameHom_monomial he, val_monomial,
    MvPowerSeries.coeff_monomial] using h

/-- Renaming along an injection moves the coefficient at `t` to the coefficient at `e(t)`. -/
theorem coeff_renameHom_mapDomain {e : σ → τ} (he : Function.Injective e)
    (f : Restricted K (1 : σ → ℝ)) (t : σ →₀ ℕ) :
    coeff (t.mapDomain e) (renameHom K e f).1 = coeff t f.1 := by
  classical
  have h2 := hasSum_single (f := fun s : σ →₀ ℕ =>
      if t.mapDomain e = s.mapDomain e then coeff s f.1 else 0) t
    fun s hs => if_neg fun hst => hs ((Finsupp.mapDomain_injective he) hst).symm
  rw [(hasSum_coeff_renameHom he f _).unique h2]
  exact if_pos rfl

/-- Renaming along an injection has no coefficients outside the renamed multi-indices. -/
theorem coeff_renameHom_of_not_mem_range {e : σ → τ} (he : Function.Injective e)
    (f : Restricted K (1 : σ → ℝ)) {t : τ →₀ ℕ} (ht : ¬ ∃ s : σ →₀ ℕ, s.mapDomain e = t) :
    coeff t (renameHom K e f).1 = 0 := by
  classical
  have h := hasSum_coeff_renameHom he f t
  have hz : ∀ s : σ →₀ ℕ, (if t = s.mapDomain e then coeff s f.1 else 0) = 0 :=
    fun s => if_neg fun hts => ht ⟨s, hts.symm⟩
  simp only [hz] at h
  exact h.unique hasSum_zero

/-- Row bounds are preserved by renaming along an injection (the total degree is). -/
theorem rowBound_renameHom {e : σ → τ} (he : Function.Injective e) {σ' : ℝ} (hσ0 : 0 ≤ σ')
    {f : Restricted K (1 : σ → ℝ)} (hf : RowBound σ' f) : RowBound σ' (renameHom K e f) := by
  intro t
  by_cases ht : ∃ s : σ →₀ ℕ, s.mapDomain e = t
  · obtain ⟨s, rfl⟩ := ht
    rw [coeff_renameHom_mapDomain he, Finsupp.degree_mapDomain]
    exact hf s
  · rw [coeff_renameHom_of_not_mem_range he f ht, norm_zero]
    exact pow_nonneg hσ0 _

end Rename

section Pi

variable {P : Type*} {ιp : P → Type*}

/-- The multi-matrix on the disjoint union of the variables of the places. Source: roadmap §1.4.1
("acting on the variables of `I_𝔭` through `γ_𝔭`"). -/
def piMulti (γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K) : (Σ p, ιp p) → Matrix (Fin 2) (Fin 2) K :=
  fun x => γ x.1 x.2

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem multiBounds_piMulti {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K} (hγ : ∀ p, MultiBounds ρ (γ p)) :
    MultiBounds ρ (piMulti γ) :=
  ⟨hρ0, hρ, fun x => (hγ x.1).integral x.2, fun x => (hγ x.1).c_le x.2,
    fun x => (hγ x.1).d_unit x.2⟩

/-- The Möbius series of the product are the renamed Möbius series of the places. -/
theorem renameHom_mobius {ρ : ℝ} {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K}
    (hγ : ∀ p, MultiBounds ρ (γ p)) (p : P) (i : ιp p) :
    renameHom K (Sigma.mk p) (mobius (γ p) i) = mobius (piMulti γ) ⟨p, i⟩ := by
  have hb := multiBounds_piMulti (hγ p).rho_nonneg (hγ p).rho_lt_one hγ
  have hlin : renameHom K (Sigma.mk p) (lin (γ p) i) = lin (piMulti γ) ⟨p, i⟩ := by
    simp [lin, piMulti]
  have hnum : renameHom K (Sigma.mk p) (num (γ p) i) = num (piMulti γ) ⟨p, i⟩ := by
    simp [num, piMulti]
  have h1 : lin (piMulti γ) ⟨p, i⟩ * renameHom K (Sigma.mk p) (linInv (γ p) i) = 1 := by
    rw [← hlin, ← map_mul, lin_mul_linInv (hγ p) i, map_one]
  have hinv : renameHom K (Sigma.mk p) (linInv (γ p) i) = linInv (piMulti γ) ⟨p, i⟩ :=
    calc renameHom K (Sigma.mk p) (linInv (γ p) i)
        = renameHom K (Sigma.mk p) (linInv (γ p) i) *
            (lin (piMulti γ) ⟨p, i⟩ * linInv (piMulti γ) ⟨p, i⟩) := by
          rw [lin_mul_linInv hb ⟨p, i⟩, mul_one]
      _ = lin (piMulti γ) ⟨p, i⟩ * renameHom K (Sigma.mk p) (linInv (γ p) i) *
            linInv (piMulti γ) ⟨p, i⟩ := by ring
      _ = linInv (piMulti γ) ⟨p, i⟩ := by rw [h1, one_mul]
  rw [mobius, map_mul, hnum, hinv]
  rfl

/-- Substitution of the product's Möbius series commutes with renaming into the `p`-block. -/
theorem renameHom_mobiusSubst {ρ : ℝ} {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K}
    (hγ : ∀ p, MultiBounds ρ (γ p)) (p : P) (f : Restricted K (1 : ιp p → ℝ)) :
    renameHom K (Sigma.mk p) (mobiusSubst (hγ p) f) =
      mobiusSubst (multiBounds_piMulti (hγ p).rho_nonneg (hγ p).rho_lt_one hγ)
        (renameHom K (Sigma.mk p) f) := by
  have h : (renameHom K (Sigma.mk p)).comp (mobiusSubst (hγ p)).toRingHom =
      (mobiusSubst (multiBounds_piMulti (hγ p).rho_nonneg (hγ p).rho_lt_one hγ)).toRingHom.comp
        (renameHom K (Sigma.mk p)) :=
    ringHom_ext_of_continuous ((continuous_renameHom (Sigma.mk p)).comp
        (continuous_mobiusSubst (hγ p)))
      ((continuous_mobiusSubst (multiBounds_piMulti (hγ p).rho_nonneg (hγ p).rho_lt_one hγ)).comp
        (continuous_renameHom (Sigma.mk p))) (fun a => ?_) fun i => ?_
  · exact RingHom.congr_fun h f
  · simp [mobiusSubst_apply, aeval_C, algebraMap_apply]
  · change renameHom K (Sigma.mk p) (mobiusSubst (hγ p) (X K 1 i)) =
      mobiusSubst (multiBounds_piMulti (hγ p).rho_nonneg (hγ p).rho_lt_one hγ)
        (renameHom K (Sigma.mk p) (X K 1 i))
    rw [mobiusSubst_X, renameHom_X, mobiusSubst_X]
    exact renameHom_mobius hγ p i

variable {Sp : P → Type*} [∀ p, Monoid (Sp p)] {ρ : ℝ} [Fintype P] [Nonempty P]

/-- **The product of weight data over finitely many places**: on `K⟨z_{(p,i)}⟩`, the monoid
`∏_p S_p` acts through the multi-matrix `(γ_p)_p` with automorphy factor `∏_p j_p(γ_p)` (each in
its own variables) — the tensor product of the actions at the places. Source: roadmap §1.4.1;
[Buz07, §10] (`A_{κ,r}` at `r = 1` for the monoid `M_t`). -/
noncomputable def WeightData.pi (W : ∀ p, WeightData (Sp p) K (ιp p) ρ) :
    WeightData (∀ p, Sp p) K (Σ p, ιp p) ρ where
  toMulti :=
    { toFun := fun γ => piMulti fun p => (W p).toMulti (γ p)
      map_one' := funext fun x => by simp [piMulti]
      map_mul' := fun γ δ => funext fun x => by simp [piMulti] }
  bounds γ := multiBounds_piMulti (W (Classical.arbitrary P)).rho_nonneg
    (W (Classical.arbitrary P)).rho_lt_one fun p => (W p).bounds (γ p)
  autFactor γ := ∏ p, renameHom K (Sigma.mk p) ((W p).autFactor (γ p))
  rowBound_autFactor γ :=
    RowBound.prod (W (Classical.arbitrary P)).rho_nonneg Finset.univ fun p _ =>
      rowBound_renameHom sigma_mk_injective (W (Classical.arbitrary P)).rho_nonneg
        ((W p).rowBound_autFactor (γ p))
  autFactor_one := Finset.prod_eq_one fun p _ => by
    rw [Pi.one_apply, (W p).autFactor_one, map_one]
  autFactor_mul γ δ := by
    simp only [Pi.mul_apply, WeightData.autFactor_mul, map_mul, Finset.prod_mul_distrib, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun p _ => renameHom_mobiusSubst (fun p => (W p).bounds (γ p)) p _

theorem WeightData.pi_toMulti (W : ∀ p, WeightData (Sp p) K (ιp p) ρ) (γ : ∀ p, Sp p) (p : P)
    (i : ιp p) : (WeightData.pi W).toMulti γ ⟨p, i⟩ = (W p).toMulti (γ p) i :=
  rfl

theorem WeightData.pi_autFactor (W : ∀ p, WeightData (Sp p) K (ιp p) ρ) (γ : ∀ p, Sp p) :
    (WeightData.pi W).autFactor γ = ∏ p, renameHom K (Sigma.mk p) ((W p).autFactor (γ p)) :=
  rfl

/-- The single-place instance of §1.4.2: the weight datum at the place `p`, with the other places
acting trivially, is the pullback along the projection. -/
noncomputable def WeightData.single (W : ∀ p, WeightData (Sp p) K (ιp p) ρ) (p : P) :
    WeightData (∀ q, Sp q) K (ιp p) ρ :=
  (W p).comap (Pi.evalMonoidHom Sp p)

end Pi

end AutomorphicForm
