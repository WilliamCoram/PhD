/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.Forms
import PhD.QMF.Slash.HeckeMatrix
import PhD.TateFredholm.BlockOp
import PhD.TateFredholm.Riesz

/-!
# Compactness of `U_ϖ` on the forms of weight `κ` (Jacobs Lemma 2.7, Buzzard Lemma 12.2)

[Jacobs, Ch. 2 Lemma 2.7, p. 30]:

> "Every non-zero `ε_{k,l}` is compact.  Proof.  Note that by definition,
> `h_{k,l}(x, y) ∈ 𝒪₃[[x, y]]`.  By Corollary 1.10, it suffices to prove that every entry
> in `D(1/3) ε_{k,l}` is in `𝒪₃`.  Equivalently, we need to show that `h_{k,l}(x/3, y)`
> lies in `𝒪₃[[x, y]]`.  It is simply a case of checking that every coefficient of `x`
> is divisible by `3` in `𝒪₃`."

[Buzzard, *Eigenvarieties*, Lemma 12.2, pp. 78–79]:

> "The map `U_π : S^D_κ(U; r) → S^D_κ(U; r)` is the composite of the natural inclusion
> `S^D_κ(U; r) → S^D_κ(U; r|π|)` and a continuous norm-decreasing map … The inclusion …
> is norm-decreasing and compact, and hence `U_π`, considered as an endomorphism of
> `S^D_κ(U; r)`, is also norm-decreasing and compact.  Proof.  … If one decomposes `UηU`
> into a finite disjoint union `∐_δ U x_δ` of cosets, then `det((x_δ)_p)/det(η_p)` is a
> unit at all places of `F` above `p`, and hence by Lemma 8.1(b) the endomorphism of
> `A_{κ,r}` induced by `(x_δ)_p` can be factored as the inclusion `A_{κ,r} ⊂ A_{κ,r|π|}`
> followed by a norm-decreasing map … the result now follows easily."

This file proves both at an arbitrary analytic weight `κ : AnalyticWeight UK S ρ`, in the
Tate-model formulation of the Jacobs fork (`PhD/JacobsSlash/U3/7_Fredholm.lean`):
evaluation at a finite family of class representatives `c : ι → G` sends `Forms` into
the block model `c(ι × ℕ, K)`, the Hecke operator `[UηU]` becomes a block operator whose
blocks are finite sums of twisted weight actions at the certificate elements
`θ(u(i,t)·vₜ)`, and for `η` of `U_ϖ` type (`‖det θ(η)‖ ≤ σ < 1`) each block — hence the
block operator — is compactoid, because `‖det‖` of every element of `U·η·U` is bounded by
that of `η` and a bounded determinant forces the `a`-entry to be small, which is Jacobs's
row-decay `‖coeff (j,i)‖ ≤ σ^j` of the generating function.

## Main declarations

* `QMF.Weight.evalAtReps` — evaluation at representatives, into the block model.
* `QMF.Weight.ext_of_forall_rep`, `QMF.Weight.evalAtReps_injective` — a form is determined
  by its values at any family meeting every double coset.
* `QMF.Weight.bijective_evalAtReps`, `QMF.Weight.formsModelEquiv` — **Buzzard's
  decomposition at a neat level**: for a complete family of representatives whose
  stabilisers `Γ_λ` act trivially, `S_κ(U) ≅ ⊕_λ A_κ` (`c(ι × ℕ, K)`).
* `QMF.Weight.heckeBlock`, `QMF.Weight.heckeBlockOp` — the blocks and block operator of
  `[UηU]` from certificate data.
* `QMF.Weight.heckeOperator_apply_rep` — the matrix recipe at the representatives,
  `([UηU]φ)(cᵢ) = Σⱼ heckeBlock i j (φ(cⱼ))`.
* `QMF.Weight.evalAtReps_heckeOperator` — **the transport**: `[UηU]` is the block operator
  under `evalAtReps`.
* `QMF.Weight.isCompactoid_heckeBlock`, `QMF.Weight.isCompactoid_heckeBlockOp` — **the
  compactness of `U_ϖ` at weight `κ`**.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ} {UK : Subgroup Kˣ}

/-! ### The block model, and compactness of `U_ϖ` (Jacobs Lemma 2.7, Buzzard Lemma 12.2)

Evaluation at a finite family of representatives `c : ι → G` sends `Forms` into the
block model `c(ι × ℕ, K)` [Buzzard, §9 p. 69: "`f ∈ L(U,A)` is determined by
`f(τ_λ)`"], and the Hecke operator `[UηU]` becomes a block operator whose blocks are
finite sums of weight actions `χ(w) • κ.kappaSlash w` at the certificate elements
`w = θ(u(i,t)·vₜ)` [Jacobs, pp. 20–21: `(U_p φ)(cᵢ) = Σ_t φ(c(i,t))‖_κ (u(i,t)vₜ)_p`].
Every element of `U·η·U` has `‖det θ(·)‖ ≤ ‖det θ(η)‖` (the outer factors are integral),
so for `η` of `U_ϖ` type (`‖det θ(η)‖ ≤ σ < 1`) each block is compactoid
(`AnalyticWeight.isCompactoid_kappaSlash`, [Jacobs, Lemma 2.7]) and hence so is the block
operator ([Buzzard, Lemma 12.2]: "`U_π` … is also norm-decreasing and compact"). -/

section BlockModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)

/-- Evaluation of a form at the representatives `c : ι → G`, assembled into the block
model `c(ι × ℕ, K)`: the `i`-th block of `evalAtReps c φ` is `φ(c i)`
[Buzzard, §9 p. 69]. -/
noncomputable def evalAtReps (c : ι → G) : Forms Γ θ κ U hU χ →ₗ[K] c(ι × ℕ, K) where
  toFun φ := ∑ i : ι, cSpace.blockIncl i ((φ : AutomorphicFunction G Γ c(ℕ, K)) (c i))
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' r φ := by simp [Finset.smul_sum]

/-- The `i`-th block of `evalAtReps c φ` is the value `φ(c i)`. -/
theorem blockProj_evalAtReps (c : ι → G) (φ : Forms Γ θ κ U hU χ) (i : ι) :
    cSpace.blockProj i (evalAtReps θ κ U hU χ c φ)
      = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i) := by
  simp only [evalAtReps, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype ι] [DecidableEq ι] in
/-- **A form is determined by its values at representatives meeting every double coset**
([Buzzard, *Eigenvarieties*, §9 p. 69]: "`f ∈ L(U,A)` is determined by `f(τ_λ)`";
[Jacobs, Lemma 1.31]). -/
theorem ext_of_forall_rep (c : ι → G)
    (hc : Function.Surjective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    {φ ψ : Forms Γ θ κ U hU χ}
    (h : ∀ i, (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i)
      = (ψ : AutomorphicFunction G Γ c(ℕ, K)) (c i)) :
    φ = ψ := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  haveI := kappaLevelSMulSlashClassTwisted θ κ χ
  refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
  obtain ⟨i, hi⟩ := hc (Quotient.mk'' g)
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
  calc (φ : AutomorphicFunction G Γ c(ℕ, K)) (a * c i * b)
      = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i * b) := by
        rw [mul_assoc]
        exact AutomorphicFunction.left_invt' _ ha _
    _ = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i) ∣ₛ (⟨b, hU hb⟩ : levelMonoidOf θ S) :=
        AutomorphicFunction.slash_apply_mul K hU φ.2 ⟨b, hb⟩ (c i)
    _ = (ψ : AutomorphicFunction G Γ c(ℕ, K)) (c i) ∣ₛ (⟨b, hU hb⟩ : levelMonoidOf θ S) := by
        rw [h i]
    _ = (ψ : AutomorphicFunction G Γ c(ℕ, K)) (c i * b) :=
        (AutomorphicFunction.slash_apply_mul K hU ψ.2 ⟨b, hb⟩ (c i)).symm
    _ = (ψ : AutomorphicFunction G Γ c(ℕ, K)) (a * c i * b) := by
        rw [mul_assoc]
        exact (AutomorphicFunction.left_invt' _ ha _).symm

/-- **Injectivity of evaluation at representatives** ([Buzzard, §9 p. 69]: "`f ∈ L(U,A)` is
determined by `f(τ_λ)`"): for any family `c : ι → G` meeting every double coset,
`evalAtReps c` is injective. -/
theorem evalAtReps_injective (c : ι → G)
    (hc : Function.Surjective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)))) :
    Function.Injective (evalAtReps (Γ := Γ) θ κ U hU χ c) :=
  fun φ ψ h => ext_of_forall_rep θ κ U hU χ c hc fun i => by
    simpa only [blockProj_evalAtReps] using congrArg (cSpace.blockProj i) h

variable {T : Type*} [Fintype T]

/-- **The `(i, j)` block of `[UηU]`** in the block model, from certificate data: right-coset
representatives `vRep : T → G` of `U·η·U = ∐ U·vₜ`, and for each `(i, t)` a factorisation
`cᵢ · vₜ⁻¹ = d(i,t) · c(idx i t) · u(i,t)`.  The block is
`Σ_{t : idx i t = j} χ(θ(u(i,t)·vₜ)) • κ.kappaSlash (θ(u(i,t)·vₜ))`
[Jacobs, p. 21: "`ε_{i,j}` … `‖_κ (u(i,t)vₜ)_p` if `c_j = c(i,t)`"]. -/
noncomputable def heckeBlock (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) (i j : ι) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ∑ t ∈ Finset.univ.filter (fun t => idx i t = j),
    ((χ (levelMonoidOfToS θ S ⟨(u i t : G) * vRep t, mul_mem (hU (u i t).2) (hvΔ t)⟩) : Kˣ) : K)
      • κ.kappaSlash (levelMonoidOfToS θ S ⟨(u i t : G) * vRep t, mul_mem (hU (u i t).2) (hvΔ t)⟩)

/-- **The block operator of `[UηU]`** on the model `c(ι × ℕ, K)`
[Jacobs, p. 21: "`U_p` can be represented as `|I|²` endomorphisms `ε_{i,j}`"]. -/
noncomputable def heckeBlockOp (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) :=
  blockOp (heckeBlock θ κ U hU χ vRep hvΔ idx u)

/-- **The matrix recipe at the representatives** ([Jacobs, pp. 20–21]: "`(U_p φ)(c_i) =
Σ_j ε_{i,j} φ(c_j)`"): the value of `[UηU] φ` at `cᵢ` is the `i`-th row of the block matrix
applied to the values `φ(cⱼ)`. -/
theorem heckeOperator_apply_rep {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (c : ι → G) (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (φ : Forms Γ θ κ U hU χ) (i : ι) :
    (heckeOperator θ κ U hU hη h φ : AutomorphicFunction G Γ c(ℕ, K)) (c i)
      = ∑ j : ι, heckeBlock θ κ U hU χ vRep hvΔ idx u i j
          ((φ : AutomorphicFunction G Γ c(ℕ, K)) (c j)) := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  letI := kappaLevelSMulSlashClassTwisted θ κ χ
  have key := AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) K hU hη h φ
    vRep hvΔ hv hvinj (c i) (fun t => c (idx i t)) (d i) (hd i) (u i) (hfact i)
    (fun t => mul_mem (hU (u i t).2) (hvΔ t))
  refine key.trans ?_
  simp only [kappaLevelSlashActionTwisted_slash, Units.smul_def]
  rw [← Finset.sum_fiberwise Finset.univ (idx i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [heckeBlock, sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [show idx i t = j from by simpa using ht]
  rfl

/-- **Transport of `[UηU]` to the block model** ([Jacobs, pp. 20–21], the general form of
the fork's `evalU3_heckeU3`): under evaluation at the representatives, the Hecke operator
is the block operator of the certificates. -/
theorem evalAtReps_heckeOperator {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (c : ι → G) (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (φ : Forms Γ θ κ U hU χ) :
    evalAtReps θ κ U hU χ c (heckeOperator θ κ U hU hη h φ)
      = heckeBlockOp θ κ U hU χ vRep hvΔ idx u (evalAtReps θ κ U hU χ c φ) := by
  simp only [evalAtReps, LinearMap.coe_mk, AddHom.coe_mk,
    heckeOperator_apply_rep θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ,
    map_sum, heckeBlockOp, blockOp_blockIncl]
  exact Finset.sum_comm

omit [Fintype T] in
/-- Every right-coset representative of `U·η·U` lies in `U·η·U`: `vₜ = u₁·η·u₂`. -/
theorem exists_mul_eta_mul_of_bijOn {η : G} {vRep : T → G}
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (t : T) : ∃ u₁ ∈ U, ∃ u₂ ∈ U, vRep t = u₁ * η * u₂ := by
  obtain ⟨x, hx, hmk⟩ := hv.mapsTo ⟨t, rfl⟩
  obtain ⟨η', hη', u₂, hu₂, rfl⟩ := Set.mem_mul.mp hx
  rw [Set.mem_singleton_iff] at hη'
  subst η'
  have hrel : (QuotientGroup.rightRel U) (η * u₂) (vRep t) := Quotient.eq''.mp hmk
  have hu₁ : vRep t * (η * u₂)⁻¹ ∈ U := QuotientGroup.rightRel_apply.mp hrel
  refine ⟨vRep t * (η * u₂)⁻¹, hu₁, u₂, hu₂, ?_⟩
  group

omit [CompleteSpace K] [Fintype T] in
include hU in
/-- The determinant of the matrix component of every certificate element `u(i,t)·vₜ`
is bounded by that of `η` ([Buzzard, Lemma 12.2 proof]: "`det((x_δ)_p)/det(η_p)` is a
unit at all places of `F` above `p`"), the outer factors having integral entries
(`hb`, and `θ(U) ⊆ S`). -/
theorem norm_det_toMatrix_certificate_le (hb : LevelBounds S ρ) {σ : ℝ} {η : G}
    (hdet : ‖(θ η).det‖ ≤ σ) {vRep : T → G}
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (u : U) (t : T) : ‖(θ ((u : G) * vRep t)).det‖ ≤ σ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hv'⟩ := exists_mul_eta_mul_of_bijOn U hv t
  have h1 : ‖(θ ((u : G) * u₁)).det‖ ≤ 1 := hb.norm_det_le_one (hU (mul_mem u.2 hu₁))
  have h2 : ‖(θ u₂).det‖ ≤ 1 := hb.norm_det_le_one (hU hu₂)
  rw [hv', show (u : G) * (u₁ * η * u₂) = ((u : G) * u₁) * η * u₂ by group, map_mul, map_mul,
    Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hdet
  calc ‖(θ ((u : G) * u₁)).det‖ * ‖(θ η).det‖ * ‖(θ u₂).det‖
      ≤ 1 * σ * 1 :=
        mul_le_mul (mul_le_mul h1 hdet (norm_nonneg _) zero_le_one) h2 (norm_nonneg _)
          (by positivity)
    _ = σ := by ring

omit [Fintype ι] in
/-- **Each block of `U_ϖ` is compactoid** ([Jacobs, Lemma 2.7]: "Every non-zero `ε_{k,l}`
is compact"), for `η` of `U_ϖ` type: `‖det θ(η)‖ ≤ σ < 1` with `ρ ≤ σ`. -/
theorem isCompactoid_heckeBlock {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) {η : G}
    (hdet : ‖(θ η).det‖ ≤ σ) {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) (i j : ι) :
    IsCompactoid (heckeBlock θ κ U hU χ vRep hvΔ idx u i j) := by
  unfold heckeBlock
  refine IsCompactoid.finset_sum _ fun t _ => IsCompactoid.smul _ ?_
  exact κ.isCompactoid_kappaSlash _ hρσ hσ
    (norm_det_toMatrix_certificate_le θ U hU κ.toWeightSeries.bounds hdet hv (u i t) t)

/-- **`U_ϖ` is compactoid on the forms of weight `κ` and level `U`** ([Buzzard, Lemma
12.2]; [Jacobs, Lemma 2.7] assembled over the class set): the block operator of `[UηU]`,
for `η` of `U_ϖ` type, is compactoid. -/
theorem isCompactoid_heckeBlockOp {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) {η : G}
    (hdet : ‖(θ η).det‖ ≤ σ) {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) :
    IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u) :=
  isCompactoid_blockOp fun i j => isCompactoid_heckeBlock θ κ U hU χ hρσ hσ hdet hvΔ hv idx u i j

/-! ### Bijectivity at a neat level (Buzzard §9 p. 69, Jacobs Lemma 1.31) -/

/-- **Buzzard's decomposition at a neat level** ([Buzzard, *Eigenvarieties*, §9 p. 69]:
"`f ↦ (f(τ_λ))` induces an isomorphism `L(U,A) → ⊕_λ A^{Γ_λ}`"; [Jacobs, Lemma 1.31]): if
`c : ι → G` is a complete set of representatives of `Γ\G/U` and every stabiliser
`Γ_λ = {u ∈ U : c_λ u c_λ⁻¹ ∈ Γ}` acts trivially on the Tate algebra, evaluation at the
representatives is a bijection `S_κ(U) ≅ ⊕_λ c(ℕ, K)`. -/
theorem bijective_evalAtReps (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a) :
    Function.Bijective (evalAtReps (Γ := Γ) θ κ U hU χ c) := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  haveI := kappaLevelSMulSlashClassTwisted θ κ χ
  refine ⟨evalAtReps_injective θ κ U hU χ c hc.2, fun F => ?_⟩
  -- the section of the double-coset projection induced by the complete family `c`
  let e : ι ≃ DoubleCoset.Quotient (Γ : Set G) (U : Set G) := Equiv.ofBijective _ hc
  have hσ : ∀ q, (Quotient.mk'' (c (e.symm q)) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))
      = q := fun q => e.apply_symm_apply q
  obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtRepsSlash (A := c(ℕ, K)) K hU
    (fun q => c (e.symm q)) hσ).2
    (fun q => ⟨cSpace.blockProj (e.symm q) F, fun w => by
      show χ ⟨θ w, _⟩ • κ.kappaSlash ⟨θ w, _⟩ (cSpace.blockProj (e.symm q) F)
        = cSpace.blockProj (e.symm q) F
      exact hstab (e.symm q) w w.2 _⟩)
  refine ⟨φ, DFunLike.ext _ _ fun x => ?_⟩
  obtain ⟨i, n⟩ := x
  have h3 : (φ : AutomorphicFunction G Γ c(ℕ, K)) (c (e.symm (e i)))
      = cSpace.blockProj (e.symm (e i)) F :=
    congrArg Subtype.val (congrFun hφ (e i))
  rw [Equiv.symm_apply_apply] at h3
  simpa only [cSpace.blockProj_apply] using
    congrArg (fun g => g n) ((blockProj_evalAtReps θ κ U hU χ c φ i).trans h3)

/-- **The image of evaluation is the block-model invariants** ([Buzzard, *Eigenvarieties*,
§9 p. 69]: "`f ↦ (f(τ_λ))` induces an isomorphism `L(U,A) → ⊕_λ A^{Γ_λ}`"): for a complete
family of representatives, a tuple lies in the image of `evalAtReps` exactly when each of its
blocks is fixed by the corresponding stabiliser `Γ_λ`. -/
theorem mem_range_evalAtReps_iff (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (x : c(ι × ℕ, K)) :
    x ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) ↔
      ∀ (i : ι) (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i)),
        χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ (cSpace.blockProj i x)
          = cSpace.blockProj i x := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  haveI := kappaLevelSMulSlashClassTwisted θ κ χ
  constructor
  · rintro ⟨φ, rfl⟩ i w hw
    rw [blockProj_evalAtReps]
    have harg : (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i * w)
        = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i) := by
      rw [show c i * w = c i * w * (c i)⁻¹ * c i from (inv_mul_cancel_right _ _).symm]
      exact (φ : AutomorphicFunction G Γ c(ℕ, K)).left_invt' hw.2 (c i)
    exact ((mem_forms_iff θ κ hU χ).mp φ.2 ⟨w, hw.1⟩ (c i)).symm.trans harg
  · intro hinv
    let e : ι ≃ DoubleCoset.Quotient (Γ : Set G) (U : Set G) := Equiv.ofBijective _ hc
    have hσ : ∀ q, (Quotient.mk'' (c (e.symm q)) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))
        = q := fun q => e.apply_symm_apply q
    obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtRepsSlash (A := c(ℕ, K)) K hU
      (fun q => c (e.symm q)) hσ).2
      (fun q => ⟨cSpace.blockProj (e.symm q) x, fun w => by
        show χ ⟨θ w, _⟩ • κ.kappaSlash ⟨θ w, _⟩ (cSpace.blockProj (e.symm q) x)
          = cSpace.blockProj (e.symm q) x
        exact hinv (e.symm q) w w.2⟩)
    refine ⟨φ, DFunLike.ext _ _ fun p => ?_⟩
    obtain ⟨i, n⟩ := p
    have h3 : (φ : AutomorphicFunction G Γ c(ℕ, K)) (c (e.symm (e i)))
        = cSpace.blockProj (e.symm (e i)) x :=
      congrArg Subtype.val (congrFun hφ (e i))
    rw [Equiv.symm_apply_apply] at h3
    simpa only [cSpace.blockProj_apply] using
      congrArg (fun g => g n) ((blockProj_evalAtReps θ κ U hU χ c φ i).trans h3)

/-- Buzzard's decomposition when the stabilisers are trivial ([Jacobs, Lemma 2.2] for
`U₁(9)`: `Γ_i = 1`). -/
theorem bijective_evalAtReps_of_stabilizer_eq_bot (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    Function.Bijective (evalAtReps (Γ := Γ) θ κ U hU χ c) := by
  refine bijective_evalAtReps θ κ U hU χ c hc fun i w hw a => ?_
  have hw1 : w = 1 := Subgroup.mem_bot.mp (hstab i ▸ hw)
  subst hw1
  rw [show (⟨θ 1, hU hw.1⟩ : S) = 1 from Subtype.ext (map_one θ), map_one,
    AnalyticWeight.kappaSlash_one, one_smul]
  rfl

/-- Evaluation at the canonical representatives `Quotient.out` of a finite class set is
injective ([Buzzard, §9 p. 73]: "`S^D_κ(U;r) → ⊕_{λ=1}^{µ} (A_{κ,r})^{Γ_λ}`"; the finiteness of
`µ` at a quaternionic level is Fujisaki's lemma, `QMF.finite_classSet`). -/
theorem evalAtReps_out_injective [Fintype (DoubleCoset.Quotient (Γ : Set G) (U : Set G))]
    [DecidableEq (DoubleCoset.Quotient (Γ : Set G) (U : Set G))] :
    Function.Injective (evalAtReps (Γ := Γ) θ κ U hU χ
      fun q : DoubleCoset.Quotient (Γ : Set G) (U : Set G) => q.out) := by
  refine evalAtReps_injective θ κ U hU χ _ fun q => ⟨q, ?_⟩
  exact Quotient.out_eq' q

/-- Buzzard's decomposition at the canonical representatives of a finite class set, when
their stabilisers act trivially. -/
theorem bijective_evalAtReps_out [Fintype (DoubleCoset.Quotient (Γ : Set G) (U : Set G))]
    [DecidableEq (DoubleCoset.Quotient (Γ : Set G) (U : Set G))]
    (hstab : ∀ (q : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) (w : G)
      (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U q.out) (a : c(ℕ, K)),
      χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a) :
    Function.Bijective (evalAtReps (Γ := Γ) θ κ U hU χ
      fun q : DoubleCoset.Quotient (Γ : Set G) (U : Set G) => q.out) := by
  refine bijective_evalAtReps θ κ U hU χ _ ⟨fun p q h => ?_, fun q => ⟨q, ?_⟩⟩ hstab
  · rw [← Quotient.out_eq' p, ← Quotient.out_eq' q]
    exact h
  · exact Quotient.out_eq' q

/-- **The model isomorphism** `S_κ(U) ≅ ⊕_λ A_κ` at a neat level ([Buzzard, §9 p. 69];
[Jacobs, (2.1.1)]), packaged as a linear equivalence. -/
noncomputable def formsModelEquiv (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a) :
    Forms Γ θ κ U hU χ ≃ₗ[K] c(ι × ℕ, K) :=
  LinearEquiv.ofBijective _ (bijective_evalAtReps θ κ U hU χ c hc hstab)

end BlockModel

end QMF.Weight
