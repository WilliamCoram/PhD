/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«12_StepOne»
import PhD.Main.LWX.«05_AtkinLehner»
import PhD.Main.LWX.«12_Bol»

/-!
# Instantiating the Atkin–Lehner reduction at the classical space — SKELETON

`PhD/Main/LWX/05_AtkinLehner.lean` proves [LWX, Prop 3.22] for *abstract* matrices
(`roots_charpoly_atkinLehner`): given the matrix `A` of `U_p` on the `ψ`-space, `B` of `U'_p` on
the `ψ`-space, `A'` of `U_p` on the `ψ⁻¹`-space, a conjugation `A' = P B Q`, `Q P = 1`, and the
operator identity `A B = p^{k+1}`, the characteristic roots pair.  This file supplies the
*genuine* matrices and names the hypothesis on them.

## What is built here

* `thetaBlock` — `θ^r` on the block model `c(ι × (ZMod (p^h) × ℕ), K)`, and
  `thetaBlock_eq_zero_iff`: its kernel at `r = k+1` is the classical subspace
  `locPolyDegSubmoduleBlock`.
* `thetaBlock_comp_discHeckeBlockOp_of_autFactor` — the `U_p` intertwining at the block-operator
  level (the `blockOp` sum of `PhD/Main/LWX/12_Bol.lean`'s `thetaDisc_comp_discHeckeBlock_of_autFactor`).
* `mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_autFactor` — **the classical subspace is
  `U_p`-stable**: if `θ f = 0` then `θ (U_p f) = c^r · U_p' (θ f) = 0`.
* `upMatrix` — the matrix of a block operator restricted to the classical subspace, in the basis
  `Module.finBasisOfFinrankEq` supplied by [LWX, (3.21.1)].
* `AtkinLehnerHypothesis` — **H1, named on the genuine spaces**: the operator identity together
  with the existence of a conjugation between the `ψ`- and `ψ⁻¹`-matrices.
* `roots_charpoly_upMatrix_of_atkinLehner` — H1 discharges to the multiset pairing; a one-line
  application of board one's lemma whose value is fixing the *types* Step I consumes.

## What is deliberately NOT built here, and why

The conjugation `(P, Q)` — the Atkin–Lehner element `w = (0, 1; −p^m, 0)` acting on classical
forms — is **not** constructible through the disc model.  Two independent obstructions:

1. `w ∉ M1 p`: `M1` requires `‖g 1 1‖ = 1` (`04_IntegralModel.lean:228`) and `w` has `g 1 1 = 0`, so
   `discSlash`, `discHeckeOperator` and every weight action in the project are undefined at `w`
   (all require `η ∈ levelM1`).
2. `w` does not preserve `ℤ_p`: it acts by `z ↦ 1/(−p^m z)`, sending `ℤ_p^×` outside `ℤ_p`, so it
   does not act on the disc model at all, at any level.

On the *classical subspace* it does act — `Sym^k` is a representation of all of `GL₂`, and `w`
acts by the twisted polynomial reversal `f(z) ↦ (−p^m z)^k f(1/(−p^m z))` together with a
permutation of the class set — but that action must be built on the finite-dimensional classical
space directly, not obtained by restricting an overconvergent one.  That construction is
hypothesis **H1a**, recorded on the board with the `Sym^k` route; the operator identity is
**H1b**, being worked in `PhD/Main/Test/AtkinLehnerIdentity.lean`.  `AtkinLehnerHypothesis` is exactly
`H1a ∧ H1b`.

See `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
-/

open AbstractHeckeOperatorSlash RightSlashAction TateFredholm QMF QMF.Weight

open scoped Pointwise QMF TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### `θ` on the block model and its kernel -/

variable (p K ι) in
/-- `θ^r` on the block model: the same `thetaDisc` in every block of the class set. -/
def thetaBlock (h r : ℕ) : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockMap (σ := ι) (thetaDisc p K h r)

omit [CharZero K] in
/-- The coefficient formula for `θ^r` on the block model: `thetaDisc_apply` in every block. -/
theorem thetaBlock_apply (h r : ℕ) (c : c(ι × (ZMod (p ^ h) × ℕ), K)) (i : ι)
    (a : ZMod (p ^ h)) (j : ℕ) :
    thetaBlock (p := p) (K := K) (ι := ι) h r c (i, (a, j))
      = ((Nat.descFactorial (j + r) r : ℕ) : K) * c (i, (a, j + r)) := by
  rw [thetaBlock, blockMap_apply_prod, thetaDisc_apply, cSpace.blockProj_apply]

/-- `ker θ^{k+1}` on the block model is the classical subspace — `thetaDisc_eq_zero_iff`,
blockwise. -/
theorem thetaBlock_eq_zero_iff (h k : ℕ) (c : c(ι × (ZMod (p ^ h) × ℕ), K)) :
    thetaBlock (p := p) (K := K) (ι := ι) h (k + 1) c = 0
      ↔ c ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  have hne : ∀ j : ℕ, ((Nat.descFactorial (j + (k + 1)) (k + 1) : ℕ) : K) ≠ 0 := fun j =>
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (Nat.le_add_left _ _)).ne'
  constructor
  · intro hzero i a j hj
    have happ := congrArg
      (fun f : c(ι × (ZMod (p ^ h) × ℕ), K) => f (i, (a, j - (k + 1)))) hzero
    simp only [thetaBlock_apply] at happ
    have hj' : j - (k + 1) + (k + 1) = j := by omega
    rw [hj'] at happ
    exact (mul_eq_zero.mp happ).resolve_left (by rw [← hj']; exact hne _)
  · intro hpoly
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨i, a, j⟩ := x
    rw [thetaBlock_apply, hpoly i a (j + (k + 1)) (by omega), mul_zero]
    rfl

/-! ### The intertwining and `U_p`-stability of the classical subspace -/

variable (ψ : ℚ_[p] →+* K) {UK UK' : Subgroup Kˣ} {ρ ρ' : ℝ}
variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])

/-! ### The intertwining and `U_p`-stability

Built on `PhD/Main/LWX/12_Bol.lean`'s `thetaDisc_comp_discHeckeBlock_of_autFactor`.  The weight hypotheses
are on the **automorphy factors** of the disc conjugates of the certificate matrices, which is what
Bol's identity actually consumes.  (Earlier drafts of these two statements shared an arbitrary
finite part `ν : UK →* Kˣ` between the two weights; that is false, since `ν(cz + d)` need not be
constant in `z`.  They were removed on 2026-09-09; see
`.mathlib-quality/lwx-theta/b2_log.jsonl`.) -/

omit [CharZero K] in
/-- **The intertwining at the block-operator level**: `blockOp` of
`thetaDisc_comp_discHeckeBlock_of_autFactor`. -/
theorem thetaBlock_comp_discHeckeBlockOp_of_autFactor (h r : ℕ)
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K) {u : ι → Fin p → ZMod (p ^ h) → K}
    (hA : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
        = PowerSeries.C (u i' t a)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ r)
    (hA' : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ'.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ (r + 1) = PowerSeries.C (u i' t a))
    (hdet : ∀ i' t, ψ ((certM1 θG U hU vRep hvΔ uu i' t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst) :
    (thetaBlock (p := p) (K := K) (ι := ι) h r).comp
        (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)
      = (cst ^ r) • ((discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu).comp
          (thetaBlock (p := p) (K := K) (ι := ι) h r)) := by
  rw [thetaBlock, discHeckeBlockOp, discHeckeBlockOp, blockMap_comp_blockOp, blockOp_comp_blockMap,
    smul_blockOpMap]
  exact congrArg blockOpMap (funext fun i => funext fun j =>
    thetaDisc_comp_discHeckeBlock_of_autFactor θG h r ψ κ κ' U hU vRep hvΔ idx uu cst hA hA'
      hdet i j)

/-- **`U_p`-stability of the classical subspace.**  If `θ^{k+1} f = 0` then
`θ^{k+1}(U_p f) = cst^{k+1} · U_p'(θ^{k+1} f) = 0`, so `U_p f` is again classical. -/
theorem mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_autFactor (h k : ℕ)
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K) {u : ι → Fin p → ZMod (p ^ h) → K}
    (hA : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
        = PowerSeries.C (u i' t a)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ (k + 1))
    (hA' : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ'.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ (k + 1 + 1) = PowerSeries.C (u i' t a))
    (hdet : ∀ i' t, ψ ((certM1 θG U hU vRep hvΔ uu i' t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
      ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  rw [← thetaBlock_eq_zero_iff]
  have hcomp := congrArg (fun T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] _ => T f)
    (thetaBlock_comp_discHeckeBlockOp_of_autFactor (p := p) (K := K) (ι := ι) ψ θG h (k + 1)
      κ κ' U hU vRep hvΔ idx uu cst hA hA' hdet)
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply] at hcomp
  rw [hcomp, (thetaBlock_eq_zero_iff h k f).2 hf, map_zero, smul_zero]

/-! ### The genuine matrices, and H1 named on them -/

omit [CharZero K] in
/-- The classical subspace is finite-dimensional ([LWX, (3.21.1)],
`finrank_locPolyDegSubmoduleBlock`). -/
theorem finite_locPolyDegSubmoduleBlock [Nonempty ι] (h k : ℕ) :
    Module.Finite K (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) := by
  refine Module.finite_of_finrank_pos ?_
  rw [finrank_locPolyDegSubmoduleBlock]
  exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos k.succ_pos (Nat.pow_pos hp.out.pos))

variable (p K ι) in
/-- **The matrix of a block operator on the classical subspace**, in the basis of size
`card ι · (k+1) · p^h` supplied by [LWX, (3.21.1)].  Applied to `U_p` at `ω`, `U'_p` at `ω`, and
`U_p` at `invChar ω`, these are the `A`, `B`, `A'` of `roots_charpoly_atkinLehner`. -/
def upMatrix [Nonempty ι] (h k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K :=
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k
  let b := Module.finBasisOfFinrankEq K _
    (finrank_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
  LinearMap.toMatrix b b ((T : c(ι × (ZMod (p ^ h) × ℕ), K) →ₗ[K] _).restrict hT)

variable (p K ι) in
/-- **Hypothesis H1, named on the genuine classical spaces.**  `A` is `U_p` at `ψ`, `B` is `U'_p`
at `ψ`, `A'` is `U_p` at `ψ⁻¹`, all as matrices on the classical subspace; the hypothesis is
* **H1b** the operator identity `A B = p^{k+1}` (worked in `PhD/Main/Test/AtkinLehnerIdentity.lean`), and
* **H1a** a conjugation `A' = P B Q`, `Q P = 1` — the Atkin–Lehner element acting on classical
  forms, which does *not* factor through the disc model (see the module docstring). -/
def AtkinLehnerHypothesis (h k : ℕ)
    (A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K) : Prop :=
  A * B = (ψ p) ^ (k + 1) • (1 : Matrix _ _ K) ∧
    ∃ P Q : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K, Q * P = 1 ∧ A' = P * B * Q

omit [DecidableEq ι] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[LWX, Prop 3.22] at the genuine classical space, granted H1**: the characteristic roots of
`U_p` on the `ψ⁻¹`-classical space are those on the `ψ`-classical space inverted and scaled by
`p^{k+1}`.  One application of `roots_charpoly_atkinLehner`. -/
theorem roots_charpoly_of_atkinLehnerHypothesis [IsAlgClosed K] (h k : ℕ)
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A') :
    A'.charpoly.roots = A.charpoly.roots.map (fun x => (ψ p) ^ (k + 1) / x) := by
  obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun hcon =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [hcon, map_zero]))
  exact roots_charpoly_atkinLehner (pow_ne_zero _ hψp) hAB hQP hA'

end LWX
