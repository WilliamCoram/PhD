/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«11_Theta»
import PhD.Main.LWX.«06_Vertices»
import PhD.Main.LWX.«07_ConjChar»

/-!
# Step I of [LWX, Theorem 1.3]: the touching — SKELETON (the parts stateable today)

[LWX, §3.23 Step I] (`lwx.txt:1807–1846`) shows that at a classical weight the Newton polygon of
the characteristic series *touches* the Corollary 3.18 lower bound polygon at
`P_k = (n_{k+1}, λ(n_{k+1}) v(T_{χ_k}))`.  This file holds the pieces of that argument whose Lean
shapes do not depend on the still-open gaps (the Newton polygon of a product, and the
instantiation of the Atkin–Lehner reduction):

* **Step I's conclusion as a named definition**, `IsStepOneTouching`, so that Step III consumes it
  as a statement rather than a project, and its discharge of `HasUnitBand` through the existing
  bridge `hasUnitBand_of_height_eq`.
* **Buzzard's small-slope argument in the abstract** (`eq_zero_of_intertwine_of_norm_lt`): an
  operator of norm at most one, intertwined with another up to a scalar, kills every eigenvector
  whose eigenvalue is larger in norm than that scalar.  This is [Bu04, Prop 4]'s
  Jacquet–Langlands-free half with the automorphic setup stripped away; the concrete
  `classical_of_slope_lt` is this lemma applied to
  `thetaDisc_comp_discHeckeBlock_of_autFactor` (`PhD/Main/LWX/12_Bol.lean`).
* **The classical subspace of the block model** and its dimension, the global form of
  [LWX, (3.21.1)] with the class-number factor.

Nothing here depends on Jacquet–Langlands; see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Step I's conclusion, named -/

/-- **Step I's conclusion** ([LWX, p. 25]: "the Newton polygon of `∑ c_n(T_{χ_k})Xⁿ` touches the
lower bound polygon at the points `P_k := (n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`"): at the halo point
`T₀`, the polygon's height at `n_k` equals the lower bound.  Stated as the exact hypothesis of
`hasUnitBand_of_height_eq`, so the bridge to Step II is definitional. -/
def IsStepOneTouching (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (T₀ : K)
    (k : ℕ) : Prop :=
  (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
      (touchX p (Fintype.card ι) k) =
    (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
      WithBotTop ℝ)

/-- **The bridge to Step II**: Step I's touching discharges the unit-band hypothesis that the
completed `lwx-slopes` board consumes.  This is `hasUnitBand_of_height_eq` verbatim. -/
theorem hasUnitBand_of_isStepOneTouching (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (h : IsStepOneTouching D ω ψ T₀ k) :
    HasUnitBand D ω k :=
  hasUnitBand_of_height_eq hp2 D ω ψ hψ h0 h1 h

/-! ### Buzzard's small-slope argument, in the abstract -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Scaling back by `μ⁻¹` bounds `‖μ‖·‖f‖` by `‖μ • f‖`: the model space `c(I, K)` carries only
`IsBoundedSMul`, so `norm_smul` is available in one direction only. -/
private theorem mul_norm_le_norm_smul {E : Type*} [NormedAddCommGroup E] [Module K E]
    [IsBoundedSMul K E] {μ : K} (hμ0 : μ ≠ 0) (f : E) : ‖μ‖ * ‖f‖ ≤ ‖μ • f‖ := by
  have h1 : ‖f‖ ≤ ‖μ‖⁻¹ * ‖μ • f‖ := by
    calc ‖f‖ = ‖μ⁻¹ • (μ • f)‖ := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ ≤ ‖μ⁻¹‖ * ‖μ • f‖ := norm_smul_le _ _
      _ = ‖μ‖⁻¹ * ‖μ • f‖ := by rw [norm_inv]
  have hμpos : 0 < ‖μ‖ := norm_pos_iff.2 hμ0
  calc ‖μ‖ * ‖f‖ ≤ ‖μ‖ * (‖μ‖⁻¹ * ‖μ • f‖) := by gcongr
    _ = ‖μ • f‖ := by field_simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **An eigenvalue of an operator of norm at most one has norm at most one** ([Bu04, Prop 4]:
"`U_p` is an operator with norm at most 1"). -/
theorem norm_le_one_of_eigen {E : Type*} [NormedAddCommGroup E] [Module K E] [IsBoundedSMul K E]
    {T : E →L[K] E} (hT : ‖T‖ ≤ 1) {f : E} (hf : f ≠ 0) {μ : K} (hTf : T f = μ • f) :
    ‖μ‖ ≤ 1 := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [norm_zero]
    exact zero_le_one
  have hpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  have hlow : ‖μ‖ * ‖f‖ ≤ ‖T f‖ := by rw [hTf]; exact mul_norm_le_norm_smul hμ0 f
  have hup : ‖T f‖ ≤ ‖f‖ := (le_opNorm T f).trans (by nlinarith [norm_nonneg f])
  nlinarith [hlow, hup, hpos]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[Bu04, Prop 4], the Jacquet–Langlands-free half, abstracted.**  If `θ ∘ P = c • (P' ∘ θ)`,
`‖P'‖ ≤ 1`, and `f` is a `P`-eigenvector with `‖c‖ < ‖μ‖`, then `θ f = 0`: otherwise `θ f` would
be a `P'`-eigenvector of eigenvalue `μ / c` of norm `> 1`, impossible for an operator of norm at
most one.  Applied with `θ = θ^{k+1}`, `P = U_p`, `c = p^{k+1}` this is "if `v(λ) < k+1` then `f`
is classical".

`_hc` is **slack**: if `c = 0` then `‖c‖ = 0 < ‖μ‖` forces `μ ≠ 0` and the same computation
closes the goal.  It is kept because the statement is the ticketed one (SO2) and because it
records the intended reading, `θ f` being a `P'`-eigenvector of eigenvalue `μ / c`.

The scalars are `[Module K E] [IsBoundedSMul K E]` rather than `[NormedSpace K E]`, because the
model space `c(I, K)` of `PhD/Main/TateFredholm/03_ModelSpace.lean` carries exactly those (and no
`NormedSpace` instance); `‖P'‖` is then `TateFredholm`'s scoped operator norm, and `‖μ • x‖` is
only bounded, not computed — the proof scales back by `μ⁻¹` instead of using `norm_smul`. -/
theorem eq_zero_of_intertwine_of_norm_lt {E : Type*} [NormedAddCommGroup E] [Module K E]
    [IsBoundedSMul K E] {P P' θ : E →L[K] E} (hP' : ‖P'‖ ≤ 1) {c : K} (_hc : c ≠ 0)
    (hint : θ.comp P = c • P'.comp θ) {f : E} {μ : K} (hf : P f = μ • f) (hμ : ‖c‖ < ‖μ‖) :
    θ f = 0 := by
  have hμ0 : μ ≠ 0 := fun h0 => absurd (h0 ▸ hμ) (by rw [norm_zero]; exact not_lt.2 (norm_nonneg c))
  have key : μ • θ f = c • P' (θ f) := by
    have happ := congrArg (fun T : E →L[K] E => T f) hint
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply] at happ
    rw [hf, map_smul] at happ
    exact happ
  by_contra hne
  have hpos : 0 < ‖θ f‖ := norm_pos_iff.mpr hne
  -- the right-hand side is at most `‖c‖·‖θ f‖`, since `‖P'‖ ≤ 1`
  have hup : ‖c • P' (θ f)‖ ≤ ‖c‖ * ‖θ f‖ :=
    (norm_smul_le c (P' (θ f))).trans (by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
      calc ‖P' (θ f)‖ ≤ ‖P'‖ * ‖θ f‖ := le_opNorm _ _
        _ ≤ 1 * ‖θ f‖ := by gcongr
        _ = ‖θ f‖ := one_mul _)
  -- the left-hand side is at least `‖μ‖·‖θ f‖`, by scaling back with `μ⁻¹`
  have hlow : ‖μ‖ * ‖θ f‖ ≤ ‖μ • θ f‖ := mul_norm_le_norm_smul hμ0 (θ f)
  rw [key] at hlow
  nlinarith [hup, hlow, hpos]

/-! ### The classical subspace of the block model, and [LWX, (3.21.1)] -/

variable (p K ι) in
/-- Locally polynomial of degree `≤ k` in every block: the classical subspace of the block model
`c(ι × (ZMod (p^h) × ℕ), K)`. -/
def locPolyDegSubmoduleBlock (h k : ℕ) : Submodule K c(ι × (ZMod (p ^ h) × ℕ), K) where
  carrier := {c | ∀ (i : ι) (a : ZMod (p ^ h)) (j : ℕ), k < j → c (i, (a, j)) = 0}
  add_mem' := by
    intro x y hx hy i a j hj
    have hadd : (x + y) (i, (a, j)) = x (i, (a, j)) + y (i, (a, j)) := rfl
    rw [hadd, hx i a j hj, hy i a j hj, add_zero]
  zero_mem' := by
    intro _ _ _ _
    rfl
  smul_mem' := by
    intro r x hx i a j hj
    have hsmul : (r • x) (i, (a, j)) = r * x (i, (a, j)) := rfl
    rw [hsmul, hx i a j hj, mul_zero]

omit hp [Fintype ι] [DecidableEq ι] in
/-- On the block index, forgetting the `Fin` bound is injective. -/
private theorem triple_val_inj {h k : ℕ} {x y : ι × ZMod (p ^ h) × Fin (k + 1)}
    (hxy : ((x.1, (x.2.1, (x.2.2 : ℕ))) : ι × (ZMod (p ^ h) × ℕ))
      = (y.1, (y.2.1, (y.2.2 : ℕ)))) : x = y := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  simp only [Prod.mk.injEq] at hxy ⊢
  exact ⟨hxy.1, hxy.2.1, Fin.ext hxy.2.2⟩

/-- The block-model classical subspace is `(ι × ZMod (p^h) × Fin (k+1))`-many coordinates.  The
block form of `11_Theta.lean`'s `locPolyDegEquiv`.  (Made public by ticket T5.17: `14_Touching.lean`
builds the classical basis from it.) -/
def locPolyDegBlockEquiv (h k : ℕ) :
    locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k ≃ₗ[K]
      (ι × ZMod (p ^ h) × Fin (k + 1) → K) where
  toFun f x := (f : c(ι × (ZMod (p ^ h) × ℕ), K)) (x.1, (x.2.1, (x.2.2 : ℕ)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g :=
    ⟨∑ x : ι × ZMod (p ^ h) × Fin (k + 1), cSpace.single (x.1, (x.2.1, (x.2.2 : ℕ))) (g x), by
      intro i a j hj
      rw [cSpace.sum_apply]
      refine Finset.sum_eq_zero fun x _ => cSpace.single_apply_of_ne (fun hcon => ?_) _
      have hj2 : j = (x.2.2 : ℕ) := congrArg Prod.snd (congrArg Prod.snd hcon)
      have hlt : (x.2.2 : ℕ) < k + 1 := x.2.2.isLt
      omega⟩
  left_inv f := by
    refine Subtype.ext (DFunLike.ext _ _ fun y => ?_)
    obtain ⟨i, a, j⟩ := y
    rw [cSpace.sum_apply]
    by_cases hj : j < k + 1
    · rw [Finset.sum_eq_single (i, a, (⟨j, hj⟩ : Fin (k + 1))) ?_ (by simp)]
      · exact cSpace.single_apply_self _ _
      · exact fun x _ hx => cSpace.single_apply_of_ne (fun hcon => hx (triple_val_inj hcon.symm)) _
    · rw [Finset.sum_eq_zero fun x _ => by
        refine cSpace.single_apply_of_ne (fun hcon => ?_) _
        have hj2 : j = (x.2.2 : ℕ) := congrArg Prod.snd (congrArg Prod.snd hcon)
        have hlt : (x.2.2 : ℕ) < k + 1 := x.2.2.isLt
        omega]
      exact (f.2 i a j (by omega)).symm
  right_inv g := by
    refine funext fun x => ?_
    show (∑ y : ι × ZMod (p ^ h) × Fin (k + 1),
        cSpace.single (y.1, (y.2.1, (y.2.2 : ℕ))) (g y))
      (x.1, (x.2.1, (x.2.2 : ℕ))) = g x
    rw [cSpace.sum_apply, Finset.sum_eq_single x ?_ (by simp)]
    · exact cSpace.single_apply_self _ _
    · exact fun y _ hy => cSpace.single_apply_of_ne (fun hcon => hy (triple_val_inj hcon.symm)) _

/-- **[LWX, (3.21.1)]**: `dim S^D_{k+2}(K^pIw_{pᵐ};ψ) = (k+1)q⁻¹pᵐt`, with `t = card ι` the class
number and `h = m − 1`.  The global form of `finrank_locPolyDegSubmodule`. -/
theorem finrank_locPolyDegSubmoduleBlock (h k : ℕ) :
    Module.finrank K (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
      = Fintype.card ι * ((k + 1) * p ^ h) := by
  rw [(locPolyDegBlockEquiv (p := p) (K := K) (ι := ι) h k).finrank_eq, Module.finrank_pi,
    Fintype.card_prod, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring

end LWX
