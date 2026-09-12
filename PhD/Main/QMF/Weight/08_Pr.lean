/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«07_Fredholm»

/-!
# Non-neat levels: the Fredholm determinant on `S_κ(U)` as a direct summand

[Buzzard, *Eigenvarieties*, §10 p. 73]: "the group `Γ_λ` contains, with finite index, a
subgroup of `O_F^×` of finite index, and hence `Γ_λ` acts on `A_{κ,r}` via a finite quotient.
Hence `S^D_κ(U;r)` is a direct summand of an ONable Banach `O(X)`-module and our Fredholm
theory applies."  [§2 pp. 18–19]: "Say `P` satisfies property (Pr) and `φ : P → P` is a
compact morphism.  Define `det(1 − Xφ)` thus: firstly choose `Q` such that `P ⊕ Q` is
potentially ONable, and define `det(1 − Xφ) = det(1 − X(φ ⊕ 0))`."

Without the neat-level hypothesis, evaluation at representatives identifies `S_κ(U)` with
`∏_λ A_κ^{Γ_λ} ⊆ c(ι × ℕ, K)` (`bijective_evalAtRepsSlash`).  When each `Γ_λ` is finite with
`|Γ_λ|` invertible in `K`, averaging over `Γ_λ` is a continuous projector onto the invariants
(`stabAvg`), so the image is a direct summand with projector `stabProj`, and the determinant
of `[UηU]` on `S_κ(U)` is `det(1 − T·(heckeBlockOp ∘ E))` for *any* continuous projector `E`
onto the image (`heckeCharPowerSeriesPr`) — independent of `E` ([Buzzard, Lemma 2.12]:
`det(1 − Xuv) = det(1 − Xvu)`), equal to `heckeCharPowerSeries` at a neat level, and with
the same eigenform criterion.

## Main declarations

* `QMF.Weight.stabAvg`, `QMF.Weight.stabProj` — the averaging projectors.
* `QMF.Weight.heckeCharPowerSeriesPr` — the determinant on a (Pr) summand.
* `QMF.Weight.heckeCharPowerSeriesPr_eq_of_proj`, `QMF.Weight.heckeCharPowerSeriesPr_eq_of_surjective`,
  `QMF.Weight.evalT_heckeCharPowerSeriesPr_eq_zero_iff`.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ} {UK : Subgroup Kˣ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)

section Averaging

variable (H : Subgroup G) (hH : (H : Set G) ⊆ U) [Fintype H]

/-- **The averaging operator** of a finite subgroup `H ≤ U` acting on the Tate algebra through
the twisted weight action: `a ↦ |H|⁻¹ Σ_{w ∈ H} χ(θ w) • κ.kappaSlash (θ w) a`
([Buzzard, §10 p. 73]: `Γ_λ` "acts on `A_{κ,r}` via a finite quotient"; cf.
`Representation.averageMap`). -/
noncomputable def stabAvg : c(ℕ, K) →L[K] c(ℕ, K) :=
  (Fintype.card H : K)⁻¹ • ∑ w : H,
    (((χ ⟨θ w, hU (hH w.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w, hU (hH w.2)⟩)

/-- The twisted action of `H` composes: acting by `w'` then by `w` is acting by `w' * w`. -/
private theorem act_act (a : c(ℕ, K)) (w w' : H) :
    ((χ ⟨θ w, hU (hH w.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w, hU (hH w.2)⟩
        (((χ ⟨θ w', hU (hH w'.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w', hU (hH w'.2)⟩ a)
      = ((χ ⟨θ ((w' : G) * w), hU (hH (H.mul_mem w'.2 w.2))⟩ : Kˣ) : K)
          • κ.kappaSlash ⟨θ ((w' : G) * w), hU (hH (H.mul_mem w'.2 w.2))⟩ a := by
  have hmul : (⟨θ ((w' : G) * w), hU (hH (H.mul_mem w'.2 w.2))⟩ : S)
      = ⟨θ w', hU (hH w'.2)⟩ * ⟨θ w, hU (hH w.2)⟩ := Subtype.ext (map_mul θ _ _)
  rw [hmul, AnalyticWeight.kappaSlash_mul, map_mul, Units.val_mul,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul, mul_comm]

/-- The average is invariant under every `w ∈ H` (reindex the sum by right translation;
the action law `kappaSlash_mul` and the twist are multiplicative). -/
theorem stabAvg_slash (a : c(ℕ, K)) (w : H) :
    ((χ ⟨θ w, hU (hH w.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w, hU (hH w.2)⟩ (stabAvg θ κ U hU χ H hH a)
      = stabAvg θ κ U hU χ H hH a := by
  have hval : ∀ b : c(ℕ, K), stabAvg θ κ U hU χ H hH b
      = (Fintype.card H : K)⁻¹ • ∑ w' : H,
          (((χ ⟨θ w', hU (hH w'.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w', hU (hH w'.2)⟩ b) := fun b => by
    simp [stabAvg]
  rw [hval, map_smul, smul_comm, map_sum, Finset.smul_sum]
  congr 1
  exact (Fintype.sum_equiv (Equiv.mulRight w)
    (fun w' : H => ((χ ⟨θ w, hU (hH w.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w, hU (hH w.2)⟩
      (((χ ⟨θ w', hU (hH w'.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w', hU (hH w'.2)⟩ a))
    (fun w'' : H => ((χ ⟨θ w'', hU (hH w''.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w'', hU (hH w''.2)⟩ a)
    fun w' => act_act θ κ U hU χ H hH a w w')

/-- The average of an invariant vector is itself. -/
theorem stabAvg_of_invariant (hcard : (Fintype.card H : K) ≠ 0) {a : c(ℕ, K)}
    (ha : ∀ w : H, ((χ ⟨θ w, hU (hH w.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w, hU (hH w.2)⟩ a = a) :
    stabAvg θ κ U hU χ H hH a = a := by
  have hval : stabAvg θ κ U hU χ H hH a
      = (Fintype.card H : K)⁻¹ • ∑ w' : H,
          (((χ ⟨θ w', hU (hH w'.2)⟩ : Kˣ) : K) • κ.kappaSlash ⟨θ w', hU (hH w'.2)⟩ a) := by
    simp [stabAvg]
  rw [hval, Finset.sum_congr rfl fun w' _ => ha w', Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The average is a projector. -/
theorem stabAvg_comp_self (hcard : (Fintype.card H : K) ≠ 0) :
    (stabAvg θ κ U hU χ H hH).comp (stabAvg θ κ U hU χ H hH) = stabAvg θ κ U hU χ H hH :=
  ContinuousLinearMap.ext fun a =>
    stabAvg_of_invariant θ κ U hU χ H hH hcard fun w => stabAvg_slash θ κ U hU χ H hH a w

/-- The range of the average is the space of `H`-invariants. -/
theorem range_stabAvg (hcard : (Fintype.card H : K) ≠ 0) :
    LinearMap.range (stabAvg θ κ U hU χ H hH : c(ℕ, K) →ₗ[K] c(ℕ, K))
      = letI := kappaLevelSlashActionTwisted θ κ χ
        letI := kappaLevelSMulSlashClassTwisted θ κ χ
        AbstractHeckeOperatorSlash.slashFixedPointsOfLE (U := H) K c(ℕ, K)
          (fun _ hw => hU (hH hw)) := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  haveI := kappaLevelSMulSlashClassTwisted θ κ χ
  refine le_antisymm ?_ fun a ha => ⟨a, stabAvg_of_invariant θ κ U hU χ H hH hcard fun w => ha w⟩
  rintro _ ⟨a, rfl⟩ w
  exact stabAvg_slash θ κ U hU χ H hH a w

end Averaging

section BlockProjector

variable (c : ι → G) [∀ i, Fintype (AutomorphicFunction.stabilizerAtSlash Γ U (c i))]

/-- **The block projector** onto `∏_λ A_κ^{Γ_λ}`: the averages over the stabilisers
`Γ_λ = stabilizerAtSlash Γ U (c i)`, block by block. -/
noncomputable def stabProj : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) :=
  blockOp fun i j =>
    if i = j then
      stabAvg θ κ U hU χ (AutomorphicFunction.stabilizerAtSlash Γ U (c i)) (fun _ hw => hw.1)
    else 0

/-- The block projector is a projector. -/
theorem stabProj_comp_self
    (hcard : ∀ i, (Fintype.card (AutomorphicFunction.stabilizerAtSlash Γ U (c i)) : K) ≠ 0) :
    (stabProj (Γ := Γ) θ κ U hU χ c).comp (stabProj (Γ := Γ) θ κ U hU χ c)
      = stabProj (Γ := Γ) θ κ U hU χ c := by
  rw [stabProj, blockOp_comp]
  refine congrArg blockOp (funext fun i => funext fun j => ?_)
  rw [Finset.sum_eq_single j]
  · by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact stabAvg_comp_self θ κ U hU χ (AutomorphicFunction.stabilizerAtSlash Γ U (c i))
        (fun _ hw => hw.1) (hcard i)
    · simp [hij]
  · intro b _ hbj
    by_cases hib : i = b
    · simp [hib, hbj]
    · simp [hib]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem blockProj_stabProj (x : c(ι × ℕ, K)) (i : ι) :
    cSpace.blockProj i (stabProj (Γ := Γ) θ κ U hU χ c x)
      = stabAvg θ κ U hU χ (AutomorphicFunction.stabilizerAtSlash Γ U (c i)) (fun _ hw => hw.1)
          (cSpace.blockProj i x) := by
  rw [stabProj, blockOp, sum_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [sum_apply, map_sum, Finset.sum_eq_single i]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        cSpace.blockProj_blockIncl, if_pos rfl, if_pos rfl]
    · intro b _ hbi
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        cSpace.blockProj_blockIncl, if_pos rfl, if_neg (Ne.symm hbi)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro a _ hai
    rw [sum_apply, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      cSpace.blockProj_blockIncl, if_neg (Ne.symm hai)]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem ext_blockProj {x y : c(ι × ℕ, K)}
    (h : ∀ i, cSpace.blockProj i x = cSpace.blockProj i y) : x = y := by
  refine DFunLike.ext _ _ fun p => ?_
  obtain ⟨i, n⟩ := p
  simpa only [cSpace.blockProj_apply] using congrArg (fun g => g n) (h i)

/-- **The image of evaluation is the range of the block projector** (Buzzard's
`S_κ(U) ≅ ∏_λ A_κ^{Γ_λ}`, `bijective_evalAtRepsSlash`, with the invariants cut out by the
averages). -/
theorem range_stabProj
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hcard : ∀ i, (Fintype.card (AutomorphicFunction.stabilizerAtSlash Γ U (c i)) : K) ≠ 0) :
    LinearMap.range (stabProj (Γ := Γ) θ κ U hU χ c : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K))
      = LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    refine (mem_range_evalAtReps_iff θ κ U hU χ c hc _).mpr fun i w hw => ?_
    rw [show (stabProj (Γ := Γ) θ κ U hU χ c : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)) y
        = stabProj (Γ := Γ) θ κ U hU χ c y from rfl, blockProj_stabProj]
    exact stabAvg_slash θ κ U hU χ (AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (fun _ hw' => hw'.1) _ ⟨w, hw⟩
  · refine ⟨x, ext_blockProj fun i => ?_⟩
    rw [show (stabProj (Γ := Γ) θ κ U hU χ c : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)) x
        = stabProj (Γ := Γ) θ κ U hU χ c x from rfl, blockProj_stabProj]
    exact stabAvg_of_invariant θ κ U hU χ (AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (fun _ hw' => hw'.1) (hcard i)
      fun w => (mem_range_evalAtReps_iff θ κ U hU χ c hc x).mp hx i w w.2

end BlockProjector

section Determinant

variable {T : Type*} [Fintype T]

/-- **The Fredholm determinant of `[UηU]` on `S_κ(U)` at an arbitrary level**: for a
continuous projector `E` onto the image of evaluation at representatives (e.g. `stabProj`),
`det(1 − T·(heckeBlockOp ∘ E))` — Buzzard's `det(1 − X(φ ⊕ 0))` on the direct summand
`∏ A^{Γ_λ} ⊕ ker E` of the ONable model ([Buzzard, §2 pp. 18–19]). -/
noncomputable def heckeCharPowerSeriesPr (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) (E : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) : PowerSeries K :=
  charPowerSeries ((heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E)

/-- The block operator preserves the image of evaluation. -/
theorem heckeBlockOp_mem_range_evalAtReps (c : ι → G) {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {x : c(ι × ℕ, K)} (hx : x ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c)) :
    heckeBlockOp θ κ U hU χ vRep hvΔ idx u x
      ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) := by
  obtain ⟨φ, rfl⟩ := hx
  exact ⟨heckeOperator θ κ U hU hη h φ,
    evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ⟩

/-- **Independence of the projector** ([Buzzard, Lemma 2.12]: `det(1 − Xuv) = det(1 − Xvu)`):
two continuous projectors with the same range, which is preserved by the block operator, give
the same determinant. -/
theorem heckeCharPowerSeriesPr_eq_of_proj (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U)
    (hcomp : IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u))
    (E E' : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (hE : E.comp E = E) (hE' : E'.comp E' = E')
    (hrange : LinearMap.range (E : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K))
      = LinearMap.range (E' : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)))
    (hstable : ∀ x ∈ LinearMap.range (E : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)),
      heckeBlockOp θ κ U hU χ vRep hvΔ idx u x ∈ LinearMap.range (E : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K))) :
    heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u E
      = heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u E' := by
  -- a projector is the identity on its own range
  have hfix : ∀ (P : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)), P.comp P = P →
      ∀ y ∈ LinearMap.range (P : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)), P y = y := by
    rintro P hP _ ⟨z, rfl⟩
    exact congrArg (fun Q : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) => Q z) hP
  have hEE' : E.comp E' = E' :=
    ContinuousLinearMap.ext fun y => hfix E hE (E' y) (hrange ▸ ⟨y, rfl⟩)
  have hE'B : E'.comp ((heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E)
      = (heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E :=
    ContinuousLinearMap.ext fun y =>
      hfix E' hE' _ (hrange ▸ hstable (E y) ⟨y, rfl⟩)
  calc heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u E
      = charPowerSeries (E'.comp ((heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E)) := by
        rw [hE'B, heckeCharPowerSeriesPr]
    _ = charPowerSeries (((heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E).comp E') :=
        (charPowerSeries_comm _ E' (hcomp.comp_right E)).symm
    _ = heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u E' := by
        rw [heckeCharPowerSeriesPr, ContinuousLinearMap.comp_assoc, hEE']

/-- At a neat level (`E = 1`) the summand determinant is the determinant. -/
theorem heckeCharPowerSeriesPr_one (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) :
    heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u 1
      = heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u := by
  rw [heckeCharPowerSeriesPr, heckeCharPowerSeries, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id]

/-- **Eigenforms are the reciprocal roots**, at an arbitrary level: for `E` a continuous
projector onto the image of evaluation at a complete family of representatives. -/
theorem evalT_heckeCharPowerSeriesPr_eq_zero_iff (c : ι → G)
    (hc : Function.Surjective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖(θ η).det‖ ≤ σ)
    (E : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (hE : E.comp E = E)
    (hrange : LinearMap.range (E : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K))
      = LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c))
    {a : K} (ha0 : a ≠ 0) :
    PowerSeries.evalT a (heckeCharPowerSeriesPr θ κ U hU χ vRep hvΔ idx u E) = 0 ↔
      ∃ φ : Forms Γ θ κ U hU χ, φ ≠ 0 ∧ heckeOperator θ κ U hU hη h φ = a⁻¹ • φ := by
  have hcomp := isCompactoid_heckeBlockOp θ κ U hU χ hρσ hσ hdet hvΔ hv idx u
  have hinj := evalAtReps_injective θ κ U hU χ c hc
  have htr : ∀ φ : Forms Γ θ κ U hU χ,
      evalAtReps θ κ U hU χ c (heckeOperator θ κ U hU hη h φ)
        = heckeBlockOp θ κ U hU χ vRep hvΔ idx u (evalAtReps θ κ U hU χ c φ) :=
    fun φ => evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ
  have hEfix : ∀ φ : Forms Γ θ κ U hU χ, E (evalAtReps θ κ U hU χ c φ)
      = evalAtReps θ κ U hU χ c φ := fun φ => by
    obtain ⟨z, hz⟩ : evalAtReps θ κ U hU χ c φ
        ∈ LinearMap.range (E : c(ι × ℕ, K) →ₗ[K] c(ι × ℕ, K)) := hrange ▸ ⟨φ, rfl⟩
    rw [← hz]
    exact congrArg (fun Q : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) => Q z) hE
  rw [heckeCharPowerSeriesPr, evalT_charPowerSeries_eq_zero_iff _ (hcomp.comp_right E) ha0]
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hxmem : x ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) := by
      have hEx : E x ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) := hrange ▸ ⟨x, rfl⟩
      have hBx : heckeBlockOp θ κ U hU χ vRep hvΔ idx u (E x)
          ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) :=
        heckeBlockOp_mem_range_evalAtReps θ κ U hU χ c hη h vRep hvΔ hv hvinj idx d hd u hfact hEx
      have hxa : x = a • heckeBlockOp θ κ U hU χ vRep hvΔ idx u (E x) := by
        rw [show heckeBlockOp θ κ U hU χ vRep hvΔ idx u (E x)
            = ((heckeBlockOp θ κ U hU χ vRep hvΔ idx u).comp E) x from rfl, hx, smul_smul,
          mul_inv_cancel₀ ha0, one_smul]
      rw [hxa]
      exact Submodule.smul_mem _ a hBx
    obtain ⟨φ, rfl⟩ := hxmem
    refine ⟨φ, fun h0 => hx0 (by rw [h0, map_zero]), hinj ?_⟩
    rw [htr, map_smul, ← hx, ContinuousLinearMap.comp_apply, hEfix]
  · rintro ⟨φ, hφ0, hφ⟩
    refine ⟨evalAtReps θ κ U hU χ c φ, fun h0 => hφ0 (hinj (by rw [h0, map_zero])), ?_⟩
    rw [ContinuousLinearMap.comp_apply, hEfix, ← htr, hφ, map_smul]

end Determinant

end QMF.Weight
