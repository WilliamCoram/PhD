import PhD.TateFredholm.«04_Matrix»
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The Noetherian bridge: closedness of finitely generated submodules
([FvdP] Lemma 1.2.3; [Buz07] Lemmas 2.2–2.3; [Lud24] Lemma 2.24, Lemma 2.26,
Exercise 2.27.  See `00_Tate.lean` for the development's overview.)

Over a **Noetherian** Banach–Tate ring, finitely generated submodules of Banach modules
are complete: first for submodules of *module-finite* Banach modules ([FvdP] 1.2.3 —
closure is f.g., open mapping theorem, geometric density iteration), then for f.g.
submodules of the model space `c(I, R)` via Buzzard's injective-truncation trick
([Buz07] Lemma 2.3(a),(b), transferred per [Lud24] Exercise 2.27, `ϖ` for `ρ`).

This file quarantines every Noetherian hypothesis of the development; everything
upstream is Noetherian-free.  Its headline is the bridge
`IsCompletelyContinuous.isCompactoid`, which yields the compactness criterion
`isCompletelyContinuous_iff_rowNorm` over Noetherian bases.

What `isClosed_of_fg` supplies is exactly [Bel] Hypothesis 3.1.8 — "every finitely
generated submodule of an ON-able Banach `A`-module is closed" — which the published
*Eigenbook* assumes outright (noting it can fail) in order to drop Noetherianity, and
which [Lud24, Remark 2.25] identifies as all that Buzzard's Lemma 2.3(3) needs.  So a
reader who prefers Bellaïche's axiomatic route can bypass this file and hypothesise its
conclusion; over a Noetherian Banach–Tate ring it is a theorem, proved here.
-/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Density

variable {M : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [IsUltrametricDist M] [CompleteSpace M]

/-- **[FvdP] Lemma 1.2.3** over a Banach–Tate ring: every submodule of a
*module-finite* Banach module over a Noetherian Banach–Tate ring is closed.

*Proof sketch* (Kedlaya's transcription, 18.727 "p-adic functional analysis, part 2",
Lemma 1).  Let `Ñ` be the closure of `N`; it is a submodule, finitely generated since
`M` is Noetherian.  Pick generators `e₁, …, eₙ` of `Ñ`; `Ñ` is closed in complete `M`,
hence complete, so the quantitative open mapping theorem (`exists_preimage_norm_le`)
applied to `(a₁, …, aₙ) ↦ ∑ aᵢeᵢ : Rⁿ → Ñ` gives `c ∈ (0,1)` with: every `x ∈ Ñ` is
`∑ aᵢeᵢ`, `c·max ‖aᵢ‖ ≤ ‖x‖`.  Choose `fᵢ ∈ N` with `‖eᵢ − fᵢ‖ ≤ c²` (density).
Iterate: `x₀ := x`; given `xⱼ = ∑ aⱼᵢeᵢ` (controlled), put `xⱼ₊₁ := ∑ aⱼᵢ(eᵢ − fᵢ)`,
so `‖xⱼ₊₁‖ ≤ c‖xⱼ‖` ultrametrically.  Telescoping, `x = ∑ᵢ (∑ⱼ aⱼᵢ) fᵢ ∈ N` (the
coefficient series converge geometrically in complete `R`).  Hence `N = Ñ`. -/
theorem isClosed_of_finite [IsTate R] [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : IsClosed (N : Set M) := by
  classical
  -- It suffices that the closure `Ñ` is contained in `N` (the reverse is `subset_closure`).
  suffices hle : N.topologicalClosure ≤ N by
    have heq : (N : Set M) = (N.topologicalClosure : Set M) :=
      congrArg SetLike.coe (le_antisymm N.le_topologicalClosure hle)
    rw [heq]; exact N.isClosed_topologicalClosure
  set Ñ := N.topologicalClosure with hÑ
  -- `Ñ` is finitely generated: `M` is Noetherian (`Module.Finite` + `IsNoetherianRing`).
  have hÑfg : Ñ.FG := IsNoetherian.noetherian Ñ
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hÑfg
  have hsmem : ∀ k, s k ∈ Ñ := fun k => hs ▸ Submodule.subset_span (Set.mem_range_self k)
  -- `↥Ñ` is a Banach `R`-module (closed in the complete `M`).
  haveI : CompleteSpace ↥Ñ := (N.isClosed_topologicalClosure).isComplete.completeSpace_coe
  haveI : IsBoundedSMul R ↥Ñ := .of_norm_smul_le fun r x => by
    simp only [Submodule.coe_norm, SetLike.val_smul]
    exact norm_smul_le r (x : M)
  -- The continuous surjection `π : Rⁿ → ↥Ñ`, `π a = ∑ k, a k • s k` (mirrors T017).
  have hmem : ∀ a : Fin n → R, Fintype.linearCombination R s a ∈ Ñ := fun a => by
    rw [Fintype.linearCombination_apply, ← hs]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  have hbound : ∀ a : Fin n → R,
      ‖((Fintype.linearCombination R s).codRestrict Ñ hmem) a‖ ≤ (∑ k, ‖s k‖) * ‖a‖ := fun a => by
    rw [Submodule.coe_norm, LinearMap.codRestrict_apply, Fintype.linearCombination_apply]
    calc ‖∑ k, a k • s k‖ ≤ ∑ k, ‖a k • s k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖s k‖ * ‖a‖ := Finset.sum_le_sum fun k _ => by
          calc ‖a k • s k‖ ≤ ‖a k‖ * ‖s k‖ := norm_smul_le _ _
          _ ≤ ‖a‖ * ‖s k‖ := mul_le_mul_of_nonneg_right (norm_le_pi_norm a k) (norm_nonneg _)
          _ = ‖s k‖ * ‖a‖ := mul_comm _ _
    _ = (∑ k, ‖s k‖) * ‖a‖ := by rw [Finset.sum_mul]
  let π : (Fin n → R) →L[R] ↥Ñ :=
    ((Fintype.linearCombination R s).codRestrict Ñ hmem).mkContinuous (∑ k, ‖s k‖) hbound
  have hπ_coe : ∀ a : (Fin n → R), (π a : M) = ∑ k, a k • s k := fun _ => rfl
  have hsurj : Function.Surjective π := fun q => by
    have hq : (q : M) ∈ Submodule.span R (Set.range s) := by rw [hs]; exact q.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨a, ha⟩ := hq
    exact ⟨a, Subtype.ext (by rw [hπ_coe]; exact ha)⟩
  -- Quantitative OMT: coefficients with norm control.
  obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le π hsurj
  choose coeff hcoeff_eq hcoeff_bound using hC
  have hπid : ∀ q : ↥Ñ, (∑ k, coeff q k • s k) = (q : M) := fun q => by
    rw [← hπ_coe (coeff q), hcoeff_eq q]
  -- Density constant `θ = 1/(2C)` giving contraction factor `Cθ = 1/2`.
  set θ : ℝ := 1 / (2 * C) with hθ
  have θpos : 0 < θ := by rw [hθ]; exact div_pos one_pos (by linarith)
  have hCθ : C * θ = 1 / 2 := by
    rw [hθ, mul_one_div, mul_comm 2 C, ← div_div, div_self hC0.ne']
  -- Choose `f k ∈ N` approximating each generator within `θ`.
  have hsk_closure : ∀ k, s k ∈ closure (N : Set M) := fun k => by
    rw [← N.topologicalClosure_coe]; exact hsmem k
  choose f hf_mem hf_dist using fun k => Metric.mem_closure_iff.1 (hsk_closure k) θ θpos
  have hf_memÑ : ∀ k, f k ∈ Ñ := fun k => N.le_topologicalClosure (hf_mem k)
  have hsub_mem : ∀ k, s k - f k ∈ Ñ := fun k => Submodule.sub_mem _ (hsmem k) (hf_memÑ k)
  have hsub_norm : ∀ k, ‖s k - f k‖ ≤ θ := fun k => by
    rw [← dist_eq_norm]; exact (hf_dist k).le
  have hmem_step : ∀ prev : ↥Ñ, (∑ k, coeff prev k • (s k - f k)) ∈ Ñ := fun prev =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hsub_mem k)
  -- Now fix `x ∈ Ñ` and show `x ∈ N` by geometric density iteration.
  intro x hx
  let g : ↥Ñ → ↥Ñ := fun prev => ⟨∑ k, coeff prev k • (s k - f k), hmem_step prev⟩
  let X : ℕ → ↥Ñ := fun j => g^[j] ⟨x, hx⟩
  have hX0 : ((X 0 : ↥Ñ) : M) = x := rfl
  have hXsucc : ∀ j, ((X (j + 1) : ↥Ñ) : M) = ∑ k, coeff (X j) k • (s k - f k) := fun j => by
    show ((g^[j + 1] ⟨x, hx⟩ : ↥Ñ) : M) = _
    rw [Function.iterate_succ_apply']
  -- Ultrametric contraction: `‖x_{j+1}‖ ≤ (1/2)‖x_j‖`.
  have hdecay : ∀ j, ‖((X (j + 1) : ↥Ñ) : M)‖ ≤ 1 / 2 * ‖((X j : ↥Ñ) : M)‖ := fun j => by
    rw [hXsucc]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    calc ‖coeff (X j) k • (s k - f k)‖
        ≤ ‖coeff (X j) k‖ * ‖s k - f k‖ := norm_smul_le _ _
      _ ≤ (C * ‖((X j : ↥Ñ) : M)‖) * θ :=
          mul_le_mul ((norm_le_pi_norm _ k).trans (hcoeff_bound (X j))) (hsub_norm k)
            (norm_nonneg _) (mul_nonneg hC0.le (norm_nonneg _))
      _ = 1 / 2 * ‖((X j : ↥Ñ) : M)‖ := by rw [mul_right_comm, hCθ]
  -- Geometric decay and coefficient decay.
  have hgeom : ∀ j, ‖((X j : ↥Ñ) : M)‖ ≤ (1 / 2) ^ j * ‖x‖ := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mul]; exact le_of_eq (congrArg norm hX0)
    | succ j ih =>
        calc ‖((X (j + 1) : ↥Ñ) : M)‖ ≤ 1 / 2 * ‖((X j : ↥Ñ) : M)‖ := hdecay j
        _ ≤ 1 / 2 * ((1 / 2) ^ j * ‖x‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2) ^ (j + 1) * ‖x‖ := by rw [pow_succ']; ring
  have hcoefbound : ∀ j k, ‖coeff (X j) k‖ ≤ C * ‖x‖ * (1 / 2) ^ j := by
    intro j k
    calc ‖coeff (X j) k‖ ≤ ‖coeff (X j)‖ := norm_le_pi_norm _ k
    _ ≤ C * ‖((X j : ↥Ñ) : M)‖ := hcoeff_bound (X j)
    _ ≤ C * ((1 / 2) ^ j * ‖x‖) := mul_le_mul_of_nonneg_left (hgeom j) hC0.le
    _ = C * ‖x‖ * (1 / 2) ^ j := by ring
  -- The coefficient series converge geometrically in the complete ring `R`.
  have hsummable_coef : ∀ k, Summable (fun j => coeff (X j) k) := fun k =>
    Summable.of_norm <|
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hcoefbound j k)
        ((summable_geometric_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)).mul_left
          (C * ‖x‖))
  set b : Fin n → R := fun k => ∑' j, coeff (X j) k with hb_def
  have hbtend : ∀ k, Tendsto (fun J => ∑ j ∈ Finset.range J, coeff (X j) k) atTop (𝓝 (b k)) :=
    fun k => (hsummable_coef k).hasSum.tendsto_sum_nat
  -- Telescoping: `x_j - x_{j+1} = ∑ k, coeff(x_j) k • f k`.
  have hstep_tel : ∀ j, (∑ k, coeff (X j) k • f k) = ((X j : ↥Ñ) : M) - ((X (j + 1) : ↥Ñ) : M) := by
    intro j
    rw [hXsucc, ← hπid (X j), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_sub]; congr 1; abel
  have htel : ∀ J, (∑ k, (∑ j ∈ Finset.range J, coeff (X j) k) • f k) = x - ((X J : ↥Ñ) : M) := by
    intro J
    induction J with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, zero_smul, Finset.sum_const_zero]
        rw [hX0, sub_self]
    | succ J ih =>
        have hsplit : (∑ k, (∑ j ∈ Finset.range (J + 1), coeff (X j) k) • f k)
            = (∑ k, (∑ j ∈ Finset.range J, coeff (X j) k) • f k)
              + (∑ k, coeff (X J) k • f k) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_range_succ, add_smul]
        rw [hsplit, ih, hstep_tel J]; abel
  -- Pass to the limit `J → ∞`: `x = ∑ k, b k • f k ∈ N`.
  have hconv : Tendsto (fun J => ∑ k, (∑ j ∈ Finset.range J, coeff (X j) k) • f k) atTop
      (𝓝 (∑ k, b k • f k)) :=
    tendsto_finsetSum Finset.univ fun k _ => (hbtend k).smul_const (f k)
  have h0 : Tendsto (fun J => ((X J : ↥Ñ) : M)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun J => norm_nonneg _) hgeom ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)).mul_const ‖x‖
  have hconv2 : Tendsto (fun J => x - ((X J : ↥Ñ) : M)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub h0
  have hx_eq : x = ∑ k, b k • f k :=
    tendsto_nhds_unique hconv2 (Filter.Tendsto.congr (fun J => htel J) hconv)
  rw [hx_eq]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hf_mem k)

end Density

section ModelSpace

variable {I : Type*} [DecidableEq I]

/-- **[Buz07] Lemma 2.3(a)** over a Banach–Tate ring: some truncation is injective on a
finitely generated submodule.

*Proof sketch* (verbatim [Buz07, p. 10]).  Say `P` is generated by `m₁, …, mᵣ`, with
`mₐ = ∑ᵢ aₐᵢ eᵢ`.  For `i ∈ I` let `vᵢ := (aₐᵢ)ₐ ∈ Rʳ`.  The submodule of `Rʳ`
generated by the `vᵢ` is finitely generated (`R` Noetherian), hence generated by
`{vᵢ : i ∈ S}` for finite `S`.  This `S` works: if `π_S (∑ₐ bₐmₐ) = 0` then
`∑ₐ bₐaₐᵢ = 0` for `i ∈ S`, hence for all `i` (each `vᵢ` is a combination of the
`vⱼ, j ∈ S`), hence `∑ₐ bₐmₐ = 0`. -/
theorem exists_truncation_injOn [IsTate R] [IsNoetherianRing R]
    (P : Submodule R c(I, R)) (hP : P.FG) :
    ∃ S : Finset I, Set.InjOn (truncation (R := R) S) (P : Set c(I, R)) := by
  classical
  -- Generators of `P`, and the column vectors `v i = (m α i)_α ∈ Rʳ`.
  obtain ⟨r, m, hm⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hP
  set v : I → (Fin r → R) := fun i α => m α i with hv
  have hv_apply : ∀ i α, v i α = m α i := fun _ _ => rfl
  set V : Submodule R (Fin r → R) := Submodule.span R (Set.range v) with hV
  -- `V` is finitely generated: `Rʳ` is Noetherian.
  have hVfg : V.FG := IsNoetherian.noetherian V
  obtain ⟨t, ht⟩ := hVfg
  -- Extract a finite subset `T ⊆ range v` still spanning `V`.
  have htV : (↑t : Set (Fin r → R)) ⊆ (Submodule.span R (Set.range v) : Set (Fin r → R)) := by
    intro w hw
    have hwV : w ∈ V := by rw [← ht]; exact Submodule.subset_span hw
    rwa [hV] at hwV
  obtain ⟨T, hTsub, hTspan⟩ := Submodule.subset_span_finite_of_subset_span htV
  -- Pull the finite set `T` back to a finite set `S ⊆ I` of coordinates.
  have hchoose : ∀ w : Fin r → R, w ∈ T → ∃ i : I, v i = w :=
    fun w hw => Set.mem_range.1 (hTsub (Finset.mem_coe.2 hw))
  set S : Finset I := T.attach.image (fun w => (hchoose w.1 w.2).choose) with hS
  have hTimg : (↑T : Set (Fin r → R)) ⊆ v '' (S : Set I) := by
    intro w hw
    have hwT : w ∈ T := Finset.mem_coe.1 hw
    refine ⟨(hchoose w hwT).choose, ?_, (hchoose w hwT).choose_spec⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨w, hwT⟩, Finset.mem_attach _ _, rfl⟩)
  -- Hence `V ≤ span (v '' S)`, so every column `v i` lies in `span (v '' S)`.
  have hVS : V ≤ Submodule.span R (v '' (S : Set I)) :=
    calc V = Submodule.span R (↑t : Set (Fin r → R)) := ht.symm
    _ ≤ Submodule.span R (↑T : Set (Fin r → R)) := Submodule.span_le.2 hTspan
    _ ≤ Submodule.span R (v '' (S : Set I)) := Submodule.span_mono hTimg
  have hviS : ∀ i, v i ∈ Submodule.span R (v '' (S : Set I)) := fun i =>
    hVS (Submodule.subset_span (Set.mem_range_self i))
  -- `S` witnesses injectivity.
  have hzero : ∀ i : I, (0 : c(I, R)) i = 0 := fun i => by
    rw [← cSpace.evalCLM_apply i (0 : c(I, R)), map_zero]
  refine ⟨S, fun p hp q hq hpq => ?_⟩
  set d := p - q with hd
  have hdP : d ∈ P := Submodule.sub_mem P hp hq
  have hdtrunc : truncation S d = 0 := by rw [hd, map_sub, hpq, sub_self]
  have hdS : ∀ i ∈ S, d i = 0 := fun i hi => by
    have key : (if i ∈ S then d i else 0) = (0 : c(I, R)) i := by
      rw [← truncation_apply, hdtrunc]
    rw [if_pos hi, hzero i] at key
    exact key
  -- Write `d = ∑ α, b α • m α` and read off the coordinate functional.
  have hdspan : d ∈ Submodule.span R (Set.range m) := by rw [hm]; exact hdP
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hdspan
  have hcoord : ∀ i, d i = Fintype.linearCombination R b (v i) := fun i => by
    have hev : (∑ α, b α • m α) i = ∑ α, b α * m α i := by
      rw [← cSpace.evalCLM_apply i, map_sum]
      exact Finset.sum_congr rfl fun α _ => by
        rw [map_smul, cSpace.evalCLM_apply, smul_eq_mul]
    rw [Fintype.linearCombination_apply, ← hb, hev]
    exact Finset.sum_congr rfl fun α _ => by rw [hv_apply, smul_eq_mul, mul_comm]
  -- The functional vanishes on `v '' S`, hence on its span, hence at every `v i`.
  have hφvan : ∀ y ∈ Submodule.span R (v '' (S : Set I)),
      Fintype.linearCombination R b y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨i, hiS, rfl⟩ := hw
        rw [← hcoord i]
        exact hdS i (Finset.mem_coe.1 hiS)
    | zero => exact map_zero _
    | add u w _ _ ihu ihw => rw [map_add, ihu, ihw, add_zero]
    | smul c w _ ihw => rw [map_smul, ihw, smul_zero]
  have hdall : ∀ i, d i = 0 := fun i => by rw [hcoord i]; exact hφvan (v i) (hviS i)
  have hd0 : d = 0 := by
    refine DFunLike.ext _ _ fun i => ?_
    rw [hdall i, hzero i]
  rwa [hd, sub_eq_zero] at hd0

/-- **[Buz07] Lemma 2.3(b)** over a Banach–Tate ring ([Lud24] Lemma 2.26(2),
Exercise 2.27): finitely generated submodules of the model space are closed.

*Proof sketch.*  Choose `S` with `π_S` injective on `P` (Lemma 2.3(a)).  The
`S`-supported submodule `M_S := range (π_S)` is module-finite (spanned by the
`eⱼ, j ∈ S`) and closed, so `Q := π_S(P) ⊆ M_S` is closed in it by `isClosed_of_finite`
and hence complete.  The algebraic inverse `g : Q → c(I, R)` of `π_S|_P` is continuous:
factor a surjection `Rᵏ ↠ Q` (continuous, since `Q` is f.g. and the generators map to
elements of `c(I,R)` — finite combinations are continuous), apply the open mapping
theorem to make it open, and descend.  Now `π_S ∘ g = (Q ↪ M_S)`, so `g` is a closed
embedding: if `g(qₙ) → y` then `qₙ = π_S(g(qₙ)) → π_S y ∈ Q` (closedness of `Q`), and
continuity gives `y = g(π_S y) ∈ P`.  Hence `P = g(Q)` is closed. -/
theorem isClosed_of_fg [IsTate R] [IsNoetherianRing R]
    (P : Submodule R c(I, R)) (hP : P.FG) : IsClosed (P : Set c(I, R)) := by
  classical
  -- Step 1: a truncation `π_S` injective on `P` (Lemma 2.3(a)).
  obtain ⟨S, hSinj⟩ := exists_truncation_injOn P hP
  -- Step 2: the `S`-supported submodule `W`, closed and module-finite.
  have htrunc_single : ∀ j ∈ S, truncation S (cSpace.single j (1 : R)) = cSpace.single j 1 := by
    intro j hj
    refine DFunLike.ext _ _ fun i => ?_
    rw [truncation_apply]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
    · rw [if_neg hi]
      rcases eq_or_ne i j with rfl | hij
      · exact absurd hj hi
      · rw [cSpace.single_apply_of_ne hij]
  set W : Submodule R c(I, R) :=
    Submodule.span R ((fun j => cSpace.single j (1 : R)) '' (S : Set I)) with hW
  have hWfg : W.FG := Submodule.fg_span (S.finite_toSet.image (fun j => cSpace.single j (1 : R)))
  haveI : Module.Finite R ↥W := Module.Finite.iff_fg.2 hWfg
  have hW_fixed : ∀ f ∈ W, truncation S f = f := by
    intro f hf
    rw [hW] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hjS, rfl⟩ := hx
        exact htrunc_single j (Finset.mem_coe.1 hjS)
    | zero => exact map_zero _
    | add u w _ _ ihu ihw => rw [map_add, ihu, ihw]
    | smul c u _ ih => rw [map_smul, ih]
  have hWclosed : IsClosed (W : Set c(I, R)) := by
    have hset : (W : Set c(I, R)) = {g | truncation S g = g} := by
      ext f
      constructor
      · intro hf; exact hW_fixed f hf
      · intro hf; rw [SetLike.mem_coe, hW, ← hf]; exact truncation_mem_span S f
    rw [hset]
    exact isClosed_eq (truncation S).continuous continuous_id
  haveI : CompleteSpace ↥W := hWclosed.isComplete.completeSpace_coe
  haveI : IsBoundedSMul R ↥W := .of_norm_smul_le fun r x => by
    simp only [Submodule.coe_norm, SetLike.val_smul]
    exact norm_smul_le r (x : c(I, R))
  -- Step 3: `Q := π_S(P) ≤ W`; closed in `↥W` by `isClosed_of_finite`, transport to `c(I,R)`.
  set Q : Submodule R c(I, R) := P.map (truncation (R := R) S).toLinearMap with hQ
  have hQfg : Q.FG := by rw [hQ]; exact Submodule.FG.map _ hP
  have hQW : Q ≤ W := by
    rw [hQ, Submodule.map_le_iff_le_comap]
    intro p _; exact truncation_mem_span S p
  set Q'' : Submodule R ↥W := Q.comap W.subtype with hQ''
  have hQ''closed : IsClosed (Q'' : Set ↥W) := isClosed_of_finite Q''
  have hmapeq : Submodule.map W.subtype Q'' = Q := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hy; exact ⟨⟨y, hQW hy⟩, hy, rfl⟩
  have hQclosed : IsClosed (Q : Set c(I, R)) := by
    rw [← hmapeq, Submodule.map_coe, Submodule.coe_subtype]
    exact hWclosed.isClosedMap_subtype_val _ hQ''closed
  haveI : CompleteSpace ↥Q := hQclosed.isComplete.completeSpace_coe
  haveI : IsBoundedSMul R ↥Q := .of_norm_smul_le fun r x => by
    simp only [Submodule.coe_norm, SetLike.val_smul]
    exact norm_smul_le r (x : c(I, R))
  -- Step 4: generators of `Q`, their chosen `P`-preimages `pp`.
  obtain ⟨tt, qgen, hqgen⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hQfg
  have hqmem : ∀ i, qgen i ∈ Q := fun i => by
    rw [← hqgen]; exact Submodule.subset_span (Set.mem_range_self i)
  have hpre : ∀ i, ∃ p ∈ P, truncation S p = qgen i := fun i => by
    have hmem := hqmem i; rw [hQ, Submodule.mem_map] at hmem; exact hmem
  choose pp hpp_mem hpp_eq using hpre
  -- Step 5: the continuous surjection `ρ : Rᵗ → ↥Q` and the OMT.
  have hmemQ : ∀ a : Fin tt → R, Fintype.linearCombination R qgen a ∈ Q := fun a => by
    rw [Fintype.linearCombination_apply, ← hqgen]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hboundρ : ∀ a : Fin tt → R,
      ‖((Fintype.linearCombination R qgen).codRestrict Q hmemQ) a‖ ≤ (∑ i, ‖qgen i‖) * ‖a‖ :=
    fun a => by
    rw [Submodule.coe_norm, LinearMap.codRestrict_apply, Fintype.linearCombination_apply]
    calc ‖∑ i, a i • qgen i‖ ≤ ∑ i, ‖a i • qgen i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖qgen i‖ * ‖a‖ := Finset.sum_le_sum fun i _ => by
          calc ‖a i • qgen i‖ ≤ ‖a i‖ * ‖qgen i‖ := norm_smul_le _ _
          _ ≤ ‖a‖ * ‖qgen i‖ := mul_le_mul_of_nonneg_right (norm_le_pi_norm a i) (norm_nonneg _)
          _ = ‖qgen i‖ * ‖a‖ := mul_comm _ _
    _ = (∑ i, ‖qgen i‖) * ‖a‖ := by rw [Finset.sum_mul]
  let ρ : (Fin tt → R) →L[R] ↥Q :=
    ((Fintype.linearCombination R qgen).codRestrict Q hmemQ).mkContinuous (∑ i, ‖qgen i‖) hboundρ
  have hρ_coe : ∀ a : Fin tt → R, (ρ a : c(I, R)) = ∑ i, a i • qgen i := fun _ => rfl
  have hρsurj : Function.Surjective ρ := fun y => by
    have hy : (y : c(I, R)) ∈ Submodule.span R (Set.range qgen) := by rw [hqgen]; exact y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, Subtype.ext (by rw [hρ_coe]; exact ha)⟩
  obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le ρ hρsurj
  -- The pointwise inverse bound: `‖z‖ ≤ C·B·‖π_S z‖` for `z ∈ P` (`B = ∑ ‖ppᵢ‖`).
  set B : ℝ := ∑ i, ‖pp i‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hpb : ∀ z ∈ P, ‖z‖ ≤ C * B * ‖truncation S z‖ := fun z hz => by
    have hzQ : truncation S z ∈ Q := by rw [hQ]; exact Submodule.mem_map_of_mem hz
    obtain ⟨a, ha_eq, ha_norm⟩ := hC ⟨truncation S z, hzQ⟩
    have haq : ∑ i, a i • qgen i = truncation S z := by
      rw [← hρ_coe a]; exact congrArg (fun w : ↥Q => (w : c(I, R))) ha_eq
    set w := ∑ i, a i • pp i with hw
    have hwP : w ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpp_mem i)
    have htw : truncation S w = truncation S z := by
      rw [hw, map_sum, ← haq]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hpp_eq i]
    have hwz : w = z := hSinj hwP hz htw
    calc ‖z‖ = ‖∑ i, a i • pp i‖ := by rw [← hwz, hw]
    _ ≤ C * B * ‖truncation S z‖ := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (mul_nonneg (mul_nonneg hC0.le hB0) (norm_nonneg _)) fun i _ => ?_
        calc ‖a i • pp i‖ ≤ ‖a i‖ * ‖pp i‖ := norm_smul_le _ _
        _ ≤ ‖a‖ * B := mul_le_mul (norm_le_pi_norm a i)
              (Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i))
              (norm_nonneg _) (norm_nonneg _)
        _ ≤ (C * ‖truncation S z‖) * B := mul_le_mul_of_nonneg_right ha_norm hB0
        _ = C * B * ‖truncation S z‖ := by ring
  -- Step 6: `P` is sequentially closed (hence closed).
  refine IsSeqClosed.isClosed ?_
  intro pn y hpn_mem hpn_lim
  have hqn_lim : Tendsto (fun n => truncation S (pn n)) atTop (𝓝 (truncation S y)) :=
    ((truncation S).continuous.tendsto y).comp hpn_lim
  have hQyQ : truncation S y ∈ Q :=
    hQclosed.mem_of_tendsto hqn_lim
      (Filter.Eventually.of_forall fun n => by rw [hQ]; exact Submodule.mem_map_of_mem (hpn_mem n))
  obtain ⟨ainf, hainf_eq, -⟩ := hC ⟨truncation S y, hQyQ⟩
  set pstar := ∑ i, ainf i • pp i with hpstar
  have hpstarP : pstar ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpp_mem i)
  have haqinf : ∑ i, ainf i • qgen i = truncation S y := by
    rw [← hρ_coe ainf]; exact congrArg (fun w : ↥Q => (w : c(I, R))) hainf_eq
  have htps : truncation S pstar = truncation S y := by
    rw [hpstar, map_sum, ← haqinf]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hpp_eq i]
  have hpn_pstar : Tendsto pn atTop (𝓝 pstar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hup : Tendsto (fun n => C * B * ‖truncation S (pn n) - truncation S y‖) atTop (𝓝 0) := by
      have hsub0 : Tendsto (fun n => truncation S (pn n) - truncation S y) atTop (𝓝 0) := by
        simpa using hqn_lim.sub (tendsto_const_nhds (x := truncation S y))
      simpa using hsub0.norm.const_mul (C * B)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hup
    have hmem : pn n - pstar ∈ P := Submodule.sub_mem P (hpn_mem n) hpstarP
    have hb := hpb (pn n - pstar) hmem
    rwa [map_sub, htps] at hb
  rw [tendsto_nhds_unique hpn_lim hpn_pstar]
  exact hpstarP

end ModelSpace

section Bridge

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

private theorem norm_matrixCoeff_le'' [IsTate R] (u : c(I, R) →L[R] c(J, R)) (j : J)
    (i : I) : ‖matrixCoeff u j i‖ ≤ ‖u‖ :=
  calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
  _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
  _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]

/-- Completely continuous ⟹ compactoid over a **Noetherian** Banach–Tate ring ([Bel]
Prop II.1.9 ⇒, [JN]'s setting; the II.1.8 step needs f.g. submodules closed — exactly
the Noetherian input, supplied by `isClosed_of_fg`). -/
theorem IsCompletelyContinuous.isCompactoid [IsTate R] [IsNoetherianRing R]
    {u : c(I, R) →L[R] c(J, R)} (hu : IsCompletelyContinuous u) : IsCompactoid u := by
  rw [IsCompactoid, Metric.tendsto_nhds]
  intro ε hε
  have hε6 : (0 : ℝ) < ε / 6 := by positivity
  obtain ⟨v, hvfr, hvu⟩ := hu (ε / 6) hε6
  obtain ⟨Q, hQfg, hQrange⟩ := hvfr
  have hv1 : (0 : ℝ) < ‖v‖ + 1 :=
    lt_of_lt_of_le one_pos (by simpa using opNorm_nonneg v)
  have hε'0 : 0 < ε / 6 / (‖v‖ + 1) := div_pos hε6 hv1
  obtain ⟨T, hT⟩ := exists_truncation_near Q hQfg (isClosed_of_fg Q hQfg) hε'0
  -- `π_T ∘ u` is `ε/2`-close to `u`: a vector-level three-term estimate
  have hTu : ‖(truncation T).comp u - u‖ ≤ ε / 2 := by
    refine opNorm_le_of_forall _ (half_pos hε).le fun f => ?_
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    have hdec : truncation T (u f) - u f
        = truncation T ((u - v) f) + (truncation T (v f) - v f) + ((v - u) f) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      abel
    rw [hdec]
    have e1 : ‖truncation T ((u - v) f)‖ ≤ ε / 6 * ‖f‖ :=
      (norm_truncation_apply_le _ _).trans ((le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hvu.le (norm_nonneg f)))
    have e2 : ‖truncation T (v f) - v f‖ ≤ ε / 6 * ‖f‖ := by
      have hmem : v f ∈ Q := hQrange ⟨f, rfl⟩
      refine (hT (v f) hmem).trans ?_
      calc ε / 6 / (‖v‖ + 1) * ‖v f‖
          ≤ ε / 6 / (‖v‖ + 1) * ((‖v‖ + 1) * ‖f‖) := by
            refine mul_le_mul_of_nonneg_left ((le_opNorm v f).trans ?_) hε'0.le
            exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f)
      _ = ε / 6 * ‖f‖ := by rw [← mul_assoc, div_mul_cancel₀ _ hv1.ne']
    have e3 : ‖(v - u) f‖ ≤ ε / 6 * ‖f‖ := by
      rw [ContinuousLinearMap.sub_apply, norm_sub_rev,
        ← ContinuousLinearMap.sub_apply]
      exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hvu.le (norm_nonneg f))
    calc ‖truncation T ((u - v) f) + (truncation T (v f) - v f) + (v - u) f‖
        ≤ ‖truncation T ((u - v) f) + (truncation T (v f) - v f)‖ + ‖(v - u) f‖ :=
          _root_.norm_add_le _ _
    _ ≤ (‖truncation T ((u - v) f)‖ + ‖truncation T (v f) - v f‖) + ‖(v - u) f‖ :=
          add_le_add (_root_.norm_add_le _ _) le_rfl
    _ ≤ (ε / 6 * ‖f‖ + ε / 6 * ‖f‖) + ε / 6 * ‖f‖ := add_le_add (add_le_add e1 e2) e3
    _ ≤ ε / 2 * ‖f‖ := le_of_eq (by ring)
  -- rows off `T` are dominated by `‖π_T∘u − u‖`
  filter_upwards [T.eventually_cofinite_notMem] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)]
  have hrow : rowNorm u j ≤ ε / 2 := by
    refine Real.iSup_le (fun i => ?_) (half_pos hε).le
    have hz : (truncation T (u (cSpace.single i 1))) j = 0 := by
      rw [truncation_apply, if_neg hj]
    have hmc : matrixCoeff u j i
        = -(matrixCoeff ((truncation T).comp u - u) j i) := by
      show u (cSpace.single i 1) j
        = -(((truncation T).comp u - u) (cSpace.single i 1) j)
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      show u (cSpace.single i 1) j
        = -(truncation T (u (cSpace.single i 1)) j - u (cSpace.single i 1) j)
      rw [hz, zero_sub, neg_neg]
    rw [hmc, norm_neg]
    exact (norm_matrixCoeff_le'' _ j i).trans hTu
  exact lt_of_le_of_lt hrow (half_lt_self hε)

/-- **The compactness criterion over a Noetherian Banach–Tate ring** ([JN]'s statement;
[Bel] Proposition II.1.9): `u` is compact iff its row sups tend to `0` cofinitely.

The Noetherian hypothesis buys exactly [Bel] Hypothesis 3.1.8 (closedness of finitely
generated submodules) via `isClosed_of_fg`; without it the `⇒` direction fails, while `⇐`
(`IsCompactoid.isCompletelyContinuous`) holds over any Banach–Tate ring. -/
theorem isCompletelyContinuous_iff_rowNorm [IsTate R] [IsNoetherianRing R]
    (u : c(I, R) →L[R] c(J, R)) :
    IsCompletelyContinuous u ↔ Tendsto (rowNorm u) cofinite (𝓝 0) :=
  ⟨fun hu => hu.isCompactoid, fun hu => IsCompactoid.isCompletelyContinuous hu⟩

end Bridge

end TateFredholm

end
