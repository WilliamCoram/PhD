/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import PhD.Main.TateFredholm.«00_Charpoly»
import PhD.Main.TateFredholm.«11_Coleman»
import PhD.Main.TateFredholm.«06_Pr»

/-!
# Riesz theory for a coprime factorisation `det(1 − Tu) = Q·S`

**[JN] Theorem 2.2.2** (= [Buz07] Theorem 3.3, = [Bel] Theorem II.2.18, ultimately
Coleman [Col97, Theorem A4.3]): for a compact `u` with Fredholm determinant `F = QS`, `Q` a
multiplicative polynomial relatively prime to the Fredholm series `S`, the module splits as
`Ker Q*(u) ⊕ N` with `Ker Q*(u)` finitely generated projective of rank `deg Q`, `N` the unique
`u`-stable closed complement on which `Q*(u)` is invertible, the projectors in the closure of
`R[u]`, `det(1 − Tu | Ker Q*(u)) = Q`, `u` invertible on `Ker Q*(u)`, and `det(1 − Tu | N) = S`.

Here `M = c(I, R)` over a Banach–Tate ring (no Noetherian hypothesis — none is used by the
sources' proofs), `u` compactoid, `Q*(u) = aeval u Q.reverse`.

The proof is Bellaïche's: `φ' = 1 − Q*(φ)/Q*(0)` is compact with Fredholm determinant
`D(1 − Q̃*, P_φ)` ([Bel] II.2.16, `Coleman.charPowerSeries_aeval`), which has a good zero of
order `deg Q` at `1` ([Bel] II.2.15, `Coleman.isGoodZero_dSeries_bQ`); Serre's projector
`exists_rieszProjection_isOpLimit` at `a = 1` then gives the decomposition, with the projector
and its inverse witness in the closure of `R[u]` (`IsOpLimitAeval`, 09_Riesz.lean), so that they
commute with `u` and not merely with `φ'`.  The refinements — that
`Q*(u)` is *zero* (not merely nilpotent) on `N`, the rank, and the determinant identities —
follow [Buz07] Proposition 3.2 / Theorem 3.3 and [JN]'s last sentence.

## Main results

* `exists_rieszColemanProjection`: the projector `p` of [JN] 2.2.2, with `Q*(u) w = p` and
  `Q*(u) ^ deg Q · (1 − p) = 0`, `p` and `w` in the closure of `R[u]`.
* `IsRieszColemanProjection`: the standing hypotheses of the refinements, with `.finite`,
  `.projective`, `.rankAtStalk` (`Ker Q*(u)` is projective of rank `deg Q` at every prime),
  `.charPowerSeries_mul_one_sub` (`det(1 − Tu | Ker Q*(u)) = Q`), `.charPowerSeries_mul`
  (`det(1 − Tu | N) = S`), `.aeval_reverse_mul_one_sub` and `.ker_aeval_reverse`
  (`Ker Q*(u) = range (1 − p)`), `.isUnit_mul_one_sub_add` (`u` invertible on `Ker Q*(u)`),
  `.eq_range_of_isTopCompl` (uniqueness of the complement) and
  `.isUnit_aeval_reverse_of_isEntireCoprime` (the slope-decomposition core of [JN] 2.2.13).
* `isEntireCoprime_iff_isUnit_aeval_reverse`: [Buz07] Lemma 3.1.
* `charPowerSeries_eq_mul_of_comm`, `exists_polynomial_charPowerSeries_of_range_le`,
  `exists_matrix_realisation`: multiplicativity, polynomiality and the matrix realisation of
  the Fredholm determinant on a finitely generated summand.
-/

open Filter Topology Polynomial

noncomputable section

namespace TateFredholm

open Coleman

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
  [IsTate R] {I : Type*} [DecidableEq I]

section Projector

variable {u : c(I, R) →L[R] c(I, R)} {Q : R[X]} {S : PowerSeries R} {v : Rˣ}

omit [IsTate R] [DecidableEq I] in
/-- Bellaïche's `φ' = 1 − Q̃*(u)` satisfies `1 − φ' = v⁻¹ Q*(u)`. -/
theorem one_sub_aeval_bQ (u : c(I, R) →L[R] c(I, R)) {Q : R[X]} (v : Rˣ) :
    (1 : c(I, R) →L[R] c(I, R)) - Polynomial.aeval u (bQ Q v) =
      ((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse := by
  rw [bQ, map_sub, map_one, map_mul, Polynomial.aeval_C, sub_sub_cancel, Algebra.smul_def]

/-- **The Riesz–Coleman projector** ([Bel] Theorem II.2.18 = [JN] Theorem 2.2.2, existence
part): for `det(1 − Tu) = QS` with `Q` multiplicative (`Q(0) = 1`, leading coefficient the
unit `v`) relatively prime to the entire `S`, there is an idempotent `p` commuting with `u`
such that `Q*(u)` is nilpotent (of exponent `deg Q`) on `range (1 − p)` and invertible on
`range p` (witness `w`).  Obtained from `exists_rieszProjection` for `φ' = aeval u (bQ Q v)`
at `a = 1`, order `deg Q` (`Coleman.isGoodZero_dSeries_bQ`). -/
theorem exists_rieszColemanProjection (hu : IsCompactoid u) (hQ0 : Q.coeff 0 = 1)
    (hv : (v : R) = Q.leadingCoeff) (hS : PowerSeries.IsEntire S)
    (hS0 : PowerSeries.coeff 0 S = 1) (hF : charPowerSeries u = (Q : PowerSeries R) * S)
    (hcop : PowerSeries.IsEntireCoprime (Q : PowerSeries R) S) :
    ∃ p w : c(I, R) →L[R] c(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      (Polynomial.aeval u Q.reverse) ^ Q.natDegree * (1 - p) = 0 ∧
      Polynomial.aeval u Q.reverse * w = p := by
  have : Nontrivial R := NormOneClass.nontrivial
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
  · obtain rfl : Q = 1 := by rw [eq_C_of_natDegree_eq_zero h0, hQ0, C_1]
    have hrev : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C, C_1]
    exact ⟨1, 1, one_mul 1, (mul_one u).trans (one_mul u).symm, (mul_one u).trans (one_mul u).symm,
      rfl, by simp, by simp [hrev]⟩
  · have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero hv
    have hgood : PowerSeries.IsGoodZero (charPowerSeries (Polynomial.aeval u (bQ Q v))) 1
        Q.natDegree := by
      rw [charPowerSeries_aeval hu _ hB0, hF]
      exact isGoodZero_dSeries_bQ Q v hQ0 hv hS hS0 hcop
    obtain ⟨p, w, hp, -, -, hpw, hnil, hw, hpl, hwl⟩ :=
      exists_rieszProjection_isOpLimit (hu.aeval _ hB0) hpos hgood.1 hgood.2
    rw [one_smul, one_sub_aeval_bQ] at hnil hw
    have hup : u * p = p * u := (hpl.comp.commute rfl).symm
    have huw : u * w = w * u := (hwl.comp.commute rfl).symm
    refine ⟨p, ((v⁻¹ : Rˣ) : R) • w, hp, hup, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul_comm, huw, smul_mul_assoc]
    · rw [mul_smul_comm, hpw, smul_mul_assoc]
    · have h1 : Polynomial.aeval u Q.reverse ^ Q.natDegree * (1 - p) =
          ((v : R) ^ Q.natDegree * ((v⁻¹ : Rˣ) : R) ^ Q.natDegree) •
            (Polynomial.aeval u Q.reverse ^ Q.natDegree * (1 - p)) := by
        rw [← mul_pow, Units.mul_inv, one_pow, one_smul]
      rw [h1, mul_smul, ← smul_mul_assoc, ← smul_pow, hnil, smul_zero]
    · rw [mul_smul_comm, ← smul_mul_assoc, hw]

end Projector

section Restriction

variable {φ p : c(I, R) →L[R] c(I, R)}

/-- The restriction of `φ` to the range of a commuting idempotent `p`. -/
def restrictRange (φ p : c(I, R) →L[R] c(I, R)) (hφp : φ * p = p * φ) :
    ↥p.range →L[R] ↥p.range :=
  (φ.comp p.range.subtypeL).codRestrict p.range fun x ↦ by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 x.2
    refine LinearMap.mem_range.2 ⟨φ y, ?_⟩
    show p (φ y) = φ (x : c(I, R))
    rw [← hy]
    exact (DFunLike.congr_fun hφp y).symm

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
@[simp] theorem coe_restrictRange_apply (hφp : φ * p = p * φ) (x : ↥p.range) :
    (restrictRange φ p hφp x : c(I, R)) = φ x := rfl

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
/-- Membership in the range of an idempotent: `x ∈ range p ↔ p x = x`. -/
theorem mem_range_iff_of_idempotent (hp : p * p = p) {x : c(I, R)} : x ∈ p.range ↔ p x = x :=
  ⟨fun ⟨y, hy⟩ ↦ by rw [← hy]; exact DFunLike.congr_fun hp y, fun h ↦ ⟨x, h⟩⟩

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
/-- The range of a continuous idempotent is closed (`range p = ker (1 − p)`). -/
theorem isClosed_range_of_idempotent (hp : p * p = p) :
    IsClosed (p.range : Set (c(I, R))) := by
  have : (p.range : Set (c(I, R))) = {x | p x = x} :=
    Set.ext fun x ↦ mem_range_iff_of_idempotent hp
  rw [this]
  exact isClosed_eq p.continuous continuous_id

omit [IsUltrametricDist R] [NormOneClass R] [IsTate R] [DecidableEq I] in
/-- The range of a continuous idempotent of a Banach model space is Banach. -/
theorem completeSpace_range_of_idempotent (hp : p * p = p) : CompleteSpace ↥p.range :=
  (isClosed_range_of_idempotent hp).isComplete.completeSpace_coe

omit [IsTate R] [DecidableEq I] in
/-- Submodules of the model space are normed `R`-modules in the bounded sense. -/
theorem isBoundedSMul_range : IsBoundedSMul R ↥p.range :=
  IsBoundedSMul.of_norm_smul_le fun r x ↦ norm_smul_le r (x : c(I, R))

omit [DecidableEq I] in
/-- The restriction of a completely continuous operator to the range of a commuting
idempotent is completely continuous (finite-rank approximants restrict: `p ∘ v ∘ ι`). -/
theorem IsCompletelyContinuous.restrictRange (hφ : IsCompletelyContinuous φ) (hp : p * p = p)
    (hφp : φ * p = p * φ) : IsCompletelyContinuous (restrictRange φ p hφp) := by
  intro ε hε
  have hp1 : 0 < ‖p‖ + 1 := by linarith [opNorm_nonneg p]
  obtain ⟨v, hv, hvε⟩ := hφ (ε / (‖p‖ + 1)) (div_pos hε hp1)
  refine ⟨(p.codRestrict p.range fun x ↦ LinearMap.mem_range_self _ x).comp
    (v.comp p.range.subtypeL), (hv.comp_right _).comp_left _, ?_⟩
  refine lt_of_le_of_lt (opNorm_le_of_forall _
    (mul_nonneg (opNorm_nonneg p) (opNorm_nonneg (φ - v))) fun x ↦ ?_) ?_
  · have hx : p (x : c(I, R)) = x := (mem_range_iff_of_idempotent hp).1 x.2
    have hφx : p (φ x) = φ x := by
      have h := DFunLike.congr_fun hφp (x : c(I, R))
      change φ (p (x : c(I, R))) = p (φ x) at h
      rw [hx] at h
      exact h.symm
    rw [Submodule.coe_norm, Submodule.coe_norm, sub_apply, Submodule.coe_sub,
      coe_restrictRange_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← hφx, ← map_sub, mul_assoc]
    exact (le_opNorm p _).trans (mul_le_mul_of_nonneg_left (le_opNorm (φ - v) _) (opNorm_nonneg p))
  · calc ‖p‖ * ‖φ - v‖ ≤ (‖p‖ + 1) * ‖φ - v‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (opNorm_nonneg _)
      _ < ε := by
        rw [mul_comm]
        exact (lt_div_iff₀ hp1).1 hvε

omit [IsTate R] [DecidableEq I] in
/-- Nilpotency of `1 − φ` on `range p` transfers to the restriction. -/
theorem restrictRange_one_sub_pow_eq_zero (hp : p * p = p) (hφp : φ * p = p * φ) {n : ℕ}
    (hnil : (1 - φ) ^ n * p = 0) : (1 - restrictRange φ p hφp) ^ n = 0 := by
  have hpow : ∀ (k : ℕ) (x : ↥p.range),
      (((1 - restrictRange φ p hφp) ^ k) x : c(I, R)) = ((1 - φ) ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← ih x, sub_apply,
        sub_apply, Submodule.coe_sub, ContinuousLinearMap.one_def, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, coe_restrictRange_apply]
  ext x
  have hx : p (x : c(I, R)) = x := (mem_range_iff_of_idempotent hp).1 x.2
  rw [hpow, ← hx, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hnil]
  simp

omit [DecidableEq I] in
/-- **[Bel] Proposition II.1.21 on the range of an idempotent** (Noetherian-free, as its
proof): if `p` is a continuous idempotent of `c(I, R)`, `φ` a completely continuous operator
commuting with `p`, and `1 − φ` nilpotent on `range p`, then `range p` is finitely
generated (`finite_of_one_sub_compact_nilpotent` on the Banach module `range p`). -/
theorem finite_range_of_one_sub_nilpotent (hφ : IsCompletelyContinuous φ) (hp : p * p = p)
    (hφp : φ * p = p * φ) {n : ℕ} (hnil : (1 - φ) ^ n * p = 0) :
    Module.Finite R ↥p.range := by
  haveI := completeSpace_range_of_idempotent hp
  haveI := isBoundedSMul_range (p := p)
  exact finite_of_one_sub_compact_nilpotent (restrictRange φ p hφp) (hφ.restrictRange hp hφp)
    ⟨n, restrictRange_one_sub_pow_eq_zero hp hφp hnil⟩

/-- A finitely generated range of an idempotent is a continuous retract of a finite free
module: a continuous surjection `g : Rʳ → range p` with a continuous section `ι` (lift the
identity through `g` using the lifting property of `c(I, R)`, `exists_lift_cSpace`). -/
theorem exists_retraction_of_finite (hp : p * p = p) [Module.Finite R ↥p.range] :
    ∃ (r : ℕ) (g : (Fin r → R) →L[R] ↥p.range) (ι : ↥p.range →L[R] (Fin r → R)),
      g.comp ι = ContinuousLinearMap.id R ↥p.range := by
  haveI := completeSpace_range_of_idempotent hp
  haveI := isBoundedSMul_range (p := p)
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R ↥p.range
  let F : (Fin n → R) →L[R] ↥p.range := ⟨g, continuous_linearMap_pi g⟩
  obtain ⟨β₀, hβ₀⟩ :=
    exists_lift_cSpace F hg (p.codRestrict p.range fun x ↦ LinearMap.mem_range_self _ x)
  refine ⟨n, F, β₀.comp p.range.subtypeL, ?_⟩
  ext x
  have hx : p (x : c(I, R)) = x := (mem_range_iff_of_idempotent hp).1 x.2
  have h2 := congrArg Subtype.val (DFunLike.congr_fun hβ₀ (x : c(I, R)))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_codRestrict_apply, hx] at h2
  exact h2

/-- **[Bel] Proposition II.1.20 / [JN] "finitely generated and projective"**: a finitely
generated direct summand of a model space is projective (lift the identity through a
surjection `Rⁿ → range p` using the lifting property of `c(I, R)`, `exists_lift_cSpace`).
Idempotent form of `HasPr.projective`, whose `Set`-indexed model space cannot be applied to a
summand of `c(I, R)` directly. -/
theorem projective_range_of_finite (hp : p * p = p) [Module.Finite R ↥p.range] :
    Module.Projective R ↥p.range := by
  obtain ⟨r, g, ι, hgι⟩ := exists_retraction_of_finite hp
  exact Module.Projective.of_split ι.toLinearMap g.toLinearMap
    (LinearMap.ext fun x ↦ DFunLike.congr_fun hgι x)

end Restriction

section Multiplicativity

/-- **Orthogonal multiplicativity of the Fredholm determinant** ([Buz07] p. 20: "if `M` and
`N` both have property (Pr) and `φ : M → M`, `ψ : N → N` are compact, then
`det(1 − X(φ ⊕ ψ)) = det(1 − Xφ) det(1 − Xψ)`"; [Bel] proof of II.2.18): for compactoid `v, w`
with `vw = wv = 0`, `det(1 − T(v + w)) = det(1 − Tv) det(1 − Tw)`.  From `fredholmDet_mul`
at every `ϖᵏ` and the identity theorem `IsEntire.eq_zero_of_forall_evalT_pow_eq_zero`. -/
theorem charPowerSeries_add_of_mul_eq_zero {v w : c(I, R) →L[R] c(I, R)} (hv : IsCompactoid v)
    (hw : IsCompactoid w) (hvw : v * w = 0) :
    charPowerSeries (v + w) = charPowerSeries v * charPowerSeries w := by
  obtain ⟨ϖ⟩ := IsTate.nonempty_pseudoUniformizer (A := R)
  have hent : ∀ {u : c(I, R) →L[R] c(I, R)}, IsCompactoid u →
      PowerSeries.IsEntire (charPowerSeries u) := fun hu c hc ↦ charPowerSeries_isEntire _ hu c hc
  have key : ∀ a : R, PowerSeries.evalT a (charPowerSeries (v + w)) =
      PowerSeries.evalT a (charPowerSeries v) * PowerSeries.evalT a (charPowerSeries w) := by
    intro a
    rw [← fredholmDet_smul a _ (hv.add hw), ← fredholmDet_smul a _ hv, ← fredholmDet_smul a _ hw,
      ← fredholmDet_mul (hv.smul a) (hw.smul a)]
    congr 1
    rw [smul_add, smul_mul_assoc, mul_smul_comm, hvw, smul_zero, smul_zero, sub_zero]
  rw [← sub_eq_zero]
  refine ((hent (hv.add hw)).sub ((hent hv).mul (hent hw))).eq_zero_of_forall_evalT_pow_eq_zero ϖ
    fun k ↦ ?_
  rw [(hent (hv.add hw)).evalT_sub ((hent hv).mul (hent hw)), (hent hv).evalT_mul (hent hw), key,
    sub_self]

/-- Orthogonal splitting of the Fredholm determinant along an idempotent `p` commuting with
`x`: `det(1 − Tx) = det(1 − Tx(1 − p)) · det(1 − Txp)`. -/
theorem charPowerSeries_eq_mul_of_comm {x p : c(I, R) →L[R] c(I, R)} (hx : IsCompactoid x)
    (hp : p * p = p) (hxp : x * p = p * x) :
    charPowerSeries x = charPowerSeries (x * (1 - p)) * charPowerSeries (x * p) := by
  have hcomm : x * (1 - p) = (1 - p) * x := by rw [mul_sub, mul_one, sub_mul, one_mul, hxp]
  have hpp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hvw : x * (1 - p) * (x * p) = 0 := by
    rw [mul_assoc, ← mul_assoc (1 - p), ← hcomm, mul_assoc x, hpp, mul_zero, mul_zero]
  have huv : x * (1 - p) + x * p = x := by rw [← mul_add, sub_add_cancel, mul_one]
  nth_rw 1 [← huv]
  exact charPowerSeries_add_of_mul_eq_zero (hx.comp_right (1 - p)) (hx.comp_right p) hvw

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem det_eq_zero_of_rows_mem_span {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {M : Matrix ι ι R} (v : κ → ι → R) (c : ι → κ → R) (hM : ∀ i, M i = ∑ k, c i k • v k)
    (hcard : Fintype.card κ < Fintype.card ι) : M.det = 0 := by
  have hr : ∀ r : ι → κ, ¬ Function.Injective (fun i ↦ v (r i)) := fun r hinj ↦
    absurd (Fintype.card_le_of_injective r hinj.of_comp) (not_le.mpr hcard)
  change Matrix.detRowAlternating M = 0
  rw [show M = fun i ↦ ∑ k, c i k • v k from funext hM, ← AlternatingMap.coe_multilinearMap,
    MultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, AlternatingMap.coe_multilinearMap,
    AlternatingMap.map_eq_zero_of_not_injective _ _ (hr r), smul_zero]

omit [IsTate R] in
private theorem minor_eq_zero_of_range_le {u : c(I, R) →L[R] c(I, R)} {s : Finset c(I, R)}
    (hs : LinearMap.range (u : c(I, R) →ₗ[R] c(I, R)) ≤ Submodule.span R (s : Set c(I, R)))
    (T : Finset I) (hT : s.card < T.card) : minor u T = 0 := by
  have hcoord : ∀ i : I, ∃ g : c(I, R) → R, ∑ f ∈ s, g f • f = u (cSpace.single i 1) := fun i ↦ by
    obtain ⟨g, -, hg⟩ :=
      Submodule.mem_span_finset.1 (hs (LinearMap.mem_range_self _ (cSpace.single i 1)))
    exact ⟨g, hg⟩
  choose g hg using hcoord
  rw [minor, ← Matrix.det_transpose]
  refine det_eq_zero_of_rows_mem_span (κ := s) (fun f j ↦ (f : c(I, R)) (j : I))
    (fun i f ↦ g i f) (fun i ↦ ?_) (by simpa using hT)
  funext j
  have hev := congrArg (cSpace.evalCLM (j : I)) (hg (i : I))
  simp only [map_sum, map_smul, cSpace.evalCLM_apply, smul_eq_mul] at hev
  show matrixCoeff u j i = _
  rw [matrixCoeff, ← hev, ← Finset.sum_coe_sort s, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]

omit [IsTate R] in
/-- The characteristic power series of an operator whose range lies in a submodule generated
by `r` elements is a polynomial of degree `≤ r` ([Buz07] proof of Prop. 3.2: "`P_N` is a
polynomial because `N` is finitely-generated"): all minors of size `> r` vanish, their
columns lying in the span of `r` vectors (`det_eq_zero_of_rows_mem_span`). -/
theorem exists_polynomial_charPowerSeries_of_range_le {u : c(I, R) →L[R] c(I, R)}
    {s : Finset c(I, R)}
    (hs : LinearMap.range (u : c(I, R) →ₗ[R] c(I, R)) ≤ Submodule.span R (s : Set c(I, R))) :
    ∃ G : R[X], G.natDegree ≤ s.card ∧ charPowerSeries u = (G : PowerSeries R) := by
  have hzero : ∀ n, s.card < n → charCoeff u n = 0 := fun n hn ↦ by
    have hz : ∀ T : {T : Finset I // T.card = n}, minor u (T : Finset I) = 0 := fun T ↦
      minor_eq_zero_of_range_le hs _ (T.2.symm ▸ hn)
    simp [charCoeff, tsum_congr hz]
  refine ⟨PowerSeries.trunc (s.card + 1) (charPowerSeries u),
    Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ _), ?_⟩
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [charPowerSeries_coeff]
    exact hzero n (by omega)

end Multiplicativity

section LemmaThreeOne

variable {u : c(I, R) →L[R] c(I, R)} {Q : R[X]} {v : Rˣ}

/-- **[Buz07] Lemma 3.1 = [Col97] Lemma A4.1** (both directions): a multiplicative polynomial
`Q` is relatively prime in `R{{T}}` to `det(1 − Tu)` iff `Q*(u)` is invertible.  Proof
(reconstructed from [Bel] II.2.14–II.2.16 and Serre's Proposition 11, the source's own proof
not being to hand): `Q*(u)` is invertible iff `1 − φ'` is, `φ' = aeval u (bQ Q v)`; by Serre's
Proposition 11 (`isUnit_one_sub_smul_iff_isUnit_evalT` at `a = 1`) iff `P_{φ'}(1)` is a unit;
`P_{φ'} = D(1 − Q̃*, P_u)` (`charPowerSeries_aeval`), and `D(1 − Q̃*, P_u)(1)` is a unit iff
`(Q, P_u) = 1` (`isUnit_evalT_one_dSeries_bQ_iff`). -/
theorem isEntireCoprime_iff_isUnit_aeval_reverse (hu : IsCompactoid u) (hQ0 : Q.coeff 0 = 1)
    (hv : (v : R) = Q.leadingCoeff) :
    PowerSeries.IsEntireCoprime (Q : PowerSeries R) (charPowerSeries u) ↔
      IsUnit (Polynomial.aeval u Q.reverse) := by
  have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero hv
  rw [← isUnit_evalT_one_dSeries_bQ_iff Q v hQ0 hv (fun c hc ↦ charPowerSeries_isEntire u hu c hc),
    ← charPowerSeries_aeval hu _ hB0, ← isUnit_one_sub_smul_iff_isUnit_evalT (hu.aeval _ hB0) 1,
    one_smul, one_sub_aeval_bQ, Algebra.smul_def,
    show algebraMap R (c(I, R) →L[R] c(I, R)) ((v⁻¹ : Rˣ) : R) =
      (Units.map (algebraMap R (c(I, R) →L[R] c(I, R))).toMonoidHom v⁻¹ :
        (c(I, R) →L[R] c(I, R))ˣ) from rfl, Units.isUnit_units_mul]

end LemmaThreeOne

section MatrixRealisation

variable {φ p : c(I, R) →L[R] c(I, R)}

omit [IsTate R] [DecidableEq I] in
/-- Coordinates of the finite model space, `c(Fin r, R) → (Fin r → R)`. -/
def toPi (r : ℕ) : c(Fin r, R) →L[R] (Fin r → R) :=
  ContinuousLinearMap.pi fun i ↦ cSpace.evalCLM i

omit [IsTate R] [DecidableEq I] in
/-- The inverse of `toPi`, `(Fin r → R) → c(Fin r, R)`. -/
def ofPi (r : ℕ) : (Fin r → R) →L[R] c(Fin r, R) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (cSpace.single i (1 : R))

omit [IsTate R] [DecidableEq I] in
@[simp] theorem toPi_apply (r : ℕ) (f : c(Fin r, R)) (i : Fin r) : toPi r f i = f i := rfl

omit [IsTate R] [DecidableEq I] in
@[simp] theorem ofPi_apply (r : ℕ) (v : Fin r → R) (j : Fin r) : ofPi r v j = v j := by
  rw [← cSpace.evalCLM_apply j, ofPi, sum_apply, map_sum, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [cSpace.single_apply_of_ne hij.symm]
  · simp

omit [IsTate R] [DecidableEq I] in
/-- `toPi` inverts `ofPi`. -/
theorem toPi_ofPi (r : ℕ) (v : Fin r → R) : toPi r (ofPi r v) = v := by
  funext i
  simp

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] in
/-- Operators into a finite model space are (trivially) compactoid. -/
theorem isCompactoid_of_finite {J : Type*} [Finite J] (u : c(I, R) →L[R] c(J, R)) :
    IsCompactoid u := by
  rw [IsCompactoid, Filter.cofinite_eq_bot]
  exact tendsto_bot

omit [IsTate R] [DecidableEq I] in
/-- On a finite model space, the characteristic power series is the reversed characteristic
polynomial of the matrix of the operator. -/
theorem charPowerSeries_eq_charpolyRev_of_finite {J : Type*} [DecidableEq J] [Fintype J]
    (w : c(J, R) →L[R] c(J, R)) :
    charPowerSeries w = ((Matrix.of fun j i ↦ matrixCoeff w j i).charpolyRev : PowerSeries R) := by
  ext n
  rw [charPowerSeries_coeff, charCoeff_eq_det_coeff w Finset.univ
    (fun j hj ↦ absurd (Finset.mem_univ j) hj) n, Polynomial.coeff_coe, Matrix.charpolyRev]
  congr 1
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (Finset.mem_univ (α := J)))]
  refine congrArg Matrix.det (Matrix.ext fun j i ↦ ?_)
  by_cases hij : j = i
  · subst hij
    simp
  · simp [hij]

omit [IsTate R] [DecidableEq I] in
/-- The matrix of `ofPi ∘ f ∘ toPi` is the matrix of `f`. -/
theorem matrixCoeff_ofPi_comp_toPi (r : ℕ) (f : (Fin r → R) →L[R] (Fin r → R)) (j i : Fin r) :
    matrixCoeff ((ofPi r).comp (f.comp (toPi r))) j i =
      LinearMap.toMatrix' (f : (Fin r → R) →ₗ[R] (Fin r → R)) j i := by
  rw [LinearMap.toMatrix'_apply]
  show ofPi r (f (toPi r (cSpace.single i 1))) j = _
  rw [ofPi_apply]
  congr 2

-- `ContinuousAdd R` is synthesised through `IsUltrametricDist.nonarchimedeanRing`, so the
-- ultrametric hypothesis cannot be omitted.
omit [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem toMatrix'_pow {r : ℕ} (f : (Fin r → R) →L[R] (Fin r → R)) (k : ℕ) :
    LinearMap.toMatrix' f.toLinearMap ^ k = LinearMap.toMatrix' (f ^ k).toLinearMap := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact LinearMap.toMatrix'_id.symm
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, ContinuousLinearMap.mul_def]
    exact (LinearMap.toMatrix'_comp _ _).symm

-- The trace property on `φ p = (ι_N ∘ g ∘ toPi) ∘ (ofPi ∘ ι ∘ φ p)`, through the finite model
-- space `c(Fin r, R)`.
private theorem charPowerSeries_mul_eq_charpolyRev_of_retraction {r : ℕ} (hp : p * p = p)
    (hφp : φ * p = p * φ) (g : (Fin r → R) →L[R] ↥p.range) (ι : ↥p.range →L[R] (Fin r → R))
    (hgι : ∀ y, g (ι y) = y) :
    charPowerSeries (φ * p) =
      ((LinearMap.toMatrix' (ι.comp ((restrictRange φ p hφp).comp g)).toLinearMap).charpolyRev :
        PowerSeries R) := by
  have hmem : ∀ x, (φ * p) x ∈ p.range := fun x ↦ ⟨φ x, (DFunLike.congr_fun hφp x).symm⟩
  set a : c(Fin r, R) →L[R] c(I, R) := p.range.subtypeL.comp (g.comp (toPi r)) with ha
  set b : c(I, R) →L[R] c(Fin r, R) :=
    (ofPi r).comp (ι.comp ((φ * p).codRestrict p.range hmem)) with hb
  have hab : a.comp b = φ * p := ContinuousLinearMap.ext fun x ↦ by
    simp only [ha, hb, ContinuousLinearMap.comp_apply, toPi_ofPi, hgι, Submodule.subtypeL_apply,
      ContinuousLinearMap.coe_codRestrict_apply]
  have hba : b.comp a =
      (ofPi r).comp ((ι.comp ((restrictRange φ p hφp).comp g)).comp (toPi r)) :=
    ContinuousLinearMap.ext fun v ↦ by
      simp only [hb, ha, ContinuousLinearMap.comp_apply]
      refine congrArg (ofPi r) (congrArg ι (Subtype.ext ?_))
      rw [ContinuousLinearMap.coe_codRestrict_apply, coe_restrictRange_apply,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        (mem_range_iff_of_idempotent hp).1 (g (toPi r v)).2]
  rw [← hab, ← charPowerSeries_comm b a (isCompactoid_of_finite b), hba,
    charPowerSeries_eq_charpolyRev_of_finite,
    show (Matrix.of fun j i ↦ matrixCoeff ((ofPi r).comp
      ((ι.comp ((restrictRange φ p hφp).comp g)).comp (toPi r))) j i) =
      LinearMap.toMatrix' (ι.comp ((restrictRange φ p hφp).comp g)).toLinearMap from
      Matrix.ext fun j i ↦ matrixCoeff_ofPi_comp_toPi r _ j i]

/-- **Matrix realisation of the operators on a finite projective summand**: for `p` idempotent
with finitely generated range there are `r`, a retraction `g : Rʳ → range p`,
`ι : range p → Rʳ` (`g ∘ ι = 1`) and the idempotent `E = ι ∘ g` as an `r × r` matrix, such
that every `φ` commuting with `p` is realised by `Ψ = ι ∘ (φ|_{range p}) ∘ g`, with
`ΨE = EΨ = Ψ`, `E − Ψ` nilpotent as soon as `1 − φ` is nilpotent on `range p`, and
`det(1 − T·φ p) = charpolyRev Ψ` (the trace property `charPowerSeries_comm` on
`φ p = (ι_N ∘ g ∘ toPi) ∘ (ofPi ∘ ι ∘ φ p)`). -/
theorem exists_matrix_realisation (hp : p * p = p) [Module.Finite R ↥p.range] :
    ∃ (r : ℕ) (E : Matrix (Fin r) (Fin r) R) (g : (Fin r → R) →ₗ[R] ↥p.range)
      (ι : ↥p.range →ₗ[R] (Fin r → R)),
      g ∘ₗ ι = LinearMap.id ∧ E = LinearMap.toMatrix' (ι ∘ₗ g) ∧ E * E = E ∧
      ∀ (φ : c(I, R) →L[R] c(I, R)) (hφp : φ * p = p * φ),
        ∃ Ψ : Matrix (Fin r) (Fin r) R,
          Ψ = LinearMap.toMatrix' (ι ∘ₗ (restrictRange φ p hφp).toLinearMap ∘ₗ g) ∧
          Ψ * E = Ψ ∧ E * Ψ = Ψ ∧ ((∃ n, (1 - φ) ^ n * p = 0) → IsNilpotent (E - Ψ)) ∧
          charPowerSeries (φ * p) = (Ψ.charpolyRev : PowerSeries R) := by
  obtain ⟨r, g, ι, hgι⟩ := exists_retraction_of_finite hp
  have hgι' : ∀ y, g (ι y) = y := fun y ↦ DFunLike.congr_fun hgι y
  set El : (Fin r → R) →L[R] (Fin r → R) := ι.comp g with hEl
  have hEE : El.comp El = El := ContinuousLinearMap.ext fun x ↦ by
    simp only [hEl, ContinuousLinearMap.comp_apply, hgι']
  have hM : ∀ f f' : (Fin r → R) →L[R] (Fin r → R),
      LinearMap.toMatrix' f.toLinearMap * LinearMap.toMatrix' f'.toLinearMap =
        LinearMap.toMatrix' (f.comp f').toLinearMap := fun f f' ↦
    (LinearMap.toMatrix'_comp _ _).symm
  refine ⟨r, LinearMap.toMatrix' El.toLinearMap, g.toLinearMap, ι.toLinearMap,
    LinearMap.ext fun x ↦ hgι' x, rfl, by rw [hM, hEE], fun φ hφp ↦ ?_⟩
  set ψ := restrictRange φ p hφp with hψ
  set Ψl : (Fin r → R) →L[R] (Fin r → R) := ι.comp (ψ.comp g) with hΨl
  have hΨE : Ψl.comp El = Ψl := ContinuousLinearMap.ext fun x ↦ by
    simp only [hΨl, hEl, ContinuousLinearMap.comp_apply, hgι']
  have hEΨ : El.comp Ψl = Ψl := ContinuousLinearMap.ext fun x ↦ by
    simp only [hΨl, hEl, ContinuousLinearMap.comp_apply, hgι']
  have hpow : ∀ k, (El - Ψl) ^ (k + 1) = ι.comp (((1 - ψ) ^ (k + 1)).comp g) := by
    intro k
    induction k with
    | zero =>
      ext x
      simp [hEl, hΨl]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
      ext x
      simp [hEl, hΨl, hgι']
  refine ⟨LinearMap.toMatrix' Ψl.toLinearMap, rfl, by rw [hM, hΨE], by rw [hM, hEΨ], ?_,
    charPowerSeries_mul_eq_charpolyRev_of_retraction hp hφp g ι hgι'⟩
  rintro ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  have h0 : (1 - ψ) ^ (n + 1) = 0 := by
    rw [pow_succ, restrictRange_one_sub_pow_eq_zero hp hφp hn, zero_mul]
  rw [← map_sub]
  show LinearMap.toMatrix' (El - Ψl).toLinearMap ^ (n + 1) = 0
  rw [toMatrix'_pow, hpow n, h0]
  simp

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem reflect_eq_reverse_mul_X_pow (P : R[X]) {r : ℕ} (hr : P.natDegree ≤ r) :
    Polynomial.reflect r P = P.reverse * Polynomial.X ^ (r - P.natDegree) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = P.natDegree + d := ⟨r - P.natDegree, by omega⟩
  have h := Polynomial.reflect_mul P 1 le_rfl (by simp : (1 : R[X]).natDegree ≤ d)
  rw [mul_one, ← Polynomial.C_1, Polynomial.reflect_C, Polynomial.C_1, one_mul] at h
  rw [h, Nat.add_sub_cancel_left, Polynomial.reverse]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
-- `charpoly Ψ = Q.reverse · X ^ (r − deg Q)` when `charpolyRev Ψ = Q`.
private theorem charpoly_eq_of_charpolyRev_eq [Nontrivial R] {r : ℕ}
    {Ψ : Matrix (Fin r) (Fin r) R} {Q : R[X]} (hQ : Ψ.charpolyRev = Q) :
    Ψ.charpoly = Q.reverse * Polynomial.X ^ (r - Q.natDegree) := by
  have hr : Q.natDegree ≤ r := by
    rw [← hQ]
    exact (Matrix.natDegree_charpolyRev_le Ψ).trans (Fintype.card_fin r).le
  rw [← reflect_eq_reverse_mul_X_pow Q hr, ← hQ, ← Matrix.reverse_charpoly, Polynomial.reverse,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Polynomial.reflect_reflect]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
-- Polynomials in an operator, transported along an intertwiner `Ψ ∘ ι = ι ∘ ψ`.
private theorem aeval_comp_of_comp_eq {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : M →ₗ[R] N} {ψ : Module.End R M} {Ψ : Module.End R N}
    (h : Ψ ∘ₗ ι = ι ∘ₗ ψ) (P : R[X]) :
    Polynomial.aeval Ψ P ∘ₗ ι = ι ∘ₗ Polynomial.aeval ψ P := by
  refine Polynomial.induction_on' P (fun P Q hP hQ ↦ ?_) (fun k a ↦ ?_)
  · rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hP, hQ]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      LinearMap.smul_comp, LinearMap.comp_smul, Module.End.commute_pow_left_of_commute h]

omit [IsTate R] [DecidableEq I] in
-- Polynomials in `φ|_{range p}` are the restrictions of polynomials in `φ`.
private theorem coe_aeval_restrictRange_apply (hφp : φ * p = p * φ) (P : R[X]) (x : ↥p.range) :
    ((Polynomial.aeval (restrictRange φ p hφp).toLinearMap P x : ↥p.range) : c(I, R)) =
      Polynomial.aeval φ P x := by
  refine Polynomial.induction_on' P (fun P Q hP hQ ↦ ?_) (fun k a ↦ ?_)
  · rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hP, hQ,
      add_apply]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      LinearMap.smul_apply, Submodule.coe_smul]
    change a • _ = a • (φ ^ k) x
    congr 1
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe, coe_restrictRange_apply]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
/-- Naturality of `TensorProduct.piScalarRight`: the base change of a matrix map `Rʳ → Rʳ` is
the map of the reduced matrix. -/
theorem piScalarRight_baseChange {S : Type*} [CommRing S] [Algebra R S] {r : ℕ}
    (f : (Fin r → R) →ₗ[R] (Fin r → R)) (x : TensorProduct R S (Fin r → R)) :
    TensorProduct.piScalarRight R S S (Fin r) (f.baseChange S x) =
      Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap R S))
        (TensorProduct.piScalarRight R S S (Fin r) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      TensorProduct.piScalarRightHom_tmul, Matrix.toLin'_apply]
    funext j
    have hf : f v j = ∑ i, LinearMap.toMatrix' f j i * v i := by
      conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
      rw [Matrix.toLin'_apply]
      rfl
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hf, Algebra.smul_def, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The rank at a prime of a finitely generated projective summand, read off from a
retraction `g ∘ ι = 1` through `Rʳ`: it is the rank of the reduction of the idempotent
`ι ∘ g` modulo the prime. -/
theorem rankAtStalk_range_eq_rank (hp : p * p = p) [Module.Finite R ↥p.range] {r : ℕ}
    (g : (Fin r → R) →ₗ[R] ↥p.range) (ι : ↥p.range →ₗ[R] (Fin r → R))
    (hgι : g ∘ₗ ι = LinearMap.id) (𝔭 : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ↥p.range 𝔭 =
      ((LinearMap.toMatrix' (ι ∘ₗ g)).map (algebraMap R 𝔭.asIdeal.ResidueField)).rank := by
  haveI : Module.Projective R ↥p.range := projective_range_of_finite hp
  haveI : Module.Flat R ↥p.range := Module.Flat.of_projective
  rw [Module.rankAtStalk_eq]
  show Module.finrank 𝔭.asIdeal.ResidueField (TensorProduct R 𝔭.asIdeal.ResidueField ↥p.range) = _
  set G : (Fin r → 𝔭.asIdeal.ResidueField) →ₗ[𝔭.asIdeal.ResidueField]
      TensorProduct R 𝔭.asIdeal.ResidueField ↥p.range :=
    g.baseChange 𝔭.asIdeal.ResidueField ∘ₗ
      (TensorProduct.piScalarRight R 𝔭.asIdeal.ResidueField 𝔭.asIdeal.ResidueField
        (Fin r)).symm.toLinearMap with hG
  set J : TensorProduct R 𝔭.asIdeal.ResidueField ↥p.range →ₗ[𝔭.asIdeal.ResidueField]
      (Fin r → 𝔭.asIdeal.ResidueField) :=
    (TensorProduct.piScalarRight R 𝔭.asIdeal.ResidueField 𝔭.asIdeal.ResidueField
      (Fin r)).toLinearMap ∘ₗ ι.baseChange 𝔭.asIdeal.ResidueField with hJ
  have hGJ : ∀ x, G (J x) = x := fun x ↦ by
    simp only [hG, hJ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hgι, LinearMap.baseChange_id,
      LinearMap.id_apply]
  have hJinj : Function.Injective J := fun x y hxy ↦ by rw [← hGJ x, hxy, hGJ]
  have hGsurj : LinearMap.range G = ⊤ := LinearMap.range_eq_top.2 fun x ↦ ⟨J x, hGJ x⟩
  have h1 : Module.finrank 𝔭.asIdeal.ResidueField
      (TensorProduct R 𝔭.asIdeal.ResidueField ↥p.range) =
      Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.range (J ∘ₗ G)) := by
    rw [LinearMap.range_comp_of_range_eq_top J hGsurj]
    exact (LinearEquiv.ofInjective J hJinj).finrank_eq
  have h2 : J ∘ₗ G = Matrix.toLin'
      ((LinearMap.toMatrix' (ι ∘ₗ g)).map (algebraMap R 𝔭.asIdeal.ResidueField)) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [hJ, hG, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have := piScalarRight_baseChange (S := 𝔭.asIdeal.ResidueField) (ι ∘ₗ g)
      ((TensorProduct.piScalarRight R 𝔭.asIdeal.ResidueField 𝔭.asIdeal.ResidueField
        (Fin r)).symm x)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at this
    rw [this, LinearEquiv.apply_symm_apply]
  rw [h1, h2, Matrix.rank, Matrix.toLin'_apply']

end MatrixRealisation

section Refinements

variable {u p w : c(I, R) →L[R] c(I, R)} {Q : R[X]} {S : PowerSeries R} {v : Rˣ}

/-- The standing hypotheses of the refinement section: `p, w` are as produced by
`exists_rieszColemanProjection` for the factorisation `det(1 − Tu) = QS`. -/
structure IsRieszColemanProjection (u p w : c(I, R) →L[R] c(I, R)) (Q : R[X])
    (S : PowerSeries R) (v : Rˣ) : Prop where
  compactoid : IsCompactoid u
  coeff_zero : Q.coeff 0 = 1
  leadingCoeff : (v : R) = Q.leadingCoeff
  entire : PowerSeries.IsEntire S
  coeff_zero_S : PowerSeries.coeff 0 S = 1
  eq : charPowerSeries u = (Q : PowerSeries R) * S
  coprime : PowerSeries.IsEntireCoprime (Q : PowerSeries R) S
  idem : p * p = p
  comm : u * p = p * u
  comm_w : u * w = w * u
  comm_pw : p * w = w * p
  nil : (Polynomial.aeval u Q.reverse) ^ Q.natDegree * (1 - p) = 0
  inv : Polynomial.aeval u Q.reverse * w = p

omit [IsTate R] [DecidableEq I] in
/-- `1 − p` is an idempotent when `p` is. -/
theorem one_sub_idem (hp : p * p = p) : (1 - p) * (1 - p) = 1 - p := by
  rw [mul_sub, mul_one, sub_mul, one_mul, hp, sub_self, sub_zero]

omit [IsTate R] [DecidableEq I] in
/-- A polynomial in `u p`, for an idempotent `p` commuting with `u`, is `P(u) p + P(0) (1 − p)`
(`(up)ᵏ = uᵏ p` for `k ≥ 1`). -/
theorem aeval_mul_idem (hp : p * p = p) (hc : u * p = p * u) (P : R[X]) :
    Polynomial.aeval (u * p) P = Polynomial.aeval u P * p + P.coeff 0 • (1 - p) := by
  refine Polynomial.induction_on' P (fun P Q hP hQ ↦ ?_) (fun n a ↦ ?_)
  · rw [map_add, map_add, Polynomial.coeff_add, add_smul, hP, hQ, add_mul]
    abel
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Polynomial.coeff_monomial]
    cases n with
    | zero =>
      rw [pow_zero, pow_zero, mul_one, if_pos rfl, Algebra.smul_def, mul_sub, mul_one]
      abel
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k), zero_smul, add_zero, (show Commute u p from hc).mul_pow,
        IsIdempotentElem.pow_succ_eq k hp, mul_assoc]

omit [IsTate R] [DecidableEq I] in
-- Block inverse: on `range p ⊕ range (1 − p)`, `A ⊕ c` is invertible with inverse `w ⊕ c⁻¹`.
private theorem isUnit_mul_add_smul_one_sub {A : c(I, R) →L[R] c(I, R)} (hp : p * p = p)
    (hAp : A * p = p * A) (hwp : p * w = w * p) (hAw : A * w = p) (hwA : w * A = p) (c : Rˣ) :
    IsUnit (A * p + (c : R) • (1 - p)) := by
  have hp1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h1p : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have h1w : (1 - p) * w = w * (1 - p) := by rw [sub_mul, one_mul, mul_sub, mul_one, hwp]
  have h1A : (1 - p) * A = A * (1 - p) := by rw [sub_mul, one_mul, mul_sub, mul_one, hAp]
  refine isUnit_iff_exists.mpr ⟨w * p + ((c⁻¹ : Rˣ) : R) • (1 - p), ?_, ?_⟩
  · rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      smul_smul, Units.mul_inv, one_smul, one_sub_idem hp,
      show A * p * (w * p) = p by
        rw [mul_assoc, ← mul_assoc p, hwp, mul_assoc w, hp, ← mul_assoc, hAw, hp],
      show A * p * (1 - p) = 0 by rw [mul_assoc, hp1, mul_zero],
      show (1 - p) * (w * p) = 0 by rw [← mul_assoc, h1w, mul_assoc, h1p, mul_zero],
      smul_zero, smul_zero, add_zero, zero_add, add_sub_cancel]
  · rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      smul_smul, Units.inv_mul, one_smul, one_sub_idem hp,
      show w * p * (A * p) = p by
        rw [mul_assoc, ← mul_assoc p, ← hAp, mul_assoc A, hp, ← mul_assoc, hwA, hp],
      show w * p * (1 - p) = 0 by rw [mul_assoc, hp1, mul_zero],
      show (1 - p) * (A * p) = 0 by rw [← mul_assoc, h1A, mul_assoc, h1p, mul_zero],
      smul_zero, smul_zero, add_zero, zero_add, add_sub_cancel]

omit [IsTate R] [DecidableEq I] in
-- `(1 − p)(u(1 − p) + p)ᵏ = uᵏ(1 − p)` for `p` idempotent commuting with `u`.
private theorem one_sub_mul_pow_eq (hp : p * p = p) (hc : u * p = p * u) (k : ℕ) :
    (1 - p) * (u * (1 - p) + p) ^ k = u ^ k * (1 - p) := by
  have h1p : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hu1 : u * (1 - p) = (1 - p) * u := by rw [mul_sub, mul_one, sub_mul, one_mul, hc]
  have hstep : (1 - p) * (u * (1 - p) + p) = u * (1 - p) := by
    rw [mul_add, h1p, add_zero, ← mul_assoc, ← hu1, mul_assoc, one_sub_idem hp]
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
  | succ k ih =>
    rw [pow_succ (u * (1 - p) + p) k, ← mul_assoc, ih, mul_assoc, hstep, ← mul_assoc,
      ← pow_succ u k]

/-- `N = range (1 − p)` is finitely generated (from `finite_range_of_one_sub_nilpotent` for
`φ' = aeval u (bQ Q v)`). -/
theorem IsRieszColemanProjection.finite (h : IsRieszColemanProjection u p w Q S v) :
    Module.Finite R ↥(1 - p).range := by
  have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero h.leadingCoeff
  refine finite_range_of_one_sub_nilpotent (φ := Polynomial.aeval u (bQ Q v))
    (h.compactoid.aeval _ hB0).isCompletelyContinuous (one_sub_idem h.idem)
    ((Commute.one_right _).sub_right ((IsOpLimitAeval.aeval u _).commute h.comm)).eq
    (n := Q.natDegree) ?_
  rw [one_sub_aeval_bQ, smul_pow, smul_mul_assoc, h.nil, smul_zero]

/-- `N = range (1 − p)` is projective. -/
theorem IsRieszColemanProjection.projective (h : IsRieszColemanProjection u p w Q S v) :
    Module.Projective R ↥(1 - p).range :=
  haveI := h.finite
  projective_range_of_finite (one_sub_idem h.idem)

/-- `det(1 − Tu | N)` — the characteristic power series of `u` on `N = range (1 − p)`,
extended by zero — is a polynomial (`exists_polynomial_charPowerSeries_of_range_le`). -/
theorem IsRieszColemanProjection.exists_polynomial (h : IsRieszColemanProjection u p w Q S v) :
    ∃ G : R[X], charPowerSeries (u * (1 - p)) = (G : PowerSeries R) := by
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 h.finite
  have hcomm : u * (1 - p) = (1 - p) * u := by rw [mul_sub, mul_one, sub_mul, one_mul, h.comm]
  have hle : LinearMap.range ((u * (1 - p) : c(I, R) →L[R] c(I, R)) : c(I, R) →ₗ[R] c(I, R)) ≤
      Submodule.span R (s : Set c(I, R)) := by
    rw [hs]
    rintro _ ⟨x, rfl⟩
    exact ⟨u x, (DFunLike.congr_fun hcomm x).symm⟩
  obtain ⟨G, -, hG⟩ := exists_polynomial_charPowerSeries_of_range_le hle
  exact ⟨G, hG⟩

/-- `det(1 − Tu) = det(1 − Tu | N) · det(1 − Tu | F)` (`charPowerSeries_add_of_mul_eq_zero`). -/
theorem IsRieszColemanProjection.charPowerSeries_eq_mul
    (h : IsRieszColemanProjection u p w Q S v) :
    charPowerSeries u = charPowerSeries (u * (1 - p)) * charPowerSeries (u * p) :=
  charPowerSeries_eq_mul_of_comm h.compactoid h.idem h.comm

/-- `det(1 − Tu | F)` is relatively prime to `Q` ([Buz07] proof of Thm 3.3: "the
characteristic power series of `φ` on `F` is coprime to `Q`, by Lemma 3.1"): `Q*(up) =
Q*(u) p + v (1 − p)` is invertible, with inverse `w p + v⁻¹ (1 − p)`. -/
theorem IsRieszColemanProjection.isEntireCoprime_range
    (h : IsRieszColemanProjection u p w Q S v) :
    PowerSeries.IsEntireCoprime (Q : PowerSeries R) (charPowerSeries (u * p)) := by
  rw [isEntireCoprime_iff_isUnit_aeval_reverse (u := u * p) (h.compactoid.comp_right p)
    h.coeff_zero h.leadingCoeff, aeval_mul_idem h.idem h.comm, Polynomial.coeff_zero_reverse,
    ← h.leadingCoeff]
  exact isUnit_mul_add_smul_one_sub h.idem ((IsOpLimitAeval.aeval u _).commute h.comm) h.comm_pw
    h.inv (((IsOpLimitAeval.aeval u _).commute h.comm_w).symm.trans h.inv) v

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem natTrailingDegree_eq_of_coeff {S : Type*} [Semiring S] {P : Polynomial S} {n : ℕ}
    (hn : P.coeff n ≠ 0) (h : ∀ i < n, P.coeff i = 0) : P.natTrailingDegree = n :=
  le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hn)
    (Polynomial.le_natTrailingDegree (fun h0 ↦ hn (by rw [h0, Polynomial.coeff_zero])) h)

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem natTrailingDegree_taylor_one_sub_pow {S : Type*} [CommRing S] [Nontrivial S]
    (d : ℕ) : (Polynomial.taylor (1 : S) ((1 - Polynomial.X) ^ d)).natTrailingDegree = d := by
  have hX : (1 - Polynomial.X : Polynomial S).comp (Polynomial.X + Polynomial.C 1) =
      Polynomial.C (-1) * Polynomial.X := by
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp, Polynomial.C_neg,
      Polynomial.C_1]
    ring
  rw [Polynomial.taylor_apply, Polynomial.pow_comp, hX, mul_pow, ← Polynomial.C_pow,
    Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.natTrailingDegree_monomial (isUnit_one.neg.pow d).ne_zero]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
private theorem taylor_one_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (P : Polynomial S) :
    Polynomial.taylor (1 : T) (P.map f) = (Polynomial.taylor (1 : S) P).map f := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, f.map_one]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
-- A good zero of order `n` at `1` of a polynomial, read on its Taylor expansion at `1`.
private theorem taylor_coeff_of_isGoodZero {P : R[X]} {n : ℕ}
    (h : PowerSeries.IsGoodZero (P : PowerSeries R) 1 n) :
    (∀ i < n, (Polynomial.taylor 1 P).coeff i = 0) ∧ IsUnit ((Polynomial.taylor 1 P).coeff n) := by
  have key : ∀ i, (Polynomial.taylor 1 P).coeff i =
      PowerSeries.evalT 1 (PowerSeries.hasseDeriv i (P : PowerSeries R)) := fun i ↦ by
    rw [Polynomial.taylor_coeff, PowerSeries.hasseDeriv_coe, PowerSeries.evalT_coe]
  exact ⟨fun i hi ↦ (key i).trans (h.1 i hi), (key n).symm ▸ h.2⟩

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
-- A polynomial with a good zero of order `n` at `1` whose image is `(1 − X) ^ m` has `m = n`.
private theorem eq_of_isGoodZero_of_map_eq {L : Type*} [CommRing L] [Nontrivial L] (f : R →+* L)
    {P : R[X]} {n m : ℕ} (h : PowerSeries.IsGoodZero (P : PowerSeries R) 1 n)
    (hP : P.map f = (1 - Polynomial.X) ^ m) : m = n := by
  obtain ⟨hlow, hn⟩ := taylor_coeff_of_isGoodZero h
  have h1 : (Polynomial.taylor 1 (P.map f)).natTrailingDegree = n := by
    rw [taylor_one_map]
    refine natTrailingDegree_eq_of_coeff ?_ fun i hi ↦ ?_
    · rw [Polynomial.coeff_map]
      exact (hn.map f).ne_zero
    · rw [Polynomial.coeff_map, hlow i hi, map_zero]
  rw [← h1, hP, natTrailingDegree_taylor_one_sub_pow]

/-- `1 − φ' p = v⁻¹ Q*(u) p + (1 − p)` is invertible (inverse `v w p + (1 − p)`), so
`det(1 − T φ' p)(1)` is a unit (Serre's Proposition 11). -/
theorem IsRieszColemanProjection.isUnit_evalT_one_aeval_bQ_mul
    (h : IsRieszColemanProjection u p w Q S v) :
    IsUnit (PowerSeries.evalT 1 (charPowerSeries (Polynomial.aeval u (bQ Q v) * p))) := by
  have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero h.leadingCoeff
  have hA₀p : Polynomial.aeval u Q.reverse * p = p * Polynomial.aeval u Q.reverse :=
    (IsOpLimitAeval.aeval u _).commute h.comm
  rw [← isUnit_one_sub_smul_iff_isUnit_evalT (u := Polynomial.aeval u (bQ Q v) * p)
    ((h.compactoid.aeval _ hB0).comp_right p) 1, one_smul]
  have hrew : (1 : c(I, R) →L[R] c(I, R)) - Polynomial.aeval u (bQ Q v) * p =
      ((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse * p + ((1 : Rˣ) : R) • (1 - p) := by
    rw [Units.val_one, one_smul, ← one_sub_aeval_bQ, sub_mul, one_mul]
    abel
  have hAp : ((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse * p =
      p * (((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse) := by
    rw [smul_mul_assoc, mul_smul_comm, hA₀p]
  have hwp : p * ((v : R) • w) = ((v : R) • w) * p := by
    rw [mul_smul_comm, smul_mul_assoc, h.comm_pw]
  have hAw : ((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse * ((v : R) • w) = p := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Units.inv_mul, one_smul, h.inv]
  have hwA : ((v : R) • w) * (((v⁻¹ : Rˣ) : R) • Polynomial.aeval u Q.reverse) = p := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul,
      ((IsOpLimitAeval.aeval u _).commute h.comm_w).symm, h.inv]
  have hA := isUnit_mul_add_smul_one_sub (w := (v : R) • w) h.idem hAp hwp hAw hwA 1
  rw [hrew]
  exact hA

/-- `det(1 − T φ'(1 − p))` has a good zero of order `deg Q` at `1`: `det(1 − T φ')` has one
([Bel] II.2.15) and splits as `det(1 − T φ'(1 − p)) · det(1 − T φ' p)` with the second factor
a unit at `1`. -/
theorem IsRieszColemanProjection.isGoodZero_aeval_bQ_mul_one_sub
    (h : IsRieszColemanProjection u p w Q S v) :
    PowerSeries.IsGoodZero (charPowerSeries (Polynomial.aeval u (bQ Q v) * (1 - p))) 1
      Q.natDegree := by
  have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero h.leadingCoeff
  have hφ'c : IsCompactoid (Polynomial.aeval u (bQ Q v)) := h.compactoid.aeval _ hB0
  have hc1 : IsCompactoid (Polynomial.aeval u (bQ Q v) * (1 - p)) := hφ'c.comp_right (1 - p)
  have hc2 : IsCompactoid (Polynomial.aeval u (bQ Q v) * p) := hφ'c.comp_right p
  have hφ'p : Polynomial.aeval u (bQ Q v) * p = p * Polynomial.aeval u (bQ Q v) :=
    (IsOpLimitAeval.aeval u _).commute h.comm
  have hgood0 : PowerSeries.IsGoodZero (charPowerSeries (Polynomial.aeval u (bQ Q v))) 1
      Q.natDegree := by
    rw [charPowerSeries_aeval h.compactoid _ hB0, h.eq]
    exact isGoodZero_dSeries_bQ Q v h.coeff_zero h.leadingCoeff h.entire h.coeff_zero_S h.coprime
  rw [charPowerSeries_eq_mul_of_comm hφ'c h.idem hφ'p] at hgood0
  have hF : PowerSeries.IsEntire (charPowerSeries (Polynomial.aeval u (bQ Q v) * (1 - p))) :=
    fun c hc ↦ charPowerSeries_isEntire _ hc1 c hc
  have hG : PowerSeries.IsEntire (charPowerSeries (Polynomial.aeval u (bQ Q v) * p)) :=
    fun c hc ↦ charPowerSeries_isEntire _ hc2 c hc
  have hunit := h.isUnit_evalT_one_aeval_bQ_mul
  exact PowerSeries.IsGoodZero.of_mul hF hG hgood0 hunit

/-- **Rank** ([JN] 2.2.2 "The rank of `Ker Q*(u)` is `deg Q`"; [Buz07] Prop. 3.2 "`N` is
projective of rank `h`"): at every prime, `N = range (1 − p)` has rank `deg Q`.  Reduction
modulo a maximal ideal: on `N ⊗ k(𝔪)` the operator `φ'` is unipotent, so
`det(1 − Tφ' | N ⊗ k(𝔪)) = (1 − T)^{rank}`, while `det(1 − Tφ' | N) = (1 − T)^{deg Q}·G'`
with `G'(1)` a unit. -/
theorem IsRieszColemanProjection.rankAtStalk (h : IsRieszColemanProjection u p w Q S v)
    (𝔭 : PrimeSpectrum R) : Module.rankAtStalk (R := R) ↥(1 - p).range 𝔭 = Q.natDegree := by
  have hB0 : (bQ Q v).coeff 0 = 0 := bQ_coeff_zero h.leadingCoeff
  have hp' := one_sub_idem h.idem
  have hcomm' : Polynomial.aeval u (bQ Q v) * (1 - p) = (1 - p) * Polynomial.aeval u (bQ Q v) :=
    ((Commute.one_right _).sub_right ((IsOpLimitAeval.aeval u _).commute h.comm)).eq
  haveI := h.finite
  obtain ⟨r, E, g, ι, hgι, hE, hEE, hΨ⟩ := exists_matrix_realisation hp'
  obtain ⟨Ψ, -, hΨE, hEΨ, hnilp, hchar⟩ := hΨ _ hcomm'
  have hgood := h.isGoodZero_aeval_bQ_mul_one_sub
  rw [hchar] at hgood
  have hnil : IsNilpotent (E - Ψ) := hnilp ⟨Q.natDegree, by
    rw [one_sub_aeval_bQ, smul_pow, smul_mul_assoc, h.nil, smul_zero]⟩
  have hbar : Ψ.charpolyRev.map (algebraMap R 𝔭.asIdeal.ResidueField) =
      (1 - Polynomial.X) ^ (E.map (algebraMap R 𝔭.asIdeal.ResidueField)).rank := by
    rw [← Matrix.charpolyRev_map]
    refine Matrix.charpolyRev_eq_one_sub_pow_rank ?_ ?_ ?_ ?_
    · rw [← Matrix.map_mul, hEE]
    · rw [← Matrix.map_mul, hΨE]
    · rw [← Matrix.map_mul, hEΨ]
    · rw [← Matrix.map_sub (algebraMap R 𝔭.asIdeal.ResidueField) (map_sub _)]
      exact hnil.map (algebraMap R 𝔭.asIdeal.ResidueField).mapMatrix
  rw [rankAtStalk_range_eq_rank hp' g ι hgι 𝔭, ← hE]
  exact eq_of_isGoodZero_of_map_eq _ hgood hbar

omit [IsTate R] in
-- From `Q*(u)ⁿ (1 − p) = 0`, `u` has an inverse on `N`: `u · D(u) (1 − p) = vⁿ (1 − p)` for
-- `D = −T`, where `Q.reverse ^ n = X·T + C vⁿ`.
private theorem IsRieszColemanProjection.exists_mul_aeval_mul_one_sub_eq
    (h : IsRieszColemanProjection u p w Q S v) :
    ∃ D : R[X], u * (Polynomial.aeval u D * (1 - p)) = ((v : R) ^ Q.natDegree) • (1 - p) := by
  have h0 : (Q.reverse ^ Q.natDegree).coeff 0 = (v : R) ^ Q.natDegree := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse, ← h.leadingCoeff]
  have hT : Q.reverse ^ Q.natDegree =
      Polynomial.X * (Q.reverse ^ Q.natDegree).divX + Polynomial.C ((v : R) ^ Q.natDegree) := by
    rw [← h0]
    exact (Polynomial.X_mul_divX_add _).symm
  refine ⟨-(Q.reverse ^ Q.natDegree).divX, ?_⟩
  have hnil := h.nil
  rw [← map_pow, hT, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, add_mul, smul_mul_assoc, one_mul] at hnil
  rw [map_neg, neg_mul, mul_neg, ← mul_assoc]
  exact neg_eq_of_add_eq_zero_right hnil

/-- **`u` is invertible on `Ker Q*(u)`** ([JN] proof of 2.2.2: "`det(u | Ker Q*(u)) = Q*(0) ∈
R^×`"): `u (1 − p) + p` is a unit.  From `Q*(u)ⁿ (1 − p) = 0` and `Q*(u) = u·T(u) + vⁿ`,
`u` has the inverse `v⁻ⁿ T(u)` on `N`. -/
theorem IsRieszColemanProjection.isUnit_mul_one_sub_add
    (h : IsRieszColemanProjection u p w Q S v) : IsUnit (u * (1 - p) + p) := by
  obtain ⟨D, hD⟩ := h.exists_mul_aeval_mul_one_sub_eq
  set c : Rˣ := v ^ Q.natDegree with hc
  have hcv : (c : R) = (v : R) ^ Q.natDegree := Units.val_pow_eq_pow_val v Q.natDegree
  have hp' := one_sub_idem h.idem
  have hu1 : Commute u (1 - p) := (Commute.one_right u).sub_right h.comm
  have hD1 : Commute (Polynomial.aeval u D) (1 - p) :=
    (Commute.one_right _).sub_right ((IsOpLimitAeval.aeval u D).commute h.comm)
  have hDu : Commute (Polynomial.aeval u D) u := (IsOpLimitAeval.aeval u D).commute rfl
  set w' : c(I, R) →L[R] c(I, R) := ((c⁻¹ : Rˣ) : R) • (Polynomial.aeval u D * (1 - p)) with hw'
  have h1w : (1 - p) * w' = w' * (1 - p) :=
    ((hD1.symm.mul_right (Commute.refl (1 - p))).smul_right ((c⁻¹ : Rˣ) : R)).eq
  have huw : u * w' = 1 - p := by
    rw [hw', mul_smul_comm, hD, smul_smul, ← hcv, Units.inv_mul, one_smul]
  have hwu : w' * u = 1 - p := by
    rw [hw', smul_mul_assoc, mul_assoc, ← hu1.eq, ← mul_assoc, hDu.eq, mul_assoc, hD, smul_smul,
      ← hcv, Units.inv_mul, one_smul]
  have := isUnit_mul_add_smul_one_sub (p := 1 - p) hp' hu1.eq h1w huw hwu 1
  rwa [Units.val_one, one_smul, sub_sub_cancel] at this

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsTate R] [DecidableEq I] in
-- Over a local ring `L`, a factorisation `E_L = AB`, `BA = 1_m` of the idempotent has
-- `card m = n` when `charpolyRev Ψ` has a good zero of order `n` at `1` and `E − Ψ` is
-- nilpotent: in the residue field, `charpolyRev Ψ = (1 − X) ^ card m`.
private theorem card_eq_of_isGoodZero {L : Type*} [CommRing L] [IsLocalRing L] (f : R →+* L)
    {r : ℕ} {E Ψ : Matrix (Fin r) (Fin r) R} (hEE : E * E = E) (hΨE : Ψ * E = Ψ)
    (hEΨ : E * Ψ = Ψ) (hnil : IsNilpotent (E - Ψ)) {n : ℕ}
    (hgood : PowerSeries.IsGoodZero (Ψ.charpolyRev : PowerSeries R) 1 n) {m : Type*} [Fintype m]
    [DecidableEq m] {A : Matrix (Fin r) m L} {B : Matrix m (Fin r) L} (hAB : A * B = E.map f)
    (hBA : B * A = 1) : Fintype.card m = n := by
  set g' := IsLocalRing.residue L with hg'
  have h1 : (E.map f).map g' * (E.map f).map g' = (E.map f).map g' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hEE]
  have h2 : (Ψ.map f).map g' * (E.map f).map g' = (Ψ.map f).map g' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hΨE]
  have h3 : (E.map f).map g' * (Ψ.map f).map g' = (Ψ.map f).map g' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hEΨ]
  have h4 : IsNilpotent ((E.map f).map g' - (Ψ.map f).map g') := by
    rw [← Matrix.map_sub g' (map_sub g'), ← Matrix.map_sub f (map_sub f)]
    exact (hnil.map f.mapMatrix).map g'.mapMatrix
  have h5 : A.map g' * B.map g' = (E.map f).map g' := by rw [← Matrix.map_mul, hAB]
  have h6 : B.map g' * A.map g' = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one g' (map_zero g') (map_one g')]
  have hbar := Matrix.charpolyRev_eq_one_sub_pow_of_mul_eq h1 h2 h3 h4 h5 h6
  rw [Matrix.charpolyRev_map, Matrix.charpolyRev_map, Polynomial.map_map] at hbar
  exact eq_of_isGoodZero_of_map_eq (g'.comp f) hgood hbar

/-- **Degree bound** ([Buz07] Thm 3.3: "`G` and `Q` have degree `n`"): `det(1 − Tu | N)` has
degree at most `deg Q`.  At a maximal ideal `𝔪`, the range of the idempotent `E` of the matrix
realisation localises to a free `R_𝔪`-module, of rank `deg Q` by the good-zero count of
`det(1 − Tφ' | N)` in the residue field; along the resulting rank factorisation, Sylvester's
identity bounds the degree of `det(1 − Tu | N) ⊗ R_𝔪` by `deg Q`, at every `𝔪`. -/
theorem IsRieszColemanProjection.natDegree_le_of_charPowerSeries_eq
    (h : IsRieszColemanProjection u p w Q S v) {G : R[X]}
    (hG : charPowerSeries (u * (1 - p)) = (G : PowerSeries R)) : G.natDegree ≤ Q.natDegree := by
  have hp' := one_sub_idem h.idem
  have hcomm' : Polynomial.aeval u (bQ Q v) * (1 - p) = (1 - p) * Polynomial.aeval u (bQ Q v) :=
    ((Commute.one_right _).sub_right ((IsOpLimitAeval.aeval u _).commute h.comm)).eq
  have hcommu : u * (1 - p) = (1 - p) * u := ((Commute.one_right u).sub_right h.comm).eq
  haveI := h.finite
  obtain ⟨r, E, g, ι, hgι, hE, hEE, hΨ⟩ := exists_matrix_realisation hp'
  obtain ⟨Ψu, -, hΨuE, hEΨu, -, hcharu⟩ := hΨ u hcommu
  obtain ⟨Ψ', -, hΨ'E, hEΨ', hnilp, hchar'⟩ := hΨ _ hcomm'
  have hGΨ : G = Ψu.charpolyRev := Polynomial.coe_inj.1 (hG.symm.trans hcharu)
  have hgood := h.isGoodZero_aeval_bQ_mul_one_sub
  rw [hchar'] at hgood
  have hnil : IsNilpotent (E - Ψ') := hnilp ⟨Q.natDegree, by
    rw [one_sub_aeval_bQ, smul_pow, smul_mul_assoc, h.nil, smul_zero]⟩
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  refine eq_zero_of_localization _ fun J hJ ↦ ?_
  set f := algebraMap R (Localization.AtPrime J) with hf
  have hEE' : E.map f * E.map f = E.map f := by rw [← Matrix.map_mul, hEE]
  haveI := Matrix.projective_range_mulVecLin_of_idempotent hEE'
  haveI : Module.Free (Localization.AtPrime J) (LinearMap.range (E.map f).mulVecLin) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨A, B, hAB, hBA⟩ := Matrix.exists_mul_eq_of_idempotent hEE'
  have hmn := card_eq_of_isGoodZero f hEE hΨ'E hEΨ' hnil hgood hAB hBA
  rw [Fintype.card_fin] at hmn
  have hdeg : (Ψu.map f).charpolyRev.natDegree ≤ Q.natDegree := by
    have h1 : Ψu.map f * E.map f = Ψu.map f := by rw [← Matrix.map_mul, hΨuE]
    have h2 : E.map f * Ψu.map f = Ψu.map f := by rw [← Matrix.map_mul, hEΨu]
    rw [Matrix.charpolyRev_eq_of_mul_eq h1 h2 hAB hBA, ← hmn]
    exact (Matrix.natDegree_charpolyRev_le _).trans (Fintype.card_fin _).le
  have hcoeff : (G.map f).coeff j = 0 := by
    rw [hGΨ, ← Matrix.charpolyRev_map]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hj)
  rwa [Polynomial.coeff_map] at hcoeff

omit [CompleteSpace R] [IsTate R] [DecidableEq I] in
-- A polynomial divisible by `Q` in the entire series is divisible by `Q` as a polynomial
-- (uniqueness of Euclidean division, `PowerSeries.eq_mul_add_r_unique`).
private theorem exists_eq_mul_of_eq_mul_isEntire [Nontrivial R] {Q G : R[X]}
    (hv : IsUnit Q.leadingCoeff) {K' : PowerSeries R} (hK' : PowerSeries.IsEntire K')
    (hG : (G : PowerSeries R) = Q * K') : ∃ K : R[X], G = Q * K := by
  obtain ⟨v, hv'⟩ := id hv
  have hQ₁m : (Polynomial.C ((v⁻¹ : Rˣ) : R) * Q).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hv', Units.inv_mul])
  obtain ⟨K, hK⟩ : ∃ K : R[X],
      K = Polynomial.C ((v⁻¹ : Rˣ) : R) * (G /ₘ (Polynomial.C ((v⁻¹ : Rˣ) : R) * Q)) := ⟨_, rfl⟩
  have hGKr : (G : PowerSeries R) = (Q : PowerSeries R) * (K : PowerSeries R) +
      ((G %ₘ (Polynomial.C ((v⁻¹ : Rˣ) : R) * Q) : R[X]) : PowerSeries R) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div G (Polynomial.C ((v⁻¹ : Rˣ) : R) * Q)]
    rw [hK]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
    ring
  have hQne : Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.1 hv.ne_zero
  have hr0 : (0 : R[X]) = G %ₘ (Polynomial.C ((v⁻¹ : Rˣ) : R) * Q) := by
    refine PowerSeries.eq_mul_add_r_unique hv hK' (Polynomial.isEntire_coe K) ?_ ?_ ?_
    · rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.2 (Polynomial.degree_eq_bot.not.2 hQne)
    · rw [← Polynomial.degree_C_mul_of_isUnit (v⁻¹).isUnit Q]
      exact Polynomial.degree_modByMonic_lt G hQ₁m
    · rw [Polynomial.coe_zero, add_zero, ← hG]
      exact hGKr
  refine ⟨K, Polynomial.coe_inj.1 ?_⟩
  rw [Polynomial.coe_mul, hGKr, ← hr0, Polynomial.coe_zero, add_zero]

/-- **`det(1 − Tu | Ker Q*(u)) = Q`** ([Buz07] Thm 3.3: "`Q` divides `G`. But `G` and `Q` have
degree `n` and the same constant term, and furthermore the leading coefficient of `Q` is a
unit. This is enough to prove that `G = Q`"): `Q` divides `G = det(1 − Tu | N)` in the entire
series (`(Q, det(1 − Tu | F)) = 1` and `QS = G·det(1 − Tu | F)`), hence as polynomials by the
uniqueness of Euclidean division; the degree bound `natDegree_le_of_charPowerSeries_eq`
forces the cofactor to be the constant `1`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub
    (h : IsRieszColemanProjection u p w Q S v) :
    charPowerSeries (u * (1 - p)) = (Q : PowerSeries R) := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨G, hG⟩ := h.exists_polynomial
  have hdeg := h.natDegree_le_of_charPowerSeries_eq hG
  have hv : IsUnit Q.leadingCoeff := by
    rw [← h.leadingCoeff]
    exact v.isUnit
  have hG0 : G.coeff 0 = 1 := by
    have := congrArg (PowerSeries.coeff 0) hG
    rwa [charPowerSeries_coeff, charCoeff_zero, Polynomial.coeff_coe, eq_comm] at this
  obtain ⟨a, b, ha, hb, hab⟩ := h.isEntireCoprime_range
  have hGH : (Q : PowerSeries R) * S = (G : PowerSeries R) * charPowerSeries (u * p) := by
    rw [← h.eq, h.charPowerSeries_eq_mul, hG]
  have hdiv : (G : PowerSeries R) = (Q : PowerSeries R) * (a * G + b * S) := by
    calc (G : PowerSeries R) = G * (a * Q + b * charPowerSeries (u * p)) := by rw [hab, mul_one]
      _ = Q * (a * G) + b * (G * charPowerSeries (u * p)) := by ring
      _ = Q * (a * G) + b * (Q * S) := by rw [← hGH]
      _ = Q * (a * G + b * S) := by ring
  obtain ⟨K, hGK⟩ := exists_eq_mul_of_eq_mul_isEntire hv
    ((ha.mul (Polynomial.isEntire_coe G)).add (hb.mul h.entire)) hdiv
  have hK0 : K ≠ 0 := fun hK0 ↦ by
    rw [hK0, mul_zero] at hGK
    exact one_ne_zero (by rw [← hG0, hGK, Polynomial.coeff_zero])
  have hdegK : K.natDegree = 0 := by
    have := Polynomial.natDegree_mul' (p := Q) (q := K)
      (hv.mul_right_eq_zero.not.2 (Polynomial.leadingCoeff_ne_zero.2 hK0))
    rw [← hGK] at this
    omega
  have hK1 : K = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegK]
    have := hG0
    rw [hGK, Polynomial.mul_coeff_zero, h.coeff_zero, one_mul] at this
    rw [this, Polynomial.C_1]
  rw [hG, hGK, hK1, mul_one]

/-- **`det(1 − Tu | N) = S`** ([JN] proof of 2.2.2: "`F = det(1−Tu|Ker Q*(u)) det(1−Tu|N) = QS'`.
Hence `Q(S − S') = 0`, and `Q` is not a zero divisor since `Q(0) = 1`, so `S = S'`"). -/
theorem IsRieszColemanProjection.charPowerSeries_mul (h : IsRieszColemanProjection u p w Q S v) :
    charPowerSeries (u * p) = S := by
  have hQ : IsUnit (Q : PowerSeries R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, h.coeff_zero]
    exact isUnit_one
  have := h.charPowerSeries_eq_mul
  rw [h.charPowerSeries_mul_one_sub, h.eq] at this
  exact (hQ.mul_right_inj.1 this).symm

/-- **`Q*(u)` vanishes on `N`** ([JN] "`Ker Q*(u) ⊆ M`"; [Buz07] Thm 3.3 "`Q*(φ)` is zero on
`N`"): Cayley–Hamilton for the matrix realisation `Ψ` of `u` on `N`, whose characteristic
polynomial is `Q*·X^(r − deg Q)` once `det(1 − Tu | N) = Q`, gives `Q*(u) u^(r − deg Q) = 0`
on `N`, and `u` is invertible there. -/
theorem IsRieszColemanProjection.aeval_reverse_mul_one_sub
    (h : IsRieszColemanProjection u p w Q S v) :
    Polynomial.aeval u Q.reverse * (1 - p) = 0 := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hp' := one_sub_idem h.idem
  have hcommu : u * (1 - p) = (1 - p) * u := ((Commute.one_right u).sub_right h.comm).eq
  haveI := h.finite
  obtain ⟨r, E, g, ι, hgι, -, -, hΨ⟩ := exists_matrix_realisation hp'
  obtain ⟨Ψ, rfl, -, -, -, hchar⟩ := hΨ u hcommu
  set ψ := (restrictRange u (1 - p) hcommu).toLinearMap with hψ
  set Ψl : Module.End R (Fin r → R) := ι ∘ₗ ψ ∘ₗ g with hΨl
  have hGQ : (LinearMap.toMatrix' Ψl).charpolyRev = Q :=
    Polynomial.coe_inj.1 (hchar.symm.trans h.charPowerSeries_mul_one_sub)
  have hCH := Matrix.aeval_self_charpoly (LinearMap.toMatrix' Ψl)
  rw [charpoly_eq_of_charpolyRev_eq hGQ, map_mul, map_pow, Polynomial.aeval_X] at hCH
  have hint : Ψl ∘ₗ ι = ι ∘ₗ ψ := by
    rw [hΨl, LinearMap.comp_assoc, LinearMap.comp_assoc, hgι, LinearMap.comp_id]
  have hCHl : Polynomial.aeval Ψl Q.reverse * Ψl ^ (r - Q.natDegree) = 0 := by
    apply LinearMap.toMatrixAlgEquiv'.injective
    rw [map_mul, map_pow, ← Polynomial.aeval_algHom_apply, map_zero]
    exact hCH
  have hN : ι ∘ₗ (Polynomial.aeval ψ Q.reverse * ψ ^ (r - Q.natDegree)) = 0 := by
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ← aeval_comp_of_comp_eq hint,
      LinearMap.comp_assoc, ← Module.End.commute_pow_left_of_commute hint, ← LinearMap.comp_assoc,
      ← Module.End.mul_eq_comp, hCHl, LinearMap.zero_comp]
  have hN' : Polynomial.aeval ψ (Q.reverse * Polynomial.X ^ (r - Q.natDegree)) = 0 := by
    rw [map_mul, map_pow, Polynomial.aeval_X]
    have := congrArg (fun F : ↥(1 - p).range →ₗ[R] (Fin r → R) ↦ g ∘ₗ F) hN
    simpa only [← LinearMap.comp_assoc, hgι, LinearMap.id_comp, LinearMap.comp_zero] using this
  have hop : Polynomial.aeval u Q.reverse * u ^ (r - Q.natDegree) * (1 - p) = 0 := by
    refine ContinuousLinearMap.ext fun y ↦ ?_
    have hy : (1 - p) y ∈ (1 - p).range := LinearMap.mem_range_self _ y
    have := coe_aeval_restrictRange_apply hcommu (Q.reverse * Polynomial.X ^ (r - Q.natDegree))
      ⟨(1 - p) y, hy⟩
    rw [hN', LinearMap.zero_apply, Submodule.coe_zero, map_mul, map_pow, Polynomial.aeval_X]
      at this
    exact this.symm
  rw [mul_assoc, ← one_sub_mul_pow_eq h.idem h.comm, ← mul_assoc] at hop
  exact ((h.isUnit_mul_one_sub_add.pow _).mul_left_eq_zero).1 hop

/-- `Ker Q*(u) = N = range (1 − p)`: `⊇` is `aeval_reverse_mul_one_sub`; conversely
`Q*(u) x = 0` gives `p x = w Q*(u) x = 0`, so `x = (1 − p) x`. -/
theorem IsRieszColemanProjection.ker_aeval_reverse (h : IsRieszColemanProjection u p w Q S v) :
    (Polynomial.aeval u Q.reverse).ker = (1 - p).range := by
  have h5 := h.aeval_reverse_mul_one_sub
  have hAw : Polynomial.aeval u Q.reverse * w = w * Polynomial.aeval u Q.reverse :=
    (IsOpLimitAeval.aeval u _).commute h.comm_w
  refine Submodule.ext fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · have hx' : Polynomial.aeval u Q.reverse x = 0 := hx
    have hpx : p x = 0 := by
      have := DFunLike.congr_fun h.inv x
      rw [hAw] at this
      rw [← this]
      show w (Polynomial.aeval u Q.reverse x) = 0
      rw [hx', map_zero]
    refine ⟨x, ?_⟩
    show x - p x = x
    rw [hpx, sub_zero]
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun h5 y

/-- **Uniqueness of the complement** ([JN] "a unique `u`-stable closed complement `N` such
that `Q*(u)` is invertible on `N`"; [Bel] II.2.17 uniqueness: "`N'' = p(N + N')` … nilpotent
and invertible, thus `N'' = 0`"): a topological complement `F'` of `Ker Q*(u)` with
`F' ⊆ Q*(u)(F')` is `range p`.  Indeed `F' ⊆ range p` since `(1 − p) Q*(u) = 0`, and a
complement of `range (1 − p)` inside `range p` is all of `range p`.  (`u`-stability and the
injectivity of `Q*(u)` on `F'` in the sources are not needed.) -/
theorem IsRieszColemanProjection.eq_range_of_isTopCompl
    (h : IsRieszColemanProjection u p w Q S v) {F' : Submodule R c(I, R)}
    (hF' : Submodule.IsTopCompl (1 - p).range F')
    (hsurj : ∀ y ∈ F', ∃ x ∈ F', Polynomial.aeval u Q.reverse x = y) : F' = p.range := by
  have h5 := h.aeval_reverse_mul_one_sub
  have hA1 : Polynomial.aeval u Q.reverse * (1 - p) = (1 - p) * Polynomial.aeval u Q.reverse :=
    ((Commute.one_right _).sub_right ((IsOpLimitAeval.aeval u _).commute h.comm)).eq
  have hp1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, h.idem, sub_self]
  have hle : F' ≤ p.range := fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := hsurj x hx
    have h0 : Polynomial.aeval u Q.reverse y - p (Polynomial.aeval u Q.reverse y) = 0 := by
      show ((1 - p) * Polynomial.aeval u Q.reverse) y = 0
      rw [← hA1, h5, zero_apply]
    exact ⟨_, (sub_eq_zero.1 h0).symm⟩
  refine le_antisymm hle ?_
  rintro _ ⟨z, rfl⟩
  have hmem : p z ∈ (1 - p).range ⊔ F' := by
    rw [hF'.isCompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨_, ⟨n', rfl⟩, f, hf, hnf⟩ := Submodule.mem_sup.1 hmem
  have e1 : p ((1 - p) n') = 0 := DFunLike.congr_fun hp1 n'
  have e2 : p (p z) = p z := DFunLike.congr_fun h.idem z
  have e := congrArg p hnf
  rw [map_add, ContinuousLinearMap.coe_coe, e1, (mem_range_iff_of_idempotent h.idem).1 (hle hf),
    e2, zero_add] at e
  exact e ▸ hf

omit [IsTate R] [DecidableEq I] in
-- `A p + c (1 − p)` invertible for a unit `c` gives `A p + (1 − p)` invertible.
private theorem isUnit_mul_add_one_sub_of_isUnit {A : c(I, R) →L[R] c(I, R)} (hp : p * p = p)
    (c : Rˣ) (hA : IsUnit (A * p + (c : R) • (1 - p))) : IsUnit (A * p + (1 - p)) := by
  have hp1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h1p : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hu : IsUnit ((1 : c(I, R) →L[R] c(I, R)) * p + ((c⁻¹ : Rˣ) : R) • (1 - p)) :=
    isUnit_mul_add_smul_one_sub hp (by rw [one_mul, mul_one]) rfl (one_mul p) (mul_one p) c⁻¹
  have key : (A * p + (c : R) • (1 - p)) * (1 * p + ((c⁻¹ : Rˣ) : R) • (1 - p)) =
      A * p + (1 - p) := by
    rw [one_mul, add_mul, mul_add, mul_add, mul_assoc A p p, hp,
      mul_smul_comm ((c⁻¹ : Rˣ) : R) (A * p) (1 - p), mul_assoc A p (1 - p), hp1, mul_zero,
      smul_zero, add_zero, smul_mul_assoc (c : R) (1 - p) p, h1p, smul_zero, zero_add,
      smul_mul_assoc (c : R) (1 - p) (((c⁻¹ : Rˣ) : R) • (1 - p)),
      mul_smul_comm ((c⁻¹ : Rˣ) : R) (1 - p) (1 - p), smul_smul, one_sub_idem hp, Units.mul_inv,
      one_smul]
  rw [← key]
  exact hA.mul hu

/-- **Slope-decomposition core of [JN] Theorem 2.2.13 (⇐)** ("It remains to show that for
every multiplicative polynomial `P` of slope `≤ h`, `P*(u)` is invertible on `N`. By Lemma
2.2.7 `P` and `S` are relatively prime. Since `S = det(1 − Tu | N)`, it follows from [Buz07,
Lemma 3.1] that `P*` is invertible on `N`"): for every multiplicative `P` relatively prime to
`S`, `P*(u)` is invertible on `range p`.  From `isEntireCoprime_iff_isUnit_aeval_reverse` for
`u p`, whose characteristic series is `S` (`charPowerSeries_mul`), and
`P*(up) = P*(u) p + lc(P) (1 − p)`. -/
theorem IsRieszColemanProjection.isUnit_aeval_reverse_of_isEntireCoprime
    (h : IsRieszColemanProjection u p w Q S v) {P : R[X]} (hP0 : P.coeff 0 = 1)
    (hPu : IsUnit P.leadingCoeff) (hcop : PowerSeries.IsEntireCoprime (P : PowerSeries R) S) :
    IsUnit (Polynomial.aeval u P.reverse * p + (1 - p)) := by
  obtain ⟨v', hv'⟩ := hPu
  rw [← h.charPowerSeries_mul,
    isEntireCoprime_iff_isUnit_aeval_reverse (u := u * p) (h.compactoid.comp_right p) hP0 hv',
    aeval_mul_idem h.idem h.comm, Polynomial.coeff_zero_reverse, ← hv'] at hcop
  exact isUnit_mul_add_one_sub_of_isUnit h.idem v' hcop

end Refinements

end TateFredholm

end
