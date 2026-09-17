import Mathlib

/-!
# Compact operators and Fredholm determinants: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures that
can already be stated against the pinned Mathlib API. It is not an exhaustive list of the results in
any layer, and where the roadmap and this file disagree the roadmap wins.

The point of the file is to pin the design decisions that are easy to get wrong and expensive to
undo: the three notions of compactness and the fact that the determinant theory runs on
`IsCompactoid` (README convention 1); that Mathlib's `IsCompactOperator` appears only in the bridge
theorem of §0.5 (convention 2); that row decay is read on the matrix with rows as coordinates
(convention 3); that the Fredholm determinant is defined by principal minors and named
`charPowerSeries` (convention 4); that entire series are a predicate on `PowerSeries` evaluated by
summation, with Hasse derivatives (convention 6); that Riesz theory produces projectors in the
closure of `R[u]` at the ring level, and that the field statements assume no discreteness
(convention 7); and that the slope-`≤ h` factorisation over a ring is stated through a dominant
index at a radius (convention 8).

The first section restates, with the same names, the few signatures of the
`p`-adic-functional-analysis roadmap's `Suggested.lean` that everything below is built on; the
development imports that roadmap's versions instead of redefining them.
-/

namespace TauCetiRoadmap.CompactOperators

open Filter Topology
open scoped ZeroAtInfty Classical Polynomial

noncomputable section

/-! ## Prerequisites restated from the `p`-adic-functional-analysis roadmap -/

section Prerequisites

/-- A *multiplicative* element (that roadmap's §0.2.4). -/
def IsMultiplicative {R : Type*} [Norm R] [Mul R] (a : R) : Prop := ∀ x, ‖a * x‖ = ‖a‖ * ‖x‖

/-- A multiplicative pseudo-uniformiser (that roadmap's §0.4.1). -/
structure PseudoUniformizer (R : Type*) [NormedRing R] where
  /-- The unit. -/
  unit : Rˣ
  /-- It is multiplicative. -/
  isMultiplicative : IsMultiplicative (unit : R)
  /-- Its norm is less than `1`. -/
  norm_lt_one : ‖(unit : R)‖ < 1

/-- Banach–Tate rings, a Prop class (that roadmap's convention 2). -/
class IsTate (R : Type*) [NormedRing R] : Prop where
  /-- Some multiplicative pseudo-uniformiser exists. -/
  exists_pseudoUniformizer : Nonempty (PseudoUniformizer R)

/-- Every nontrivially normed field is Banach–Tate (that roadmap's §0.4.4, the bridge lemma);
recorded as an instance here so that the field statements below need no extra hypothesis. -/
instance isTate_of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  sorry

/-- The operator norm by Mathlib's formula, for a semiring of scalars (that roadmap's §1.1.1). -/
def opNorm {R M N : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module R N] (u : M →L[R] N) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}

variable {R : Type*} [NormedRing R]
variable {I J : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J]

/-- The coordinate vector `single j r` of the model space `C₀(J, R)` (that roadmap's §2.1.2). -/
def single [DecidableEq J] (j : J) (r : R) : C₀(J, R) :=
  ⟨⟨Pi.single j r, continuous_of_discreteTopology⟩, sorry⟩

/-- The matrix of an operator between model spaces, rows as coordinates and columns as images
(that roadmap's convention 7). -/
def matrixCoeff [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) : R :=
  u (single j 1) i

/-- The coordinate truncation `π_S` (that roadmap's §2.6.3). -/
def truncation [DecidableEq I] (S : Finset I) : C₀(I, R) →L[R] C₀(I, R) :=
  sorry

/-- The scalar action of a normed ring on its model space is continuous (that roadmap's §2.1.1;
Mathlib has the instance for normed fields only). With the next instance it makes the
endomorphisms of `C₀(I, R)` an `R`-algebra, so that `a • u` and `Polynomial.aeval u` make sense. -/
instance instContinuousConstSMul : ContinuousConstSMul R C₀(I, R) :=
  sorry

/-- Scalars commute with scalars on the model space (that roadmap's §2.1.1). -/
instance instSMulCommClass : SMulCommClass R R C₀(I, R) :=
  sorry

end Prerequisites

/-! ## Layer 0: compact operators -/

section CompletelyContinuous

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {M N : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **Finite rank** (§0.1.1): the range lies in a finitely generated submodule. -/
def IsFiniteRank (u : M →L[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ LinearMap.range (u : M →ₗ[R] N) ≤ Q

/-- **Completely continuous** (§0.1.2; Serre's definition): an operator-norm limit of finite-rank
operators. Intrinsic on any Banach module; not the organising notion of the determinant theory. -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[R] N, IsFiniteRank v ∧ opNorm (u - v) < ε

/-- **The identity criterion** (§0.1.3): the identity is completely continuous iff the module is
finitely generated — the ring-level form of `isCompactOperator_id_iff_finiteDimensional`. -/
theorem isCompletelyContinuous_id_iff [IsTate R] [IsUltrametricDist M] [CompleteSpace M] :
    IsCompletelyContinuous (ContinuousLinearMap.id R M) ↔ Module.Finite R M :=
  sorry

end CompletelyContinuous

section Compactoid

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {I J L : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J] [TopologicalSpace L] [DiscreteTopology L]

/-- The row supremum `rowNorm u i = sup_j ‖matrixCoeff u i j‖` (§0.2.1). ⚠ A real supremum: the
Banach–Tate hypothesis is what keeps every row bounded (README convention 3). -/
def rowNorm [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) : ℝ :=
  ⨆ j, ‖matrixCoeff u i j‖

/-- **Compactoid** (§0.2.1): the rows of the matrix tend to `0` cofinitely. The organising notion
of the whole determinant theory (README convention 1). -/
def IsCompactoid [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) : Prop :=
  Tendsto (rowNorm u) cofinite (𝓝 0)

/-- Compactoid implies completely continuous, unconditionally (§0.2.3). -/
theorem IsCompactoid.isCompletelyContinuous [IsTate R] [DecidableEq J]
    {u : C₀(J, R) →L[R] C₀(I, R)} (hu : IsCompactoid u) : IsCompletelyContinuous u :=
  sorry

/-- **The truncation criterion** (§0.2.2): an operator is compactoid iff its truncations converge
to it in operator norm — the statement the `p`-adic-functional-analysis roadmap's §2.6.3 defers. -/
theorem isCompactoid_iff_tendsto_truncation [IsTate R] [DecidableEq I]
    (u : C₀(I, R) →L[R] C₀(I, R)) :
    IsCompactoid u ↔
      Tendsto (fun S : Finset I ↦ opNorm ((truncation S).comp u - u)) atTop (𝓝 0) :=
  sorry

/-- The two-sided ideal property, post-composition (§0.2.4). -/
theorem IsCompactoid.comp_left [IsTate R] [DecidableEq J] {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : IsCompactoid u) (f : C₀(I, R) →L[R] C₀(L, R)) : IsCompactoid (f.comp u) :=
  sorry

/-- The two-sided ideal property, pre-composition (§0.2.4). -/
theorem IsCompactoid.comp_right [IsTate R] [DecidableEq J] [DecidableEq L]
    {u : C₀(J, R) →L[R] C₀(I, R)} (hu : IsCompactoid u) (f : C₀(L, R) →L[R] C₀(J, R)) :
    IsCompactoid (u.comp f) :=
  sorry

/-- **The converse under Noetherianity** (§0.2.9): over a Noetherian Banach–Tate ring, and over
every field, completely continuous is compactoid. ⚠ False without the closedness of finitely
generated submodules, which is why nothing in Layers 1–4 depends on it. -/
theorem isCompletelyContinuous_iff_isCompactoid [IsTate R] [IsNoetherianRing R] [DecidableEq J]
    (u : C₀(J, R) →L[R] C₀(I, R)) : IsCompletelyContinuous u ↔ IsCompactoid u :=
  sorry

/-- Row decay makes an operator compactoid (§0.2.8; Jacobs, Corollary 1.10). -/
theorem isCompactoid_of_row_decay [IsTate R] [DecidableEq J] {u : C₀(J, R) →L[R] C₀(I, R)}
    {σ C : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (w : I → ℕ) (hw : Tendsto w cofinite atTop)
    (h : ∀ i j, ‖matrixCoeff u i j‖ ≤ C * σ ^ w i) : IsCompactoid u :=
  sorry

end Compactoid

section MathlibBridge

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]
  [CompleteSpace F]

/-- **The bridge to Mathlib** (§0.5.4): over a locally compact nonarchimedean field, completely
continuous is Mathlib's `IsCompactOperator`. ⚠ The only place `IsCompactOperator` appears (README
convention 2): over `ℂ_p` the identity of a line is finite-rank and not `IsCompactOperator`. -/
theorem isCompletelyContinuous_iff_isCompactOperator [LocallyCompactSpace K] (u : E →L[K] F) :
    IsCompletelyContinuous u ↔ IsCompactOperator (u : E → F) :=
  sorry

end MathlibBridge

/-! ## Layer 1: the Fredholm determinant -/

section Fredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- The principal minor of the matrix of `u` on a finite set of indices (§1.2.1). Norm-free. -/
def minor (u : C₀(I, R) →L[R] C₀(I, R)) (S : Finset I) : R :=
  Matrix.det (Matrix.of fun i j : S ↦ matrixCoeff u i j)

/-- The coefficients of the Fredholm determinant, by Serre's formula (README convention 4): the
`n`-th coefficient is `(−1)ⁿ` times the sum of all `n × n` principal minors. A formal sum; the
theorems assume `IsCompactoid`, which makes it converge. -/
def charCoeff (u : C₀(I, R) →L[R] C₀(I, R)) (n : ℕ) : R :=
  (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)

/-- **The Fredholm determinant** `det(1 − Tu)`, Buzzard's characteristic power series (§1.2.2). -/
def charPowerSeries (u : C₀(I, R) →L[R] C₀(I, R)) : PowerSeries R :=
  PowerSeries.mk (charCoeff u)

/-- **Entirety** (§1.3.1; Serre, §5; Bellaïche, Lemma II.1.14): the determinant of a compactoid
operator is restricted at every radius. -/
theorem charPowerSeries_isEntire [IsTate R] {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    (c : ℝ) (hc : 0 < c) : PowerSeries.IsRestricted c (charPowerSeries u) :=
  sorry

/-- **The Lipschitz bound** (§1.3.2; Bellaïche, Lemma II.1.15), the quantitative continuity that
every limit argument runs on. -/
theorem norm_charCoeff_sub_le [IsTate R] {u v : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    (hv : IsCompactoid v) {n : ℕ} (hn : 1 ≤ n) :
    ‖charCoeff u n - charCoeff v n‖ ≤ max (opNorm u) (opNorm v) ^ (n - 1) * opNorm (u - v) :=
  sorry

/-- **Agreement with the finite case** (§1.2.3): for a row-supported operator the determinant is
Mathlib's `charpolyRev` of the finite matrix, by the principal-minors expansion of §1.1.1. -/
theorem charPowerSeries_eq_charpolyRev (u : C₀(I, R) →L[R] C₀(I, R)) (S : Finset I)
    (hS : ∀ i ∉ S, ∀ j, matrixCoeff u i j = 0) :
    charPowerSeries u = ((Matrix.of fun i j : S ↦ matrixCoeff u i j).charpolyRev : PowerSeries R) :=
  sorry

/-- **The trace property** (§1.4.1; Bellaïche, Proposition II.1.17), the primitive invariance
(README convention 5): one factor compactoid, the other merely bounded. -/
theorem charPowerSeries_comm [IsTate R] {J : Type*} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(I, R) →L[R] C₀(J, R))
    (hu : IsCompactoid u) : charPowerSeries (u.comp v) = charPowerSeries (v.comp u) :=
  sorry

/-- **Conjugation invariance** (§1.4.2), a formal corollary of the trace property; it is what
makes the determinant well defined on potentially orthonormalisable modules (§1.5.1). -/
theorem charPowerSeries_conj [IsTate R] {J : Type*} [TopologicalSpace J] [DiscreteTopology J]
    [DecidableEq J] (e : C₀(I, R) ≃L[R] C₀(J, R)) (u : C₀(I, R) →L[R] C₀(I, R))
    (hu : IsCompactoid u) :
    charPowerSeries ((e : C₀(I, R) →L[R] C₀(J, R)).comp
        (u.comp (e.symm : C₀(J, R) →L[R] C₀(I, R)))) = charPowerSeries u :=
  sorry

/-- **Diagonal intertwining** (§1.4.3): `D · M_v = M_u · D` with unit diagonal entries gives equal
minors, with no compactness hypothesis and no inverse of `D`. -/
theorem charPowerSeries_eq_of_diag_intertwine {u v : C₀(I, R) →L[R] C₀(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i)) (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) :
    charPowerSeries v = charPowerSeries u :=
  sorry

/-- **Commuting idempotents** (§1.6.4): the determinant splits along a `u`-stable decomposition. -/
theorem charPowerSeries_eq_mul_of_comm [IsTate R] {u p : C₀(I, R) →L[R] C₀(I, R)}
    (hu : IsCompactoid u) (hp : p * p = p) (hup : u * p = p * u) :
    charPowerSeries u = charPowerSeries (u * (1 - p)) * charPowerSeries (u * p) :=
  sorry

/-- **Bounded base change** (§1.7.1), matrix-wise: the determinant of the operator with matrix
`ψ (a_{ij})` is the image of the determinant. No completed tensor product is used. -/
theorem charPowerSeries_map [IsTate R] {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [NormOneClass S] [CompleteSpace S] [IsTate S] (ψ : R →+* S) (C : ℝ)
    (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖) (u : C₀(I, R) →L[R] C₀(I, R)) (hu : IsCompactoid u)
    (v : C₀(I, S) →L[S] C₀(I, S)) (hv : ∀ i j, matrixCoeff v i j = ψ (matrixCoeff u i j)) :
    charPowerSeries v = PowerSeries.map ψ (charPowerSeries u) :=
  sorry

end Fredholm

/-! ## Layer 2: entire series, the resolvent, and the invertibility criterion -/

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]

/-- **Entire** (§2.1.1; README convention 6): restricted at every radius. A predicate on Mathlib's
`PowerSeries`; the subring `R{{T}}` is `entireSubring`. -/
def IsEntire (f : PowerSeries R) : Prop := ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f

/-- Evaluation of a series at a point by summation (§2.1.2), convergent for entire series at
every point. ⚠ Not Mathlib's `PowerSeries.eval₂`, which needs a linear topology. -/
def evalAt (a : R) (f : PowerSeries R) : R := ∑' n, PowerSeries.coeff n f * a ^ n

/-- The `k`-th **Hasse derivative** `Δᵏ f = ∑ₙ (n+k choose k) a_{n+k} Tⁿ` (§2.1.3; Serre's `Δᵏ`,
Buzzard's `∆ᵏ`); Mathlib has `Polynomial.hasseDeriv` only. -/
def hasseDeriv (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ ((n + k).choose k : R) * PowerSeries.coeff (n + k) f

/-- **Euclidean division in `R{{T}}`** (§2.2.2; Bellaïche, Proposition II.2.8), obtained from
Weierstrass division at a radius where the polynomial is dominant. -/
theorem IsEntire.exists_eq_mul_add {F : PowerSeries R} (hF : IsEntire F) {B : R[X]}
    (hB : IsUnit B.leadingCoeff) (hmul : IsMultiplicative B.leadingCoeff) :
    ∃ (q : PowerSeries R) (r : R[X]),
      IsEntire q ∧ r.degree < B.degree ∧ F = (B : PowerSeries R) * q + r :=
  sorry

/-- **Relative primality in `R{{T}}`** (§2.2.3; Johansson–Newton, Definition 2.2.1). -/
def IsEntireCoprime (F G : PowerSeries R) : Prop :=
  ∃ a b : PowerSeries R, IsEntire a ∧ IsEntire b ∧ a * F + b * G = 1

/-- **A good zero of order `s`** (§2.3.1; Bellaïche, Definition II.2.11): the first `s` Hasse
derivatives vanish at `a` and the `s`-th is a unit. -/
def IsGoodZero (F : PowerSeries R) (a : R) (s : ℕ) : Prop :=
  (∀ i < s, evalAt a (hasseDeriv i F) = 0) ∧ IsUnit (evalAt a (hasseDeriv s F))

/-- **Factorisation at a good zero** (§2.3.2): `F = (1 − a⁻¹T)ˢ · G` with `G(a)` a unit. -/
theorem IsGoodZero.exists_factor {F : PowerSeries R} (hF : IsEntire F) (hF0 : PowerSeries.coeff 0 F = 1)
    {a : R} {s : ℕ} (hs : 1 ≤ s) (h : IsGoodZero F a s) (ha : IsUnit a) :
    ∃ G : PowerSeries R, IsEntire G ∧ PowerSeries.coeff 0 G = 1 ∧ IsUnit (evalAt a G) ∧
      F = (1 - PowerSeries.C ((ha.unit⁻¹ : Rˣ) : R) * PowerSeries.X) ^ s * G :=
  sorry

end PowerSeries

section Resolvent

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- Serre's `det(1 − u)`, the value of the Fredholm determinant at `T = 1` (§2.4.4). -/
def fredholmDet (u : C₀(I, R) →L[R] C₀(I, R)) : R :=
  PowerSeries.evalAt 1 (charPowerSeries u)

/-- **Multiplicativity of `det(1 − u)`** (§2.4.4; Serre, §5): `det((1−u)(1−v)) = det(1−u) det(1−v)`. -/
theorem fredholmDet_mul {u v : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    (hv : IsCompactoid v) : fredholmDet (u + v - u * v) = fredholmDet u * fredholmDet v :=
  sorry

/-- **Serre's Proposition 11** (§2.5.1): `1 − a·u` is invertible iff `det(1 − Tu)(a)` is a unit,
over any Banach–Tate ring. -/
theorem isUnit_one_sub_smul_iff_isUnit_evalAt {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    (a : R) : IsUnit (1 - a • u) ↔ IsUnit (PowerSeries.evalAt a (charPowerSeries u)) :=
  sorry

end Resolvent

section Spectrum

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- **The nonzero spectrum over a field** (§2.5.3): a nonzero `λ` is in Mathlib's `spectrum` iff
`λ⁻¹` is a zero of `det(1 − Tu)`. -/
theorem mem_spectrum_iff (u : C₀(I, K) →L[K] C₀(I, K)) (hu : IsCompactoid u) {μ : K}
    (hμ : μ ≠ 0) : μ ∈ spectrum K u ↔ PowerSeries.evalAt μ⁻¹ (charPowerSeries u) = 0 :=
  sorry

end Spectrum

/-! ## Layer 3: Riesz theory -/

section Riesz

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- **The Riesz projector at a good zero** (§3.1.1; Serre, §7; Johansson–Newton, Theorem 2.2.2):
an idempotent `p` and a witness `w`, both in the closure of `R[u]`, with `1 − a·u` nilpotent on
`range (1 − p)` and inverted by `w` on `range p`. -/
theorem exists_rieszProjection {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u) {a : R}
    {h : ℕ} (hh : 1 ≤ h) (ha : PowerSeries.IsGoodZero (charPowerSeries u) a h) :
    ∃ p w : C₀(I, R) →L[R] C₀(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      (1 - a • u) ^ h * (1 - p) = 0 ∧ (1 - a • u) * w = p :=
  sorry

/-- **Coleman's `D(B, P)`** for polynomials (§3.3.1), as Mathlib's resultant of the reciprocal
polynomial `P*` against `1 − T·B(X)`; equal to `∏ (1 − B(tᵢ) T)` over the reciprocal roots `tᵢ`
of `P`. -/
def colemanD (B P : R[X]) : R[X] :=
  Polynomial.resultant ((Polynomial.reflect P.natDegree P).map (Polynomial.C : R →+* R[X]))
    (1 - Polynomial.C (Polynomial.X : R[X]) * B.map (Polynomial.C : R →+* R[X]))

/-- Coleman's transform of an entire series (§3.3.2): the coefficientwise limit of the transforms
of the truncations. -/
def colemanDSeries (B : R[X]) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun j ↦ limUnder atTop fun N ↦ (colemanD B (PowerSeries.trunc (N + 1) F)).coeff j

/-- **The spectral mapping formula** (§3.3.4; Bellaïche, Proposition II.2.16; Coleman):
`det(1 − T·B(u)) = D(B, det(1 − Tu))` for `B(0) = 0`. -/
theorem charPowerSeries_aeval {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u) (B : R[X])
    (hB0 : B.coeff 0 = 0) :
    charPowerSeries (Polynomial.aeval u B) = colemanDSeries B (charPowerSeries u) :=
  sorry

/-- **The Riesz–Coleman decomposition** (§3.4.1–2; Coleman, Theorem A4.3; Buzzard, Theorem 3.3;
Bellaïche, Theorem II.2.18; Johansson–Newton, Theorem 2.2.2), over a Banach–Tate ring with no
Noetherian hypothesis: for a coprime factorisation `det(1 − Tu) = Q·S`, projectors in the closure
of `R[u]` cutting out `ker Q*(u)`, finitely generated projective, with the determinant identities. -/
theorem exists_rieszColemanProjection {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    {Q : R[X]} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) {S : PowerSeries R}
    (hS : PowerSeries.IsEntire S) (hS0 : PowerSeries.coeff 0 S = 1)
    (hF : charPowerSeries u = (Q : PowerSeries R) * S)
    (hcop : PowerSeries.IsEntireCoprime (Q : PowerSeries R) S) :
    ∃ p w : C₀(I, R) →L[R] C₀(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      Polynomial.aeval u Q.reverse * (1 - p) = 0 ∧ Polynomial.aeval u Q.reverse * w = p ∧
      Module.Finite R (LinearMap.range ((1 - p : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) ∧
      Module.Projective R (LinearMap.range ((1 - p : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) ∧
      charPowerSeries (u * (1 - p)) = (Q : PowerSeries R) ∧ charPowerSeries (u * p) = S :=
  sorry

end Riesz

section RieszField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- **The eigenvector theorem** (§3.2.1): the zeros of `det(1 − Tu)` are the reciprocals of the
nonzero eigenvalues, over every complete nonarchimedean field. -/
theorem evalAt_charPowerSeries_eq_zero_iff (u : C₀(I, K) →L[K] C₀(I, K)) (hu : IsCompactoid u)
    {a : K} (ha : a ≠ 0) :
    PowerSeries.evalAt a (charPowerSeries u) = 0 ↔ ∃ x : C₀(I, K), x ≠ 0 ∧ u x = a⁻¹ • x :=
  sorry

/-- **Serre's Proposition 12** (§3.2.2): at a zero `a` of order `h`, the topological splitting
`c₀(I, K) = ker (1 − a·u)ʰ ⊕ range (1 − a·u)ʰ` with the finite piece of dimension exactly `h`.
⚠ No discreteness of the valuation (README convention 7). -/
theorem exists_rieszDecomposition (u : C₀(I, K) →L[K] C₀(I, K)) (hu : IsCompactoid u) {a : K}
    (ha : PowerSeries.evalAt a (charPowerSeries u) = 0) :
    ∃ (h : ℕ) (N F : Submodule K C₀(I, K)), 1 ≤ h ∧ Submodule.IsTopCompl N F ∧
      (∀ x ∈ N, u x ∈ N) ∧ (∀ x ∈ F, u x ∈ F) ∧ (∀ x ∈ N, ((1 - a • u) ^ h) x = 0) ∧
      (∀ y ∈ F, ∃ x ∈ F, (1 - a • u) x = y) ∧ (∀ x ∈ F, (1 - a • u) x = 0 → x = 0) ∧
      Module.finrank K N = h :=
  sorry

/-- The finite piece of the Riesz–Coleman decomposition over a field has dimension `deg Q`
(§3.4.5). -/
theorem finrank_ker_aeval_reverse (u : C₀(I, K) →L[K] C₀(I, K)) (hu : IsCompactoid u)
    {Q : K[X]} (hQ0 : Q.coeff 0 = 1) {S : PowerSeries K} (hS : PowerSeries.IsEntire S)
    (hF : charPowerSeries u = (Q : PowerSeries K) * S)
    (hcop : PowerSeries.IsEntireCoprime (Q : PowerSeries K) S) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) :
      C₀(I, K) →ₗ[K] C₀(I, K))) = Q.natDegree :=
  sorry

end RieszField

/-! ## Layer 4: slopes -/

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]

/-- **A dominant index at radius `ρ`** (§4.3.3; Bellaïche, Definition II.2.3): `‖aₖ‖ρᵏ` is
maximised at `N`, strictly beyond `N`. Over a field, `N` is the right endpoint of the face of
slope `log_b ρ` of the Newton polygon (README convention 8). -/
def IsDominantIndex (ρ : ℝ) (F : PowerSeries R) (N : ℕ) : Prop :=
  (∀ k, ‖PowerSeries.coeff k F‖ * ρ ^ k ≤ ‖PowerSeries.coeff N F‖ * ρ ^ N) ∧
    ∀ k, N < k → ‖PowerSeries.coeff k F‖ * ρ ^ k < ‖PowerSeries.coeff N F‖ * ρ ^ N

/-- **The vertex factorisation over a ring** (§4.3.4; Bellaïche, Theorem II.3.6): at a dominant
index with multiplicative unit dominant coefficient, `F = P · G` with `P` of degree `N`, `G` of
dominant index `0`, and the factors coprime in `R{{T}}`. -/
theorem exists_dominantFactorization {ρ : ℝ} (hρ : 0 < ρ) {F : PowerSeries R}
    (hF : IsEntire F) (hF0 : PowerSeries.coeff 0 F = 1) {N : ℕ} (hN : IsDominantIndex ρ F N)
    (hunit : IsUnit (PowerSeries.coeff N F)) (hmul : IsMultiplicative (PowerSeries.coeff N F)) :
    ∃ (P : R[X]) (G : PowerSeries R), P.natDegree = N ∧ P.coeff 0 = 1 ∧
      IsUnit P.leadingCoeff ∧ IsEntire G ∧ PowerSeries.coeff 0 G = 1 ∧ IsDominantIndex ρ G 0 ∧
      F = (P : PowerSeries R) * G ∧ IsEntireCoprime (P : PowerSeries R) G :=
  sorry

end PowerSeries

section Bounds

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- **The row-weight bound** (§4.4.2): row decay `‖a_{ij}‖ ≤ σ ^ (w i)` bounds `‖cₙ‖` by
`σ ^ (f n)` for any lower bound `f n` on the weight sums over `n`-element index sets. -/
theorem norm_charCoeff_le_pow [IsTate R] {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u) (w : I → ℕ)
    (hdiv : ∀ i j, ‖matrixCoeff u i j‖ ≤ σ ^ w i) {f : ℕ → ℕ}
    (hf : ∀ S : Finset I, ∀ n : ℕ, S.card = n → f n ≤ ∑ i ∈ S, w i) (n : ℕ) :
    ‖charCoeff u n‖ ≤ σ ^ f n :=
  sorry

/-- **The two-sided bound** (§4.4.3), the engine of the halo estimate: no compactness and no Tate
hypothesis, the minors being summable from the cofinite growth of `w − w'`. -/
theorem norm_charCoeff_le_pow_two_sided {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : C₀(I, R) →L[R] C₀(I, R)} (w w' : I → ℕ)
    (hdiv : ∀ i j, ‖matrixCoeff u i j‖ ≤ σ ^ (w i - w' j))
    (hw : Tendsto (fun i ↦ w i - w' i) cofinite atTop) {f : ℕ → ℕ}
    (hf : ∀ S : Finset I, ∀ n : ℕ, S.card = n → f n ≤ (∑ i ∈ S, w i) - ∑ i ∈ S, w' i)
    (n : ℕ) : ‖charCoeff u n‖ ≤ σ ^ f n :=
  sorry

end Bounds

section ExactCase

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The exact case** (§4.4.4; Jacobs, Theorem 2.12, generalised): strictly decreasing
multiplicative row bounds and unit rescaled leading minors force `‖cₙ‖ = ∏_{i<n} ‖dᵢ‖`, so the
slopes are exactly `v d₀, v d₁, …`. -/
theorem norm_charCoeff_of_unit_minors (u : C₀(ℕ, K) →L[K] C₀(ℕ, K)) (d : ℕ → K)
    (hd0 : ∀ i, d i ≠ 0) (hanti : StrictAnti fun i ↦ ‖d i‖)
    (hdiv : ∀ i j, ‖matrixCoeff u i j‖ ≤ ‖d i‖)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun i j : Fin n ↦ (d i)⁻¹ * matrixCoeff u (i : ℕ) (j : ℕ)).det‖ = 1)
    (n : ℕ) : ‖charCoeff u n‖ = ∏ i ∈ Finset.range n, ‖d i‖ :=
  sorry

end ExactCase

end

end TauCetiRoadmap.CompactOperators
