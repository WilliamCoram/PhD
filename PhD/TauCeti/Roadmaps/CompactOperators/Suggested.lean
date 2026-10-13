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

/-! ## Targets requested by the Tau Ceti LocallyAnalyticDistributions and AdicSpacesPartIII roadmaps -/

namespace TauCetiRoadmap.CompactOperators

open Filter Topology
open scoped ZeroAtInfty Classical Polynomial

noncomputable section

/-! ### Layer 0 -/

section CompletelyContinuousTargets

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {M N : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **Finite rank against finitely generated range** (§0.1.1): over a Noetherian ring an operator
has finite rank iff its range is finitely generated, so both finite-rank conventions give the same
`IsCompletelyContinuous`. Without the Noetherian hypothesis only `←` holds. -/
theorem isFiniteRank_iff_range_fg [IsNoetherianRing R] (u : M →L[R] N) :
    IsFiniteRank u ↔ (LinearMap.range (u : M →ₗ[R] N)).FG :=
  sorry

/-- **Finite rank implies complete continuity** (§0.1.2): a finite-rank operator is its own
approximant. -/
theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u :=
  sorry

end CompletelyContinuousTargets

section CompletelyContinuousChecks

/- `IsBoundedSMul R C₀(ℕ, R)` is part of the `p`-adic-functional-analysis roadmap's §2.1.1; Mathlib
has no instance for a normed ring, so the checks carry it as a hypothesis. -/
variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R] [IsBoundedSMul R C₀(ℕ, R)]

/-- Check `identity_on_infinite_c0` (§0.1.2): the identity of `c₀(ℕ, R)` is not completely
continuous, by §0.1.3, since `c₀(ℕ, R)` maps onto every `Rⁿ`. No Noetherian hypothesis. -/
example : ¬ IsCompletelyContinuous (ContinuousLinearMap.id R C₀(ℕ, R)) :=
  sorry

/-- Check `decaying_diagonal` (§0.1.2): the operator with diagonal matrix `ϖⁱ` is completely
continuous and does not have finite rank. -/
example (ϖ : PseudoUniformizer R) (u : C₀(ℕ, R) →L[R] C₀(ℕ, R))
    (hu : ∀ i j, matrixCoeff u i j = if i = j then (ϖ.unit : R) ^ i else 0) :
    IsCompletelyContinuous u ∧ ¬ IsFiniteRank u :=
  sorry

end CompletelyContinuousChecks

/-! ### Layer 1 -/

section FredholmTargets

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- Check `nonzero_nilpotent` (§1.2.2): the nonzero nilpotent Jordan block on `c₀(Fin 2, R)` has
`charPowerSeries u = 1` although `u ≠ 0`. -/
example (u : C₀(Fin 2, R) →L[R] C₀(Fin 2, R))
    (hu : ∀ i j, matrixCoeff u i j = if i = 0 ∧ j = 1 then 1 else 0) :
    charPowerSeries u = 1 ∧ u ≠ 0 :=
  sorry

/-- **Uniform tail bound under a common row majorant** (§1.2.4, §1.3.3; Serre, Proposition 7(b)):
if the row norms of every member of a family are bounded by one null family `r`, the weighted
coefficients `‖cₙ‖ ρⁿ` of their determinants are at most `B ^ |T| · q ^ (n − |T|)`, uniformly in
the family, where `ρ · r i ≤ q < 1` off the finite set `T` and `ρ · r i ≤ B` everywhere. -/
theorem norm_charCoeff_mul_pow_le_of_rowNorm_le [IsTate R] {ι : Type*}
    (u : ι → C₀(I, R) →L[R] C₀(I, R)) {r : I → ℝ} (hr : Tendsto r cofinite (𝓝 0))
    (hur : ∀ α i, rowNorm (u α) i ≤ r i) {ρ q B : ℝ} (hρ : 0 < ρ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB : 1 ≤ B) (T : Finset I) (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) (α : ι)
    (n : ℕ) : ‖charCoeff (u α) n‖ * ρ ^ n ≤ B ^ T.card * q ^ (n - T.card) :=
  sorry

/- The sup norm on `K × K` is ultrametric; Mathlib has no instance for products, so the check
carries it as a hypothesis. -/
/-- Check `variable_rank_projective` (§1.5.2): over `K × K` with `e = (1, 0)`, the determinant of
the identity of the summand `e • (K × K)`, that of multiplication by `e` on `c₀(Fin 1, K × K)`,
is `1 − eT`, whose leading coefficient `−e` is not a unit. -/
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsUltrametricDist (K × K)] (u : C₀(Fin 1, K × K) →L[K × K] C₀(Fin 1, K × K))
    (hu : ∀ x, u x = ((1, 0) : K × K) • x) :
    charPowerSeries u = 1 - PowerSeries.C ((1, 0) : K × K) * PowerSeries.X ∧
      ¬ IsUnit (-((1, 0) : K × K)) :=
  sorry

end FredholmTargets

/-! ### Layer 2 -/

namespace PowerSeries

/-- **Hasse derivatives over any semiring** (§2.1.3; Buzzard, §3): the formula of `hasseDeriv`
over a semiring `B`, commutative or not, with the binomial coefficient acting as a natural-number
multiple. It applies to series with operator coefficients, such as the resolvent of §2.4.3. -/
def semiringHasseDeriv {B : Type*} [Semiring B] (k : ℕ) (f : PowerSeries B) : PowerSeries B :=
  PowerSeries.mk fun n ↦ (n + k).choose k • PowerSeries.coeff (n + k) f

section SemiringHasse

variable {B : Type*} [Semiring B]

/-- `Δ⁰ = id` over any semiring (§2.1.3). -/
theorem semiringHasseDeriv_zero (f : PowerSeries B) : semiringHasseDeriv 0 f = f :=
  sorry

/-- `Δᵏ` is additive over any semiring (§2.1.3). -/
theorem semiringHasseDeriv_add (k : ℕ) (f g : PowerSeries B) :
    semiringHasseDeriv k (f + g) = semiringHasseDeriv k f + semiringHasseDeriv k g :=
  sorry

/-- `Δᵏ` commutes with constants acting on the left, `B` being possibly noncommutative
(§2.1.3). -/
theorem semiringHasseDeriv_smul (k : ℕ) (b : B) (f : PowerSeries B) :
    semiringHasseDeriv k (b • f) = b • semiringHasseDeriv k f :=
  sorry

/-- Check `hasse_characteristic_two` (§2.1.3): over `ZMod 2`, `Δ²(T²) = 1`, while the second
derivative of `T²` vanishes. -/
example : semiringHasseDeriv 2 (PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) = 1 ∧
    PowerSeries.derivative (ZMod 2) (PowerSeries.derivative (ZMod 2) (PowerSeries.X ^ 2)) = 0 :=
  sorry

end SemiringHasse

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]

/-- Over a normed commutative ring the two Hasse derivatives agree (§2.1.3). -/
theorem hasseDeriv_eq_semiringHasseDeriv (k : ℕ) (f : PowerSeries R) :
    hasseDeriv k f = semiringHasseDeriv k f :=
  sorry

/-- **The explicit quotient by a monic polynomial** (§2.2.2; Coleman, Appendix A3): for `Q` monic of
degree `d` and `bₖ` the coefficients of the inverse of `Q.reverse`, the series whose `n`-th
coefficient is `∑ₖ coeff (n + d + k) F · bₖ`. -/
def divByMonic (Q : R[X]) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ ∑' k, PowerSeries.coeff (n + Q.natDegree + k) F *
    PowerSeries.coeff k (PowerSeries.invOfUnit (Q.reverse : PowerSeries R) 1)

/-- The explicit quotient of an entire series by a monic polynomial is entire (§2.2.2). -/
theorem IsEntire.isEntire_divByMonic {F : PowerSeries R} (hF : IsEntire F) {Q : R[X]}
    (hQ : Q.Monic) : IsEntire (divByMonic Q F) :=
  sorry

/-- **Euclidean division by a monic polynomial, explicitly** (§2.2.2): `F = Q · divByMonic Q F + r`
with `deg r < deg Q`, with no multiplicativity hypothesis on the leading coefficient. -/
theorem IsEntire.exists_eq_mul_divByMonic_add {F : PowerSeries R} (hF : IsEntire F) {Q : R[X]}
    (hQ : Q.Monic) :
    ∃ r : R[X], r.degree < Q.degree ∧ F = (Q : PowerSeries R) * divByMonic Q F + r :=
  sorry

/-- Check `monic_quotient_quadratic` (§2.2.2): for `Q = T² + aT + b`, the quotient of `T³` is
`T − a`. -/
example (a b : R) :
    divByMonic (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b)
      (PowerSeries.X ^ 3 : PowerSeries R) = PowerSeries.X - PowerSeries.C a :=
  sorry

/-- **Zeros and linear factors** (§2.2.2; Coleman, Appendix A3): an entire series vanishes at `a`
iff `T − a` divides it in `R{{T}}`. -/
theorem IsEntire.evalAt_eq_zero_iff {F : PowerSeries R} (hF : IsEntire F) (a : R) :
    evalAt a F = 0 ↔
      ∃ G : PowerSeries R, IsEntire G ∧ F = (PowerSeries.X - PowerSeries.C a) * G :=
  sorry

/-- **The resultant of a monic polynomial and an entire series** (§2.2.3–4; Coleman, Lemma A3.7):
the norm, in `R[T]/(Q)`, of the class of the remainder of `F` on division by `Q`. -/
def entireResultant (Q : R[X]) (F : PowerSeries R) : R :=
  Algebra.norm R (AdjoinRoot.mk Q
    (PowerSeries.trunc Q.natDegree (F - (Q : PowerSeries R) * divByMonic Q F)))

/-- The resultant depends only on `F` modulo `Q` (§2.2.3–4). -/
theorem entireResultant_eq_of_eq_mul_add {Q : R[X]} (hQ : Q.Monic) {F G S : PowerSeries R}
    (hG : IsEntire G) (hS : IsEntire S) (h : F = (Q : PowerSeries R) * S + G) :
    entireResultant Q F = entireResultant Q G :=
  sorry

/-- The resultant is multiplicative in the entire argument (§2.2.3–4). -/
theorem entireResultant_mul {Q : R[X]} (hQ : Q.Monic) {F G : PowerSeries R} (hF : IsEntire F)
    (hG : IsEntire G) : entireResultant Q (F * G) = entireResultant Q F * entireResultant Q G :=
  sorry

/-- Against a linear factor the resultant is evaluation, `Res(T − a, F) = F(a)` (§2.2.3–4). -/
theorem entireResultant_X_sub_C (a : R) {F : PowerSeries R} (hF : IsEntire F) :
    entireResultant (Polynomial.X - Polynomial.C a) F = evalAt a F :=
  sorry

/-- On polynomials the resultant is Mathlib's, with these degree bounds (§2.2.3–4). -/
theorem entireResultant_coe {Q : R[X]} (hQ : Q.Monic) (P : R[X]) :
    entireResultant Q (P : PowerSeries R) = Q.resultant P Q.natDegree P.natDegree :=
  sorry

/-- **The resultant Bézout identity** (§2.2.3–4): `Res(Q, F) = Q · G + H · F` with `G` entire and
`H` a polynomial of degree less than `deg Q`. -/
theorem entireResultant_bezout {Q : R[X]} (hQ : Q.Monic) {F : PowerSeries R} (hF : IsEntire F) :
    ∃ (G : PowerSeries R) (H : R[X]), IsEntire G ∧ H.degree < Q.degree ∧
      PowerSeries.C (entireResultant Q F) = (Q : PowerSeries R) * G + (H : PowerSeries R) * F :=
  sorry

/-- Check `constant_divisor` (§2.2.3–4): `Res(1, F) = 1`, including `F = 0`. -/
example (F : PowerSeries R) : entireResultant 1 F = 1 :=
  sorry

/-- Check `linear_evaluation` (§2.2.3–4): `Res(T − a, 1 − bT) = 1 − ba`. -/
example (a b : R) :
    entireResultant (Polynomial.X - Polynomial.C a) (1 - PowerSeries.C b * PowerSeries.X) =
      1 - b * a :=
  sorry

/-- Check `common_factor` (§2.2.3–4): `Res(Q, Q) = 0` for `Q` monic of positive degree. -/
example {Q : R[X]} (hQ : Q.Monic) (hd : 0 < Q.natDegree) :
    entireResultant Q (Q : PowerSeries R) = 0 :=
  sorry

/-- Check `resultant_zero_series` (§2.2.3–4): against the zero series the resultant is `0`, not a
unit, for `Q` of positive degree, and `1` for `Q = 1`. -/
example {Q : R[X]} (hQ : Q.Monic) (hd : 0 < Q.natDegree) :
    entireResultant Q 0 = 0 ∧ ¬ IsUnit (entireResultant Q 0) ∧
      entireResultant (1 : R[X]) 0 = 1 :=
  sorry

/-- Check `resultant_nilpotent_linear` (§2.2.3–4): `Res(T², a + bT) = a²`. -/
example (a b : R) :
    entireResultant (Polynomial.X ^ 2) (PowerSeries.C a + PowerSeries.C b * PowerSeries.X) =
      a ^ 2 :=
  sorry

/-- **Zeros of a normalised entire series are units** (§2.3.1; Buzzard, §3): if `F(0) = 1` and
`F(a) = 0`, then `a` is a unit with inverse `−∑ₙ coeff (n + 1) F · aⁿ`. -/
theorem IsEntire.isUnit_of_evalAt_eq_zero {F : PowerSeries R} (hF : IsEntire F)
    (hF0 : PowerSeries.coeff 0 F = 1) {a : R} (ha : evalAt a F = 0) :
    IsUnit a ∧ a * -(∑' n, PowerSeries.coeff (n + 1) F * a ^ n) = 1 :=
  sorry

/-- Check `root_nonunit_constant` (§2.3.1): `T` vanishes at the non-unit `0`, so `F(0) = 1` is
needed. -/
example : evalAt 0 (PowerSeries.X : PowerSeries R) = 0 ∧ ¬ IsUnit (0 : R) :=
  sorry

end PowerSeries

section ResolventChecks

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R]

/-- Check `resolvent_not_neumann` (§2.4.1): for the identity of `c₀(Fin 1, R)`, `H = 1 − T`, the
resolvent coefficients `vₘ = ∑_{k ≤ m} cₖ uᵐ⁻ᵏ` are `v₀ = 1` and `vₘ = 0` for `m ≥ 1`, so the
resolvent is `1`, while the Neumann coefficients `uᵐ` keep operator norm `1`. -/
example (u : C₀(Fin 1, R) →L[R] C₀(Fin 1, R)) (hu : u = 1) :
    ∑ k ∈ Finset.range 1, charCoeff u k • u ^ (0 - k) = 1 ∧
      (∀ m, 1 ≤ m → ∑ k ∈ Finset.range (m + 1), charCoeff u k • u ^ (m - k) = 0) ∧
      ¬ Tendsto (fun m ↦ opNorm (u ^ m)) atTop (𝓝 0) :=
  sorry

/-- Check `whole_series_product_nonexample` (§2.4.4): for the identity `u` of `c₀(Fin 1, R)`,
`det(1 − u)` is multiplicative along `u + u − u ∘ u = u` while `det(1 − Tu)` is not. -/
example (u : C₀(Fin 1, R) →L[R] C₀(Fin 1, R)) (hu : u = 1) :
    charPowerSeries (u + u - u * u) ≠ charPowerSeries u * charPowerSeries u ∧
      fredholmDet (u + u - u * u) = fredholmDet u * fredholmDet u :=
  sorry

end ResolventChecks

/-! ### Layer 3 -/

section RieszChecks

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R]

/-- Check `riesz_jordan_root` (§3.1.1): for `u = 1 + N` on `c₀(Fin 2, R)`, `a = 1` is a good zero
of order `2` with `c = 1`, and every projector of §3.1.1 there is `p = 0`, so `1 − p` is the
identity although `1 − u ≠ 0`. -/
example (u : C₀(Fin 2, R) →L[R] C₀(Fin 2, R))
    (hu : ∀ i j, matrixCoeff u i j = if i = j ∨ (i = 0 ∧ j = 1) then 1 else 0) :
    PowerSeries.IsGoodZero (charPowerSeries u) 1 2 ∧
      PowerSeries.evalAt 1 (PowerSeries.hasseDeriv 2 (charPowerSeries u)) = 1 ∧
      (∀ p w : C₀(Fin 2, R) →L[R] C₀(Fin 2, R), p * p = p → u * p = p * u → u * w = w * u →
        p * w = w * p → (1 - (1 : R) • u) ^ 2 * (1 - p) = 0 → (1 - (1 : R) • u) * w = p →
        p = 0) ∧
      1 - u ≠ 0 :=
  sorry

end RieszChecks

section ColemanBounded

variable {A : Type*} [CommRing A]

/-- **Coleman's transform at a prescribed rank** (§3.3.1; Coleman, Appendix A3): the resultant in
`X` of the rank-`n` reversal of `P` and of `1 − T·B(X)`, with the degree bounds `n` and `m`. -/
def colemanDBounded (n m : ℕ) (B P : A[X]) : A[X] :=
  Polynomial.resultant ((Polynomial.reflect n P).map (Polynomial.C : A →+* A[X]))
    (1 - Polynomial.C (Polynomial.X : A[X]) * B.map (Polynomial.C : A →+* A[X])) n m

/-- The transform does not depend on the bound `m ≥ deg B` (§3.3.1). -/
theorem colemanDBounded_of_natDegree_le {n m : ℕ} {B P : A[X]} (hP0 : P.coeff 0 = 1)
    (hPn : P.natDegree ≤ n) (hBm : B.natDegree ≤ m) :
    colemanDBounded n m B P = colemanDBounded n B.natDegree B P :=
  sorry

/-- **Padding** (§3.3.1): raising the rank by one multiplies the transform by `1 − B(0) T`, the
factor of the added eigenvalue `0`. -/
theorem colemanDBounded_succ {n m : ℕ} {B P : A[X]} (hP0 : P.coeff 0 = 1)
    (hPn : P.natDegree ≤ n) (hBm : B.natDegree ≤ m) :
    colemanDBounded (n + 1) m B P =
      colemanDBounded n m B P * (1 - Polynomial.C (B.coeff 0) * Polynomial.X) :=
  sorry

/-- When `B(0) = 0` the transform does not depend on the rank (§3.3.1). -/
theorem colemanDBounded_add_of_coeff_zero {n m : ℕ} {B P : A[X]} (hB0 : B.coeff 0 = 0)
    (hP0 : P.coeff 0 = 1) (hPn : P.natDegree ≤ n) (hBm : B.natDegree ≤ m) (k : ℕ) :
    colemanDBounded (n + k) m B P = colemanDBounded n m B P :=
  sorry

/-- Check `nonzero_constant_padding` (§3.3.1): over `ℤ`, `D_{1,0}(1, 1) = 1 − T` although
`D_{0,0}(1, 1) = 1`. -/
example : colemanDBounded 1 0 (1 : ℤ[X]) 1 = 1 - Polynomial.X ∧
    colemanDBounded 0 0 (1 : ℤ[X]) 1 = 1 :=
  sorry

/-- Check `nonzero_constant` (§3.3.4): for `B = c ≠ 0` and `P = 1` the rank-`N` transform is
`(1 − cT) ^ N`, whose linear coefficients `−Nc` do not converge in `ℚ_p`. -/
example (p : ℕ) [Fact p.Prime] {c : ℚ_[p]} (hc : c ≠ 0) :
    (∀ N, colemanDBounded N 0 (Polynomial.C c) 1 = (1 - Polynomial.C c * Polynomial.X) ^ N) ∧
      ¬ CauchySeq fun N : ℕ ↦ (colemanDBounded N 0 (Polynomial.C c) 1).coeff 1 :=
  sorry

end ColemanBounded

section ColemanEntire

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]

/-- The **functional majorant** `sup_{m ≥ 1} ‖bₘ‖ rᵐ` of a series `B` at the radius `r`
(§3.3.4). -/
def colemanMajorant (B : PowerSeries R) (r : ℝ) : ℝ :=
  ⨆ m : ℕ, ‖PowerSeries.coeff (m + 1) B‖ * r ^ (m + 1)

/-- **Newton majorants** (§3.3.4): the coefficients of a normalised entire series are dominated by
the products `ρ₀ ⋯ ρ_{j−1}` of a positive sequence decreasing to `0`. -/
theorem exists_newtonMajorant {F : PowerSeries R} (hF : PowerSeries.IsEntire F)
    (hF0 : PowerSeries.coeff 0 F = 1) :
    ∃ ρ : ℕ → ℝ, (∀ i, 0 < ρ i) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ j, ‖PowerSeries.coeff j F‖ ≤ ∏ i ∈ Finset.range j, ρ i :=
  sorry

/-- Along radii decreasing to `0` the functional majorants of an entire series decrease to `0`
(§3.3.4). -/
theorem tendsto_colemanMajorant {B : PowerSeries R} (hB : PowerSeries.IsEntire B) {ρ : ℕ → ℝ}
    (hρ0 : ∀ i, 0 < ρ i) (hρ : Antitone ρ) (hρ' : Tendsto ρ atTop (𝓝 0)) :
    Antitone (fun i ↦ colemanMajorant B (ρ i)) ∧
      Tendsto (fun i ↦ colemanMajorant B (ρ i)) atTop (𝓝 0) :=
  sorry

/-- **The coefficient bound without eigenvalues** (§3.3.4): the `k`-th coefficient of every
truncated transform is at most `β₀ ⋯ β_{k−1}`, with `βᵢ = colemanMajorant B ρᵢ`. -/
theorem norm_coeff_colemanDBounded_le {B F : PowerSeries R} (hB : PowerSeries.IsEntire B)
    (hB0 : PowerSeries.coeff 0 B = 0) (hF0 : PowerSeries.coeff 0 F = 1) {ρ : ℕ → ℝ}
    (hρ0 : ∀ i, 0 < ρ i) (hρ : Antitone ρ)
    (hFρ : ∀ j, ‖PowerSeries.coeff j F‖ ≤ ∏ i ∈ Finset.range j, ρ i) (N M k : ℕ) :
    ‖(colemanDBounded N M (PowerSeries.trunc (M + 1) B) (PowerSeries.trunc (N + 1) F)).coeff k‖ ≤
      ∏ i ∈ Finset.range k, colemanMajorant B (ρ i) :=
  sorry

/-- Check `spectralMajorant_coordinate` (§3.3.4): the majorant of `T` at `r > 0` is `r`. -/
example {r : ℝ} (hr : 0 < r) : colemanMajorant (PowerSeries.X : PowerSeries R) r = r :=
  sorry

/-- Check `spectralMajorant_zero` (§3.3.4): the majorant of `0` vanishes. -/
example (r : ℝ) : colemanMajorant (0 : PowerSeries R) r = 0 :=
  sorry

/-- Check `spectralMajorant_square` (§3.3.4): the majorant of `T²` at `r > 0` is `r²`. -/
example {r : ℝ} (hr : 0 < r) : colemanMajorant (PowerSeries.X ^ 2 : PowerSeries R) r = r ^ 2 :=
  sorry

/-- **Coleman's transform with an entire functional input** (§3.3.4; Coleman, Appendix A3): the
coefficientwise limit of the transforms of the truncations of `F` by the truncations of `B`, the
two ranks tending to infinity independently. -/
def colemanDEntire (B F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k ↦ limUnder (atTop ×ˢ atTop) fun NM : ℕ × ℕ ↦
    (colemanDBounded NM.1 NM.2 (PowerSeries.trunc (NM.2 + 1) B)
      (PowerSeries.trunc (NM.1 + 1) F)).coeff k

/-- The truncated transforms converge to `colemanDEntire B F` in every Gauss norm, the two ranks
tending to infinity independently (§3.3.4). -/
theorem tendsto_gaussNorm_colemanDBounded {B F : PowerSeries R} (hB : PowerSeries.IsEntire B)
    (hB0 : PowerSeries.coeff 0 B = 0) (hF : PowerSeries.IsEntire F)
    (hF0 : PowerSeries.coeff 0 F = 1) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun NM : ℕ × ℕ ↦ PowerSeries.gaussNorm norm c
      ((colemanDBounded NM.1 NM.2 (PowerSeries.trunc (NM.2 + 1) B)
        (PowerSeries.trunc (NM.1 + 1) F) : PowerSeries R) - colemanDEntire B F))
      (atTop ×ˢ atTop) (𝓝 0) :=
  sorry

/-- The transform with entire input is entire with constant coefficient `1` (§3.3.4). -/
theorem colemanDEntire_isEntire {B F : PowerSeries R} (hB : PowerSeries.IsEntire B)
    (hB0 : PowerSeries.coeff 0 B = 0) (hF : PowerSeries.IsEntire F)
    (hF0 : PowerSeries.coeff 0 F = 1) :
    PowerSeries.IsEntire (colemanDEntire B F) ∧ PowerSeries.coeff 0 (colemanDEntire B F) = 1 :=
  sorry

/-- The transform with entire input is multiplicative in `F` (§3.3.4). -/
theorem colemanDEntire_mul {B F G : PowerSeries R} (hB : PowerSeries.IsEntire B)
    (hB0 : PowerSeries.coeff 0 B = 0) (hF : PowerSeries.IsEntire F)
    (hF0 : PowerSeries.coeff 0 F = 1) (hG : PowerSeries.IsEntire G)
    (hG0 : PowerSeries.coeff 0 G = 1) :
    colemanDEntire B (F * G) = colemanDEntire B F * colemanDEntire B G :=
  sorry

/-- Check `identity` (§3.3.4): `D(T, F) = F` for every normalised entire `F`. -/
example {F : PowerSeries R} (hF : PowerSeries.IsEntire F) (hF0 : PowerSeries.coeff 0 F = 1) :
    colemanDEntire PowerSeries.X F = F :=
  sorry

/-- Check `zero` (§3.3.4): `D(0, F) = 1`, and `D(B, 1) = 1` when `B(0) = 0`. -/
example {B F : PowerSeries R} (hB : PowerSeries.IsEntire B) (hB0 : PowerSeries.coeff 0 B = 0)
    (hF : PowerSeries.IsEntire F) (hF0 : PowerSeries.coeff 0 F = 1) :
    colemanDEntire 0 F = 1 ∧ colemanDEntire B 1 = 1 :=
  sorry

/-- Check `nilpotent` (§3.3.4): for `ε² = 0`, `D(T, 1 − εT²) = 1 − εT²`. -/
example {ε : R} (hε : ε ^ 2 = 0) :
    colemanDEntire PowerSeries.X (1 - PowerSeries.C ε * PowerSeries.X ^ 2) =
      1 - PowerSeries.C ε * PowerSeries.X ^ 2 :=
  sorry

/-- Check `wrong_topology` (§3.3.4): `T ^ N` tends to `0` coefficientwise while its Gauss norm at
radius `1` is `1`. -/
example :
    (∀ k, Tendsto (fun N ↦ PowerSeries.coeff k (PowerSeries.X ^ N : PowerSeries R)) atTop
      (𝓝 0)) ∧ ∀ N, PowerSeries.gaussNorm norm 1 (PowerSeries.X ^ N : PowerSeries R) = 1 :=
  sorry

end ColemanEntire

section ColemanTate

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R]
  [IsTate R]
variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- `colemanD` is the transform at the smallest rank, `n = deg P` and `m = deg B` (§3.3.1). -/
theorem colemanD_eq_colemanDBounded {B P : R[X]} (hP0 : P.coeff 0 = 1) :
    colemanD B P = colemanDBounded P.natDegree B.natDegree B P :=
  sorry

/-- For a polynomial `B` with `B(0) = 0`, the transform with entire input is `colemanDSeries`
(§3.3.2, §3.3.4). -/
theorem colemanDEntire_coe {B : R[X]} (hB0 : B.coeff 0 = 0) {F : PowerSeries R}
    (hF : PowerSeries.IsEntire F) (hF0 : PowerSeries.coeff 0 F = 1) :
    colemanDEntire (B : PowerSeries R) F = colemanDSeries B F :=
  sorry

/-- **Operator evaluation of an entire series** (§2.1.2 in the algebra of operators, §3.3.4): the
partial sums `∑_{m<N} bₘ • uᵐ` converge in operator norm. -/
theorem exists_tendsto_opNorm_sum_pow (u : C₀(I, R) →L[R] C₀(I, R)) {B : PowerSeries R}
    (hB : PowerSeries.IsEntire B) :
    ∃ v : C₀(I, R) →L[R] C₀(I, R), Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N,
      PowerSeries.coeff m B • u ^ m)) atTop (𝓝 0) :=
  sorry

/-- For `u` compactoid and `B(0) = 0` the operator `B(u)` is compactoid (§3.3.4). -/
theorem IsCompactoid.of_tendsto_opNorm_sum_pow {u v : C₀(I, R) →L[R] C₀(I, R)}
    (hu : IsCompactoid u) {B : PowerSeries R} (hB : PowerSeries.IsEntire B)
    (hB0 : PowerSeries.coeff 0 B = 0)
    (hv : Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N, PowerSeries.coeff m B • u ^ m))
      atTop (𝓝 0)) :
    IsCompactoid v :=
  sorry

/-- **The spectral mapping formula for an entire `B`** (§3.3.4; Coleman, Theorem A3.9):
`det(1 − T·B(u)) = D(B, det(1 − Tu))` for `u` compactoid and `B(0) = 0`. -/
theorem charPowerSeries_eq_colemanDEntire {u v : C₀(I, R) →L[R] C₀(I, R)} (hu : IsCompactoid u)
    {B : PowerSeries R} (hB : PowerSeries.IsEntire B) (hB0 : PowerSeries.coeff 0 B = 0)
    (hv : Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N, PowerSeries.coeff m B • u ^ m))
      atTop (𝓝 0)) :
    charPowerSeries v = colemanDEntire B (charPowerSeries u) :=
  sorry

/-- Check `entireOperator_zero` (§3.3.4): `B = 0` evaluates to `0` and `B = T` to `u`. -/
example (u v w : C₀(I, R) →L[R] C₀(I, R))
    (hv : Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N,
      PowerSeries.coeff m (0 : PowerSeries R) • u ^ m)) atTop (𝓝 0))
    (hw : Tendsto (fun N ↦ opNorm (w - ∑ m ∈ Finset.range N,
      PowerSeries.coeff m (PowerSeries.X : PowerSeries R) • u ^ m)) atTop (𝓝 0)) :
    v = 0 ∧ w = u :=
  sorry

/-- Check `entireOperator_nilpotent` (§3.3.4): if `u² = 0` then `B(u) = b₀ + b₁ u`. -/
example (u v : C₀(I, R) →L[R] C₀(I, R)) (hu : u * u = 0) (B : PowerSeries R)
    (hv : Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N, PowerSeries.coeff m B • u ^ m))
      atTop (𝓝 0)) :
    v = PowerSeries.coeff 0 B • 1 + PowerSeries.coeff 1 B • u :=
  sorry

/-- Check `entireOperator_constant` (§3.3.4): on `c₀(ℕ, R)`, `B = 1` evaluates to the identity,
which is not compactoid. -/
example (u v : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (hu : IsCompactoid u)
    (hv : Tendsto (fun N ↦ opNorm (v - ∑ m ∈ Finset.range N,
      PowerSeries.coeff m (1 : PowerSeries R) • u ^ m)) atTop (𝓝 0)) :
    v = 1 ∧ ¬ IsCompactoid v :=
  sorry

end ColemanTate

end

end TauCetiRoadmap.CompactOperators
