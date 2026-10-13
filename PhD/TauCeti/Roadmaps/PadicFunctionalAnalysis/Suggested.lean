import Mathlib

/-!
# p-adic functional analysis: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures that
can already be stated against the pinned Mathlib API. It is not an exhaustive list of the results in
any layer, and where the roadmap and this file disagree the roadmap wins.

The point of the file is to pin the design decisions that are easy to get wrong and expensive to
undo: nonarchimedean is `IsUltrametricDist` and a Banach module over a normed ring is
`Module R M` with `IsBoundedSMul R M` (README convention 1); a Banach–Tate ring is a Prop class with
the pseudo-uniformiser as separate data (convention 2); the model space is Mathlib's `C₀(I, R)` on
a discrete `I` (convention 3); orthonormalisability is defined by isometry to it (convention 4); the
operator norm is Mathlib's `sInf` formula, stated for ring scalars (convention 6); the matrix of an
operator has the images of the basis vectors as columns (convention 7); locally analytic functions
of level `h` are presented by their Taylor coefficients on the discs (convention 9); and weight space
is the set of continuous characters with its `T`-coordinate (convention 10).
-/

namespace TauCetiRoadmap.PadicFunctionalAnalysis

open Filter Topology
open scoped ZeroAtInfty Classical

noncomputable section

/-! ## Layer 0: ultrametric sums and nonarchimedean Banach modules -/

section Sums

variable {ι E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]

/-- **The strict bound** (§0.1.3). Mathlib has the summability criterion
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`) and the bound
`‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖` (`IsUltrametricDist.norm_tsum_le`), but not the strict form. No
summability hypothesis is needed: the sum of a non-summable family is `0`. -/
theorem norm_tsum_lt_of_forall_lt {f : ι → E} {B : ℝ} (hB : 0 < B) (h : ∀ i, ‖f i‖ < B) :
    ‖∑' i, f i‖ < B :=
  sorry

/-- **The unique dominant term** (§0.1.3): the engine of every leading-term argument. -/
theorem norm_tsum_eq_of_forall_lt {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ :=
  sorry

end Sums

section Tate

/-- A *multiplicative* element: multiplication by it is norm-multiplicative (§0.2.4). -/
def IsMultiplicative {R : Type*} [Norm R] [Mul R] (a : R) : Prop := ∀ x, ‖a * x‖ = ‖a‖ * ‖x‖

/-- A **multiplicative pseudo-uniformiser** (Johansson–Newton, Definition 2.1.2): a multiplicative
unit of norm less than `1`. Data, because the constants of Layer 1 depend on the choice. -/
structure PseudoUniformizer (R : Type*) [NormedRing R] where
  /-- The unit. -/
  unit : Rˣ
  /-- It is multiplicative. -/
  isMultiplicative : IsMultiplicative (unit : R)
  /-- Its norm is less than `1`. -/
  norm_lt_one : ‖(unit : R)‖ < 1

/-- A normed ring is **Tate** when it has a multiplicative pseudo-uniformiser; a *Banach–Tate ring*
is a complete one. A Prop (README convention 2), not to be confused with Huber's topological
`IsTateRing`, to which §0.4.5 bridges. -/
class IsTate (R : Type*) [NormedRing R] : Prop where
  /-- Some multiplicative pseudo-uniformiser exists. -/
  exists_pseudoUniformizer : Nonempty (PseudoUniformizer R)

/-- **The bridge lemma** (§0.4.4): a normed algebra with `‖1‖ = 1` over a nontrivially normed field
is Tate, with `ϖ = λ • 1` for any scalar `0 < ‖λ‖ < 1`. This is how the field-based theory of
Buzzard and Bellaïche is recovered from the ring-based one. -/
theorem isTate_of_normedAlgebra (K R : Type*) [NontriviallyNormedField K] [NormedRing R]
    [NormedAlgebra K R] [NormOneClass R] : IsTate R :=
  sorry

/-- The valuation `v_ϖ` of a pseudo-uniformiser (§0.4.3): `log ‖r‖ / log ‖ϖ‖`, with `⊤` at `0`, so
that `v_ϖ ϖ = 1` and `‖r‖ = ‖ϖ‖ ^ (v_ϖ r)`. ⚠ Not an `AddValuation` unless the norm is
multiplicative. -/
noncomputable def PseudoUniformizer.val {R : Type*} [NormedRing R] (ϖ : PseudoUniformizer R)
    (r : R) : WithTop ℝ :=
  if r = 0 then ⊤ else ((Real.log ‖r‖ / Real.log ‖(ϖ.unit : R)‖ : ℝ) : WithTop ℝ)

theorem PseudoUniformizer.val_self {R : Type*} [NormedRing R] [Nontrivial R]
    (ϖ : PseudoUniformizer R) : ϖ.val (ϖ.unit : R) = 1 :=
  sorry

/-- **The scaling trick** (§0.4.2): every nonzero vector can be moved into the shell
`‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1` by a unique power of the pseudo-uniformiser. -/
theorem PseudoUniformizer.exists_zpow_smul_mem_shell {R M : Type*} [NormedRing R]
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] (ϖ : PseudoUniformizer R) {m : M}
    (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ≤ 1 ∧ ‖(ϖ.unit : R)‖ < ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ :=
  sorry

end Tate

/-! ## Layer 1: bounded linear maps -/

section OperatorNorm

/-- The operator norm, by Mathlib's formula, for a semiring of scalars (§1.1.1). It is a `def` here
and a `scoped` instance in the development (README convention 6), so that for field scalars
Mathlib's `ContinuousLinearMap.opNorm` remains the only global instance. -/
noncomputable def opNorm {R M N : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module R N] (u : M →L[R] N) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}

variable {R M N : Type*} [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Over a Tate normed ring, continuity is boundedness and the norm bounds the operator
(§1.1.2). ⚠ False over a general normed ring, e.g. `ℤ_p`. -/
theorem le_opNorm [IsTate R] (u : M →L[R] N) (x : M) : ‖u x‖ ≤ opNorm u * ‖x‖ :=
  sorry

/-- **Agreement with Mathlib** (§1.1.6): for field scalars the formula is the operator norm. -/
theorem opNorm_eq {K M N : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M]
    [NormedSpace K M] [NormedAddCommGroup N] [NormedSpace K N] (u : M →L[K] N) :
    opNorm u = ‖u‖ :=
  sorry

/-- **The quantitative open mapping theorem over a Banach–Tate ring** (§1.2.1): preimages of
controlled norm. Derived from Tau Ceti's topological form (Henkel's theorem) by the scaling
trick. -/
theorem exists_preimage_norm_le [IsUltrametricDist M] [IsUltrametricDist N] [CompleteSpace R]
    [IsTate R] [CompleteSpace M] [CompleteSpace N] (u : M →L[R] N)
    (hu : Function.Surjective u) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : N, ∃ m : M, u m = n ∧ ‖m‖ ≤ C * ‖n‖ :=
  sorry

/-- **Banach–Steinhaus over a Banach–Tate ring** (§1.2.4). -/
theorem banach_steinhaus [IsUltrametricDist M] [IsUltrametricDist N] [CompleteSpace R] [IsTate R]
    [CompleteSpace M] {ι : Type*} (u : ι → M →L[R] N) (h : ∀ x, ∃ C, ∀ i, ‖u i x‖ ≤ C) :
    ∃ C, ∀ i, opNorm (u i) ≤ C :=
  sorry

end OperatorNorm

/-! ## Layer 2: the model space and orthonormal bases -/

section ModelSpace

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormOneClass R]
variable {I J : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J]

/-- The model space is `C₀(I, R)` on a discrete `I` (README convention 3); this is the instance
Mathlib lacks (§2.1.1). -/
theorem isUltrametricDist_zeroAtInfty {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] :
    IsUltrametricDist C₀(I, E) :=
  sorry

/-- The coordinate vector `single j r` (§2.1.2). Continuity is automatic on a discrete domain; the
decay at infinity is the finiteness of the support. -/
noncomputable def single [DecidableEq J] (j : J) (r : R) : C₀(J, R) :=
  ⟨⟨Pi.single j r, continuous_of_discreteTopology⟩, sorry⟩

/-- A family is **orthonormal** when its members have norm one and finite combinations have the
sup norm (README convention 5). -/
def IsOrthonormalFamily (R : Type*) [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
    (e : I → M) : Prop :=
  (∀ i, ‖e i‖ = 1) ∧
    ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊

/-- An orthonormal family whose span is dense is an **orthonormal basis** (§2.2.2). -/
def IsOrthonormalBasis (R : Type*) [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
    (e : I → M) : Prop :=
  IsOrthonormalFamily R e ∧ Dense (Submodule.span R (Set.range e) : Set M)

/-- **Orthonormalisable** (README convention 4; Johansson–Newton, Definition 2.1.5): isometric to a
model space. -/
def IsONable (R M : Type*) [NormedRing R] [NormedAddCommGroup M] [Module R M] : Prop :=
  ∃ (I : Type) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃ₗᵢ[R] C₀(I, R))

/-- **Potentially orthonormalisable**: homeomorphic to a model space. -/
def IsPotentiallyONable (R M : Type*) [NormedRing R] [NormedAddCommGroup M] [Module R M] : Prop :=
  ∃ (I : Type) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃L[R] C₀(I, R))

/-- The isometry to the model space is an orthonormal basis, and conversely (§2.2.3). -/
theorem isONable_iff_exists_isOrthonormalBasis (M : Type*) [NormedAddCommGroup M] [Module R M]
    [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] :
    IsONable R M ↔ ∃ (I : Type) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (e : I → M),
      IsOrthonormalBasis R e :=
  sorry

/-- **Serre's theorem, field form** (§2.3.3): every Banach space over a discretely valued
nonarchimedean field is potentially orthonormalisable. Discreteness is the Newton-polygons
roadmap's `IsRankOneDiscrete` for `NormedField.valuation`. -/
theorem isPotentiallyONable_of_isRankOneDiscrete (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    [(NormedField.valuation (K := K)).IsRankOneDiscrete] (M : Type*) [NormedAddCommGroup M]
    [NormedSpace K M] [IsUltrametricDist M] [CompleteSpace M] : IsPotentiallyONable K M :=
  sorry

/-- The matrix of a bounded operator between model spaces (README convention 7): column `j` is the
image of the `j`-th basis vector. -/
noncomputable def matrixCoeff [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    R :=
  u (single j 1) i

/-- Each column of the matrix tends to `0` cofinitely, and the norm is the sup of the entries
(§2.6.1). -/
theorem tendsto_matrixCoeff_column [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) :
    Tendsto (fun i ↦ matrixCoeff u i j) cofinite (𝓝 0) :=
  sorry

/-- **A unitriangular perturbation** (§2.7.1): entries in the unit ball, multiplicative units of
norm one on the diagonal, entries of norm at most `q < 1` below it, finitely supported columns. -/
structure IsUnitriangularPerturbation (a : ℕ → ℕ → R) (q : ℝ) : Prop where
  q_lt_one : q < 1
  norm_le_one : ∀ i j, ‖a i j‖ ≤ 1
  diag_isUnit : ∀ i, IsUnit (a i i)
  diag_isMultiplicative : ∀ i, IsMultiplicative (a i i)
  norm_diag : ∀ i, ‖a i i‖ = 1
  norm_lower_le : ∀ i j, j < i → ‖a i j‖ ≤ q
  column_finite : ∀ j, {i | a i j ≠ 0}.Finite

/-- Such a matrix is the matrix of an isometric automorphism of `C₀(ℕ, R)` (§2.7.1): the criterion
behind Amice's theorem, over any nonarchimedean Banach ring and with no residue field. -/
theorem exists_linearIsometryEquiv_of_isUnitriangularPerturbation [CompleteSpace R]
    {a : ℕ → ℕ → R} {q : ℝ} (ha : IsUnitriangularPerturbation a q) :
    ∃ T : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R),
      ∀ i j, matrixCoeff T.toContinuousLinearEquiv.toContinuousLinearMap i j = a i j :=
  sorry

end ModelSpace

/-! ## Layer 3: continuous functions on `ℤ_p` -/

section Continuous

/-- **Locally constant functions are dense** in the continuous functions on a profinite space
(§3.1.2); not in Mathlib. -/
theorem dense_range_locallyConstant (X E : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [MetricSpace E] :
    Dense (Set.range fun f : LocallyConstant X E ↦ (⟨f, f.continuous⟩ : C(X, E))) :=
  sorry

end Continuous

/-! ## Layer 4: locally analytic functions -/

section LocallyAnalytic

variable {p : ℕ} [hp : Fact p.Prime]
variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

/-- **The Amice basis** `⌊n/pʰ⌋! · (x choose n)` (§4.4.1), built on Mathlib's `PadicInt.mahler`. -/
noncomputable def amice (h n : ℕ) : C(ℤ_[p], ℤ_[p]) :=
  ((n / p ^ h).factorial : ℤ_[p]) • mahler (p := p) n

/-- The Amice term `⌊n/pʰ⌋! · (x choose n) · a`, mirroring `PadicInt.mahlerTerm`. -/
noncomputable def amiceTerm (a : E) (h n : ℕ) : C(ℤ_[p], E) :=
  (amice (p := p) h n : C(_, ℤ_[p])) • .const _ a

/-- **The disc model** of the functions analytic on every disc `a + pʰ ℤ_p` (README convention 9):
the Taylor coefficients at the natural centre of each disc, in the coordinate `w` with
`x = a + pʰ w`. -/
abbrev LocallyAnalytic (h : ℕ) (E : Type*) [NormedAddCommGroup E] : Type _ :=
  C₀(ZMod (p ^ h) × ℕ, E)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- Evaluation of a coefficient family as a function on `ℤ_p` (§4.3.1): `∑ₖ c (a, k) • wᵏ` at
`a + pʰ w`. Norm-decreasing; injective under the hypothesis of §4.1.6, and not in general. -/
noncomputable def eval (h : ℕ) : LocallyAnalytic (p := p) h E →L[ℤ_[p]] C(ℤ_[p], E) :=
  sorry

/-- `f` is **analytic of level `h`**: it is the evaluation of some coefficient family. -/
def IsAnalyticOfLevel (h : ℕ) (f : C(ℤ_[p], E)) : Prop :=
  ∃ c : LocallyAnalytic (p := p) h E, eval h c = f

/-- **Amice's theorem** (§4.4.2; Colmez, Théorème 1.4.7): the Amice basis is an orthonormal basis of
the level-`h` locally analytic functions, module-valued. -/
theorem exists_amiceEquiv (h : ℕ) :
    ∃ e : C₀(ℕ, E) ≃ₗᵢ[ℤ_[p]] LocallyAnalytic (p := p) h E,
      ∀ b : C₀(ℕ, E), eval h (e b) = ∑' n, amiceTerm (b n) h n :=
  sorry

/-- The Mahler coefficients of a level-`h` function are `⌊n/pʰ⌋!` times its Amice coordinates
(§4.4.3); for a `ℚ_p`-Banach space this is the criterion `aₙ(f) / ⌊n/pʰ⌋! → 0`. -/
theorem mahlerEquiv_eval_amice (h : ℕ) (e : C₀(ℕ, E) ≃ₗᵢ[ℤ_[p]] LocallyAnalytic (p := p) h E)
    (he : ∀ b : C₀(ℕ, E), eval h (e b) = ∑' n, amiceTerm (b n) h n) (b : C₀(ℕ, E)) (n : ℕ) :
    PadicInt.mahlerEquiv E (eval h (e b)) n = ((n / p ^ h).factorial : ℤ_[p]) • b n :=
  sorry

end LocallyAnalytic

section ExpLog

variable {p : ℕ} [hp : Fact p.Prime]
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A]
  [CompleteSpace A]

/-- The radius `p^{-1/(p-1)}` of the exponential disc; `‖p‖ = p⁻¹` because `A` is a normed
`ℚ_p`-algebra (README convention 8). -/
noncomputable def expRadius (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))

/-- The `p`-adic exponential `∑ xⁿ / n!` (§4.5.1). -/
noncomputable def padicExp (x : A) : A := ∑' n : ℕ, ((n.factorial : ℚ_[p])⁻¹) • x ^ n

/-- The `p`-adic logarithm `∑ (−1)ⁿ (u − 1)ⁿ⁺¹ / (n + 1)` (§4.5.1). -/
noncomputable def padicLog (u : A) : A :=
  ∑' n : ℕ, ((-1 : ℚ_[p]) ^ n * ((n + 1 : ℕ) : ℚ_[p])⁻¹) • (u - 1) ^ (n + 1)

/-- The binomial series `(1 + x)^s = ∑ (s choose n) xⁿ` with an arbitrary exponent `s : A`
(§4.5.5). -/
noncomputable def binomialSeries (s x : A) : A :=
  ∑' n : ℕ, (((n.factorial : ℚ_[p])⁻¹) • ∏ i ∈ Finset.range n, (s - (i : A))) * x ^ n

/-- **The exponential disc is sharp** (§4.5.1). -/
theorem hasSum_padicExp {x : A} (hx : ‖x‖ < expRadius p) :
    HasSum (fun n : ℕ ↦ ((n.factorial : ℚ_[p])⁻¹) • x ^ n) (padicExp (p := p) x) :=
  sorry

/-- `exp ∘ log = id` on the joint disc (§4.5.3). -/
theorem padicExp_padicLog {u : A} (hu : ‖u - 1‖ < expRadius p) :
    padicExp (p := p) (padicLog (p := p) u) = u :=
  sorry

/-- **The binomial series is an exponential** (§4.5.5), proved by the identity theorem in the
exponent. -/
theorem binomialSeries_eq_padicExp {s x : A} (hx : ‖x‖ < expRadius p)
    (hsx : ‖s‖ * ‖x‖ < expRadius p) :
    binomialSeries (p := p) s x = padicExp (p := p) (s * padicLog (p := p) (1 + x)) :=
  sorry

end ExpLog

/-! ## Layer 5: weight space and the halo -/

section WeightSpace

variable (p : ℕ) [hp : Fact p.Prime]

/-- `q = 4` for `p = 2` and `q = p` otherwise (Liu–Wan–Xiao, Notation 2.1). -/
def q : ℕ := if p = 2 then 4 else p

/-- **Weight space** over `R` (README convention 10): the continuous characters of `ℤ_pˣ`. -/
abbrev WeightSpace (R : Type*) [Monoid R] [TopologicalSpace R] : Type _ := ℤ_[p]ˣ →ₜ* Rˣ

/-- The topological generator `exp q` of `1 + qℤ_p` (§5.1.2): the element with `log γ = q`. -/
noncomputable def gamma : ℤ_[p]ˣ := sorry

variable {p}

/-- The `T`-coordinate `κ γ − 1` of a weight (§5.2.1). -/
def TCoord {R : Type*} [Ring R] [TopologicalSpace R] (κ : WeightSpace p R) : R :=
  (κ (gamma p) : R) - 1

variable {R : Type*} [NormedCommRing R] [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]

/-- The `T`-coordinate is topologically nilpotent (§5.2.1). -/
theorem isTopologicallyNilpotent_TCoord [IsUltrametricDist R] (κ : WeightSpace p R) :
    IsTopologicallyNilpotent (TCoord κ) :=
  sorry

/-- **The parametrisation of weight space** (§5.2.2): Mathlib's `PadicInt.continuousAddCharEquiv`
on the `1 + qℤ_p` factor and the finite group `Δ = (ZMod q)ˣ`. -/
theorem nonempty_weightSpace_equiv [IsUltrametricDist R] [CompleteSpace R] :
    Nonempty (WeightSpace p R ≃ ((ZMod (q p))ˣ →* Rˣ) × {r : R // IsTopologicallyNilpotent r}) :=
  sorry

/-- A weight is **analytic of level `h`** (§5.4.1): as a function on the units it is the
evaluation of a level-`h` coefficient family. -/
def IsAnalyticOfLevelWeight [IsUltrametricDist R] [CompleteSpace R] (h : ℕ)
    (κ : WeightSpace p R) : Prop :=
  ∃ c : LocallyAnalytic (p := p) h R, ∀ x : ℤ_[p]ˣ, eval h c (x : ℤ_[p]) = ((κ x : Rˣ) : R)

/-- **The level criterion** (§5.4.2), for a field: `κ` is analytic of level `h` iff
`‖T_κ‖ < p^{−q/(pʰ(p−1))}`; Liu–Wan–Xiao's "`m`-locally analytic". -/
theorem isAnalyticOfLevelWeight_iff {K : Type*} [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K]
    [Module ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
    (κ : WeightSpace p K) (h : ℕ) (hh : q p ∣ p ^ h) :
    IsAnalyticOfLevelWeight h κ ↔
      ‖TCoord κ‖ < (p : ℝ) ^ (-((q p : ℝ) / ((p : ℝ) ^ h * ((p : ℝ) - 1)))) :=
  sorry

end WeightSpace

section Halo

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The halo ring** `Λ^{>1/p} = ℤ_p⟦T, pT⁻¹⟧`, one component (README convention 11; Liu–Wan–Xiao,
Lemma 3.15): Laurent coefficient streams with `v_p(dₘ) ≥ max(0, −m)`. -/
structure Halo where
  /-- The coefficient of `Tᵐ`. -/
  coeff : ℤ → ℤ_[p]
  /-- The halo bound `‖dₘ‖ ≤ p^{min(0, m)}`. -/
  norm_coeff_le : ∀ m, ‖coeff m‖ ≤ (p : ℝ) ^ (min 0 m)

variable {p}

/-- The gauge norm `sup_m ‖dₘ‖ p^{−m}` (§5.6.1). -/
noncomputable instance : Norm (Halo p) :=
  ⟨fun d ↦ ⨆ m : ℤ, ‖d.coeff m‖ * (p : ℝ) ^ (-m)⟩

/-- The variable `T = δ₁`. -/
noncomputable def Halo.T : Halo p :=
  ⟨fun m ↦ if m = 1 then 1 else 0, sorry⟩

/-- **`T`-divisibility is a norm bound** (§5.6.2): `T ^ k ∣ d` iff `‖d‖ ≤ p^{−k}`, in coefficient
form. -/
theorem Halo.norm_le_zpow_iff (d : Halo p) (k : ℕ) :
    ‖d‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ↔ ∀ m : ℤ, ‖d.coeff m‖ ≤ (p : ℝ) ^ (min 0 (m - k)) :=
  sorry

/-- **Specialisation at a halo point** converges exactly on the open annulus (§5.6.4). -/
theorem Halo.summable_specialize {K : Type*} [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K]
    [IsUltrametricDist K] [CompleteSpace K] (d : Halo p) {T₀ : K} (h₁ : (p : ℝ)⁻¹ < ‖T₀‖)
    (h₂ : ‖T₀‖ < 1) :
    Summable fun m : ℤ ↦ algebraMap ℚ_[p] K (d.coeff m : ℚ_[p]) * T₀ ^ m :=
  sorry

end Halo

end

end TauCetiRoadmap.PadicFunctionalAnalysis

/-! ## Targets requested by the Tau Ceti PadicMeasuresIwasawaAlgebras, LocallyAnalyticDistributions and AdicSpaces roadmaps -/

namespace TauCetiRoadmap.PadicFunctionalAnalysis

open Filter Topology
open scoped ZeroAtInfty Classical AbstractMeasure PowerSeries.WithPiTopology

noncomputable section

/-! ### Layer 0, §0.4.6: the datum-dependent gauge -/

/-- The gauge attached to the ring of definition, unit and inverse radius of §0.4.6. -/
def tateGauge {A : Type*} [CommRing A] (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (x : A) : ℝ :=
  sInf ((fun n : ℤ ↦ a ^ (-n)) '' {n | ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀})

/-- The gauge gives an ultrametric ring seminorm and its open balls recover the topology. -/
theorem exists_tateSeminorm {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (ha : 1 < a)
    (hϖ : (ϖ : A) ∈ A₀) (hnil : IsTopologicallyNilpotent (ϖ : A))
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀})) :
    ∃ α : RingSeminorm A, (∀ x, α x = tateGauge A₀ ϖ a x) ∧
      (∀ x y, α (x + y) ≤ max (α x) (α y)) ∧
      (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ {x | α x < ε}) := sorry

/-- The seminorm kernel is the closure of zero, so separation is exactly Hausdorffness. -/
theorem tateGauge_eq_zero_iff {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (ha : 1 < a)
    (hϖ : (ϖ : A) ∈ A₀) (hnil : IsTopologicallyNilpotent (ϖ : A))
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀})) :
    (∀ x, tateGauge A₀ ϖ a x = 0 ↔ x ∈ closure ({0} : Set A)) ∧
      ((∀ x, tateGauge A₀ ϖ a x = 0 ↔ x = 0) ↔ T2Space A) := sorry

/-- Changing the ring of definition, with fixed unit and radius, gives bounded-equivalent gauges. -/
theorem tateGauge_equiv {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (A₀ B₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (ha : 1 < a)
    (hA : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀}))
    (hB : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ B₀}))
    (hϖA : (ϖ : A) ∈ A₀) (hϖB : (ϖ : A) ∈ B₀)
    (hnil : IsTopologicallyNilpotent (ϖ : A)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x,
      tateGauge A₀ ϖ a x ≤ C * tateGauge B₀ ϖ a x ∧
      tateGauge B₀ ϖ a x ≤ C * tateGauge A₀ ϖ a x := sorry

/-- Changing only the inverse radius raises the gauge to the indicated real power. -/
theorem tateGauge_rpow {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (A₀ : Subring A) (ϖ : Aˣ) (a b : ℝ) (ha : 1 < a) (hb : 1 < b)
    (hϖ : (ϖ : A) ∈ A₀) (hnil : IsTopologicallyNilpotent (ϖ : A))
    (hbase : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀})) (x : A) :
    tateGauge A₀ ϖ b x = (tateGauge A₀ ϖ a x) ^ (Real.log b / Real.log a) := sorry

example (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) (hu : (u : ℚ_[p]) = p) (x : ℚ_[p]) :
    tateGauge (PadicInt.subring p) u p x = ‖x‖ := sorry

example (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) (hu : (u : ℚ_[p]) = (p : ℚ_[p]) ^ 2) :
    tateGauge (PadicInt.subring p) u p (p : ℚ_[p]) = 1 ∧
    tateGauge (PadicInt.subring p) u p ((p : ℚ_[p]) ^ 2) = (p : ℝ)⁻¹ ∧
      tateGauge (PadicInt.subring p) u p ((p : ℚ_[p]) ^ 2) ≠
        tateGauge (PadicInt.subring p) u p (p : ℚ_[p]) ^ 2 := sorry

example (a : ℝ) (ha : 1 < a) (x : ZMod 1) :
    tateGauge (⊤ : Subring (ZMod 1)) 1 a x = 0 := sorry

example (p : ℕ) [Fact p.Prime] (A₀ : Subring (ℚ_[p] × ℚ_[p]))
    (hA₀ : ∀ x, x ∈ A₀ ↔ ‖x.1‖ ≤ 1 ∧ ‖x.2‖ ≤ 1 ∧
      ‖x.1 - x.2‖ ≤ (p : ℝ) ^ (-2 : ℤ))
    (u : (ℚ_[p] × ℚ_[p])ˣ) (hu : (u : ℚ_[p] × ℚ_[p]) = ((p : ℚ_[p]), (p : ℚ_[p]) ^ 2))
    (a : ℝ) (ha : 1 < a) :
    (u : ℚ_[p] × ℚ_[p]) ∉ A₀ ∧ tateGauge A₀ u a 1 = 1 ∧
      tateGauge A₀ u a (u : ℚ_[p] × ℚ_[p]) ≤ a⁻¹ ∧
      tateGauge A₀ u a (1 + (u : ℚ_[p] × ℚ_[p])) = a ^ 2 ∧
      max (tateGauge A₀ u a 1) (tateGauge A₀ u a (u : ℚ_[p] × ℚ_[p])) <
        tateGauge A₀ u a (1 + (u : ℚ_[p] × ℚ_[p])) := sorry

/-! ### Layer 2, §2.4.3: strict splitting; §2.6.5: finite coordinates -/

/-- A strict exact Banach sequence with countable-type middle term splits topologically. -/
theorem exists_continuousLinearEquiv_prod_of_countableType
    {K M E N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M] [CompleteSpace M]
    [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] [CompleteSpace E]
    [NormedAddCommGroup N] [NormedSpace K N] [IsUltrametricDist N] [CompleteSpace N]
    (e : ℕ → E) (he : Dense (Submodule.span K (Set.range e) : Set E))
    (i : M →L[K] E) (q : E →L[K] N) (hi : Topology.IsClosedEmbedding i)
    (hq : Function.Surjective q) (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) :
    ∃ d : E ≃L[K] M × N, (∀ m, d (i m) = (m, 0)) ∧ ∀ x, (d x).2 = q x := sorry

-- The constant coefficient and the constant series give the Tate-module splitting.
example {K : Type*} [NontriviallyNormedField K] (f : C₀(ℕ, K)) :
    ∃ (c : C₀(ℕ, K) →L[K] K) (s : K →L[K] C₀(ℕ, K)),
      (∀ g, c g = g 0) ∧ (∀ x, s x = single (J := ℕ) 0 x) ∧
      (∀ x, c (s x) = x) ∧ f = (f - s (c f)) + s (c f) ∧ c (f - s (c f)) = 0 := sorry

-- The two degenerate exact sequences split by the identity, also after scalar extension.
example {K E : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E] :
    ∃ d : E ≃L[K] E, ∀ x, d x = x := sorry

example {K E : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E] :
    ∃ s : E →L[K] E, ∀ x, (ContinuousLinearMap.id K E) (s x) = x := sorry

/-- Finite coordinates control the norm on a finite submodule, without assuming freeness. -/
theorem exists_finset_norm_le {R I : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] [CompleteSpace R] [IsTate R] [IsNoetherianRing R]
    [TopologicalSpace I] [DiscreteTopology I] (P : Submodule R C₀(I, R)) (hP : P.FG) :
    ∃ (S : Finset I) (C : ℝ), 0 < C ∧ ∀ f ∈ P, ‖f‖ ≤ C * (S.sup fun i ↦ ‖f i‖₊) := sorry

example {R I : Type*} [NormedCommRing R] [TopologicalSpace I] [DiscreteTopology I]
    (f : C₀(I, R)) (hf : f ∈ (⊥ : Submodule R C₀(I, R))) :
    ‖f‖ ≤ 1 * ((∅ : Finset I).sup fun i ↦ ‖f i‖₊) := sorry

example {R I : Type*} [NormedCommRing R] [TopologicalSpace I] [DiscreteTopology I]
    [DecidableEq I] (i : I) (r : R) :
    ‖single i r‖ ≤ 1 * (({i} : Finset I).sup fun j ↦ ‖single i r j‖₊) := sorry

example {R I : Type*} [NormedCommRing R] [TopologicalSpace I] [DiscreteTopology I]
    (S : Finset I) (f : C₀(I, R)) (hf : ∀ i, i ∉ S → f i = 0) :
    ‖f‖ ≤ 1 * (S.sup fun i ↦ ‖f i‖₊) := sorry

/-! ### Layer 3, §3.4: native measures, bounded coefficients and Frobenius -/

section Measures

variable {p : ℕ} [Fact p.Prime]

/-- The integral scalar action on the rational field is norm-decreasing. -/
local instance isBoundedSMul_padicInt_padic : IsBoundedSMul ℤ_[p] ℚ_[p] := sorry

/-- The native power series of Mahler moments on the existing measure carrier. -/
def amiceTransform {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] (μ : AbstractMeasure ℤ_[p] R R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ μ (PadicInt.mahlerTerm (1 : R) n)

/-- The Mahler moments determine the dual operator norm. -/
theorem norm_toCLMEquiv_eq_iSup_coeff {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
    (μ : AbstractMeasure ℤ_[p] K K) :
    ‖AbstractMeasure.toCLMEquiv μ‖ = ⨆ n, ‖(amiceTransform μ).coeff n‖ := sorry

/-- Exactly the bounded native coefficient streams are transforms of bounded measures. -/
theorem mem_range_amiceTransform_iff {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
    (F : PowerSeries K) :
    (∃ μ : AbstractMeasure ℤ_[p] K K, amiceTransform μ = F) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖F.coeff n‖ ≤ C := sorry

example : amiceTransform (AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p])) = 1 ∧
    ‖AbstractMeasure.toCLMEquiv (AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p]))‖ = 1 := sorry

example : amiceTransform ((p : ℚ_[p])⁻¹ • AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p])) =
      PowerSeries.C (p : ℚ_[p])⁻¹ ∧
    ‖AbstractMeasure.toCLMEquiv ((p : ℚ_[p])⁻¹ • AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p]))‖ = p := sorry

example : ¬ ∃ μ : AbstractMeasure ℤ_[p] ℚ_[p] ℚ_[p],
    amiceTransform μ = PowerSeries.mk (fun n ↦ (p : ℚ_[p]) ^ (-(n : ℤ))) := sorry

/-- Integral measures identify with the rational continuous-dual unit ball by integral tests. -/
theorem existsUnique_integral_iff_norm_le_one (ν : AbstractMeasure ℤ_[p] ℚ_[p] ℚ_[p]) :
    (∃! μ : AbstractMeasure ℤ_[p] ℤ_[p] ℤ_[p], ∀ f : C(ℤ_[p], ℤ_[p]),
      ν ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
        (μ f : ℚ_[p])) ↔ ‖AbstractMeasure.toCLMEquiv ν‖ ≤ 1 := sorry

example : ‖AbstractMeasure.toCLMEquiv (AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p]))‖ ≤ 1 ∧
    ∀ f : C(ℤ_[p], ℤ_[p]),
      AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p])
        ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
        (AbstractMeasure.dirac ℤ_[p] (0 : ℤ_[p]) f : ℚ_[p]) := sorry

example : ‖AbstractMeasure.toCLMEquiv (0 : AbstractMeasure ℤ_[p] ℚ_[p] ℚ_[p])‖ ≤ 1 ∧
    ∀ f : C(ℤ_[p], ℤ_[p]),
      (0 : AbstractMeasure ℤ_[p] ℚ_[p] ℚ_[p])
        ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
        ((0 : AbstractMeasure ℤ_[p] ℤ_[p] ℤ_[p]) f : ℚ_[p]) := sorry

example : ¬ ‖AbstractMeasure.toCLMEquiv
    ((p : ℚ_[p])⁻¹ • AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p]))‖ ≤ 1 ∧
    ¬ ∃ μ : AbstractMeasure ℤ_[p] ℤ_[p] ℤ_[p], ∀ f : C(ℤ_[p], ℤ_[p]),
      ((p : ℚ_[p])⁻¹ • AbstractMeasure.dirac ℚ_[p] (0 : ℤ_[p]))
        ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
        (μ f : ℚ_[p]) := sorry

/-- Frobenius is pushforward along multiplication by p, with no mass rescaling. -/
def phiMeasure (R : Type*) [NormedCommRing R] :
    AbstractMeasure ℤ_[p] R R →ₗ[R] AbstractMeasure ℤ_[p] R R :=
  AbstractMeasure.map ⟨fun x ↦ (p : ℤ_[p]) * x, continuous_const.mul continuous_id⟩

/-- The continuous characteristic function of the clopen p-multiples. -/
def pMultiplesIndicator (R : Type*) [NormedCommRing R] : C(ℤ_[p], R) :=
  ⟨fun x ↦ if PadicInt.toZMod x = 0 then 1 else 0, sorry⟩

/-- Weighting a measure acts by `(weightMeasure g μ)(f) = μ (g * f)` on continuous tests. -/
def weightMeasure {R : Type*} [NormedCommRing R] (g : C(ℤ_[p], R)) :
    AbstractMeasure ℤ_[p] R R →ₗ[R] AbstractMeasure ℤ_[p] R R := sorry

/-- The two projector identities determine the left inverse of Frobenius uniquely. -/
theorem existsUnique_psiMeasure (R : Type*) [NormedCommRing R] :
    ∃! ψ : AbstractMeasure ℤ_[p] R R →ₗ[R] AbstractMeasure ℤ_[p] R R,
      (∀ μ, ψ (phiMeasure R μ) = μ) ∧
        ∀ μ, phiMeasure R (ψ μ) = weightMeasure (pMultiplesIndicator R) μ := sorry

/-- Frobenius is binomial substitution on integral Amice transforms. -/
theorem amiceTransform_phiMeasure (μ : AbstractMeasure ℤ_[p] ℤ_[p] ℤ_[p]) :
    amiceTransform (phiMeasure ℤ_[p] μ) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p])
        (amiceTransform μ) := sorry

example : phiMeasure (p := 3) ℤ_[3] 0 = 0 := sorry

example : phiMeasure (p := 3) ℤ_[3] (AbstractMeasure.dirac ℤ_[3] 2) =
    AbstractMeasure.dirac ℤ_[3] 6 := sorry

example (μ : AbstractMeasure ℤ_[3] ℤ_[3] ℤ_[3]) :
    phiMeasure ℤ_[3] μ 1 = μ 1 := sorry

example (ψ : AbstractMeasure ℤ_[3] ℤ_[3] ℤ_[3] →ₗ[ℤ_[3]] AbstractMeasure ℤ_[3] ℤ_[3] ℤ_[3])
    (h₁ : ∀ μ, ψ (phiMeasure ℤ_[3] μ) = μ)
    (h₂ : ∀ μ, phiMeasure ℤ_[3] (ψ μ) = weightMeasure (pMultiplesIndicator ℤ_[3]) μ) :
    ψ (AbstractMeasure.dirac ℤ_[3] 0) = AbstractMeasure.dirac ℤ_[3] 0 ∧
      ψ (AbstractMeasure.dirac ℤ_[3] 6) = AbstractMeasure.dirac ℤ_[3] 2 ∧
      ψ (AbstractMeasure.dirac ℤ_[3] 1) = 0 := sorry

example : amiceTransform (phiMeasure (p := 3) ℤ_[3] (AbstractMeasure.dirac ℤ_[3] 0)) = 1 := sorry

example : amiceTransform (phiMeasure (p := 3) ℤ_[3] (AbstractMeasure.dirac ℤ_[3] 1)) =
    (1 + PowerSeries.X) ^ 3 := sorry

example : amiceTransform (phiMeasure (p := 3) ℤ_[3] 0) = 0 := sorry

end Measures

/-! ### Layer 4, §4.7.2: coefficient forms of the quantitative distribution estimates -/

section DistributionEstimates

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- The level-h dual norm computed from Mahler moments in the Amice basis. -/
def amiceDualNorm (h : ℕ) (F : PowerSeries K) : ℝ :=
  ⨆ n, ‖F.coeff n‖ * ‖((n / p ^ h).factorial : ℚ_[p])‖

/-- The coefficient Gauss norm on the disc with valuation radius 1/((p-1)p^h). -/
def amiceDiscNorm (h : ℕ) (F : PowerSeries K) : ℝ :=
  ⨆ n : ℕ, ‖F.coeff n‖ * (p : ℝ) ^ (-((n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ h)))

/-- The Gauss norm at the level-h radius is bounded by the level-h Amice dual norm. -/
theorem amiceDiscNorm_le_amiceDualNorm (h : ℕ) (F : PowerSeries K)
    (hF : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → PowerSeries.IsRestricted ρ F) :
    amiceDiscNorm (p := p) h F ≤ amiceDualNorm (p := p) h F := sorry

/-- The Amice dual norm is at most p times the Gauss norm at the next radius. -/
theorem amiceDualNorm_le_amiceDiscNorm (h : ℕ) (F : PowerSeries K)
    (hF : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → PowerSeries.IsRestricted ρ F) :
    amiceDualNorm (p := p) h F ≤ p * amiceDiscNorm (p := p) (h + 1) F := sorry

example (h : ℕ) : amiceDiscNorm (p := p) h (0 : PowerSeries K) = 0 ∧
    amiceDualNorm (p := p) h (0 : PowerSeries K) = 0 := sorry

example (h : ℕ) : amiceDiscNorm (p := p) h (1 : PowerSeries K) = 1 ∧
    amiceDualNorm (p := p) h (1 : PowerSeries K) = 1 := sorry

-- The derivative distribution gives a logarithm, whose coefficients are unbounded.
example (h : ℕ) :
    let F : PowerSeries ℚ_[p] := PowerSeries.mk fun n ↦
      if n = 0 then 0 else (-1 : ℚ_[p]) ^ (n + 1) / n
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → PowerSeries.IsRestricted ρ F) ∧
      (¬ ∃ C : ℝ, ∀ n, ‖F.coeff n‖ ≤ C) ∧
      amiceDiscNorm (p := p) h F ≤ amiceDualNorm (p := p) h F ∧
      amiceDualNorm (p := p) h F ≤ p * amiceDiscNorm (p := p) (h + 1) F := sorry

end DistributionEstimates

/-! ### Layer 5, §5.3.3: the character part of the adic and normed universal properties -/

section UniversalCharacter

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic topology of the integral coefficient ring is linear. -/
local instance isLinearTopology_padicInt : IsLinearTopology ℤ_[p] ℤ_[p] := sorry

/-- Adic specialisation of the principal universal character, with a prescribed torsion factor. -/
theorem exists_character_of_hasEval {S : Type*} [CommRing S] [UniformSpace S]
    [IsUniformAddGroup S] [IsTopologicalRing S] [IsLinearTopology S S] [CompleteSpace S]
    [T2Space S] [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S]
    (e : ℤ_[p]ˣ ≃ₜ* ((ZMod (q p))ˣ × Multiplicative ℤ_[p]))
    (he : e (gamma p) = (1, Multiplicative.ofAdd 1))
    (η : (ZMod (q p))ˣ →* Sˣ) {z : S} (hz : PowerSeries.HasEval z) :
    ∃! κ : WeightSpace p S, TCoord κ = z ∧ ∀ x,
      (κ x : S) = (η (e x).1 : S) * PowerSeries.aeval (R := ℤ_[p]) hz
        (PowerSeries.binomialSeries ℤ_[p] (Multiplicative.toAdd (e x).2)) := sorry

/-- A weight with nilpotent principal coordinate is the adic evaluation of its binomial character. -/
theorem eq_aeval_binomialSeries {S : Type*} [CommRing S] [UniformSpace S]
    [IsUniformAddGroup S] [IsTopologicalRing S] [IsLinearTopology S S] [CompleteSpace S]
    [T2Space S] [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S]
    (e : ℤ_[p]ˣ ≃ₜ* ((ZMod (q p))ˣ × Multiplicative ℤ_[p]))
    (he : e (gamma p) = (1, Multiplicative.ofAdd 1)) (κ : WeightSpace p S)
    (hz : PowerSeries.HasEval (TCoord κ)) (x : ℤ_[p]ˣ) :
    (κ x : S) = (κ (e.symm ((e x).1, 1)) : S) *
      PowerSeries.aeval (R := ℤ_[p]) hz
        (PowerSeries.binomialSeries ℤ_[p] (Multiplicative.toAdd (e x).2)) := sorry

/-- Small-norm specialisation gives a unique weight, with its convergent binomial sum formula. -/
theorem existsUnique_character_of_norm_lt_one {A : Type*} [NormedCommRing A]
    [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A] [CompleteSpace A]
    (e : ℤ_[p]ˣ ≃ₜ* ((ZMod (q p))ˣ × Multiplicative ℤ_[p]))
    (he : e (gamma p) = (1, Multiplicative.ofAdd 1))
    (η : (ZMod (q p))ˣ →* Aˣ) {z : A} (hz : ‖z‖ < 1) :
    ∃! κ : WeightSpace p A, TCoord κ = z ∧ ∀ x,
      HasSum (fun n : ℕ ↦ (η (e x).1 : A) *
        (((Ring.choose (Multiplicative.toAdd (e x).2) n : ℤ_[p]) : ℚ_[p]) • z ^ n))
        (κ x : A) := sorry

example (n : ℕ) : PowerSeries.binomialSeries ℤ_[p] (n : ℤ_[p]) =
    (1 + PowerSeries.X) ^ n ∧
    (PowerSeries.binomialSeries ℤ_[p] (n : ℤ_[p])).coeff 1 = n := sorry

example : PowerSeries.binomialSeries ℤ_[p] (-1 : ℤ_[p]) =
    PowerSeries.mk (fun n ↦ (-1) ^ n) ∧
    PowerSeries.binomialSeries ℤ_[p] (-1 : ℤ_[p]) ≠ 1 - PowerSeries.X := sorry

example (e : ℤ_[p]ˣ ≃ₜ* ((ZMod (q p))ˣ × Multiplicative ℤ_[p]))
    (he : e (gamma p) = (1, Multiplicative.ofAdd 1)) :
    (∃ κ : WeightSpace p (TrivSqZeroExt ℚ_[p] ℚ_[p]), ∀ x,
      (κ x : TrivSqZeroExt ℚ_[p] ℚ_[p]) =
        1 + TrivSqZeroExt.inr ((Multiplicative.toAdd (e x).2 : ℤ_[p]) : ℚ_[p])) ∧
      max ‖(TrivSqZeroExt.inr 1 : TrivSqZeroExt ℚ_[p] ℚ_[p]).fst‖
        ‖(TrivSqZeroExt.inr 1 : TrivSqZeroExt ℚ_[p] ℚ_[p]).snd‖ = 1 := sorry

example : TCoord (1 : WeightSpace p ℤ_[p]) = 0 := sorry

-- The dual-number evaluation only uses the constant and linear coefficients.
example : ∃ f : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] TrivSqZeroExt ℚ_[p] ℚ_[p],
    Continuous f ∧ ∀ F, f F = TrivSqZeroExt.inl (F.coeff 0 : ℚ_[p]) +
      TrivSqZeroExt.inr (F.coeff 1 : ℚ_[p]) := sorry

example (F : PowerSeries ℤ_[p]) :
    PowerSeries.aeval (R := ℤ_[p]) (PowerSeries.HasEval.zero : PowerSeries.HasEval (0 : ℤ_[p])) F =
      F.coeff 0 := sorry

example (n : ℕ) : ∃ hp : PowerSeries.HasEval (p : ℤ_[p]),
    PowerSeries.aeval (R := ℤ_[p]) hp (PowerSeries.binomialSeries ℤ_[p] (n : ℤ_[p])) =
      (1 + (p : ℤ_[p])) ^ n := sorry

example : ¬ PowerSeries.HasEval ((p : ℚ_[p]) - 1) ∧
    ¬ ∃ f : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] ℚ_[p], Continuous f ∧ f PowerSeries.X = (p : ℚ_[p]) - 1 :=
  sorry

example : ‖(p : ℚ_[p])‖ < 1 ∧ ¬ IsLinearTopology ℚ_[p] ℚ_[p] ∧
    ∃ f : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] ℚ_[p], Continuous f ∧ f PowerSeries.X = p := sorry

end UniversalCharacter

/-! ### Layer 5, §5.3.5: integral measures as bounded functions on the existing weight space -/

section MeasureFunctions

variable {p : ℕ} [Fact p.Prime]

/-- Extend coefficients to `ℂ_p`, characterised by agreement on integral continuous tests:
the value on the coefficient image of `f` is the image of `μ f`. -/
def extendIntegralMeasure (μ : AbstractMeasure ℤ_[p]ˣ ℤ_[p] ℤ_[p]) :
    AbstractMeasure ℤ_[p]ˣ ℂ_[p] ℂ_[p] := sorry

/-- A weight, viewed as a continuous field-valued test function. -/
def weightTest {A : Type*} [NormedCommRing A] (κ : WeightSpace p A) : C(ℤ_[p]ˣ, A) :=
  ⟨fun x ↦ (κ x : A), Units.continuous_val.comp κ.continuous⟩

/-- The specialisation pairing as a function of the weight. -/
def measureFun (μ : AbstractMeasure ℤ_[p]ˣ ℤ_[p] ℤ_[p]) (κ : WeightSpace p ℂ_[p]) : ℂ_[p] :=
  extendIntegralMeasure μ (weightTest κ)

/-- Integral coefficient extension has norm at most one, bounding every character value. -/
theorem measureFun_norm_le (μ : AbstractMeasure ℤ_[p]ˣ ℤ_[p] ℤ_[p])
    (κ : WeightSpace p ℂ_[p]) :
    ‖measureFun μ κ‖ ≤ ‖AbstractMeasure.toCLMEquiv (extendIntegralMeasure μ)‖ ∧
      ‖AbstractMeasure.toCLMEquiv (extendIntegralMeasure μ)‖ ≤ 1 ∧
      (⨆ κ : WeightSpace p ℂ_[p], ‖measureFun μ κ‖) ≤ 1 := sorry

/-- Values on all weights distinguish integral measures. -/
theorem measureFun_injective :
    Function.Injective (measureFun (p := p)) := sorry

example (a b : ℤ_[p]ˣ) (k : ℤ) (κ : WeightSpace p ℂ_[p])
    (hκ : ∀ x, (κ x : ℂ_[p]) = (((x : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) ^ k) :
    measureFun (AbstractMeasure.dirac ℤ_[p] a) κ = (((a : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) ^ k ∧
      measureFun (AbstractMeasure.dirac ℤ_[p] 1) κ = 1 ∧
      measureFun (AbstractMeasure.map
        (⟨fun x : ℤ_[p]ˣ × ℤ_[p]ˣ ↦ x.1 * x.2, continuous_fst.mul continuous_snd⟩)
        (AbstractMeasure.prodMk (AbstractMeasure.dirac ℤ_[p] a) (AbstractMeasure.dirac ℤ_[p] b))) κ =
        ((((a * b : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) ^ k := sorry

example (a b : ℤ_[p]ˣ) (κ : WeightSpace p ℂ_[p])
    (hκ : ∀ x, (κ x : ℂ_[p]) = (((x : ℤ_[p]) : ℚ_[p]) : ℂ_[p])) :
    measureFun (AbstractMeasure.dirac ℤ_[p] a + AbstractMeasure.dirac ℤ_[p] b) κ =
      (((a : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) + (((b : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) := sorry

example (a b : ℤ_[p]ˣ) (hab : a ≠ b) (κ : WeightSpace p ℂ_[p])
    (hκ : ∀ x, (κ x : ℂ_[p]) = (((x : ℤ_[p]) : ℚ_[p]) : ℂ_[p])) :
    measureFun (AbstractMeasure.dirac ℤ_[p] a - AbstractMeasure.dirac ℤ_[p] b) 1 = 0 ∧
      measureFun (AbstractMeasure.dirac ℤ_[p] a - AbstractMeasure.dirac ℤ_[p] b) κ =
        (((a : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) - (((b : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) ∧
      measureFun (AbstractMeasure.dirac ℤ_[p] a - AbstractMeasure.dirac ℤ_[p] b) κ ≠ 0 := sorry

example (a : ℤ_[p]ˣ) (κ : WeightSpace p ℂ_[p]) :
    ‖AbstractMeasure.toCLMEquiv (extendIntegralMeasure (AbstractMeasure.dirac ℤ_[p] a))‖ = 1 ∧
      ‖measureFun (AbstractMeasure.dirac ℤ_[p] a) κ‖ = 1 := sorry

end MeasureFunctions

end

end TauCetiRoadmap.PadicFunctionalAnalysis
