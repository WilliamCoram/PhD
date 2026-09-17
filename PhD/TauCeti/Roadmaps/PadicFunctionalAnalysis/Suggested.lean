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

/-- **The ultrametric bound** (§0.1.2): a null family sums to something no larger than its largest
term. Mathlib has the summability (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`)
but not the bound. -/
theorem norm_tsum_le_iSup {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) :
    ‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖ :=
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
