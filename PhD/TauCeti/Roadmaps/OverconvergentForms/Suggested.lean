import Mathlib

/-!
# Overconvergent automorphic forms: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures that
can already be stated against the pinned Mathlib API. It is not an exhaustive list of the results in
any layer, and where the roadmap and this file disagree the roadmap wins.

The point of the file is to pin the design decisions that are easy to get wrong and expensive to
undo: the coefficient module is abstract and the wild level is a submonoid (README convention 1);
actions are right actions, implemented as `MulOpposite` actions (convention 2); a weight is a
character with its expansion data, and the wild level `(Σ, ρ)` is part of the weight
(conventions 3–4); the weight action is defined by its kernel and normalised as Buzzard's
`n(cz + d) v(det γ)` (convention 5); neat levels are a hypothesis on the representatives and
property (Pr) is the general case (convention 6); Hecke operators are computed from certificates
(convention 7); and nothing uses Jacquet–Langlands (convention 8).

The first section restates, with the same names, the signatures of the
`p`-adic-functional-analysis and compact-operators roadmaps' `Suggested.lean` files that everything
below is built on; the development imports those roadmaps' versions instead of redefining them.
The adelic objects of Layer 0 are stated for a division algebra `D` over a number field `F` with
Mathlib's `FiniteAdeleRing`, as the FLT project states them.
-/

namespace TauCetiRoadmap.OverconvergentForms

open Filter Topology IsDedekindDomain
open scoped ZeroAtInfty Classical Polynomial TensorProduct

noncomputable section

/-! ## Prerequisites restated from the two analytic roadmaps -/

section Prerequisites

variable {R : Type*} [NormedRing R]
variable {I J : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J]

/-- The coordinate vector of the model space (the `p`-adic-functional-analysis roadmap's §2.1.2). -/
def single [DecidableEq J] (j : J) (r : R) : C₀(J, R) :=
  ⟨⟨Pi.single j r, continuous_of_discreteTopology⟩, sorry⟩

/-- The matrix of an operator between model spaces, rows as coordinates (that roadmap's
convention 7). -/
def matrixCoeff [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) : R :=
  u (single j 1) i

/-- The row supremum and the compactoid predicate (the compact-operators roadmap's §0.2.1). -/
def rowNorm [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) : ℝ :=
  ⨆ j, ‖matrixCoeff u i j‖

/-- **Compactoid**: the rows tend to `0` cofinitely (that roadmap's convention 1). -/
def IsCompactoid [DecidableEq J] (u : C₀(J, R) →L[R] C₀(I, R)) : Prop :=
  Tendsto (rowNorm u) cofinite (𝓝 0)

/-- The scalar action of a normed ring on its model space (that roadmap's §2.1.1). -/
instance instContinuousConstSMul : ContinuousConstSMul R C₀(I, R) := sorry

instance instSMulCommClass : SMulCommClass R R C₀(I, R) := sorry

/-- The Fredholm determinant `det(1 − Tu)` of a compactoid operator (the compact-operators
roadmap's §1.2.2), restated here as an opaque constant of the right type. -/
def charPowerSeries [DecidableEq I] (u : C₀(I, R) →L[R] C₀(I, R)) : PowerSeries R := sorry

/-- The block operator on `C₀(σ × I, R)` assembled from a `σ × σ` matrix of operators (the
compact-operators roadmap's §0.2.6). -/
def blockOp {σ : Type*} [Fintype σ] [DecidableEq σ] [TopologicalSpace σ] [DiscreteTopology σ]
    [DecidableEq I] (T : σ → σ → (C₀(I, R) →L[R] C₀(I, R))) :
    C₀(σ × I, R) →L[R] C₀(σ × I, R) := sorry

end Prerequisites

/-! ## Layer 0: the adelic setting -/

section Adelic

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D]

/-- The adelic group `D_f^× = (D ⊗_F 𝔸_F^f)^×` (§0.2.1), as the FLT project defines it. -/
abbrev Dfx : Type _ := (D ⊗[F] FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ

/-- The inclusion `D^× → D_f^×` and its image `Γ = D^×` (§0.2.1). -/
def unitsIncl : Dˣ →* Dfx F D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := D)).toMonoidHom

def globalUnits : Subgroup (Dfx F D) := (unitsIncl F D).range

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))

/-- **A rigidification at `v`** (§0.1.3): a chosen `F`-algebra isomorphism
`D ⊗_F F_v ≃ M₂(F_v)`. Carried as data (README convention: `RigidificationAt`). -/
class RigidificationAt : Type _ where
  /-- The isomorphism. -/
  equiv : (D ⊗[F] v.adicCompletion F) ≃ₐ[F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)

/-- The `v`-component of an adelic unit as a matrix over `F_v` (§0.2.2), through the
rigidification; `toMatrix F D v : D_f^× →* M₂(F_v)`. -/
def toMatrix [RigidificationAt F D v] : Dfx F D →* Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  sorry

/-- The class set `D^× \ D_f^× / U` (§0.3.3), Mathlib's double-coset quotient. -/
abbrev classSet (U : Subgroup (Dfx F D)) : Type _ :=
  DoubleCoset.Quotient ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D))
    (U : Set (Dfx F D))

/-- **Fujisaki's lemma** (§0.3.2): the class set of an open subgroup is finite, for any
finite-dimensional division algebra over a number field. The FLT project's
`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`. -/
theorem finite_classSet [IsDomain D] [FiniteDimensional F D] [TopologicalSpace (Dfx F D)]
    {U : Subgroup (Dfx F D)} (hU : IsOpen (U : Set (Dfx F D))) : Finite (classSet F D U) :=
  sorry

/-- The wild-level monoid `Δ = θ_v⁻¹(Σ)` for a submonoid `Σ` of `M₂(F_v)` (§0.4.3), and the
statement that `(Δ, U)` is a Hecke triple in Mathlib's sense for every compact open `U ⊆ Δ`
(§0.4.5). -/
def levelMonoid [RigidificationAt F D v]
    (S : Submonoid (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) : Submonoid (Dfx F D) :=
  S.comap (toMatrix F D v)

theorem isHeckeTriple_levelMonoid [RigidificationAt F D v] [TopologicalSpace (Dfx F D)]
    [IsTopologicalGroup (Dfx F D)]
    (S : Submonoid (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v S) (hUc : IsCompact (U : Set (Dfx F D)))
    (hUo : IsOpen (U : Set (Dfx F D))) :
    IsHeckeTriple (levelMonoid F D v S) U U :=
  sorry

end Adelic

/-! ## Layer 1: weights and weight modules -/

section Weights

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The level monoid in norm form (§1.1.1): integral entries, `‖c‖ ≤ ρ`, `‖d‖ = 1`, nonzero
determinant — Buzzard's `M_t` at `ρ = ‖ϖ‖^t`. -/
def SigmaNorm (ρ : ℝ) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0}
  one_mem' := sorry
  mul_mem' := sorry

/-- **The determinant bound** (§1.1.2): on the level, `‖det γ‖ ≤ σ` forces `‖a‖ ≤ σ` — the only
property of the `U_𝔭`-cosets that compactness uses. -/
theorem norm_apply_zero_zero_le_of_norm_det_le {ρ σ : ℝ} (hρσ : ρ ≤ σ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ SigmaNorm (K := K) ρ) (hdet : ‖g.det‖ ≤ σ) :
    ‖g 0 0‖ ≤ σ :=
  sorry

/-- Evaluation of a restricted series at a point of the closed unit disc (the
`p`-adic-functional-analysis roadmap's §4.1.3). -/
def evalAt (f : PowerSeries K) (z : K) : K := ∑' n, PowerSeries.coeff n f * z ^ n

/-- **Expansion data** for a character `n` of a subgroup `𝒪` of units, at level `(Σ, ρ)`
(§1.2.2, README convention 3), for `F_𝔭 = ℚ_p`-type coefficients (one variable): for every lower
row `(c, d)` of the level, a series with `‖coeff m‖ ≤ ρ^m` evaluating to `n(cz + d)` on the
integral points. Here `𝒪 : Subring K` plays the role of `𝒪_𝔭`. -/
structure ExpansionData (𝒪 : Subring K) (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ)
    (n : 𝒪ˣ →* Kˣ) where
  /-- The expansion of `n(c·z + d)` at zero. -/
  col : K → K → PowerSeries K
  /-- Row decay at the level. -/
  norm_coeff_le : ∀ {g}, g ∈ S → ∀ m : ℕ, ‖PowerSeries.coeff m (col (g 1 0) (g 1 1))‖ ≤ ρ ^ m
  /-- Restricted at radius `ρ⁻¹`. -/
  tendsto : ∀ {g}, g ∈ S →
    Tendsto (fun m : ℕ ↦ ‖PowerSeries.coeff m (col (g 1 0) (g 1 1))‖ * ρ⁻¹ ^ m) atTop (𝓝 0)
  /-- The level's values `cz + d` at integral points are units of `𝒪`. -/
  mem : ∀ {g}, g ∈ S → ∀ z ∈ 𝒪, ∃ u : 𝒪ˣ, (u : K) = g 1 0 * z + g 1 1
  /-- The expansion evaluates to the character. -/
  eval : ∀ {g} (hg : g ∈ S) (z : K) (hz : z ∈ 𝒪) (u : 𝒪ˣ) (hu : (u : K) = g 1 0 * z + g 1 1),
    evalAt (col (g 1 0) (g 1 1)) z = (n u : K)

/-- **An analytic weight** at level `(Σ, ρ)` (§1.2.2): Buzzard's `κ = (n, v)` with the expansion
datum of `n` made explicit. -/
structure AnalyticWeight (𝒪 : Subring K) (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ) where
  /-- The character `n`. -/
  n : 𝒪ˣ →* Kˣ
  /-- The character `v`, entering through `v(det γ)`. -/
  v : 𝒪ˣ →* Kˣ
  /-- The expansion datum of `n`. -/
  expansion : ExpansionData 𝒪 S ρ n

variable {𝒪 : Subring K} {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}

/-- **The weight action** `f ∣_κ γ` on the Tate algebra `c₀(ℕ, K)` (§1.2.5): the operator presented
by the kernel `j_κ(γ)(x) · (1 − w_γ(x) y)⁻¹` (README convention 5). -/
def kappaSlash (κ : AnalyticWeight 𝒪 S ρ) (γ : S) : C₀(ℕ, K) →L[K] C₀(ℕ, K) := sorry

/-- The action laws (§1.2.6): a right action of the level monoid, the cocycle being derived from
multiplicativity and the identity theorem. -/
theorem kappaSlash_one (κ : AnalyticWeight 𝒪 S ρ) : kappaSlash κ 1 = ContinuousLinearMap.id K _ :=
  sorry

theorem kappaSlash_mul (κ : AnalyticWeight 𝒪 S ρ) (γ δ : S) :
    kappaSlash κ (δ * γ) = (kappaSlash κ γ).comp (kappaSlash κ δ) :=
  sorry

/-- **The row bound** (§1.2.4): `‖a‖ ≤ σ` and `ρ ≤ σ` give row decay `σ^m` of the matrix of the
action. -/
theorem norm_matrixCoeff_kappaSlash_le (κ : AnalyticWeight 𝒪 S ρ) (γ : S) {σ : ℝ}
    (hρσ : ρ ≤ σ) (ha : ‖(γ : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≤ σ) (m r : ℕ) :
    ‖matrixCoeff (kappaSlash κ γ) m r‖ ≤ σ ^ m :=
  sorry

/-- **Uniqueness of the expansion on the level** (§1.2.3): the action depends only on the
characters. -/
theorem kappaSlash_eq_of_n_eq (κ κ' : AnalyticWeight 𝒪 S ρ) (hn : κ.n = κ'.n) (hv : κ.v = κ'.v)
    (γ : S) : kappaSlash κ γ = kappaSlash κ' γ :=
  sorry

/-- The classical weight module `L_n` as the polynomials of degree at most `n` in the Tate algebra
(§1.3.2–3): stable under the weight action of the algebraic weight `u ↦ u ^ n`. -/
def polySubmodule (n : ℕ) : Submodule K C₀(ℕ, K) :=
  Submodule.span K (Set.range fun m : Fin (n + 1) ↦ single (m : ℕ) (1 : K))

theorem polySubmodule_finrank (n : ℕ) : Module.finrank K (polySubmodule (K := K) n) = n + 1 :=
  sorry

end Weights

/-! ## Layer 2: automorphic functions and the spaces of forms -/

section Forms

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] (Γ : Subgroup G) (Δ : Submonoid G)
variable (A : Type*) [NormedAddCommGroup A] [NormedSpace K A] [DistribMulAction Δᵐᵒᵖ A]
  [SMulCommClass K Δᵐᵒᵖ A]

omit Δ in
/-- **Automorphic functions** (§2.1.1): functions `G → A` invariant under left translation by
`Γ`. -/
def AutomorphicFunction : Submodule K (G → A) where
  carrier := {φ | ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- The right slash `(φ ∣ δ)(g) = φ(g δ⁻¹) ∣ δ` (§2.1.1; README convention 2), as a
`MulOpposite` action. -/
def slash (φ : AutomorphicFunction K Γ A) (δ : Δ) : AutomorphicFunction K Γ A :=
  ⟨fun g ↦ MulOpposite.op δ • (φ : G → A) (g * (δ : G)⁻¹), sorry⟩

/-- **The level space** `L(U, A)` (§2.1.2): the functions fixed by every `u ∈ U`. -/
def Level (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) : Submodule K (AutomorphicFunction K Γ A) where
  carrier := {φ | ∀ u : U, slash K Γ Δ A φ ⟨u, hU u.2⟩ = φ}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- **The decomposition over the class set** (§2.2.1): evaluation at a section of `Γ \ G / U` is a
bijection onto the product of the invariants under the stabilisers. Stated as injectivity plus
the description of the image. -/
theorem eval_injective (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) {ι : Type*} (c : ι → G)
    (hc : Function.Surjective fun i ↦
      (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))) :
    Function.Injective fun φ : Level K Γ Δ A U hU ↦ fun i ↦ ((φ : AutomorphicFunction K Γ A) : G → A) (c i) :=
  sorry

/-- **The block model at a neat level** (§2.5.1): for `A = c₀(ℕ, K)` and a section whose
stabilisers act trivially, evaluation is a bijection onto `c₀(ι × ℕ, K)`. -/
theorem bijective_evalAtReps (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) {ι : Type*} [Fintype ι]
    [DistribMulAction Δᵐᵒᵖ C₀(ℕ, K)] [SMulCommClass K Δᵐᵒᵖ C₀(ℕ, K)] (c : ι → G)
    (hc : Function.Bijective fun i ↦
      (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)))
    (hstab : ∀ i (w : U), (c i) * w * (c i)⁻¹ ∈ Γ →
      ∀ a : C₀(ℕ, K), MulOpposite.op (⟨(w : G), hU w.2⟩ : Δ) • a = a) :
    Function.Bijective fun φ : Level K Γ Δ C₀(ℕ, K) U hU ↦
      (fun p : ι × ℕ ↦ ((φ : AutomorphicFunction K Γ C₀(ℕ, K)) : G → C₀(ℕ, K)) (c p.1) p.2) :=
  sorry

end Forms

/-! ## Layer 3: Hecke operators -/

section Hecke

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] (Γ : Subgroup G) (Δ : Submonoid G)
variable (A : Type*) [NormedAddCommGroup A] [NormedSpace K A] [DistribMulAction Δᵐᵒᵖ A]
  [SMulCommClass K Δᵐᵒᵖ A]

/-- **The double-coset operator** `[UηU] φ = ∑_t φ ∣ x_t` (§3.1.1), from a finite family of
right-coset representatives of `U η U`. -/
def heckeOperator (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) {T : Type*} [Fintype T] (x : T → G)
    (hx : ∀ t, x t ∈ Δ) : Level K Γ Δ A U hU →ₗ[K] Level K Γ Δ A U hU :=
  sorry

/-- **The matrix recipe** (§3.2.2; Jacobs pp. 20–21): with a certificate
`c_i · x_t⁻¹ = d(i,t) · c_{σ(i,t)} · u(i,t)`, the value of `[UηU] φ` at `c_i` is the sum of the
values of `φ` at `c_{σ(i,t)}` slashed by `u(i,t) x_t`. -/
theorem heckeOperator_apply_rep (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) {T : Type*} [Fintype T]
    (x : T → G) (hx : ∀ t, x t ∈ Δ) {ι : Type*} (c : ι → G) (σ : ι → T → ι) (d : ι → T → Γ)
    (u : ι → T → U) (hcert : ∀ i t, c i * (x t)⁻¹ = (d i t : G) * c (σ i t) * (u i t : G))
    (φ : Level K Γ Δ A U hU) (i : ι) :
    ((heckeOperator K Γ Δ A U hU x hx φ : AutomorphicFunction K Γ A) : G → A) (c i) =
      ∑ t, MulOpposite.op (⟨(u i t : G) * x t, mul_mem (hU (u i t).2) (hx t)⟩ : Δ) •
        ((φ : AutomorphicFunction K Γ A) : G → A) (c (σ i t)) :=
  sorry

end Hecke

/-! ## Layers 3–4 on the block model: compactness and the determinant -/

section Compact

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {𝒪 : Subring K} {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}
variable {ι T : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [Fintype T]

/-- The certificate blocks `ε_{ij} = ∑_{t : σ(i,t) = j} (· ∣ γ(i,t))` (§3.2.3), with `γ(i, t)` the
`𝔭`-component of `u(i,t) x_t` in the level monoid. -/
def heckeBlock (κ : AnalyticWeight 𝒪 S ρ) (γ : ι → T → S) (σ : ι → T → ι) (i j : ι) :
    C₀(ℕ, K) →L[K] C₀(ℕ, K) :=
  ∑ t ∈ Finset.univ.filter (fun t ↦ σ i t = j), kappaSlash κ (γ i t)

/-- **`U_𝔭` is compact** (§3.5.2; Buzzard, Lemma 12.2; Jacobs, Lemma 2.7): when every certificate
element has `‖det‖ ≤ σ` with `ρ ≤ σ < 1`, the block operator is compactoid. -/
theorem isCompactoid_heckeBlockOp (κ : AnalyticWeight 𝒪 S ρ) (γ : ι → T → S) (σ : ι → T → ι)
    {s : ℝ} (hρσ : ρ ≤ s) (hs : s < 1)
    (hdet : ∀ i t, ‖((γ i t : S) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ s) :
    IsCompactoid (blockOp (heckeBlock κ γ σ)) :=
  sorry

/-- **The Fredholm determinant of `U_𝔭`** at a neat level (§4.1.1): the determinant of the block
operator of a certificate. -/
def heckeCharPowerSeries (κ : AnalyticWeight 𝒪 S ρ) (γ : ι → T → S) (σ : ι → T → ι) :
    PowerSeries K :=
  charPowerSeries (blockOp (heckeBlock κ γ σ))

/-- **The slope bound** (§4.4.1): with `ρ ≤ ‖ϖ‖` and `‖det‖ = ‖ϖ‖` on the certificate, the `n`-th
coefficient of `det(1 − T·U_𝔭)` has norm at most `‖ϖ‖ ^ (∑_{k<n} ⌊k / |ι|⌋)`. -/
theorem norm_coeff_heckeCharPowerSeries_le (κ : AnalyticWeight 𝒪 S ρ) (γ : ι → T → S)
    (σ : ι → T → ι) {ϖ : K} (hϖ : ‖ϖ‖ < 1) (hρ : ρ ≤ ‖ϖ‖)
    (hdet : ∀ i t, ‖((γ i t : S) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ ‖ϖ‖) (n : ℕ) :
    ‖PowerSeries.coeff n (heckeCharPowerSeries κ γ σ)‖ ≤
      ‖ϖ‖ ^ (∑ k ∈ Finset.range n, k / Fintype.card ι) :=
  sorry

end Compact

/-! ## Layer 5: the theta operator -/

section Theta

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The theta operator** `θ^r = (d/dz)^r` on the Tate algebra (§5.1.1): `z^m ↦ (m)_r z^{m−r}`. -/
def theta (r : ℕ) : C₀(ℕ, K) →L[K] C₀(ℕ, K) := sorry

theorem theta_apply_single (r m : ℕ) :
    theta (K := K) r (single m 1) = single (m - r) ((Nat.descFactorial m r : ℕ) : K) :=
  sorry

/-- `ker θ^{k+1}` is the space of polynomials of degree at most `k` (§5.1.2; Buzzard 2004,
Proposition 4). -/
theorem ker_theta_succ (k : ℕ) :
    LinearMap.ker ((theta (K := K) (k + 1) : C₀(ℕ, K) →L[K] C₀(ℕ, K)) : C₀(ℕ, K) →ₗ[K] C₀(ℕ, K))
      = polySubmodule k :=
  sorry

/-- **Bol's identity** in subtraction-free column form (§5.2.1; Bol 1949; Buzzard 2004, §7):
for `N = a z + b`, `L = c z + d` with `d ≠ 0` and `D = det γ`,
`∂^r (N^{j+r} L^{−(j+1)}) = D^r (j+r)_r N^j L^{−(j+r+1)}`. -/
theorem bol (a b c d : K) (hd : d ≠ 0) (r j : ℕ) :
    let N : PowerSeries K := PowerSeries.C b + PowerSeries.C a * PowerSeries.X
    let L : PowerSeries K := PowerSeries.C d + PowerSeries.C c * PowerSeries.X
    (PowerSeries.derivative K)^[r] (N ^ (j + r) * L⁻¹ ^ (j + 1)) =
      PowerSeries.C (a * d - b * c) ^ r * ((Nat.descFactorial (j + r) r : ℕ) : PowerSeries K)
        * N ^ j * L⁻¹ ^ (j + r + 1) :=
  sorry

/-- **The small-slope lemma** (§5.4.1): an operator of norm at most `1` intertwined with another
up to a scalar `c` kills every eigenvector whose eigenvalue has norm larger than `‖c‖`. The abstract
form of "eigenforms of slope less than `k + 1` are classical". -/
theorem eq_zero_of_intertwine_of_norm_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {P P' θ : E →L[K] E} (hP' : ‖P'‖ ≤ 1) {c : K} (hint : θ.comp P = c • P'.comp θ) {f : E} {μ : K}
    (hf : P f = μ • f) (hμ : ‖c‖ < ‖μ‖) : θ f = 0 :=
  sorry

end Theta

end

end TauCetiRoadmap.OverconvergentForms
