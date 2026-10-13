import Mathlib

/-!
# Rigid analytic geometry: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures that
can already be stated against the pinned Mathlib API. It is not an exhaustive list of the results in
any layer, and where the roadmap and this file disagree the roadmap wins.

The point of the file is to pin the design decisions that are easy to get wrong and expensive to
undo: the Tate algebra is Mathlib's subring of restricted power series at the unit polyradius
(README convention 2); an affinoid algebra is a `Prop` on a `K`-algebra and carries no topology
(convention 3); points are maximal ideals and `|f(x)|` is the spectral norm on the residue field
(convention 4); the supremum seminorm is an `iSup` over the maximal spectrum (convention 5); an
affinoid subdomain is the data of its representing algebra with the universal property, and the
special subdomains have explicit quotient presentations (convention 6); a G-topology is a site on
a poset of subsets and sheaves are Mathlib's (convention 8); rigid varieties are locally G-ringed
spaces (convention 9); and the comparison with adic spaces goes through the classical points
(convention 12).
-/

universe u

namespace TauCetiRoadmap.RigidAnalyticGeometry

open scoped NNReal Topology
open CategoryTheory

noncomputable section

/-! ## Layer 0: the Tate algebra -/

section TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The Tate algebra `Tₙ = K⟨X₁, …, Xₙ⟩`: Mathlib's subring of restricted power series at the unit
polyradius, as a `K`-subalgebra of `MvPowerSeries (Fin n) K` (README convention 2). In code the
Tate algebra is the type of mathlib4#42867, `MvPowerSeries.Restricted K (1 : Fin n → ℝ)`, under the
name `Affinoid.TateAlgebra K n`; that type is not in the pinned Mathlib, so this file states the
targets on the subalgebra. -/
def TateAlgebra (n : ℕ) : Subalgebra K (MvPowerSeries (Fin n) K) where
  __ := MvPowerSeries.IsRestricted.subring (fun _ : Fin n ↦ (1 : ℝ))
  algebraMap_mem' a := by
    rw [MvPowerSeries.algebraMap_apply]
    exact MvPowerSeries.isRestricted_C (fun _ : Fin n ↦ (1 : ℝ)) (algebraMap K K a)

/-- The Gauss norm `|f| = max_ν |a_ν|` on `Tₙ`, read off Mathlib's `MvPowerSeries.gaussNorm`
(§0.1.1). -/
def gaussNorm {n : ℕ} (f : TateAlgebra K n) : ℝ :=
  MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K)

set_option warn.classDefReducibility false in
/-- The Gauss norm makes `Tₙ` a Banach `K`-algebra with multiplicative norm (§0.1.1). The
`NormedCommRing` structure is a target; Mathlib has only the bare function. Deliberately not an
instance: a `sorry`-backed instance would enter typeclass search for the rest of the file. -/
def tateAlgebraNormedCommRing (n : ℕ) : NormedCommRing (TateAlgebra K n) :=
  sorry

/-- The Gauss norm is multiplicative (§0.1.1; Mathlib's `gaussNorm_mul_eq_mul` once a dominant
pair of indices is produced). -/
theorem gaussNorm_mul {n : ℕ} (f g : TateAlgebra K n) :
    gaussNorm K (f * g) = gaussNorm K f * gaussNorm K g :=
  sorry

/-- `Tₙ` is noetherian (BGR 5.2.6/1; §0.3.2): proved in Layer 0 through Rückert's theory, together
with factoriality, the Jacobson property and the dimension. Stated as a theorem rather than an
instance so that a `sorry`-backed instance is not in typeclass search. -/
theorem isNoetherianRing_tateAlgebra (n : ℕ) : IsNoetherianRing (TateAlgebra K n) :=
  sorry

/-- `Tₙ` is a Jacobson ring (BGR 5.2.6/3; §0.3.3): the algebraic form of the Nullstellensatz. -/
theorem isJacobsonRing_tateAlgebra (n : ℕ) : IsJacobsonRing (TateAlgebra K n) :=
  sorry

/-- **Distinguished charts** (BGR 5.2.4; Bosch 1.2/7; §0.2.3): a nonzero series becomes
`Xₙ`-distinguished after the automorphism `Xᵢ ↦ Xᵢ + Xₙ^{αᵢ}` (in code the distinguished variable
is `X 0`, README convention 2). Stated here only through the
existence of the automorphism; distinguishedness is the one-variable
`TauCeti.PowerSeries.IsDistinguished` over `T_{n−1}` read along `finSuccEquiv`. -/
theorem exists_algEquiv_isDistinguished {n : ℕ} (f : TateAlgebra K (n + 1)) (hf : f ≠ 0) :
    ∃ σ : TateAlgebra K (n + 1) ≃ₐ[K] TateAlgebra K (n + 1), ∃ s : ℕ,
      -- the image `σ f` is `X_n`-distinguished of order `s`: its coefficient of `X_n ^ s` as a
      -- series in `T_n` is a unit of Gauss norm `gaussNorm (σ f)`, and every later coefficient is
      -- strictly smaller
      True ∧ s = s ∧ σ f ≠ 0 :=
  sorry

end TateAlgebra

/-! ## Layer 1: affinoid algebras -/

section Affinoid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An affinoid `K`-algebra (BGR 6.1.1/1; README convention 3): a `K`-algebra admitting a
surjective `K`-algebra map from some Tate algebra. A `Prop`, carrying no topology: the affinoid
topology is a theorem (§1.3), as is the continuity of every homomorphism. -/
class IsAffinoidAlgebra (A : Type u) [CommRing A] [Algebra K A] : Prop where
  exists_surjective : ∃ (n : ℕ) (φ : TateAlgebra K n →ₐ[K] A), Function.Surjective φ

variable {K}

namespace IsAffinoidAlgebra

variable {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]

/-- Affinoid algebras are noetherian (§1.1.2). -/
theorem isNoetherianRing : IsNoetherianRing A :=
  sorry

/-- Affinoid algebras are Jacobson (§1.1.2). -/
theorem isJacobsonRing : IsJacobsonRing A :=
  sorry

/-- **Residue fields are finite over `K`** (BGR 6.1.2/3; §1.2.4). ⚠ Mathlib's
`finite_of_finite_type_of_isJacobsonRing` needs a finitely generated algebra and does not apply. -/
theorem finite_quotient_of_isMaximal (m : Ideal A) [m.IsMaximal] : Module.Finite K (A ⧸ m) :=
  sorry

/-- **Noether normalisation** (BGR 6.1.2/2; §1.2.1): a nonzero affinoid algebra is a finite
extension of some `T_d`. -/
theorem exists_finite_injective [Nontrivial A] :
    ∃ (d : ℕ) (φ : TateAlgebra K d →ₐ[K] A), Function.Injective φ ∧ φ.toRingHom.Finite :=
  sorry

/-- Quotients of affinoid algebras are affinoid (BGR 6.1.1/3; §1.1.2). -/
theorem quotient (I : Ideal A) : IsAffinoidAlgebra K (A ⧸ I) :=
  sorry

end IsAffinoidAlgebra

/-- **Continuity of homomorphisms** (BGR 6.1.3/1; §1.3.2): every `K`-algebra homomorphism between
affinoid algebras is continuous for any complete `K`-algebra norms. The norms are arbitrary, which
is what convention 3 buys. -/
theorem continuous_algHom {A B : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsAffinoidAlgebra K A] [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsAffinoidAlgebra K B] (φ : B →ₐ[K] A) : Continuous φ :=
  sorry

/-- **Uniqueness of the Banach topology** (BGR 6.1.3/2; §1.3.3), in the form "any two complete
`K`-algebra norms on an affinoid algebra are equivalent", stated through a `K`-algebra
isomorphism of two complete normed affinoid algebras being a homeomorphism. -/
theorem continuous_algEquiv_symm {A B : Type u} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsAffinoidAlgebra K A] [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsAffinoidAlgebra K B] (e : A ≃ₐ[K] B) :
    Continuous e ∧ Continuous e.symm :=
  sorry

/-- `A⟨X₁, …, Xₘ⟩` for a nonarchimedean normed commutative ring `A` (§1.1.3): Mathlib's restricted
series over `A` at the unit polyradius. For affinoid `A` with a residue norm this is again
affinoid, and the result is independent of the residue norm by §1.3.3. -/
abbrev RestrictedAlgebra (A : Type u) [NormedCommRing A] [IsUltrametricDist A] (m : ℕ) :
    Subring (MvPowerSeries (Fin m) A) :=
  MvPowerSeries.IsRestricted.subring (fun _ : Fin m ↦ (1 : ℝ))

/-- The relation `g Xᵢ − fᵢ` of a rational localisation, as an element of `A⟨X₁, …, Xₘ⟩`. -/
def rationalRelation {A : Type u} [NormedCommRing A] [IsUltrametricDist A] {m : ℕ}
    (f : Fin m → A) (g : A) (i : Fin m) : RestrictedAlgebra A m :=
  ⟨MvPowerSeries.monomial (Finsupp.single i 1) g - MvPowerSeries.C (f i),
    sub_mem (MvPowerSeries.isRestricted_monomial _ _ _) (MvPowerSeries.isRestricted_C _ _)⟩

/-- The coordinate ring `A⟨f/g⟩ = A⟨X₁, …, Xₘ⟩ ⧸ (g Xᵢ − fᵢ)` of the rational domain `X(f/g)`
(BGR 6.1.4/4; README convention 6). ⚠ This is the *same ring* as the adic-spaces roadmap's
`A⟨T/s⟩` for `T = {f₁, …, fₘ, g}`, `s = g`, through Tau Ceti's `rationalQuotientRingEquiv`; the
identification is §1.4.3, not a second construction. -/
abbrev RationalLocalization {A : Type u} [NormedCommRing A] [IsUltrametricDist A] {m : ℕ}
    (f : Fin m → A) (g : A) : Type u :=
  RestrictedAlgebra A m ⧸ Ideal.span (Set.range (rationalRelation f g))

/-- The structure map `A → A⟨f/g⟩`. -/
def toRationalLocalization {A : Type u} [NormedCommRing A] [IsUltrametricDist A] {m : ℕ}
    (f : Fin m → A) (g : A) : A →+* RationalLocalization f g :=
  (Ideal.Quotient.mk _).comp
    ((MvPowerSeries.C (σ := Fin m) (R := A)).codRestrict (RestrictedAlgebra A m)
      fun a ↦ MvPowerSeries.isRestricted_C _ a)

/-- `g` becomes a unit in `A⟨f/g⟩` (BGR 6.1.4/3; §1.4.2). -/
theorem isUnit_toRationalLocalization {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
    {m : ℕ} (f : Fin m → A) (g : A) : IsUnit (toRationalLocalization f g g) :=
  sorry

end Affinoid

/-! ## Layer 2: the supremum seminorm -/

section SupSeminorm

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- `|f(x)|` for a point `x ∈ Sp A = MaximalSpectrum A` (README convention 4): the spectral norm of
the residue class of `f` in the residue field `A ⧸ x`, written as the spectral value of its minimal
polynomial so that no field instance on the quotient has to be chosen. For affinoid `A` the residue
field is a finite extension of `K` (§1.2.4) and this is Mathlib's `spectralNorm K (A ⧸ x)`. -/
def evalNorm (x : MaximalSpectrum A) (f : A) : ℝ :=
  spectralValue (minpoly K (Ideal.Quotient.mk x.asIdeal f))

/-- The supremum seminorm (BGR 6.2.1/2; README convention 5): an `iSup` over the maximal spectrum,
`0` on the zero algebra. -/
def supSeminorm (f : A) : ℝ :=
  ⨆ x : MaximalSpectrum A, evalNorm K x f

variable [IsAffinoidAlgebra K A]

/-- `|f(x)| = 0` exactly when `f ∈ x` (§3.1.1). -/
theorem evalNorm_eq_zero_iff (x : MaximalSpectrum A) (f : A) :
    evalNorm K x f = 0 ↔ f ∈ x.asIdeal :=
  sorry

/-- The supremum seminorm is power-multiplicative (BGR 6.2.1/1; §2.1.1). -/
theorem supSeminorm_pow (f : A) (n : ℕ) : supSeminorm K (f ^ n) = supSeminorm K f ^ n :=
  sorry

/-- **Maximum modulus** (BGR 6.2.1/4(i); Bosch 1.4/14; §2.2.1): the supremum is attained. -/
theorem exists_evalNorm_eq_supSeminorm [Nontrivial A] (f : A) :
    ∃ x : MaximalSpectrum A, evalNorm K x f = supSeminorm K f :=
  sorry

/-- The value group (BGR 6.2.1/4(ii); §2.2.2): `|c fᵐ|_sup = 1` for some `c ∈ K`, `m ≥ 1`. -/
theorem exists_supSeminorm_smul_pow_eq_one (f : A) (hf : supSeminorm K f ≠ 0) :
    ∃ (c : K) (m : ℕ), 0 < m ∧ supSeminorm K (c • f ^ m) = 1 :=
  sorry

/-- Nilpotents are the elements of supremum seminorm zero (BGR 6.2.1/4(iii); §2.2.4). -/
theorem supSeminorm_eq_zero_iff (f : A) : supSeminorm K f = 0 ↔ IsNilpotent f :=
  sorry

/-- The supremum seminorm is the Gauss norm on `Tₙ` (BGR 5.1.4/6 with 6.2.1; §0.1.4). -/
theorem supSeminorm_tateAlgebra {n : ℕ} (f : TateAlgebra K n) :
    supSeminorm K f = gaussNorm K f :=
  sorry

end SupSeminorm

section PowerBounded

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsAffinoidAlgebra K A]

/-- **Power-bounded elements** (BGR 6.2.3/1; Bosch 1.4/16; §2.3.1), for any complete `K`-algebra
norm on `A`: power-bounded iff `|f|_sup ≤ 1`. Power-boundedness is Mathlib's `Bornology.IsBounded`
of the set of powers, as in mathlib4#40013. -/
theorem isBounded_range_pow_iff (f : A) :
    Bornology.IsBounded (Set.range fun k : ℕ ↦ f ^ k) ↔ supSeminorm K f ≤ 1 :=
  sorry

/-- **Topologically nilpotent elements** (BGR 6.2.3/2; Bosch 1.4/17; §2.3.2). -/
theorem isTopologicallyNilpotent_iff (f : A) :
    IsTopologicallyNilpotent f ↔ supSeminorm K f < 1 :=
  sorry

/-- **The spectral-radius formula** (BGR 6.2.3/3; §2.3.3): `|f|_sup = inf ‖fⁱ‖^{1/i}`, which
identifies the supremum seminorm with Mathlib's `smoothingSeminorm` of the norm. -/
theorem supSeminorm_eq_iInf (f : A) :
    supSeminorm K f = ⨅ i : ℕ+, ‖f ^ (i : ℕ)‖ ^ (1 / (i : ℝ)) :=
  sorry

/-- **Reduced affinoid algebras are Banach function algebras** (BGR 6.2.4/1; §2.4.1): the
supremum seminorm of a reduced affinoid algebra is a norm equivalent to any complete `K`-algebra
norm. The inequality `|f|_sup ≤ ‖f‖` holds always (BGR 3.8.2/2); the content is the constant. -/
theorem exists_norm_le_mul_supSeminorm [IsReduced A] :
    ∃ C : ℝ, ∀ f : A, ‖f‖ ≤ C * supSeminorm K f :=
  sorry

end PowerBounded

/-! ## Layers 3–4: affinoid varieties and affinoid subdomains -/

section Varieties

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]

/-- The map on maximal spectra induced by a `K`-algebra homomorphism of affinoid algebras
(BGR 7.1.4; §3.3.1): the preimage of a maximal ideal is maximal because residue fields are finite
over `K` (§1.2.4). -/
def spComap {B : Type u} [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B] (σ : B →ₐ[K] A) :
    MaximalSpectrum A → MaximalSpectrum B :=
  sorry

/-- `|g(Sp σ x)| = |σ g (x)|` (Bosch 1.5/6; §3.3.1). -/
theorem evalNorm_spComap {B : Type u} [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    (σ : B →ₐ[K] A) (x : MaximalSpectrum A) (g : B) :
    evalNorm K (spComap K σ x) g = evalNorm K x (σ g) :=
  sorry

/-- **The Nullstellensatz** (BGR 7.1.2/5; Bosch 1.5/6; §3.2.2), in the form used by every rational
domain: functions without a common zero generate the unit ideal. -/
theorem span_eq_top_of_forall_exists_evalNorm_ne_zero (s : Set A)
    (h : ∀ x : MaximalSpectrum A, ∃ f ∈ s, evalNorm K x f ≠ 0) : Ideal.span s = ⊤ :=
  sorry

/-- The Weierstrass domain `X(f₁, …, fₘ) = {x : |fᵢ(x)| ≤ 1}` (BGR 7.2.3; §4.2.1). -/
def weierstrassDomain {m : ℕ} (f : Fin m → A) : Set (MaximalSpectrum A) :=
  {x | ∀ i, evalNorm K x (f i) ≤ 1}

/-- The Laurent domain `X(f, g⁻¹) = {x : |fᵢ(x)| ≤ 1, |gⱼ(x)| ≥ 1}` (BGR 7.2.3; §4.2.1). -/
def laurentDomain {m r : ℕ} (f : Fin m → A) (g : Fin r → A) : Set (MaximalSpectrum A) :=
  {x | (∀ i, evalNorm K x (f i) ≤ 1) ∧ ∀ j, 1 ≤ evalNorm K x (g j)}

/-- The rational domain `X(f/g) = {x : |fᵢ(x)| ≤ |g(x)|}` (BGR 7.2.3; §4.2.1), meaningful when
`f₁, …, fₘ, g` have no common zero; the hypothesis is carried by the theorems, not the set. -/
def rationalDomain {m : ℕ} (f : Fin m → A) (g : A) : Set (MaximalSpectrum A) :=
  {x | ∀ i, evalNorm K x (f i) ≤ evalNorm K x g}

/-- **An affinoid subdomain** of `Sp A` (BGR 7.2.2/2; Bosch 1.6/9; README convention 6): the data of
an affinoid algebra `Alg` with a map `ι : A → Alg` whose spectrum lands in `carrier`, such that
every affinoid map into `Sp A` with image in `carrier` factors uniquely through `Sp ι`. The subset
is data here only so that it can be named; it is determined by `ι` (Bosch 1.6/10). -/
structure AffinoidSubdomain : Type (u + 1) where
  /-- The underlying subset of `Sp A`. -/
  carrier : Set (MaximalSpectrum A)
  /-- The representing algebra `𝒪_X(U)`. -/
  Alg : Type u
  [commRing : CommRing Alg]
  [algebra : Algebra K Alg]
  [isAffinoid : IsAffinoidAlgebra K Alg]
  /-- The structure map `A → 𝒪_X(U)`. -/
  ι : A →ₐ[K] Alg
  /-- `Sp ι` lands in the subset. -/
  comap_mem : ∀ y, spComap K ι y ∈ carrier
  /-- The universal property. -/
  universal : ∀ (B : Type u) [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    (φ : A →ₐ[K] B), (∀ y, spComap K φ y ∈ carrier) → ∃! ψ : Alg →ₐ[K] B, ψ.comp ι = φ

attribute [instance] AffinoidSubdomain.commRing AffinoidSubdomain.algebra
  AffinoidSubdomain.isAffinoid

/-- The subset of an affinoid subdomain is the image of `Sp ι` (Bosch 1.6/10; §4.1.1). -/
theorem AffinoidSubdomain.range_spComap (U : AffinoidSubdomain K (A := A)) :
    Set.range (spComap K U.ι) = U.carrier :=
  sorry

/-- **Gerritzen–Grauert** (BGR 7.3.5/3; Bosch 1.6/20; §4.6.3): every affinoid subdomain is a finite
union of rational subdomains. -/
theorem gerritzenGrauert (U : AffinoidSubdomain K (A := A)) :
    ∃ (r : ℕ) (m : Fin r → ℕ) (f : ∀ i, Fin (m i) → A) (g : Fin r → A),
      (∀ i, Ideal.span (insert (g i) (Set.range (f i))) = ⊤) ∧
        U.carrier = ⋃ i, rationalDomain K (f i) (g i) :=
  sorry

/-- **The standard rational covering** (BGR 8.2.2 with 7.1.2/5; §5.2.1 and §8.2.5): the rational
domains `X(g₁/gᵢ, …, gᵣ/gᵢ)` cover `Sp A` exactly when `g₁, …, gᵣ` generate the unit ideal. This is
the rigid half of the covering criterion whose adic half is Wedhorn's Corollary 7.53. -/
theorem iUnion_rationalDomain_eq_univ_iff {r : ℕ} (g : Fin r → A) :
    (⋃ i, rationalDomain K g (g i)) = Set.univ ↔ Ideal.span (Set.range g) = ⊤ :=
  sorry

end Varieties

section RationalSubdomain

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  [IsAffinoidAlgebra K A]

/-- A rational domain is an affinoid subdomain, represented by `A⟨f/g⟩` (BGR 7.2.3 and 6.1.4/4;
§4.2.2). Stated for a residue norm on `A`, which the representing algebra's presentation needs. -/
theorem exists_affinoidSubdomain_rationalDomain {m : ℕ} (f : Fin m → A) (g : A)
    (hfg : Ideal.span (insert g (Set.range f)) = ⊤) :
    ∃ U : AffinoidSubdomain K (A := A), U.carrier = rationalDomain K f g ∧
      Nonempty (U.Alg ≃+* RationalLocalization f g) :=
  sorry

end RationalSubdomain

/-! ## Layer 5: Tate's acyclicity theorem, in its two-piece Laurent form -/

section Tate

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A] [IsAffinoidAlgebra K A]

/-- `A⟨f⟩ = A⟨X⟩ ⧸ (X − f)`, the algebra of the Weierstrass domain `{|f| ≤ 1}` (§4.2.2). -/
abbrev laurentPlus (f : A) : Type u :=
  RationalLocalization (fun _ : Fin 1 ↦ f) 1

/-- `A⟨f⁻¹⟩ = A⟨X⟩ ⧸ (f X − 1)`, the algebra of the Laurent domain `{|f| ≥ 1}` (§4.2.2). -/
abbrev laurentMinus (f : A) : Type u :=
  RationalLocalization (fun _ : Fin 1 ↦ (1 : A)) f

/-- `A⟨f, f⁻¹⟩ = A⟨X, Y⟩ ⧸ (X − f, f Y − 1)`, the algebra of `{|f| = 1}` (§4.2.2). Presented as the
rational localisation at `({f², f, 1}, f)`, which is the adic-spaces roadmap's presentation of the
intersection of the two Laurent pieces. -/
abbrev laurentBoth (f : A) : Type u :=
  RationalLocalization (![f ^ 2, 1] : Fin 2 → A) f

/-- The restriction `A⟨f⟩ → A⟨f, f⁻¹⟩` (§4.1.4): the comparison map of the two presentations,
`X ↦ X` on the first variable. -/
def restrictPlus (f : A) : laurentPlus f →+* laurentBoth f :=
  sorry

/-- The restriction `A⟨f⁻¹⟩ → A⟨f, f⁻¹⟩` (§4.1.4), `X ↦ Y`. -/
def restrictMinus (f : A) : laurentMinus f →+* laurentBoth f :=
  sorry

/-- **Tate's theorem for a two-piece Laurent covering** (BGR 8.2.3; Bosch 1.9, the sequence after
1.9/7; §5.3.1): `0 → A → A⟨f⟩ × A⟨f⁻¹⟩ → A⟨f, f⁻¹⟩ → 0` is exact. This is the adic-spaces roadmap's
Wedhorn 8.33 (`TauCeti.ValuationSpectrum.laurentCover_exact`) transported along the identification
of the coordinate rings, and the only input of Layer 5 taken from the adic side. The affinoid
hypothesis is carried explicitly, since the statement itself does not mention `K`. -/
theorem laurent_exact (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] [IsAffinoidAlgebra K A] (f : A) :
    Function.Injective (fun a : A ↦
        (toRationalLocalization _ _ a, toRationalLocalization _ _ a) :
      A → laurentPlus f × laurentMinus f) ∧
    (∀ (u : laurentPlus f) (v : laurentMinus f), restrictPlus f u = restrictMinus f v →
      ∃ a : A, toRationalLocalization _ _ a = u ∧ toRationalLocalization _ _ a = v) ∧
    Function.Surjective (fun p : laurentPlus f × laurentMinus f ↦
      restrictPlus f p.1 - restrictMinus f p.2) :=
  sorry

end Tate

end

end TauCetiRoadmap.RigidAnalyticGeometry

/-! ## Layer 6: G-topologies and locally G-ringed spaces

`GTopology` is the one declaration this roadmap places in the root namespace (README convention
13): it is reusable topology with no rigid-geometric content. -/

/-- A Grothendieck topology on a set, in Tate's sense (BGR 9.1.1/1; README convention 8): a class
of admissible open subsets closed under binary intersection, and for each admissible open a class
of admissible coverings by admissible opens, stable under restriction and composition and
containing the trivial covering. Coverings are indexed by types in the universe of `X`. -/
structure GTopology (X : Type u) where
  /-- The admissible open subsets. -/
  IsAdmissibleOpen : Set X → Prop
  /-- The admissible coverings of an admissible open: families of subsets indexed by a type. -/
  IsAdmissibleCover : Set X → ∀ {ι : Type u}, (ι → Set X) → Prop
  inter_mem : ∀ {U V}, IsAdmissibleOpen U → IsAdmissibleOpen V → IsAdmissibleOpen (U ∩ V)
  cover_isAdmissibleOpen : ∀ {U : Set X} {ι : Type u} {V : ι → Set X},
    IsAdmissibleCover U V → IsAdmissibleOpen U
  mem_isAdmissibleOpen : ∀ {U : Set X} {ι : Type u} {V : ι → Set X},
    IsAdmissibleCover U V → ∀ i, IsAdmissibleOpen (V i)
  iUnion_eq : ∀ {U : Set X} {ι : Type u} {V : ι → Set X}, IsAdmissibleCover U V → ⋃ i, V i = U
  trivial_cover : ∀ {U}, IsAdmissibleOpen U → IsAdmissibleCover U (fun _ : PUnit ↦ U)
  restrict : ∀ {U W : Set X} {ι : Type u} {V : ι → Set X}, IsAdmissibleCover U V →
    IsAdmissibleOpen W → W ⊆ U → IsAdmissibleCover W (fun i ↦ V i ∩ W)
  trans : ∀ {U : Set X} {ι : Type u} {V : ι → Set X}, IsAdmissibleCover U V →
    ∀ {κ : ι → Type u} {W : ∀ i, κ i → Set X}, (∀ i, IsAdmissibleCover (V i) (W i)) →
      IsAdmissibleCover U (fun p : Σ i, κ i ↦ W p.1 p.2)

namespace GTopology

open CategoryTheory

variable {X : Type u} (𝒯 : GTopology X)

/-- The admissible opens, as a preorder under inclusion; the site's underlying category. -/
def Opens : Type u := {U : Set X // 𝒯.IsAdmissibleOpen U}

instance : Preorder 𝒯.Opens := Subtype.preorder _

/-- The coverage on the admissible opens whose covering families are the admissible coverings
(§6.1.2). -/
def coverage : Coverage 𝒯.Opens :=
  sorry

/-- The Grothendieck topology generated by the admissible coverings. A sheaf on a G-topological
space *is* a sheaf for it (README convention 8). -/
def grothendieckTopology : GrothendieckTopology 𝒯.Opens :=
  𝒯.coverage.toGrothendieck

/-- The completeness condition `(G0)` of BGR 9.1.2. -/
def G0 : Prop := 𝒯.IsAdmissibleOpen ∅ ∧ 𝒯.IsAdmissibleOpen Set.univ

/-- The completeness condition `(G1)` of BGR 9.1.2: a subset of an admissible open that meets every
member of an admissible covering in an admissible open is admissible open. -/
def G1 : Prop := ∀ {U : Set X} {ι : Type u} {V : ι → Set X}, 𝒯.IsAdmissibleCover U V →
  ∀ W ⊆ U, (∀ i, 𝒯.IsAdmissibleOpen (W ∩ V i)) → 𝒯.IsAdmissibleOpen W

/-- The completeness condition `(G2)` of BGR 9.1.2: a covering by admissible opens that has an
admissible refinement is admissible. -/
def G2 : Prop := ∀ {U : Set X} {ι : Type u} {V : ι → Set X}, 𝒯.IsAdmissibleOpen U →
  (∀ i, 𝒯.IsAdmissibleOpen (V i)) → (⋃ i, V i) = U →
  ∀ {κ : Type u} {W : κ → Set X}, 𝒯.IsAdmissibleCover U W → (∀ k, ∃ i, W k ⊆ V i) →
    𝒯.IsAdmissibleCover U V

/-- The stalk of a presheaf of commutative rings at a point: the filtered colimit over the
admissible opens containing it (§6.3.1), which is the fibre functor of the point of the site. -/
def stalk (F : 𝒯.Opensᵒᵖ ⥤ CommRingCat.{u}) (x : X) : CommRingCat.{u} :=
  sorry

/-- A topological space is a G-topological space with every open set and every open covering
admissible (§6.1.2); its Grothendieck topology is Mathlib's `Opens.grothendieckTopology`. -/
def ofTopologicalSpace (Y : Type u) [TopologicalSpace Y] : GTopology Y :=
  sorry

end GTopology

namespace TauCetiRoadmap.RigidAnalyticGeometry

open CategoryTheory

/-- A locally G-ringed space (BGR 9.3.1; README convention 9): a G-topological space with a sheaf of
commutative rings whose stalks are local. The `K`-algebra structure on the sections, the
completeness conditions and the affinoid covering are the further fields of `IsVariety`. -/
structure LocallyGRingedSpace : Type (u + 1) where
  /-- The underlying set of points. -/
  carrier : Type u
  /-- The G-topology. -/
  gt : GTopology carrier
  /-- The structure sheaf, a sheaf for the Grothendieck topology of the G-topology. -/
  𝒪 : Sheaf gt.grothendieckTopology CommRingCat.{u}
  /-- Stalks are local rings. -/
  isLocalRing_stalk : ∀ x, IsLocalRing (gt.stalk 𝒪.obj x)

namespace LocallyGRingedSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The affinoid variety `Sp A` as a locally G-ringed space: the strong G-topology with the
structure sheaf extended from the affinoid subdomains (§6.4.2). -/
def Sp (A : Type u) [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] :
    LocallyGRingedSpace.{u} :=
  sorry

/-- The open subspace on an admissible open (§6.4.1). -/
def restrict (Y : LocallyGRingedSpace.{u}) (U : Set Y.carrier) (hU : Y.gt.IsAdmissibleOpen U) :
    LocallyGRingedSpace.{u} :=
  sorry

/-- A morphism of locally G-ringed spaces (BGR 9.3.1): a continuous map of G-topological spaces
with a map of sheaves, local on stalks. The sheaf component is the pushforward along the preimage
functor, and locality is stated through the induced stalk maps; both are constructed in §6.4.1. -/
structure Hom (Y Z : LocallyGRingedSpace.{u}) : Type u where
  /-- The underlying map of points. -/
  base : Y.carrier → Z.carrier
  /-- Preimages of admissible opens are admissible opens. -/
  isAdmissibleOpen_preimage : ∀ {U}, Z.gt.IsAdmissibleOpen U → Y.gt.IsAdmissibleOpen (base ⁻¹' U)
  /-- Preimages of admissible coverings are admissible coverings. -/
  isAdmissibleCover_preimage : ∀ {U : Set Z.carrier} {ι : Type u} {V : ι → Set Z.carrier},
    Z.gt.IsAdmissibleCover U V → Y.gt.IsAdmissibleCover (base ⁻¹' U) (fun i ↦ base ⁻¹' V i)

/-- The identity morphism. -/
def Hom.id (Y : LocallyGRingedSpace.{u}) : Hom Y Y where
  base := _root_.id
  isAdmissibleOpen_preimage h := h
  isAdmissibleCover_preimage h := h

/-- A rigid analytic variety (BGR 9.3.1; Bosch 1.12/4; README convention 9): the completeness
conditions `(G0)`–`(G2)` and an admissible covering by open subspaces isomorphic to affinoid
varieties. Isomorphism is stated by a pair of mutually inverse morphisms on points together with
the sheaf identification, which §6.4.1 supplies; here only the point-level condition is recorded,
and the sheaf identification is the content of `Sp` being fully faithful (BGR 9.3.1/1). -/
structure IsVariety (Y : LocallyGRingedSpace.{u}) : Prop where
  g0 : Y.gt.G0
  g1 : Y.gt.G1
  g2 : Y.gt.G2
  exists_affinoid_cover : ∃ (ι : Type u) (U : ι → Set Y.carrier) (hU : Y.gt.IsAdmissibleCover
    Set.univ U), ∀ i, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
      (_ : IsAffinoidAlgebra K A) (φ : Hom (Sp K A) (Y.restrict (U i) (Y.gt.mem_isAdmissibleOpen hU i)))
      (ψ : Hom (Y.restrict (U i) (Y.gt.mem_isAdmissibleOpen hU i)) (Sp K A)),
        Function.LeftInverse ψ.base φ.base ∧ Function.RightInverse ψ.base φ.base

/-- Affinoid varieties are rigid varieties (§6.4.3). -/
theorem isVariety_Sp (A : Type u) [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] :
    IsVariety K (Sp K A) :=
  sorry

/-- **Analytification** (BGR 9.3.4; Bosch 1.13/4; §8.1.2): a `K`-scheme locally of finite type has
a rigid analytification. -/
def analytification (Z : AlgebraicGeometry.Scheme.{u})
    (f : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType f] : LocallyGRingedSpace.{u} :=
  sorry

theorem isVariety_analytification (Z : AlgebraicGeometry.Scheme.{u})
    (f : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType f] : IsVariety K (analytification K Z f) :=
  sorry

end LocallyGRingedSpace

/-! ## Layer 8: classical points -/

section Classical

open scoped NNReal

/-- The classical point of `x ∈ Sp A` (§8.2.2; README convention 12): the valuation `f ↦ |f(x)|`
on `A`, a continuous rank-one valuation with support `x`, which is at most one on `A°` and so is a
point of the adic-spaces roadmap's `Spa(A, A°)`. The ground field is an explicit argument: the
valuation is `evalNorm K x`, which depends on the `K`-algebra structure. -/
def classicalValuation (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (x : MaximalSpectrum A) : Valuation A ℝ≥0 :=
  sorry

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]

theorem coe_classicalValuation (x : MaximalSpectrum A) (f : A) :
    (classicalValuation K x f : ℝ) = evalNorm K x f :=
  sorry

/-- The support of the classical point of `x` is `x` (§8.2.2). -/
theorem supp_classicalValuation (x : MaximalSpectrum A) :
    (classicalValuation K x).supp = x.asIdeal :=
  sorry

/-- Distinct points have distinct classical valuations (§8.2.2). -/
theorem classicalValuation_injective :
    Function.Injective (classicalValuation K : MaximalSpectrum A → Valuation A ℝ≥0) :=
  sorry

end Classical

end TauCetiRoadmap.RigidAnalyticGeometry

/-! ## Targets requested by the Tau Ceti AdicSpaces roadmaps -/

namespace TauCetiRoadmap.RigidAnalyticGeometry

open CategoryTheory Opposite
open scoped TensorProduct Topology

noncomputable section
set_option warn.classDefReducibility false

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Layers 1–2: algebra and normalization of the consumer interface -/

/-- Finite injective affinoid maps are closed embeddings for any complete algebra norms
(BGR 3.7.3/3, 6.1.3/1). No continuity assumption is necessary. -/
theorem isClosedEmbedding_of_finite_injective
    {A B : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsAffinoidAlgebra K A] [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsAffinoidAlgebra K B] (φ : A →ₐ[K] B) (hi : Function.Injective φ)
    (hf : φ.toRingHom.Finite) : Topology.IsClosedEmbedding φ := sorry

/-- Positive powers, including the zero algebra (BGR 6.2.1/1).
This is the consumer form of `supSeminorm_pow`; exponent zero requires `Nontrivial A`. -/
theorem supSeminorm_pow_pos {A : Type u} [CommRing A] [Algebra K A]
    [IsAffinoidAlgebra K A] (f : A) (n : ℕ) (hn : 0 < n) :
    supSeminorm K (f ^ n) = supSeminorm K f ^ n := sorry

/-- Power-bounded elements are integral over the image of the integral Tate algebra
(BGR 6.3.5/1, applied to the presentation). `S` is that image, not the whole unit ball of `A`.
The explicit image equation avoids introducing a second integral Tate-algebra carrier. -/
theorem powerBounded_integral_over_presentation
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {n : ℕ} (π : TateAlgebra K n →ₐ[K] A) (hπ : Function.Surjective π)
    (S : Subring A) (hS : ∀ a, a ∈ S ↔ ∃ t, gaussNorm K t ≤ 1 ∧ π t = a) (a : A) :
    supSeminorm K a ≤ 1 ↔ IsIntegral S a := sorry

/-- A finite affinoid map induces a finite map of canonical reductions (BGR 6.3.5/1).
The subrings, ideals and quotient map are specified by equations, so the theorem applies to
any implementation of the reduction already requested in Layer 2. -/
theorem reduction_finite_of_finite
    {A B : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    (φ : A →ₐ[K] B) (hf : φ.toRingHom.Finite)
    (R : Subring A) (S : Subring B)
    (hR : ∀ a, a ∈ R ↔ supSeminorm K a ≤ 1)
    (hS : ∀ b, b ∈ S ↔ supSeminorm K b ≤ 1)
    (I : Ideal R) (J : Ideal S)
    (hI : ∀ a : R, a ∈ I ↔ supSeminorm K (a : A) < 1)
    (hJ : ∀ b : S, b ∈ J ↔ supSeminorm K (b : B) < 1)
    (φ₀ : R →+* S) (hφ₀ : ∀ a, (φ₀ a : B) = φ (a : A))
    (φr : R ⧸ I →+* S ⧸ J)
    (hφr : ∀ a, φr (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ₀ a)) :
    φr.Finite := sorry

/-! ### Layers 3–4: dimension and affinoid subdomains -/

/-- Equidimensionality of an affinoid domain (BGR 6.1.2/2 and 7.1.1/3;
Conrad, Irreducible components, Lemma 2.1.5). -/
theorem height_eq_ringKrullDim_of_isDomain
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] [IsDomain A]
    (m : Ideal A) [m.IsMaximal] : (m.height : WithBot ℕ∞) = ringKrullDim A := sorry

/-- Nonempty affinoid restriction in a domain is injective (BGR 7.3.2/6 and
6.1.2/2, by flatness and the domain criterion). -/
theorem AffinoidSubdomain.injective_of_isDomain
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] [IsDomain A]
    (U : AffinoidSubdomain K (A := A)) (hU : U.carrier.Nonempty) :
    Function.Injective U.ι := sorry

/-- Faithful flatness of a finite affinoid cover (BGR 7.3.2/6 and 7.2.2/2).
The algebra structure is exactly the product of the representing maps. -/
theorem faithfullyFlat_affinoidCover
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {r : ℕ} (U : Fin r → AffinoidSubdomain K (A := A))
    (hU : (⋃ i, (U i).carrier) = Set.univ) :
    let φ : A →+* (∀ i, (U i).Alg) := RingHom.pi fun i ↦ (U i).ι.toRingHom
    letI := φ.toAlgebra
    Module.FaithfullyFlat A (∀ i, (U i).Alg) := sorry

/-- The denominator becomes a unit when the numerator and denominator generate 1
(BGR 6.1.4/3–4). This adds the missing hypothesis to the earlier representative target. -/
theorem isUnit_toRationalLocalization_of_span_eq_top
    {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
    {m : ℕ} (f : Fin m → A) (g : A)
    (hfg : Ideal.span (insert g (Set.range f)) = ⊤) :
    IsUnit (toRationalLocalization f g g) := sorry

/-- Standard rational covers with the denominator nonzero (BGR 7.1.2/5, 8.2.2).
The existing `rationalDomain` intentionally imposes only inequalities; the intersection below
prevents a common zero from belonging to every member of a purported cover. -/
theorem iUnion_rationalDomain_nonzero_eq_univ_iff
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {r : ℕ} (g : Fin r → A) :
    (⋃ i, rationalDomain K g (g i) ∩ {x | evalNorm K x (g i) ≠ 0}) = Set.univ ↔
      Ideal.span (Set.range g) = ⊤ := sorry

/-! ### Layers 6–8: signatures on the existing locally G-ringed spaces

The following auxiliary definitions are the interfaces already requested in Layers 6–8,
not additional rigid-space carriers. Their implementations, like `Sp` above, remain targets.
In particular, the old point-only `Hom` is supplemented by an explicit sheaf map: theorems about
proper maps never silently treat a map of G-topological sets as a morphism of ringed spaces.
-/

namespace LocallyGRingedSpace

/-- Forget the commutativity of the existing structure sheaf. -/
def ringSheaf (X : LocallyGRingedSpace.{u}) : Sheaf X.gt.grothendieckTopology RingCat.{u} :=
  ⟨X.𝒪.obj ⋙ forget₂ CommRingCat RingCat, by sorry⟩

/-- Mathlib module sheaves on the original G-site. -/
abbrev Modules (X : LocallyGRingedSpace.{u}) := SheafOfModules.{u} X.ringSheaf

/-- BGR 9.4.3 coherence, equivalently local finite presentation on this locally noetherian site. -/
abbrev IsCoherent {X : LocallyGRingedSpace.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsFinitePresentation.{u, u} F

/-- The admissible whole space; its proof comes from `IsVariety.g0`. -/
def topOpen (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X) : X.gt.Opens :=
  ⟨Set.univ, hX.g0.2⟩

/-- Admissible affinoid open, with its structure sheaf identified with that of `Sp A`
as in BGR 9.3.1/1, not merely a bijection of points. -/
def IsAffinoidOpen (K : Type u) (X : LocallyGRingedSpace.{u}) (U : X.gt.Opens) : Prop := sorry

/-- The canonical finite-module Banach topology of coherent sections on an affinoid open
(BGR 3.7.3, 9.4.3). This is a definition, not a global instance. -/
def sectionsTopology {X : LocallyGRingedSpace.{u}} (F : X.Modules)
    (U : X.gt.Opens) (hU : IsAffinoidOpen K X U) (hF : IsCoherent F) :
    TopologicalSpace (F.val.obj (op U)) := sorry

/-- The affinoid Banach topology on the original ring of sections. -/
def affinoidRingTopology (X : LocallyGRingedSpace.{u}) (U : X.gt.Opens) :
    TopologicalSpace (X.𝒪.obj.obj (op U)) := sorry

/-- A countable increasing admissible affinoid covering whose ring restrictions are dense
(Kiehl A/B, Definition 2.3). No relative compactness is required for quasi-Stein. -/
def IsQuasiSteinExhaustion (X : LocallyGRingedSpace.{u}) (U : ℕ → X.gt.Opens) : Prop :=
  (∀ n, IsAffinoidOpen K X (U n)) ∧ Monotone U ∧
    X.gt.IsAdmissibleCover Set.univ (fun n : ULift.{u} ℕ ↦ (U n.down).val) ∧
    ∀ n, ∃ h : U n ≤ U (n + 1),
      letI := affinoidRingTopology X (U n)
      DenseRange (fun x ↦ (X.𝒪.obj.map (homOfLE h).op) x)

/-- Coherent sections have dense restriction along the exhaustion and from the whole space
(Kiehl A/B, Satz 2.4.1 and Hilfssatz 2.5). -/
theorem quasiStein_dense_restriction
    (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X)
    (U : ℕ → X.gt.Opens) (hU : IsQuasiSteinExhaustion K X U)
    (F : X.Modules) (hF : IsCoherent F) (n : ℕ) :
    @DenseRange (F.val.obj (op (U n))) (sectionsTopology K F (U n) (hU.1 n) hF) _
      (fun x ↦ F.val.map (homOfLE (hU.2.1 (Nat.le_succ n))).op x) ∧
    @DenseRange (F.val.obj (op (U n))) (sectionsTopology K F (U n) (hU.1 n) hF) _
      (fun x ↦ F.val.map (homOfLE (show U n ≤ topOpen K X hX from Set.subset_univ _)).op x) := sorry

/-- Theorem A on each affinoid member, which also gives generation at every stalk
(Kiehl A/B, Satz 2.4.3). -/
theorem quasiStein_global_generation
    (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X)
    (U : ℕ → X.gt.Opens) (hU : IsQuasiSteinExhaustion K X U)
    (F : X.Modules) (hF : IsCoherent F) (n : ℕ) :
    Submodule.span (X.ringSheaf.obj.obj (op (U n)))
      (Set.range (F.val.map
        (homOfLE (show U n ≤ topOpen K X hX from Set.subset_univ _)).op)) = ⊤ := sorry

/-- Kiehl's Theorem B, using Mathlib sheaf cohomology on the G-site, not Čech cohomology
as a new definition (Kiehl A/B, Satz 2.4.2). -/
theorem quasiStein_acyclic
    (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X)
    (U : ℕ → X.gt.Opens) (hU : IsQuasiSteinExhaustion K X U)
    (F : X.Modules) (hF : IsCoherent F) (i : ℕ) (hi : 0 < i) :
    Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringSheaf).obj F) i) := sorry

/-- Connected in the admissible sense, with the empty space allowed. -/
def IsPreconnected (X : LocallyGRingedSpace.{u}) : Prop :=
  ∀ V W : Set X.carrier, X.gt.IsAdmissibleOpen V → X.gt.IsAdmissibleOpen W →
    Disjoint V W → X.gt.IsAdmissibleCover Set.univ (fun b : ULift.{u} Bool ↦ if b.down then V else W) →
      V = ∅ ∨ W = ∅

/-- Analytic Zariski closed sets are supports of coherent ideals (BGR 9.5.2/1). -/
def IsAnalyticSubset (K : Type u) (X : LocallyGRingedSpace.{u}) (Z : Set X.carrier) : Prop := sorry

/-- The rigid identity principle, including analytic density and irreducibility
(BGR 7.3.2/9–10; Conrad, Irreducible components, Lemma 2.1.4). -/
theorem identityPrinciple (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X)
    (hc : X.IsPreconnected)
    (hn : ∀ x, IsDomain (X.gt.stalk X.𝒪.obj x) ∧
      IsIntegrallyClosed (X.gt.stalk X.𝒪.obj x))
    (U : X.gt.Opens) (hU : U.val.Nonempty) :
    (∀ Z, IsAnalyticSubset K X Z → U.val ⊆ Z → Z = Set.univ) ∧
    (∀ Z W, IsAnalyticSubset K X Z → IsAnalyticSubset K X W →
      Z ∪ W = Set.univ → Z = Set.univ ∨ W = Set.univ) ∧
    Function.Injective (X.𝒪.obj.map
      (homOfLE (show U ≤ topOpen K X hX from Set.subset_univ _)).op) := sorry

/-- Finite local freeness, with bases compatible under every admissible restriction
(BGR 9.4.2/1). -/
def IsFiniteLocallyFree {X : LocallyGRingedSpace.{u}} (F : X.Modules) : Prop :=
  ∃ (ι : Type u) (V : ι → X.gt.Opens),
    X.gt.IsAdmissibleCover Set.univ (fun i ↦ (V i).val) ∧
    ∀ i, ∃ (n : ℕ) (b : Fin n → F.val.obj (op (V i))),
      ∀ (W : X.gt.Opens) (h : W ≤ V i),
        ∃ e : Module.Basis (Fin n) (X.ringSheaf.obj.obj (op W)) (F.val.obj (op W)),
          ∀ j, e j = F.val.map (homOfLE h).op (b j)

/-- The vector-bundle identity principle; no vanishing or injectivity is assumed. -/
theorem identityPrinciple_locallyFree (X : LocallyGRingedSpace.{u}) (hX : IsVariety K X)
    (hc : X.IsPreconnected)
    (hn : ∀ x, IsDomain (X.gt.stalk X.𝒪.obj x) ∧
      IsIntegrallyClosed (X.gt.stalk X.𝒪.obj x))
    (F : X.Modules) (hf : IsFiniteLocallyFree F) (U : X.gt.Opens) (hU : U.val.Nonempty) :
    Function.Injective (F.val.map
      (homOfLE (show U ≤ topOpen K X hX from Set.subset_univ _)).op) := sorry

/-- The existing map of G-spaces acts on admissible opens by inverse image. -/
def Hom.preimage {X Y : LocallyGRingedSpace.{u}} (f : Hom X Y) : Y.gt.Opens ⥤ X.gt.Opens :=
  { obj := fun U ↦ ⟨f.base ⁻¹' U.val, f.isAdmissibleOpen_preimage U.property⟩
    map := fun h ↦ homOfLE (Set.preimage_mono (leOfHom h)) }

/-- The sheaf component omitted by the representative `Hom` above. -/
abbrev Hom.SheafMap {X Y : LocallyGRingedSpace.{u}} (f : Hom X Y) :=
  Y.𝒪.obj ⟶ f.preimage.op ⋙ X.𝒪.obj

/-- Locality on stalks and compatibility with the structural K-algebra maps of a rigid
morphism (BGR 9.3.1). The structure maps are part of the full `IsVariety` interface. -/
def Hom.IsRigid (K : Type u) {X Y : LocallyGRingedSpace.{u}} (f : Hom X Y) (φ : f.SheafMap) : Prop := sorry

/-- Kiehl properness: a rigid morphism, separated, with pairs of finite affinoid covers
relatively compact over each affinoid in the target (BGR 9.6.2/2; Kiehl E, Definition 2.3). -/
def IsProper (K : Type u) {X Y : LocallyGRingedSpace.{u}} (f : Hom X Y) (φ : f.SheafMap) : Prop := sorry

/-- Derived direct image of module sheaves along the specified ringed-site morphism;
the degree-zero functor is restriction of scalars on the inverse-image opens. -/
def higherDirectImage {X Y : LocallyGRingedSpace.{u}} (f : Hom X Y)
    (φ : f.SheafMap) (hf : Hom.IsRigid K f φ) (i : ℕ) : X.Modules ⥤ Y.Modules := sorry

/-- Kiehl's proper mapping theorem, over every complete nontrivially valued K
(Kiehl E, Theorem 3.3). -/
theorem kiehlProperMapping {X Y : LocallyGRingedSpace.{u}}
    (hX : IsVariety K X) (hY : IsVariety K Y)
    (f : Hom X Y) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ) (hp : IsProper K f φ)
    (F : X.Modules) (hF : IsCoherent F) (i : ℕ) :
    IsCoherent ((higherDirectImage K f φ hf i).obj F) := sorry

/-- Cohomology with its canonical action of the affinoid base. The underlying additive group
is Mathlib `Sheaf.H`; the scalar action is induced by the structural sheaf map. -/
def cohomologyOver {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (hf : Hom.IsRigid K f φ) (F : X.Modules) (i : ℕ) : ModuleCat.{u} A := sorry

/-- Finiteness over an affinoid base, including degree zero and nonreduced bases
(Kiehl E, Satz 2.6). -/
theorem proper_cohomology_finite
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F) (i : ℕ) :
    Module.Finite A (cohomologyOver K f φ hf F i) := sorry

/-- Proper cohomology is strict on finite affinoid Čech complexes (Kiehl E, Satz 2.6).
`cechDifferential` is the alternating restriction differential, with degree-zero sign
`s_j| - s_i|`; no arbitrary complex is quantified over. -/
def cechTerm {X : LocallyGRingedSpace.{u}} (F : X.Modules)
    {r : ℕ} (U : Fin r → X.gt.Opens) (q : ℕ) : AddCommGrpCat.{u} := sorry

def cechDifferential {X : LocallyGRingedSpace.{u}} (F : X.Modules)
    {r : ℕ} (U : Fin r → X.gt.Opens) (q : ℕ) :
    cechTerm F U q ⟶ cechTerm F U (q + 1) := sorry

/-- Product Banach topology from the finite intersection modules. -/
def cechTopology {X : LocallyGRingedSpace.{u}} (F : X.Modules)
    {r : ℕ} (U : Fin r → X.gt.Opens) (q : ℕ) :
    TopologicalSpace (cechTerm F U q) := sorry

theorem proper_cech_closedRange
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F)
    {r : ℕ} (U : Fin r → X.gt.Opens) (hU : ∀ j, IsAffinoidOpen K X (U j))
    (hcover : X.gt.IsAdmissibleCover Set.univ (fun j : ULift.{u} (Fin r) ↦ (U j.down).val)) (q : ℕ) :
    @IsClosed _ (cechTopology F U (q + 1)) (Set.range (cechDifferential F U q)) := sorry

end LocallyGRingedSpace
end
end TauCetiRoadmap.RigidAnalyticGeometry

namespace TauCetiRoadmap.RigidAnalyticGeometry
open CategoryTheory Opposite
open scoped TensorProduct
noncomputable section
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace LocallyGRingedSpace

/-- Rigid base change of `f` along `Sp B → Sp A`, from the fibre product of §6.4. -/
def affinoidBaseChange
    {A B : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (g : A →ₐ[K] B) : LocallyGRingedSpace.{u} := sorry

/-- Cohomology over B of the pullback of F to the preceding fibre product, with the
canonical B-action. The underlying group is the `Sheaf.H` of the pulled-back module. -/
def baseChangedCohomology
    {A B : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (g : A →ₐ[K] B) (F : X.Modules) (i : ℕ) : ModuleCat.{u} B := sorry

/-- Scalar extension followed by pullback: b ⊗ m is sent to b times the pullback of m. -/
def properBaseChangeMap
    {A B : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (hf : Hom.IsRigid K f φ) (g : A →ₐ[K] B) (F : X.Modules) (i : ℕ) :
    letI := g.toRingHom.toAlgebra
    B ⊗[A] cohomologyOver K f φ hf F i →ₗ[B] baseChangedCohomology K f φ g F i := sorry

/-- Kiehl E, Satz 3.5: the canonical base-change map for an affinoid subdomain. -/
theorem proper_cohomology_affinoidSubdomain
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F)
    (U : AffinoidSubdomain K (A := A)) (i : ℕ) :
    Function.Bijective (properBaseChangeMap K f φ hf U.ι F i) := sorry

/-- Finite flat base change, by flat tensoring the finite affinoid Čech complex
(BGR 9.4.2/1; Kiehl E, Satz 3.5 and its Čech argument). -/
theorem proper_cohomology_finiteFlat
    {A B : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    [CommRing B] [Algebra K B] [IsAffinoidAlgebra K B]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F)
    (g : A →ₐ[K] B) (hfinite : g.toRingHom.Finite)
    (hflat : letI := g.toRingHom.toAlgebra; Module.Flat A B) (i : ℕ) :
    Function.Bijective (properBaseChangeMap K f φ hf g F i) := sorry

/-- Inverse limit of H^i(X,F/J^(n+1)F), with the quotient transition maps. -/
def cohomologyQuotientLimit
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (F : X.Modules) (J : Ideal A) (i : ℕ) : ModuleCat.{u} A := sorry

/-- The canonical map induced by reduction modulo all powers of J. -/
def formalFunctionsMap
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (hf : Hom.IsRigid K f φ) (F : X.Modules) (J : Ideal A) (i : ℕ) :
    AdicCompletion J (cohomologyOver K f φ hf F i) →ₗ[A]
      cohomologyQuotientLimit K f φ F J i := sorry

/-- Rigid formal functions, for an arbitrary ideal of the affinoid base
(Kiehl E, Theorems 3.4 and 3.7). -/
theorem proper_formalFunctions
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F) (J : Ideal A) (i : ℕ) :
    Function.Bijective (formalFunctionsMap K f φ hf F J i) := sorry

/-- Relative analytification over the affinoid base Sp A, extending §8.1; it is formed
by the relative restricted-series charts and their gluing, not by assuming X is of finite type
as a K-scheme. For A = K it agrees with the existing `analytification`. -/
def relativeAnalytification
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] : LocallyGRingedSpace.{u} := sorry

/-- Analytification of module sheaves is pullback along the ringed-site map to X. -/
def analytificationModules
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] :
    X.Modules ⥤ (relativeAnalytification K X a).Modules := sorry

/-- Coherence and exactness of analytification (BGR 9.4.2/1 and 9.6.3; flatness of
analytic stalks is the input). Exactness means preservation of finite limits and colimits. -/
theorem analytificationModules_exact_coherent
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] :
    Limits.PreservesFiniteLimits (analytificationModules K X a) ∧
    Limits.PreservesFiniteColimits (analytificationModules K X a) ∧
    ∀ F : X.Modules, SheafOfModules.IsFinitePresentation.{u, u} F →
      IsCoherent ((analytificationModules K X a).obj F) := sorry

/-- The structural rigid morphism of relative analytification. -/
def relativeAnalytificationMap
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] : Hom (relativeAnalytification K X a) (Sp K A) := sorry

def relativeAnalytificationSheafMap
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] : (relativeAnalytificationMap K X a).SheafMap := sorry

/-- Proper algebraic morphisms over an affinoid have Kiehl-proper analytification
(BGR 9.6.3; Köpf GAGA, with Chow dévissage). -/
theorem analytification_isProper
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.IsProper a] :
    IsProper K (relativeAnalytificationMap K X a) (relativeAnalytificationSheafMap K X a) := sorry

/-- The ordinary algebraic H^i(X,F), with its A-action. -/
def algebraicCohomology
    {A : Type u} [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (F : X.Modules) (i : ℕ) :
    ModuleCat.{u} A := sorry

/-- The analytic H^i(X^an,F^an), with its A-action. -/
def analytifiedCohomology
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] (F : X.Modules) (i : ℕ) : ModuleCat.{u} A := sorry

/-- The canonical δ-functorial comparison, induced by the unit of pullback/pushforward;
in degree zero it sends a section to its analytic pullback. -/
def gagaComparison
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.LocallyOfFiniteType a] (F : X.Modules) (i : ℕ) :
    algebraicCohomology X a F i ⟶ analytifiedCohomology K X a F i := sorry

/-- Proper GAGA cohomology over an affinoid base (BGR 9.6.3; Köpf, §5;
Conrad, Relative ampleness, Example 3.2.6). -/
theorem proper_gaga_cohomology
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.IsProper a]
    (F : X.Modules) (hF : SheafOfModules.IsFinitePresentation.{u, u} F) (i : ℕ) :
    IsIso (gagaComparison K X a F i) := sorry

/-- Proper GAGA on coherent sheaves, with the equivalence identified with the specified
analytification functor by a natural isomorphism (same sources). -/
theorem proper_gaga_equivalence
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.IsProper a] :
    ∃ e : (SheafOfModules.isFinitePresentation (R := X.ringCatSheaf)).FullSubcategory ≌
        (SheafOfModules.isFinitePresentation
          (R := (relativeAnalytification K X a).ringSheaf)).FullSubcategory,
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ analytificationModules K X a) := sorry

/-- Connectedness comparison, including the empty scheme (BGR 9.3.4;
Conrad, Irreducible components, Theorem 2.3.1 and Appendix A.1.3). -/
theorem analytification_preconnected_iff
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType a] :
    PreconnectedSpace X ↔ (analytification K X a).IsPreconnected := sorry

end LocallyGRingedSpace
end
end TauCetiRoadmap.RigidAnalyticGeometry

namespace TauCetiRoadmap.RigidAnalyticGeometry
open CategoryTheory Opposite
open scoped TensorProduct
noncomputable section
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The completed affinoid scalar extension of §6.4.6, with its canonical ring structure.
This names the construction requested there, not another affinoid-algebra carrier. -/
def scalarExtensionRing (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    (A : Type u) [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] : CommRingCat.{u} := sorry

/-- The canonical map a ↦ a ⊗ 1 into the completed scalar extension. -/
def scalarExtensionMap (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    (A : Type u) [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] :
    A →+* scalarExtensionRing K L A := sorry

/-- Completed extension of complete nontrivially valued fields is faithfully flat
(Conrad, Irreducible components, Lemma 1.1.5(1); BGR 3.7.3/3). -/
theorem faithfullyFlat_scalarExtension
    (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    (A : Type u) [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A] :
    letI := (scalarExtensionMap K L A).toAlgebra
    Module.FaithfullyFlat A (scalarExtensionRing K L A) := sorry

namespace LocallyGRingedSpace

/-- Cohomology after the §6.4.6 extension to L, with coefficients pulled back from F. -/
def fieldExtendedCohomology
    (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (F : X.Modules) (i : ℕ) : ModuleCat.{u} (scalarExtensionRing K L A) := sorry

/-- The δ-functorial scalar-extension map, b ⊗ m ↦ b times the pullback of m. -/
def fieldExtensionCohomologyMap
    (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (f : Hom X (Sp K A)) (φ : f.SheafMap)
    (hf : Hom.IsRigid K f φ) (F : X.Modules) (i : ℕ) :
    letI := (scalarExtensionMap K L A).toAlgebra
    scalarExtensionRing K L A ⊗[A] cohomologyOver K f φ hf F i →ₗ[scalarExtensionRing K L A]
      fieldExtendedCohomology K L f φ F i := sorry

/-- Proper cohomology commutes with arbitrary complete isometric field extension
(Conrad, Relative ampleness, Theorem A.1.2). -/
theorem proper_cohomology_fieldExtension
    (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [CompleteSpace L] [NormedAlgebra K L]
    {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
    {X : LocallyGRingedSpace.{u}} (hX : IsVariety K X)
    (f : Hom X (Sp K A)) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hp : IsProper K f φ) (F : X.Modules) (hF : IsCoherent F) (i : ℕ) :
    Function.Bijective (fieldExtensionCohomologyMap K L f φ hf F i) ∧
      Module.Finite (scalarExtensionRing K L A) (fieldExtendedCohomology K L f φ F i) := sorry

/-- Vanishing of higher direct images when all affinoid inverse images are quasi-Stein
(Kiehl A/B, Satz 2.4.2, applied locally on the target). -/
theorem quasiStein_higherDirectImage
    {X Y : LocallyGRingedSpace.{u}} (hX : IsVariety K X) (hY : IsVariety K Y)
    (f : Hom X Y) (φ : f.SheafMap) (hf : Hom.IsRigid K f φ)
    (hq : ∀ V : Y.gt.Opens, IsAffinoidOpen K Y V →
      ∃ U : ℕ → (restrict X (f.base ⁻¹' V.val)
        (f.isAdmissibleOpen_preimage V.property)).gt.Opens,
      IsQuasiSteinExhaustion K _ U)
    (F : X.Modules) (hF : IsCoherent F) (i : ℕ) (hi : 0 < i) :
    Limits.IsZero ((higherDirectImage K f φ hf i).obj F) := sorry

/-- The point map of analytification, sending an analytic point to its closed algebraic
point; its construction is part of §8.1. -/
def analytificationPointMap
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType a] : (analytification K X a).carrier → X := sorry

/-- Irreducible components in the analytic Zariski topology. -/
def analyticIrreducibleComponents (X : LocallyGRingedSpace.{u}) : Set (Set X.carrier) :=
  { Z | Maximal (fun Z ↦ IsAnalyticSubset K X Z ∧ Z.Nonempty ∧
      ∀ V W, IsAnalyticSubset K X V → IsAnalyticSubset K X W →
        Z ⊆ V ∪ W → Z ⊆ V ∨ Z ⊆ W) Z }

/-- The component bijection is the inverse-image operation on supports; components carry
reduced induced structures (Conrad, Irreducible components, Theorem 2.3.1). -/
theorem analytification_irreducibleComponents
    (X : AlgebraicGeometry.Scheme.{u}) (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType a] :
    ∃ e : ↥(irreducibleComponents X) ≃
        ↥(analyticIrreducibleComponents K (analytification K X a)),
      ∀ Z, (e Z).val = analytificationPointMap K X a ⁻¹' Z.val := sorry

end LocallyGRingedSpace
end
end TauCetiRoadmap.RigidAnalyticGeometry

namespace TauCetiRoadmap.RigidAnalyticGeometry.LocallyGRingedSpace
open CategoryTheory
noncomputable section
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : Type u} [CommRing A] [Algebra K A] [IsAffinoidAlgebra K A]
variable (X Y : AlgebraicGeometry.Scheme.{u})
variable (a : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
variable (b : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
variable [AlgebraicGeometry.LocallyOfFiniteType a] [AlgebraicGeometry.LocallyOfFiniteType b]

/-- The algebraic derived pushforward R^i f_* on sheaves of modules. -/
def algebraicHigherDirectImage (f : X ⟶ Y) (i : ℕ) : X.Modules ⥤ Y.Modules := sorry

/-- Relative analytification of a morphism of schemes over the affinoid base,
extending the functoriality requested in §8.1. -/
def analyticSchemeMap (f : X ⟶ Y) (h : f ≫ b = a) :
    Hom (relativeAnalytification K X a) (relativeAnalytification K Y b) := sorry

def analyticSchemeSheafMap (f : X ⟶ Y) (h : f ≫ b = a) :
    (analyticSchemeMap K X Y a b f h).SheafMap := sorry

theorem analyticSchemeMap_isRigid (f : X ⟶ Y) (h : f ≫ b = a) :
    Hom.IsRigid K (analyticSchemeMap K X Y a b f h)
      (analyticSchemeSheafMap K X Y a b f h) := sorry

/-- The canonical derived comparison; degree zero is the adjunction mate of the
analytification units and all higher degrees are its δ-functor extension. -/
def directImageComparison (f : X ⟶ Y) (h : f ≫ b = a) (i : ℕ) :
    algebraicHigherDirectImage X Y f i ⋙ analytificationModules K Y b ⟶
      analytificationModules K X a ⋙
        higherDirectImage K (analyticSchemeMap K X Y a b f h)
          (analyticSchemeSheafMap K X Y a b f h)
          (analyticSchemeMap_isRigid K X Y a b f h) i := sorry

/-- Relative proper GAGA over an affinoid base: the specified comparison is an
isomorphism on coherent modules (Kiehl, Endlichkeitssatz, §4, via Theorems 3.3 and 3.5; Conrad, Relative
ampleness, equation (A.1.1)). The base Y need not be proper. -/
theorem proper_gaga_directImage (f : X ⟶ Y) (h : f ≫ b = a)
    [AlgebraicGeometry.IsProper f] (F : X.Modules)
    (hF : SheafOfModules.IsFinitePresentation.{u, u} F) (i : ℕ) :
    IsIso ((directImageComparison K X Y a b f h i).app F) := sorry

end
end TauCetiRoadmap.RigidAnalyticGeometry.LocallyGRingedSpace
