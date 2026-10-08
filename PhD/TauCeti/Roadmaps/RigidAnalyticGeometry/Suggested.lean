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
