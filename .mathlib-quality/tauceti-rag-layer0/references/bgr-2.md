# BGR Chapter 2 excerpts: §2.2.5, §2.2.6, §2.3, §2.7.1 — hand transcription from the scan

Render files `scratchpad/bgr_c/pNNN.pdf.png` (file `pNNN` shows book page NNN − 8). Locators are
`bgr-2.md:<line>`. `ℒ(L, M)` is the module of bounded `A`-linear maps; `b(∏ Mᵢ)`, `c(∏ Mᵢ)` are the
bounded and the zero families with the sup norm.

## 2.2.5 b-separable modules, pp. 86–87

"The following notion will turn out to be extremely useful."

**Definition 1 (2.2.5/1).** A normed A-module M is called *separable with respect to bounded linear
maps* or simply *b-separable* if for each x ≠ 0 in M there exists a bounded A-linear map
λ: M → A such that λ(x) ≠ 0.

"Normed submodules of b-separable modules are b-separable."

**Proposition 2 (2.2.5/2).** Let {Mᵢ}_{i∈I} be a family of b-separable A-modules. Then the modules

  b(∏ Mᵢ) ⊃ c(∏ Mᵢ) ⊃ ⊕ Mᵢ

are b-separable.

*Proof.* Let x = (xᵢ) ∈ b(∏ Mᵢ), x ≠ 0. Choose j such that x_j ≠ 0, and choose a bounded linear
map λ: M_j → A such that λ(x_j) ≠ 0. Define Λ: b(∏ Mᵢ) → A by (yᵢ) ↦ λ(y_j). Then Λ is A-linear
and Λ(x) = λ(x_j) ≠ 0. Moreover |Λ| = |λ|; i.e., Λ is bounded. ∎

**Corollary 3 (2.2.5/3).** All the A-modules b(A), c(A), A^{(∞)}, Aⁿ, A^{(I)} are b-separable. The
module F = A[[Y₁, Y₂, …]] is b-separable.

**Corollary 4 (2.2.5/4).** Let {Mᵢ; i ∈ I} be a family of normed A-modules such that each finitely
generated submodule of Mᵢ is b-separable. Then each finitely generated submodule of ⊕_{i∈I} Mᵢ is
b-separable.

*Proof.* Let N = Σ_{ρ=1}^r A n_ρ be a finitely generated submodule of ⊕ Mᵢ. Then there are elements
m_{ρi} ∈ Mᵢ for ρ = 1, …, r and i ∈ I such that n_ρ = Σ_{i∈I} m_{ρi}. Define
Nᵢ := Σ_{ρ=1}^r A m_{ρi}. Then Nᵢ is a finitely generated A-submodule of Mᵢ and hence b-separable.
According to Proposition 2, we know that ⊕ Nᵢ is b-separable. Because N is obviously contained in
⊕ Nᵢ, N is b-separable. ∎

## 2.2.6 The functor M ⇝ T(M), pp. 87–89

"Let n ≥ 0 be a given fixed integer. We write Tₙ(A) or just T(A) for the normed ring
A⟨X₁, …, Xₙ⟩ provided with the Gauss norm as introduced in (1.4). (T₀(A) is to be interpreted as A.)
For each normed A-module M, we denote by T(M), or more explicitly by Tₙ(M), the set of 'strictly
convergent power series' with coefficients in M:

  Tₙ(M) = { Σ x_{ν₁…νₙ} X₁^{ν₁} ⋯ Xₙ^{νₙ} ; x_{ν₁…νₙ} ∈ M, lim x_{ν₁…νₙ} = 0 }.

Again, T₀(M) stands for the module M itself. Obviously T(M) is an A-module if addition and scalar
multiplication are introduced in the usual way. By defining
|Σ x_{ν₁…νₙ} X₁^{ν₁} ⋯ Xₙ^{νₙ}| := max |x_{ν₁…νₙ}|, we introduce an ultrametric function on T(M)
which again will be called the Gauss norm."

**Lemma 1 (2.2.6/1).** T(M) is a normed A-module (isometrically isomorphic to c(M)).

"Now we are going to provide T(M) with the structure of a T(A)-module. If f = Σ a_μ X^μ,
x = Σ x_ν X^ν is the shorthand notation for elements f ∈ T(A), x ∈ T(M) […], we define their
'Cauchy product' f·x by f·x := Σ_λ (Σ_{μ+ν=λ} a_μ x_ν) X^λ. As in the case of T(A), one checks that
f·x ∈ T(M) and proves that |f·x| ≤ |f|·|x|."

**Proposition 2 (2.2.6/2).** For each normed A-module M, the set T(M) of strictly convergent power
series over M is a normed T(A)-module.

**Proposition 3 (2.2.6/3).** Let L, M be normed A-modules; let φ ∈ ℒ(L, M). Then the map
Tφ: T(L) → T(M) defined by Σ y_ν X^ν ↦ Σ φ(y_ν) X^ν is a T(A)-linear bounded homomorphism with
|Tφ| = |φ|. The map T: ℒ(L, M) → ℒ(T(L), T(M)), φ ↦ Tφ, is an A-linear isometry.

*Proof.* We have |φ(y_ν)| ≤ |φ| |y_ν| → 0; i.e., the power series on the right-hand side above
actually is in T(M). Obviously Tφ is additive. Moreover for f = Σ a_μ X^μ ∈ T(A),
y = Σ y_ν X^ν ∈ T(L), we get

  (Tφ)(f·y) = (Tφ) Σ_λ (Σ_{μ+ν=λ} a_μ y_ν) X^λ = Σ_λ φ(Σ_{μ+ν=λ} a_μ y_ν) X^λ
            = Σ_λ (Σ_{μ+ν=λ} a_μ φ(y_ν)) X^λ = f·(Tφ)(y);

i.e., Tφ is a T(A)-module homomorphism. Finally
|(Tφ)(y)| = max_ν |φ(y_ν)| ≤ |φ| max_ν |y_ν| = |φ|·|y|, whence |Tφ| ≤ |φ|. Since M ⊂ T(M), we also
have |Tφ| ≥ |φ| and therefore |Tφ| = |φ|. […] ∎

**Proposition 4 (2.2.6/4).** T: M ⇝ T(M) is a covariant additive functor from the category of
normed A-modules into the category of normed T(A)-modules (with bounded linear maps as morphisms
in both cases).

"We state an important corollary of Proposition 3:"

**Corollary 5 (2.2.6/5), p. 89.** If M is a b-separable A-module, then T(M) is a b-separable
T(A)-module.

*Proof.* Take x = Σ x_ν X^ν ≠ 0 in T(M), say x_i ≠ 0. By assumption there exists a λ ∈ ℒ(M, A) such
that λ(x_i) ≠ 0. Then Tλ ∈ ℒ(T(M), T(A)) by Proposition 3, and (Tλ)(x) ≠ 0 by definition of Tλ. ∎

**Proposition 6 (2.2.6/6).** If M is a faithfully normed A-module, then T(M) is a faithfully normed
T(A)-module.

**Proposition 7 (2.2.6/7).** Let φ ∈ ℒ(L, M) be given. Then ker Tφ = T(ker φ). In particular, Tφ is
injective if and only if φ is injective. If φ is open and surjective, Tφ is surjective.

**Proposition 8 (2.2.6/8).** Let M₁, …, M_s be normed A-modules. There is a canonical isometric
T(A)-module isomorphism T(⊕₁ˢ M_σ) ≅ ⊕₁ˢ T(M_σ).

## 2.3 Weakly cartesian spaces, pp. 89–93

"In the following, we always work over a field K with a non-trivial valuation. Let V denote a
normed (hence faithfully normed, cf. Proposition 2.1.1/4) K-vector space. We often write 'space'
instead of 'normed K-vector space'. From Proposition 2.1.8/2, we get that, for K-linear maps
between spaces, continuity and boundedness are equivalent properties."

### 2.3.1 Elementary properties of normed spaces, p. 90

**Proposition 1 (2.3.1/1).** Let U be a subspace of Kⁿ. Then U is closed, and there exists a linear
homeomorphism U → K^r where r := dim_K U.

*Proof.* An automorphism of Kⁿ is always a homeomorphism (cf. (2.2.1)). Because each subspace U may
be transformed by an automorphism into the subspace {(c₁, …, c_r, 0, …, 0); cᵢ ∈ K}, where
r := dim_K U, the assertion is evident. ∎

"Recall, however, that a (bounded) K-linear bijection Kⁿ → V need not be a homeomorphism (cf.
(2.2.1)), whereas each bounded K-linear bijection V → Kⁿ is a homeomorphism.
The space V obviously is b-separable if each K-linear map V → K is bounded. We have the following
converse for finite-dimensional spaces."

**Proposition 2 (2.3.1/2).** If a finite-dimensional normed space U is b-separable, then each
K-linear map U → K is bounded.

*Proof.* It is enough to construct n := dim_K U linearly independent bounded K-linear maps
λ₁, …, λₙ of U into K, since each K-linear map is a linear combination of these and hence bounded.
Choose at random a bounded K-linear map λ₁ ≠ 0. Let λ₁, …, λ_{m−1}, m − 1 < n, already be
constructed. Choose u ≠ 0 in ⋂₁^{m−1} ker λ_μ, and take a bounded K-linear map λ_m: U → K such that
λ_m(u) = 1. Since λ₁(u) = ⋯ = λ_{m−1}(u) = 0, each linear relation Σ₁^m a_μ λ_μ = 0, a_μ ∈ K,
implies a_m = 0 and hence a₁ = ⋯ = a_{m−1} = 0, since λ₁, …, λ_{m−1} are independent by
assumption. ∎

**Corollary 3 (2.3.1/3).** A finite-dimensional normed space U is b-separable if and only if
Hom_K(U, K) = ℒ(U, K).

"For each bounded K-linear map λ: V → K, the kernel space ker λ is closed in V. We shall need the
following converse."

**Proposition 4 (2.3.1/4).** Each K-linear map λ: V → K with a closed kernel is bounded.

*Proof.* Assume λ ≠ 0. Since ker λ is closed in V, the residue space V/ker λ provided with the
residue norm is a 1-dimensional normed K-vector space. Therefore, it follows from Proposition
2.1.1/3 that the K-linear bijection λ̄: V/ker λ → K induced by λ is bounded (V/ker λ is a
faithfully normed K-module since K is a field). Now the boundedness of λ follows since λ is the
composition of the canonical contraction map V → V/ker λ with λ̄. ∎

### 2.3.2 Weakly cartesian spaces, pp. 90–91

"For each K-vector space V, we denote by 𝔉(V) the family of all finite-dimensional K-subspaces. We
have the following"

**Theorem 1 (2.3.2/1).** The following statements over a normed K-vector space V are equivalent:
 (1) For each U ∈ 𝔉(V), there exists a linear homeomorphism U ⥲ Kⁿ, n := dim_K U.
 (2) Each U ∈ 𝔉(V) is closed in V.
 (3) Each U ∈ 𝔉(V) is b-separable.

*Proof.* (1) → (2): Take U ∈ 𝔉(V) and x ∈ Ū. Then U' := U + Kx ∈ 𝔉(V). Hence by assumption U' is
homeomorphic to a space Kⁿ. Therefore U ⊂ U' ≃ Kⁿ is closed in U' by Proposition 2.3.1/1. Since
x ∈ U' is in the U'-closure of U, we deduce that x ∈ U. Thus U = Ū.
(2) → (3): Take U ∈ 𝔉(V) and u ∈ U − {0}. Then there exists a K-linear map λ: U → K such that
λ(u) ≠ 0. By assumption ker λ ∈ 𝔉(V) is closed in V and hence also closed in U. Thus, by
Proposition 2.3.1/4, λ is bounded.
(3) → (1): Take U ∈ 𝔉(V). Choose n := dim_K U linearly independent maps λ_ν: U → K, 1 ≤ ν ≤ n. By
Proposition 2.3.1/2 these maps are continuous. Therefore the product map λ₁ × ⋯ × λₙ: U → Kⁿ is
continuous. Since it is bijective, it is a homeomorphism. ∎

**Definition 2 (2.3.2/2).** A normed K-vector space V is called *weakly cartesian* (more precisely
*weakly K-cartesian*) if the conditions of Theorem 1 are fulfilled.

"We say that a finite-dimensional K-vector space carries the *product topology* if there exists a
linear homeomorphism U → Kⁿ, n := dim_K U. […] Therefore,"

**Lemma 3 (2.3.2/3).** V is weakly cartesian if and only if each finite-dimensional subspace of V
carries the product topology.

**Proposition 4 (2.3.2/4).** An n-dimensional space V is weakly cartesian if and only if there
exists a linear homeomorphism φ: V → Kⁿ. (Observe that φ need not be isometric.)

**Lemma 5 (2.3.2/5).** Each space V which can be exhausted by weakly cartesian spaces is weakly
cartesian. Each subspace of a weakly cartesian space is weakly cartesian.

**Lemma 6 (2.3.2/6).** If each finite-dimensional subspace of V is weakly cartesian, V itself is
weakly cartesian.

**Proposition 7 (2.3.2/7).** Each b-separable space V is weakly cartesian.

"So, in particular, the spaces Kⁿ, K^{(∞)}, K^{(I)}, c(K) and b(K) are weakly cartesian."

### 2.3.3 Properties of weakly cartesian spaces, pp. 92–93

**Proposition 1 (2.3.3/1).** The direct sum of weakly cartesian spaces is weakly cartesian.

*Proof.* Since each finite-dimensional subspace of a direct sum ⊕_{i∈I} Vᵢ is contained in a
*finite* direct sum of finite-dimensional subspaces of the Vᵢ, it is enough to consider the direct
sum of two finite-dimensional weakly cartesian spaces V₁, V₂. However, if Vᵢ is homeomorphic to
K^{nᵢ}, i = 1, 2, the sum V₁ ⊕ V₂ is homeomorphic to K^{n₁+n₂}. ∎

**Proposition 2 (2.3.3/2).** Let K be a subfield of a valued field K' such that K' is weakly
K-cartesian. Then each weakly K'-cartesian K'-vector space V is weakly K-cartesian.

*Proof.* Let U = Σ₁^m K e_μ be a finite-dimensional K-subspace of V. Then U' := Σ₁^m K' e_μ is a
finite-dimensional K'-subspace, and hence by assumption homeomorphic to a space K'^s. Since K' is
weakly K-cartesian, the direct sum K'^s is also weakly K-cartesian by Proposition 1. Thus the
K-space U' is weakly K-cartesian. Hence the K-subspace U ⊂ U' is also weakly K-cartesian. ∎

**Lemma 3 (2.3.3/3).** Let A be a valued integral domain and K its valued field of fractions. Let M
be a faithfully normed A-module such that each finitely generated A-submodule of M is b-separable.
Then the K-vector space V := M ⊗_A K (provided with the canonical norm extension) is weakly
K-cartesian.

*Proof.* Let U = Σ₁^m K e_μ ⊂ V be a finite-dimensional K-vector space. We may assume e_μ ∈ M, since
each e_μ is of the form x_μ/a_μ, x_μ ∈ M, a_μ ∈ A − {0}. By assumption the A-module
N := Σ₁^m A e_μ ⊂ M is b-separable. Take u ≠ 0 in U. Choose c ≠ 0 in A such that cu ∈ N. Since
cu ≠ 0, there is a bounded A-linear map λ': N → A with λ'(cu) ≠ 0. Now λ' extends uniquely to a
bounded K-linear map λ: U → K (cf. (2.1.3), use that U = N ⊗_A K). From cλ(u) = λ'(cu) ≠ 0, we
conclude λ(u) ≠ 0. Hence U is a b-separable K-space. Thus V is weakly K-cartesian. ∎

**Proposition 4 (2.3.3/4).** If K is complete, each normed K-space V is weakly cartesian. In
particular, V is complete if dim_K V < ∞.

*Proof (p. 93).* We only have to show that each finite-dimensional K-space V is weakly cartesian.
That such a space is complete follows then from Proposition 2.1.5/6. We proceed by induction on
n := dim_K V. The case n = 0 is clear. Suppose n > 0; let U ⊂ V be a subspace. We want to show that
U is closed in V. This is clear if U = V. Therefore, assume that U ≠ V. By the induction
hypothesis, U is weakly cartesian and hence complete. As a complete space, U is closed in V. ∎

**Corollary 5 (2.3.3/5).** If K is complete, any two norms | |₁, | |₂ on a finite-dimensional
K-vector space are equivalent.

**Proposition 6 (2.3.3/6).** Let V be a finite-dimensional normed K-vector space and V̂ its
completion. Then dim_K V ≥ dim_K̂ V̂, and equality holds if and only if V is weakly K-cartesian. […]

### 2.3.4 Weakly cartesian spaces and tame modules, pp. 93–94

"*If V is weakly K-cartesian, each K̊-submodule M of V° of finite rank is b-separable.*
In order to see this, take x ∈ M − {0}. Since rk M < ∞, the K-vector space U := K·M ⊂ V is
finite-dimensional; hence, there exists a bounded K-linear map λ: U → K such that λ(x) ≠ 0. Choose
c ∈ K* such that |λ(U°)| ≤ |c| and set Λ := c⁻¹λ. Since M ⊂ U°, the map Λ induces a bounded
K̊-linear map Λ|M: M → K̊ with Λ(x) ≠ 0. ∎"

**Proposition 1 (2.3.4/1).** If V° is a tame K̊-module (i.e., if each K̊-submodule M ⊂ V° of finite
rank is finitely generated), then V is weakly K-cartesian.

**Proposition 2 (2.3.4/2).** If K̊ is a discrete valuation ring, a normed K-vector space V is weakly
K-cartesian if and only if V° is a tame K̊-module.

## 2.6 Weakly cartesian spaces of countable dimension, pp. 107–110

"As always, let K denote a field with a non-trivial valuation. All vector spaces which occur are
K-normed. For an arbitrary index set I, let eᵢ := (δ_ij)_{j∈I}, i ∈ I, denote the canonical K-basis
of K^{(I)}. A vector space V is said to have *countable dimension* if there exists a K-linear
bijection K^{(ℕ)} → V."

### 2.6.1 Weakly cartesian bases

"Each K-basis {yᵢ}_{i∈I} of a vector space V induces a K-linear bijection Φ: K^{(I)} → V given by
Σ aᵢeᵢ ↦ Σ aᵢyᵢ […]. If sup |yᵢ| < ∞, then Φ is bounded with |Φ| = sup |yᵢ| (cf. Proposition
2.2.2/1). Fixing an element ρ ∈ |K|, ρ > 1, we see by Proposition 2.1.8/1 that for each vector
v ∈ V, v ≠ 0, there exists an element c ∈ K* such that 1 ≤ |cv| ≤ ρ. […]"

**Proposition 1 (2.6.1/1).** Each space V admits a ρ-bounded basis. Each such basis gives rise to a
bounded K-linear bijection Φ: K^{(I)} → V with 1 ≤ |Φ| ≤ ρ.

**Proposition 2 (2.6.1/2).** Let {yᵢ}_{i∈I} be a ρ-bounded basis of V, and let α > 0 be a real
number such that max_{i∈I} {|aᵢyᵢ|} ≤ α |Σ aᵢyᵢ| for all vectors Σ aᵢyᵢ of V. Then |Φ⁻¹| ≤ α.

**Definition 3 (2.6.1/3), p. 108.** Let α be a positive real number. A ρ-bounded family
{yᵢ; i ∈ I} of V with yᵢ ≠ 0 is called *α-cartesian* if max_{i∈I} {|aᵢyᵢ|} ≤ α |Σ aᵢyᵢ| for every
vector v = Σ aᵢyᵢ ∈ V, where aᵢ = 0 for almost all i ∈ I. A ρ-bounded family {yᵢ; i ∈ I} is called
*weakly K-cartesian* […] if there exists a real number α > 0 such that it is α-cartesian.

**Proposition 4 (2.6.1/4).** For each normed vector space V admitting a weakly K-cartesian basis,
there is a linear homeomorphism onto the space K^{(I)}. In particular, all these spaces are
b-separable and weakly K-cartesian.

### 2.6.2 Existence of weakly cartesian bases. Fundamental theorem, pp. 108–110

**Observation 1 (2.6.2/1).** Let α > 1. A ρ-bounded family {y₁, y₂, …} of V is α-cartesian if there
exists a strictly increasing sequence 1 =: α₁ < α₂ < ⋯ of real numbers converging to α such that,
for n = 1, 2, …, we have

  (*) αₙ · max {|u|, |ay_{n+1}|} ≤ α_{n+1} |u + ay_{n+1}| for all a ∈ K, u ∈ Σ₁ⁿ K y_ν.

**Observation 2 (2.6.2/2).** Let V be any K-space (not necessarily weakly cartesian and not
necessarily of countable dimension). Let U ⊂ V be a K-subspace, and let x ∈ V be not in the closure
of U. Then for each real number β > 1, there exists a vector y ∈ U' := U + Kx such that
U' = U + Ky and such that max {|u|, |ay|} ≤ β |u + ay| for all u ∈ U, a ∈ K.

*Proof.* Since x ∉ Ū, we have |x, U| = inf_{u∈U} |x + u| > 0. Choose u₀ ∈ U such that
|x + u₀| ≤ β |x, U|. We claim that y := x + u₀ has the required properties. Since y ∉ U, we have
U' = U + Ky. If |u| ≠ |ay|, we have (since β > 1) β |u + ay| ≥ |u + ay| = max {|u|, |ay|}. So assume
|u| = |ay|. It remains to show that |ay| ≤ β |u + ay|. We may assume a ≠ 0. The condition
|y| ≤ β |x, U| implies (since u₀ ∈ U) β |x + u₀ + a⁻¹u| ≥ |y|. Multiplying by |a| and using
x + u₀ = y, we get β |ay + u| ≥ |ay|. ∎

**Proposition 3 (2.6.2/3).** Let V be weakly cartesian of at most countable dimension. Let
{vᵢ; 1 ≤ i < d} be any basis of V (where d = ∞ if V is infinite-dimensional). Then for each α > 1,
there is an α-cartesian basis {yᵢ; 1 ≤ i < d} of V such that Σ₁ⁿ K vᵢ = Σ₁ⁿ K yᵢ for all n,
1 ≤ n < d.

*Proof.* Set Uₙ := Σ₁ⁿ K vᵢ, and choose a strictly increasing sequence 1 =: α₁ < α₂ < ⋯ of real
numbers converging to α. Due to Observation 1, it is enough to construct a system {yᵢ; 1 ≤ i < d}
of vectors in V with the following properties: (1) 1 ≤ |yₙ| ≤ ρ and Uₙ = Σ₁ⁿ K yᵢ for all n,
(2) αₙ max {|u|, |ay_{n+1}|} ≤ α_{n+1} |u + ay_{n+1}|, a ∈ K, u ∈ Uₙ for all n. We proceed by
induction on n: choose y₁ := c₁v₁, c₁ ∈ K*, such that 1 ≤ |y₁| ≤ ρ. Let y₁, …, yₙ be already
constructed, n ≥ 1. Then Uₙ = Σ₁ⁿ K yᵢ. Since V is weakly cartesian, Uₙ is closed in V, and hence
v_{n+1} is not in the closure of Uₙ. Thus, we may apply Observation 2 (with U := Uₙ, x := v_{n+1}
and β := α_{n+1}/αₙ). We get a vector y ∈ U_{n+1} such that U_{n+1} = Uₙ + Ky and
max {|u|, |ay|} ≤ (α_{n+1}/αₙ) |u + ay| for all a ∈ K, u ∈ Uₙ. Choose c ∈ K* such that 1 ≤ |cy| ≤ ρ,
and set y_{n+1} := cy. Then (1) and (2) are fulfilled for y₁, …, yₙ, y_{n+1}. ∎

**Theorem 4 (2.6.2/4), p. 110.** For each weakly K-cartesian vector space V of countable
(non-finite) dimension, there exists a linear homeomorphism onto K^{(∞)}.

"In fact, we proved slightly more: *For each ρ ∈ |K|, ρ > 1, and each α > 1, there is a linear
homeomorphism Φ: K^{(∞)} → V such that |Φ| ≤ ρ, |Φ⁻¹| ≤ α.*"

**Corollary 5 (2.6.2/5).** Each weakly cartesian vector space of countable dimension is
b-separable.

## 2.7 Normed vector spaces of countable type. The Lifting Theorem, p. 110

"In this section we always assume that K is complete and that its valuation is non-trivial."

### 2.7.1 Spaces of countable type

"By Proposition 2.3.3/4 all normed K-vector spaces are weakly cartesian (K is complete, as we
said). For such spaces we now introduce a concept generalizing the notion of 'weakly cartesian
spaces of countable dimension'."

**Definition 1 (2.7.1/1).** A normed K-vector space V is said to be *of countable type* if V
contains a dense linear subspace of at most countable dimension.

"The space c(K) of all zero sequences over K is of countable type, since K^{(∞)} is dense in c(K).
This is, in fact, the most general example of a space of countable type, as can be seen from"

**Proposition 2 (2.7.1/2).** Each normed K-vector space V of countable type admits a linear
homeomorphism onto some space Kⁿ or onto a dense subspace of c(K). In particular, V is b-separable.

"Because c(K) is b-separable (see Corollary 2.2.5/3), we only have to *prove* the first assertion.
If dim_K V < ∞, the assertion follows from Proposition 2.3.3/4. If dim_K V = ∞, we can apply
Theorem 2.6.2/4 and the fact that c(K) is the completion of K^{(∞)}. ∎"

**Proposition 3 (2.7.1/3), p. 111.** Let W be a dense linear subspace of V of countable dimension,
and let {wᵢ; i ∈ ℕ} be an α-cartesian (and ρ-bounded) basis of W (cf. Proposition 2.6.2/3). Then the
map ψ: W → K^{(∞)}, given by Σ cᵢwᵢ ↦ (cᵢ), where cᵢ = 0 for almost all i ∈ ℕ, extends uniquely to
a strict K-linear injection Ψ: V → c(K). We have

  (o) α⁻¹ |Ψ(v)| ≤ |v| ≤ ρ |Ψ(v)| for all v ∈ V.

The map Ψ is an epimorphism if and only if V is complete so that V = {Σ_{i∈ℕ} cᵢwᵢ; cᵢ ∈ K, cᵢ → 0}
in this case.

*Proof.* The map ψ is a homeomorphism. Namely, for each w = Σ cᵢwᵢ ∈ W, where cᵢ = 0 for almost
all i ∈ ℕ, we have α⁻¹ max |cᵢ| |wᵢ| ≤ |w| ≤ max |cᵢ| |wᵢ|. Since 1 ≤ |wᵢ| ≤ ρ for all i ∈ ℕ and
since max |cᵢ| = |ψ(w)|, we conclude that α⁻¹ |ψ(w)| ≤ |w| ≤ ρ |ψ(w)| for all w ∈ W. Because W is
dense in V and c(K) is complete and contains K^{(∞)}, the map ψ can be extended to a K-linear
homeomorphism V̂ → c(K). Let Ψ: V → c(K) be its restriction to V. By continuity arguments, (o)
holds. Hence Ψ is injective and bounded, and Ψ⁻¹: Ψ(V) → V is bounded. The last assertion is
obvious. ∎
