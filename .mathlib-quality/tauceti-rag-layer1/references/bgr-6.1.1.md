# BGR §6.1.1 The category 𝔄 of k-affinoid algebras (book pp. 221–227) — hand transcription from the scan

Render files `bgr1/pNNN.pdf.png` show book page NNN − 6. Locators are `bgr-6.1.1.md:<line>`.
Throughout, "k" is a field with a complete valuation; all homomorphisms are k-algebra homomorphisms.

(p. 221) "6.1.1. The category 𝔄 of k-affinoid algebras. — Each residue algebra Tₙ/𝔞 of Tₙ by a (closed)
ideal 𝔞 ⊂ Tₙ becomes a k-Banach algebra if one defines the residue norm of the residue class f̄ of an
element f ∈ Tₙ by
    |f̄| := |f, 𝔞| := inf {|h| ; h ∈ f̄}.
The residue epimorphism Tₙ → Tₙ/𝔞 is contractive (hence continuous) and open. In particular, the residue
norm induces the quotient topology on Tₙ/𝔞. Notice that the residue norm is not in general
power-multiplicative. For example, Tₙ/𝔞 can have nilpotent elements ≠ 0."

**Definition 1 (6.1.1/1).** "A k-Banach algebra A is called affinoid (more precisely, k-affinoid) if there
exists an integer n ≥ 0 and a continuous epimorphism α: Tₙ → A."

(p. 222) "By BANACH's Theorem, α is open; hence A is isomorphic as a k-Banach algebra to the residue algebra
Tₙ/ker α. In particular, the residue norm, which from now on will be denoted by | |_α, induces the given
Banach topology on A.
The residue norm | |_α depends heavily on the choice of the epimorphism α. However all norms | |_α are
equivalent, since they induce the given Banach topology on A."

**Proposition 2 (6.1.1/2).** "Let A be k-affinoid and let | |_α be a residue norm on A. Then |A|_α ⊂ |k|.
In particular, each vector ≠ 0 in A can be normed to length 1 by multiplication with a scalar."
"The assertion follows directly from Corollary 5.2.7/8."

**Remark.** "We shall see later that a reduced affinoid algebra can be provided in a natural way with a
complete power-multiplicative norm, the so-called spectral norm. For this norm, all values are roots of
elements of |k|."

**Proposition 3 (6.1.1/3).** "Let A be a k-affinoid algebra. Then A is a Noetherian Jacobson ring. Each ideal
𝔞 ⊂ A is closed, and each quotient A/𝔞 (provided with the residue norm) is k-affinoid."
*Proof.* "Let α: Tₙ → A be a continuous epimorphism. Then A ≅ Tₙ/ker α is a Noetherian Jacobson ring since
Tₙ is such a ring (Theorems 5.2.6/1 and 5.2.6/3). The closedness of any ideal 𝔞 ⊂ A follows from
Proposition 3.7.2/2 (or simply from the closedness of ideals in Tₙ), and A/𝔞 is k-affinoid, since
Tₙ →α A → A/𝔞 is a continuous epimorphism."

"The k-affinoid algebras form the objects of a category 𝔄; the morphisms of this category are the
continuous k-algebra homomorphisms. (We shall see later that every k-algebra homomorphism between
k-affinoid algebras is continuous.) For our purposes, the category 𝔄 will play the same fundamental role as
does the category of affine algebras in algebraic geometry.
As in (1.2.5), we use the notation Å for the subring of power-bounded elements in a k-affinoid algebra A.
Morphisms of 𝔄 map power-bounded elements into power-bounded elements."

**Proposition 4 (6.1.1/4).** "Let φ: B → A be a continuous homomorphism between k-Banach algebras A, B.
Let f₁, …, fₙ be power-bounded elements in A; let X₁, …, Xₙ be indeterminates. Then there exists a unique
continuous homomorphism Φ: B⟨X₁, …, Xₙ⟩ → A such that
    Φ | B = φ,    Φ(Xᵢ) = fᵢ,    i = 1, …, n."
*Proof.* "For h = Σ a_{ν₁…νₙ} X₁^{ν₁} … Xₙ^{νₙ} ∈ B⟨X₁, …, Xₙ⟩, we set
    Φ(h) := Σ φ(a_{ν₁…νₙ}) f₁^{ν₁} … fₙ^{νₙ}.
(p. 223) Since fᵢ ∈ Å and lim a_{ν₁…νₙ} = 0, the series on the right-hand side represents a well-defined
element of A. It is clear that this is the only way to extend φ to the polynomial algebra B[X₁, …, Xₙ] and
that Φ is a homomorphism of B[X₁, …, Xₙ] into A. As B[X₁, …, Xₙ] is dense in B⟨X₁, …, Xₙ⟩, it follows that
Φ is the unique continuous extension of φ to a homomorphism of B⟨X₁, …, Xₙ⟩ into A."

(p. 223) "In the case B = k, Proposition 4 says that, for each set f₁, …, fₙ ∈ Å and each chart
{X₁, …, Xₙ} of Tₙ, there exists exactly one continuous homomorphism Φ: Tₙ → A such that Φ(Xᵢ) = fᵢ,
i = 1, …, n. If Φ is surjective, we call the elements f₁, …, fₙ a system of affinoid generators of A. In
particular, A is a k-affinoid algebra, and we write suggestively A = k⟨f₁, …, fₙ⟩.
We shall prove now that the category 𝔄 is closed under finite extensions, i.e., that 𝔄 contains all finite
overalgebras of a given k-affinoid algebra. Recall that a ring homomorphism ϱ: R → S is called finite if S
provided with the induced R-module structure (i.e., r · s := ϱ(r) s) is a finite R-module. Recall further
that the composition of two finite ring homomorphisms is finite. Each epimorphism is finite; hence each
A ∈ 𝔄 admits finite homomorphisms Tₙ → A."

**Proposition 5 (6.1.1/5).** "Let B be an object of 𝔄, and let φ: B → A be a continuous finite homomorphism
into a k-Banach algebra A. Then A ∈ 𝔄."
*Proof.* "We may assume B = Tₙ for some n. By assumption there are elements a₁, …, a_m ∈ A such that
A = Σ_{i=1}^{m} φ(Tₙ) aᵢ. We may assume aᵢ ∈ Å. By Proposition 4, the map φ extends to a continuous
homomorphism Φ: Tₙ⟨Y₁, …, Y_m⟩ → A such that Φ(Yᵢ) = aᵢ. Then Φ is surjective, and hence A ∈ 𝔄."

"If φ is not assumed to be continuous and A is not assumed to be a Banach algebra, we still have"

**Proposition 6 (6.1.1/6).** "Let B be an object of 𝔄, and let φ: B → A be a finite homomorphism into a
k-algebra A. Then A can be provided with a topology such that φ is continuous and strict and such that
A ∈ 𝔄."
*Proof.* "By Proposition 3.7.4/1, we can provide A with a topology such that A becomes a k-Banach algebra
and φ becomes continuous and strict. We have A ∈ 𝔄 by Proposition 5."

"Later we shall see that the topology on A is uniquely determined.
The category 𝔄 is closed with respect to the operation of forming direct sums; i.e., if A, B are objects
of 𝔄, then the ring-theoretic direct sum A ⊕ B belongs to 𝔄."
*Proof.* "Let α: Tₙ → A and β: T_m → B be continuous epimorphisms. We may assume m = n. Define
α ⊕ β: Tₙ ⊕ Tₙ → A ⊕ B by (α ⊕ β)(f ⊕ g) := α(f) ⊕ β(g). Then α ⊕ β is a continuous k-algebra
epimorphism. Therefore (p. 224) we only have to show that the k-Banach algebra Tₙ ⊕ Tₙ (viewed as the normed
direct sum of Tₙ with itself) belongs to 𝔄. The map φ: Tₙ → Tₙ ⊕ Tₙ given by x ↦ (x, x) is a continuous
finite homomorphism. Hence Tₙ ⊕ Tₙ ∈ 𝔄 by Proposition 5."
"The statement Tₙ ⊕ Tₙ ∈ 𝔄 can also be verified by checking directly that the map Φ: Tₙ⟨Y⟩ → Tₙ ⊕ Tₙ given by
Φ(Σ a_ν Y^ν) := (a₀, Σ a_ν) is a continuous epimorphism."

(p. 224) "We want to see that 𝔄 is also closed with respect to complete tensor products. Beginning with a
slightly more general situation, we let A and B denote k-Banach algebras. Then A ⊗̂_k B is a complete
normed k-algebra (cf. (3.1.1)), hence a k-Banach algebra. If in particular B = k⟨X₁, …, Xₙ⟩, there exists
by Proposition 4 a unique continuous homomorphism σ: A⟨X₁, …, Xₙ⟩ → A ⊗̂_k k⟨X₁, …, Xₙ⟩ such that
    Xᵢ ↦ 1 ⊗̂ Xᵢ, i = 1, …, n,   a ↦ a ⊗̂ 1, a ∈ A.
More generally, Proposition 4 says that the inclusions σ₁: A ↪ A⟨X₁, …, Xₙ⟩ and σ₂: k⟨X₁, …, Xₙ⟩ ↪
A⟨X₁, …, Xₙ⟩ satisfy the universal property stated in Proposition 3.1.1/2 which characterizes the complete
tensor product A ⊗̂_k k⟨X₁, …, Xₙ⟩. Thus one concludes that σ is an isomorphism. Furthermore, σ is obviously
contractive. Also σ⁻¹ is contractive by Proposition 3.1.1/2, since σ₁ and σ₂ are contractive. Hence we get"

**Proposition 7 (6.1.1/7).** "Let A denote a k-Banach algebra. Then the canonical k-algebra homomorphism
σ: A⟨X₁, …, Xₙ⟩ → A ⊗̂_k k⟨X₁, …, Xₙ⟩ is an isometric isomorphism."

"The proposition applies in particular to the cases where A is a TATE algebra Tₙ(k) or where A is an
extension field k′ of k with a complete valuation on k′ extending the valuation on k. Thus, we have"

**Corollary 8 (6.1.1/8).** "There are canonical isometric isomorphisms T_m ⊗̂_k Tₙ ≅ T_{m+n} and
k′ ⊗̂_k Tₙ(k) ≅ Tₙ(k′)."

**Corollary 9 (6.1.1/9).** "Let A and B denote k-affinoid algebras, and as above let k′ be a complete valued
extension field of k. Then A ⊗̂_k B is k-affinoid and k′ ⊗̂_k B is k′-affinoid. The canonical homomorphism
B → k′ ⊗̂_k B is a strict monomorphism."
*Proof.* "Let φ: k⟨X₁, …, Xₙ⟩ → B denote a continuous epimorphism. By BANACH's Theorem, φ is open and hence
strict by Proposition 1.1.9/3. Applying (p. 225) Proposition 2.1.8/6, we get continuous epimorphisms
    id_A ⊗̂ φ: A ⊗̂_k k⟨X₁, …, Xₙ⟩ → A ⊗̂_k B,   id_{k′} ⊗̂ φ: k′ ⊗̂_k k⟨X₁, …, Xₙ⟩ → k′ ⊗̂_k B
showing that A ⊗̂_k B is k-affinoid and that k′ ⊗̂_k B is k′-affinoid, since the corresponding facts
obviously hold for the algebras A ⊗̂_k k⟨X₁, …, Xₙ⟩ and k′ ⊗̂_k k⟨X₁, …, Xₙ⟩ by Proposition 7. To verify the
remaining assertion, we view B as a k-Banach space. If {f₁, …, fₙ} is a system of affinoid generators of
B, then B contains k[f₁, …, fₙ] as a dense subspace. Thus we see that B is a Banach space of countable
type and that there is a linear homeomorphism of B onto c(k) or onto k^r if r := dim_k B < ∞ (Theorem
2.8.2/2). Since the inclusion map k ↪ k′ is strict and since the restricted direct product of normed vector
spaces commutes with the complete tensor product (Proposition 2.1.7/8), it follows that the canonical
homomorphism B → B ⊗̂_k k′ is a strict monomorphism."

"The category 𝔄 admits also complete tensor products of a more general type; namely the following holds:"

**Proposition 10 (6.1.1/10).** "Let B₁, B₂ ∈ 𝔄 be normed algebras over some algebra A ∈ 𝔄 via contractive
homomorphisms A → Bᵢ, i = 1, 2. Then also B₁ ⊗̂_A B₂, viewed as a k-algebra, belongs to 𝔄. If A′ → A is a
contractive homomorphism of k-affinoid algebras, the canonical homomorphism B₁ ⊗̂_{A′} B₂ → B₁ ⊗̂_A B₂ is
surjective."
*Proof.* "We start with the second assertion. According to Proposition 3.1.1/2, the canonical maps from B₁
and B₂ into B₁ ⊗̂_{A′} B₂, respectively B₁ ⊗̂_A B₂, induce a commutative diagram of contractive
homomorphisms [A′ → A → B₁, A′ → A → B₂, B₁ ⊗̂_{A′} B₂ →ψ B₁ ⊗̂_A B₂] and furthermore a commutative diagram
of contractive homomorphisms [A′ → A → B_i → (B₁ ⊗̂_{A′} B₂)/ker ψ ↪ B₁ ⊗̂_A B₂] (p. 226) where
(B₁ ⊗̂_{A′} B₂)/ker ψ is provided with the canonical residue norm (ker ψ is a closed ideal in
B₁ ⊗̂_{A′} B₂). It is a straightforward verification to see that the maps Bᵢ → (B₁ ⊗̂_{A′} B₂)/ker ψ,
i = 1, 2, satisfy the universal property stated in Proposition 3.1.1/2 which characterizes the complete
tensor product B₁ ⊗̂_A B₂. Hence (B₁ ⊗̂_{A′} B₂)/ker ψ → B₁ ⊗̂_A B₂ is an isomorphism showing that
B₁ ⊗̂_{A′} B₂ → B₁ ⊗̂_A B₂ is surjective. In particular, if A′ equals k and if A′ → A is the canonical map
k → A, it follows from Proposition 3 that B₁ ⊗̂_A B₂ is k-affinoid since B₁ ⊗̂_k B₂ is k-affinoid."

**Proposition 11 (6.1.1/11).** "In the situation of Proposition 10, let 𝔟ᵢ ⊂ Bᵢ, i = 1, 2, be ideals, and
denote by (𝔟₁, 𝔟₂) ⊂ B₁ ⊗̂_A B₂ the ideal generated by the images of 𝔟₁ and 𝔟₂ in B₁ ⊗̂_A B₂. Then the
canonical map π: B₁ ⊗̂_A B₂ → B₁/𝔟₁ ⊗̂_A B₂/𝔟₂ is surjective and satisfies ker π = (𝔟₁, 𝔟₂); hence, π
induces a strict isomorphism B₁ ⊗̂_A B₂/(𝔟₁, 𝔟₂) ≅ B₁/𝔟₁ ⊗̂_A B₂/𝔟₂."
*Proof.* "The map π is surjective by Proposition 2.1.8/6, and obviously (𝔟₁, 𝔟₂) ⊂ ker π. Hence π induces a
continuous homomorphism π′: (B₁ ⊗̂_A B₂)/(𝔟₁, 𝔟₂) → B₁/𝔟₁ ⊗̂_A B₂/𝔟₂. Furthermore, the canonical maps
Bᵢ → B₁ ⊗̂_A B₂ induce maps Bᵢ/𝔟ᵢ → B₁ ⊗̂_A B₂/(𝔟₁, 𝔟₂), i = 1, 2. Just as in the preceding proof, it is not
hard to see that these induced maps satisfy the universal property characterizing the complete tensor
product B₁/𝔟₁ ⊗̂_A B₂/𝔟₂. Thus (B₁ ⊗̂_A B₂)/(𝔟₁, 𝔟₂) is k-affinoid and π′ is a strict isomorphism by
Proposition 3.1.1/2."

"As a consequence, we now have an explicit description of the complete tensor product over k in 𝔄.
Namely for T_m/𝔞, Tₙ/𝔟 ∈ 𝔄, it follows that
    T_m/𝔞 ⊗̂_k Tₙ/𝔟 = T_{m+n}/(𝔞, 𝔟).
Using the same technique as in Proposition 11, one shows that"

**Proposition 12 (6.1.1/12).** "Let A be a k-affinoid algebra, and let 𝔞 be an ideal in A. If k′ is a complete
field extending k, the canonical homomorphism of k′-affinoid algebras π: A ⊗̂_k k′ → (A/𝔞) ⊗̂_k k′ is
surjective, and ker π equals the ideal 𝔞′ generated by 𝔞 in A ⊗̂_k k′. Hence π induces a strict isomorphism
(A ⊗̂_k k′)/𝔞′ ≅ A/𝔞 ⊗̂_k k′."

(p. 226) "The category 𝔄 is not closed with respect to the operation of passing to rings of fractions. Set
A := T₁ = k⟨X⟩, S := {1, X, X², …}, and consider the ring A_S = {h = Σ_{ν > −∞} a_ν X^ν ; lim a_ν = 0} of
strictly convergent Laurent series with finite principal part. Then A_S provided with the norm
|h| := max {|a_ν|} is not complete. In (6.1.4), we shall see that the completion of A_S is again
k-affinoid."

(p. 227) **Remark.** "A closed k-Banach subalgebra of a k-affinoid algebra is not necessarily Noetherian and
hence not necessarily k-affinoid." [Example: A := {f ∈ T₂ ; f(0, X₂) ∈ k}, whose ideal generated by
X₁ X₂^i, i ≥ 0, is not finitely generated.]

"For each A ∈ 𝔄, we denote by 𝔐_A the category of all finite complete normed A-modules with continuous
A-module homomorphisms as morphisms. Since A is Noetherian, all results of (3.7.3) hold for this category.
Thus, we know that each submodule of a module M ∈ 𝔐_A is closed, that up to equivalence each finite
A-module can be uniquely provided with a complete A-module norm, and that each A-linear homomorphism
φ: M → M′, M, M′ ∈ 𝔐_A, is automatically continuous and strict."
