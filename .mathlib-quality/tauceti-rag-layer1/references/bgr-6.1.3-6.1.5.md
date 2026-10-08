# BGR §6.1.3–§6.1.5 (book pp. 229–236) — hand transcription from the scan

Render files `bgr1/pNNN.pdf.png` show book page NNN − 6. Locators are `bgr-6.1.3-6.1.5.md:<line>`.

## 6.1.3 Continuity of homomorphisms (pp. 229–230)

(p. 229) "We now apply the general results on k-Banach algebras of (3.7.5) to k-affinoid algebras. The
following remark is crucial:
For each k-affinoid algebra B ∈ 𝔄, the set
    𝔅 := {𝔪^ν ; 𝔪 maximal ideal in B, ν ∈ ℕ}
fulfills conditions (i) and (ii) of Proposition 3.7.5/2. Namely,
    (i) dim_k B/𝔟 < ∞ for each 𝔟 ∈ 𝔅,
    (ii) ⋂_{𝔟 ∈ 𝔅} 𝔟 = (0)."
*Proof.* "We have dim_k B/𝔟 < ∞ for all 𝔟 ∈ 𝔅 by Corollary 6.1.2/3. In order to show ⋂ 𝔟 = (0), take any
f ∈ B such that f ∈ ⋂_{ν ≥ 1} 𝔪^ν for all maximal ideals 𝔪 ⊂ B. KRULL's Intersection Theorem implies that
for each 𝔪 there is an element m ∈ 𝔪 such that (1 − m) f = 0. Hence the annihilator of f is contained in
no maximal ideal in B. Therefore, f = 0 and (ii) holds."

"Since each B ∈ 𝔄 is Noetherian, we derive from Proposition 3.7.5/2"

**Theorem 1 (6.1.3/1).** "Each k-algebra homomorphism of a Noetherian k-Banach algebra into a k-affinoid
algebra is continuous."

"This theorem tells us for the category 𝔄 of k-affinoid algebras that (similarly as in the category of
finite modules over a k-affinoid algebra A) one need not bother about questions of continuity. Each
morphism is automatically continuous. Furthermore, a k-algebra can carry at most one k-affinoid structure,
since the identity map must be continuous in both directions. Actually a stronger result holds:"

**Proposition 2 (6.1.3/2).** "If A is k-affinoid, then any k-Banach algebra topology on the k-algebra A
coincides with the k-affinoid topology of A."
*Proof.* "The assertion is a direct consequence of Proposition 3.7.5/3."

"We can strengthen Theorem 1 also in the following way."

**Proposition 3 (6.1.3/3).** "Let φ: B → A be a homomorphism of k-affinoid algebras. Then the algebra norm
on A can be replaced by an equivalent one such that φ becomes contractive, and thus A becomes a normed
B-algebra."
*Proof.* "Let a₁, …, aₙ ∈ A denote affinoid generators of A. Then according to Proposition 6.1.1/4, the map
φ extends uniquely to a continuous homomorphism ψ: B⟨X₁, …, Xₙ⟩ → A such that ψ(Xᵢ) = aᵢ, i = 1, …, n. The
map ψ (p. 230) is obviously surjective and hence open by BANACH's Theorem. Therefore, the residue norm via
ψ is equivalent to the original norm on A; thus ψ and, in particular, φ are contractive with respect to
this norm on A."

(p. 230) "Consequently, for arbitrary homomorphisms B → A₁ and B → A₂ of k-affinoid algebras, the complete
tensor product A₁ ⊗̂_B A₂ can be constructed by taking suitable norms on A₁ and A₂. The B-algebra
A₁ ⊗̂_B A₂ is then k-affinoid by Proposition 6.1.1/10. Moreover, according to Proposition 2.1.8/5,
equivalent norms on A₁ and A₂ (and even on B as a simple computation shows) lead to equivalent norms on
A₁ ⊗̂_B A₂. Thus, in our situation, A₁ ⊗̂_B A₂ is a well-defined k-affinoid algebra, uniquely determined
up to isomorphism."

**Proposition 4 (6.1.3/4).** "Let φ: B → A be a finite homomorphism of a k-affinoid algebra B into a
k-Banach algebra A. Then φ is strict and A is k-affinoid."
*Proof.* "According to Proposition 6.1.1/6 the k-algebra A can be provided with a complete k-algebra norm
such that φ is strict and A is k-affinoid with respect to this new norm. From Proposition 2, we conclude
that the corresponding k-affinoid topology of A coincides with the given Banach topology."

**Remark.** "We see that the category 𝔄 could also have been defined as the category of all k-Banach
algebras A permitting a finite (not necessarily surjective and continuous) homomorphism from some Tₙ into
A. Furthermore, this category is equivalent to the (purely algebraic) category of all k-algebras which are
finite over some Tₙ."

## 6.1.4 Examples. Generalized rings of fractions (pp. 230–234)

(p. 230) "If A is a k-affinoid algebra with norm | | and if X = (X₁, …, X_m) denotes a system of
indeterminates, then the ring A⟨X⟩ of strictly convergent power series over A is k-affinoid. Similarly one
can consider strictly convergent Laurent series; define
    A⟨X, X⁻¹⟩ := {Σ_{νᵢ ∈ ℤ} a_{ν₁…ν_m} X₁^{ν₁} … X_m^{ν_m} ; a_ν ∈ A and |a_ν| → 0 for |ν₁| + ⋯ + |ν_m| → ∞}.
If Σ a_ν X^ν and Σ b_μ X^μ are elements of A⟨X, X⁻¹⟩, then c_λ := Σ_{ν+μ=λ} a_ν b_μ converges for all
λ ∈ ℤ and Σ_λ c_λ X^λ is again an element of A⟨X, X⁻¹⟩. Thus, it is easily verified that A⟨X, X⁻¹⟩ is a
k-Banach algebra with the norm given by |Σ a_ν X^ν| := max |a_ν|. Furthermore, A⟨X, X⁻¹⟩ is even
k-affinoid. Namely, let Y = (Y₁, …, Y_m) denote a second system of indeterminates. Then, according to
Proposition 6.1.1/4, the injection A⟨X⟩ → A⟨X, X⁻¹⟩ extends to a homomorphism A⟨X, Y⟩ → A⟨X, X⁻¹⟩,
Y ↦ X⁻¹, which is obviously surjective."

(p. 231) "The k-affinoid algebra A⟨X, X⁻¹⟩ contains, in particular, the ring A⟨X⟩[X⁻¹] which stands for the
localization of A⟨X⟩ by X, and it is clear that A⟨X⟩[X⁻¹] is dense in A⟨X, X⁻¹⟩. Hence, in some sense,
A⟨X, X⁻¹⟩ is the "smallest" k-affinoid algebra over A⟨X⟩ such that X₁, …, X_m become units. We want to
carry out similar constructions in a more general situation.
As before, let A denote a k-affinoid algebra, and let f = (f₁, …, f_m) and g = (g₁, …, gₙ) be systems of
elements in A. We are looking for a k-Banach algebra A′ over A such that the gⱼ become units and the fᵢ,
gⱼ⁻¹ are power-bounded in A′. In order to give a construction for A′, we start with the ring of fractions
A[g⁻¹]. Any element a ∈ A[g⁻¹] can be written as a finite sum
    a = Σ_{μᵢ, νⱼ ≥ 0} a_{μν} f^μ g^{−ν},   a_{μν} ∈ A,
and we define a semi-norm on A[g⁻¹] by
    |a| = inf (max_{μ,ν} |a_{μν}|),
where the infimum runs over all possible representations of a. Note that this semi-norm on A[g⁻¹] depends
not only on the system g but also on the system f. It is a natural semi-norm such that the elements of f
and g⁻¹ become power-bounded. Hence A⟨f, g⁻¹⟩, the completion of A[g⁻¹], is a k-Banach algebra over A,
which has the properties we are looking for. We will see below that A⟨f, g⁻¹⟩ is even k-affinoid;
however, first note that, by construction, the canonical map A → A⟨f, g⁻¹⟩ satisfies the following
universal property."

**Proposition 1 (6.1.4/1).** "Let φ: A → B denote a continuous homomorphism from the k-affinoid algebra A
into a k-Banach algebra B such that the elements φ(gⱼ) are units and the elements φ(fᵢ), φ(gⱼ)⁻¹ are
power-bounded. Then there is a unique continuous homomorphism φ′: A⟨f, g⁻¹⟩ → B such that the diagram
[A → A⟨f, g⁻¹⟩, φ: A → B, φ′: A⟨f, g⁻¹⟩ → B] commutes."

"In particular, if A is replaced by the algebra A⟨X⟩ of strictly convergent power series in
X = (X₁, …, X_m), and if f := ∅ and g := X, we see that the algebra A⟨X⟩⟨X⁻¹⟩ is canonically isomorphic to
the algebra A⟨X, X⁻¹⟩ of strictly convergent Laurent series in X. Namely, both algebras satisfy the same
universal property. (The isomorphism can also be obtained by a direct argument.) We always use the notation
A⟨X, X⁻¹⟩ instead of A⟨X⟩⟨X⁻¹⟩.
Returning to the general case, there is another possible way to construct a k-Banach algebra A′ over A
satisfying the required properties. Let X = (X₁, …, X_m) and Y = (Y₁, …, Yₙ) denote systems of
indeterminates. Then (p. 232) A′ := A⟨X, Y⟩/(X − f, gY − 1) is obviously a k-Banach and even a k-affinoid
algebra over A such that the gⱼ become units and the fᵢ, gⱼ⁻¹ are power-bounded in A′. Furthermore, the
canonical map A → A⟨X, Y⟩/(X − f, gY − 1) also satisfies the universal property stated in Proposition 1.
Namely, let φ: A → B be a continuous homomorphism as in Proposition 1. Then φ extends to a continuous
homomorphism φ″: A⟨X, Y⟩ → B, X ↦ φ(f), Y ↦ φ(g)⁻¹, with
    (X − f, gY − 1) ⊂ ker φ″.
Thus φ″ gives rise to a continuous homomorphism φ′: A⟨X, Y⟩/(X − f, gY − 1) → B such that the diagram
[A → A⟨X, Y⟩/(X − f, gY − 1), φ, φ′ into B] commutes, and φ′ is uniquely determined by this diagram since
the residue classes of X and Y must be mapped by φ′ onto φ(f) and φ(g)⁻¹ respectively. In particular,
taking B := A⟨f, g⁻¹⟩, we get"

**Proposition 2 (6.1.4/2).** "The continuous homomorphism A⟨X, Y⟩ → A⟨f, g⁻¹⟩, X ↦ f, Y ↦ g⁻¹, is surjective
and gives rise to a strict isomorphism A⟨X, Y⟩/(X − f, gY − 1) ≅ A⟨f, g⁻¹⟩."

"Providing A⟨X, Y⟩/(X − f, gY − 1) with the canonical residue norm, it is not hard to see that the above
isomorphism is in fact isometric. In particular, it is now clear that A⟨f, g⁻¹⟩ is k-affinoid.
A few remarks concerning the notation A⟨f, g⁻¹⟩ = A⟨f₁, …, f_m, g₁⁻¹, …, gₙ⁻¹⟩ seem to be necessary. In the
case where g = ∅, we simply write A⟨f⟩ instead of A⟨f, g⁻¹⟩; likewise we write A⟨g⁻¹⟩ if f = ∅. Note also
that A⟨h⁻¹⟩ is defined in two ways when h ∈ A is a unit. However, no difficulties will arise from that,
since both definitions coincide in this special case. Finally it follows from Proposition 2 that we have
associativity in the following sense:
    A⟨f₁, …, f_{m−1}, g₁⁻¹, …, g_{n−1}⁻¹⟩⟨f_m, gₙ⁻¹⟩ = A⟨f₁, …, f_m, g₁⁻¹, …, gₙ⁻¹⟩."

(p. 232) "There is another procedure which partially generalizes the above one. Let g, f₁, …, f_m ∈ A be
elements generating the unit ideal in A; i.e., there are elements a, a₁, …, a_m ∈ A such that
    a g + Σ_{i=1}^{m} aᵢ fᵢ = 1.
We are looking for a k-Banach algebra A′ over A such that g becomes a unit and such that the fractions
fᵢ/g are power-bounded in A′. Since, in the ring of fractions A[g⁻¹], we have g⁻¹ = a + Σ aᵢ fᵢ/g,
(p. 233) it is clear that any element b ∈ A[g⁻¹] can be written as a finite sum
    b = Σ b_ν (f/g)^ν,   b_ν ∈ A,
where f/g stands for the system (f₁/g, …, f_m/g). Similarly as before, one defines a semi-norm on A[g⁻¹]
by |b| = inf (max |b_ν|), where the infimum runs over all possible representations of b. The completion of
A[g⁻¹] is denoted by A⟨f/g⟩; it is a k-Banach algebra having the properties we are looking for.
Furthermore, the canonical map A → A⟨f/g⟩ satisfies the following universal property:"

**Proposition 3 (6.1.4/3).** "Let φ: A → B denote a continuous homomorphism from the k-affinoid algebra A
into the k-Banach algebra B such that φ(g) is a unit and the elements φ(fᵢ)/φ(g) are power-bounded. Then
there is a unique continuous homomorphism φ′: A⟨f/g⟩ → B such that the diagram [A → A⟨f/g⟩, φ, φ′ into B]
commutes."

"Also in this case, we want to have an explicit description of A⟨f/g⟩ which shows that it is k-affinoid.
Let X = (X₁, …, X_m) be a system of indeterminates, and consider the k-affinoid algebra
A′ = A⟨X⟩/(gX − f). With X̄ᵢ denoting the residue class of Xᵢ in A′, we get
    (a + Σ_{i=1}^{m} aᵢ X̄ᵢ) g = a g + Σ aᵢ fᵢ = 1
which shows that g is a unit in A′. Moreover, X̄ᵢ = fᵢ/g in A′; hence, the elements fᵢ/g must be
power-bounded in A′. It is now a straightforward verification to see that also A′ = A⟨X⟩/(gX − f)
satisfies the universal property stated in Proposition 3. Thus we get"

**Proposition 4 (6.1.4/4).** "The continuous homomorphism A⟨X⟩ → A⟨f/g⟩, X ↦ f/g, is surjective and gives
rise to a strict isomorphism A⟨X⟩/(gX − f) → A⟨f/g⟩."

(p. 234) "Again, providing A⟨X⟩/(gX − f) with the canonical residue norm, one shows that the above
isomorphism is isometric. Note also that our definition of A⟨f/g⟩ is compatible with the one given
before, if the fᵢ or g are units."

## 6.1.5 Further examples. Convergent power series on general polydiscs (pp. 234–236)

(p. 234) "Let X = (X₁, …, Xₙ) be a set of indeterminates, and let ϱ be an n-tuple of positive real
numbers. It is clear that a formal power series f = Σ a_ν X^ν ∈ k[[X]] is convergent on the polydisc P_ϱ
if lim |a_ν| ϱ^ν = 0. Conversely, if the components of ϱ belong to |k*|, any series converging on P_ϱ
must satisfy this condition. Therefore we define
    T_{n,ϱ} = {Σ a_ν X^ν ∈ k[[X]] ; lim |a_ν| ϱ^ν = 0}.
In particular, T_{n,ϱ} = Tₙ if ϱ = (1, …, 1). Generalizing the Gauss norm on Tₙ, we set for any
f = Σ a_ν X^ν ∈ T_{n,ϱ}
    |f|_ϱ := max |a_ν| ϱ^ν.
Then, similarly as in the case ϱ = (1, …, 1), one shows that"

**Proposition 1 (6.1.5/1).** "The series in T_{n,ϱ} form a k-subalgebra of k[[X]]. The map | |_ϱ is a
k-algebra norm on T_{n,ϱ}, making it a k-Banach algebra, which contains k[X] as a dense subalgebra."

"Furthermore, an argument similar to the one used in the classical proof of the GAUSS Lemma (see (1.5.3))
shows that, in fact,"

**Proposition 2 (6.1.5/2).** "The norm | |_ϱ is a valuation on T_{n,ϱ}."

"If ϱ consists of a tuple of numbers in |k*|, then by definition, T_{n,ϱ} consists of precisely those
power series f ∈ k[[X]] which converge on the polydisc P_ϱ(k). This assertion cannot be maintained if not
all components of ϱ belong to |k*|. For example if n = 1 and ϱ ∉ |k*|, then convergence on
P_ϱ(k) = B⁺(0, ϱ) is the same as convergence on B⁻(0, ϱ). However there are power series f = Σ a_ν X^ν
converging on B⁻(0, ϱ), which do not satisfy the condition lim |a_ν| ϱ^ν = 0, so that f ∉ T_{1,ϱ} in this
case.
As a by-product of Proposition 2, it follows that there are valued fields k′ extending k such that |k′|
contains arbitrary prescribed values ϱ₁, …, ϱₙ > 0. Just take for k′ the field of fractions of T_{n,ϱ}.
Thereby we see that"

**Proposition 3 (6.1.5/3).** (p. 235) "The algebra T_{n,ϱ} consists of precisely those series f ∈ k[[X]]
such that f converges on P_ϱ(k′) for all complete fields k′ extending k."

"We want to characterize the tuples ϱ, for which T_{n,ϱ} is k-affinoid. Of course if ϱ = (|c₁|, …, |cₙ|),
where c₁, …, cₙ ∈ k*, then Tₙ → T_{n,ϱ}, Xᵢ ↦ cᵢ⁻¹ Xᵢ, defines an isometric isomorphism between Tₙ and
T_{n,ϱ} so that T_{n,ϱ} is k-affinoid in this case. In order to deal with the general case, let k_a be the
algebraic closure of k. Then a positive real α belongs to |k_a*| if and only if α^s ∈ |k*| for some
s ∈ ℕ."

**Theorem 4 (6.1.5/4).** "The algebra T_{n,ϱ} is k-affinoid if and only if all components ϱᵢ of ϱ belong
to |k_a*|."
*Proof.* "First assume that there are s₁, …, sₙ ∈ ℕ and c₁, …, cₙ ∈ k* such that ϱᵢ^{sᵢ} = |cᵢ⁻¹| for
i = 1, …, n. Then |cᵢ Xᵢ^{sᵢ}|_ϱ = 1, and we can define a monomorphism φ: Tₙ → T_{n,ϱ} by setting
φ(Xᵢ) := cᵢ Xᵢ^{sᵢ}, i = 1, …, n (see Proposition 6.1.1/4). We claim that φ is finite. Take f = Σ a_ν X^ν
∈ T_{n,ϱ} and write
    f = Σ_{λ, 0 ≤ λᵢ < sᵢ} X^λ ( Σ_{μ, 0 ≤ μᵢ} a_{μs+λ} c^{−μ} (c X^s)^μ ),
where λ = (λ₁, …, λₙ), μ = (μ₁, …, μₙ), s = (s₁, …, sₙ), and c = (c₁, …, cₙ). For each λ with
0 ≤ λᵢ < sᵢ, define
    g_λ := Σ_μ (a_{μs+λ} c^{−μ}) X^μ ∈ k[[X]].
Then g_λ ∈ Tₙ, since
    |a_{μs+λ} c^{−μ}| = |a_{μs+λ}| ϱ^{μs} = |a_{μs+λ}| ϱ^{μs+λ} ϱ^{−λ} → 0
as |μ| → ∞. We have f = Σ_{λ, 0 ≤ λᵢ < sᵢ} φ(g_λ) X^λ so that T_{n,ϱ} is a finite Tₙ-module via φ; the
monomials X^λ, 0 ≤ λᵢ < sᵢ, i = 1, …, n, are generators. Thus, T_{n,ϱ} is k-affinoid by Proposition
6.1.1/5, and half of the theorem is proved.
To show the other half, assume that T_{n,ϱ} is k-affinoid. Choose a finite normalization monomorphism
φ: T_d → T_{n,ϱ}. Then φ is strict by Proposition 6.1.3/4. Furthermore, φ must be an isometry, because both
norms | | (on T_d) and | |_ϱ (on T_{n,ϱ}) are power-multiplicative (use Proposition 3.1.5/1). Thus we can
apply Proposition 3.1.5/2 and thereby find integers s₁, …, sₙ ∈ ℕ satisfying ϱᵢ^{sᵢ} = |Xᵢ|^{sᵢ} ∈
|Q(T_d)| = |k| for i = 1, …, n."

**Remark.** "If one uses the results of (6.2), the above ad hoc proof for the second part of the theorem
can be replaced by the following consideration. If T_{n,ϱ} is k-affinoid, the power-multiplicative norm
| |_ϱ must coincide with the supremum norm | |_sup on T_{n,ϱ}; the supremum norm takes values only in the
value group of the algebraic closure of k."

(p. 236) **Proposition 5 (6.1.5/5).** "If all components ϱᵢ of ϱ belong to |k_a*|, then the norm | |_ϱ
coincides with the supremum norm | |_sup on T_{n,ϱ}, and T_{n,ϱ} is a Banach function algebra."
*Proof.* "Choose a finite algebraic extension k′ of k such that ϱ₁, …, ϱₙ ∈ |k′| and consider T_{n,ϱ}(k)
as a k-subalgebra of T_{n,ϱ}(k′) (we add k, respectively k′, in brackets in order to specify the ground
field). Then T_{n,ϱ}(k′), considered as a k′-algebra, is a Banach function algebra, because there is an
isometric k′-isomorphism Tₙ(k′) → T_{n,ϱ}(k′), and because Tₙ(k′) is a Banach function algebra (Corollary
5.1.4/6). Since the k-algebraic and the k′-algebraic maximal ideals coincide in Tₙ(k′) (k′ is finite over
k), we see that T_{n,ϱ}(k′) is also a Banach function algebra over k. Since T_{n,ϱ}(k) is closed in
T_{n,ϱ}(k′), it follows from Lemma 3.8.3/4 that T_{n,ϱ}(k) is a Banach function algebra."

"Actually, the assumption of Proposition 5 is superfluous. This relies on the fact that one has
|f|_ϱ = sup {|f(x)| ; x ∈ P_ϱ(k_a)} for all f ∈ T_{n,ϱ} (where k_a is the algebraic closure of k). Knowing
this, one can conclude along the lines of the proof of Corollary 5.1.4/6 in order to see that T_{n,ϱ} is
a Banach function algebra. Furthermore, T_{n,ϱ} satisfies the Maximum Modulus Principle if and only if
the above supremum is always assumed. This is equivalent to the fact that T_{n,ϱ} is k-affinoid."
