# BGR §3.7 Banach algebras (book pp. 163–168) and §1.2.4–1.2.5 (pp. 26–28) — hand transcription

Render files `bgr1/pNNN.pdf.png`; book page = PDF page − 8 for §3.7, − 6 for §1.2. Locators are
`bgr-3.7.md:<line>`.

## 3.7.1 Definition and examples (p. 163)

"For every field k with a complete non-Archimedean non-trivial valuation, we define as in the complex case"
**Definition 1 (3.7.1/1).** "A k-algebra with a complete k-algebra norm is called a k-Banach algebra."
"Any homomorphism of k-Banach algebras φ: B → A is, in particular, k-linear. Therefore by Proposition
2.1.8/2, such a map φ is continuous if and only if it is bounded. If 𝔞 is a closed ideal in a k-Banach
algebra A, it is easy to see that the residue algebra A/𝔞 provided with the residue norm is again a
k-Banach algebra (cf. Proposition 1.1.6/1, Remark 2 of (1.2.1) and Proposition 2.1.2/3).
Obviously k itself is a k-Banach algebra. Applying Propositions 1.4.1/2 and 1.4.1/3, we see that, for every
k-Banach algebra A, the algebra A⟨X⟩ of strictly convergent power series with coefficients in A is a
k-Banach algebra. Therefore the algebra k⟨X₁, …, Xₙ⟩ (the main object in the beginning of the following
part B) is a Banach algebra. Further simple examples are provided by finite extensions of k provided with
the spectral valuation. We already know that these extensions carry always the product topology and that
all subspaces are closed."

## 3.7.2 Finiteness and completeness of modules over a Banach algebra (pp. 163–164)

"The underlying vector space of a k-Banach algebra is a k-Banach space and the underlying ring is a
complete normed ring. Therefore we may apply the results of (1.2.4) and of (2.8). This leads to the
following proposition."

**Proposition 1 (3.7.2/1).** "Let A be a k-Banach algebra and let M be a normed A-module such that the
completion M̂ of M is a finite A-module. Then M is complete."
*Proof.* "There are elements x₁, …, xₙ ∈ M̂ such that the homomorphism π: Aⁿ → M̂ defined by
π(a₁, …, aₙ) := Σ aᵢ xᵢ is surjective. By BANACH's Theorem, π is open, and therefore Σ Ǎ xᵢ = π(Ǎⁿ) is a
neighborhood of 0 in M̂. Since M is dense in M̂, we have
    x_ν ∈ M + Σ_{μ=1}^{n} Ǎ x_μ   for ν = 1, …, n.
Now NAKAYAMA's Lemma 1.2.4/6 yields M = M̂."

(p. 164) "As an immediate consequence of this proposition, we have that all submodules of a Noetherian
complete normed module over a Banach algebra A are closed. This property characterizes the Noetherian
complete normed modules over A; more precisely"

**Proposition 2 (3.7.2/2).** "Let A be a k-Banach algebra and M a complete normed A-module. Then M is
Noetherian if and only if all submodules of M are closed. In particular, the ring A is Noetherian if and
only if all ideals in A are closed."
*Proof.* "We only have to show that M is Noetherian if all submodules are closed. Let M₁ ⊂ M₂ ⊂ … be an
ascending chain of submodules. Let M′ := ⋃ Mᵢ. Then M′ being a closed submodule of the complete module M
is a Baire space. Since all Mᵢ are closed, we have by BAIRE's Theorem the existence of an index i such that
Mᵢ contains a neighborhood of 0 in M′. This implies Mᵢ = M′; hence the chain becomes stationary."

## 3.7.3 The category 𝔐_A (pp. 164–165)

"In this section, A always denotes a Noetherian k-Banach algebra. We denote by 𝔐_A the category of all
finite complete normed A-modules with continuous A-linear maps as morphisms. Note that, by Corollary
2.1.8/3, such an A-linear map is continuous if and only if it is bounded. Since each M ∈ 𝔐_A is a
Noetherian A-module, we conclude from Proposition 3.7.2/2"
**Proposition 1 (3.7.3/1).** "Every submodule M′ of a module M ∈ 𝔐_A is closed. Therefore M′ ∈ 𝔐_A and
M/M′ ∈ 𝔐_A if M′ carries the induced norm and M/M′ the residue norm. Furthermore M₁ ⊕ M₂ ∈ 𝔐_A if
M₁, M₂ ∈ 𝔐_A."
**Proposition 2 (3.7.3/2).** "If M, M′ are objects of 𝔐_A, each A-linear map φ: M → M′ is continuous."
*Proof.* "Choose an epimorphism π: Aⁿ → M for a suitable n ∈ ℕ. Define φ′: Aⁿ → M′ by φ′ := φ ∘ π. Since
addition and scalar multiplication are continuous operations in normed modules, both maps π and φ′ are
continuous. Furthermore π is open (by BANACH's Theorem). Hence φ is continuous."
**Proposition 3 (3.7.3/3).** "Each finite A-module M can be provided with a complete A-module norm. All
such norms are equivalent."
*Proof.* "We only have to prove the existence of such a norm. Take any A-linear epimorphism π: Aⁿ → M. Since
Aⁿ ∈ 𝔐_A, the kernel ker π is closed. The residue norm on Aⁿ/ker π gives rise to a complete A-module norm
on M."
(p. 165) "Recall that a continuous map ξ: X → Y between topological spaces X, Y is called strict if the
topology of the subspace ξ(X) ⊂ Y (i.e., the topology on ξ(X) induced from Y) equals the quotient
topology with respect to the map X →ξ ξ(X). In particular, ξ is strict if ξ is open."
**Proposition 4 (3.7.3/4).** "A continuous k-linear map φ: X → Y between k-Banach spaces is strict if and
only if φ(X) is closed in Y."
**Corollary 5 (3.7.3/5).** "Each A-module homomorphism φ: M → M′, where M, M′ ∈ 𝔐_A, is strict."

## 3.7.4 Finite homomorphisms (pp. 166–167)

**Proposition 1 (3.7.4/1).** "Let A be a Noetherian k-Banach algebra, and let φ: A → B be a finite
k-algebra homomorphism from A into a k-algebra B. Then B is Noetherian and can be provided with a complete
A-algebra norm (which by Definition 3.7.1/1 makes B a k-Banach algebra) such that φ is continuous and
strict. All complete k-algebra norms on B such that φ is continuous are equivalent."
*Proof (sketch of the source).* "Since φ is finite, B is a finite A-module. By Proposition 3.7.3/3, we can
provide B with a complete A-module norm | |′. Then the map φ is contractive. In general | |′ will fail to
be a ring norm on B. However, the following is true: There exists a constant ϱ > 0 such that
|xy|′ ≤ ϱ |x|′ |y|′ for all x, y ∈ B. [… via a system of A-generators b₁, …, bₙ of B and
C := max |b_μ b_ν|′ …] Now we define for x ∈ B: |x| := sup_{y ∈ B − {0}} |xy|′/|y|′. Applying Proposition
1.2.1/2, we see that | | is a ring norm on B inducing (p. 167) the same topology as | |′. It is easy to
verify that | | is also an A-module norm. In particular, φ is continuous and hence strict by the results of
(3.7.3). It remains to be shown that each complete k-algebra norm | |* on B such that φ is continuous is
equivalent to | |. The k-linear map π: Aⁿ → B given by (a₁, …, aₙ) ↦ Σ φ(a_ν) b_ν is continuous with
respect to any such norm | |*. Therefore, due to BANACH's Theorem, we see that | |* must induce the
quotient topology with respect to π on B."
**Corollary 2 (3.7.4/2).** "Each finite continuous k-algebra homomorphism between Noetherian k-Banach
algebras is strict."

## 3.7.5 Continuity of homomorphisms (pp. 167–168)

"In this section we consider a class of k-Banach algebras with the property that all k-algebra
homomorphisms are automatically continuous."

**Proposition 1 (3.7.5/1).** "Let A, B be k-Banach algebras, and let Φ: A → B be a k-algebra homomorphism.
Assume that there is a family 𝔅 of ideals in B such that
    (i) each 𝔟 ∈ 𝔅 is closed in B and each inverse image Φ⁻¹(𝔟) is closed in A,
    (ii) for each 𝔟 ∈ 𝔅 one has dim_k B/𝔟 < ∞,
    (iii) ⋂_{𝔟 ∈ 𝔅} 𝔟 = (0).
Then Φ is continuous."
*Proof.* "Fix 𝔟 ∈ 𝔅 and denote by β the residue epimorphism B → B/𝔟. Define ψ: A → B/𝔟 by ψ := β ∘ Φ. Let
ψ̄: A/ker ψ → B/𝔟 be the injection induced by ψ. Then we have the commutative diagram [A →Φ B, A →ψ B/𝔟,
B →β B/𝔟, A/ker ψ →ψ̄ B/𝔟]. Obviously ker ψ = Φ⁻¹(𝔟). According to (i) and (ii), the residue spaces
A/ker ψ and B/𝔟 provided with the residue norms are finite-dimensional weakly cartesian k-vector spaces
(see Proposition 2.3.3/4). Therefore ψ̄ and hence ψ are continuous. Now we get the continuity of Φ from the
Closed Graph Theorem; namely, assume there is given a sequence aₙ ∈ A with lim aₙ = 0 and lim Φ(aₙ) = b.
Using the continuity of ψ and β, we get β(b) = β(lim Φ(aₙ)) = lim (β ∘ Φ)(aₙ) = lim ψ(aₙ) = ψ(lim aₙ)
= ψ(0) = 0, i.e., b ∈ 𝔟. Since this holds for all 𝔟 ∈ 𝔅, we deduce b = 0 from (iii). This implies the
continuity of Φ."

"From Propositions 1 and 3.7.2/2, we easily derive"
**Proposition 2 (3.7.5/2).** "Let B be a Noetherian k-Banach algebra with a family 𝔅 of ideals of B such
that (i) dim_k B/𝔟 < ∞ for all 𝔟 ∈ 𝔅, (ii) ⋂_{𝔟 ∈ 𝔅} 𝔟 = (0). (p. 168) Then each k-algebra homomorphism
of a Noetherian k-Banach algebra A into B is continuous."

**Proposition 3 (3.7.5/3).** "All complete k-algebra norms (if there exist any) on a Noetherian k-algebra
B with a family 𝔅 of ideals satisfying conditions (i) and (ii) of the preceding proposition are
equivalent, i.e., all Banach algebra structures on B have the same underlying topological space. In
particular, B admits at most one power-multiplicative complete norm."
"The above results are somewhat amazing, insofar as purely algebraic conditions have topological
implications. A special case of Proposition 3 is of course the earlier result that a finite extension of k
has at most one valuation extending the valuation on k."

## 1.2.4 Topologically nilpotent elements and complete normed rings (pp. 26–28)

**Definition 1 (1.2.4/1).** "An element a ∈ A is called topologically nilpotent if lim aⁿ = 0. The set of
all topologically nilpotent elements of A is denoted by Ǎ."
(p. 27) "Obviously, A^∨ ⊂ Ǎ. Since 1 ∉ Ǎ (unless |A| = {0}), we see that A° is not, in general, contained
in Ǎ. The set Ǎ depends only on the topology of A."
**Proposition 2 (1.2.4/2).** "The set Ǎ is a subgroup of A⁺, which is multiplicatively closed. Furthermore,
Ǎ is open and closed with respect to the topology of A."
**Corollary 3 (1.2.4/3).** "If A is complete, then Ǎ is complete."
**Proposition 4 (1.2.4/4).** "If A is complete, each element of the form e = 1 − y, y ∈ Ǎ, is a unit in A.
We have e⁻¹ = Σ_{0}^{∞} yⁿ = 1 + z, where z ∈ Ǎ."
"Note that Proposition 4 remains true if one replaces Ǎ by A^∨."
**Corollary 5 (1.2.4/5).** "In a complete normed ring A, the multiplicative group E(A) of units is open.
Consequently, all maximal ideals of A are closed."
"Another important consequence of Proposition 4 is the following "NAKAYAMA Lemma", which allows us to
derive equations from congruences modulo topologically nilpotent elements."
**Lemma 6 (1.2.4/6).** "Let A be complete and let M be an A-module. Let N be a submodule of M such that
there are elements x₁, …, xₙ in M with the property: M ⊂ N + Σ_{μ=1}^{n} Ǎ x_μ. Then N = M."
*Proof.* (p. 28) "By assumption there are elements c_{νμ} ∈ Ǎ and y_ν ∈ N such that
    x_ν = y_ν + Σ_{μ=1}^{n} c_{νμ} x_μ,   ν = 1, …, n.
If we denote by x (resp. y) the column vector with entries x_ν (resp. y_ν) and by I (resp. C) the n × n
unit matrix (resp. the n × n matrix with entries c_{νμ}), we have y = (I − C) x. If we can show that the
matrix I − C is invertible, we get x = (I − C)⁻¹ y. Thus, x₁, …, xₙ ∈ N, and M ⊂ N. Using CRAMER's rule,
it is enough to show that det(I − C) is a unit in A. But clearly det(I − C) is of the form 1 − c with
c ∈ Ǎ (since Ǎ is closed under the algebraic operations performed in computing the determinant). Hence
Proposition 4 gives det(I − C) ∈ E(A)."

## 1.2.5 Power-bounded elements (p. 28)

**Definition 1 (1.2.5/1).** "An element a ∈ A is called power-bounded if the set {|aⁿ| ; n ∈ ℕ} ⊂ ℝ₊ is
bounded. We denote by Å the set of all power-bounded elements of A."
**Proposition 2 (1.2.5/2).** "The set Å is a subring of A and Ǎ is an ideal in Å. The subring Å is open and
closed in A."
*Proof.* "Let a, b ∈ Å. Choose M > 0 such that, for all n ∈ ℕ, |aⁿ| ≤ M, |bⁿ| ≤ M. We conclude
|(ab)ⁿ| ≤ |aⁿ| |bⁿ| ≤ M², and |(a − b)ⁿ| ≤ max_{0 ≤ ν ≤ n} {|a^ν| |b^{n−ν}|} ≤ M². Since 1 ∈ Å, we see that
Å is a subring of A. If a ∈ Ǎ, b ∈ Å, then |(ab)ⁿ| ≤ |aⁿ| |bⁿ| ≤ |aⁿ| M → 0 — i.e., ab ∈ Ǎ. So Ǎ is an
ideal in Å. Å is a subgroup of A and contains Ǎ, which is open in A. Hence Å is open and closed in A."

## 7.2.5 Affinoid generating systems over an affinoid algebra (p. 287)

"In the following the map σ: A → B denotes a homomorphism between affinoid algebras. A system
b = (b₁, …, bₙ) of power-bounded elements in B is called an affinoid generating system of B over A if the
continuous homomorphism σ₁: A⟨ζ₁, …, ζₙ⟩ → B extending σ and mapping ζᵢ onto bᵢ, for i = 1, …, n, (cf.
Proposition 6.1.1/4) is surjective. Recall that affinoid generating systems (over k) were already
introduced in (6.1.1). Each affinoid generating system of B over k is an affinoid generating system of B
over A. In particular, affinoid generating systems of the considered type do exist in general."
