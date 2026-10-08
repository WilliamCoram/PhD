# BGR §6.2 "The spectrum of a k-affinoid algebra and the supremum semi-norm" (book pp. 236–242)
# and §6.3 intro + §6.3.1 "Monomorphisms, isometries and epimorphisms" (book pp. 242–245)
# — hand transcription from the scan (PDF page = book page + 6 in chapter 6; renders bgr2/p242–p251)

Notation: `| |_sup` is the supremum semi-norm, `Max A` the maximal spectrum, `Å` the power-bounded
elements, `Ǎ` the topologically nilpotent elements, `Ã = Å/Ǎ`, `red A = A/rad A`, `k_a` the
algebraic closure of k, `σ(q) = max |b_i|^{1/i}` the spectral value of a monic polynomial
`q = Xⁿ + b₁Xⁿ⁻¹ + ⋯ + bₙ`.

## 6.2.1 The supremum semi-norm (pp. 236–238)

p. 236: "Let A denote an arbitrary k-affinoid algebra. We want to introduce an intrinsic semi-norm on
every such algebra A, not depending on the incidental representation of A as a residue algebra of
some algebra Tₙ. Such an intrinsic semi-norm is already at our disposal: we take the supremum
semi-norm | |_sup as defined and studied in (3.8). For the convenience of the reader, we repeat some
of the relevant material given there and adapt it to our special situation.

According to Corollary 6.1.2/3, all maximal ideals in a k-affinoid algebra A are k-algebraic.
Therefore the supremum semi-norm is computed using the *whole* spectrum of maximal ideals Max A.
Furthermore, because A is a k-Banach algebra, Corollary 3.8.2/2 yields that | |_sup is finite;
more precisely, |f|_sup ≤ |f|_α for all f ∈ A and all epimorphisms α: Tₙ → A. Thus using Lemma
3.8.1/3, we see that"

**Lemma 1 (6.2.1/1).** "The function | |_sup: A → ℝ₊ defined by
    |f|_sup := sup_{x ∈ Max A} |f(x)|,  f ∈ A,
is a power-multiplicative k-algebra semi-norm."

**Definition 2 (6.2.1/2), p. 237.** "This semi-norm is called the supremum (or the spectral)
semi-norm on A. It is also referred to as the semi-norm of uniform convergence on Max A."

p. 237: "Let red A = A/rad A denote the nilreduction of A, and let red: A → red A be the canonical
residue map. Since A is Noetherian, there are only finitely many minimal prime ideals 𝔭₁, …, 𝔭_r
in A. Let π_i: A → A/𝔭_i, i = 1, …, r, denote the canonical residue maps. With these notations we
state the following lemma which allows us to reduce problems concerning affinoid algebras with zero
divisors to integral domains."

**Lemma 3 (6.2.1/3).** "For each f ∈ A, one has
    |f|_sup = max_{1≤i≤r} |π_i(f)|_sup   and   |f|_sup = |red f|_sup."

*Proof.* "The first equation is the assertion of Lemma 3.8.1/5. The second one follows from the fact
that the nilradical rad A is contained in each maximal ideal of A. □"

p. 237: "According to Corollary 5.1.4/6, the spectral semi-norm coincides with the Gauss norm on Tₙ.
This fact allows us — by means of Proposition 3.8.1/7 — to extend some of our results on free Tate
algebras to general affinoid algebras. Let k_a be the algebraic closure of k."

**Proposition 4 (6.2.1/4).**
"(i) The Maximum Modulus Principle holds for | |_sup on each k-affinoid algebra A.
(ii) For all f ∈ A such that |f|_sup ≠ 0, there are c ∈ k and m ∈ ℕ such that |cf^m|_sup = 1.
Consequently, |A|_sup ⊂ |k_a|.
(iii) An element f ∈ A is nilpotent if and only if |f|_sup = 0. In particular, | |_sup is a norm on
A if and only if A is reduced."

*Proof.* "Let us first consider the special case, where A is an integral domain. Applying the
Noether Normalization Lemma (Corollary 6.1.2/2), we find a finite monomorphism φ: T_d → A for some
d ≥ 0. Since T_d is integrally closed (Theorem 5.2.6/2) and since the Maximum Modulus Principle
holds for T_d (Corollary 5.1.4/6), assertions (i) and (ii) follow from Proposition 3.8.1/7.
Furthermore, this proposition shows that | |_sup is a norm on A (since | |_sup is a norm on T_d).

Now let A be arbitrary. Denote by 𝔭₁, …, 𝔭_r the minimal prime ideals in A. By what we have just
seen, assertions (i) and (ii) are true for the algebras A/𝔭_i, i = 1, …, r. Thus by Lemma 3, they
must also be true for A. Furthermore it follows that | |_sup is a norm on red A = A/rad A, since
rad A = ⋂_{i=1}^r 𝔭_i. Therefore assertion (iii) is clear by Lemma 3. □"

p. 237: "Combining assertion (iii) of the above proposition with the assertion of Proposition
3.8.2/3, we get the following improvement of Theorem 6.1.3/1 for reduced k-affinoid algebras."

**Corollary 5 (6.2.1/5), p. 238.** "If A is a reduced k-affinoid algebra, then each homomorphism of
a (not necessarily Noetherian) k-Banach algebra into A is continuous."

**Remark (p. 238).** "The assertion (iii) of Proposition 4 simply says that rad A = ⋂_{𝔪 ∈ Max A} 𝔪.
If A ≅ Tₙ/𝔞, where 𝔞 is an ideal in the free Tate algebra Tₙ, this is equivalent to
rad 𝔞 = ⋂_{𝔪 ∈ Max Tₙ, 𝔞 ⊂ 𝔪} 𝔪. Thus assertion (iii) of Proposition 4 is equivalent to the fact
that each Tₙ is a Jacobson ring. (The latter has already been obtained in Theorem 5.2.6/3. The
proof of this theorem can be viewed as a refinement of the detailed considerations in (3.8) which
led to the proof of Proposition 4.)"

## 6.2.2 Integral homomorphisms (pp. 238–239)

p. 238: "Some facts from (3.8) about integral homomorphisms have already implicitly been used in the
preceding section. Here we want to write down explicitly some properties of such homomorphisms.
First, Lemmata 3.8.1/4 and 3.8.1/6 yield"

**Proposition 1 (6.2.2/1).** "Every homomorphism of k-affinoid algebras φ: B → A is a contraction
with respect to the supremum semi-norm. If φ is an integral monomorphism, it is an isometry."

p. 238: "Since T_d is a valued integrally closed domain, we can derive from Proposition 3.8.1/7 (a)
and (d) the following result."

**Proposition 2 (6.2.2/2).** "Let φ: T_d → A be an integral torsion-free monomorphism into some
k-affinoid algebra A. Then | |_sup is a faithful T_d-algebra norm on A (i.e.,
|φ(t) f|_sup = |t| |f|_sup for all f ∈ A and all t ∈ T_d). If
    fⁿ + φ(t₁) fⁿ⁻¹ + ⋯ + φ(tₙ) = 0
is the integral equation of minimal degree for f over T_d, then one has
    |f|_sup = max_{1≤i≤n} |t_i|^{1/i}."

p. 238: "We want to extend the equation |f|_sup = max |t_i|^{1/i} to the case where φ: B → A is an
arbitrary integral homomorphism of k-affinoid algebras. We need a simple lemma, which is closely
related to Proposition 3.1.2/1."

**Lemma 3 (6.2.2/3), pp. 238–239.** "Let φ: B → A be a homomorphism of k-affinoid algebras. Let
f ∈ A, b₁, …, bₙ ∈ B such that
    fⁿ + φ(b₁) fⁿ⁻¹ + ⋯ + φ(bₙ) = 0.
Then
    |f|_sup ≤ max_{1≤i≤n} |b_i|_sup^{1/i}."

*Proof.* "There exists an index j, 1 ≤ j ≤ n, such that
    |f|_sup^n = |fⁿ|_sup ≤ |φ(b_j) fⁿ⁻ʲ|_sup ≤ |b_j|_sup |f|_sup^{n−j}.
Then |f|_sup ≤ |b_j|_sup^{1/j}. □"

**Proposition 4 (6.2.2/4), p. 239.** "Let φ: B → A be an integral homomorphism of affinoid algebras.
Then for each f ∈ A, there exists a monic polynomial q = Xⁿ + b₁Xⁿ⁻¹ + ⋯ + bₙ ∈ B[X] such that
q(f) = 0 and
    |f|_sup = σ(q) = max_{1≤i≤n} |b_i|_sup^{1/i}."

*Proof.* "According to the preceding lemma, it suffices to show |f|_sup ≥ σ(q) in order to get
equality. First we treat the special case where A is an integral domain. Theorem 6.1.2/1 provides
us with a homomorphism ψ: T_d → B such that φ ∘ ψ: T_d → B → A is an integral monomorphism. The map
φ ∘ ψ is torsion-free. Hence we may apply Proposition 2 to find that, for all f ∈ A, we have
|f|_sup = σ(p), where p ∈ T_d[X] is the minimal polynomial of f over T_d with respect to φ ∘ ψ.
This means in particular that p(f) = 0. Consider the polynomial q ∈ B[X], which is obtained from p
by replacing all its coefficients by their ψ-images in B. Clearly, q(f) = p(f) = 0, and
|f|_sup = σ(p) ≥ σ(q). Thus we have proved the proposition in the case where A is an integral
domain.

In order to take care of the general case, let 𝔭₁, …, 𝔭_r be the minimal prime ideals in A and,
for i = 1, …, r, denote by π_i the residue epimorphism A → A/𝔭_i. According to what we already
proved, there are monic polynomials q_i ∈ B[X], i = 1, …, r, such that q_i(π_i(f)) = 0 and
|π_i(f)|_sup = σ(q_i). The first relation can be rephrased as q_i(f) ∈ 𝔭_i for i = 1, …, r. If one
defines q* := ∏_{i=1}^r q_i, one gets a monic polynomial in B[X] such that
    q*(f) ∈ ⋂_{i=1}^r 𝔭_i = rad A.
Then there is an exponent e ∈ ℕ such that (q*(f))^e = 0. Setting q := q*^e, we get a monic
polynomial in B[X] such that q(f) = 0. Furthermore, Proposition 1.5.4/1 gives us
    σ(q) ≤ max_{1≤i≤r} σ(q_i) = max_{1≤i≤r} |π_i(f)|_sup = |f|_sup,
where the last equality follows from Lemma 6.2.1/3. Thus the proof is finished. □"

## 6.2.3 Power-bounded and topologically nilpotent elements (pp. 240–242)

p. 240: "Let A be a k-affinoid algebra. Then each norm | |, inducing the given Banach topology on
A, satisfies | |_sup ≤ | | (Corollary 3.8.2/2). In particular, all power-bounded elements f ∈ A
must satisfy |f|_sup ≤ 1, since | |_sup is power-multiplicative. The converse is also true."

**Proposition 1 (6.2.3/1).** "For each f ∈ A, the following statements are equivalent:
(i) f is power-bounded.
(ii) |f|_sup ≤ 1."

*Proof.* "We have only to show that f is power-bounded if |f|_sup ≤ 1. Choose a finite homomorphism
φ: T_d → A (for example, an epimorphism). Then due to Proposition 6.2.2/4, there is an integral
equation
    fⁿ + t₁fⁿ⁻¹ + ⋯ + tₙ = 0
of f over T_d such that
    |f|_sup = max_{1≤i≤n} |t_i|^{1/i}.
We have t₁, …, tₙ ∈ T̊_d if |f|_sup ≤ 1. Induction on ν gives then
    f^{n+ν} ∈ Σ_{i=0}^{n−1} φ(T̊_d) f^i,   ν = 0, 1, 2, … .
Since φ(T̊_d) is bounded in A, we see that Σ_{i=0}^{n−1} φ(T̊_d) f^i is bounded. □"

p. 240: "From this proposition we may derive the following characterization of topologically
nilpotent elements."

**Proposition 2 (6.2.3/2).** "For each f ∈ A, the following statements are equivalent:
(i) f is topologically nilpotent,
(ii) |f(x)| < 1 for all x ∈ Max A,
(iii) |f|_sup < 1."

*Proof.* "Statements (ii) and (iii) are equivalent due to the Maximum Modulus Principle
(Proposition 6.2.1/4). Furthermore, statement (i) implies statement (iii), since any Banach norm on
A dominates | |_sup and since | |_sup is power-multiplicative. In order to verify the opposite
direction, assume |f|_sup < 1. Then there exist a constant c ∈ k, |c| > 1, and an integer m > 0 such
that |cf^m|_sup ≤ 1. This follows from Proposition 6.2.1/4 (ii) if |f|_sup ≠ 0 and is trivial if
|f|_sup = 0. We have cf^m ∈ Å by Proposition 1. Therefore f^m ∈ c⁻¹Å ⊂ Ǎ, and we see that f^m and
hence also f are topologically nilpotent. □"

p. 240: "Furthermore, Proposition 1 allows to compute | |_sup in terms of an arbitrary complete
k-algebra norm on A."

**Proposition 3 (6.2.3/3), p. 241.** "Let | | be a complete k-algebra norm on A. Then
|f|_sup = inf_{i ∈ ℕ} |f^i|^{1/i} for all f ∈ A."

*Proof.* "Define |f|' := inf_{i ∈ ℕ} |f^i|^{1/i} for all f ∈ A. Then | |' is a power-multiplicative
k-algebra semi-norm according to Proposition 1.3.2/1, and it follows from Corollary 3.8.2/2 that
|f|_sup ≤ |f|' for all f ∈ A. The opposite inequality shall be shown indirectly. Assume that
|f|_sup < |f|' for some f ∈ A. Proposition 6.2.1/4 (ii) allows us to assume |f|_sup = 1, and hence
|f|' > 1. This implies |f^i| ≥ |f|'^i → ∞, and therefore f cannot be power-bounded, in
contradiction to Proposition 1. □"

**Remark (p. 241).** "For affinoid algebras without zero divisors, the preceding propositions are
direct consequences of Proposition 3.8.2/5 and Corollary 3.8.2/6."

p. 241: "Using Propositions 1 and 2, we can give the following description of the residue algebra
Ã = Å/Ǎ (as defined in (1.2.5))."

**Proposition 4 (6.2.3/4).** "Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}."

p. 241: "We want to finish this section by giving a criterion for | |_sup to be a valuation on A.
Namely, using Propositions 1.5.3/1, 6.2.1/4, and the above Proposition 4, we conclude that"

**Proposition 5 (6.2.3/5).** "The supremum semi-norm is a valuation on A if and only if A is reduced
and Ã is an integral domain."

**Example (pp. 241–242).** "Even if A is an integral domain, the supremum semi-norm | |_sup is not
in general a valuation on A. This can be seen from the following example.

Consider the k-algebra k⟨X, X⁻¹⟩ of strictly convergent Laurent series in one variable X over k
and look at the subalgebra A of all series which converge on the annulus {x ∈ k; |c| ≤ |x| ≤ 1},
where c ∈ k, 0 < |c| < 1, is fixed. Then
    A = {f = Σ_{ν=−∞}^{+∞} a_ν X^ν; lim_{ν→∞} a_ν = 0, lim_{ν→−∞} c^ν a_ν = 0},
and A is an integral domain, since k⟨X, X⁻¹⟩ is an integral domain. A direct computation shows
that there is a canonical isomorphism
    A ≅ k⟨X, Y⟩/(XY − c).
Identifying A with k⟨X, Y⟩/(XY − c), the algebra A becomes k-affinoid. Let f₁, f₂ ∈ A denote the
residue classes of X, Y ∈ k⟨X, Y⟩. The ideals (X − 1, Y − c) and (X − c, Y − 1) are maximal ideals
in k⟨X, Y⟩ containing the ideal (XY − c), because
    XY − c = (X − 1) Y + (Y − c) = X(Y − 1) + (X − c).
Therefore
    x₁ := (X − 1, Y − c)/(XY − c),  and  x₂ := (X − c, Y − 1)/(XY − c)
are maximal ideals in A. Since f₁(x₁) = 1 = f₂(x₂), we see that |f₁|_sup = 1 = |f₂|_sup. However
|f₁f₂|_sup = |c|_sup = |c| < 1. Consequently, | |_sup cannot be a valuation on A."

## 6.2.4 Reduced k-affinoid algebras are Banach function algebras (p. 242)

"In this section we study the relationship between the supremum semi-norm | |_sup and the Banach
topology on a k-affinoid algebra A."

**Theorem 1 (6.2.4/1).** "Every reduced k-affinoid algebra A is a Banach function algebra; i.e.,
| |_sup is a complete norm on A. It is equivalent to every other complete k-algebra norm on A."

*Proof.* "Let us first consider the case, where A is an integral domain. Choose a finite
normalization monomorphism φ: T_d → A for a suitable d ≥ 0. Then φ is torsion-free, and the
assertion follows immediately from Theorem 3.8.3/7, because the field of fractions Q(T_d) is
weakly stable (Theorem 5.3.1/1).

Now consider an arbitrary reduced k-affinoid algebra A. Let 𝔭₁, …, 𝔭_r denote the minimal prime
ideals in A. Then the canonical homomorphism
    π: A → A' := ⊕_{i=1}^r A/𝔭_i
is injective, and | |_sup is a complete norm on each algebra A/𝔭_i. Provide A' with the maximum
norm, i.e. |(a₁, …, a_r)| := max_{1≤i≤r} |a_i|_sup. Then A' is complete under | |, and due to
Lemma 6.2.1/3, the norm | | induces the supremum norm on A. Viewing A as a submodule of the finite
A-module A', we see by Proposition 3.7.3/1 that A is closed in A'. Hence | |_sup is complete on A,
and A is a Banach function algebra. That all complete k-algebra norms on A are equivalent to
| |_sup follows from Proposition 6.1.3/2. □"

p. 242: "It should be noted that the characterization of power-bounded elements and of topologically
nilpotent elements as given in Propositions 6.2.3/1 and 6.2.3/2 is an easy consequence of the above
theorem, at least in the case where A is reduced. However, the direct proofs given in (6.2.3) do
not need the weak stability of Q(T_d). This fact had to be used in the proof of Theorem 1."

## 6.3 The reduction functor A ⇝ Ã — introduction (pp. 242–243)

"In the following sections we consider homomorphisms φ: B → A between k-affinoid algebras A and B.
As we already saw in (1.2.5), each such φ maps power-bounded elements into power-bounded elements
and topologically nilpotent elements into topologically nilpotent elements. Thus φ gives rise to a
homomorphism φ̊: B̊ → Å and furthermore, by reducing modulo topologically nilpotent elements, to a
homomorphism φ̃: B̃ = B̊/B̌ → Ã = Å/Ǎ. This is described by the following commutative diagram
    B  —φ→  A
    ↑        ↑
    B̊  —φ̊→  Å
    ↓τ_B     ↓τ_A
    B̃  —φ̃→  Ã,
where τ_A and τ_B denote the canonical reduction epimorphisms modulo topologically nilpotent
elements. If there is no confusion possible, we just write τ instead of τ_A or τ_B.

We are interested in studying properties of the map φ which are inherited by φ̊ or φ̃ and vice
versa. Of particular interest will be the case of integral, respectively finite homomorphisms. The
characterization of power-bounded elements and of topologically nilpotent elements by means of the
supremum semi-norm | |_sup (see Propositions 6.2.3/1 and 6.2.3/2) is important for our
considerations. We will make use of the mentioned results without giving a further reference."

## 6.3.1 Monomorphisms, isometries and epimorphisms (pp. 243–245)

"We begin with injectivity properties."

**Lemma 1 (6.3.1/1).** "The homomorphism φ: B → A is an isometry with respect to | |_sup if and
only if |φ(f)|_sup = 1 for all f ∈ B satisfying |f|_sup = 1."

*Proof.* "We have only to verify the if part of the assertion. Therefore assume |φ(f)|_sup = 1 for
all f ∈ B with |f|_sup = 1. Consider an arbitrary element g ∈ B. If |g|_sup = 0, we conclude
|φ(g)|_sup = 0 from |φ(g)|_sup ≤ |g|_sup. If |g|_sup ≠ 0, choose c ∈ k* and m ∈ ℕ such that
|cg^m|_sup = 1 (Proposition 6.2.1/4). Then
    |c| |φ(g)|_sup^m = |φ(cg^m)|_sup = 1 = |cg^m|_sup = |c| |g|_sup^m,
and hence |φ(g)|_sup = |g|_sup. □"

"An immediate consequence of the lemma is"

**Proposition 2 (6.3.1/2).** "The map φ̃: B̃ → Ã is injective if and only if φ: B → A is an
isometry."

**Corollary 3 (6.3.1/3).** "If φ̃: B̃ → Ã is injective, then ker φ is contained in the nilradical
rad B."

*Proof.* "We have rad B = {g ∈ B; |g|_sup = 0} by Proposition 6.2.1/4. Consequently, the kernel of
any isometry φ: B → A is contained in rad B. □"

pp. 243–244: "Under the additional hypothesis that φ is strict, the converse of Corollary 3 is true.
In order to prove this, we look more closely at the ideal τ⁻¹(ker φ̃) = φ̊⁻¹(Ǎ) in B̊, which is
reduced (i.e., equal to its nilradical), since Ã is reduced. Obviously, we have
B̌ + ker φ̊ ⊂ τ⁻¹(ker φ̃) and therefore also
    rad (B̌ + ker φ̊) ⊂ τ⁻¹(ker φ̃).
If φ is strict, this inclusion relation is just an equality; namely,"

**Observation 4 (6.3.1/4), p. 244.** "If φ is strict, then we have
    τ⁻¹(ker φ̃) = rad (B̌ + ker φ̊)   and   ker φ̃ = rad (τ(ker φ̊))."

*Proof.* "In order to verify the first equation, assume that φ is strict. Then φ(B̌) is open in
φ(B). Consider an arbitrary element g ∈ τ⁻¹(ker φ̃) = φ̊⁻¹(Ǎ). From lim_{n→∞} φ(g)ⁿ = 0, we conclude
φ(g)ⁿ ∈ φ(B̌) and hence gⁿ ∈ B̌ + ker φ̊ for n big enough. This verifies the first equation. The
second equation is a consequence of the first one, since the formation of the nilradical commutes
with the map τ: B̊ → B̃ for those ideals in B̊ which contain B̌ = ker τ. □"

"Now we can give the converse to Corollary 3."

**Proposition 5 (6.3.1/5).** "If φ: B → A is strict and ker φ ⊂ rad B, then φ̃ is injective."

*Proof.* "If ker φ ⊂ rad B, then a fortiori ker φ̊ ⊂ rad B̊. Since B̌ is a reduced ideal, one has
rad (B̌ + ker φ̊) = B̌. Now the preceding observation implies ker φ̃ = 0. □"

"Summarizing the above results, we obtain"

**Theorem 6 (6.3.1/6).** "Let B be reduced. Then the following statements are equivalent:
(i) φ: B → A is injective and strict.
(ii) φ: B → A is an isometry with respect to | |_sup.
(iii) φ̃: B̃ → Ã is injective."

*Proof.* "The equivalence of statements (ii) and (iii) is asserted by Proposition 2. Furthermore,
statement (i) implies (iii) by Proposition 5. So far we did not use the fact that B is reduced.
However this assumption is necessary in order to verify the remaining implication, say from (ii) to
(i). We know from Theorem 6.2.4/1 that B is a Banach function algebra, i.e., that | |_sup is a
complete norm on B. Therefore, any isometry φ: B → A with respect to | |_sup is injective. It
remains to verify that φ is also strict. Fix a Banach norm | | on A. Then | | dominates | |_sup
on A and |g|_sup = |φ(g)|_sup ≤ |φ(g)| for all g ∈ B. Since the supremum norm | |_sup induces the
given Banach topology on B and since φ is continuous anyway, we see that φ is strict. □"

"There are no good criteria relating the surjectivity of φ and φ̃. We give two examples. The first
one shows that φ̃ may be surjective, even bijective, without φ being surjective. The second one
shows that φ may be surjective without φ̃ being surjective."

**Example 1 (p. 245).** "Consider a ground field k, which admits a finite extension K of degree
n > 1 such that e(K/k) = n. (The field ℚ₂ of 2-adic numbers is such a field; one can set
K := ℚ₂(√2).) Then f(K/k) = 1 by Proposition 3.1.3/2. Thus, viewing k and K as k-affinoid
algebras, the injection φ: k ↪ K is a homomorphism of k-affinoid algebras which is not surjective.
However, the residue homomorphism φ̃: k̃ → K̃ is bijective, since f(K/k) = 1."

**Remark.** "As we will see later, in the case of a stable ground field k with divisible value group
|k*|, the surjectivity of φ̃ implies the surjectivity of φ: B → A if A is reduced. Therefore, for
reduced k-affinoid algebras over such a field (e.g., over an algebraically closed field), φ is
bijective if and only if φ̃ is bijective, see Corollary 6.4.2/2."

**Example 2 (p. 245).** "Set B := T₁ = k⟨X⟩ and A := k ⊕ k (ring-theoretic normed direct sum of
two copies of k). Choose a constant c ∈ k, 0 < |c| < 1, and consider the homomorphism
    φ: B → A,  X ↦ (c, 0).
It is easily verified that φ is surjective. However φ̃: k̃[X] → k̃ ⊕ k̃ cannot be surjective, since
|φ(X)|_sup = |c| < 1 and hence φ̃(X) = 0."
