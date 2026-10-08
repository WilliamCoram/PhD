# BGR §3.4.2 (end), §3.5 — Weakly stable fields (book pp. 149–156; PDF page = book + 6)

Hand transcription from the scan. Locators are `bgr-3.5.md:<line>`.

## 3.4.2 (end), p. 149

**Proposition 3 (3.4.2/3).** Let α be separable over K of degree n > 1, and let f ∈ K[X] be the
minimal polynomial of α over K. Set ε(α) := (|f|⁻¹ r(α))ⁿ. Then each monic polynomial g ∈ K[X] of
degree n such that |f − g| < ε(α) has a root β ∈ B⁻(α, r(α)). Furthermore, each such root β
satisfies K(β) = K(α).

**Corollary 4 (3.4.2/4).** Let f be a polynomial in K[X] of degree n > 1, which is monic,
irreducible and separable. Then any monic polynomial g ∈ K[X] of the same degree n which is
sufficiently close to f is also irreducible and separable.

**Proposition 5 (3.4.2/5).** Let K' be a dense subfield of K, and let α ∈ K_a be separable of
degree n > 1 over K. Then there exist elements α' ∈ K(α) arbitrarily close to α and algebraic over
K' such that K(α) = K(α').

## 3.4.3 Example. p-adic numbers, pp. 149–151

**Lemma 1 (3.4.3/1).** Let K be a field with a complete non-trivial valuation. Assume that the
algebraic closure K_a of K is of infinite degree over K. Then K_a (provided with the unique
valuation extending the valuation on K) is not complete.

(Proof uses Proposition 2.3.3/4 [finite extensions of a complete field are complete], Proposition
3.4.1/6 [K_sep dense in K_a] and Krasner's Lemma, Corollary 3.4.2/2.)

## 3.5 Weakly stable fields, p. 151

"We want to combine the notions of weakly cartesian vector space and spectral norm. As always, K
denotes a valued field and K_a the algebraic closure of K. Let L be an algebraic extension of K
provided with a K-algebra norm (usually the spectral norm)."

### 3.5.1 Weakly cartesian fields

**Lemma 1 (3.5.1/1).** Let L be a finite extension of K with a K-algebra norm | | such that L is
weakly K-cartesian. Then the semi-norm | |' defined by |x|' := inf_{ν→∞} |x^ν|^{1/ν} is the
spectral norm. In particular, if the product topology on L can be induced by a power-multiplicative
K-algebra norm, then this norm must be the spectral norm.

*Proof.* Because L provided with | | carries the product topology, the identity map
(L, | |) → (L, | |_sp) is continuous. Therefore, there is a constant ρ > 0 such that
|x|_sp ≤ ρ|x| for all x ∈ L, whence |x|_sp ≤ |x|' for all x ∈ L. Thus we see by Proposition
1.3.2/1 that | |' is a power-multiplicative K-algebra norm dominating the spectral norm. According
to Proposition 3.1.2/1, the two norms | |' and | |_sp coincide. The second assertion of the lemma
is obvious. ∎

**Observation 2 (3.5.1/2).** The K-vector space L is weakly K-cartesian (resp. K-cartesian) if each
finite extension L' ⊂ L of K is weakly K-cartesian (resp. K-cartesian).

*Proof.* Let W be any K-subspace of L of finite dimension. Since L is algebraic over K, the field
L' := K[W] generated over K by all elements of W is a finite extension of K. By assumption L' is
weakly K-cartesian (resp. K-cartesian). Hence W ⊂ L' is weakly K-cartesian (resp. K-cartesian) as
well, cf. Lemma 2.3.2/5 (resp. Proposition 2.4.1/5). ∎

**Proposition 3 (3.5.1/3).** Let L be a finite separable extension of K such that the trace
function T := Tr_{L/K} : L → K is continuous. Then L is weakly K-cartesian.

*Proof.* By assumption the K-bilinear map L × L → K defined by (x, y) ↦ T(xy) is continuous. Since
L is a separable extension, T(xy) is non-degenerate, i.e., for given x₀ ≠ 0 in L, there always
exists a y₀ ∈ L such that T(x₀y₀) ≠ 0. Hence x ↦ T(xy₀) is a continuous K-linear map λ: L → K such
that λ(x₀) ≠ 0. Thus L is a b-separable K-vector space and therefore weakly K-cartesian
(Proposition 2.3.2/7). ∎

**Proposition 4 (3.5.1/4).** If K is perfect (in particular, if K is of characteristic 0) the
algebraic closure K_a of K provided with the spectral norm is weakly K-cartesian.

*Proof.* The field K being perfect, each finite extension L ⊂ K_a is separable. The trace function
T: L → K is a contraction with respect to the spectral norm on L (see Corollary 3.2.3/2). Hence L
is weakly K-cartesian by Proposition 3. The observation made above concludes the proof. ∎

### 3.5.2 Weakly stable fields, pp. 152–154

(Opening discussion: the proposition is false for non-perfect K in general; example of a valued
field K with a purely inseparable extension L ≠ K in which K is dense: k of characteristic p with
[k^{p⁻¹} : k] = ∞, R := k^{p⁻¹}⟨X⟩, A ⊂ R the series whose coefficients generate a finite
extension of k, K := Q(A), L := Q(R).)

**Definition 1 (3.5.2/1).** A valued field K is called *weakly stable* if each finite extension L
of K provided with the spectral norm is weakly K-cartesian.

"The example just given shows the existence of fields which are not weakly stable (for further
examples, see (3.5.4)). Obviously our definition can be rephrased as follows:

*The field K is weakly stable if and only if K_a is weakly K-cartesian with respect to the spectral
norm.*

By Proposition 3.5.1/4, *each perfect field is weakly stable*. Furthermore, it follows from
Proposition 2.3.3/4 that *each complete field K is weakly stable*."

**Remark.** Another way of expressing the fact that K is weakly stable is to say that the completion
K̂ of K is a separable extension of K, i.e., that K̂ ⊗_K K^{p⁻¹} is reduced (if p := char K ≠ 0).
However we shall never use this characterization.

### 3.5.3 Criterion for weak stability, pp. 154–155

"We only have to consider the case where p := char K ≠ 0. The essential role is played by the field
K^{p⁻¹} = {x ∈ K_a; x^p ∈ K} of all p-th roots. The spectral norm on K^{p⁻¹} is a valuation."

**Theorem 1 (3.5.3/1).** A valued field K is weakly stable if and only if K^{p⁻¹} (provided with
the spectral valuation) is weakly K-cartesian.

*Proof.* We only have to show that K_a is weakly K-cartesian with respect to the spectral norm if
K^{p⁻¹} is weakly K-cartesian. First we show by induction on n

  *Each field K_n := {x ∈ K_a; x^{pⁿ} ∈ K} is weakly K-cartesian, n ≥ 1.*

Assume K_n is weakly K-cartesian (true by assumption for n = 1). In order to prove that K_{n+1} is
weakly K-cartesian, it is enough to prove (use Proposition 2.3.3/2 with V := K_{n+1} and
K' := K_n and the fact that the spectral norm on K_n is a valuation extending the valuation on K)

  *Each finite-dimensional K_n-vector space U ⊂ K_{n+1} is closed in K_{n+1}.*

The Frobenius homomorphism x ↦ x^{pⁿ} is a homeomorphism mapping the K_n-algebra K_{n+1} onto the
K-algebra K_1. Thereby U is mapped onto a finite-dimensional K-subspace of K_1 which is closed in
K_1 by assumption. Hence, U must be closed in K_{n+1}.

Next we consider the "perfect closure" K_∞ := ⋃_{n=1}^∞ K_n which is a valued subfield of K_a. From
what we just proved, we conclude that K_∞ is weakly K-cartesian. Thus, again by Proposition
2.3.3/2, all that remains to be shown is that K_a is weakly K_∞-cartesian. This follows from
Proposition 3.5.1/4, since K_∞ is perfect and since the spectral norm on K_a over K coincides with
the spectral norm over K_∞ (see Proposition 3.2.2/4). ∎

"In applications K is often given as the field of fractions of a valued ring A. Then

  A_1 = A^{p⁻¹} = {x ∈ K_1; x^p ∈ A}

is a valued ring having K_1 as field of fractions. More precisely, K_1 = A_1 ⊗_A K; i.e., each
z ∈ K_1 is of the form z = x/a, x ∈ A_1, a ∈ A − {0}. (In order to see this, just write z^p = b/a,
b ∈ A, a ∈ A − {0}, and set x := az. Then z = x/a and x^p = a^{p−1}b ∈ A; i.e., x ∈ A_1.) Now
Lemma 2.3.3/3 (with M = A_1, V = K_1) and Theorem 1 directly imply"

**Lemma 2 (3.5.3/2), p. 155.** Let K be the field of fractions of the ring A. Assume that each
finitely generated A-submodule of A^{p⁻¹} is b-separable. Then K is weakly stable.

"For later reference and as an illustration of Lemma 2, we want to show"

**Proposition 3 (3.5.3/3).** Let K = k(X₁, …, Xₙ) be the field of rational functions over some
field k. Provide K with the valuation induced by the total degree, i.e.,
|f/g| := exp(deg f − deg g) for all polynomials f, g ∈ k[X₁, …, Xₙ], g ≠ 0. Then K is weakly stable.

*Proof.* Let A := k[X₁, …, Xₙ] be provided with the valuation induced by the total degree. Then K
is the field of fractions of A, and the valuation on K extends the valuation on A. In order to
apply the preceding lemma, we must show that A^{p⁻¹} is a b-separable A-module. Viewing
k[X₁, …, Xₙ] as a k[X₁^p, …, Xₙ^p]-module, we have a canonical decomposition as a norm-direct sum

  k[X₁, …, Xₙ] = ⊕_{0 ≤ νᵢ < p} k[X₁^p, …, Xₙ^p] X₁^{ν₁} ⋯ Xₙ^{νₙ}.

Then we can use the Frobenius homomorphism f ↦ f^p (or more precisely, its inverse) to see that
A^{p⁻¹} is a norm-direct sum of finitely many A-submodules linearly homeomorphic to
k^{p⁻¹}[X₁, …, Xₙ]. Thus by Proposition 2.2.5/2, we have only to show that k^{p⁻¹}[X₁, …, Xₙ] is a
b-separable A-module. However this is clear, since k^{p⁻¹} (carrying the trivial valuation) is
b-separable over k. ∎

### 3.5.4 Weak stability and Japaneseness, p. 155

"In this section we assume the reader is familiar with the notions and results of the appendix
'Tame modules and Japanese rings'. Lemma 3.5.3/2 and Proposition 4.4/3 indicate a close connection
between the notions of Japaneseness and weak stability. Here we prove"

**Proposition 1 (3.5.4/1).** A discrete valuation ring A is Japanese if and only if its field of
fractions K is weakly stable.

*Proof.* Set p := char A. If p = 0, our statement is true due to Propositions 3.5.1/4 and 4.3/2,
since A = K° is a principal ideal domain by Proposition 1.6.1/4 and, in particular, both Noetherian
and normal. Assume p ≠ 0. Then it follows from Theorem 3.5.3/1 and Proposition 2.3.4/2 that K is
weakly stable if and only if (K^{p⁻¹})° is a tame K°-module. Now A^{p⁻¹} = (K^{p⁻¹})°, and
Proposition 4.4/2 says that A (being Noetherian and normal) is Japanese if and only if A^{p⁻¹} is a
tame A-module. Hence the assertion follows. ∎

**Proposition 2 (3.5.4/2).** There exist fields K with a discrete valuation which are not weakly
stable.

(p. 156 begins §3.6 Stable fields — Definition 3.6.1/1: K is stable if each finite extension L of K
provided with the spectral norm is a K-cartesian vector space. Not used in Layer 0.)
