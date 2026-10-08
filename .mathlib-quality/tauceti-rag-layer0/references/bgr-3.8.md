# BGR §3.8 Function algebras (book pp. 168–182) — hand transcription from the scan

Render file `bgr_a/pNNN.pdf.png` shows book page NNN − 8. Locators are `bgr-3.8.md:<line>`.

## 3.8 Function algebras, p. 168

"Let k be a (not necessarily complete) valued field and let X be a set. Then the set of all bounded
functions f: X → k forms a k-algebra. Defining |f| := sup_{x∈X} |f(x)|, one gets a k-algebra
semi-norm on this algebra, the so-called supremum semi-norm. […] We assume that the reader is
familiar with the notion of integral dependence."

### 3.8.1 The supremum semi-norm on k-algebras, pp. 168–173

"For the purposes of this section, we do not suppose that our ground field k is complete. Let A be
a k-algebra. We want to derive a semi-norm on A from the given valuation on k. In order to do so,
we use the following"

**Definition 1 (3.8.1/1).** *Spectrum of k-algebraic maximal ideals of A:*

  Max_k A := {x; x maximal ideal in A and A/x algebraic over k}.

"Of course, Max_k A may be empty; e.g., this is the case if A is a field which is transcendent over
k. But in many cases, the spectrum of k-algebraic maximal ideals of A yields substantial
information about A.
For x ∈ Max_k A and f ∈ A, denote by f(x) the image of f under the canonical residue epimorphism
π_x: A → A/x. Since A/x is an algebraic extension of k, it can be provided with the spectral norm
derived from the given valuation on k (cf. (3.2)). Writing |f(x)| for the spectral norm of the
element f(x) ∈ A/x, we are able to introduce"

**Definition 2 (3.8.1/2), p. 169.** *Semi-norm of uniform convergence on Max_k A or supremum
semi-norm on Max_k A:*

  |f|_sup := 0                          if Max_k A = ∅,
             sup {|f(x)|; x ∈ Max_k A}  if Max_k A ≠ ∅ and f(Max_k A) bounded,
             ∞                          otherwise.

"This definition generalizes the concept of the spectral norm. Namely, if A is an algebraic
extension of k, this definition obviously yields the spectral norm on A. […] However, although we
have used the term semi-norm, it is not in general true that the function | |_sup defines a
semi-norm on A. Namely, the third case occurring in Definition 2 is possible: e.g., take A = k[X].
Then Max_k A ⊃ {(X − c)k[X]; c ∈ k}. If one takes f := X ∈ A, then f(Max_k A) ⊃ k, which is clearly
not bounded (unless k carries the trivial valuation). We shall say that the supremum semi-norm on A
is finite if f(Max_k A) is bounded for all f ∈ A."

**Lemma 3 (3.8.1/3).** If | |_sup is finite, it is a power-multiplicative "k-algebra semi-norm" on
A; i.e., one has for all f, g ∈ A, c ∈ k, n ∈ ℕ
 (a) |f|_sup ∈ ℝ, |f|_sup ≥ 0, |0|_sup = 0,
 (b) |f + g|_sup ≤ max {|f|_sup, |g|_sup},
 (c) |cf|_sup = |c| |f|_sup,
 (d) |fg|_sup ≤ |f|_sup |g|_sup,
 (e) |1|_sup ≤ 1,
 (f) |fⁿ|_sup = |f|ⁿ_sup.

**Lemma 4 (3.8.1/4).** Let φ: B → A be a k-algebra homomorphism between two k-algebras A and B.
Then φ is a contraction with respect to | |_sup, i.e., |φ(g)|_sup ≤ |g|_sup for all g ∈ B.

*Proof.* If Max_k A = ∅, there is nothing to show. If x ∈ Max_k A, then φ induces a k-algebra
monomorphism B/φ⁻¹(x) → A/x. Because A/x is an algebraic extension of k, its subring B/φ⁻¹(x) must
also be an algebraic extension of k. Hence φ⁻¹(x) ∈ Max_k B. Then one has

 (*) |φ(g)|_sup = sup_{x∈Max_k A} |φ(g)(x)| = sup_{x∈Max_k A} |g(φ⁻¹(x))| ≤ sup_{y∈Max_k B} |g(y)|
     = |g|_sup. ∎

**Lemma 5 (3.8.1/5), p. 170.** Let 𝔐 be the set of all minimal prime ideals in A, and let
π_𝔭: A → A/𝔭 denote the canonical residue map for all 𝔭 ∈ 𝔐. Then we have
|f|_sup = sup_{𝔭∈𝔐} |π_𝔭(f)|_sup for all f ∈ A.

**Lemma 6 (3.8.1/6).** Let φ: B → A be an integral k-algebra monomorphism. Then one has
 (a) φ is an isometry with respect to | |_sup,
 (b) |f|_sup ≤ max_{1≤i≤n} |bᵢ|_sup^{1/i} for f ∈ A, where fⁿ + φ(b₁)fⁿ⁻¹ + ⋯ + φ(bₙ) = 0 is an
     equation of integral dependence for f over φ(B),
 (c) | |_sup is finite on A if and only if it is finite on B.

*Proof.* Ad(a): If Max_k B = ∅, then by Lemma 4 we have |φ(g)|_sup ≤ |g|_sup = 0 for all g ∈ B.
Therefore we may assume Max_k B ≠ ∅. Take y ∈ Max_k B. Since φ is integral and injective, there is
a maximal ideal x of A lying over y, i.e., φ⁻¹(x) = y. Now φ induces an integral monomorphism from
B/y into A/x. The field B/y is an algebraic extension of k by our assumption, and A/x is integral
over B/y. Therefore A/x is an algebraic extension of k. In other words, the map x ↦ φ⁻¹(x) from
Max_k A to Max_k B is surjective. Therefore, one has equality in the formula (*) occurring in the
proof of Lemma 4, and so φ is an isometry.
Ad(b): For all x ∈ Max_k A, one has
0 = f(x)ⁿ + (φ(b₁))(x) f(x)ⁿ⁻¹ + ⋯ + φ(bₙ)(x) = f(x)ⁿ + b₁(φ⁻¹(x)) f(x)ⁿ⁻¹ + ⋯ + bₙ(φ⁻¹(x)). Due
to Proposition 3.1.2/1, this equation implies
|f(x)| ≤ max_{1≤i≤n} |bᵢ(φ⁻¹(x))|^{1/i} ≤ max_{1≤i≤n} |bᵢ|_sup^{1/i}. Since this holds for all
x ∈ Max_k A, we have |f|_sup ≤ max_{1≤i≤n} |bᵢ|_sup^{1/i}.
Ad(c): If g(Max_k B) is bounded for all g ∈ B, then f(Max_k A) is also bounded for all f ∈ A due
to (b). The converse is true due to (a). ∎

"We say that the *Maximum Modulus Principle* holds for a k-algebra A if, for all f ∈ A, there
exists an x ∈ Max_k A such that |f(x)| = |f|_sup." (p. 171)

**Proposition 7 (3.8.1/7).** Let φ: B → A be an integral torsion-free k-algebra monomorphism between
two k-algebras A and B, where B is an integrally closed (integral) domain. Then one has
 (a) |f|_sup = max_{1≤i≤n} |bᵢ|_sup^{1/i} for f ∈ A, where fⁿ + φ(b₁)fⁿ⁻¹ + ⋯ + φ(bₙ) = 0 is the
     (unique) integral equation of minimal degree for f over φ(B).
 (b) The Maximum Modulus Principle holds for A if and only if it holds for B.
 (c) | |_sup is a norm on A if and only if | |_sup is a norm on B and A is reduced.
 (d) We have |φ(b) f|_sup = |b|_sup |f|_sup for all b ∈ B and all f ∈ A if and only if
     |bb'|_sup = |b|_sup |b'|_sup for all b, b' ∈ B.

(Proof pp. 171–173; uses Proposition 3.2.2/4, Corollary 3.2.1/6. Layer 2 material.)

**Corollary 8 (3.8.1/8), p. 173.** In addition to the assumptions of Proposition 7, assume that the
Maximum Modulus Principle holds for B. Then for every f ∈ A with |f| ≠ 0, there exist c ∈ k and
m ∈ ℕ such that |cf^m|_sup = 1.

**Lemma 9 (3.8.1/9).** If | |_sup is a norm on a k-algebra A, then ⋂_{𝔪 ∈ Max_k A} 𝔪 = (0). In
particular, A is reduced, and the Jacobson radical ⋂_{𝔪 ∈ Max A} 𝔪 vanishes.

(pp. 173–174: Remark on the spectral norm of Q(A); Propositions 10, 11 on k-cartesian algebras for
stable k. Not used in Layer 0.)

### 3.8.2 The supremum semi-norm on k-Banach algebras, pp. 174–178

"[…] From now on we assume that we are given a norm | | on A and ask how are | | and | |_sup
interrelated. For simplicity, we restrict ourselves to the case where the ground field k is
complete and A is a k-Banach algebra. Even in this case, the maximal ideals 𝔪 of A need not be
algebraic over k (i.e., A/𝔪 need not be algebraic over k). For example, just take A to be the
completion of the field of fractions of k⟨X⟩ provided with the Gauss valuation. One has the
following preliminary result."

**Lemma 1 (3.8.2/1), p. 175.** Let A be a k-Banach algebra with norm | | and let x ∈ Max_k A be a
k-algebraic maximal ideal. Then x is closed in A and A/x provided with the residue norm | |_res is a
k-Banach algebra. Moreover, one has

  |f(x)| = inf_{i∈ℕ} |f(x)^i|_res^{1/i} ≤ |f(x)|_res ≤ |f|.

*Proof.* Assume that x is not closed in A. Then its completion x̂ is an ideal in A such that
x ⊊ x̂. Therefore x̂ = A; i.e., x is dense in A. In particular, x contains elements which are
arbitrarily close to the unit element 1 ∈ A. Hence by Proposition 1.2.4/4, the ideal x must contain
units itself. However this is impossible so that x must be closed in A. Therefore the function
| |_res, given by

  |f(x)|_res = inf_{f(x)=g(x)} |g|  for f ∈ A,

is a norm on A/x (cf. (1.1.6)). Using Proposition 1.1.7/3, we see that | |_res is actually a
complete k-algebra norm on A/x with |f(x)|_res ≤ |f|.
We want to define another norm | |' on A/x by |f(x)|' := inf_{i∈ℕ} |f(x)^i|_res^{1/i}. Due to
Proposition 1.3.2/1, the map | |' is a power-multiplicative "k-algebra semi-norm" on A/x such that
|f(x)|' ≤ |f(x)|_res for all f ∈ A. Because A/x is a field, | |' is in fact a norm. The field k is
complete, and A/x is an algebraic extension of k. Hence the spectral norm is the only
power-multiplicative k-algebra norm on A/x, and therefore it coincides with | |'. Thus we have
|f(x)| = inf_{i∈ℕ} |f(x)^i|_res^{1/i}. ∎

"Applying this lemma to all x ∈ Max_k A, we get"

**Corollary 2 (3.8.2/2).** If A is a k-Banach algebra with norm | |, then for all f ∈ A one has

  |f|_sup ≤ |f|.

"If A is not complete, this statement may fail to be true. For example, take A = k[X] provided with
the Gauss norm and f := X; then |X| = 1, whereas |f|_sup = ∞, as we have seen already in (3.8.1)."

**Proposition 3 (3.8.2/3).** Let A be a k-Banach algebra. Assume that | |_sup is a norm on A. Then
every k-algebra homomorphism φ from an arbitrary k-Banach algebra B into A is continuous.

**Corollary 4 (3.8.2/4), p. 176.** If A is a k-Banach algebra such that | |_sup is a norm on A, then
all complete k-algebra norms on A are equivalent.

**Proposition 5 (3.8.2/5).** Let φ: B → A be an integral torsion-free k-algebra monomorphism between
two k-algebras A and B, where B is an integrally closed domain. Assume furthermore that A is a
k-Banach algebra with norm | | and that φ is continuous if B is provided with the topology induced
by | |_sup. Then one has for all f ∈ A

  inf_{i∈ℕ} |f^i|^{1/i} = |f|_sup = max_{1≤i≤n} |bᵢ|_sup^{1/i},

where fⁿ + φ(b₁)fⁿ⁻¹ + ⋯ + φ(bₙ) = 0 is the integral equation of minimal degree for f over φ(B).

**Corollary 6 (3.8.2/6), p. 177.** Under the hypotheses of Proposition 5, the following statements
are equivalent for all f ∈ A: (a) f is topologically nilpotent, (b) inf |f^i|^{1/i} < 1,
(c) |f|_sup < 1. If the Maximum Modulus Principle holds for A or B, then (a), (b) and (c) are
equivalent to (d) |f(x)| < 1 for all x ∈ Max_k A. Furthermore, the following statements are
equivalent for all f ∈ A: (a') f is power-bounded, (b') inf |f^i|^{1/i} ≤ 1, (c') |f|_sup ≤ 1.

### 3.8.3 Banach function algebras, p. 178

**Definition 1 (3.8.3/1).** A k-algebra A is called a *Banach function algebra* if | |_sup is a
complete norm on A.

**Lemma 2 (3.8.3/2).** A k-Banach algebra A is a Banach function algebra if and only if | |_sup is
equivalent to the given norm on A.

**Lemma 3 (3.8.3/3).** If A is a Banach function algebra, then | |_sup is the only
power-multiplicative complete k-algebra norm on A.

**Lemma 4 (3.8.3/4).** Let φ: B → A be a k-algebra monomorphism between two k-algebras A and B.
Assume that A is a Banach function algebra. Then B is a Banach function algebra if φ(B) is closed
in A. In particular, a closed subalgebra of a Banach function algebra is again a Banach function
algebra.

(3.8.3/5–6 on pp. 179–181 and Theorem 7 on p. 181: see `bgr-4.md` for Theorem 7.)
