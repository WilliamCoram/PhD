# BGR §1.3.1–1.3.2 (book pp. 30–33) and §1.5.1, 1.5.3, 1.5.4 (book pp. 41–45) — hand transcription
# (renders bgr2/p038–p041, p049–p053; PDF page = book page + 8)

## 1.2.5 (end), p. 30

**Definition 6 (1.2.5/6).** "The ring ~A := Å/Ǎ is called the invariant residue ring of A."
**Proposition 7 (1.2.5/7).** "The rings Ã and ~A are reduced; i.e., they have no nilpotent elements
≠ 0."
*Proof.* "Let b be an element of A. It is enough to prove that if bⁿ ∈ Ǎ for some n ≥ 1, then b ∈ Ǎ.
Now bⁿ ∈ Ǎ means lim_ν |b^{nν}| = 0. Choose M > 0 such that |b^j| < M for 0 ≤ j < n. Each m ∈ ℕ can
be written in the form m = nν + j, 0 ≤ j < n. This implies |b^m| ≤ |b^{nν}| M, and hence |b^m| → 0
as m → ∞; i.e., b ∈ Ǎ. □"
**Proposition 8 (1.2.5/8).** "Let A ∈ 𝔑 be complete. Then an element a ∈ Å (resp. Ȧ, resp. A°) is a
unit in Å (resp. Ȧ, resp. A°) if and only if its residue class ā ∈ Ã (resp. ~a ∈ ~A, resp.
a~ ∈ A~) is a unit in Ã (resp. ~A, resp. A~)."

## 1.3 Power-multiplicative semi-norms

### 1.3.1 Definition and elementary properties (pp. 30–32)

"Let (A, | |) ∈ 𝔑 be given."
**Definition 1 (1.3.1/1).** "The semi-norm | | is called power-multiplicative or a pm-semi-norm if
all elements of A are power-multiplicative. If in addition ker | | = 0, we call | | a pm-norm."
"It follows immediately from Proposition 1.2.2/2 that rad A ⊂ ker | | for pm-semi-norms. In
particular, all rings A with a pm-norm are reduced; i.e., rad A = 0."
**Proposition 2 (1.3.1/2).** "Let (A, | |) and (A', | |') be given, and let | |' be
power-multiplicative. Then every bounded ring homomorphism φ: A → A' is a contraction:
|φ(a)|' ≤ |a|, a ∈ A."
*Proof.* "There exists a positive real number K with |φ(a)|' ≤ K|a|, a ∈ A. For all n ∈ ℕ, we have
|φ(aⁿ)|' ≤ K|aⁿ| ≤ K|a|ⁿ. The pm-property of | |' implies |φ(aⁿ)|' = (|φ(a)|')ⁿ. Hence
|φ(a)|'ⁿ ≤ K|a|ⁿ for all n ∈ ℕ; i.e., |φ(a)|' ≤ ⁿ√K |a|. Since lim ⁿ√K = 1, we get |φ(a)|' ≤ |a|. □"
**Corollary 3 (1.3.1/3), p. 31.** "Let | |, | |' be pm-semi-norms on A such that there are real
numbers ρ, ρ' > 0 with | |' ≤ ρ| | ≤ ρ'| |'. Then these semi-norms are equal: | | = | |'."
*Proof.* "The identity map id: (A, | |) → (A, | |') is an isometry by Proposition 2. □"
**Proposition 4 (1.3.1/4).** "If | | is a pm-semi-norm on A, then Å = {a ∈ A; |a| ≤ 1},
Ǎ = {a ∈ A; |a| < 1}. In particular, Å = A° and Ǎ = A˅." "The proof is straightforward."
**Remark.** "If | | is a pm-semi-norm on A and if |A| is finite, then |A| = {0} or |A| = {0, 1}, and
Ã = A/ker | |."
**Proposition 5 (1.3.1/5).** "A function | |: A → ℝ₊ is a pm-semi-norm if and only if the following
conditions are satisfied for all x, y ∈ A: (a) |0| = 0, (b) |xy| ≤ |x|·|y|, |xⁿ| = |x|ⁿ for all
n ≥ 1, (c) |x + y| ≤ max{|x|, |y|}. Furthermore, if | | satisfies (b), then condition (c) is
equivalent to (c') |x + y| ≤ |x| + |y|, and |n| ≤ 1 for all n ∈ ℕ."
*Proof (pp. 31–32).* "If | | is a semi-norm on A, then |−x| = |x| for all x ∈ A (cf. Proposition
1.1.1/3). Therefore, any pm-semi-norm | | satisfies conditions (a), (b) and (c). Conversely, assume
that | | satisfies these conditions. Then |1| = |1|² = |−1|² by condition (b), hence |1| ≤ 1 and
|−1| = |1| ≤ 1. In particular, we have |x| ≤ |−x| |−1| ≤ |−x| and, similarly, |−x| ≤ |x| so that
|x| = |−x| for all x ∈ A. Thus, from (c), one deduces |x − y| ≤ max{|x|, |y|}, and it is clear that
| | is a pm-semi-norm. It remains only to show that condition (c') implies (c) if (b) holds for
| |. Using (x + y)ⁿ = Σ_{ν=0}^n C(n,ν) x^ν y^{n−ν}, we get
|x + y|ⁿ = |(x + y)ⁿ| ≤ Σ |C(n,ν)| |x^ν| |y^{n−ν}| ≤ Σ |x|^ν |y|^{n−ν} since C(n,ν) ∈ ℕ and therefore
|C(n,ν)| ≤ 1. Assume |x| ≤ |y|. Then |x + y|ⁿ ≤ (n + 1)|y|ⁿ; i.e., |x + y| ≤ ⁿ√(n+1) |y|. As
lim ⁿ√(n+1) = 1, we see that |x + y| ≤ |y| = max{|x|, |y|}. □"

### 1.3.2 Smoothing procedures for semi-norms (pp. 32–33)

"First we describe a procedure that allows us to derive a power-multiplicative semi-norm from an
arbitrarily given semi-norm. If | | is any semi-norm on A, we define a new function | |': A → ℝ₊
by setting |x|' := inf_{n≥1} |xⁿ|^{1/n}, x ∈ A. First we claim |x|' = lim_{n→∞} |xⁿ|^{1/n} for all
x ∈ A."
*Proof.* "Fix x ∈ A and set ρ := inf_{n≥1} |xⁿ|^{1/n}. Clearly, 0 ≤ ρ ≤ |x|. For each ε > 0, we can
find an integer m such that |x^m|^{1/m} ≤ ρ + ε. Each n ∈ ℕ can be written in the form n = qm + r,
q, r ∈ ℕ, 0 ≤ r < m. This implies |xⁿ|^{1/n} ≤ (|x^m|^q |x^r|)^{1/n} ≤ (ρ + ε)^{(1 − r/n)} |x^r|^{1/n}.
Now |x^r|^{1/n} tends to 1 or 0 for all r, 0 ≤ r < m. Since r/n → 0, we get ρ ≤ |xⁿ|^{1/n} ≤ ρ + 2ε
for large n; i.e., lim_{n→∞} |xⁿ|^{1/n} = ρ. □"
**Proposition 1 (1.3.2/1).** "The function | |': A → ℝ₊ is a power-multiplicative semi-norm on A.
We have | |' ≤ | |. The equation |a|' = |a| holds whenever a is power-multiplicative with respect
to | |. If c is multiplicative with respect to | |, then c is also multiplicative with respect to
| |'."
*Proof (pp. 32–33).* "The equations |0|' = 0 and |1|' ≤ 1 are trivial. Furthermore, we have
|xy|' = lim |(xy)ⁿ|^{1/n} ≤ lim (|xⁿ|^{1/n})(|yⁿ|^{1/n}) = (lim |xⁿ|^{1/n})(lim |yⁿ|^{1/n}) = |x|'|y|'
for all x, y ∈ A. Next we verify the triangle inequality (this is the only non-trivial point in the
proof). Let x, y ∈ A be given. Then |x − y|' ≤ |(x − y)ⁿ|^{1/n} ≤ max_{μ+ν=n} {|x^μ| |y^ν|}^{1/n}.
For each n, we choose μ(n) and ν(n) such that μ(n) + ν(n) = n and |(x − y)ⁿ| ≤ |x^{μ(n)}| |y^{ν(n)}|.
Since 0 ≤ μ(n)/n ≤ 1, we can choose a sequence (n_i) ⊂ ℕ such that α := lim μ_i/n_i exists, where
μ_i stands for μ(n_i). The limit β := lim ν_i/n_i, where ν_i := ν(n_i), also exists, and we have
α + β = 1. Now it is enough to show that lim sup |x^{μ_i}|^{1/n_i} ≤ |x|'^α and
lim sup |y^{ν_i}|^{1/n_i} ≤ |y|'^β. Namely, if ε > 0 is given, this yields for i ∈ ℕ big enough
|(x − y)^{n_i}|^{1/n_i} ≤ |x^{μ_i}|^{1/n_i} |y^{ν_i}|^{1/n_i} ≤ |x|'^α |y|'^β + ε ≤ max{|x|', |y|'} + ε.
To verify the stated estimates, first assume α ≠ 0. Then lim μ_i = ∞ and
lim |x^{μ_i}|^{1/n_i} = lim (|x^{μ_i}|^{1/μ_i})^{μ_i/n_i} = |x|'^α. If α = 0, we have
lim sup |x^{μ_i}|^{1/n_i} ≤ lim sup |x|^{μ_i/n_i} ≤ 1 = |x|'^α. Hence lim sup |x^{μ_i}|^{1/n_i} ≤ |x|'^α
in all cases. The analogous inequality for y is proved in the same way. Thus, | |' is a semi-norm.
The inequality | |' ≤ | | is clear by definition of | |'. For each x ∈ A and each exponent m, we
have |x^m|' = lim_n |x^{mn}|^{1/n} = lim_{mn} (|x^{mn}|^{1/mn})^m = |x|'^m; i.e., | |' is
power-multiplicative. If |aⁿ| = |a|ⁿ for all n ≥ 1, clearly |aⁿ|^{1/n} = |a|, and hence |a|' = |a|.
If c is multiplicative with respect to | |, we have |(cx)ⁿ| = |c|ⁿ|xⁿ| for all x ∈ A. Therefore
|cx|' = lim |(cx)ⁿ|^{1/n} = lim |c| |xⁿ|^{1/n} = |c| lim |xⁿ|^{1/n} = |c|·|x|'. □"
**Remark.** "The topology induced by | | is finer (and in most cases strictly finer) than the
topology induced by | |'. The power-multiplicative semi-norm | |' is sometimes referred to as the
spectral semi-norm on A induced by | |."

## 1.5 Non-Archimedean valuations (p. 41)

"Let A be a commutative ring with identity 1."
### 1.5.1 Valued rings
**Definition 1 (1.5.1/1).** "A map | |: A → ℝ, where A ≠ 0, is called a (non-Archimedean) valuation
on A if (a) |0| = 0 and |x| > 0 for all x ≠ 0, (b) |x − y| ≤ max{|x|, |y|}, (c) |xy| = |x|·|y|.
From (c) one gets |1| ≤ 1; hence, a valuation on A is a norm on A such that all elements ≠ 0 are
multiplicative. The pair (A, | |) will be called a valued ring. Condition (c) immediately implies
the following: A valued ring is an integral domain. The ideal Ǎ is prime in Å; hence Ã is also an
integral domain."
**Proposition 4 (1.5.1/4).** "Each valuation | | on A can be uniquely extended to a valuation on the
field of fractions Q of A."

### 1.5.3 The Gauss-Lemma (pp. 43–44)
"First we write down a simple sufficient condition for a norm to be a valuation."
**Proposition 1 (1.5.3/1).** "Let (A, | |) be a normed ring with the following properties:
(i) for each a ∈ A, a ≠ 0, there exists a multiplicative element m ∈ A and an exponent s ∈ ℕ such
that |ma^s| = |m| |a|^s = 1,
(ii) A~ = A°/A˅ is an integral domain.
Then | | is a valuation on A."
*Proof.* "Assume there are elements a₁, a₂ ∈ A such that |a₁a₂| < |a₁| |a₂|. Clearly a₁ ≠ 0, a₂ ≠ 0.
By (i) we may choose m_ν ∈ A and s_ν ≥ 1 such that |m_ν| |a_ν|^{s_ν} = |m_ν a_ν^{s_ν}| = 1 and hence,
m_ν a_ν^{s_ν} ∈ A° − A˅, ν = 1, 2. Assume s₂ ≥ s₁. Since m_ν is multiplicative, we get
|(m₁a₁^{s₁})(m₂a₂^{s₂})| = |m₁|·|m₂|·|a₁^{s₁}a₂^{s₂}| ≤ |m₁| |m₂| |a₁a₂|^{s₁} |a₂|^{s₂−s₁}
< |m₁|·|m₂|·(|a₁|·|a₂|)^{s₁}·|a₂|^{s₂−s₁} = |m₁| |a₁|^{s₁}·|m₂| |a₂|^{s₂} = 1.
Thus, (m₁a₁^{s₁})(m₂a₂^{s₂}) ∈ A˅. However, this is in contradiction with the fact that, by
condition (ii), the ideal A˅ is prime in A°. □"
**Remark (p. 44).** "If in Proposition 1 one weakens condition (ii) to 'A~ is reduced', the same
type of proof shows that | | is a power-multiplicative norm."

### 1.5.4 Spectral value of monic polynomials (pp. 44–45)
"Let (A, | |) be a semi-normed ring. For each monic polynomial p = X^m + a₁X^{m−1} + ⋯ + a_m ∈ A[X]
of degree m ≥ 1, we set σ(p) := max_{1≤μ≤m} |a_μ|^{1/μ}, and call σ(p) the spectral value of p. The
use of the adjective 'spectral' will be motivated later. Note that
σ(p) ≤ max{1, |a₁|, …, |a_m|} = Gauss norm of p and that σ(X^m) = 0. The spectral function σ has
the following fundamental property:"
**Proposition 1 (1.5.4/1), p. 45.** "Let p, q ∈ A[X] be monic. Then σ(pq) ≤ max{σ(p), σ(q)}. If
σ(p) ≠ σ(q) or if | | is a valuation, the above inequality is, in fact, an equality."
*Proof.* "(1) We set a₀ := 1, b₀ := 1 and write p = Σ_{μ=0}^m a_μ X^{m−μ}, q = Σ_{ν=0}^n b_ν X^{n−ν}.
Then pq = Σ_{λ=0}^{m+n} c_λ X^{m+n−λ}, where c_λ = Σ_{μ+ν=λ} a_μ b_ν. From |a_μ| ≤ σ(p)^μ,
|b_ν| ≤ σ(q)^ν, μ = 0, …, m; ν = 0, …, n, (where σ(p)⁰ = σ(q)⁰ = 1), we conclude
|c_λ| ≤ max_{μ+ν=λ} {|a_μ| |b_ν|} ≤ max_{μ+ν=λ} {σ(p)^μ σ(q)^ν}, λ = 1, …, m + n. Suppose
σ(p) ≤ σ(q). Then |c_λ| ≤ max_{μ+ν=λ} {σ(q)^μ σ(q)^ν} = σ(q)^λ. Thus
σ(pq) = max_{1≤λ≤m+n} |c_λ|^{1/λ} ≤ σ(q) = max{σ(p), σ(q)}.
(2) Assume now σ(p) < σ(q). We choose j, 1 ≤ j ≤ n, such that |b_j| = σ(q) [sic: |b_j|^{1/j} = σ(q)]
and consider the coefficient c_j = b_j + a₁b_{j−1} + ⋯ + a_{j−1}b₁ + a_j. From |a_μ| ≤ σ(p)^μ < σ(q)^μ
for all μ ≥ 1 and |b_ν| ≤ σ(q)^ν for all ν ≥ 1, we conclude that
|a_μ b_{j−μ}| ≤ |a_μ| |b_{j−μ}| < σ(q)^μ σ(q)^{j−μ} = σ(q)^j for μ ≥ 1, and hence |c_j| = |b_j| = σ(q)^j.
Since σ(pq) ≥ |c_j|^{1/j}, we see that σ(pq) ≥ σ(q) = max{σ(p), σ(q)}.
(3) Assume now that | | is a valuation. We only have to deal with the case σ(p) = σ(q). Just as in
the classical proof of the Gauss Lemma, let i (resp. j) be the smallest index ≥ 1 such that
|a_i| = σ(p)^i (resp. |b_j| = σ(q)^j). We consider c_{i+j} = a_i b_j + Σ'_{μ+ν=i+j} a_μ b_ν where Σ'
means that the pair (i, j) is to be omitted. Now |a_μ b_ν| < σ(p)^μ σ(q)^ν = σ(q)^{i+j} for all
(μ, ν) ≠ (i, j) with μ + ν = i + j. Since |a_i b_j| = |a_i| |b_j| = σ(q)^{i+j}, we get
|c_{i+j}| = σ(q)^{i+j}, and therefore σ(pq) ≥ |c_{i+j}|^{1/(i+j)} = σ(q) = max{σ(p), σ(q)}. □"
