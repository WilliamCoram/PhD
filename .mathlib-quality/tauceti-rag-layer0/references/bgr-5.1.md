# BGR §5.1 — hand transcription from the scan

Source: S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984),
Chapter 5 "Strictly convergent power series", §5.1 "Definition and elementary properties of `Tₙ` and
`T̃ₙ`", pp. 192–198. The PDF (`~/Desktop/Papers/BGR - Non Archimedean Analysis.pdf`) is an image scan
with no text layer; this file was transcribed by eye from page renders (PDF page = book page + 6 in
this range). Mathematics is written in Unicode; `T̊ₙ` is BGR's `T` with a ring accent (power-bounded),
`Ťₙ` the check accent (topologically nilpotent), `T̃ₙ` the tilde (residue ring); `k̊`, `ǩ`, `k̃` likewise
(valuation ring, maximal ideal, residue field of `k`). `Tₙ°`, `Tₙˇ`, `Tₙ~` are BGR's *superscript*
versions (defined by the Gauss norm). Line numbers of this file are the locators used by the board.

## p. 192 — 5.1.1 Description of `Tₙ`

**5.1.1. Description of `Tₙ`.** — Let `k` be a commutative field with a complete non-trivial
non-Archimedean valuation. For `n = 1, 2, …`, define the following subalgebra of the `k`-algebra
`k⟦X₁, …, Xₙ⟧` of formal power series in `n` indeterminates over `k` (cf. (1.4.1)):

    Tₙ(k) := k⟨X₁, …, Xₙ⟩ := { Σ_{ν₁,…,νₙ ≥ 0} a_{ν₁…νₙ} X₁^{ν₁} … Xₙ^{νₙ} ;
                               a_{ν₁…νₙ} ∈ k and |a_{ν₁…νₙ}| → 0 for ν₁ + ⋯ + νₙ → ∞ }.

We call `Tₙ(k)` the (free) *Tate algebra in n indeterminates over k*. The elements of `Tₙ(k)` are
called *strictly convergent power series*. It is easily checked that the inductive definition of
strictly convergent power series in several variables, as given in (1.4.1), is equivalent to the one
given here. In particular, we have `Tₙ(k) = Tₙ₋₁(k)⟨Xₙ⟩`. If the ground field is clear from the
context, we write `Tₙ` instead of `Tₙ(k)`; furthermore, we write `T₀(k) := k`. For simplicity we adopt
the following notation: `X = (X₁, …, Xₙ)`, `ν = (ν₁, …, νₙ)`, `X^ν = X₁^{ν₁} … Xₙ^{νₙ}` and
`|ν| := ν₁ + ⋯ + νₙ`. For `f = Σ_ν a_ν X^ν ∈ Tₙ`, the real number

    |f| := max_ν |a_ν|

is well-defined. Similarly as in (1.4.1), we call `| |` the *Gauss norm* on `Tₙ`. The results of
(1.4.1) immediately give us the following

**Proposition 1.** *`Tₙ(k)` is a `k`-subalgebra of the algebra of formal power series
`k⟦X₁, …, Xₙ⟧`. The Gauss norm is a `k`-algebra norm on `Tₙ(k)` making it into a `k`-Banach algebra
containing the polynomial algebra `k[X₁, …, Xₙ]` as a dense `k`-subalgebra.*

Using the fact that `|Tₙ| = |k|`, we see that every non-zero series can be normed to length 1 by
multiplication with a scalar from `k`:

**Observation 2.** *For every `f ∈ Tₙ − {0}`, there exists `c ∈ k` such that `|cf| = 1`.*

For later reference we add two more remarks.

**Remark 3.** *`Tₙ` is a field if and only if `n = 0`.*

**Remark 4.** *As a `k`-vector space, each `Tₙ(k)`, `n ≥ 1`, is isometrically isomorphic to the space
`c(k)` of all zero sequences over `k`.*

## p. 193 — 5.1.2 and the start of 5.1.3

The first remark follows simply from the fact that `X₁` is not a unit. To prove the second one, just
convert the multiple zero sequences `a_{ν₁…νₙ}` into simple zero sequences by CANTOR's diagonal
procedure. (Remark 4 is a special case of the general fact that every complete `k`-vector space of
countable type and of infinite dimension admits a linear homeomorphism onto `c(k)`; cf. Proposition
2.7.1/2.)

**5.1.2. The Gauss norm is a valuation and `T̃ₙ` is a polynomial ring over `k̃`.** — As in (1.2.4)
and (1.2.5) we set

    Ťₙ := {f ∈ Tₙ ; f topologically nilpotent},
    T̊ₙ := {f ∈ Tₙ ; f power-bounded}.

Then `T̊ₙ` is a subring of `Tₙ`, and `Ťₙ` is a `T̊ₙ`-ideal. The residue ring `T̊ₙ/Ťₙ` is a
`k̃`-algebra; it is denoted by `T̃ₙ`.

**Proposition 1.** *The Gauss norm is a valuation on `Tₙ`.*

**Proposition 2.** *`T̃ₙ = k̃[X]`.*

We give a combined *proof* for both assertions. Following (1.2.3), we use the Gauss norm in order to
define the objects

    Tₙ° := {f ∈ Tₙ ; |f| ≤ 1},
    Tₙˇ := {f ∈ Tₙ ; |f| < 1},
    Tₙ~ := Tₙ° / Tₙˇ.

We can extend the canonical epimorphism `~ : k̊ → k̃` (where `k̊` is the valuation ring of `k` and
`k̃` is the residue field of `k`) to a map `~ : Tₙ° → k̃[X]` by setting

    (Σ a_ν X^ν)~ := Σ ã_ν X^ν ∈ k̃[X].

Obviously the kernel of this map is `Tₙˇ`, and the map is surjective. Therefore we get
`Tₙ~ = k̃[X]`. In particular, the residue algebra `Tₙ~` is an integral domain. Since the Gauss norm
of any non-zero element in `Tₙ` can be adjusted to 1 by scalar multiplication, it is easily verified
that `| |` is a valuation (see Proposition 1.5.3/1). But then we must have `T̊ₙ = Tₙ°`, `Ťₙ = Tₙˇ`,
and hence `T̃ₙ = Tₙ~ = k̃[X]`. □

Alternatively, the above results can be deduced from Corollary 1.5.3/2 and Proposition 1.4.2/2; use
induction on `n`.

**5.1.3. Going up and down between `Tₙ` and `T̃ₙ`.** — By reducing mod `Ťₙ`, we move from power
series to polynomials, thereby simplifying the problems at hand in many cases, as the following
results will show.

**Proposition 1.** *A series `f ∈ Tₙ` with `|f| = 1` is a unit in `Tₙ` if and only if `|f(0)| = 1`
and `|f − f(0)| < 1`. Thus `f` is a unit if and only if `f̃` is a unit (i.e., a constant) in `T̃ₙ`.*

## p. 194 — 5.1.3 continued

*Proof.* Since `| |` is a valuation, `f = Σ a_ν X^ν ∈ Tₙ` with `|f| = 1` is a unit in `Tₙ` if and
only if it is a unit in `T̊ₙ`. Due to Proposition 1.4.2/3 (use induction on `n` and the fact that
`Tₙ` is complete), this is equivalent to `a_{(0,…,0)}` being a unit in `k̊` and `a_ν` belonging to
`ǩ` for all `ν`, `|ν| > 0`. This is the assertion. □

Using the above characterization of units, we get the following technical lemma:

**Lemma 2.** *For each `f ∈ Tₙ` with `|f| = 1`, there is an element `c ∈ k` with `|c| = 1` such that
`c + f` is not a unit in `Tₙ`.*

*Proof.* We shall treat the two cases `|f(0)| < 1` and `|f(0)| = 1` separately. If `|f(0)| < 1`,
then `|f| = 1` implies `|f − f(0)| = 1`. For `g := 1 + f ∈ Tₙ`, we have `|g| = 1` and
`|g − g(0)| = |f − f(0)| = 1`. According to the preceding proposition, `g` is not a unit in `Tₙ`. If
`|f(0)| = 1`, define `g := f − f(0)`. Then `g(0) = 0`, and hence `g` cannot be a unit in `Tₙ`. □

This lemma has two important consequences.

**Proposition 3.** *`⋂_{𝔪 ∈ Max Tₙ} 𝔪 = (0)`, where `Max Tₙ` denotes the set of all maximal ideals
of `Tₙ`.*

*Proof.* Assume that there is a non-zero series `f` contained in all maximal ideals of `Tₙ`. We may
assume that `|f| = 1`. Choose `c ∈ k` with `|c| = 1` such that `c + f` is a non-unit. Then we can
find a maximal ideal `𝔪` such that `c + f ∈ 𝔪`. By assumption, `f` also is an element of `𝔪`. This
implies `c ∈ 𝔪`, which is impossible since `c ∈ k*`. □

**Theorem 4.** *Every `k`-algebra homomorphism `φ : Tₙ → Tₘ` is a contraction, i.e.,
`|φ(f)| ≤ |f|` for all `f ∈ Tₙ`.*

*Proof.* Again we proceed indirectly. Assume that there is an `f ∈ Tₙ` such that `|φ(f)| > |f|`.
Without loss of generality, we may assume that `|φ(f)| = 1`. Choose `c ∈ k` with `|c| = 1` such that
`c + φ(f)` is not a unit in `Tₘ` (Lemma 2). On the other hand, `g := c + f` is a unit in `Tₙ`
according to Proposition 1, since `|g| = 1` and `|g − g(0)| = |f − f(0)| < 1` (because `|f| < 1`).
Hence `φ(g) = c + φ(f)` must be a unit in `Tₘ`, which is a contradiction. □

The proof just given is similar to the proof that a `k`-algebra homomorphism between analytical local
algebras is local.
We draw some conclusions from the above theorem.

**Corollary 5.** *Every `k`-algebra homomorphism `φ : Tₙ → Tₘ` is a continuous substitution
homomorphism; i.e., for any such map `φ`, there are `f₁, …, fₙ ∈ T̊ₘ` such that*

    φ(Σ a_ν X^ν) = Σ a_{ν₁…νₙ} f₁^{ν₁} … fₙ^{νₙ}

*for all series `Σ a_ν X^ν ∈ Tₙ`. More precisely, the map `φ ↦ (φ(X₁), …, φ(Xₙ))` defines a
bijection between `Hom (Tₙ, Tₘ)` and `(T̊ₘ)ⁿ`.*

## p. 195 — 5.1.3 continued

*Proof.* Let `φ : Tₙ → Tₘ` be a `k`-algebra homomorphism. Define `fᵢ := φ(Xᵢ)` for `i = 1, …, n`.
According to the theorem, we have `|fᵢ| ≤ |Xᵢ| = 1`, whence `fᵢ ∈ T̊ₘ`. For `Σ a_ν X^ν ∈ k[X]`, one
clearly has `φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}`. Due to the theorem, `φ` is continuous, and
therefore `φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}` for all `Σ a_ν X^ν ∈ Tₙ`. Thus `φ` is uniquely
determined by the tuple `(φ(X₁), …, φ(Xₙ)) ∈ (T̊ₘ)ⁿ`. Now let `f₁, …, fₙ ∈ T̊ₘ` be given. Then it is
easy to verify that `φ : Tₙ → Tₘ` defined by `φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}` is a
`k`-algebra homomorphism with `φ(Xᵢ) = fᵢ`. Therefore it is clear that the map
`Hom (Tₙ, Tₘ) → (T̊ₘ)ⁿ` given by `φ ↦ (φ(X₁), …, φ(Xₙ))` is bijective. □

**Corollary 6.** *Every `k`-algebra isomorphism `φ : Tₙ → Tₘ` is an isometry.*

This result follows immediately from Theorem 4. It can be improved as follows:

**Corollary 7.** *If `φ : Tₙ → Tₘ` is a `k`-algebra isomorphism, then `n = m` and `φ` is an
isometric automorphism of `Tₙ`.*

*Proof.* The `k`-algebra homomorphisms `φ` and `φ⁻¹` induce `k̃`-algebra homomorphisms
`φ̃ : k̃[X₁, …, Xₙ] → k̃[X₁, …, Xₘ]` and `(φ⁻¹)~ : k̃[X₁, …, Xₘ] → k̃[X₁, …, Xₙ]`. Obviously, `φ̃`
and `(φ⁻¹)~` are inverse to each other. Hence `φ̃` is a `k̃`-algebra isomorphism. Then `φ̃` extends
to an isomorphism `k̃(X₁, …, Xₙ) → k̃(X₁, …, Xₘ)` between the fields of fractions, and by looking at
transcendence degrees over `k̃`, we get `n = m`. □

The proof of Corollary 7 depends on the fact that the bijectivity of `φ` implies the bijectivity of
`φ̃`. The converse of this fact is also true.

**Corollary 8.** *A `k`-algebra endomorphism `φ` of `Tₙ` is bijective if and only if `φ̃` is
bijective.*

*Proof.* We only have to show that "`φ̃` bijective" implies "`φ` bijective". It is easily seen that
`φ` is an isometry if `φ̃` is injective. It remains to show that `φ` is surjective. Therefore assume
that `φ̃` is bijective. There are elements `f₁, …, fₙ ∈ T̊ₙ` such that
`ε := max_{1≤i≤n} |Xᵢ − φ(fᵢ)| < 1`. An easy computation shows that, for any `g = Σ a_ν X^ν ∈ Tₙ`,
one can find an `h ∈ Tₙ` such that `|g − φ(h)| ≤ ε|g|`. Namely, using the standard estimate

    |u₁ … u_r − v₁ … v_r| = |Σ_{i=1}^{r} u₁ … uᵢ v_{i+1} … v_r − u₁ … u_{i−1} vᵢ … v_r|
                          ≤ (max_{1≤i≤r} |uᵢ − vᵢ|) (max_{1≤i≤r} |uᵢ|, |vᵢ|)^{r−1},

we see that the series `h := Σ a_ν f₁^{ν₁} … fₙ^{νₙ}` is as desired. Thus `φ(Tₙ)` is "`ε`-dense" in
`Tₙ`, and Proposition 1.1.4/2 shows that `φ(Tₙ)` is, in fact, dense in `Tₙ`. But `φ` is an isometry,
and hence `φ(Tₙ)` is closed in `Tₙ`. So we must have `φ(Tₙ) = Tₙ`. □

Alternatively, the above result can be obtained by applying the Lifting Theorem 2.7.3/2. — We
conclude this section by considering a special class of

## p. 196 — the Example, and 5.1.4

automorphisms of `Tₙ` which will play an important role in the applications of the WEIERSTRASS
Preparation Theorem.

**Example.** *Let `c₁, …, c_{n−1} ∈ ℕ` be given. Define `φ : Tₙ → Tₙ` by
`φ(X_ν) := X_ν + Xₙ^{c_ν}` for `ν = 1, …, n − 1` and `φ(Xₙ) := Xₙ`. Then `φ` is an isometric
automorphism of `Tₙ`.*

*Proof.* Let `ψ : Tₙ → Tₙ` be defined by `ψ(X_ν) := X_ν − Xₙ^{c_ν}` for `ν = 1, …, n − 1` and
`ψ(Xₙ) := Xₙ`. One easily checks that `ψ` is an inverse of `φ`. Applying Corollary 6, we see that
`φ` is an isometric automorphism of `Tₙ`. □

**5.1.4. `Tₙ` as a function algebra.** — As before, we consider strictly convergent power series
with coefficients in the complete valued field `k`. Let `k_a` be the algebraic closure of `k`
provided with the spectral valuation (which is the unique valuation extending the valuation from
`k`; see Theorem 3.2.4/2). For any valued field `K`, we denote by

    Bⁿ(K) := {(x₁, …, xₙ) ∈ Kⁿ ; max_{1≤ν≤n} |x_ν| ≤ 1}

the `n`-dimensional unit ball (or polydisc) around the origin.

We want to show that each power series `f = Σ a_ν X^ν ∈ Tₙ` defines a map

    Bⁿ(k_a) → k_a,   x ↦ f(x) := Σ a_{ν₁…νₙ} x₁^{ν₁} … xₙ^{νₙ},

which also shall be denoted by `f`. Namely, consider a point `x ∈ Bⁿ(k_a)`, and let `L ⊂ k_a` be a
finite field extension of `k` containing all coordinates `x₁, …, xₙ` of `x`. Then `L` is complete by
Theorem 3.2.4/2. Since `a_ν x^ν` is a zero-sequence in `L`, the series `Σ a_ν x^ν` must converge to
some element in `L`. Thus we see that, for all `x ∈ Bⁿ(k_a)`, the element `f(x)` is well-defined in
`k_a`. In particular, `f(x) ∈ k` for all `x ∈ Bⁿ(k)`.

Conversely, every `k_a`-valued function `f : Bⁿ(k_a) → k_a` admitting a power series expansion (with
coefficients in `k_a`) converging for all `x ∈ Bⁿ(k_a)` and satisfying the additional requirement
`f(Bⁿ(k)) ⊂ k` comes from a strictly convergent power series in the manner described above. Namely,
if one starts with a power series `f = Σ c_ν X^ν ∈ k_a⟦X₁, …, Xₙ⟧`, the requirement that it must
converge for `x = (1, …, 1)` immediately yields `|c_ν| → 0` for `ν₁ + ⋯ + νₙ → ∞`. It remains to
show that the second condition "`f(Bⁿ(k)) ⊂ k`" implies `c_ν ∈ k` for all `ν`. [The argument, by
splitting `f = f₁ + f₂` and an induction on the number of variables, runs to the middle of p. 197; it
is not used by the board and is not transcribed.]

## p. 197 — 5.1.4 continued

We summarize the preceding considerations in the following

**Proposition 1.** *The series of `Tₙ(k)` give rise to exactly those functions
`f : Bⁿ(k_a) → k_a` which*

  *(i) have a power series expansion over `k_a` converging on the whole unit ball `Bⁿ(k_a)` and*
  *(ii) map `Bⁿ(k)` into `k`.*

*If `L ⊂ k_a` is any finite algebraic extension of `k`, then `f(Bⁿ(L)) ⊂ L` for all `f ∈ Tₙ(k)`.*

Later on (cf. Corollary 5), we shall see that two power series of `Tₙ(k)` induce the same function
`Bⁿ(k_a) → k_a` if and only if they coincide. To prove this fact, we have to look at the norm of
uniform convergence on `Bⁿ(k_a)`.

**Proposition 2.** *Let `f` be a series in `Tₙ`. Then `sup_{x ∈ Bⁿ(k_a)} |f(x)| ≤ |f|`, and `f`
gives rise to a continuous function on `Bⁿ(k_a)`.*

*Proof.* For all `x ∈ Bⁿ(k_a)` and all `ν`, we have `|a_ν x^ν| ≤ |a_ν| ≤ |f|` if `f = Σ a_ν X^ν`.
Therefore, `|f(x)| ≤ max |a_ν x^ν| ≤ |f|`, whence the first assertion follows. Furthermore, `f` is a
uniform limit of polynomials and hence continuous. □

Let `~ : Bⁿ(k_a) = k̊_aⁿ → k̃_aⁿ` denote the obvious extension of the residue map `~ : k̊ → k̃`. It
is easy to see that the following diagram

    k̊_aⁿ ──f──→ k̊_a
      │~            │~
      ↓             ↓
    k̃_aⁿ ──f̃──→ k̃_a

is commutative for all `f ∈ T̊ₙ`. (In the diagram, `f̃` stands for the map induced by the polynomial
`f̃ ∈ k̃_a[X₁, …, Xₙ]`.) We shall use this connection between the functions in `Tₙ` and the
polynomials over `k̃` associated to them to show that the inequality in Proposition 2 is actually an
equality.

**Proposition 3** (Maximum Modulus Principle). *For all `f ∈ Tₙ`, there is an `x ∈ Bⁿ(k_a)` such
that `|f(x)| = |f|`. If `|f(x)| = |f|` for some `x ∈ ǩ_aⁿ`, then `|f(x)| = |f|` for all
`x ∈ ǩ_aⁿ`. These assertions remain valid if `k_a` is replaced by any field extension `L ⊂ k_a` of
`k`, provided `L̃` is infinite.*

## p. 198 — 5.1.4 concluded

*Proof.* We may assume `|f| = 1`. Since the residue field `k̃_a` of `k_a` equals the algebraic
closure of `k̃` (see Lemma 3.4.1/4), it has infinitely many elements. Then there must be a point
`x = (x₁, …, xₙ) ∈ Bⁿ(k_a)` such that `f̃(x̃₁, …, x̃ₙ) ≠ 0`, i.e., `(f(x))~ ≠ 0`, which is
equivalent to `|f(x)| = 1`. So the first assertion is proved.

From `|f(x)| = 1` for some `x ∈ ǩ_aⁿ`, we can conclude `f̃(0, …, 0) ≠ 0`, which again is equivalent
to `(f(x))~ ≠ 0` or `|f(x)| = 1` for all `x ∈ ǩ_aⁿ`. The only property of `k_a` (besides being
valued) needed for the proof was the fact that `k̃_a` had to be infinite. Hence the last remark of
the proposition is also justified. □

The preceding proposition can be strengthened in the following way:

**Proposition 4.** *The maximum of the values taken by a strictly convergent power series `f` is
assumed on the subset `{(x₁, …, xₙ) ∈ Bⁿ(k_a) ; |x₁| = ⋯ = |xₙ| = 1}` of the unit ball `Bⁿ(k_a)`.*

*Proof.* Use the fact that the Gauss norm is a valuation on `Tₙ` (Proposition 5.1.2/1), and apply
Proposition 3 to the series `X₁ … Xₙ f`. □

**Corollary 5** (Identity Theorem). *If `f ∈ Tₙ` vanishes for all `x ∈ Bⁿ(k_a)`, then `f = 0`.
Therefore the map associating to a series `f ∈ Tₙ` its corresponding function from `Bⁿ(k_a)` to
`k_a` is an injection.*

*Proof.* If `f` induces the zero function, then `|f| = sup_{x∈Bⁿ(k_a)} |f(x)| = 0` and hence
`f = 0`. □

This is a rather weak version of the Identity Theorem. Using elementary methods, one can show the
following much better statement: The zero set of a strictly convergent series `f ≠ 0` is nowhere
dense in `Bⁿ(k_a)`. In the one variable case, the WEIERSTRASS Preparation Theorem will tell us that a
non-zero series has only a finite number of zeros.

**Corollary 6.** *`Tₙ` is a Banach function algebra satisfying the Maximum Modulus Principle. The
Gauss norm `| |` and the supremum norm `| |_sup` coincide on `Tₙ`.*

*Proof.* For the definition of `| |_sup` and of Banach function algebras see (3.8). Since
`| |_sup ≤ | |` by Corollary 3.8.2/2, we have only to show that, for each `f ∈ Tₙ`, there exists a
`k`-algebraic maximal ideal `𝔪 ⊂ Tₙ` such that `|f(𝔪)| = |f|`. In order to do this, consider a point
`x = (x₁, …, xₙ) ∈ Bⁿ(k_a)` such that `|f(x)| = |f|` (Proposition 3). Denote by
`L := k(x₁, …, xₙ)` the extension of `k` generated by the components of `x`. Then `L` is finite over
`k`, and due to the last assertion of Proposition 1, there is an evaluation homomorphism

    h_x : Tₙ → L,   g ↦ h_x(g) := g(x).

Since the image of `h_x` contains `k` and the elements `x₁, …, xₙ`, it follows that `h_x` is
surjective. Thus `𝔪_x := ker h_x` is a `k`-algebraic maximal ideal in `Tₙ`, and `Tₙ/𝔪_x` is
isomorphic to `L` over `k`. Corresponding elements in `Tₙ/𝔪_x` and `L` must have the same spectral
norm over `k` so that `|g(𝔪_x)| = |g(x)|` for all `g ∈ Tₙ`. In particular, we have
`|f(𝔪_x)| = |f(x)| = |f|`. □

## p. 199 — 5.1.4 concluded: endomorphisms and affinoid charts

The proof relies on the fact that the sets `Bⁿ(k_a)`, `Hom_k (Tₙ, k_a)`, and `Max_k Tₙ` are
essentially the same. This point of view shall be elaborated on in more detail in (7.1.1).

We now give a geometric interpretation of algebra homomorphisms `Tₙ → Tₘ`. Let `φ : Tₙ → Tₘ` be such
a homomorphism, and consider the elements `fᵢ := φ(Xᵢ)` for `i = 1, …, n`. By Proposition 2 and
Theorem 5.1.3/4, we have `|fᵢ(x)| ≤ |fᵢ| ≤ |Xᵢ| = 1` for all `x ∈ Bᵐ(k_a)`, `i = 1, …, n`. Therefore
by defining `φ′(x₁, …, xₘ) := (f₁(x₁, …, xₘ), …, fₙ(x₁, …, xₘ))`, one gets a map
`φ′ : Bᵐ(k_a) → Bⁿ(k_a)`. If we call a mapping `ψ : Bᵐ(k_a) → Bⁿ(k_a)` affinoid whenever its
coordinate mappings `ψᵢ : Bᵐ(k_a) → k_a` are given by elements of `Tₘ`, then `φ ⇝ φ′` is a
contravariant functor from the category `{Tₙ ; n ∈ ℕ}` with `k`-algebra homomorphisms as morphisms
into the category `{Bⁿ(k_a) ; n ∈ ℕ}` with affinoid mappings as morphisms.

Using the Identity Theorem, one easily deduces the following

**Proposition 7.** *Let `φ` be a `k`-algebra endomorphism of `Tₙ`. Then `φ` is bijective if and only
if the corresponding map `φ′ : Bⁿ(k_a) → Bⁿ(k_a)` is bi-affinoid (i.e., `φ′` is bijective, and `φ′`
as well as `φ′⁻¹` are affinoid).*

When considering automorphisms of `Tₙ`, it is convenient to look at special topological generating
systems of `Tₙ`.

**Definition 8.** *A system `{f₁, …, fₙ} ⊂ Tₙ` is called an affinoid chart of `Tₙ` if there is a
`k`-algebra automorphism `φ` of `Tₙ` with `φ(Xᵢ) = fᵢ` for `i = 1, …, n`, i.e., if every `f ∈ Tₙ` can
be written uniquely as `f = Σ a_{ν₁…νₙ} f₁^{ν₁} … fₙ^{νₙ}` with `a_ν ∈ k` and `|a_ν| → 0`.*

**Remark.** It can be shown that `{f₁, …, fₙ} ⊂ T̊ₙ` is already a chart if the map defined by
`Xᵢ ↦ fᵢ`, `i = 1, …, n`, is surjective. Loosely speaking, we could rephrase this in the following
way: if a generating system has minimal length, the representation of any series by it is uniquely
determined.

Using Corollary 5.1.3/8, we find the following characterization of charts:

**Proposition 9.** *The system `{f₁, …, fₙ} ⊂ T̊ₙ` is an affinoid chart of `Tₙ` if and only if
`{f̃₁, …, f̃ₙ}` generates `T̃ₙ` as a `k̃`-algebra.*

*Proof.* Define `φ : Tₙ → Tₙ` by `φ(Xᵢ) = fᵢ`, `i = 1, …, n`. The map `φ` is an automorphism if and
only if `φ̃` is an automorphism of `T̃ₙ`. The latter is equivalent to `φ̃` being surjective. Namely
if `φ̃` is surjective, consider the isomorphism `T̃ₙ/ker φ̃ → T̃ₙ` and extend it to an isomorphism
`Q(T̃ₙ/ker φ̃) → Q(T̃ₙ)` between the fields of fractions. By looking at transcendence degrees over
`k̃`, we see that `Q(T̃ₙ/ker φ̃)` must have transcendence degree `n`. However this can only be true
if `ker φ̃ = 0`. □

Specializing to the case of one variable, we get the following description of the "group of
automorphisms of the unit disc". [Corollary 10 is on p. 200; see `bgr-5.2.md`.]
