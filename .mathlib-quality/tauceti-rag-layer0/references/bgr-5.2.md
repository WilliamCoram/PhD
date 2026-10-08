# BGR §5.2 — hand transcription from the scan

Source: S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984),
Chapter 5, §5.2 "Weierstrass-Rückert theory for `Tₙ`", pp. 200–211 (and the end of §5.1.4 on
p. 200). Transcribed by eye from page renders of the scan (PDF page = book page + 6). Notation as in
`bgr-5.1.md`. Line numbers of this file are the locators used by the board.

## p. 200 — end of 5.1.4; 5.2.1 Weierstrass Division Theorem

**Corollary 10.** *The series `f = Σ_{ν=0}^∞ a_ν X^ν ∈ T₁` defines a bi-affinoid map of the unit
disc onto itself if and only if `|a₀| ≤ 1`, `|a₁| = 1` and `|a_ν| < 1` for all `ν > 1`.*

*Proof.* The system `{f}` is a chart of `T₁` if and only if `|f| ≤ 1` and `f̃ = Σ ã_ν X^ν` generates
`k̃[X]`. This is equivalent to `|a_ν| ≤ 1` for all `ν`, `ã₁ ≠ 0` and `ã_ν = 0` for `ν > 1`. □

A remark one should add is that, contrary to the classical complex case, the automorphism group of
the unit disc has infinitely many parameters.

### 5.2. Weierstrass-Rückert theory for `Tₙ`

There are basically two ways to get further information on `Tₙ` and on finite `Tₙ`-modules. One can
prove the WEIERSTRASS Preparation Theorem and then follow rather closely the classical method of
RÜCKERT, or one can use the Lifting Theorem 2.7.3/2 and derive the desired results from well-known
facts about the polynomial algebra `T̃ₙ`. Here we shall follow the first approach; for the second
one, refer to [2].

**5.2.1. Weierstrass Division Theorem.** — Let us start with

**Definition 1.** *A strictly convergent power series
`g = Σ_{ν=0}^∞ g_ν(X₁, …, X_{n−1}) Xₙ^ν` is `Xₙ`-distinguished of degree `s` if*

  *(1) `g_s` is a unit in `T_{n−1}` and*
  *(2) `|g_s| = |g|` and `|g_s| > |g_ν|` for all `ν > s`.*

It is easy to see that a power series `g ∈ Tₙ` with `|g| = 1` is `Xₙ`-distinguished of degree `s` if
and only if `g̃ ∈ T̃ₙ` is a unitary polynomial of degree `s` in the polynomial ring
`k̃[X₁, …, X_{n−1}][Xₙ]`. (Recall that a polynomial is called unitary if its highest coefficient is a
unit, and use Proposition 5.1.3/1.) This remark already gives an idea of how to proceed if one wishes
to carry out a division by a distinguished element `g` with `|g| = 1`. Namely, just use EUCLID's
division in `k̃[X₁, …, X_{n−1}][Xₙ]` and then pull back the results to `Tₙ`. To describe this
procedure precisely, let us state the so-called WEIERSTRASS Division Theorem.

**Theorem 2.** *Let `g ∈ Tₙ` be `Xₙ`-distinguished of degree `s`. Then for each `f ∈ Tₙ`, there
exist uniquely determined elements `q ∈ Tₙ` and `r ∈ T_{n−1}[Xₙ]` with `deg r < s` such that*

    f = qg + r.

*One has the following estimates*

    |f| = max {|q| |g|, |r|};   i.e.,   |q| ≤ |g|⁻¹ |f|   and   |r| ≤ |f|.

*If, in addition, `f` and `g` are polynomials in `T_{n−1}[Xₙ]` and if `g` has degree `s`, then also
`q` is a polynomial in `T_{n−1}[Xₙ]`.*

## p. 201 — proof of the Division Theorem; 5.2.2 Preparation Theorem

*Proof.* Without loss of generality, we may assume `|g| = 1`. First we show that the existence of a
representation

    (*)   f = qg + r,   r ∈ T_{n−1}[Xₙ],   deg r < s,   q ∈ Tₙ

implies the estimates `|q| ≤ |f|` and `|r| ≤ |f|`. This can be seen as follows. By multiplying (*)
with a scalar from `k`, we may assume

    (**)   max {|q|, |r|} = 1,

which implies `|f| ≤ 1`. We have to show `|f| = 1`. Assume the contrary. Then we would have
`0 = f̃ = q̃g̃ + r̃`. Since `deg g̃ = s > deg r ≥ deg r̃`, this would imply `q̃ = r̃ = 0`, in
contradiction to (**). So we have verified the estimates. Now it is trivial to show uniqueness.
Namely if one has a representation `0 = qg + r`, `r ∈ T_{n−1}[Xₙ]`, `deg r < s`, `q ∈ Tₙ`, the
estimates just verified yield `q = r = 0`.

Next we want to show the existence of the representation (*). Define
`B := {qg + r ; r ∈ T_{n−1}[Xₙ], deg r < s, q ∈ Tₙ}`. It follows from what we have shown above that
`B` is a closed subgroup of `Tₙ`. We claim `B = Tₙ`. Writing
`g = Σ_{ν=0}^∞ g_ν(X₁, …, X_{n−1}) Xₙ^ν`, we define `ε := max_{ν>s} {|g_ν|}`, where `ε < 1`.
Furthermore, set `k_ε := {x ∈ k ; |x| ≤ ε}` and `k̃_ε := k̊/k_ε`. Then there is a natural ring
epimorphism `τ_ε : T̊ₙ → k̃_ε[X₁, …, Xₙ]` with `ker τ_ε = {f ∈ Tₙ ; |f| ≤ ε}`, and `τ_ε(g)` is a
unitary polynomial in `Xₙ` of degree `s`. Therefore, EUCLID's division with respect to `τ_ε(g)` is
possible in the ring `(k̃_ε[X₁, …, X_{n−1}])[Xₙ]`. So for all `f ∈ T̊ₙ`, we can find `q ∈ T̊ₙ` and
`r ∈ T̊_{n−1}[Xₙ]` with `deg r < s` such that `τ_ε(f) = τ_ε(q) τ_ε(g) + τ_ε(r)`, or equivalently
`|f − (qg + r)| ≤ ε`. Hence, for all `f ∈ Tₙ`, there is an element `b ∈ B` such that
`|f − b| ≤ ε|f|`. Therefore `B` is `ε`-dense in `Tₙ`, and Proposition 1.1.4/2 says that `B`, in
fact, is dense in `Tₙ`. Since `B` is closed in `Tₙ`, we get `B = Tₙ`. Hence every `f ∈ Tₙ` admits a
representation (*).

Only the last statement of the theorem remains to be shown. If `g ∈ T_{n−1}[Xₙ]` and `deg g = s`,
then `g` is a unitary polynomial, and EUCLID's division with respect to `g` can be applied in
`T_{n−1}[Xₙ]`. For every `f ∈ T_{n−1}[Xₙ]`, one can find polynomials `q, r ∈ T_{n−1}[Xₙ]` with
`deg r < s` such that `f = qg + r`. Due to the uniqueness of `q` and `r`, the last assertion is
clear. □

**5.2.2. Weierstrass Preparation Theorem.** — As an easy application we deduce the Preparation
Theorem.

**Theorem 1.** *Let `g ∈ Tₙ` be `Xₙ`-distinguished of degree `s`. Then there are a unique monic
polynomial `ω ∈ T_{n−1}[Xₙ]` of degree `s` and a unique unit `e ∈ Tₙ` such that `g = e·ω`. One has:
`|ω| = 1` so that `ω` is `Xₙ`-distinguished of degree `s`. If `g ∈ T_{n−1}[Xₙ]`, then also
`e ∈ T_{n−1}[Xₙ]`.*

*Proof.* By the WEIERSTRASS Division Theorem, there exist `e′ ∈ Tₙ` and `r′ ∈ T_{n−1}[Xₙ]` with
`deg r′ < s` such that `Xₙ^s = e′g + r′`. Define `ω := Xₙ^s − r′`. Then `ω` is a monic polynomial in
`T_{n−1}[Xₙ]` of degree `s` and `ω = e′g`. To complete the existence part of the theorem, we only
have to show that `e′` is a unit. Since

## p. 202 — 5.2.2 concluded; 5.2.3 Weierstrass polynomials

`|r′| ≤ |Xₙ^s| = 1`, we see that `|ω| = 1` and that `ω` is `Xₙ`-distinguished of degree `s`. We may
assume `|g| = 1`. From `ω̃ = ẽ′g̃`, we conclude that `ẽ′` is a unit in `T̃_{n−1}`, because `ω̃` and
`g̃` are unitary polynomials of the same degree. Then `ẽ′` is a fortiori a unit in `T̃ₙ`, and
therefore `e′` is a unit in `Tₙ` (see Proposition 5.1.3/1). This proves the existence part of the
theorem. Now let `ω ∈ T_{n−1}[Xₙ]` be a monic polynomial of degree `s` and `e` be a unit in `Tₙ`
such that `g = e·ω`. Define `r := Xₙ^s − ω`. Then one has `Xₙ^s = e⁻¹g + r`. The series `g` being
given, this relation uniquely determines `e` and `r`, and therefore also `ω`. If `g ∈ T_{n−1}[Xₙ]`,
then according to the last assertion of the Division Theorem, also `e` must be a polynomial in
`T_{n−1}[Xₙ]`. □

**5.2.3. Weierstrass polynomials and Weierstrass Finiteness Theorem.** — The polynomials
`ω ∈ T_{n−1}[Xₙ]` appearing in the preceding theorem will play an important role later on. Therefore
we introduce a special name for them.

**Definition 1.** *A Weierstrass polynomial (in `Xₙ`) is a monic polynomial `ω ∈ T_{n−1}[Xₙ]` with
`|ω| = 1`.*

For later reference we mention the following simple fact:

**Lemma 2.** *Let `ω₁` and `ω₂` be monic polynomials in `T_{n−1}[Xₙ]`. If `ω₁·ω₂` is a Weierstrass
polynomial, then `ω₁` and `ω₂` are Weierstrass polynomials.*

*Proof.* Since `ω₁` and `ω₂` are monic, we have `|ωᵢ| ≥ 1` for `i = 1, 2`. On the other hand,
`|ω₁| |ω₂| = |ω₁·ω₂| = 1`, and therefore we get `|ωᵢ| = 1`. □

The importance of the concept of Weierstrass polynomials is shown by the fact that, for every
`Xₙ`-distinguished power series `g`, there is a Weierstrass polynomial `ω` with `ωTₙ = gTₙ`.
Moreover, we have the following

**Proposition 3.** *Let `ω` be a Weierstrass polynomial of degree `s` in `Xₙ`. Then*

  *(i) `Tₙ/ωTₙ` is a finite free `T_{n−1}`-module;*
  *(ii) `T_{n−1}[Xₙ]/ωT_{n−1}[Xₙ] ≅ Tₙ/ωTₙ`.*

*More explicitly, the sequence*

    T_{n−1}^s ──j──→ T_{n−1}[Xₙ] ──i──→ Tₙ,

*where `T_{n−1}^s` is the `s`-fold normed direct sum of copies of `T_{n−1}`, where `j` is given by
`j(t₀, …, t_{s−1}) := Σ_{ν=0}^{s−1} t_ν Xₙ^ν`, and where `i` is the natural injection, induces a
sequence of isometric `T_{n−1}`-module isomorphisms*

    T_{n−1}^s ──j̄──→ T_{n−1}[Xₙ]/ωT_{n−1}[Xₙ] ──ī──→ Tₙ/ωTₙ.

*The map `ī` is the `k`-algebra isomorphism mentioned in (ii).*

## p. 203 — proof of Proposition 3; the Finiteness Theorem

*Proof.* We consider the following commutative diagram of `T_{n−1}`-module homomorphisms:

                 T_{n−1}[Xₙ] ────i────→ Tₙ
               j↗      │ψ                │π
    T_{n−1}^s          ↓                 ↓
               j̄↘ T_{n−1}[Xₙ]/ωT_{n−1}[Xₙ] ──ī──→ Tₙ/ωTₙ

where `ψ` and `π` are the canonical residue epimorphisms and `ī` and `j̄` are induced by `i` and `j`,
respectively. The existence statement of the WEIERSTRASS Division Theorem tells us that `π∘i∘j` and
`ψ∘j` are surjective. Hence `ī` and `j̄` must be surjective. Furthermore, the uniqueness part of the
Division Theorem shows that `π∘i∘j` is injective, whence the injectivity of `j̄` and `ī` follows.
Thus, `ī` and `j̄` are bijections. Obviously, `ī` is not only a `T_{n−1}`-module isomorphism, but
also a `k`-algebra isomorphism, because `i`, `ψ` and `π` are `k`-algebra homomorphisms. It remains
to be shown that `ī` and `j̄` are isometries if one provides `T_{n−1}[Xₙ]/ωT_{n−1}[Xₙ]` and
`Tₙ/ωTₙ` with the residue norm derived from the Gauss norm on `Tₙ`. Since `ωT_{n−1}[Xₙ]` is dense in
`ωTₙ`, we see that `ī` is an isometry. Furthermore, the map `j̄` is contractive. If `j̄` is not an
isometry, there must exist a tuple `(t₀, …, t_{s−1}) ∈ T_{n−1}^s` and a polynomial
`q ∈ T_{n−1}[Xₙ]` such that `f := qω + Σ_{ν=0}^{s−1} t_ν Xₙ^ν` satisfies

    |f| < max_{0≤ν≤s−1} |t_ν| = |Σ_{ν=0}^{s−1} t_ν Xₙ^ν|.

However this is impossible by the WEIERSTRASS Division Theorem. Thus also `j̄` must be an isometry.
□

The essence of the preceding proposition is rephrased in the following theorem which will turn out
to be a useful tool for proofs by induction on the number of indeterminates.

**Theorem 4** (WEIERSTRASS Finiteness Theorem). *Let `A` be a `k`-Banach algebra, let
`φ : Tₙ → A` be a finite `k`-algebra homomorphism and let `ω ∈ T_{n−1}[Xₙ]` be a Weierstrass
polynomial contained in `ker φ`. Then the map `φ′ : T_{n−1} → A` defined by `φ′ := φ | T_{n−1}` is
also finite. In particular, the `k`-algebra monomorphism `T_{n−1} ↪ Tₙ/ωTₙ` induced by the natural
injection `T_{n−1} ↪ Tₙ` is finite for every Weierstrass polynomial `ω`.*

*Proof.* Let us consider the following commutative diagram

    T_{n−1} ──ε──→ Tₙ ──φ──→ A
          ε̄ ↘      │π      ↗ φ̄
               Tₙ/ωTₙ

## p. 204 — the Finiteness Theorem concluded; 5.2.4 Generation of distinguished power series

where `ε` denotes the natural embedding of `T_{n−1}` into `Tₙ` and `π` the canonical residue
epimorphism. The maps `ε̄` and `φ̄` are induced by `ε` and `φ`, respectively, in an obvious manner.
Since `φ` is finite, so is `φ̄`. By the preceding proposition, `Tₙ/ωTₙ` is a finite
`T_{n−1}`-module via `ε̄`; i.e., the map `ε̄` is finite. Then `φ̄∘ε̄` is also finite. Since
`φ′ = φ∘ε = φ̄∘ε̄`, the proof is finished. □

At this point we would like to mention without proof a stronger WEIERSTRASS Finiteness Theorem,
which is not needed now and which will be a later consequence of more general facts about affinoid
algebras. Namely,

*If `g ∈ Tₙ` is `Xₙ`-distinguished of degree `s > 0`, then the endomorphism `φ` of `Tₙ` defined by
`φ(Xₙ) := g` and `φ(Xᵢ) := Xᵢ` for `i = 1, …, n − 1` is finite with `1, Xₙ, …, Xₙ^{s−1}` as a free
generating system.*

**5.2.4. Generation of distinguished power series.** — The two preceding results show that
Weierstrass polynomials are extremely useful in reducing problems to similar problems in a lower
dimension. But, in order to exploit this fact for `Tₙ`, one has to make sure that there are "enough"
of these Weierstrass polynomials. For the applications we have in mind, "enough" means that every
`f ∈ Tₙ − {0}` can be transformed by a suitable automorphism `σ` into an `Xₙ`-distinguished series
`σ(f)` which then is associated to some Weierstrass polynomial. That this is feasible is asserted by
the following

**Proposition 1.** *For every `f ∈ Tₙ`, `f ≠ 0`, there is a `k`-algebra automorphism `σ` of `Tₙ`
such that `σ(f)` is `Xₙ`-distinguished.*

*Proof.* We may assume `|f| = 1`. Let `f = Σ_μ a_μ X^μ`. Let `m = (m₁, …, mₙ)` be the maximal
`n`-tuple (with respect to lexicographical ordering) such that `|a_m| = 1`. Let `t` be a natural
number such that `t ≥ max_{1≤i≤n} μᵢ` for all indices `μ = (μ₁, …, μₙ)` with `ã_μ ≠ 0`; e.g., take
`t` equal to the total degree of `f̃`. The automorphism `σ` for which we are looking will be one of
the class we considered at the end of (5.1.3). Namely, set `σ(Xᵢ) := Xᵢ + Xₙ^{cᵢ}` for
`i = 1, …, n − 1` and `σ(Xₙ) := Xₙ` where, starting with an additional number `cₙ := 1`, the
exponents `c_{n−1}, …, c₁` are defined recursively by

    c_{n−j} := 1 + t Σ_{d=0}^{j−1} c_{n−d}   for j = 1, …, n − 1.

(The formula remains true for `j = 0`; it reproduces the definition of `cₙ`.) We claim that then
`σ(f)` is `Xₙ`-distinguished of order `s := Σ_{i=1}^n cᵢmᵢ`. First we observe that, for all
`μ = (μ₁, …, μₙ)` with `ã_μ ≠ 0` and `μ ≠ m`, we have `Σ_{i=1}^n cᵢμᵢ < s`. Namely, there is an
index `p`, `1 ≤ p ≤ n`, such that `μ₁ = m₁, …, μ_{p−1} = m_{p−1}` and `μ_p < m_p`. Then

    Σ_{i=1}^n cᵢμᵢ ≤ Σ_{i=1}^{p−1} cᵢmᵢ + c_p(m_p − 1) + Σ_{i=p+1}^n cᵢt
                   = Σ_{i=1}^p cᵢmᵢ − 1 < Σ_{i=1}^n cᵢmᵢ = s,

## p. 205 — 5.2.4 concluded; 5.2.5 Rückert's theory

whence our claim is justified. Now let us compute `(σ(f))~`. We have

    (σ(f))~ = σ̃(f̃) = Σ_μ ã_μ (X₁ + Xₙ^{c₁})^{μ₁} … (X_{n−1} + Xₙ^{c_{n−1}})^{μ_{n−1}} Xₙ^{μₙ}
            = Σ_{μ, ã_μ ≠ 0} ã_μ Σ_{λ₁,…,λ_{n−1}, 0 ≤ λᵢ ≤ μᵢ} C(μ₁,λ₁) … C(μ_{n−1},λ_{n−1})
                  X₁^{μ₁−λ₁} … X_{n−1}^{μ_{n−1}−λ_{n−1}} Xₙ^{c₁λ₁+⋯+c_{n−1}λ_{n−1}+μₙ}
            = Σ pᵢ Xₙ^i,

where the `pᵢ` are suitable elements of `k̃[X₁, …, X_{n−1}]`. Using the above observation, we see
that `(σ(f))~` is a polynomial in `Xₙ` of degree `≤ s`. Furthermore, a power
`Xₙ^{c₁λ₁+⋯+c_{n−1}λ_{n−1}+μₙ}` occurring in the above representation for `(σ(f))~` equals `Xₙ^s`
if and only if `μₙ = mₙ` and `λᵢ = μᵢ = mᵢ` for `i = 1, …, n − 1`. Thus we have
`p_s = ã_m ∈ k̃ − {0}`. In particular, `(σ(f))~` is a unitary polynomial of degree `s` in
`(k̃[X₁, …, X_{n−1}])[Xₙ]`, and hence `σ(f)` is `Xₙ`-distinguished of that degree. □

For later reference we state what we have actually proved.

**Proposition 2.** *Let `f = Σ_μ a_μ X^μ ∈ Tₙ`, `f ≠ 0`, and let `t ∈ ℕ ∪ {0}` such that
`t ≥ max_{1≤i≤n} μᵢ` for all indices `μ = (μ₁, …, μₙ)` with `|a_μ| = |f|`. Define an automorphism
`σ : Tₙ → Tₙ` by `σ(Xₙ) := Xₙ` and `σ(Xᵢ) := Xᵢ + Xₙ^{cᵢ}` for `i = 1, …, n − 1`, where, starting
with `cₙ := 1`, the coefficients `cᵢ` are determined recursively by
`c_{n−j} := 1 + t Σ_{d=0}^{j−1} c_{n−d}`, `j = 1, …, n − 1`. Then `σ(f)` is `Xₙ`-distinguished of
order `s := Σ_{i=1}^n cᵢmᵢ` where `m = (m₁, …, mₙ)` is the maximal index (with respect to
lexicographical ordering) such that `|a_m| = |f|`.*

[Board note, not BGR: the recursion gives `c_{n−j} = (1 + t)^j`, i.e. `cᵢ = (1 + t)^{n−i}`.]

**5.2.5. Rückert's theory.** — Following the classical method of RÜCKERT in the complex case, we
want to establish some results about the ring structure of the algebra `Tₙ`. For clarity, we
axiomatize the situation by introducing the following concept.

**Definition 1.** *Let `I` be a ring (commutative with identity element). An overring `I′` of
`I[X]` is called Rückert over `I` if there is a family `W` of monic polynomials in `I[X]` such that
the following three axioms are fulfilled:*

  *(1) If the product of two monic polynomials lies in `W`, so do the factors.*
  *(2) For all `ω ∈ W`, there is an isomorphism of `I`-algebras `I′/ωI′ ≅ I[X]/ωI[X]`. In
  particular, the canonical map `I → I′/ωI′` is finite.*
  *(3) For all `f ∈ I′ − {0}`, there is an automorphism `σ` of `I′` and a unit `e` of `I′` such that
  `e·σ(f) ∈ W`.*

According to the results of (5.2.2), (5.2.3) and (5.2.4), the algebra `Tₙ` is Rückert over
`T_{n−1}` if one takes `W` to be the family of Weierstrass polynomials in `Xₙ`. If one replaces the
strictly convergent power series by the formal, or simply the convergent series, the same statement
holds mutatis mutandis. With respect to many aspects, a Rückert overring of `I` behaves as `I[X]`
does. In particular, some ring properties of `I` are inherited by `I′`, as the following three
propositions show.

## p. 206 — 5.2.5 continued: the three inheritance propositions

**Proposition 2.** *A Rückert overring `I′` of a Noetherian ring `I` is Noetherian.*

*Proof.* We have to show that every ideal `𝔞 ≠ (0)` in `I′` is finitely generated. According to
axiom (3), we may assume that `𝔞` contains a polynomial `ω ∈ W`. Since `I` is Noetherian by
assumption, so is `I[X]` by HILBERT's Basis Theorem. Because `I′/ωI′` is isomorphic to
`I[X]/ωI[X]` due to axiom (2), the image of `𝔞` in `I′/ωI′` has a finite generating system. Pulling
back that system to `𝔞` and adding `ω`, we get a finite generating system for `𝔞`. □

Recall that a ring `I` is said to be a *Jacobson ring* if for every ideal `𝔞 ⊂ I` the nilradical
`rad 𝔞` equals the Jacobson radical `j(𝔞)` (which is the intersection of all maximal ideals in `I`
containing `𝔞`). Obviously any field is a Jacobson ring, whereas a local ring `I` is not Jacobson
unless `I/rad I` is a field. So one cannot expect that every ring `I′` which is Rückert over a
Jacobson ring `I` is itself a Jacobson ring, because `I := k` and `I′ := k⟦X⟧` provide a
counterexample. But at least one can show the following

**Proposition 3.** *Let `I` be a Jacobson ring, and let `I′` be a Rückert overring of `I`. Then
`rad 𝔞 = j(𝔞)` for any non-zero ideal `𝔞 ⊂ I′`.*

*Proof.* Since the nilradical of any ideal `𝔞 ⊂ I′` equals the intersection of all prime ideals
containing `𝔞` (see the argument used in the proof of DEDEKIND's Lemma 3.1.4/1), we have only to show
`j(𝔭′) = 𝔭′` for any non-zero prime ideal `𝔭′ ⊂ I′`. This will be done by showing that the Jacobson
radical `j(I′/𝔭′)` of (the zero ideal in) `I′/𝔭′` vanishes for all such `𝔭′`. Therefore let `𝔭′` be
a non-zero prime ideal in `I′`, and set `𝔭 := 𝔭′ ∩ I`. We may assume that `𝔭′` contains an element
`ω ∈ W` so that by axiom (2) the canonical injection `I/𝔭 ↪ I′/𝔭′` is finite. For each
`b ∈ j(I′/𝔭′)` we consider an integral equation

    bⁿ + a₁bⁿ⁻¹ + ⋯ + aₙ = 0

of `b` over `I/𝔭` of minimal degree `n`. Then

    aₙ = −(bⁿ + a₁bⁿ⁻¹ + ⋯ + a_{n−1}b) ∈ j(I′/𝔭′) ∩ I/𝔭.

Since for each maximal ideal `𝔪 ⊂ I/𝔭` there exists a maximal ideal `𝔪′ ⊂ I′/𝔭′` lying over `𝔪`,
we see that

    j(I′/𝔭′) ∩ I/𝔭 = j(I/𝔭) = 0.

Then `aₙ = 0`, and due to the minimality of `n`, we must have `n = 1` and therefore `b = 0`. This
shows that `j(I′/𝔭′) = 0`. □

Recall that a factorial ring is an integral domain `I` such that each non-unit `f ∈ I − {0}` can be
written as a finite product of prime elements in `I`. (An element `p ∈ I − {0}` is called a prime
element if it generates a prime ideal in `I`.) Any such product decomposition of `f` is unique up to
units.

**Proposition 4.** *Every integral domain `I′`, which is Rückert over a factorial ring `I`, is
factorial itself.*

## p. 207 — proof of Proposition 4; 5.2.6 Applications of Rückert's theory for `Tₙ`

*Proof.* The assertion is an easy consequence of the fact that `I[X]` is factorial if `I` is
factorial. However, since this result is not needed in full generality, we include here a direct
proof which is based on the Classical GAUSS Lemma (1.5.3).

We have to factor every non-unit `f ∈ I′ − {0}` into prime elements. Since automorphisms and units
do not matter for that task, we may assume `f ∈ W ⊂ I[X]`. The polynomial ring `Q(I)[X]` over the
field of fractions `Q(I)` is factorial. Hence there is a factorization `f = p₁ … p_r` into monic
polynomials `p₁, …, p_r ∈ Q(I)[X]`. We can choose elements `c₁, …, c_r ∈ I` such that the
polynomials `c₁p₁, …, c_rp_r` are primitive in `I[X]`. (A polynomial `p ∈ I[X]` is called primitive
if there is no prime element in `I` dividing all coefficients of `p`.) Then we see by the Classical
GAUSS Lemma (1.5.3) that

    (∏_{i=1}^r cᵢ) f = ∏_{i=1}^r (cᵢpᵢ)

is a primitive polynomial in `I[X]`. But this can only be true if `∏_{i=1}^r cᵢ` and hence all `cᵢ`
are units in `I`. Consequently, `f = p₁ … p_r` is a factorization of `f` in `I[X]`. It remains to be
shown that all `pᵢ` are prime elements in `I′`. Since `p₁, …, p_r ∈ W` (axiom (1)), and since
`I[X]/pᵢI[X] ≅ I′/pᵢI′` for all `i` (axiom (2)), it is enough to show that each `pᵢ` is a prime
element in `I[X]`. However this follows from the equations

    I[X] ∩ pᵢQ(I)[X] = pᵢI[X],   i = 1, …, r,

which are easily obtained from the Classical GAUSS Lemma by an argument similar to the one used
above. □

**5.2.6. Applications of Rückert's theory for `Tₙ`.** — As we have already observed, Theorem
5.2.2/1, Lemma 5.2.3/2 and Propositions 5.2.3/3 and 5.2.4/1 guarantee that `Tₙ` is Rückert over
`T_{n−1}`. Furthermore `T₀ = k` is a Noetherian factorial ring. Thus using induction on `n`, we get
from Propositions 5.2.5/2 and 5.2.5/4

**Theorem 1.** *The ring `Tₙ` is Noetherian and factorial.*

It is a well-known fact that any factorial ring `I` is normal (i.e., integrally closed in its field
of fractions `Q(I)`). Namely if

    (a/b)^r + c₁ (a/b)^{r−1} + ⋯ + c_r = 0

is an integral equation of some element `a/b ∈ Q(I)` over `I`, we may assume that `a` and `b` have
no common prime factor. However since

    a^r + c₁a^{r−1}b + ⋯ + c_rb^r = 0,

## p. 208 — 5.2.6 concluded; 5.2.7 Finite `Tₙ`-modules

we see that any prime factor `p` of `b` must divide `a^r` and hence `a`. Thus `b` can only be a unit
in `I`, and hence `a/b` belongs to `I`. In particular, we see that

**Theorem 2.** *`Tₙ` is normal.*

Finally, we get

**Theorem 3.** *`Tₙ` is a Jacobson ring.*

*Proof.* Proposition 5.1.3/3 tells us that `j(Tₙ) = 0`. Therefore we can conclude from Proposition
5.2.5/3 that `Tₙ` is a Jacobson ring if `T_{n−1}` is. Since `T₀ = k` is a Jacobson ring, the
assertion follows by induction on `n`. □

**5.2.7. Finite `Tₙ`-modules.** — Because `Tₙ` is Noetherian, all finite `Tₙ`-modules are
Noetherian. In particular, all submodules of the `s`-fold normed direct sum `Tₙ^s` are finitely
generated over `Tₙ`. We want to improve this result and derive finiteness theorems with estimates,
comparable to CARTAN's Theorem in the classical case.

**Proposition 1.** *Let `M` be a submodule of a finite complete `Tₙ`-module. Then `M` itself is a
finite complete `Tₙ`-module. Furthermore for every `Tₙ`-generating system `{m₁, …, m_s}` of `M`,
there exists a real constant `ρ` such that every `m ∈ M` admits a representation
`m = Σ_{i=1}^s tᵢmᵢ` with `max_{1≤i≤s} |tᵢ| ≤ ρ |m|`.*

*Proof.* The first assertion follows from Proposition 3.7.3/1. In order to verify the second
assertion, consider the `Tₙ`-epimorphism `φ : Tₙ^s → M` defined by
`φ(t₁, …, t_s) := Σ_{i=1}^s tᵢmᵢ`. Due to Proposition 3.7.3/1, we know that `Tₙ^s/ker φ` provided
with the residue norm is a finite complete `Tₙ`-module. Therefore the induced `Tₙ`-isomorphism
`φ̄ : Tₙ^s/ker φ ⥲ M` and its inverse are both continuous (see Proposition 3.7.3/2) and hence
bounded (see Proposition 2.1.8/2). Let `ρ′` be a bound for `φ̄⁻¹`, and set `ρ := ρ′ + 1`. Then the
inverse image `φ̄⁻¹(m)` of any element `m ∈ M` has norm `≤ ρ′ |m|` and can be represented by a
tuple `(t₁, …, t_s) ∈ Tₙ^s` satisfying `max_{1≤i≤s} |tᵢ| ≤ ρ |m|`. Since
`m = φ(t₁, …, t_s) = Σ_{i=1}^s tᵢmᵢ`, the second assertion follows. □

**Corollary 2.** *All ideals of `Tₙ` are closed.*

We want to improve Proposition 1 by looking for generating systems admitting the bound `ρ = 1`. For
vector spaces (instead of modules), we have studied in detail such questions as the existence of
orthonormal bases (cf. Chapter 2). Now we are going to handle analogous questions for `A`-modules,
where `A` is a normed ring (thought to be equal to `Tₙ` for some `n`). We want to make precise what
we mean by "generating system admitting the bound `ρ = 1`".

**Definition 3.** *A finite generating system `{m₁, …, m_s}` of a normed `A`-module `M`

## p. 209 — pseudo-cartesian and cartesian modules

is called pseudo-cartesian if every `m ∈ M` admits a representation `m = Σ_{i=1}^s aᵢmᵢ` with
`a₁, …, a_s ∈ A` and `|m| = max_{1≤i≤s} |aᵢ| |mᵢ|`. If this equation is true for all possible
representations of each `m ∈ M`, the system `{m₁, …, m_s}` is called cartesian. If such generating
systems exist for `M`, we say that `M` is a pseudo-cartesian or a cartesian `A`-module,
respectively.*

This is a generalization of Definition 2.4.1/1, where we defined finite `k`-cartesian spaces and
bases. A pseudo-cartesian generating system is cartesian if and only if it is free:

**Remark.** A finite-dimensional normed `k`-vector space `V` is pseudo-cartesian if and only if it
is cartesian.

Namely, let `{v₁, …, v_s}` be a pseudo-cartesian generating system of `V`, where `vᵢ ≠ 0` for all
`i`. Consider the epimorphism `φ : k^s → V`, `(c₁, …, c_s) ↦ Σ_{i=1}^s cᵢvᵢ`, and provide `k^s` with
the norm given by `|(c₁, …, c_s)| := max_{1≤i≤s} |cᵢ| |vᵢ|`. Then `k^s` is a cartesian space, and
the norm on `V` equals the residue norm with respect to the map `φ`. The subspace `ker φ` admits a
norm-direct supplement `U` in `V`, and `U` is cartesian (see Proposition 2.4.1/5). Since `φ` induces
an isometric isomorphism `U ⥲ V`, we see that `V` is cartesian. □

The above remark is not true for general `A`-modules, since one can easily find pseudo-cartesian
modules which are not free. For example, let `𝔪` denote the maximal ideal in `Tₙ` which is generated
by the indeterminates. Then `k = Tₙ/𝔪` is a pseudo-cartesian `Tₙ`-module which is not cartesian
(unless `n = 0`). We state some elementary properties of pseudo-cartesian and cartesian modules.

**Lemma 4.** *(a) The normed direct sum of finitely many pseudo-cartesian `A`-modules is
pseudo-cartesian. The same is true if pseudo-cartesian is replaced by cartesian.*
*(b) Let `M` be a pseudo-cartesian `A`-module, and let `N` be a strictly closed submodule of `M`.
Then `M/N` (provided with the residue norm) is a pseudo-cartesian `A`-module.*

**Lemma 5.** *Let `M` be a normed `A`-module over a normed `k`-algebra `A`. Suppose that
`|M| = |k|`. Then `M` is a pseudo-cartesian `A`-module if and only if `M°` is a finite
`A°`-module.*

The assumption `|M| = |k|` occurring in Lemma 5 cannot in general be avoided. However it can be
weakened (as far as the only if part of Lemma 5 is concerned) if the valuation on `k` is discrete.

**Lemma 6.** *Let `M` be a normed `A`-module over a normed `k`-algebra `A`. Suppose that
`|A| = |k|` and that the valuation on `k` is discrete. Then `M°` is a finite `A°`-module if `M` is a
pseudo-cartesian `A`-module.*

## p. 210 — Theorem 7 and Corollary 8

*Proof.* Let `{m₁, …, m_s}` be a pseudo-cartesian generating system for `M`, where `mᵢ ≠ 0` for all
`i`, and define `η := max {α ∈ |k| ; α < 1}`. Then `η < 1`. By multiplying `m₁, …, m_s` with
suitable coefficients from `k`, we may assume that `η < |mᵢ| ≤ 1` for all `i`. Given `m ∈ M°`,
`m ≠ 0`, we can find `a₁, …, a_s ∈ A` such that `m = Σ_{i=1}^s aᵢmᵢ` and
`|m| = max_{1≤i≤s} |aᵢ| |mᵢ|`. Then we get

    max |aᵢ| ≤ (max |aᵢ| |mᵢ|) / (min |mᵢ|) < |m|/η ≤ 1/η.

Since `|aᵢ| ∈ |A| = |k|`, this is only possible if `max_{1≤i≤s} |aᵢ| ≤ 1`. Hence `{m₁, …, m_s}` is a
finite generating system for `M°` over `A°`. □

For the remainder of this section, we restrict ourselves to the case `A = Tₙ`. We want to show that
submodules of cartesian `Tₙ`-modules are always pseudo-cartesian.

**Theorem 7.** *Let `M` be a submodule of a cartesian `Tₙ`-module `F`. Then `M` is pseudo-cartesian
and strictly closed in `F`. In particular if `|M| = |k|`, then `M°` is a finite `T̊ₙ`-module.*

We can apply the theorem in the special case, where `F` equals `Tₙ` and where `M` is an ideal in
`Tₙ`. Thereby we obtain

**Corollary 8.** *Each ideal `𝔞 ⊂ Tₙ` is strictly closed in `Tₙ`, and the residue norm on `Tₙ/𝔞`
satisfies `|Tₙ/𝔞| = |Tₙ| = |k|`.*

For the proof of Theorem 7, we need some preparations. We denote by `Q := Q(Tₙ)` the field of
fractions of `Tₙ`. If `F` is a normed `Tₙ`-module, the norm on `F` induces a (semi-) norm on the
`Q`-vector space `F ⊗_{Tₙ} Q` (see (2.1.7) for general facts). The process is very simple if `F` is
a cartesian `Tₙ`-module. Namely, we may view `F` as a `Tₙ`-submodule of `F ⊗_{Tₙ} Q`, and any
cartesian generating system of `F` gives rise to an orthogonal basis of `F ⊗_{Tₙ} Q`, all norms
being preserved. In particular, `F ⊗_{Tₙ} Q` is a cartesian `Q`-vector space.

**Lemma 9.** *Let `F` be a cartesian `Tₙ`-module and let `ω` be a non-zero element in `Tₙ`. Then
`ωF` is a strictly closed submodule of `F`. Furthermore, `F` is strictly closed in `F ⊗_{Tₙ} Q`.*

*Proof.* First we show that `ωTₙ` is strictly closed in `Tₙ`. Applying a suitable automorphism of
`Tₙ`, we may assume that `ω` is a Weierstrass polynomial in `Tₙ` of some degree `s ≥ 0`. Then the
WEIERSTRASS Division Theorem 5.2.1/2 says that `Tₙ` (viewed as a `T_{n−1}`-module) is the
norm-direct sum of `ωTₙ` and `Σ_{ν=0}^{s−1} T_{n−1}Xₙ^ν`. In particular, `ωTₙ` is strictly closed in
`Tₙ`. That `ωF` is strictly closed in `F` is an easy consequence of this fact.

Viewing `F` as a `Tₙ`-submodule of `F ⊗_{Tₙ} Q`, we can also say that `F` is strictly

## p. 211 — Lemma 10 and the proof of Theorem 7

closed in `(1/ω)F`. Since `F ⊗_{Tₙ} Q` is the union of all `Tₙ`-submodules `(1/ω)F`,
`ω ∈ Tₙ − {0}`, we see that `F` is strictly closed in `F ⊗_{Tₙ} Q`. □

**Lemma 10.** *Let `M` be a submodule of a cartesian `Tₙ`-module `F`. Then there exist an element
`ω ∈ Tₙ − {0}` and a cartesian `Tₙ`-submodule `F′ ⊂ F ⊗_{Tₙ} Q` such that `ωF′ ⊂ M ⊂ F′`.*

*Proof.* We consider `V′ := M ⊗_{Tₙ} Q` as a `Q`-subspace of `V := F ⊗_{Tₙ} Q`. Then `V′` is
cartesian, since `V` is cartesian (see Proposition 2.4.1/5). Let `{v₁, …, v_r}` denote an orthogonal
basis for `V′`. We may assume `v₁, …, v_r ∈ M`. Namely if `vᵢ = mᵢ/tᵢ` with elements `mᵢ ∈ M`,
`tᵢ ∈ Tₙ − {0}`, then `{m₁, …, m_r}` is an orthogonal basis of the desired type. Since `M` is
finitely generated, there is a universal denominator `ω ∈ Tₙ − {0}` such that

    M ⊂ (1/ω) Σ_{i=1}^r Tₙvᵢ.

Define `F′ := Σ_{i=1}^r Tₙ (vᵢ/ω)`. Then `F′` is a cartesian `Tₙ`-submodule of `V` satisfying
`ωF′ ⊂ M ⊂ F′`. □

*Proof of Theorem 7.* Due to Lemma 5, we have only to show that `M` is pseudo-cartesian and strictly
closed in `F`. We use induction on `n`. For `n = 0`, the assertion follows from Propositions 2.4.1/5
and 2.4.2/1. Therefore, let `n ≥ 1`. Choose a non-zero element `ω ∈ Tₙ` and a cartesian
`Tₙ`-submodule `F′ ⊂ F ⊗_{Tₙ} Q` such that `ωF′ ⊂ M ⊂ F′` (Lemma 10). There is a chart
`{X₁, …, Xₙ} ⊂ Tₙ` such that `ω` is `Xₙ`-distinguished of some degree `s ≥ 0` (use Proposition
5.2.4/1). Hence, by the WEIERSTRASS Preparation Theorem 5.2.2/1, we may assume that `ω` is a
Weierstrass polynomial in `Xₙ`. Writing `T_{n−1} := k⟨X₁, …, X_{n−1}⟩`, we see that `F′/ωF′` is a
cartesian `T_{n−1}`-module. Namely, an easy computation verifies that `F′/ωF′` is a cartesian
`Tₙ/ωTₙ`-module; furthermore, `Tₙ/ωTₙ` is a cartesian `T_{n−1}`-module by Proposition 5.2.3/3. If we
view `M/ωF′` as a `T_{n−1}`-submodule of `F′/ωF′`, we can apply the induction hypothesis and see
that `M/ωF′` is pseudo-cartesian and strictly closed in `F′/ωF′`.

In order to construct a pseudo-cartesian generating system for `M`, we consider a pseudo-cartesian
generating system for the `T_{n−1}`-module `M/ωF′`. Since `ωF′` is strictly closed in `F′` (Lemma 9)
and hence strictly closed in `M`, this system can be lifted to `M` without changing norms. Adding a
cartesian generating system for `ωF′`, we get a pseudo-cartesian generating system for the
`Tₙ`-module `M`. It remains to show that `M` is strictly closed in `F`. Since `M/ωF′` is strictly
closed in `F′/ωF′` and since `ωF′` is strictly closed in `F′` (Lemma 9), we can apply Lemma 1.1.6/4
and thereby see that `M` is strictly closed in `F′`. Now `F′` is strictly closed in `F′ ⊗_{Tₙ} Q`
(Lemma 9), and `F′ ⊗_{Tₙ} Q` is strictly closed in `F ⊗_{Tₙ} Q` because any subspace of a
finite-dimensional cartesian vector
