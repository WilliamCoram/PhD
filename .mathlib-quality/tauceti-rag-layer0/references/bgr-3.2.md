# BGR §3.2.2 (end), §3.2.3, §3.2.4 (start), §3.4 (start) — hand transcription from the scan

Source: S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984),
Chapter 3 "Extensions of norms and valuations", pp. 138–139 and 145–146. Transcribed by eye from
page renders of the scan (render file `bgr_a/pNNN.pdf.png` shows book page NNN − 8). `σ(q)` is the
spectral value of a monic polynomial `q = Xⁿ + a₁Xⁿ⁻¹ + ⋯ + aₙ`, i.e. `max_ν |a_ν|^{1/ν}` (3.1.2);
`| |_sp` is the spectral norm. Locators are `bgr-3.2.md:<line>`.

## p. 138 — 3.2.2/4, transitivity of spectral norms

**Proposition 4 (3.2.2/4).** *Let `K′` be an algebraic extension of `K` and let `L` be a reduced
integral `K′`-algebra. Denote by `| |_{K′,K}` the spectral norm on `K′` induced by the norm on `K`,
and by `| |_{L,K′}` the spectral norm on `L` induced by the norm `| |_{K′,K}` on `K′` and by
`| |_{L,K}` the spectral norm on `L` induced by the norm on `K`. Then we have*

    | |_{L,K} = | |_{L,K′}.

## p. 139 — 3.2.3 Spectral norm and field polynomials

*Proof (of 3.2.2/4).* `| |_{L,K′}` is a `K′`-algebra norm and `| |_{K′,K}` is a `K`-algebra norm;
hence a fortiori `| |_{L,K′}` is a `K`-algebra norm. Therefore, by Theorem 3.2.2/2 (iii), the norm
`| |_{L,K′}` is dominated by `| |_{L,K}`. The opposite inequality can be shown quite similarly:
`| |_{L,K}` is an extension of `| |_{K′,K}`, because, for elements of `K′`, both norms are defined
via the same minimal polynomials. If we apply Theorem 3.2.2/2 (iii) again (this time to the
extension `L` over `K′`), we see that `| |_{L,K′}` dominates `| |_{L,K}`. □

**3.2.3. Spectral norm and field polynomials.** — We describe another way of computing the spectral
norm.

Let `L` be a finite field extension of `K`. For each `y ∈ L`, the *field polynomial* of `y` over
`K` is defined to be the characteristic polynomial of the `K`-linear map `L → L` defined by
`x ↦ yx`, `x ∈ L`. This polynomial, which is monic, depends not only on `y` but also on the field
`L`. Nevertheless, we have

**Proposition 1 (3.2.3/1).** *Let `L` be a finite extension of `K`. Then for each `y ∈ L`, the
spectral norm `|y|_sp` equals the spectral value `σ(ξ)` of the field polynomial `ξ` of `y` over
`K`.*

*Proof.* As is well known, the field polynomial `ξ` of `y` is a power of the minimal polynomial `q`
of `y`, say `ξ = q^m`. Hence `σ(ξ) = σ(q)` by Corollary 3.2.1/6. □

If `ξ = Xⁿ + a₁Xⁿ⁻¹ + ⋯ + aₙ ∈ K[X]` is the field polynomial of `y ∈ L` over `K`, the element
`−a₁ ∈ K` is called the *trace* of `y ∈ L` over `K`:

    Tr_{L/K} y = −a₁.

The map `Tr_{L/K} : L → K` is `K`-linear.

**Corollary 2 (3.2.3/2).** *The `K`-linear trace map `Tr_{L/K} : L → K` is a contraction (and hence
continuous) if `L` is provided with the spectral norm.*

*Proof.* We have

    |Tr_{L/K} y| = |a₁| ≤ max_{1≤ν≤n} |a_ν|^{1/ν} = σ(ξ) = |y|_sp. □

**3.2.4. Spectral norm and valuations.** — In important cases the spectral norm is not only a
`K`-algebra norm, but also a valuation on `L` so that we can talk about the *spectral valuation* on
`L` over `K`.

**Proposition 1 (3.2.4/1).** *The spectral norm on `L` is a valuation on `L` if `L~ = L°/Lˇ` is an
integral domain.*

*Proof.* The assertion follows immediately from Proposition 1.5.3/1, since, for each `y ∈ L*`, there
exist an `s ≥ 1` and an element `c ∈ K*` such that `|cy^s| = 1`. □

Next we prove the important

**Theorem 2 (3.2.4/2).** *Let `K` be complete with respect to the given valuation `| |`, and let `L`
be an algebraic extension of `K`. Then the spectral norm on `L` is a valuation, and* [the statement
continues on p. 140: it is the unique valuation on `L` extending the valuation of `K`, and `L` is
complete if it is finite over `K`; cited in this form by BGR 5.1.4, `bgr-5.1.md:207–209` and
`bgr-5.1.md:219–221`.]

## p. 145 — 3.4 Properties of the spectral valuation

By `K_a` we always mean the algebraic closure of `K` provided with the spectral norm `| |`. All
roots of polynomials `f ∈ K[X]` are elements of `K_a`. For each `f ∈ K[X]`, we denote by `|f|` its
Gauss norm. If `f` is monic, we have `σ(f) ≤ |f|` for the spectral value `σ(f)` of `f`. Hence, in
particular, `|α| ≤ |f|` for each root `α ∈ K_a` of `f` due to Proposition 3.1.2/1.

**3.4.1. Continuity of roots.** — Let `f, g ∈ K[X]` be monic polynomials of the same degree `n`. Let
`α ∈ K_a` be a root of `f`. We have the crucial inequality:

    (*)   |g(α)| ≤ |f − g| · |f|ⁿ⁻¹.

**Proposition 1 (3.4.1/1) (Continuity of roots).** *Let `K` be complete; let `f, g ∈ K[X]` be monic
polynomials of the same degree `n`. Then for each root `α ∈ K_a` of `f`, there exists a root
`β ∈ K_a` of `g` such that `|α − β| ≤ ⁿ√(|f − g|) · |f|`.*

[3.4.1/2–4 on pp. 145–147 lead to Lemma 3.4.1/4, "the residue field of `K_a` is the algebraic
closure of the residue field of `K`", which BGR 5.1.4/3 cites (`bgr-5.1.md:277–278`). The board does
not use 3.4.1: it replaces `K_a` by the splitting field of `Xᵐ − 1`, as BGR's own remark
`bgr-5.1.md:272–273` permits ("provided `L̃` is infinite").]
