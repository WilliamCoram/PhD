# Multivariate Weierstrass theory at every polyradius

Notes on the proof of unconditional multivariate Weierstrass division and preparation
(`DivisibleRadius.lean`), the literature it draws on, and how it relates to what is in
print. Written 2026-07-28; **corrected the same day** after locating F. Martin's
J. EMS paper (§5 below) — an earlier version of these notes claimed the endpoint
statements were absent from the literature, which is wrong.

## 1. The theorem

Let `K` be a complete nontrivially normed ultrametric field and `c : Fin (n+1) → ℝ` a
polyradius, `0 < c i` for every `i` — **no further hypotheses on the radii**. Write
`Restricted K c` for the algebra of power series `∑ a_ν X^ν` with `‖a_ν‖ ∏ c_i^{ν_i} → 0`,
normed by the Gauss (sup) norm `‖f‖ = sup_ν ‖a_ν‖ c^ν`.

`IsDistinguishedX0 g s` (through the splitting isomorphism `finSuccEquiv`, so as a
univariate series over the coefficient Tate algebra `R = Restricted K (Fin.tail c)`):
the degree-`s` coefficient is a **unit** of `R`, its Gauss term attains `‖g‖`, and it
strictly dominates every **later** Gauss term (ties with lower terms are allowed).

* **Division** (`weierstrassDivision_exists`, `weierstrassDivision_uniqueness`): every `f`
  factors uniquely as `f = g * q + r` with `r` an `X 0`-polynomial of degree `< s` over `R`.
* **Preparation** (`weierstrassPreparation_exists`, `weierstrassPreparation_unique`):
  `g = e * ω` with `e` a unit and `ω` monic distinguished of degree `s`, uniquely, with
  `‖ω‖ = (c 0)^s`.
* Polynomial variants (`weierstrassDivision_polynomial`, `weierstrassPreparation_polynomial`).

## 2. Our proof architecture

Induction on the number of radii outside the divisible closure
`√‖K^×‖ = { c : ∃ n ≠ 0, c^n ∈ ‖K^×‖ }` (`MemDivisibleValueGroup`):

1. **All radii realised by units of `K`**
   (`weierstrassDivision_exists_of_forall_units`): transport the univariate division over
   `R` through `finSuccEquiv`; the engine's scaling oracle (`exists_norm_inv_isUnit` —
   every nonzero series admits a unit of the coefficient ring realising the inverse of its
   norm) is discharged from the unit realisers of the radii.
2. **All radii in the divisible closure** (`weierstrassDivision_exists_divisible`): one
   finite extension carrying the spectral norm realises every radius as a unit norm
   (`MemDivisibleValueGroup.elim_finite_extension`); divide there and descend by
   uniqueness along the automatic finite-dimensional bounded retraction
   (`weierstrassDivision_descend`).
3. **Some radius `c i₀` off the divisible closure**: pass to the **Gauss extension**
   `GaussExtension K (c i₀) = Completion (GaussLaurent K (c i₀))` — the completion of
   `K[T, T⁻¹]` under the radius-`c i₀` Gauss norm, a complete nontrivially normed
   ultrametric **field** (off the divisible closure, distinct exponents have distinct
   Gauss terms, so the norm is multiplicative and every nonzero element is a unit times
   `1 + small`), in which `c i₀ = ‖T‖` with `T` a unit. The count of unrealised radii
   strictly drops; divide by induction and descend along the norm-one `T⁰`-coefficient
   retraction (`GaussExtension.retraction`, `weierstrassDivision_descend_of_retraction`),
   using uniqueness of division over the extension.

`GaussExtension K r` is Berkovich's field `K_r = ℋ(η_r)`, the completed residue field of
the Gauss point of radius `r`; in the Dwork–Robba tradition, the field of the generic
point of radius `r`.

## 3. The prior statement in the literature: Martin, J. EMS 2016

**F. Martin**, "Overconvergent subanalytic subsets in the framework of Berkovich spaces",
*J. Eur. Math. Soc.* 18 (2016), 2405–2457 (arXiv:1211.6684), **§1.3**, states and proves
(his motivation being constructible data with overconvergent radii):

* **Definition 1.24.** For `A` any ultrametric complete normed ring and `r > 0` an
  arbitrary real, `g = ∑ g_n T^n ∈ A{r⁻¹T}` is `T`-distinguished of order `s` if `g_s` is
  a *multiplicative unit* (a unit with `‖g_s a‖ = ‖g_s‖‖a‖` for all `a`, equivalently
  `‖g_s⁻¹‖ = ‖g_s‖⁻¹`), `‖g_s‖r^s = ‖g‖`, and `‖g_n‖r^n < ‖g_s‖r^s` for all `n > s`.
* **Proposition 1.27 (Weierstrass division).** For such `g`, every `f ∈ A{r⁻¹T}` has a
  unique decomposition `f = gq + R`, `R ∈ A[T]` of degree `< s`, with the norm equality
  `‖f‖ = max(‖g‖‖q‖, ‖R‖)`.
* **Corollary 1.28 (Weierstrass preparation).** Such `g` factors uniquely as `g = e·w`
  with `w` monic of degree `s` and `e` a multiplicative unit of `A{r⁻¹T}`.
* The **multivariate case at arbitrary polyradius** is the remark following Cor 1.28:
  take `A := A₀{r₁⁻¹T₁, …, r_{n-1}⁻¹T_{n-1}}` and iterate — "which corresponds to the
  classical one, especially if `A = k`, where we find the classical Tate algebra".

**Equivalence with our hypothesis.** Over our coefficient rings the two notions of
distinguished coincide: `Restricted K c` carries a *multiplicative* Gauss norm
(`NormMulClass` instance in `MvPowerSeries/Restricted/GaussNorm.lean`; Gauss's lemma over
a field, valid at every polyradius), and in a ring with multiplicative norm every unit
satisfies `‖u⁻¹‖ = ‖u‖⁻¹`, i.e. is a multiplicative unit in Martin's sense. So
`IsDistinguishedX0 g s` ⟺ Martin's `T`-distinguished of order `s` for the pulled-back
series over `R`, and our endpoint theorems are instances of Prop 1.27 / Cor 1.28 with
`A = R` (which is complete, ultrametric, normed). Conversely Martin's coefficient ring is
more general than ours (any ultrametric Banach ring, no field downstairs).

**Martin's proof is direct and extension-free.** Truncate the divisor at degree `s`:
`g' = ∑_{m ≤ s} g_m T^m` is a polynomial with invertible leading coefficient, so exact
Euclidean division by `g'` is available in `A[T]`; the norm equality (proved first, from
the multiplicativity of `g_s` — his Lemma 1.26) bounds the Euclidean quotient; the error
`f - (gq + R)` contracts by the factor `κ = max_{m>s}(‖g_m‖r^m)/‖g‖ < 1`, which uses
strict dominance **above `s` only** — part of the definition, at every radius. Iterate and
pass to the limit by completeness. Ties at indices `< s` — the phenomenon that blocks the
one-step strictly-dominated engine, e.g. `X₀ + X₁` at equal radii — are absorbed exactly
by the polynomial Euclidean division. No value groups, no field extensions, no descent.

## 4. Honest comparison

* **The endpoint theorems are not new.** Division, uniqueness, norm control and
  preparation at arbitrary radius over an ultrametric Banach ring are [Mar16, §1.3]; the
  arbitrary-polyradius multivariate statement is his closing remark of that section
  (stated, not numbered). Our contribution regarding the *statements* is the
  formalisation, the explicit multivariate packaging (`IsDistinguishedX0`, splitting
  isomorphism, polynomial variants, the `‖ω‖ = (c 0)^s` clause), and complete written
  proofs of the iteration.
* **What our earlier analysis got wrong.** We argued the division engine "needs the
  radius as a unit norm" — true of the *oracle-based* engine (normalise `f` to norm 1 and
  reduce), and of the *one-step strictly-dominated* engine (needs no ties anywhere). It is
  not true of Martin's truncation engine, which replaces normalisation by exact Euclidean
  division below degree `s`. The obstruction we documented (algebraic extensions cannot
  leave `√‖K^×‖`; cross-variable ties are real) is an obstruction to *those two proof
  strategies*, not to the theorem — and Martin's third strategy needs neither.
* **Consequence for the Lean development (optional).** `DivisibleRadius.lean`'s
  three-case induction, the finite spectral extension, and the Gauss-extension descent
  could in principle be replaced by a single Martin-style proof over a `NormMulClass`
  coefficient ring (truncate; Euclidean-divide; iterate; the `Complete.lean`
  completeness of `Restricted` provides the limits). This would shorten the critical
  path considerably. The present proof is sorry-free and stays.
* **What retains independent value.** The `GaussExtension` API — the normed field
  `K_r = ℋ(η_r)` with its `Field`/`NontriviallyNormedField` instances, `‖T‖ = r`, and the
  norm-one retraction — is a reusable object (base change, spectral theory, Berkovich
  points), as are the descent lemmas `weierstrassDivision_descend(_of_retraction)`
  (which descend the division *equation*, not just ring-theoretic properties) and the
  `MemDivisibleValueGroup` API. The Gauss-extension proof is also a faithful
  formalisation of the classical Berkovich reduction pattern, which has interest of its
  own.

## 5. References

The statement and its direct proof:

* **F. Martin**, "Overconvergent subanalytic subsets in the framework of Berkovich
  spaces", J. Eur. Math. Soc. 18 (2016), 2405–2457, **§1.3** (Def 1.24, Prop 1.27,
  Cor 1.28 and the following remark) — Weierstrass division and preparation over an
  arbitrary ultrametric complete normed ring at an arbitrary radius; the multivariate
  polyradius case by iteration. *The* prior statement of our endpoint theorems.

The Gauss extension and the ingredients of our proof route:

* **V. G. Berkovich**, *Spectral Theory and Analytic Geometry over Non-Archimedean
  Fields*, Math. Surveys and Monographs 33, AMS, 1990 — §2.1: the field
  `K_r = {∑_{i∈ℤ} a_i T^i : |a_i|r^i → 0}` for `r ∉ √|K^×|`; extension of scalars to
  `K_r` + descent as the mechanism for transferring properties of `K⟨r⁻¹T⟩` from the
  strictly convergent case.
* **N. Bourbaki**, *Algèbre commutative*, ch. VI (Valuations), §10, n° 1 — the Gauss
  extension of a valuation to `K(T)`.
* **A. J. Engler, A. Prestel**, *Valued Fields*, Springer, 2005, §2.2 — the
  value-transcendental case: `ℤδ ∩ Γ = 0` gives a unique extension with `Γ_w = Γ ⊕ ℤδ`
  (the no-ties phenomenon behind `GaussLaurent`'s `norm_mul`).
* **M. Temkin**, "Introduction to Berkovich analytic spaces", in *Berkovich Spaces and
  Applications*, LNM 2119 — Example 3.1.1.4 (`K_r = k{r⁻¹T, rT⁻¹}`), Remark 3.1.2.4
  (strict-case Weierstrass theory + `K_r` base change for the rest).
* **L. Gruson**, "Théorie de la descente et algèbres de Banach ultramétriques",
  Ann. Sci. ÉNS (4) 1, 1966 — ultrametric Banach descent; the `(T^i)` are an orthogonal
  Schauder basis of `K_r`, our retraction is the projection onto the `K`-summand. Cf.
  Ducros, Astérisque 400, §2.11–2.12 (arXiv numbering): ground field extension to `k_r`
  and its "Shilov section".
* **J. Neukirch**, *Algebraic Number Theory*, Thm II.4.8 (or BGR §3.2) — `|x| =
  |N_{L/K}(x)|^{1/[L:K]}`: algebraic extensions never leave `√‖K^×‖` (why the
  finite-extension mechanism stops at the divisible closure).

Classical strict-case theory and adjacent general-radius results:

* **S. Bosch, U. Güntzer, R. Remmert**, *Non-Archimedean Analysis*, Springer, 1984 —
  §5.2.1–5.2.2 (division/preparation at radius 1); §6.1.5 (the algebras `T_n(c)`,
  defined for `c ∈ √|K^×|`); §3.2 (spectral norm on finite extensions).
* **M. Lazard**, "Les zéros des fonctions analytiques d'une variable sur un corps valué
  complet", Publ. Math. IHÉS 14 (1962), 47–75 — univariate zeros/factorisation at
  arbitrary radii, Newton polygons.
* **K. S. Kedlaya**, *p-adic Differential Equations*, CUP, 2010, ch. 9 — Dwork–Robba
  generic points; the completion of `F(t)` under the `ρ`-Gauss norm.
* **J. Poineau**, *La droite de Berkovich sur ℤ*, Astérisque 334, 2010 — §2.2.1
  (germ-level division/preparation over any uniform Banach ring; radii shrink in the
  colimit) and §5.2 (fixed radius above the Newton radius of a monic polynomial divisor).
* **J. Poineau**, "Espaces de Berkovich sur ℤ : étude locale", Invent. Math. 194 (2013),
  Thm 8.3; **T. Lemanissier, J. Poineau**, *Espaces de Berkovich globaux*
  (arXiv:2010.08858), §1.6 and §3.2 — division at rigid points of fibres; the
  norm-controlled version lives on polynomial domains whose radii are produced by the
  proof.
* **M. Temkin**, "On local properties of non-Archimedean analytic spaces. II", Israel J.
  Math. 140 (2004) — graded reduction: handles all radii uniformly without extensions.

## 6. Where this leaves the write-up

Suggested phrasing:

> Weierstrass division and preparation at an arbitrary radius, over an arbitrary
> ultrametric Banach ring, are due to Martin [Mar16, §1.3], by a direct
> truncation-and-iteration argument; the multivariate case at an arbitrary polyradius is
> the remark closing that section. We give a formalised account of the multivariate
> theory. Our proof follows a different route, of independent interest: the classical
> reduction of Berkovich [Ber90, §2.1] — extension of scalars to the Gauss-point field
> `K_r = ℋ(η_r)` realising the radius as a unit norm, here presented as the completion
> of the Gauss-normed Laurent algebra `K[T,T⁻¹]` — together with a descent of the
> division equation itself along the canonical `T⁰`-coefficient retraction of
> `K → K_r`, in the spirit of ultrametric Banach descent [Gruson]. To our knowledge this
> descent of the equation (as opposed to ring-theoretic properties) had not been carried
> out in print, and the field `K_r`, its multiplicative Gauss norm off the divisible
> closure [Bourbaki VI §10; Engler–Prestel §2.2], and the retraction are formalised here
> for the first time.

Residual caution: our literature survey (Berkovich, BGR, Temkin, Ducros, the Poineau
school, Martin) was conducted by reading the sources named above on 2026-07-28; Martin's
§1.3 was found only on a second pass, which is a reminder that further instances may
exist (e.g. inside Astérisque 400's later chapters, or the dagger/overconvergent
literature — Grosse-Klönne). Claims of the form "not in the literature" should stay
soft.
