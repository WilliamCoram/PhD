# Weierstrass division & preparation at every radius — two proofs

This project proves Weierstrass **division** and **preparation** for restricted power series
`Restricted R c` (the Tate algebra `R⟨c⁻¹T⟩` of series `∑ aₙTⁿ` with `‖aₙ‖cⁿ → 0`), at an
**arbitrary** radius `c > 0` (and, multivariately, at an arbitrary polyradius), with no
hypothesis relating `c` to the value group of `R`.

There are **two independent formal proofs** in the repository:

1. the **Martin proof** — elementary, extension-free, maximally general; this is the
   *canonical* development and lives in `PhD/Main/ForMathlib/`;
2. the **Berkovich proof** — via the Gauss-extension field `K_r = ℋ(η_r)` and descent; the
   classical route, kept for its reusable objects; it lives in `PhD/Main/BirkovichWP/`.

This note explains both and collects the references. It is the successor of the deleted
`WEIERSTRASS_AT_EVERY_RADIUS.md`.

---

## 0. The statement

Fix a complete ultrametric normed commutative ring `R` (`[NormedCommRing R]`,
`[IsUltrametricDist R]`, `[CompleteSpace R]`) and `c > 0`. Call `g ∈ Restricted R c`
**distinguished of degree `s`** when

* its `s`-th coefficient `gₛ` is *invertible* (Berkovich) / a *multiplicative unit*
  `‖gₛ · a‖ = ‖gₛ‖‖a‖ ∀a` (Martin), and
* the `s`-th Gauss term attains the norm, `‖gₛ‖cˢ = ‖g‖`, and **strictly dominates every
  later term**, `‖gₜ‖cᵗ < ‖gₛ‖cˢ` for `t > s`.

**Division.** Every `f` is uniquely `f = g·q + r` with `r` a polynomial of degree `< s`;
moreover `‖f‖ = max(‖g‖‖q‖, ‖r‖)` (Martin's norm identity (1.8)), giving `‖q‖ ≤ ‖g‖⁻¹‖f‖`,
`‖r‖ ≤ ‖f‖`.

**Preparation.** `g = e·ω` with `e` a unit and `ω` a monic polynomial of degree `s` with
`‖ω‖ = cˢ`; the factorisation is unique.

The **strict domination is required only *above* `s`** — ties at indices `< s` are allowed.
This is the crucial subtlety that makes both the general radius and the multivariate case
work, and it is exactly what the polynomial (Euclidean) step below absorbs.

Multivariately (`c : Fin (n+1) → ℝ`), one works "in `X 0`": `f` is distinguished in `X 0` of
degree `s` iff its image under the splitting isomorphism `finSuccEquiv`, a univariate series
over the Tate algebra of the remaining variables, is distinguished of degree `s` at radius
`c 0`. All multivariate statements are transports of the univariate ones along `finSuccEquiv`.

---

## 1. The Martin proof (canonical, `PhD/Main/ForMathlib/`)

**Source.** F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich
spaces*, **J. EMS 18 (2016), 2405–2457, §1.3** (arXiv:1211.6684). The multivariate,
arbitrary-polyradius statement is the closing remark of that section.

Martin proves division/preparation over **any** ultrametric complete normed ring at **any**
radius, with **no field, no extension, no completion of a Gauss norm**. The idea:

1. **Multiplicative units** (Def 1.20; Lemma 1.21: `u` mult. unit `⟺ ‖u⁻¹‖ = ‖u‖⁻¹`; Rem.
   1.22: `1 + x` is a mult. unit when `‖x‖ < 1`). Over a `NormMulClass` ring (multiplicative
   norm — e.g. a Tate algebra over a field) *every* unit is a multiplicative unit, so this
   hypothesis is invisible there; over a general ring it is the right strengthening.
2. **Norm-multiplicativity** (Lemma 1.26): multiplication by a distinguished `g` is
   norm-multiplicative, `‖g·q‖ = ‖g‖‖q‖`, with the product's norm attained at `s + k₀`
   (`k₀` = greatest index achieving `‖q‖`). This gives the norm identity (1.8), hence the
   bounds and **uniqueness** directly.
3. **Existence** (Prop 1.27). Truncate the divisor at degree `s`: `g' = ∑_{m ≤ s} gₘTᵐ` is a
   *polynomial* whose leading coefficient `gₛ` is invertible, so **exact Euclidean division**
   by `g'` is available (`Polynomial.modByMonic` after rescaling by the unit `gₛ⁻¹`). The
   one-step approximation (1.11) — Euclidean-divide a truncation of `f` by `g'` — has error
   contracting by `κ = max_{m>s}(‖gₘ‖cᵐ)/‖g‖ < 1` (finite because `κ < 1` uses strict
   domination **above `s` only**; replace `0` by `1/2`). Iterate; the Cauchy limit lands in
   `divisionSet g s`, which is **closed** by the bounds. Density + closedness ⇒ everything.
4. **Preparation** (Cor 1.28) is the corollary: divide `Xˢ` by `g` to get the distinguished
   monic `ω = Xˢ − r`, divide `g` by `ω`, and hypothesis-free quotient uniqueness forces the
   cofactor to be a unit.

**Why it dodges the radius entirely.** The Berkovich engine normalises `f` to norm `1`
(needs `c` to be the norm of a *unit* — see §3). Martin replaces "normalise to norm 1" by
"Euclidean-divide by the degree-`s` truncation", which needs only the *invertible leading
coefficient*. No unit-norm radius is ever required, so the coefficient ring need not be a
field and no extension is needed. Cross-variable ties below `s` (e.g. `X₀ + X₁` at equal
radii) are absorbed by the polynomial division.

### Lean file map (canonical)

| File (`PhD/Main/ForMathlib/RingTheory/…` unless noted) | Contents |
|---|---|
| `…/Analysis/Normed/Ring/NormMulUnit.lean` | `IsNormMulUnit` — multiplicative unit (Def 1.20, Lemma 1.21, Rem. 1.22) |
| `PowerSeries/Restricted/DivisionSet.lean` | `divisionSet`, `divisionAddSubgroup`, `isClosed_setOf_coeff_eq_zero`, `coeff_continuous` — hypothesis-light shared primitives |
| `PowerSeries/Restricted/MulDistinguished.lean` | `IsMulDistinguished` (Def 1.24) + native `norm_pos`/`norm_coeff_mul_pow_eq`/`nontrivial`; Lemma 1.26; `isMulDistinguished_toRestricted_of_monic` |
| `PowerSeries/Restricted/MulWeierstrassDivision.lean` | Prop 1.27: norm identity (1.8), bounds, `weierstrassDivision_{exists,q_unique,r_unique,polynomial}_of_isMulDistinguished` |
| `PowerSeries/Restricted/MulWeierstrassPrep.lean` | Cor 1.28: `weierstrassPreparation_{exists,unique,omega_unique,e_unique,polynomial}_of_isMulDistinguished` |
| `MvPowerSeries/Restricted/X0Polynomial.lean` | `toMvRestrictedX0` + `finSuccEquiv` isometry/unit transport (no distinguishedness) |
| `MvPowerSeries/Restricted/MulWeierstrass.lean` | `IsMulDistinguishedX0` + all multivariate endpoints and polynomial corollaries, by transport along `finSuccEquiv` |

Everything is sorry-free, depends only on `[propext, Classical.choice, Quot.sound]`, and
`PhD/ForMathlib` imports only `Mathlib` / `PhD.Main.ForMathlib` / `PhD.Main.Mathlib`.

---

## 2. The Berkovich proof (legacy, `PhD/Main/BirkovichWP/`)

The classical reduction, over a complete **nontrivially normed ultrametric field** `K`. It
proves the same endpoints by a dichotomy on the **divisible closure of the value group**
`√‖K^×‖` (`MemDivisibleValueGroup K c`: some `cⁿ = ‖x‖`, `x ∈ K`, `n ≠ 0`):

* **Radius-`1`, norm-one engine.** Normalise the divisor to `‖g‖ = 1`, reduce modulo the
  closed-ball ideal of radius `ε` to a **monic polynomial** over the residue ring `R°⧸ball`
  (a polynomial ring only at radius `1` — hence the rescaling detour), Euclideanly lift, and
  conclude by density (`AddSubgroup.dense_of_infDist_le`, BGR 1.1.4/2) + closedness. This is
  the `WeierstrassDivisionOracle`.
* **`c` in the divisible closure.** Adjoin an `n`-th root of a realising element inside a
  finite **spectral-norm** extension `L/K` (`MemDivisibleValueGroup.elim_finite_extension`);
  there `c` is a unit norm, divide with the oracle, and **descend** to `K`
  (`weierstrassDivision_descend`).
* **`c` off the divisible closure.** No Gauss term can tie the dominant one
  (`forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup` — a tie would exhibit
  `c^(s−t)` as a realised norm), so the strictly-dominated one-step engine
  (`weierstrassDivision_exists_of_forall_lt`) applies directly. **Multivariately**, this
  fails: cross-variable ties are genuine, so one passes to the **Gauss extension**
  `GaussExtension K (c i) = ℋ(η_{c i})` — a complete valued field in which `c i` becomes the
  norm of the unit `T` while the count of unrealised radii drops — divides there by
  induction, and descends along the `T⁰`-coefficient retraction
  (`weierstrassDivision_descend_of_retraction`). This is `MvPowerSeries/…/DivisibleRadius`.

`GaussExtension K r` is the completion of the `r`-Gauss-normed Laurent algebra
`K[T,T⁻¹]`; off the divisible closure every nonzero element has a unique dominant monomial,
so it is a **field** — Berkovich's `K_r = ℋ(η_{0,r})`, the completed residue field of the
type-3 (Gauss) point of radius `r`.

### Lean file map (legacy, `PhD/Main/BirkovichWP/RingTheory/…`)

| File | Contents |
|---|---|
| `LaurentPolynomial/GaussNorm.lean`, `GaussExtension.lean` | the field `K_r = ℋ(η_r)`, `‖T‖ = r`, norm-one retraction |
| `PowerSeries/Restricted/Distinguished.lean` | `IsDistinguished` (unit leading coefficient) |
| `PowerSeries/Restricted/Rescale.lean` | rescaling `Restricted R c ≃ Restricted R 1` for the oracle |
| `PowerSeries/Restricted/WeierstrassDivision.lean` | the **shared core**: bounds, uniqueness, closedness of `divisionSet`, the `_of_forall_lt` strictly-dominated engine, `weierstrassDivision_polynomial` |
| `PowerSeries/Restricted/WeierstrassDivisionOracle.lean` | the radius-`1` residue-field existence engine |
| `PowerSeries/Restricted/WeierstrassPrep.lean` | preparation as a corollary of division (`_of_forall_exists`) |
| `PowerSeries/Restricted/BaseChange.lean`, `MvPowerSeries/…/BaseChange.lean` | descent of a division along an isometric extension / the retraction |
| `PowerSeries/Restricted/DivisibleRadius.lean` | `MemDivisibleValueGroup`, the finite spectral extension, the univariate `_of_field` endpoints |
| `MvPowerSeries/Restricted/{Distinguished,WeierstrassDivision,DivisibleRadius}.lean` | `IsDistinguishedX0`, transported bounds, the multivariate Gauss-extension induction |
| `…/MulDistinguishedCompat.lean`, `MvPowerSeries/…/MulWeierstrassCompat.lean` | bridges `IsMulDistinguished ⟺ IsDistinguished` over `NormMulClass`, and the `_of_normMulClass` field-facing endpoints |

---

## 3. Why two proofs — the obstruction, and how Martin removes it

Both engines need the divisor's degree-`s` coefficient invertible and its Gauss term
strictly dominant *above* `s`. They differ in **existence**:

* The Berkovich oracle must **realise the radius as the norm of a unit** (to normalise `f`
  and to make the residue a polynomial ring). Over a field, algebraic extensions can never
  leave `√‖K^×‖` (`|x| = |N_{L/K}(x)|^{1/[L:K]}`, Neukirch II.4.8), so for radii off the
  divisible closure one needs a **value-transcendental** extension — precisely the Gauss
  extension `K_r`. Multivariately, cross-variable ties force it even to *state* the inductive
  step. This is why the classical theory (BGR §6.1.5: `T_n(c)` only for `c ∈ √‖K^×‖`) stops
  at the divisible closure and why the extension route looks unavoidable.
* Martin's **truncation/Euclidean** engine needs no unit-norm radius at all. So the
  obstruction above is an obstruction to the *oracle/one-step strategies*, **not to the
  theorem**. Martin's third strategy needs neither field, extension, nor completion.

**Consequence.** The endpoint theorems are **Martin's, not new** — cite [Mar16, §1.3]. The
project's contribution is (a) the formalisation, (b) the maximally general canonical
development, and (c) the Gauss-extension development as a verified alternative of independent
value: `GaussExtension` (the reusable `ℋ(η_r)` field), the equation-level descent lemmas, and
the `MemDivisibleValueGroup` API.

---

## 4. References

**The Martin proof.**
- **F. Martin**, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. **18** (2016), 2405–2457, **§1.3** (arXiv:1211.6684). Def 1.20, Lemma
  1.21, Rem. 1.22, Def 1.24, Lemma 1.26, **Prop 1.27** (division), **Cor 1.28**
  (preparation); multivariate polyradius as the closing remark of §1.3.
- **S. Lang**, *Algebra* (rev. 3rd ed.), IV §1 — Euclidean division by a polynomial with
  invertible leading coefficient (the `modByMonic` step, cited by Martin as [Lan02, 4.1.1]).

**The Berkovich / Gauss-extension proof.**
- **V. G. Berkovich**, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  AMS Math. Surveys & Monographs **33** (1990), **§2.1** — the field
  `K_r = {∑_{i∈ℤ} aᵢTⁱ : |aᵢ|rⁱ → 0}`, complete valued for `r ∉ √|K^×|`; the "extend scalars
  then descend" method. *The* reference for the route.
- **Bourbaki**, *Algèbre commutative* VI (Valuations), §10 n°1 — the Gauss extension of a
  valuation to `K(T)` with prescribed `v(T)`.
- **A. J. Engler, A. Prestel**, *Valued Fields*, §2.2 — value-transcendental case:
  `ℤδ ∩ Γ = 0 ⇒` the extension with `w(t) = δ` is unique, `Γ_w = Γ ⊕ ℤδ`, residue field
  unchanged (the "no ties off the closure" fact).
- **M. Lazard**, *Les zéros des fonctions analytiques d'une variable sur un corps valué
  complet*, Publ. Math. IHÉS **14** (1962), 47–75 — univariate division/zeros at arbitrary
  radii via Newton polygons.
- **K. S. Kedlaya**, *p-adic Differential Equations*, ch. 9 — Dwork–Robba generic points:
  completion of `F(t)` under the `ρ`-Gauss norm.
- **S. Bosch, U. Güntzer, R. Remmert (BGR)**, *Non-Archimedean Analysis* — §5.2.1–2
  (division at radius 1), §6.1.5 (`T_n(c)` only for `c ∈ √|K^×|`), §3.2 (spectral norm), and
  1.1.4/2 (the `infDist` density criterion).
- **L. Gruson**, *Théorie de Fredholm p-adique*, Ann. Sci. ÉNS (1966) — ultrametric Banach
  descent (backdrop for the retraction descent).
- **M. Temkin**, *On local properties of non-Archimedean analytic spaces II*, Israel J.
  Math. **140** (2004) — graded reduction, the known extension-free alternative; survey
  arXiv:1010.2235 Rem. 3.1.2.4 (Weierstrass theory developed only for strictly affinoid
  algebras; base change by `K_r` transfers *properties*, not the division statement).
- **J. Neukirch**, *Algebraic Number Theory*, Thm II.4.8 — `|x| = |N_{L/K}(x)|^{1/[L:K]}`:
  algebraic extensions never leave `√|K^×|` (why finite extensions cannot reach radii off the
  divisible closure).

**On the fixed-arbitrary-radius statement in the literature (context).** No Weierstrass
statement at a *fixed arbitrary* radius (over a Tate algebra, divisor a distinguished series)
appears to be recorded outside Martin. The Poineau school proves division for germs /
around rigid points, with radii *produced* by the proof, never centred at the Gauss point:
- **J. Poineau**, *La droite de Berkovich sur ℤ*, Astérisque **334** (2010), §2.2.1 (germ
  division, Grauert–Remmert) and §5.2 (fixed radius but only *large* `w`, monic polynomial
  divisor);
- **A. Ducros**, *Families of Berkovich spaces*, Astérisque **400** (2018), §2.11–2.12
  (ground-field extension `k_r`, "Shilov section" — the analogue of the retraction);
- **T. Lemanissier, J. Poineau**, *Espaces de Berkovich globaux* (arXiv:2010.08858), §1.6,
  §3.2 (rigid-point-centred norm-controlled division).

---

## 5. Summary for the write-up

The multivariate Weierstrass theorems have two independent formal proofs. The **canonical**
one (Martin) is elementary and maximally general — any complete ultrametric normed
commutative coefficient ring, every polyradius, no field extensions — and is the
mathlib-bound version in `PhD/Main/ForMathlib/`. The **Berkovich** one (Gauss extensions
`ℋ(η_r)` + descent) proves the same statements over a field by the classical reduction and
is retained under `PhD/Main/BirkovichWP/` for the reusable `GaussExtension` field, the descent
lemmas, and the `MemDivisibleValueGroup` API. Over a `NormMulClass` base the two notions of
"distinguished" coincide, and the compatibility bridges recover the field-facing endpoints
from the canonical ones with no extension machinery.
