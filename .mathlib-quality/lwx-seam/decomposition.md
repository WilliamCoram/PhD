# Decomposition for lwx-seam ([LWX] Prop 2.17 at `m = 1`, and Prop 3.1 in full for `D/ℚ`)

Planned 2026-09-05.  Source: [LWX] = Liu–Wan–Xiao, *The eigencurve over the boundary of weight
space*, arXiv:1412.2584v4 (printed page = PDF page).  Secondary locators `lwx.txt:N` = line `N`
of the `pypdf` extraction (see `plan.md`).  Every quote below is verbatim from that extraction
(hyphenation/spacing artifacts reproduced; subscripts flattened).  Other references:
[Colmez] = Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), Théorème 1.29
(cited by [LWX, §2.16]); [Koblitz] = *p-adic Numbers, p-adic Analysis, and Zeta-Functions*,
Ch. IV §2; [Buzzard] = *Eigenvarieties* (LMS 320), Cor 2.6, Lemma 12.2; [Jacobs] = *Slopes of
Compact Hecke Operators* (Imperial 2003), Def 1.27, pp. 20–21.

## Skeleton location

Every lemma is stated with `:= by sorry`; `lake build PhD.LWX.Quaternionic` (which pulls in the
other eight modules) passed on 2026-09-05 — **3720 jobs, sorries only, no type errors**.

| File | Lines | `sorry` | Tranche |
|---|---|---|---|
| `PhD/TateFredholm/Conjugation.lean` | 123 | 8 | C |
| `PhD/LWX/Specialize.lean` | 125 | 9 | S |
| `PhD/LWX/Binomial.lean` | 128 | 10 | B |
| `PhD/LWX/Colmez.lean` | 191 | 21 | M |
| `PhD/LWX/HaloWeight.lean` | 314 | 33 | W |
| `PhD/LWX/Certificates.lean` | 158 | 6 | H |
| `PhD/LWX/Seam.lean` | 321 | 23 | E |
| `PhD/ForMathlib/NumberTheory/Padics/AdicCompletionEquiv.lean` | 55 | 3 | F |
| `PhD/LWX/Quaternionic.lean` | 207 | 13 | Q |

No file of the concurrent `tate-riesz` board is touched (its footprint: `PhD/LWX/HaloRing.lean`,
`HaloTate.lean`, `TateRiesz.lean`, `PadicExpLog.lean` (declared frozen there),
`PhD/TateFredholm/{Coleman,Entire,Pr,Resultant,RieszColeman,SlopeFactor}.lean`).  All nine
files above are new; they *import* `HaloRing`/`PadicExpLog` through `IntegralModel` but never
edit them.

## Notation

`Λ^{>1/p} = HaloInt p`; `ψ : ℚ_[p] →+* K` isometric (`hψ`), `intHom ψ = ψ ∘ (ℤ_p ⊂ ℚ_p)`;
`T₀ ∈ K` a halo point, `h0 : p⁻¹ < ‖T₀‖`, and for the weight the **sub-annulus**
`h1 : ‖T₀‖² < p⁻¹` (i.e. `1/2 < v(T₀) < 1`; `‖T₀‖ < 1` follows);
`spec = HaloInt.specialize (intHom ψ) T₀ : Λ^{>1/p} → K`, `f ↦ ∑_j ψ(f_j)T₀^j`;
`s = haloExponent T₀ = log(1+T₀)/p` (`‖s‖ = p‖T₀‖ > 1`); `χ = haloCharFun ψ T₀ ω` ([LWX]'s
`κ_{T₀}`); `ρ = haloRho T₀ = ‖T₀‖√p`; `M1K ψ = ψ(M₁)`; `P = D.op ω` (integral `U_p`, Mahler
basis), `P(T₀) = specOp ψ T₀ ω D`; `Φ = monomialToMahler`, `Ψ⁻¹ = colmezToMonomial`,
`Ψ = colmezEquiv.symm`, `Δ = diagFactorial = diag(m!)`; `H = heckeBlockOp` (QMF, monomial basis).

---

## Result R1: [LWX, Proposition 2.17] at `m = 1` (`Seam.lean:315`, `Quaternionic.lean:156`)

### The source, verbatim

`lwx.txt:963–989` (p. 15): "Proposition 2.17. Using the isomorphism (2.11.1), the space SD int
admits an orthonormal basis (over Λ) given by 10,..., 1t−1,z 0,...,z t−1, (z0 2), ..., (zi 2),
..., where the subscript i indicates that the term comes from the ith direct summand. Let P =
(Pm,n)m,n∈Z≥0 denote the corresponding inﬁnite matrix for the Up-action, with coeﬃcients in Λ.
Suppose that the (uniform) limit of power series Char(P ) := det(I∞−XP ) = lim n→∞ det (In−X(Pi,j)
i,j=0,...,n−1) ∈ ΛJXK exists (which we shall prove in Theorem 3.16). Then it agrees with the
characteristic power series of the Up-action on each SD,†,m [−]m."

`lwx.txt:990–1016`: "Proof. By [Colm10, Théorèm 1.29] we cited above, the functions
⌊n/(q−1pm)⌋!·(zi n) for i = 0,...,t − 1 and n∈ Z≥0 form an orthonormal basis of SD,†,m [−]m. If
P′ denotes the inﬁnite matrix of Up-action on this basis, then P and P′ are conjugated by an
inﬁnite diagonal matrix with diagonal entries 1,..., 1 (t), 1,..., 1 (t),..., ⌊n/(q−1pm)⌋!,...,
⌊n/(q−1pm)⌋! (t), ... So taking the limit of the characteristic polynomial of the ﬁrst
r×r-minors, as r goes to inﬁnity gives Char(Up;SD,†,m [−]m) = det(I∞−XP′) = det(I∞−XP ),
provided that the latter is well deﬁned. □"

`lwx.txt:947–953` (§2.16): "By [Colm10, Théorèm 1.29], the functions ⌊n/(q−1pm)⌋!·(z n);
n∈ Z≥0 form an orthonormal basis of OBqp−m for the norm |·| qp−m,an."

`lwx.txt:863–875` (§2.12): "SD,†,m χ is an orthonormalizable Banach A-module … With respect to
this basis, the action of Up is given by an inﬁnite matrix, say P . Moreover, the action of Up
is compact (see e.g. [Bu07, Lemma 12.2]) … We deﬁne the characteristic power series of the
Up-action on SD,†,m χ to be Char(Up;SD,†,m χ) := det(I∞−XP )∈AJXK. This power series converges
and does not depend on the choice of the orthonormal basis (ei)i∈Z≥0."

`lwx.txt:770–778` (§2.7): "for m0∈ N≥4, we write Wm0 :=W≤p−1/pm0−4 and use [−]m0 : Z×p →
O×Wm0 to denote the induced universal character (the radius here is not optimal), which is
m0-locally analytic. Then SD intˆ⊗ΛOWm0 contains SD,† [−]m0 = ∪m≥m0 SD,†,m [−]m0 and hence
SD,†,m0 [−]m0 as subspaces."

### What is formalised, and what "`m = 1`" means

[LWX] prove Prop 2.17 for every `m` with `[−]_m` `m`-analytic.  The repo's general-weight layer
(`PhD/QMF/Weight/`) is Buzzard's `S^D_κ(U)` with the **Tate algebra** `c(ℕ, K)` as coefficient
module — functions analytic on the closed unit disc, i.e. [LWX]'s `OB_{qp^{-m}}` at `q⁻¹pᵐ = 1`,
i.e. `m = 1` for odd `p`.  At `m = 1` the Colmez basis is `n!·(z choose n) = descPochhammer n`.
The weight `κ_{T₀} = [−](T₀)` is `1`-analytic iff `‖log(1+T₀)‖ < p^{−1/(p−1)}`; we use the
joint-disc form `‖T₀‖² < p⁻¹` (`v(T₀) > 1/2`, sharp for `p = 3`) that `PhD/LWX/PadicExpLog.lean`'s
`exp`/`log` API provides.  [LWX, §2.7]'s radius `p^{−1/p^{m₀−4}}` is, in their words, "not
optimal"; on the sub-annulus `1/2 < v(T₀) < 1` our `m = 1` statement is the honest instance.
**Out of scope**: `m ≥ 2` (functions analytic on `a + p^{m−1}ℤ_p`), which the Tate-algebra layer
cannot express without [Bu04, Lemma 4] (level change `Iw_p ↔ Iw_{p^m}`), hence the boundary
region `v(T₀) ≤ 1/2` — recorded in `plan.md`.

### The decomposition (mirrors the proof)

```
R1  Char(P)(T₀) = det(1 − X·[UηU])                                  (E18)
├── R1.a  det(1 − X·H) = det(1 − X·(Ψ⁻¹HΨ))      [§2.12: basis independence; Buzzard Cor 2.6]
│         = charPowerSeries_conj (exists) + IsCompactoid H            (E16)
├── R1.b  Ψ⁻¹HΨ = P′ is diagonally intertwined with P(T₀):
│         Δ·P′ = P(T₀)·Δ                          [Prop 2.17 proof: "conjugated by an infinite
│         ├── R1.b.1  Φ ∘ H = P(T₀) ∘ Φ (blockwise seam identity)      diagonal matrix"]   (E15)
│         │   └── one certificate matrix: Φ ∘ (·‖_κ ψδ) = P(δ)(T₀) ∘ Φ   (E13)
│         │       ├── LHS on e_n: Mahler coords of z ↦ evalAt(autFactor·mobius^n)(z)  (M16, E11)
│         │       ├── RHS on e_n: spec of Mahler coords of z ↦ [cz+d]·möb(z)^n         (E8, E7)
│         │       │   [Prop 3.4: P_{m,n}(δ) = Δ̃^{(m)}(binom((az+b)/(cz+d), n)·[cz+d])]
│         │       └── pointwise agreement at ℕ-points                                    (E12)
│         │           [(2.3.2): χ(cz+d)·h((az+b)/(cz+d)); the weight's autFactor is χ(cz+d)]
│         └── R1.b.2  Φ = Δ ∘ Ψ   [Colmez basis = n!·Mahler basis]                  (M14, M15, E14)
├── R1.c  charPowerSeries P′ = charPowerSeries P(T₀)   [diagonal conjugation acts trivially
│         on principal minors — "the characteristic polynomial of the first r×r-minors"] (C1–C3, E17)
└── R1.d  charPowerSeries P(T₀) = specCharSeries D = spec(Char(P))   [Thm 3.16: Char(P) exists;
          Cor 3.18: evaluate at T₀]                                    (E1–E5, S1–S9)
```

Supporting sub-developments (leaves the source *cites* rather than proves):

```
W  the halo weight as an AnalyticWeight                  [§2.3: "χ m-locally analytic … so that
   ├── W.char  κ_{T₀} on ψ(ℤ_p^×)(1+p𝒪_K), multiplicative   (2.3.2) is well defined"; Notation 2.1:
   ├── W.psi   κ_{T₀}∘ψ = spec∘[−]                          [a] = ω(ā)(1+T)^{ℓ⟨a⟩}]
   ├── W.col   the column (cz+d)²κ_{T₀}(d)∑C(s,m)(c/d)^m z^m, decay ρ^m, evaluation
   └── W.aut   autFactor = χ(cz+d)
B  the p-adic binomial theorem ∑C(e,r)x^r = exp(e·log(1+x)) for an arbitrary exponent [Koblitz IV §2]
M  Colmez's basis is orthonormal at m = 1 (isometric equivalence)          [Colmez Thm 1.29; §2.16]
C  diagonal intertwining preserves principal minors; block-diagonal equivalences (general)
S  specialization is a continuous ring homomorphism (Cor 3.18's evaluation, bundled)
```

### Leaves, with source quotes and Lean ↔ source match

**Tranche C — `PhD/TateFredholm/Conjugation.lean` (general TateFredholm).**

* C1 `minor_eq_of_diag_intertwine` (:55), C2 `charCoeff_eq_of_diag_intertwine` (:63), C3
  `charPowerSeries_eq_of_diag_intertwine` (:71).  Source: Prop 2.17 proof, "P and P′ are
  conjugated by an inﬁnite diagonal matrix … taking the limit of the characteristic polynomial of
  the ﬁrst r×r-minors … gives det(I∞−XP′) = det(I∞−XP )".  **Match**: [LWX] phrase this with the
  inverse diagonal `diag(1/n!)`, which is unbounded on the Tate algebra; the formalisation states
  the *intertwining* `d i·v_{ij} = u_{ij}·d j` with `d i` units, which is exactly the finite-minor
  computation `det(D_S)det(v_S) = det(u_S)det(D_S)`, `det(D_S) = ∏_{i∈S} d i` a unit — the same
  argument at each minor, no inverse needed.  `charCoeff u n = (−1)^n ∑' S, minor u S` is
  TateFredholm's definition, so C2 is termwise (`tsum_congr`) and needs **no compactness**: this
  matches "provided that the latter is well defined" — well-definedness is a hypothesis on `P`
  ([LWX, Thm 3.16]), not on `P′`.
  Attacks: (i) *Is `det(D_S)` a unit in a general `NormedCommRing`?*  Product of units, yes
  (`IsUnit.prod`/`Finset.prod_isUnit`-type; or state via `Matrix.det_diagonal`); over `K` a field it
  is nonzero.  (ii) *Does restriction to `S` commute with multiplication by a diagonal?*  Yes —
  `(D·M)_S = D_S·M_S` because `D` is diagonal (`Matrix.diagonal_mul`, `Matrix.mul_diagonal`
  entrywise); this is precisely why the argument works for diagonal and fails for triangular `C`.
  (iii) *Orientation*: `d i * v_{ij} = u_{ij} * d j` ⇒ `D·M_v = M_u·D` ⇒ `det D det v = det u det D`
  ⇒ `minor v S = minor u S` — checked against the application in E17/E18 (`v = P′`, `u = P(T₀)`,
  `d(i,m) = m!`).
* C4–C8 `blockDiag_id`, `blockDiag_comp_blockOp`, `blockOp_comp_blockDiag`,
  `matrixCoeff_blockDiag`, `diagBlockEquiv` (:86–:109).  Source: the blockwise reading of
  (2.11.1), `S^D_int ≅ ⊕ᵢ C(ℤ_p; Λ)`, "where the subscript i indicates that the term comes from
  the ith direct summand" — the diagonal matrix of Prop 2.17 is block-diagonal with the same block
  `diag(n!)` in each summand.  **Match**: `blockOp_comp` (BlockOp.lean:699) gives all three
  composition rules with `Finset.sum_ite_eq`; `diagBlockEquiv` is `equivOfInverse` of
  `blockDiag e` and `blockDiag e.symm`, inverse by C5 + C4.
  Attacks: (i) `blockOp` of `if a = b then f else 0` needs `DecidableEq σ` — present.  (ii) The two
  `private` lemmas `diagBlock_comp_blockOp`/`blockOp_comp_diagBlock` in BlockOp.lean:833/846 are
  the scalar case (`φ a • id`); we re-prove the operator case rather than un-private (different
  statement) — no library edit needed.

**Tranche S — `PhD/LWX/Specialize.lean`.**

* S1–S9.  Source: `lwx.txt:1681–1700` (Cor 3.18 proof): "if ∑ m∈Z dmTm∈ Λ>1/p, then v(dm)≥
  max{0,−m}" and the evaluation `c_n(T)` at `T ∈ ℂ_p`, `0 < v(T) < 1`; Prop 2.17 needs the
  evaluation *through* `det(I∞−XP)` and through the limit.  **Match**: `HaloInt.specialize` is
  the coefficientwise evaluation of `HaloRing.lean`; S1–S5 make it a ring hom (`specializeHom`),
  S6–S7 make it continuous so it passes through `∑' S, minor` (E4).  S8–S9 compute it on
  `(1+T)^s` and `[a]` ([LWX, Notation 2.1], `lwx.txt:410–419`: "T corresponds to [exp(q)]−1 …
  [−] : Z×p → Λ× is the universal character").
  Attacks: (i) *Multiplicativity needs a Cauchy product over `ℤ × ℤ`*: the product family
  `ψ(f_i)T₀^i·ψ(g_j)T₀^j` tends to `0` cofinitely on `ℤ × ℤ` (each factor does, both bounded),
  which in the complete ultrametric `K` gives summability (`TateFredholm.summable_of_tendsto_cofinite`);
  `tsum_mul_tsum` + reindexing `(i, j) ↦ (i, i + j)` + `tsum_prod'` recovers
  `∑'_k ∑'_i ψ(f_i)ψ(g_{k−i}) T₀^k`; `ψ` passes through the inner `tsum` (`HaloRing.summable_mul_coeff`
  is public; `ψ` continuous since isometric).  Norm-summability (`summable_mul_of_summable_norm`)
  is **not** available — the terms decay only geometrically in a nonarchimedean field where
  `Summable ⇏ Summable ‖·‖` is fine but the mathlib product lemma needs norm-summability; the
  cofinite route avoids it.  (ii) *Continuity*: not Lipschitz (`‖spec f‖ ≤ ‖f‖^{α}`), but
  `norm_specialize_le` gives `‖f‖ ≤ p^{−k} ⇒ ‖spec f‖ ≤ ‖T₀‖^k`, which is continuity at `0`;
  additive ⇒ continuous (`continuous_of_continuousAt_zero`).  (iii) *`specialize_oneAddTPow`
  reindexes `ℤ → ℕ`*: `coeff_oneAddTPow` is `0` for `j < 0`; use `tsum_eq_tsum_of_ne_zero_bij` or
  `Function.Injective.tsum_eq` along `Nat.cast : ℕ → ℤ`.  `ψ (Ring.choose s r) = Ring.choose (ψ s) r`:
  `Ring.descPochhammer_eq_factorial_smul_choose` on both sides and cancel `r! ≠ 0` in `K`
  (`CharZero`); `Ring.choose` on `K` exists via `Module ℚ≥0 K` (Binomial.lean:277, verified by the
  build of `Binomial.lean`).

**Tranche B — `PhD/LWX/Binomial.lean`.**

* B10 `hasSum_choose_mul_pow` (:124): `∑_r C(e,r)x^r = exp(e·log(1+x))` on `‖x‖ ≤ c`,
  `‖e‖‖x‖ ≤ c`, `c² < ‖p‖`.  Source: [Koblitz, Ch. IV §2] (the `p`-adic binomial series); in
  [LWX] the identity is implicit in Notation 2.1's `(1+T)^s = [exp(qs)]` and §2.3's "The condition
  that χ is m-locally analytic is used so that the action (2.3.2) is well deﬁned" (`lwx.txt:626`).
  **Match**: the two instances used are `(e, x) = (ψ(ℓ⟨a⟩), T₀)` (W15: `[a](T₀) = ω(ā)·exp(ℓ⟨a⟩·log(1+T₀))`)
  and `(e, x) = (s, (c/d)z)` (W21: `(1+wz)^s = exp(s·log(1+wz))`); both satisfy the hypotheses
  with `c = ‖T₀‖` (checked: `‖s‖‖wz‖ ≤ p‖T₀‖·p⁻¹ = ‖T₀‖`; `p⁻¹ ≤ ‖T₀‖` by `h0`).
  **Why a new proof**: the fork's `tsum_binomialCoeff_eq_unitPow` (`1_PadicAnalytic.lean`) needs
  `e` in the closure of `ℕ` (`hnat`); here `e = s` has `‖s‖ > 1` and `e = ℓ⟨x⟩ ∈ 𝒪_K ⊄ ℤ_p` for
  ramified `K`.  The route is the identity theorem **in the exponent** (B5–B9): for fixed `x`,
  `∑_r C(e,r)x^r = ∑_j chooseCoeff x j·e^j` (B7, Fubini; `C(e,r) = ∑_j (descPoch_r)_j e^j / r!`) and
  `exp(e·L) = ∑_j (L^j/j!)e^j` (B8); both take the value `(1+x)^n` at `e = n ∈ ℕ` (B3, B4:
  `Ring.choose_natCast` + `add_pow`; `padicExp_natCast_mul` + `padicExp_padicLog`); the difference
  has coefficients `≤ C q^j`, `q = ‖x‖√(‖p‖⁻¹) < 1` (B6) and vanishes on `ℕ`, hence is `0` (B5,
  Strassman at `n = p^k → 0`).
  Attacks: (i) *Convergence at our `e` with `‖e‖ > 1`*: `‖chooseCoeff x j · e^j‖ ≤ (‖e‖‖x‖·√(‖p‖⁻¹))^j
  ≤ (c√(‖p‖⁻¹))^j`, and `c² < ‖p‖ ⇔ c√(‖p‖⁻¹) < 1` — fine; the naive bound with `‖x‖ ≤ c` alone
  would need `c² < ‖p‖^{3/2}` (rejected in planning; the statement carries `‖e‖‖x‖ ≤ c`
  separately for this reason).  (ii) *B5 needs vanishing at `p^k`, which are natural numbers* —
  yes, `(p^k : K)`; the tail estimate `‖∑_{j>j₀} a_j (p^k)^j‖ ≤ C q^{j₀+1}‖p‖^k → 0 < ‖a_{j₀}‖`.
  (iii) *B7's Fubini*: the double family `(r, j) ↦ (descPoch_r)_j/r!·x^r e^j` vanishes for `j > r`
  (`descPochhammer_natDegree`), so per `r` finitely many `j`; norm `≤ max(‖x‖, ‖e‖‖x‖)^r/‖r!‖ ≤
  c^r √(‖p‖⁻¹)^{r−1}` → summable on `ℕ × ℕ` by cofinite decay; `tsum_prod'`/`tsum_comm'` need the
  fiber summabilities, available from the same bound.  (iv) *`descPochhammer ℤ r` coefficients cast
  to `K` have norm `≤ 1`*: integers in an ultrametric field (`IsUltrametricDist.norm_intCast_le_one`
  or via `norm_natCast_le_one` + `norm_neg`).  (v) *`‖1/r!‖ ≤ √(‖p‖⁻¹)^{r−1}`*: `sq_norm_factorial_ge`
  (PadicExpLog.lean:89, `hp2`): `‖p‖^{r−1} ≤ ‖r!‖²`.

**Tranche M — `PhD/LWX/Colmez.lean`.**

* M1–M6 (Mahler coordinates of monomials; Newton's formula on `ℕ` and `ℤ_p`).  Source: §2.16
  `lwx.txt:927–933`: "The functions 1,z,..., (z n),... form an orthonormal basis of C(Zp; Zp),
  called the Mahler basis. In other words, any f∈C (Zp; Zp) admits a Mahler expansion: (2.16.1)
  f(z) = ∑ n≥0 an (z n), where all an∈ Zp; and lim n→∞ |an| = 0."  **Match**: for the monomial
  `zᵏ` the expansion is finite with `a_m = Δ^m(nᵏ)(0)` (Newton's forward-difference formula,
  mathlib `shift_eq_sum_fwdDiff_iter`), which is M3 on `ℕ` and M6 on `ℤ_p` (both sides continuous,
  `PadicInt.denseRange_natCast`); `fwdDiff_iter_pow_eq_zero_of_lt`/`fwdDiff_iter_eq_factorial`
  give the vanishing/`k!` (M1, M2).
  Attacks: (i) mathlib's `fwdDiff_iter_pow_eq_zero_of_lt` is for `fun r : R => r^j` with domain =
  codomain = `R` — the skeleton defines `mahlerCoeffPow` on `ℤ → ℤ` to match (fixed during the
  skeleton build).  (ii) M4 uses `fwdDiff_iter_choose_zero : Δ^m (fun x : ℕ => (x.choose n : ℤ)) 0 =
  if m = n then 1 else 0` (domain `ℕ`) while `mahlerCoeffPow` has domain `ℤ`: at the point `0`
  both expand to the same finite sum over `0..m` (`fwdDiff_iter_eq_sum_shift`); the worker proves a
  one-line bridge.  (iii) *Is `Ring.choose z m` continuous in `z ∈ ℤ_p`?*  It is
  `PadicInt.mahler m` (mathlib `MahlerBasis.lean`), a `C(ℤ_[p], ℤ_[p])`.
* M7–M11 (`colmezToMonomial` is an isometric equivalence).  Source: §2.16 `lwx.txt:947–953`
  ([Colmez, Thm 1.29]: the functions `⌊n/(q⁻¹pᵐ)⌋!·(z choose n)` are an ON basis of
  `OB_{qp^{−m}}`), at `m = 1`: `n!·(z choose n) = descPochhammer n`.  **Match**: an ON basis of
  the Tate algebra in monomial coordinates is a linear isometry onto `c(ℕ, K)`; `colmezToMonomial`
  sends `e_m` to the coefficient sequence of `descPochhammer ℤ m` (integers, upper-unitriangular).
  Isometry (M8): at the largest index `n₀` with `‖a n₀‖ = ‖a‖` (exists: `a → 0` cofinitely), the
  `n₀`-th monomial coordinate is `a n₀ + ∑_{m>n₀} a_m·(integer)` with the sum strictly smaller.
  Surjectivity (M9–M10): the range is closed (isometry) and contains every `single k 1`
  (triangular solving, `monic_descPochhammer`, `descPochhammer_natDegree`), hence all finitely
  supported sequences, which are dense (`cSpace.hasSum_single`).
  Attacks: (i) *We do not prove the inverse has integral entries* (Stirling numbers of the second
  kind) — not needed: `colmezEquiv` is built from bijectivity + the isometry, and the inverse is
  again an isometry (`‖Ψ b‖ = ‖Ψ⁻¹(Ψ b)‖`) hence continuous (`continuous_invFun`), so no
  open-mapping theorem and no `NormedSpace` instance (mathlib's
  `ContinuousLinearEquiv.ofBijective` needs `NormedSpace`, which `c(ℕ, K)` does not carry — found
  and fixed at skeleton time).  (ii) *Density of finitely supported sequences in `c(ℕ, K)`*:
  `cSpace.hasSum_single` gives every `f` as the limit of finite partial sums — the partial sums
  are finite combinations of `single`s in the range.
* M12–M15 (`Φ = Δ ∘ Ψ`).  Source: Prop 2.17 proof, "P and P′ are conjugated by an inﬁnite
  diagonal matrix with diagonal entries … ⌊n/(q−1pm)⌋! …".  **Match**: the Mahler coordinates of
  `descPochhammer m = m!·(z choose m)` are `m!·e_m` (M4), i.e. `Φ ∘ Ψ⁻¹ = Δ` (M14), i.e.
  `Φ = Δ ∘ Ψ` (M15) — the diagonal matrix, with `n!` at `m = 1`.
  Attacks: (i) `ext_matrixCoeff` + `matrixCoeff_comp` (Matrix.lean:66, :84) reduce M14 to
  `∑' k, (descPoch_m)_k·Δ^j(nᵏ)(0) = Δ^j(descPoch_m)(0)`, a finite sum since `(descPoch_m)_k = 0`
  for `k > m`; linearity of `Δ^j` over the finite sum via `fwdDiff_iter_eq_sum_shift`.  (ii) `Δ` is
  bounded (`‖m!‖ ≤ 1`) — entries integral; columns finite.
* M16 `fwdDiff_iter_evalAt_natCast` (:185): `Δ^m(n ↦ F(n))(0) = ∑'_k F_k·Δ^m(nᵏ)(0)` for
  `TendstoCoeff F`.  Source: (2.16.1) again — the Mahler coefficients of a function are its forward
  differences at `0`, and for a convergent series this is termwise.  **Match**: `Δ^m g(0)` is the
  finite sum `∑_{i≤m} (−1)^{m−i}C(m,i) g(i)` and `g(i) = ∑'_k F_k i^k` (`TendstoCoeff.hasSum_evalAt`);
  swapping a finite sum with `tsum` (`tsum_finset_sum`/`HasSum.sum`).
  Attack: *no Mahler theorem over `K` is needed* — the statement is about the finitely many points
  `0..m`; this is deliberate (the `ℤ_p`-Banach-module structure on `K` via `ψ` is avoided
  altogether).

**Tranche W — `PhD/LWX/HaloWeight.lean`.**

* W2–W7 (`teichRes`).  Source: Notation 2.1 `lwx.txt:410–412`: "We write Z×p as ∆× (1 +qZp)×
  with ∆∼= (Z/qZ)×".  **Match**: `teichRes r` is the Teichmüller representative of the residue
  class `r` (`UnitsLog.teichmuller` of a unit lift), multiplicative (`teichmuller_mul`, locally
  constant by `teichmuller_eq_of_norm_sub_le`), residue `r`, injective, and every unit is within
  `p⁻¹` of it (`norm_mul_teichmuller_inv_sub_one_le`).
  Attacks: (i) *the lift `(r.val : ℤ_p)` is a unit*: `PadicInt.isUnit_iff`/`norm_eq_one` from
  `toZMod (r.val) = r ≠ 0` (`ZMod.natCast_zmod_val`, `map_natCast`); (ii) *injectivity*: distinct
  residues ⇒ `‖τr − τr'‖ = 1` (residues differ) — via `toZMod_teichRes` and `PadicInt.norm_lt_one_iff`-type.
* W8–W9 (`haloUnits`).  Source: §2.3 `lwx.txt:606–612`: the action `χ(cz + d)` needs `χ`
  defined at `cz + d`; [Jacobs, p. 29] / `QMF.ExpansionData.mem_level`: the level's values
  `cz + d`, `‖z‖ ≤ 1`, must lie in the character's domain.  **Match**: for `g ∈ M1K ψ`,
  `d ∈ ψ(ℤ_p^×)` and `‖cz‖ ≤ p⁻¹`, so `cz + d ∈ ψ(ℤ_p^×)(1 + p𝒪_K) = haloUnits ψ` (W19).
  Attacks: (i) *closure under products*: `x ≈ ψa`, `y ≈ ψb` ⇒ `xy ≈ ψ(ab)` (ultrametric, all norms
  `1`); *inverses*: `‖x⁻¹ − (ψa)⁻¹‖ = ‖ψa − x‖`.  (ii) *uniqueness of the residue class* (W9): two
  lifts within `p⁻¹` of `x` are within `p⁻¹` of each other ⇒ equal Teichmüller lifts (W7).
* W10–W16 (`χ = haloCharFun`, `haloChar`).  Source: Notation 2.1 `lwx.txt:412–419` ("We identify
  (1 +qZp)× with Zp via (1/q) log(−) … [−] : Z×p → Λ× is the universal character … each
  continuous ring homomorphism χ : Λ→ Cp deﬁnes a continuous character χ◦ [−]") and the
  formalised `univChar ω a = ω(ā)·(1+T)^{ℓ⟨a⟩}` (IntegralModel.lean:159).  **Match**:
  `χ(x) = ψ(ω r)·exp(s·log(x/ψ(τr)))` with `s = log(1+T₀)/p`, i.e. `(1+T₀)^{log⟨x⟩/p}` written
  through `exp`/`log` on the joint disc (`‖s·log⟨x⟩‖ ≤ p‖T₀‖·p⁻¹ = ‖T₀‖`, `‖T₀‖² < ‖p‖`):
  multiplicative by `teichRes_mul` + `padicLog_mul` + `padicExp_add` (W13); on `ψ(ℤ_p^×)` it is
  `spec ∘ univChar` by S9 + B10 (W15: `(1+T₀)^{ψ(ℓ⟨a⟩)} = ∑ C(ψℓ, r)T₀^r = exp(ψℓ·log(1+T₀))`,
  `ψ(ℓ⟨a⟩) = log(ψ⟨a⟩)/p` since `ψ` commutes with the log series).  The QMF character is
  `x ↦ x²·χ(x)` (W16): [Jacobs, Def 1.27] normalises by `(cz+d)^{−2}`, [LWX, (2.3.2)] does not.
  Attacks: (i) *the total-function definition* `∑_r if … then … else 0` has exactly one nonzero
  summand on the halo units (W9) and is `0` off them — W11 is `Finset.sum_eq_single`.  (ii)
  *`haloCharFun_one`*: `r = 1`, `teichRes 1 = 1`, `padicLog 1 = 0`, `padicExp 0 = 1`.  (iii)
  *`‖s‖ = p‖T₀‖`*: `norm_padicLog_eq` (PadicExpLog.lean:753) on `‖T₀‖² < ‖p‖`, and `‖p‖ = p⁻¹`
  (`norm_natCast_p` from `hψ`).  (iv) *`padicExp_add` hypotheses*: `‖s·log(x/ψτr)‖² ≤ ‖T₀‖² < ‖p‖`.
* W17–W19 (`M1K`, `haloRho`, level bounds).  Source: (2.3.3) `lwx.txt:614–617`: "M1 := {(a b; c d)
  ∈ M2(Zp) | q|c, p ∤ d, and ad−bc ≠ 0}".  **Match**: `M1K ψ` is the `ψ`-image of the formalised
  `M1 p` (IntegralModel.lean:226); `LevelBounds (M1K ψ) ρ` needs `‖c‖ ≤ ρ`, true since
  `‖c‖ ≤ p⁻¹ ≤ ρ = ‖T₀‖√p` (`p⁻¹ < ‖T₀‖`).
  Attack: *`ρ ≥ p⁻¹` is essential*: the QMF compactness certificate and the row-decay bound both use
  it (W20, E16); with `ρ < p⁻¹` the level would not satisfy `LevelBounds`.
* W20 `norm_coeff_haloCol_le` (:260).  Source: §2.3 `lwx.txt:606–612`: "Here analytic function
  means that the values of the function can be given by a convergent Taylor series on the speciﬁed
  p-adic disk. The condition that χ is m-locally analytic is used so that the action (2.3.2) is
  well deﬁned"; [Jacobs, p. 29]: "`exp₃(t log(cx + d))` converges to an element of `𝒪₃[[x]]`".
  **Match**: the column `(cz+d)²·χ(d)·∑_m C(s,m)(c/d)^m z^m` has `‖C(s,m)(c/d)^m‖ ≤
  (p‖T₀‖)^m·√p^{m−1}·p^{−m} ≤ (‖T₀‖√p)^m = ρ^m` (`‖s − k‖ ≤ ‖s‖` since `‖s‖ > 1`;
  `sq_norm_factorial_ge`), and multiplying by `(cz+d)²` (coefficients `d², 2cd, c²` of norms
  `1, ≤ p⁻¹, ≤ p⁻²`) keeps `≤ ρ^m` because `p⁻¹ ≤ ρ`.
  Attacks: (i) *edge cases `m = 0, 1`*: the `(cz+d)²`-shift terms with negative index are absent;
  handle by `PowerSeries.coeff_mul` and case analysis.  (ii) *the bound is exactly the joint-disc
  condition*: `ρ < 1 ⇔ ‖T₀‖² p < 1` — with `‖T₀‖² < p⁻¹` from `h1`; this is where the sub-annulus
  enters and cannot be weakened by this proof.
* W21 `evalAt_haloCol`, W22 `haloExpansion.eval` (:270, :280).  Source: [Jacobs, Def 1.27] as
  formalised in `QMF.ExpansionData.eval`: "The expansion evaluates to the character".  **Match**:
  `evalAt(haloCol)(z) = (cz+d)²·χ(d)·∑_m C(s,m)(wz)^m = (cz+d)²·χ(d)·exp(s·log(1+wz))` (B10) `=
  (cz+d)²·χ(d)·χ(1+wz)` (W11 at `r = 1`) `= (cz+d)²·χ(cz+d)` (W13).
  Attacks: (i) *`evalAt` of a product of a polynomial and a series*: `evalAt_mul` (Char.lean:92)
  needs `AbsSummable` of both factors — the polynomial is finitely supported, the series has
  geometric decay (W20).  (ii) *`1 + wz ∈ haloUnits`* with `r = 1`: `‖(1+wz) − 1‖ ≤ p⁻¹`.
* W23–W24 (`autFactor`).  Source: [Jacobs, Def 1.27] "`κ(cz+d)/(cz+d)²`" (README §3) and
  [LWX, (2.3.2)] `lwx.txt:596–603`: "h‖χ (a b; c d)(z) = … = χ(cz +d)h((az +b)/(cz +d))".
  **Match**: `autFactor = col·(linX)⁻²` (SlashAction.lean:356) with `linX γ = C d + C c·X`
  (Series.lean:167): the `(cX+d)²` of the column cancels (`linX` is a unit, constant coefficient
  `d ≠ 0`), leaving `C(χ(d))·mk(C(s,m)(c/d)^m)` (W23), which evaluates to `χ(cz+d)` (W24, from W21
  and `evalAt_linX_inv` or directly from B10 + W13).

**Tranche H — `PhD/LWX/Certificates.lean`.**

* H1–H4 (shapes).  Source: Prop 3.1 proof `lwx.txt:1094–1101`: "δi,j,p = ui,j,p vj ∈ Iwq (p 0; 0 1)
  Iwq ⊆ (pZp Zp; qZp Z×p)".  **Match**: `x, y ∈ U ⊆ θ⁻¹(M₁)` and `η` with `‖η₀₀‖ ≤ p⁻¹`,
  `‖η₁₀‖ ≤ p⁻¹` (both hold for `(p 0; 0 1)`): the `(0,0)` entry of `θx·θη·θy` is
  `x₀₀η₀₀y₀₀ + x₀₀η₀₁y₁₀ + x₀₁η₁₀y₀₀ + x₀₁η₁₁y₁₀`, each term in `pℤ_p` (`‖y₁₀‖ ≤ p⁻¹` from `M₁`);
  the certificate `u_{i,t}·v_t` with `v_t = u₁ηu₂` (`exists_mul_eta_mul_of_bijOn`) is of this form.
  H1–H2 (unit determinant, unit `a`) are the Iwahori shape of group elements — needed only as
  documentation of "`Iw_q`" (the shape proof uses just `M₁`-membership).
  Attacks: (i) *does the shape proof need `x ∈ U` or only `θx ∈ M₁`?*  Only `M₁` (entries `≤ 1`,
  `‖c‖ ≤ p⁻¹`); stated with `x y : U` for the application.  (ii) *`Halo.lean`'s
  `exists_localMat_iwahori_mul`/`UpDatum.ofCosets`* prove the same shape with the explicit
  `v_j = (p 0; jp 1)` and a `choose`; `ofCerts` replaces the `choose` by `M1.toLocalMat` so that the
  display hypothesis of `intEvalAtReps_comm` is `rfl` (`ofCerts_mat`).
* H5 `intEvalAtReps_intHeckeOperator` (:143).  Source: Prop 3.1 statement `lwx.txt:1035–1050`
  (the commutative diagram) and proof `lwx.txt:1080–1093`: "(Upϕ)(γi) = ∑ p−1 j=0 ϕ(γiv−1 j)‖[−]
  vj. Write each γiv−1 j uniquely as δ−1 i,jγλi,jui,j … Then we have (Upϕ)(γi) = ∑ p−1 j=0
  ϕ(γλi,j)‖[−] ui,j,pvj".  **Match**: `heckeOperatorSlash_apply_rep` (Slash/HeckeMatrix.lean:57)
  *is* this display for any ring-generic slash action (`c·vₜ⁻¹ = dₜ·cₜ'·uₜ`), and
  `intEvalAtReps_comm` (IntegralModel.lean:1458) turns the display into the block-matrix identity
  with `D.mat i t = M1.toLocalMat (certM1 i t)` (`rfl`) — exactly `QMF.Weight.heckeOperator_apply_rep`'s
  proof (Compact.lean:166) transposed to the integral action.
  Attacks: (i) *`IntForms` vs `slashFixedPointsOfLE`*: `IntForms` is `levelSubmoduleSlash`
  (IntegralModel.lean:1402) while `heckeOperatorSlash` acts on `slashFixedPointsOfLE`; the skeleton
  compiles `intHeckeOperator` with the latter's type ascribed to `IntForms`, so the two are
  definitionally equal under the same `letI`/`haveI` (verified by the build).  (ii) *the slash of
  the level action at `⟨u·vRep t, _⟩`* is `seqSlashAction.slash a (levelM1ToM1 θ ⟨…⟩)` with
  `levelM1ToM1 θ g = ⟨θ g, g.2⟩` (IntegralModel.lean:1360) — `certM1` by `rfl`.
* H6 `bijective_intEvalAtReps_of_stabilizer_eq_bot` (:154).  Source: (2.11.1) `lwx.txt:847–856`:
  "SD int ≅ ⊕ t−1 i=0 C(Zp; Λ) … ϕ ↦ (ϕ(γi))" under Hypothesis 2.10 (neat).  **Match**: the
  ring-generic `bijective_evalAtRepsSlash` at trivial stabilisers, exactly
  `QMF.Weight.bijective_evalAtReps_of_stabilizer_eq_bot` (Compact.lean:368) with `K` replaced by
  `HaloInt p` and the values `c(ℕ, HaloInt p)`.
  Attack: *the QMF proof uses `blockProj_evalAtReps`/`cSpace.blockProj_apply`* — the integral
  mirrors exist (`blockProj_intEvalAtReps`, IntegralModel.lean:1435).

**Tranche E — `PhD/LWX/Seam.lean`.**

* E1–E5 (`P(T₀)` and `det(I − XP(T₀)) = Char(P)(T₀)`).  Source: Thm 3.16 `lwx.txt:1596–1609`
  ("Let P = (Pm,n) … as in Proposition 2.17. The characteristic power series … Char(P) … is well
  deﬁned") and Cor 3.18 `lwx.txt:1681`: "For T∈ Cp with 0 < v(T ) < 1, we have v(cn(T ))≥
  λ(n)v(T )" — `c_n(T)` is the evaluation.  **Match**: `specCharSeries D ω ψ T₀ = mk (n ↦
  spec(charCoeff (D.op ω) n))` (Halo.lean:157); `specOp` has matrix `spec ∘ D.matrix`
  (`matrixCoeff_blockOp`, `matrixCoeff_ofCoeffs`, `matrixCoeff_op`); its minors are `spec` of the
  integral minors (`RingHom.map_det` for `specializeHom`), and the sum over `|S| = n` passes
  through `spec` by continuity (S7) because the integral family is summable
  (`summable_minor_upOp`, Halo.lean:113 — [LWX, Thm 3.16]'s "well defined").
  Attacks: (i) *`specOp` is a bounded operator although `P(T₀)` is not compactoid* (Remark 2.8):
  `ofCoeffs` needs only bounded entries and cofinite column decay, which `norm_entry_le` +
  `norm_specialize_le` give (`‖spec(entry m n)‖ ≤ ‖T₀‖^{m − ⌊n/p⌋}` → 0 in `m`).  (ii) *no
  `charCoeff_map`* (BaseChange.lean:482 needs an isometric hom and a compactoid `u`) — E3/E4 go
  through the minors directly; `charCoeff` is the `tsum` by definition (Fredholm.lean:148).
* E6 (`levelMonoidOf_thetaK`).  Source: §2.4 `lwx.txt:697–703` (equivariance under `Iw_q`) and
  the formalised `levelM1 θ = θ⁻¹(M₁)` (IntegralModel.lean:1355).  **Match**: `θ_K = ψ∘θ`,
  `θ⁻¹(ψ(M₁)) = θ⁻¹(M₁)` since `ψ` (hence `Matrix.map ψ`) is injective.
* E7–E8 (integral Mahler coordinates of `[cz+d]·möb(z)ⁿ`).  Source: Prop 3.4 `lwx.txt:1144–1150`:
  "Let P (δp) = (Pm,n(δp)) denote the inﬁnite matrix for this action with respect to the
  orthonormal Mahler basis 1,z, (z 2),... . Then (3.4.1) Pm,n(δp) = ∆̃(m)( ((az +b)/(cz +d) n)
  ·[cz + d] )".  **Match**: `seqSlash_coeff` (IntegralModel.lean:1414) is (3.4.1) as
  `(a ∣ δ)_m = ∑' k, a_k·P_{m,k}(δ)` with `a ∣ δ = mahlerCoeffs (cfunSlash (mahlerON a) δ)` and
  `mahlerCoeffs F m = Δ^m F 0`; at `a = mahlerOfPow n` (finite Mahler coordinates of `zⁿ`, E7 via M6
  and `mahlerON_apply`) the sum is finite and `mahlerON a = zⁿ`, giving E8.
  Attack: *`cfunSlash (z ↦ const zⁿ) δ = z ↦ [cz+d]·const(möb(z)ⁿ)`* is `rfl` from `cfunSlash`
  (IntegralModel.lean:533) once `mahlerON_mahlerOfPow` is rewritten pointwise (`ContinuousMap.ext`).
* E9–E12 (pointwise agreement at `ℕ`-points).  Source: (2.3.2) `lwx.txt:596–603` (the action is
  `χ(cz+d)·h((az+b)/(cz+d))`) read on both sides of `ψ`.  **Match**: `spec([cz+d]·const(möb(z)ⁿ))
  = χ(ψ(cz+d))·ψ(möb z)ⁿ` (S3, S5, W15) and `ψ(cz+d) = c'ψz + d'`, `ψ(möb z) = evalAt(mobius g)(ψz)`
  (E9, E10: `LocalMat.denUnit`/`mobiusFun` are `cz + d` and `(az+b)·inverse(cz+d)`,
  `evalAt_mobius`); `evalAt(autFactor·mobiusⁿ)(w) = χ(c'w+d')·evalAt(mobius)(w)ⁿ` (W24,
  `evalAt_mul`, `evalAt_pow`, `absSummable_autFactor`, `absSummable_mobius`).
  Attacks: (i) *`Ring.inverse` through `ψ`*: `ψ(Ring.inverse u) = (ψ u)⁻¹` for a unit `u`
  (`Ring.inverse_unit`, `map_units_inv`); (ii) *`evalAt_mobius` needs `‖c'‖ < ‖d'‖`*: `p⁻¹ < 1`.
* E13 `monomialToMahler_comp_kappaSlash` (:212).  Source: Prop 2.17 proof — `P′` is "the inﬁnite
  matrix of Up-action on this basis"; the formal content that the QMF operator in monomial
  coordinates and `P(T₀)` in Mahler coordinates are the *same operator* `f ↦ χ(cz+d)f(möb z)`.
  **Match**: `ext_matrixCoeff` + `matrixCoeff_comp`: column `n` of the left is the Mahler
  coordinates of `n ↦ evalAt(autFactor·mobiusⁿ)(n)` (M16, E11); column `n` of the right is
  `∑_{k≤n} Δ^k(zⁿ)(0)·spec(P_{m,k})` = `spec` of `Δ^m(z ↦ [cz+d]möb(z)ⁿ)(0)` (E8, M5 with
  `specializeHom.toAddMonoidHom`) = `Δ^m(k ↦ χ(ψ(ck+d))ψ(möb k)ⁿ)(0)` (E12 pointwise); the two
  `Δ^m` at `0` agree since both are the finite sum over `0..m` (`fwdDiff_iter_eq_sum_shift`; the
  integral function is on `ℤ_p`, the `K`-side one on `ℕ`, evaluated at the casts of `0..m`).
  Attacks: (i) *the `ℤ_p`-domain vs `ℕ`-domain bridge* — a two-line lemma the worker adds (both
  sides `= ∑_{i≤m} (−1)^{m−i}C(m,i)·(value at i)`); (ii) *columns of `Φ` are finite* so the
  `tsum` on the right is a `Finset.sum` (`tsum_eq_sum` with `mahlerCoeffPow_eq_zero_of_lt`).
* E14–E15 (blockwise).  Source: (2.11.1) blockwise; Prop 3.1(1)–(2): "Each entry of Up is a sum
  of operators of the form ‖[−] δp … There are exactly p such operators appearing in each row and
  each column".  **Match**: `heckeBlock i j = ∑_{t : idx i t = j} 1 • kappaSlash(θ_K(u·vRep t))`
  (Compact.lean:151, `χ = 1`) and `specOp (ofCerts)` has the same block structure with
  `specEntryOp (M1.toLocalMat (certM1 i t))`; `θ_K(u·vRep t) = ψ(certM1 i t)` is `rfl`
  (`thetaK_cert`), and `levelMonoidOfToS θ_K S ⟨g, _⟩ = M1K.ofM1 ψ (certM1 …)` by `Subtype.ext rfl`.
  C5/C6 pass `blockDiag Φ` through `blockOp`.
  Attack: *`(1 : Kˣ) • ·`* in `heckeBlock` — `one_smul` after `MonoidHom.one_apply`, as in
  `mem_forms_iff_one`.
* E16 `isCompactoid_heckeBlockOp_haloWeight` (:270).  Source: §2.12 "the action of Up is compact
  (see e.g. [Bu07, Lemma 12.2])".  **Match**: `isCompactoid_blockOp` (BlockOp.lean:683) +
  `IsCompactoid.finset_sum`/`smul` + `AnalyticWeight.isCompactoid_kappaSlash g (hρσ : ρ ≤ σ) (hσ)
  (ha : ‖g 0 0‖ ≤ σ)` at `σ = ρ` with `‖g 0 0‖ = ‖δ.a‖ ≤ p⁻¹ ≤ ρ` from `hshape` — the `U_p`-shape
  is exactly the compactness certificate ([Jacobs, Lemma 2.7] as formalised).
  Attack: *QMF's `isCompactoid_heckeBlockOp` needs `η` and `hv`* (the `‖det θη‖ ≤ σ` route); we use
  the entrywise route from the shape hypothesis instead, so R1 needs no `η` at all — consistent
  with `UpDatum` carrying only shapes.
* E17 `diagFactorialBlock_comp_colmezConj` (:287), E18 **milestone** (:305).  Source: Prop 2.17
  proof in full (quoted above).  **Match**: E15 + E14 give `Δ·Ψ⁻¹·H = P(T₀)·Δ·Ψ⁻¹`; composing with
  `Ψ` on the right, `Δ·(Ψ⁻¹HΨ) = P(T₀)·Δ` (E17, `ContinuousLinearEquiv.symm_comp_self`); reading
  matrix coefficients (`matrixCoeff_comp`, `matrixCoeff_blockDiag`, `matrixCoeff_diagFactorial`):
  `m!·(Ψ⁻¹HΨ)_{(i,m),(j,n)} = P(T₀)_{(i,m),(j,n)}·n!`, so C3 (`d (i,m) = m!`, units in `K`) gives
  `charPowerSeries (Ψ⁻¹HΨ) = charPowerSeries P(T₀)`; `charPowerSeries_conj` (Fredholm.lean:953) with
  `φ = colmezEquivBlock.symm` and E16 gives `charPowerSeries (Ψ⁻¹HΨ) = charPowerSeries H`; E5
  closes.  `heckeCharPowerSeries = charPowerSeries H` is `rfl` (Fredholm.lean:49).
  Attacks: (i) *`charPowerSeries_conj`'s shape* is `((φ.comp u).comp φ.symm)`; with `φ := Ψ_ι.symm`
  this is `(Ψ⁻¹ ∘ H) ∘ Ψ`, matching E17's left factor exactly.  (ii) *orientation of C3* checked
  above (v = `Ψ⁻¹HΨ`, u = `P(T₀)`).  (iii) *`Γ` does not appear*: `heckeCharPowerSeries` is defined
  from the block operator alone — no neatness, no bijectivity, no `η` in R1 (they enter only in the
  spectral reading Q10).

**Tranche F/Q — `AdicCompletionEquiv.lean`, `PhD/LWX/Quaternionic.lean`.**

* F1–F3.  Source: [LWX, §2.4] `lwx.txt:687–690`: "We ﬁx a deﬁnite quaternion algebra D over Q
  which splits at p, and we ﬁx an isomorphism D⊗ Qp≃ M2(Qp)".  **Match**: the general-weight
  layer fixes `D ⊗ F_v ≅ M₂(F_v)` (`RigidificationAt`); at `F = ℚ`, `v = (p)`, `F_v ≅ ℚ_p` is
  mathlib's `Padic.adicCompletionEquiv`, an isometry once `absNorm (v) = p` is known — the
  `p = 3` proof `JacobsSlash.norm_adicCompletionEquiv` (`U3/2_PadicEmbedding.lean:132`) generalises
  verbatim (`span_natGenerator`, `Ideal.absNorm_span_singleton`, `Algebra.norm_algebraMap`).
  Attacks: (i) `Fact p.1.Prime` for `p : Nat.Primes` is a *local* instance in mathlib's file —
  re-declared locally in ours (found at skeleton time).  (ii) the `NontriviallyNormedField`
  instance on `v.adicCompletion ℚ` is the project's global one (`FinitePlace.lean`), imported.
* Q1–Q8.  Source: §2.4–2.5 `lwx.txt:687–716` (`K^p`, `Iw_q`, `U_p = Iw_q (p 0;0 1) Iw_q`).
  **Match**: `thetaInt = E⁻¹ ∘ toMatrix ℚ D v`, `thetaK E thetaInt = toMatrix` (Q5), so
  `IntFormsQ` is `IntForms` at the quaternionic data and the QMF side is literally `FormsQ`;
  `η = etaAdelic' ℚ D v p` has `toMatrix η = (p 0; 0 1)` (`toMatrix_etaAdelic'`), hence
  `thetaInt η = (p 0; 0 1) ∈ M₁` with `‖η₀₀‖ = p⁻¹` (Q7–Q8).
  Attacks: (i) *`CharZero (Kp p)`* is not an instance in mathlib for adic completions — proved as
  in `U3/1_Setting.lean:109` (`charZero_of_injective_algebraMap`).  (ii) *`toMatrix_etaAdelic'`
  takes `γ hγ`* (unused dummies) and `Valued.v p ≤ 1` (Q4).
* Q9–Q10 **milestones**.  Source: Prop 2.17 (Q9 = E18 at the quaternionic data) and Def 2.13
  `lwx.txt:876–885`: "The spectral curve Spc≤r D over W≤r is deﬁned to be the (scheme theoretic)
  zero locus of the characteristic power series Char(Up;SD,†,m [−]≤r) inside W≤r× Grig m … The
  composition of x↦→x−1 on Grig m and the natural projection SpcD→ Grig m is called the slope map".
  **Match**: Q10 is `QMF.Weight.evalT_heckeCharPowerSeries_eq_zero_iff` (Fredholm.lean:57) at the
  halo weight, `σ = ρ` (`‖det θη‖ = p⁻¹ ≤ ρ`), rewritten by Q9: at a neat level and a halo point,
  `Char(P)(T₀)(a) = 0 ⇔ a⁻¹` is a `U_p`-eigenvalue on `S^D_{κ_{T₀}}(U)` — the fibre of the
  spectral curve over `T₀`, read through `x ↦ x⁻¹`.
  Attacks: (i) *`hstab` shapes differ*: Q10 takes `stabilizerAtSlash = ⊥` and the QMF criterion
  wants "stabilisers act trivially"; the conversion is the body of
  `bijective_evalAtReps_of_stabilizer_eq_bot` (Compact.lean:368) — 6 lines.  (ii) *the `hshape`
  argument of `ofCerts` is a term* (`isUpShape_certM1 … hv`) so the statement carries no extra
  hypothesis — verified by the build.

## Cross-cutting attacks (each survived)

1. **"Is Prop 2.17 at `m = 1` vacuous on the halo?"**  No: `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹` is the
   annulus `1/2 < v(T₀) < 1`, nonempty for every `p` (e.g. `v(T₀) = 3/4` in a ramified `K`).  It
   does *not* cover the boundary region `v(T₀) ≤ 1/2` where [LWX, §4.2]'s Claim lives (there
   `0 < v(T₀) < 8/((p²−1)t+8) ≤ 1/2`); recorded in `plan.md` as the `m ≥ 2` follow-up.
2. **"Could `heckeCharPowerSeries` at the halo weight fail to be compactoid?"**  QMF's sufficient
   condition `ρ ≤ σ`, `‖det θη‖ ≤ σ < 1` is satisfied with `σ = ρ = ‖T₀‖√p ∈ [p^{−1/2}, 1)`; the
   entrywise route (E16) needs only `‖a‖ ≤ p⁻¹ ≤ ρ`.
3. **"Does the weight normalisation match?"**  QMF acts by `κ(cz+d)/(cz+d)²·f(möb z)`, [LWX] by
   `χ(cz+d)·h(möb z)`; `κ := (·)²·χ` makes `autFactor = χ(cz+d)` (W23–W24); the classical bridge
   `algWeight n : κ(u) = u^{n+2}` uses the same `+2` convention (README §3).
4. **"Is `specialize` really multiplicative on `Λ^{>1/p}`?"**  `f*g` is the convolution with a
   `tsum` over `ℤ` (`coeff_mul`); the double series `∑_{i,j} ψ(f_i)ψ(g_j)T₀^{i+j}` converges
   cofinitely on `ℤ × ℤ` (both tails die: `(p‖T₀‖)^i → 0` as `i → −∞`, `‖T₀‖^i → 0` as `i → ∞`),
   and reindexing gives the convolution — no norm-summability needed.
5. **"Is the identity theorem on `ℕ` (B5) true without assuming `TendstoCoeff` on the closed
   disc?"**  The hypothesis `‖a_j‖ ≤ C q^j`, `q < 1`, gives convergence on a disc of radius `> 1`;
   vanishing at `p^k` for all `k` and the first-nonzero-coefficient argument need only this.
6. **"Are Stirling numbers needed anywhere?"**  No: mathlib's `Stirling.lean` has only the
   recurrences (no Pochhammer link), and the plan avoids them — `mahlerCoeffPow` is defined by
   forward differences, `colmezEquiv` by bijectivity + isometry.
7. **"Does anything here edit a tate-riesz file?"**  No (footprint above); `HaloRing.specialize`,
   `summable_mul_coeff`, `norm_specialize_le` are used as they stand.
8. **LOC**: skeleton 1609 lines with 126 sorries; estimated proofs 60–90 lines for the analytic
   leaves (S5, B7, B9, M8, W13, W20, E13), 10–30 for the rest — comparable to lwx-halo's tranche H.

## Feasibility

Every leaf is either (a) transcribed from [LWX, Prop 2.17 / Prop 3.1 / (2.11.1) / Prop 3.4 /
(2.3.2)] with the quote above, (b) the `m = 1` instance of a fact [LWX] cite ([Colmez, Thm 1.29],
[Bu07, Lemma 12.2], `m`-analyticity of `[−]_m`) with the external reference, or (c) general
infrastructure (diagonal intertwining, block equivalences, the specialization ring hom, the
`p`-adic binomial theorem for an arbitrary exponent, mathlib's comparison isometry at every prime).
No leaf was found false; no leaf needs infrastructure beyond ~300 lines.  The one deliberate
restriction — `m = 1`, sub-annulus `v(T₀) > 1/2` — is a *scope* decision forced by the Tate-algebra
model of the general-weight layer, not a gap in the argument.
