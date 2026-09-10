# Decomposition — `lwx-theta` (the theta layer and the two assemblies)

**BOARD PATH: `.mathlib-quality/lwx-theta/`.**  Never touch the default `.mathlib-quality/` board
or any other board's files.

## Skeleton location and status

- `PhD/LWX/Theta.lean` (10 sorries) — tranche 1, the shared theta layer, now including the
  equivariance (one disc and disc model) and the `U_p` intertwining.
- `PhD/LWX/StepOne.lean` (6 sorries) — tranche 2, the parts of Step I stateable today.
- `PhD/LWX/Degrees.lean` (3 sorries) — tranche 3, Hida's input at the coefficient level.
- `PhD/LWX/ConjChar.lean` (3 sorries) — tranche 1b, the conjugate nebentypus.
- `PhD/TateFredholm/FiniteFactor.lean` (1 sorry) — tranche 1b, the finite factor of a Fredholm
  determinant.
- `PhD/LWX/AtkinLehnerInst.lean` (5 sorries) — the Atkin–Lehner instantiation: `θ` on the block
  model, `U_p`-stability of the classical subspace, the genuine matrices, and H1 named on them.  Both added 2026-09-06; `lake build` clean on both, sorry warnings only.
  `lake build PhD.LWX.Theta` passes with **sorry warnings only, no errors** (verified 2026-09-06).
  The two operators `thetaOne` and `thetaDisc` are **constructed, not sorried**: the boundedness
  and column-finiteness obligations of `TateFredholm.ofCoeffs` are discharged in the definition.

**Scope as of 2026-09-09.**  Six files are skeletoned.  Tranche 1, the seams, the equivariance and
intertwining, the stateable parts of Steps I and III, and the stateable half of the Atkin–Lehner
instantiation are all ticketed.  The remaining gaps are exactly two: **T-AG3** (the Newton polygon
of a product) and **T-AG5** (constructing the Atkin–Lehner conjugation on classical forms,
hypothesis H1a).  Everything still unticketed is downstream of one of those.  Earlier text on this
page describing tranches 2 and 3 as unticketed is superseded by the "skeletoned today" subsections
below.

---

## Jacquet–Langlands audit for this board

Per the standing rule, the per-result audit is `.mathlib-quality/lwx-stepone/JL-AUDIT.md` and is
cited from `plan.md`.  For this board specifically:

- **Nothing in tranche 1 touches Jacquet–Langlands.**  [Bu04, Prop 4]'s first sentence (the kernel
  characterisation) and [LWX, (3.21.1)] (the dimension count) are elementary.
- **Tranche 2 imports only the Jacquet–Langlands-free half of [Bu04, Prop 4]**
  (`bu04.txt:1125–1129`).  Its converse half (`bu04.txt:1122–1124`, which uses "Theorem 4.6.17 of
  [15], the fact that λ is an algebraic integer, and **the Jacquet-Langlands theorem**") is **never
  imported**: we derive the converse from hypothesis H1 plus non-negativity of slopes.  See L2.4.
- **Tranche 3's Hida input is taken at the coefficient level**, which is Jacquet–Langlands-free;
  [LWX]'s own proof of Thm 3.19 is a Newton-polygon argument on the characteristic series.
- The two hypotheses are H1 (Atkin–Lehner; **now available** as
  `LWX.roots_charpoly_atkinLehner`, board `lwx-atkinlehner`, complete) and H2 (right-exactness of
  the theta sequence, [LWX] cites Jones's BGG analogue, `lwx.txt:2049` — **not** a
  Jacquet–Langlands issue; recorded so no worker misfiles it).

---

## Tranche 1 — the shared theta layer (SKELETONED, TICKETED)

### Source proof read

[Bu04, §7], `references/bu04.txt:1050–1070` and `1090–1113`, and [LWX, §3.21], `lwx.txt:1755–1760`.

Buzzard's definition, verbatim (`bu04.txt:1053–1066`):

> "Let `κ = (k, ε_p)` be a classical weight-character, where `k ≥ 1` … Let `κ′` be the character
> `(2 − k, ε_p)`.  We define a map `θ^{1−k} : S^D_κ(U, 1) → S^D_{κ′}(U, 1)` by
> `(θ^{1−k}(f))(g) = (|ν(g)| det(g_p))^{1−k} d^{k−1}f(g)/dz^{k−1}`."

### Plain-English proof

A disc-model element is the family of Taylor coefficients of a function on each disc `a + pʰℤ_p`
in the coordinate `z = a + pʰw`.  Differentiating `r` times in `w` multiplies the degree-`j`
coefficient of the shifted array by `(j+1)(j+2)⋯(j+r)`; these are integers, so the operator is
bounded by `1`, and each column meets only one row, so it is column-finite.  It therefore exists as
a continuous linear map, and since differentiation does not mix discs it is block-diagonal.  Its
`(k+1)`-st power kills exactly the arrays supported in degrees `≤ k`, because in characteristic
zero the multiplier `(j+1)⋯(j+k+1)` never vanishes; those arrays are the locally polynomial
functions of degree `≤ k`, which is Buzzard's classical subspace.  Counting a basis gives
`(k+1)` coefficients per disc and `p^h` discs.

### Leaves

- **L1.1** (leaf, project + mathlib): `LWX.thetaOne` — `Theta.lean:67`
  - Statement: `def thetaOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K)`, built by `ofCoeffs` with matrix
    `if i = j + r then descFactorial (j+r) r else 0`.
  - Source: [Bu04, §7], `bu04.txt:1064` (verbatim above) — the `d^{k−1}/dz^{k−1}`.
  - Lean ↔ source match: Buzzard's map is the `(k−1)`-st derivative twisted by a determinant
    factor.  `thetaOne` is exactly the derivative half read on Taylor coefficients; the determinant
    twist is AG1's business and is deliberately not baked in.
  - Discharged by: `TateFredholm.ofCoeffs` (`GenFun.lean:178`, verified),
    `IsUltrametricDist.norm_natCast_le_one`.  **Already proved** — the definition compiles with
    both obligations discharged.
  - Attacks attempted:
    - [1] Counterexample: the obligations are `‖·‖ ≤ 1` on integer casts (true in any ultrametric
      field) and column-finiteness (each column meets one row).  Neither can fail.  Confirmed by
      the definition compiling.
    - [2] Edge cases: `r = 0` gives the identity matrix (`descFactorial j 0 = 1`); `r` large gives
      a far shift, still column-finite.  Both fine.
    - [3] Hypothesis test: `CharZero K` is **not** used by the construction (only by L1.4), so it is
      not smuggled in here; `IsUltrametricDist` is genuinely needed for the norm bound.
    - Verdict: SURVIVED; leaf is already discharged.

- **L1.2** (leaf, project): `LWX.thetaDisc` — `Theta.lean:91`
  - Statement: `blockMap (σ := ZMod (p ^ h)) (thetaOne K r)`.
  - Source: same passage; the disc decomposition is [LWX, §2.16] / `DiscModel.lean`'s model.
  - Lean ↔ source match: differentiation is local to each disc, so the disc-model operator is
    block-diagonal with the single-disc operator in each block.
  - Discharged by: `TateFredholm.blockMap` (`BlockMap.lean:41`, verified) + L1.1.  **Already
    proved.**
  - Attacks attempted:
    - [1] Counterexample: block-diagonality would fail only if `d/dw` moved mass between discs; it
      does not, since each disc has its own coordinate.
    - [2] Edge cases: `h = 0` (one disc) — `blockMap` over a one-element index is the fibre map ✓.
    - [3] Hypothesis test: `blockMap` needs `Fintype σ`/`DecidableEq σ`, both automatic for
      `ZMod (p^h)` with `p` prime.  No hidden assumption.
    - Verdict: SURVIVED; leaf already discharged.

- **L1.3** (leaf, project): `LWX.thetaDisc_apply` — `Theta.lean:95`
  - Statement: `thetaDisc p K h r c (a, j) = descFactorial (j+r) r * c (a, j+r)`.
  - Source: the coefficient form of `bu04.txt:1064`'s derivative.
  - Lean ↔ source match: this *is* "differentiate `r` times", written on coefficients.
  - Discharged by: `matrixCoeff_thetaOne` (this file, already proved) + `blockMap`'s apply lemmas
    + `ofCoeffs_apply` (`GenFun.lean:186`, verified) — the `tsum` collapses to one term.
  - Attacks attempted:
    - [1] Counterexample: none; it is the definition unfolded.  The only risk is an off-by-one in
      the shift, checked against `matrixCoeff_thetaOne`'s `i = j + r`.
    - [2] Edge cases: `r = 0` gives `c (a, j)` ✓ (consistent with L1.4); `j = 0`, `r = 1` gives
      `1 · c (a, 1)` ✓.
    - [3] Hypothesis test: no hypotheses beyond the section's.
    - Verdict: SURVIVED.

- **L1.4** (leaf, mathlib): `LWX.thetaDisc_zero` — `Theta.lean:100`
  - Statement: `thetaDisc p K h 0 = ContinuousLinearMap.id K _`.
  - Source: none needed (`θ^0 = id`); it is the API lemma the `def` requires per the no-one-off
    rule.
  - Discharged by: L1.3 + `Nat.descFactorial_zero` + `ContinuousLinearMap.ext`.
  - Attacks attempted: [1] none possible; [2] checked at `h = 0` and general `h`; [3] no
    hypotheses.  SURVIVED.

- **L1.5** (leaf, mathlib): `LWX.locPolyDegSubmodule` — `Theta.lean:114`
  - Statement: the submodule of arrays with `∀ a j, k < j → c (a,j) = 0`.
  - Source: [Bu04, Prop 4] proof, `bu04.txt:1113–1115` (verbatim):
    > "The kernel of `θ^{1−k}` is the functions `f ∈ S^D_κ(U;1)` whose image is contained within
    > the space of polynomials of degree at most `k − 2`, which is precisely the space of classical
    > forms `L(U, L_{k,ε_p}) = S^D_k(U₀ ∩ U₁(pⁿ))(ε_p)`."
  - Lean ↔ source match: "polynomials of degree at most `k − 2`" in Buzzard's weight indexing is
    "degree `≤ k`" in [LWX]'s (his `k` is our `k + 2`); on the disc model that is exactly vanishing
    of the Taylor coefficients above degree `k`.
  - Discharged by: the three submodule obligations are pointwise and immediate
    (`add_apply`, `zero_apply`, `smul_apply` on `c(·,·)`).
  - Attacks attempted:
    - [1] Counterexample search: a submodule fails only if the condition is not closed under `+`
      and `•`; "coefficient vanishes" is.
    - [2] Edge cases: `k = 0` gives the locally constant functions ✓ (weight-2 classical forms,
      matching [LWX]'s `k = 0`).
    - [3] Hypothesis test: no `CharZero` needed here (only in L1.6).
    - Verdict: SURVIVED.

- **L1.6** (leaf, mathlib): `LWX.thetaDisc_eq_zero_iff` — `Theta.lean:126`
  - Statement: `thetaDisc p K h (k+1) c = 0 ↔ IsLocPolyDeg p K h k c`.
  - Source: the same verbatim passage as L1.5 (`bu04.txt:1113–1115`) — this **is** [Bu04, Prop 4]'s
    first sentence.
  - Lean ↔ source match: exactly the quoted "the kernel of `θ^{1−k}` is … the classical forms",
    transported to the disc model where "classical" is `IsLocPolyDeg`.
  - Discharged by: L1.3 + `Nat.descFactorial_pos` + `Nat.cast_ne_zero` (needs `CharZero K`) +
    `mul_eq_zero`.
  - Attacks attempted:
    - [1] Counterexample search: the `←` direction is immediate; the `→` direction needs
      `descFactorial (j+k+1) (k+1) ≠ 0` **in `K`**.  Over `ℤ/p` this would be false when
      `p ≤ k+1`, which is exactly the failure mode to look for.  `CharZero K` rules it out, and
      `K` is a characteristic-zero field throughout the LWX layer.  **This attack is the reason
      `CharZero K` is load-bearing and is recorded as such.**
    - [2] Edge cases: `k = 0` gives `θ¹ c = 0 ↔ c` constant on each disc ✓; `j` at the boundary
      `j = k` (not required to vanish) and `j = k+1` (required) both check out against L1.3.
    - [3] Hypothesis test: dropping `CharZero K` breaks the `→` direction as above — necessary,
      not over-specified.
    - Verdict: SURVIVED, with `CharZero K` confirmed necessary.

- **L1.7** (leaf, mathlib): `LWX.finrank_locPolyDegSubmodule` — `Theta.lean:132`
  - Statement: `Module.finrank K (locPolyDegSubmodule p K h k) = (k + 1) * p ^ h`.
  - Source: [LWX, §3.21], `lwx.txt:1755–1760` (verbatim):
    > "Let `m ∈ ℕ_{≥2}`, and let `ψ` be a finite character of conductor `pᵐ`.  For `k ∈ ℤ_{≥0}`,
    > using an isomorphism analogous to (2.11.1), we see that `S^D_{k+2}(K^pIw_{pᵐ};ψ)` is
    > isomorphic to the direct sum of `t` copies of `LP_{m−v(q),deg≤k}(ℤ_p;E)`.  So in total,
    > (3.21.1) `dim S^D_{k+2}(K^pIw_{pᵐ};ψ) = (k + 1)q⁻¹pᵐt`."
  - Lean ↔ source match: the source's `LP_{m−v(q),deg≤k}(ℤ_p;E)` is precisely our
    `locPolyDegSubmodule` at `h = m − 1` (odd `p`, `v(q) = 1`), and its dimension is
    `(k+1)·p^h = (k+1)q⁻¹pᵐ`.  The factor `t` (the class number) is supplied by the block index
    `ι` when this is assembled over `DiscForms`; this leaf is deliberately the **local** half, so
    that the `t` bookkeeping happens once, in tranche 2.
  - Discharged by: a `Finsupp`/`Pi` basis on `ZMod (p^h) × Fin (k+1)`; `Module.finrank_pi`,
    `Fintype.card_prod`, `ZMod.card`.
  - Attacks attempted:
    - [1] Counterexample search: the count is `#discs × #degrees`; the only way to be wrong is an
      off-by-one in `k+1` (degrees `0..k`).  Checked: `IsLocPolyDeg` requires vanishing for
      `k < j`, so degrees `0,…,k` survive — that is `k+1` ✓, matching the source's `(k+1)`.
    - [2] Edge cases: `k = 0`, `h = 0` gives `1` ✓ (constants on one disc); `h = 0` general `k`
      gives `k+1` ✓.
    - [3] Hypothesis test: needs `p` prime only through `ZMod.card`/`Fintype`; no `CharZero`.
    - [4] Source-drift: the source states the *global* dimension `(k+1)q⁻¹pᵐt`; the Lean statement
      is the local factor.  This is a deliberate, documented split, not drift — the `t` appears in
      tranche 2's assembly.  Recorded so a reviewer does not read the leaf as claiming (3.21.1).
    - Verdict: SURVIVED, with the local/global split documented.

### API gaps in tranche 1 (ticketed; block everything downstream)

- **AG1**: the weight equivariance of `θ`.
  - Needed by: AG2, and everything in tranches 2 and 3.
  - Status: **designed 2026-09-06; skeletoned** as `LWX.thetaOne_comp_kappaSlash`
    (`Theta.lean:159`, one disc) and `LWX.thetaDisc_comp_discSlash` (`Theta.lean:178`, disc model).
  - Statement (one disc, verbatim from skeleton):
    ```lean
    theorem thetaOne_comp_kappaSlash (κ κ' : AnalyticWeight UK S ρ) (r : ℕ) (ν : UK →* Kˣ)
        (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1) * ν u)
        (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)) * ν u)
        (g : S) :
        (thetaOne K r).comp (κ.kappaSlash g)
          = ((g : Matrix (Fin 2) (Fin 2) K).det ^ r) •
            ((κ'.kappaSlash g).comp (thetaOne K r))
    ```
  - Lean ↔ source match: `kappaSlash` acts by `f ↦ κ(cz+d)(cz+d)⁻² f((az+b)/(cz+d))`
    (`QMF/Weight/Char.lean:808`), so a weight `x^m·ν` acts through exponent `m − 2`.  Matching the
    source's `(cz+d)^{k−2}` with its `(k−1)`-st derivative forces `m − 2 = r − 1`, i.e. `κ` of
    weight `r + 1` and `κ'` of weight `1 − r` against a common finite part `ν` — hence `hκ`, `hκ'`.
    The `(ad − bc)^{k−1}` is `det g ^ r`.
  - Attacks attempted:
    - [3] Hypothesis-strength — **attack succeeded on the first draft.**  A bare shift relation
      `κ' = κ·x^{−2r}` is *not* enough: at `r = 1` with weight `m`, differentiating once leaves a
      term `(m−2)c(cz+d)^{m−3}f` that vanishes only for `m = 2 = r + 1`.  So `κ` must be classical
      of weight exactly `r + 1`.  The statement was strengthened to `hκ`/`hκ'` before ticketing.
    - [4] Source-drift — **attack succeeded on the second draft.**  The determinant factor had been
      placed on the wrong side.  [Bu04, Prop 4]'s proof (`bu04.txt:1125–1127`) says `θ f` has
      eigenvalue `λ/p^{k−1}`, *divided*, which forces `θ ∘ U_p = p^r • (U_p ∘ θ)`; confirmed by the
      `r = 1`, weight-`2` computation `d/dz[f(möb z)] = (ad−bc)(cz+d)⁻² f'(möb z)`.  The three
      statements were re-oriented; the ticket records the check so a worker does not re-derive it.
    - [2] Edge cases: `r = 0` — both sides are `κ.kappaSlash g` and `hκ = hκ'` (weight `1`),
      consistent with `thetaDisc_zero` ✓.
    - Verdict: SURVIVED after two corrections, both recorded.
  - Source: [Bu04, §7], `bu04.txt:1074–1090` (verbatim):
    > "One has to verify that the map `θ^{1−k}` is well-defined, which boils down to checking that
    > for `(a b; c d) ∈ M_α` and `F` a power series in `z`, we have the identity
    > `(d^{k−1}/dz^{k−1})((cz + d)^{k−2}F((az + b)/(cz + d))) =
    > (ad − bc)^{k−1}(cz + d)^{−k}(d^{k−1}F/dz^{k−1})((az + b)/(cz + d))`.
    > This identity is trivial for `k = 1` and the general case is easily established by induction
    > on `k`."
  - Sub-decomposition (from the source's own words): (i) the `k = 1` base case; (ii) the induction
    step; (iii) transport to the disc model along `DiscModel.discEval_discSlash`, which is already
    proved and states that the disc action is [LWX, (2.3.2)] pointwise.  The source proves the
    identity "by induction on `k`" in ~6 lines; expect a proportionate Lean development plus the
    disc-model transport.

- **AG2**: the `U_p` intertwining `[UηU] θ^{1−k} = |ν(η)|^{k−1} θ^{1−k} [UηU]`.
  - Needed by: both halves of classicality (tranche 2), and the theta sequence (tranche 3).
  - Status: **designed 2026-09-06; skeletoned** as `LWX.thetaDisc_comp_discHeckeBlock`
    (`Theta.lean:196`), with the uniform certificate determinant carried as a hypothesis `hdet` so
    the lemma covers any Hecke element and `U_p` (`η = diag(1,p)`, `cst = ψ p`) is the instance.
    Orientation as AG1: `θ ∘ U_p = cst^r • (U_p' ∘ θ)`.
  - Attacks attempted: [3] carrying `hdet` as a hypothesis rather than deriving it keeps the lemma
    reusable and puts the (easy) determinant computation in the instantiation — not over-specified;
    [2] a block with no summand (`idx i t ≠ j` for all `t`) gives `0 = cst^r • 0` ✓; [4] matches
    `bu04.txt:1095–1100` termwise.  SURVIVED.
  - Source: [Bu04, §7], `bu04.txt:1095–1100` (verbatim):
    > "Next one can analyse the relationship between `θ^{1−k}` and Hecke operators.  Again it is
    > elementary to check that if `f ∈ S^D_κ(U, 1)` and `η ∈ D^×_f` with `η_p ∈ M_α`, then
    > `(θ^{1−k}f)|η = |ν(η)|^{k−1}θ^{1−k}(f|η)` and hence that
    > `[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`."
  - Sub-decomposition: the per-coset statement `(θf)|η = |ν(η)|^{k−1}θ(f|η)` from AG1, then sum
    over the coset decomposition of `[UηU]` (which `DiscForms.discEvalAtReps_discHeckeOperator`
    already provides).  The source calls this "elementary" given AG1 — one paragraph.

---

## Tranche 1b — the three connecting seams (added 2026-09-06)

These were surfaced when the board was reviewed against what Step I actually consumes.  Two of the
three turned out to be **independent of the theta layer** and are skeletoned and ticketed; the
third is an API gap.

### Why the first seam is small (a planning correction)

The initial reading was that Step I needs a relation between "the operator datum at `ω`" and "the
datum at `ω⁻¹`".  Re-reading `PhD/LWX/UpMatrix.lean:531–547` shows this is wrong in a helpful
direction: `UpDatum` carries only the coset data (`tgt`, `mat`), and the nebentypus enters at
`UpDatum.matrix D ω` through `entry ω`.  **The same datum serves both characters** — the
`ψ⁻¹`-space is `D` at `ω⁻¹`.  Since every halo result is stated for an arbitrary `ω`, the second
instance of the Corollary 3.18 lower bound costs nothing once `ω⁻¹` exists as a term.  It does not
exist anywhere in the project (grep for any `ω⁻¹` / conjugate-character relation in `PhD/LWX`
returns nothing), so all that is needed is the definition and its API.

- **S1** (leaf, mathlib): `LWX.invChar` — `PhD/LWX/ConjChar.lean:35`
  - Statement: `def invChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : (ZMod p)ˣ →* ℤ_[p]ˣ`, `u ↦ (ω u)⁻¹`.
  - Source: [LWX, §3.23 Step I], `lwx.txt:1826–1830` (verbatim):
    > "On the other hand, for each of `T_{(k,χ)}` and `T_{(k,χ⁻¹)}`, when the x-coordinate is
    > `(k + 1)qt`, the y-coordinate of the lower bound polygon is … `= (k + 1)²qt/2`."
  - Lean ↔ source match: the source applies the lower bound at the character and at its inverse.
    `invChar` is that inverse; the lower bound then instantiates with no further work.
  - Discharged by: `inv_one`, `mul_inv` (target `ℤ_[p]ˣ` is commutative).
  - Attacks attempted:
    - [1] Counterexample: `u ↦ (ω u)⁻¹` fails to be a hom only if the target is non-commutative;
      `ℤ_[p]ˣ` is commutative.  No counterexample.
    - [2] Edge cases: `ω` trivial gives `invChar ω` trivial ✓; `p = 2` where `(ZMod 2)ˣ` is trivial
      ✓ (both sides trivial).
    - [3] Hypothesis test: no `p ≠ 2` and no primality needed for the definition itself; only
      `Fact p.Prime` from the ambient section, matching the file convention.
    - Verdict: SURVIVED.
- **S2** (leaf, mathlib): `LWX.invChar_invChar` — `ConjChar.lean:44`, the involution.  API hygiene
  for S1 (no-one-off-definitions rule).  `inv_inv` + `MonoidHom.ext`.  Attacks: [1] none possible;
  [2] trivial `ω` ✓; [3] no hypotheses.  SURVIVED.

- **S3** (leaf, project): `TateFredholm.charPowerSeries_eq_mul_polynomial` —
  `PhD/TateFredholm/FiniteFactor.lean:46`
  - Statement: for compactoid `u` commuting with an idempotent `pr` whose `u·pr`-range lies in the
    span of a finite `s`, `charPowerSeries u = charPowerSeries (u * (1 − pr)) * G` with
    `G : R[X]`, `G.natDegree ≤ s.card`.
  - Source: [LWX, §3.23 Step I], `lwx.txt:1818–1822` (verbatim):
    > "By Proposition 2.15, one deduces that the set of all `U_p`-slopes on
    > `S^D_{k+2}(K^pIw_{q²};ψ) ⊕ S^D_{k+2}(K^pIw_{q²};ψ⁻¹)` is exactly the set of the first
    > `n_{k+1}` `U_p`-slopes in each of `S^{D,†}_{(k,ψ)}` and `S^{D,†}_{(k,ψ⁻¹)}`."
  - Lean ↔ source match: the source compares the slopes of a finite-dimensional stable piece (the
    classical space) with an initial block of the whole space's slopes.  S3 is the algebraic half
    of that comparison: the determinant genuinely factors, with the classical piece contributing a
    polynomial of the right degree.  The *ordering* half — that this factor supplies the *initial*
    segment — is AG3, deliberately separate.
  - Discharged by: `TateFredholm.charPowerSeries_eq_mul_of_comm` (`RieszColeman.lean:278`,
    verified sorry-free) then `TateFredholm.exists_polynomial_charPowerSeries_of_range_le`
    (`RieszColeman.lean:326`, verified sorry-free).  Two lemmas, at the threshold.
  - Attacks attempted:
    - [1] Counterexample search: the split needs `pr` idempotent **and** commuting; dropping either
      breaks `charPowerSeries_eq_mul_of_comm`'s own hypotheses.  Both are present.
    - [2] Edge cases: `pr = 0` gives `G = 1` and the trivial split ✓; `pr = 1` gives
      `charPowerSeries (u * 0) = 1` on the left factor ✓; `s = ∅` forces `u * pr = 0` ✓.
    - [3] Hypothesis test: `IsTate R` is inherited from `charPowerSeries_eq_mul_of_comm`'s section
      and is genuinely needed there; `IsCompactoid u` is needed for the determinant to exist.
      Nothing over-specified.
    - [5] Discharge attack: both cited lemmas re-read at the named lines; signatures match the use
      (`hx : IsCompactoid x`, `hp : p * p = p`, `hxp : x * p = p * x`; and the `range ≤ span`
      shape).  Composition is 2 lemmas.
    - Verdict: SURVIVED.

### AG3 — the initial-segment half (API gap, NOT ticketed as a proof)

- **AG3**: the Newton polygon of a product, i.e. that the finite factor of S3 contributes the
  *first* `n` slopes.
  - Needed by: tranche 2's `classicalSlopes_eq_initialSegment` (L2.6) and the squeeze (L2.7).
  - Status: **not in mathlib, not in the project.**  A grep over `PhD/NewtonPolygons/` for any
    product or Minkowski-sum lemma on polygons or heights returns nothing.  The building blocks do
    exist: `NewtonPolygons/Height.lean` has `unitSlope (j : ℕ)` (the `j`-th slope) and `heightFun`,
    and `NewtonPolygons/Spec.lean:61` has the `IsNewtonPolygonOf` spec with its `height_le` and
    maximality clauses.
  - Source: [LWX, §3.23 Step I], `lwx.txt:1818–1822` (quoted under S3) — the source treats "the
    first `n_{k+1}` slopes" as evident once the classical slopes are known; the formal content is
    that the slope multiset of a product is the union of the two slope multisets.
  - Sub-decomposition: (i) the slope multiset of `F * G` is the multiset union of those of `F` and
    `G`; (ii) hence if every slope of the degree-`n` factor is at most every slope of the other,
    the polygon's height at `n` is the sum of the finite factor's slopes.  (ii) follows from (i)
    plus sorting; (i) is the real content.
  - **No Lean statement is pre-written**, because the right phrasing depends on whether to work
    with `unitSlope` as a sequence or to introduce a slope multiset; that choice is step 1 of the
    ticket.  As with T-AG1 and T-AG2, this means `/beastmode` will refuse the ticket until the
    statement lands — flagged deliberately, not an oversight.

### AG4 — instantiating the Atkin–Lehner reduction at the classical space (API gap)

- **AG4** — **expanded 2026-09-09**; see "The Atkin–Lehner instantiation" section below.  The
  original entry follows for the record.
- **AG4 (original)**: supply the abstract data of `LWX.roots_charpoly_atkinLehner` at the genuine classical
  space.
  - Needed by: tranche 2's L2.4 (the converse half of classicality) and L2.7 (the squeeze).
  - Status: **not in the project.**  Board one proved the reduction for abstract matrices and
    recorded in `PhD/LWX/AtkinLehner.lean`'s module docstring that instantiating it "at the genuine
    classical space … is out of scope for this board" because that space did not exist in Lean.
    It will exist once tranche 1 and AG2 land.
  - What it needs: the classical subspace as a finite-dimensional space with a matrix for `U_p`
    (from `locPolyDegSubmodule` + `finrank_locPolyDegSubmodule` + AG2's stability), the same at
    `invChar ω` (S1), and the conjugating pair `(P, Q)` from the Atkin–Lehner element of
    `PhD/LWX/AtkinLehner.lean` acting on forms.
  - Depends on: T-AG1, T-AG2, S1, T007.  Downstream of everything else on this board.

---

## The Atkin–Lehner instantiation (`PhD/LWX/AtkinLehnerInst.lean`, skeletoned 2026-09-09)

### The finding that reshaped AG4

The Atkin–Lehner element `w = (0, 1; −p^m, 0)` **cannot act through the disc model**.  Verified:
`M1 p` requires `‖g 1 1‖ = 1` (`IntegralModel.lean:226–228`) and `w` has `g 1 1 = 0`, so `w ∉ M1`
and every weight/Hecke operator (`DiscForms.lean:179,202,262`, all requiring `η ∈ levelM1`) is
undefined at it; and `w` acts by `z ↦ 1/(−p^m z)`, which does not preserve `ℤ_p`.  So "instantiate
the reduction" splits: pinning the genuine matrices and discharging H1 to the pairing is
stateable now (leaves below); *building* the conjugation is H1a, a genuine gap (T-AG5), realisable
only on the finite-dimensional classical subspace via the `Sym^k` action.

### Leaves

- **AL0a/AL1** `thetaBlock` (`AtkinLehnerInst.lean:72`, done) and
  `thetaBlock_eq_zero_iff` (`:77`).  Source `bu04.txt:1113–1115` as
  L1.6, with the class-set index.  Discharged by T006 blockwise.  Attacks: [3] `CharZero` inherited
  and load-bearing (L1.6); [2] one-element `ι` reduces to L1.6 exactly ✓.  SURVIVED.
- **AL2** `thetaBlock_comp_discHeckeBlockOp` (`:88`).  Source
  `bu04.txt:1095–1100`.  Discharged by T-AG2 blockwise.  Attacks: [4] orientation is the corrected
  `θ ∘ U_p = cst^r • (U_p' ∘ θ)` ✓; [2] an empty block gives `0 = cst^r • 0` ✓.  SURVIVED.
- **AL3** `mem_locPolyDegSubmoduleBlock_discHeckeBlockOp` (`:104`)
  — `U_p`-stability of the classical subspace.  Source: the same Hecke relation; the kernel of an
  intertwiner is stable.  Discharged by AL1 + AL2 + `map_zero`.  Attacks: [3] the hypotheses name
  `κ'` although the conclusion does not — **not** over-specified, the proof goes through the
  target weight; recorded because it looks like slack.  [1] a counterexample would be a classical
  `f` with `U_p f` non-classical, i.e. `θ(U_p f) ≠ 0` while `θ f = 0`, contradicting AL2.
  SURVIVED.
- **AL4** `finite_locPolyDegSubmoduleBlock` (`:122`).  Source
  `lwx.txt:1755–1760`.  Discharged by `Module.finite_of_finrank_pos` (`Dimension/Free.lean:248`,
  verified) + SO4.  Attacks: [3] `[Nonempty ι]` is **slack** (the empty case is trivially finite);
  kept for the `finrank_pos` route and because the class set is nonempty in every use — recorded,
  not hidden.  SURVIVED with slack noted.
- **AL0b** `upMatrix` (`:130`, done): `LinearMap.toMatrix` in
  `Module.finBasisOfFinrankEq` (`Dimension/Free.lean:298`, verified) from SO4, of `T.restrict hT`.
  Attacks: [5] the `Module.Finite` instance comes from AL4, so the def depends on `sorryAx` until
  AL4 and SO4 are proved — acceptable in a skeleton, flagged in the ticket.
- **AL0c** `AtkinLehnerHypothesis` (`:145`, done): `A B = ψ p^{k+1} • 1 ∧
  ∃ P Q, Q P = 1 ∧ A' = P B Q`.  Source `lwx.txt:1763–1768`; the `∃ P Q` is the source's
  "twist … by a central Hecke character associated to `ψ⁻¹`" (`lwx.txt:1783–1786`).
  Attacks: [4] this is exactly `H1a ∧ H1b` as `JL-AUDIT.md` §1 decomposes H1 — no drift; [3] the
  operator identity is stated as an equality of matrices in the *chosen basis*, which is
  basis-independent content since both sides are conjugation-invariant.  SURVIVED.
- **AL5** `roots_charpoly_of_atkinLehnerHypothesis` (`:155`).
  Discharged by `LWX.roots_charpoly_atkinLehner` (`AtkinLehner.lean:182`, sorry-free) +
  `pow_ne_zero` + `RingHom.injective`.  Three lemmas.  Attacks: [3] `IsAlgClosed K` needed for
  roots with multiplicity, as board one; `ψ p ≠ 0` from injectivity, not an extra hypothesis.
  SURVIVED.

### T-AG5 — H1a, the conjugation (API gap, not ticketed as a proof)

Needed by everything that uses `AtkinLehnerHypothesis` non-vacuously.  Status: not in mathlib, not
in the project; **cannot be obtained by restricting an overconvergent action** (obstructions
above).  Route: the `Sym^k` action of `w` on the classical subspace — twisted polynomial reversal
on each fibre plus the class-set permutation — then verify nebentypus inversion, `U_p ↦ U'_p`, and
level normalisation using board one's three matrix identities.  Source `lwx.txt:1783–1786`.
Recommended as its own board.

## Tranche 2 — Step I (decomposed; the stateable part ticketed)

### Source proof read

[LWX, §3.23 Step I], `lwx.txt:1807–1846`, and [Bu04, Prop 4], `bu04.txt:1105–1129`.

### Plain-English proof

Buzzard's small-slope half: if `f` is a `U_p`-eigenvector with `v(λ) < k+1`, then `θ^{k+1}f` is an
eigenvector with eigenvalue `λ/p^{k+1}`, of negative valuation; since `U_p` has operator norm at
most one that forces `θ^{k+1}f = 0`, so `f` is classical.  The converse half we do **not** import
from Buzzard: hypothesis H1 gives the slope symmetry `α_i(ψ) = k+1 − α_{n−1−i}(ψ⁻¹)`, and slopes
are non-negative because `U_p` has norm at most one, so every classical slope is at most `k+1`.
Together with the dimension count these identify the classical slopes with the first `n_{k+1}`
overconvergent slopes.  Step I then squeezes: the Corollary 3.18 lower bound applies to both `ψ`
and `ψ⁻¹`, H1 pins the total, so both inequalities are equalities — which is the touching.

### Leaves (specified; skeleton deferred)

- **L2.1** `norm_discHeckeBlockOp_le_one` — `U_p` has operator norm at most one.
  Source (`bu04.txt:1128`): > "`U_p` is an operator with norm at most 1".
  Likely already derivable from `DiscForms.isCompactoid_discHeckeBlockOp` plus the integrality of
  the certificate matrices; to be confirmed when skeletoned.
- **L2.2** `slope_nonneg` — every slope is non-negative.  Immediate from L2.1.
- **L2.3** `classical_of_slope_lt` — the small-slope half.  Source (`bu04.txt:1125–1129`, quoted in
  full in `../lwx-stepone/JL-AUDIT.md`).  Needs AG2 + L2.1 + L1.6.
- **L2.4** `slope_le_of_classical` — the converse half, **derived from H1**, not imported.
  From `LWX.roots_charpoly_atkinLehner` (multiset form) plus L2.2.
- **L2.5** `finrank_classical_eq` — the global (3.21.1) with the class-number factor `t`, from L1.7.
- **L2.6** `classicalSlopes_eq_initialSegment` — classical slopes are the first `n_{k+1}`.
  Composition of L2.3, L2.4, L2.5.
- **L2.7** `height_eq_at_touchX` — the squeeze, using the completed halo lower bound and H1.
- **L2.8** `IsStepOneTouching` (**named definition**, per the plan) — Step I's conclusion, so that
  tranche 3 consumes it as a statement rather than as a project.
- **L2.9** `hasUnitBand_of_stepOne` — discharges `HasUnitBand` in `PhD/LWX/Vertices.lean:69` via
  the existing bridge `hasUnitBand_of_height_eq` (`Vertices.lean:769`, verified sorry-free).

### Tranche 2 leaves skeletoned today (`PhD/LWX/StepOne.lean`)

- **L2.8** (def, done): `LWX.IsStepOneTouching` — `StepOne.lean:48`.  The exact hypothesis of
  `hasUnitBand_of_height_eq`, named.  Source `lwx.txt:1807–1811` (Step I's first sentence, quoted
  above).  Attacks: [4] it is that hypothesis verbatim, so no drift is possible; [2] `k = 0` is
  `hasUnitBand_zero`'s case ✓.  SURVIVED.
- **L2.9** (leaf, project): `LWX.hasUnitBand_of_isStepOneTouching` — `StepOne.lean:57`.
  Discharged by `hasUnitBand_of_height_eq` (`Vertices.lean:769`, verified sorry-free), one line.
  Attacks: [5] signature matches argument-for-argument; [3] no hypothesis beyond the bridge's.
  SURVIVED.
- **L2.3-abstract** (leaf, mathlib): `LWX.eq_zero_of_intertwine_of_norm_lt` — `StepOne.lean:70`.
  Source `bu04.txt:1125–1129` (quoted verbatim in the ticket).  Lean ↔ source: the source's
  argument with `θ`, `U_p`, `p^{k−1}` abstracted to `θ`, `P`, `c`, in the corrected orientation.
  Discharged by `ContinuousLinearMap.le_opNorm`, `norm_smul`, `norm_eq_zero`.
  Attacks: [3] `hc : c ≠ 0` is needed to divide; `‖c‖ < ‖μ‖` is exactly "negative valuation"; `μ`
  itself may be `0` only if `c` is, so no missing case; [2] `θ = 0` trivially satisfies the
  conclusion ✓; [1] a counterexample would be an operator of norm `≤ 1` with an eigenvalue of norm
  `> 1`, impossible.  SURVIVED.
- **L2.5** (leaf, mathlib): `LWX.locPolyDegSubmoduleBlock`, `LWX.finrank_locPolyDegSubmoduleBlock`
  — `StepOne.lean:81`, `:89`.  The global [LWX, (3.21.1)], source `lwx.txt:1755–1760`.
  Attacks as L1.5/L1.7 with the extra index; [4] this one *is* the source's global formula, with
  `t = card ι`.  SURVIVED.

Still deferred (downstream of T-AG3/T-AG4): L2.1 (`‖U_p‖ ≤ 1`, likely from
`isCompactoid_discHeckeBlockOp` + integrality), L2.2, L2.4, L2.6, L2.7, and the concrete
`classical_of_slope_lt` (= L2.3-abstract applied to AG2).

## Tranche 3 — Step III (decomposed; the Hida input skeletoned today)

Source: [LWX, §3.23 Step III], `lwx.txt:2014–2088`.  Inputs: tranche 2's `IsStepOneTouching`, the
already-complete Step II (`lwx-slopes` board), the coefficient-level Hida statement, and H2.

- **L3.1** (def + API, skeletoned): `LWX.ordDim` (`Degrees.lean:41`, done),
  `bddAbove_isUnit_charCoeff` (`:46`), `isUnit_charCoeff_ordDim` (`:51`),
  `not_isUnit_charCoeff_of_ordDim_lt` (`:56`).  Source `lwx.txt:1717–1719` (verbatim in the
  tickets): "the maximal index such that `c_d(T)` is a unit … such a `d` must exist by Corollary
  3.18".  Attacks: [2] the set contains `0` (`c₀ = 1`), so `sSup` is attained; [3] boundedness needs
  only the halo bound plus `λ(n) → ∞`, no extra hypothesis; [4] LWX's `ℤ_p⟦T⟧`-unit is our
  `HaloInt`-unit, detected by the constant coefficient (`HaloInt.isUnit_of_isUnit_coeff_zero`).
  SURVIVED.  The **control statement** `ordDim_eq_slopeZeroDim` — that `ordDim` is the slope-zero
  dimension at every character in the disc — is *not* yet skeletoned: its shape needs the
  slope-zero count from the Newton polygon (`FirstBreak.lean`), which is T-AG3's design territory.  This is the coefficient-level content of [LWX, Cor 3.21]; the source's own proof of
  Thm 3.19 (`lwx.txt:1717–1730`) is exactly this Newton-polygon argument, so it should be
  **proved, not hypothesised**.  It sits in the same register as `IsUnitCoeff`
  (`PhD/LWX/Vertices.lean:47`, verified present).
- **L3.2** the theta exact sequence's right-exactness — **hypothesis H2**, cited by [LWX] at
  `lwx.txt:2049` to "[Jo11] O. Jones, *An analogue of the BGG resolution for locally analytic
  principal series*".  Not ticketed.
- **L3.3–L3.5** the degree bookkeeping: the left gap, the right gap, and the two closed formulas
  for `deg X_{k,ω}` and `deg X_{(k,k+1),ω}` (`lwx.txt:2080–2088`).

**Split point.** Once tranche 1 lands and tranche 2 is skeletoned, tranche 3 is file-disjoint from
tranche 2 and can become a third board (`lwx-degrees`) run concurrently, consuming `L2.8` as a
statement.  This is the split the plan anticipated.

---

## Prior-B2 log consultation (Step 4.6)

Read `.mathlib-quality/b2_log.jsonl` and every per-board log — 12 entries total.

- **No match by name**: none of the ten declaration names in the tranche-1 skeleton appears as a
  `lemma_name` in any log.
- **No match by shape**: grep for `theta|classical|locPoly|Hida` across all logs returns 0 hits.
- Verdict: clean of prior B2 history.

## Confidence gate (Step 5)

| # | Condition | Status (tranche 1 only) |
|---|---|---|
| 1 | Every leaf discharged from mathlib / project, or an explicit API gap with a sub-tree | **PASS** — 7 leaves discharged; AG1 and AG2 are explicit gaps with source-quoted sub-decompositions |
| 2 | Lean skeleton compiles | **PASS** — `lake build PhD.LWX.{Theta,StepOne,Degrees,ConjChar} PhD.TateFredholm.FiniteFactor`, sorry warnings only, no build-linter warnings |
| 3 | Verbatim source quote per leaf | **PASS** — L1.1–L1.7 each carry a quote from `bu04.txt` or `lwx.txt`; L1.4 is API hygiene and is marked as needing none |
| 4 | Adversarial pass on every leaf | **PASS** — 3+ categories each; two findings recorded rather than waved through (L1.6's `CharZero` necessity, L1.7's local/global split) |
| 5 | Prior-B2 log checked | **PASS** — 12 entries, no match |
| 6 | Tree mirrors the source's proof structure | **PASS** for tranche 1; AG1/AG2 follow Buzzard's own "verify well-definedness, then the Hecke relation" order.  No LOC estimates are given except where anchored to a source line count (AG1: "~6 lines, by induction on `k`") |
| 7 | Every leaf single-conclusion | **PASS** — no `∧`-chains; `thetaDisc_eq_zero_iff` is an `Iff`, which is one conclusion |

**Gate verdict: PASS for tranche 1 ticket creation.**  Tranches 2 and 3 do **not** pass conditions
2 and 3 yet (no skeleton, and their leaves' statements are not yet writable), and are therefore
deliberately excluded from the ticket board, exactly as the API-gap rule requires.

---

## Tranches 5–7 — Steps I and III on the corrected foundation (added 2026-09-09)

**Skeleton**: `PhD/LWX/Touching.lean` (24 sorries), `PhD/LWX/ClassicalPoint.lean` (14),
`PhD/LWX/StepThree.lean` (16); `lake build` passes with sorry warnings only (verified
2026-09-09).  Every leaf below names its declaration; the Lean statements are in `tickets.md`.

**Prior-B2 consultation** (`b2_log.jsonl`, 5 entries, all the `ν` defect of 2026-09-09): no leaf
below carries a finite part `ν`; the classical shape is stated on `autFactor` with explicit
constants `u`, which is the repair.  Clean.

### Step I — plain-English proof (source: [LWX, §3.23 Step I], `lwx.txt:1807–1846`)

Verbatim (`lwx.txt:1807–1846`): "Step I: The first important observation is that the Newton
polygon of `∑_{n≥0} c_n(T_{χ_k})Xⁿ` touches the lower bound polygon at the points
`P_k := (n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`.  On the one hand, Proposition 3.22 says that the sum of
all `U_p`-slopes on `S^D_{k+2}(K^pIw_{q²};ψ) ⊕ S^D_{k+2}(K^pIw_{q²};ψ⁻¹)` is `(k+1)²qt`.  By
Proposition 2.15, one deduces that the set of all `U_p`-slopes on … is exactly the set of the
first `n_{k+1}` `U_p`-slopes in each of `S^{D,†}_{(k,ψ)}` and `S^{D,†}_{(k,ψ⁻¹)}`.  It follows that
the sum of the first `n_{k+1}` `U_p`-slopes in each … is also `(k+1)²qt`.  On the other hand, for
each of `T_{(k,χ)}` and `T_{(k,χ⁻¹)}`, when the `x`-coordinate is `(k+1)qt`, the `y`-coordinate of
the lower bound polygon is `p/(q(p−1))·λ((k+1)qt) = … = (k+1)²qt/2`. (3.23.1)  This exactly agrees
(!) with half of the sum of the first `n_{k+1}` `U_p`-slopes on each … In particular, we see that
the sum of first `n_{k+1}` `U_p`-slopes on `S^{D,†}_{(k,ψ)}` (resp. `S^{D,†}_{(k,ψ⁻¹)}`) is
`(k+1)²qt/2`.  That is, the Newton polygon … passes through the point
`((k+1)qt, (k+1)²qt/2) = (n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`."

**Our transcription, with one inequality relaxed.**  Write `h_ψ` for the height of the
overconvergent polygon at `n_{k+1}` (= the sum of its first `n_{k+1}` slopes) and `S_ψ` for the sum
of the classical slopes (= `−log‖det A_ψ‖`).  The source proves `h_ψ = S_ψ` (via Prop 2.15) and
then `S_ψ + S_{ψ⁻¹} = 2λv` (Prop 3.22 + (3.23.1)), and concludes with the lower bound.  We prove
only `h_ψ ≤ S_ψ` — the classical slopes are *some* `n_{k+1}` of the overconvergent slopes, and the
first `n_{k+1}` are the smallest — which is the Minkowski bound of the product polygon (T5.1),
and the same squeeze `λv ≤ h_ψ ≤ S_ψ = 2λv − S_{ψ⁻¹} ≤ 2λv − h_{ψ⁻¹} ≤ λv` closes.  **Attack on
the deviation**: could `h_ψ = λv` hold with the classical slopes *not* the first `n_{k+1}`?  No:
`h_ψ = S_ψ` follows a posteriori (`h_ψ ≤ S_ψ` and both sides forced to `λv`), so the first
`n_{k+1}` slopes sum to the classical sum while being pointwise at most any `n_{k+1}` of the
slopes — hence they are the classical slopes with multiplicity; the source's classicality is
recovered, not lost.  SURVIVED.

#### Leaves (tranche 5, `Touching.lean`)

- **T5.1** (leaf, project) `height_mul_le_height_right` — source [Ked07, §2] via `Product.lean`:
  "the Newton polygon of `fg` is the Minkowski sum".  Discharged by `height_mul` + `minkowskiHeight_le 0`.
  Attacks: [2] `n = 0`: both sides `0` ✓; `g = 1`: `height (f)(n) ≤ 0`?? — with `g = 1`,
  `height_g n = 0` for `n = 0` only; for `n > 0` the polygon of `1` is `⊤` beyond `0`, so the
  bound reads `≤ ⊤` ✓ (junk-safe); [3] `hf0`/`hg0` are needed for `height 0 = 0`
  (`height_zero_newtonPolygon₀OfPowerSeries`); entire-ness is needed by `height_mul` (the
  `(1−X)∑Xⁱ = 1` counterexample of `Product.lean`); [5] all cited names verified in `Product.lean`.
  SURVIVED.
- **T5.2** (leaf, project) `height_le_coeffVal` — `IsNewtonPolygonOf.height_le`. Attacks: [4] the
  spec's own field; [2] `coeff n g = 0` gives `⊤` on the right ✓. SURVIVED.
- **T5.3** (leaf, mathlib) `coeff_charpolyRev_card` — `reverse_charpoly`, `coeff_reverse`,
  `charpoly_natDegree_eq_dim`, `det_eq_sign_charpoly_coeff` (all verified). Attacks: [2] `n` empty:
  `charpolyRev = 1`, `card = 0`, `det = 1` ✓; [1] a search for `coeff_charpolyRev` found only
  `coeff_charpolyRev_eq_neg_trace` (coefficient `1`), no contradiction. SURVIVED.
- **T5.4/T5.5** (leaves, project) determinants under H1 — `det_mul_det_of_mul_eq_smul`
  (`CharpolyPairing.lean:57`, verified). Source quote: [LWX, Prop 3.22] `lwx.txt:1766–1768`. Attacks:
  [4] the source's "total sum of slopes is `(k+1)²q⁻¹pᵐt`" is `−log‖det A det A'‖ =
  N(k+1)v(p)` with `N = (k+1)q⁻¹pᵐt` ✓ (`N·(k+1)·v(p)` vs the source's `(k+1)²q⁻¹pᵐt·v(p)`,
  equal); [3] `hc : c ≠ 0` is needed (`det B` could be `0` otherwise). SURVIVED.
- **T5.6–T5.9** (leaves, project) stability of the classical subspace from the shape —
  `autFactor_mul_mobius_pow_eq`/`polySubmodule_stable` (`Algebraic.lean:139,277`, verified) with a
  constant. Source: [LWX, Step I] treats `S^D_{k+2}` as a `U_p`-stable subspace. Attacks: [2]
  `k = 0`: columns are `C u·numX⁰·linX⁰ = C u` for `i = 0`, constants ✓; [3] `u = 0` allowed (the
  zero weight action preserves everything) — no unit hypothesis needed ✓; [4] the previous design
  (AL3) derived stability through the theta target and was *false* for a non-constant `ν`; this
  route uses only the shape at the source weight. SURVIVED.
- **T5.10–T5.15** (leaves, project/mathlib) the finite factor bookkeeping — `truncation`
  (`Matrix.lean:239`), `charCoeff_eq_det_coeff` (`Fredholm.lean:491`), `charPowerSeries_comm`
  (`Fredholm.lean:773`), all verified. Attacks: [2] `k = 0`, `ι` a singleton: `classicalSupport` has
  `p^h` elements ✓ (`card = 1·(1·p^h)`); [5] `charCoeff_eq_det_coeff` wants vanishing *rows* outside
  `S` — that is why the split uses `pr ∘ T` and `charPowerSeries_comm`, not `T ∘ pr`. SURVIVED.
- **T5.16** (internal) `charPowerSeries_eq_mul_of_stable` — composition of T5.12–T5.15 with
  `charPowerSeries_add_of_mul_eq_zero` (`RieszColeman.lean:257`: hypotheses `IsCompactoid v`,
  `IsCompactoid w`, `v * w = 0` — one-sided, verified). **Attack on the composition**: S3's
  `charPowerSeries_eq_mul_polynomial` needs `T` to commute with the projection, which the
  coordinate truncation does NOT (a slash of `z^n`, `n > k`, has low-degree coefficients); the
  one-sided vanishing `T(1−pr)·T pr = 0` holds from stability alone and suffices for the
  determinant identity `(1−TV)(1−TW) = 1−T(V+W)` when `VW = 0`. SURVIVED.
- **T5.17/T5.18** (leaves, mathlib) basis independence — `LinearMap.det_toMatrix`
  (`Determinant.lean:212`), `LinearMap.charpoly_toMatrix` (`ToMatrix.lean:43`), verified; needs
  `locPolyDegBlockEquiv` de-privatised (`StepOne.lean:126`). SURVIVED.
- **T5.19** (internal) `height_le_negLogNorm_det` — composition of T5.1, T5.2, T5.3, T5.16, T5.17.
  Attack on the composition: `coeff N (charpolyRev M) = (−1)^N det M` needs `N = card` of the
  index type `ι × ZMod (p^h) × Fin (k+1)`, which is `card ι·(k+1)·p^h` (T5.11) — the same `N` as the
  height index ✓. SURVIVED.
- **T5.20** (leaf, project) the lower bound — `isBelow_newtonPolygon_specCharSeries`
  (`Halo.lean:210`), `height_ofSlopes` (`OfSlopes.lean:138`), verified. Source: [LWX, Cor 3.18]
  `lwx.txt:1684–1686` (verbatim in the ticket). SURVIVED.
- **T5.21/T5.22** (leaves, project) the arithmetic — `two_mul_lwxLambda_touchX`
  (`UpperPolygon.lean:59`, verified: `2λ(n_k) = k²p(p−1)t`). Source: [LWX, (3.23.1)],
  `lwx.txt:1826–1832`. Attacks: [2] `k = 0`: `2λ(pt) = p(p−1)t` and `N·1·v(p) = pt·v(p)`; with
  `(p−1)v(T₀) = v(p)` both sides are `pt·v(p)` ✓; [3] `hT0 : 0 < ‖T₀‖` is needed for `log`. SURVIVED.
- **T5.23** (internal, **milestone**) `isStepOneTouching_of_atkinLehnerHypothesis` — the squeeze;
  composition of T5.5, T5.19, T5.20, T5.21 through the seam
  `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries` (`SeamH.lean:401`, verified). Attacks on the
  composition: [a] the seam needs level `h` with `‖TH p h T₀‖² < p⁻¹`; at `h = 1` and a classical
  point this is `‖exp(p²k) − 1‖² ≤ p⁻⁴ < p⁻¹` ✓ (C6.9); [b] `v(T₀) = v(T₀')`: both equal
  `v(p)/(p−1)` by `hnorm` ✓; [c] the two weights have different `ρ` (`haloRhoH p 1 T₀` vs `T₀'`) —
  `ClassicalData` carries its own, and `AtkinLehnerHypothesis` only sees matrices ✓; [d] could
  `h_ψ` be `⊤` or `⊥`?  `≤ −log‖det A‖ < ⊤` by T5.19 (det ≠ 0 by T5.4) and `≠ ⊥` by
  `height_natCast_ne_bot` ✓. SURVIVED.
- **T5.24** (leaf, project) `hasUnitBand_of_isStepOneTouching` (`StepOne.lean:58`). SURVIVED.

### Classical points — plain-English (source: [LWX, §3.23], `lwx.txt:1794–1798`)

Verbatim: "We consider the classical weights `χ_k = (k, ψ)` of conductor `q²` with `k ∈ ℤ_{≥0}`,
such that `χ_k|_Δ = ω`.  The corresponding `T`-coordinates `T_{χ_k}` have valuation
`q/ϕ(q²) = p/(q(p−1)) < 1`."  With `q = p`: `T_{χ_k} = χ_k(exp p) − 1 = ζ·exp(pk) − 1`,
`ζ = ψ(exp p)` a primitive `p`-th root of unity, `v(T_{χ_k}) = v(ζ − 1) = 1/(p−1)`.  At level
`h = 1`: `T'_1 = (1+T_{χ_k})^p − 1 = exp(p²k) − 1`, so `s_1 = k` and the halo weight's automorphy
factor is `haloCharFunH(d)·(1 + (c/d)z)^k` — the classical shape with `u = haloCharFunH(d)d^{−k}`.

#### Leaves (tranche 6, `ClassicalPoint.lean`)

- **C6.1–C6.3** (leaves, mathlib) `‖ζ − 1‖ < 1`, `‖1 − ζⁱ‖ = ‖1 − ζ‖`, `‖ζ − 1‖^{p−1} = ‖p‖` —
  `Polynomial.eval_one_cyclotomic_prime` (`Cyclotomic/Eval.lean:33`),
  `cyclotomic_eq_prod_X_sub_primitiveRoots` (`Cyclotomic/Basic.lean:476`), `add_pow`,
  `Nat.Prime.dvd_choose_self` (verified). Attacks: [2] `p = 3`, `ζ` a cube root of unity:
  `(1−ζ)(1−ζ²) = 3`, `‖1−ζ‖² = ‖3‖` ✓; [3] `‖p‖ < 1` is needed (over `ℂ` the claim is false);
  [4] the source's `v(T_{χ_k}) = p/(q(p−1))` at `q = p` is `1/(p−1)` ✓. SURVIVED.
- **C6.4–C6.7** (leaves, project) the halo conditions at the classical point — the `padicExp`
  bounds of `PadicExpLog.lean` (`padicExp_add` at 410 verified; the norm-of-`exp − 1` bound to be
  located by name at execution). Attacks: [2] `k = 0`: `T₀ = ζ − 1` ✓; [3] `p ≠ 2`: for `p = 2`,
  `‖ζ − 1‖ = ‖2‖ = p⁻¹` is *on* the boundary and `inv_lt` fails — `hp2` is necessary, not slack.
  SURVIVED.
- **C6.8–C6.10** (leaves, project) `T'_1`, its norm, and `haloExponentH = k` —
  `padicLog_padicExp` (`PadicExpLog.lean:806`), `IsPrimitiveRoot.pow_eq_one` (verified).
  Attacks: [4] `HaloWeightH.lean:342`: `haloExponentH = log(1 + T'_h)/p^{h+1}`; with
  `1 + T'_1 = exp(p²k)` this is `p²k/p² = k` ✓; [3] the disc condition `‖p²k‖² < ‖p‖` holds for
  every `k` when `p ≠ 2` ✓. SURVIVED.
- **C6.11** (leaf, mathlib) `Ring.choose_natCast` (`Binomial.lean:399`, verified) + `add_pow`.
  SURVIVED.
- **C6.12/C6.13/C6.14** (internal) the shape — `autFactor_haloWeightH` (`HaloWeightH.lean:1097`,
  verified: `C (haloCharFunH … d) * mk (choose s_h m * (c/d)^m)`). Attack on the composition: the
  constant is `haloCharFunH(d)·d^{−k}`, *not* `ψ(d)`; the two agree only after the binomial
  evaluation at `ζ` (gap AG-ζ), which Step I never needs. SURVIVED (with the gap recorded).

### Step III — plain-English proof (source: [LWX, §3.23 Step III], `lwx.txt:2014–2088`)

Verbatim quotes are in the tickets S7.3, S7.11, S7.13, S7.14–S7.16.  Structure: (i) `n⁺_0 =
r_ord(ω)` by Cor 3.21 (`lwx.txt:2018–2020`); (ii) `n_{k+1} − n⁻_{k+1}` = multiplicity of slope
`k+1` on the classical space = (Atkin–Lehner) slope-`0` multiplicity on `S^{D,†}_{(k,ψ⁻¹)}` =
(Cor 3.21) `r_ord(ω⁻¹ω₀^{2k})` (`lwx.txt:2026–2036`); (iii) `n⁺_{k+1} − n_{k+1}` = codimension of
the classical space in the slope-`≤ k+1` part = (exact sequence, **H2**) slope-`0` dimension of
`S^{D,†}_{(−k−2,ψ)}` = (Cor 3.21) `r_ord(ωω₀^{−2k−2})` (`lwx.txt:2047–2070`); (iv) the degree
formulas by arithmetic (`lwx.txt:2080–2088`).

**Our transcription.**  Multiplicities are face lengths: `n⁻_k = faceLeft_F(kϕ(q)v)`,
`n⁺_k = faceRight_F(kϕ(q)v)` (Step II's bands, S7.4/S7.5); `faceRight_F(σ) = faceRight_{G_cl}(σ) +
faceRight_R(σ)` and the same for `faceLeft` (`faceRight_mul`/`faceLeft_mul`, the product theorem —
this is the "Prop 2.15" step: the classical factor and the complement factor); every slope of the
complement is `≥ k+1` (the small-slope argument on the compression, S7.8/S7.9 — [Bu04, Prop 4]'s
Jacquet–Langlands-free half, and the only place theta is used); the classical factor's faces are
root counts (`card_roots_slope`) and Atkin–Lehner reflects them (`norm_roots_charpoly_atkinLehner`,
S7.10/S7.11); `faceRight_F(0) = ordDim` is Cor 3.21 (S7.3, from Step II at `k = 0`,
unconditional); and H2 makes `faceRight_R(σ) = faceRight_{F_target}(0)` (S7.13).

#### Leaves (tranche 7, `StepThree.lean`)

- **S7.1** (API gap AG-Z, three sub-steps) `exists_evalT_eq_zero_of_unitSlope_eq` —
  `exists_isDominantFactorization` (`SlopeFactor.lean:463`), `card_roots_slope`
  (`PolynomialRoots.lean:955`), `unitSlope_mul_of_forall_le` (`Product.lean:1025`), and the
  algebraic-closure transport of `JacobsSlash/5_EigenSlopes.lean:110–122` (all verified). Source:
  blueprint §5.11 + `SlopeFactor.lean`'s slope factorisation. Attacks: [1] the converse
  `norm_eq_exp_slope_of_hasSum_zero` (`PowerSeriesZeros.lean:1290`) is proved, no contradiction;
  [2] `f` a polynomial: `card_roots_slope` directly ✓; [3] `IsAlgClosed K` is needed (over `ℚ_p`
  the root may live in an extension) — the consumers already assume it. SURVIVED; recorded as a
  gap because it is general Newton-polygon theory that belongs in `PowerSeriesZeros.lean`.
- **S7.2** (leaf, project) `rightIndex_zero_eq_ordDim` — `HaloInt.isUnit_of_isUnit_coeff_zero`
  (`TateRiesz.lean`), `lwxLambda_pos` (`Degrees.lean:64`). Source: [LWX, Thm 3.19 proof]
  `lwx.txt:1717–1719` (the "equivalently"). Attacks: [2] `ordDim = 0` (no unit beyond `c₀`): both
  sides `0` ✓; [3] the converse `IsUnit g → IsUnit (g 0)` in `HaloInt` may need a sub-ticket (the
  D1a note anticipated it). SURVIVED.
- **S7.3** (leaf, project) `faceRight_zero_specCharSeries_eq_ordDim` — Step II's band lemmas at
  `k = 0` (`Vertices.lean:982,1000`, verified), `hasUnitBand_zero`. Source: [LWX, Cor 3.21]
  `lwx.txt:1743–1752` and the Thm 3.19 proof `lwx.txt:1717–1730` (verbatim in the ticket).
  Attacks: [4] the source's "slope zero in the first `d` segment" is exactly `faceRight 0 = d` ✓;
  [3] no touching hypothesis: `HasUnitBand … 0` is a theorem ✓. SURVIVED.
- **S7.4/S7.5** (leaves, project) faces from bands — `Vertices.lean:559,982,1000`, verified.
  Source: [LWX, Step II] `lwx.txt:1975–1990`. Attacks: [2] `leftIndex = rightIndex` (a vertex, no
  band): `faceLeft σ = faceRight σ` and the slope `σ` is skipped ✓ consistent. SURVIVED.
- **S7.6** (leaf, project after G1) the intertwining with constants. SURVIVED conditional on G1.
- **S7.7** (leaf, project) `‖U_p‖ ≤ 1` — `norm_eq_iSup_matrixCoeff` (`Matrix.lean:90`),
  `norm_coeff_genFun_le_one` (`Series.lean:320`), `matrixCoeff_sum` (`Fredholm.lean:661`),
  verified. Source: `bu04.txt:1128`. SURVIVED.
- **S7.8** (internal) the small-slope argument on the compression — `eq_zero_of_intertwine_of_norm_lt`
  (`StepOne.lean:76`), `thetaBlock_eq_zero_iff` (`AtkinLehnerInst.lean:86`), verified. Source:
  `bu04.txt:1125–1129` (verbatim in the ticket). **Attack on the composition**: the earlier plan
  (L2.6) needed generalised eigenvectors/multiplicities to pass from "every eigenvector of small
  slope is classical" to "the small slopes are classical slopes"; the compression `U_p ∘ (1 − pr)`
  avoids this — its eigenvectors are killed by `θ` outright, so *every zero* of its determinant has
  large valuation, with no multiplicity bookkeeping. SURVIVED.
- **S7.9** (internal) `le_unitSlope_compl` — S7.1 + S7.8 + `evalT_charPowerSeries_eq_zero_iff`
  (`Riesz.lean:2381`, verified). SURVIVED.
- **S7.10/S7.11** (internal) the classical faces and their reflection —
  `roots_charpoly_atkinLehner`/`norm_roots_charpoly_atkinLehner` (`AtkinLehner.lean:260,277`),
  `roots_charpolyRev` (`CharpolyPairing.lean:157`), `card_roots_lt_slope`/`_le_slope`
  (`PolynomialRoots.lean:869,832`), `IsAlgClosed.card_roots_eq_natDegree`
  (`IsAlgClosed/Basic.lean:110`), verified. Source: `lwx.txt:2026–2036` (verbatim in S7.11).
  Attacks: [4] the source says "multiplicity of slope `k+1` on `S^D(ψ)` = slope-`0` dimension on
  `S^{D,†}(ψ⁻¹)`"; ours is "classical slopes `< k+1` at `ψ` = `N −` slope-`0` classical slopes at
  `ψ⁻¹`", the same statement read on `faceLeft` (`N − faceLeft = #{slope = k+1}` since all
  classical slopes are `≤ k+1` by S7.10) ✓. SURVIVED.
- **S7.12/S7.13** (internal) the two gaps — `faceLeft_mul`/`faceRight_mul`
  (`Product.lean:1203,1156`), the seam, S7.3, S7.5/S7.4, S7.9, S7.11; S7.13 additionally H2 and a
  rescaling lemma (`PowerSeries.rescale`, `Basic.lean:543`, verified). Attacks: [3] H2 is stated
  as `R = rescale (p^{k+1}) F_target` — a *hypothesis*, in the form the source consumes; could the
  source's exact sequence give something weaker (e.g. only divisibility)?  Right-exactness with
  equivariance gives an isomorphism of `U_p`-modules `S^{D,†}/S^D ≅ S^{D,†}_{(−k−2)}` (with `U_p`
  ↦ `p^{k+1}U_p`), whose Fredholm determinants therefore agree — the determinant form is exactly
  what "by the exact sequence" uses ✓; [2] `ordDim ω₁ = 0`: `n⁺_{k+1} = n_{k+1}` ✓ consistent with
  `rightIndex_mem`. SURVIVED.
- **S7.14–S7.16** (leaves/assemblies) the degree formulas — `Nat` arithmetic on S7.2, S7.12, S7.13.
  Source: `lwx.txt:2080–2088` (verbatim in the tickets). Attacks: [3] `Nat` subtraction: all the
  inequalities `leftIndex ≤ touchX ≤ rightIndex` hold under `HasUnitBand` (`leftIndex_mem`,
  `rightIndex_mem`), which T5.24 supplies ✓. SURVIVED.

**Confidence gate.**  Every leaf is discharged from mathlib or project code by verified names, or
is an explicit gap with its sub-decomposition (AG-Z: S7.1's three steps; AG-ζ and AG-ω₀ are design
gaps that no ticket depends on); the skeleton compiles; every leaf carries a source locator and
quote (in the tickets); the tree mirrors the source's chain Prop 3.22 → (Minkowski in place of
Prop 2.15) → (3.23.1) → Cor 3.18 for Step I and Cor 3.21 → Atkin–Lehner → exact sequence → arithmetic
for Step III; no leaf bundles two conclusions.  Gate passes for tranches 5–7.
