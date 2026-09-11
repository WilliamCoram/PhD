# Decomposition — `lwx-degrees` (the degrees at every classical weight, and [LWX, Cor 1.4])

**BOARD PATH: `.mathlib-quality/lwx-degrees/`.**  Companion to `plan.md`; read both before working a
ticket.  Written 2026-09-11 with the adversarial pass.  References by locator: `lwx.txt` =
`.mathlib-quality/tate-riesz/references/lwx.txt`; project code by `File.lean:line`.

## 0. The goal, and what the source says

**Targets**: `degXint_pos_of_atkinLehnerFamily` (**M1**, with `degX_succ_of_atkinLehnerFamily`,
`degXint_of_atkinLehnerFamily`: the degree statements of [LWX, Thm 1.3] at every classical weight,
granted the family of Atkin–Lehner data) and `degXint_add_period` / `degX_succ_add_period` (**M2**:
[LWX, Cor 1.4]).

**Theorem 1.3's degree display** — `lwx.txt:148–155` and `lwx.txt:157–160`:

> "Moreover, if the tame level is neat, and we denote by X_{n,ω} and X_{(n,n+1),ω} the preimages of W^{>1/p}_ω in X_n and X_{(n,n+1)} respectively, then deg X_{n,ω} = { r_ord(ω), if n = 0, r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n}), if n ≥ 1,"
> "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."

**Corollary 1.4** — `lwx.txt:164–169` (stated without proof):

> "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."

**Step III, the computation of the degrees** — `lwx.txt:2014–2022`, `lwx.txt:2025–2047`, `lwx.txt:2048–2078`, `lwx.txt:2079–2097`:

> "Step III: It remains to compute the degrees of X_{I,ω}'s. It is clear that X_{0,ω} coincides with the restriction of X^ord_ω, which is introduced in the proof of Theorem 3.19, to W^{>1/p}_ω. Then by Corollary 3.21, deg X_{0,ω} is equal to the dimension of slope zero subspace in S^{D,†}_ω. That is, deg X_{0,ω} = n⁺_0 = r_ord(ω)."
>
> "For k ≥ 0, first note that n_{k+1} − n⁻_{k+1} is equal to the dimension of slope k + 1 subspace in S^D_{k+2}(K^pIw_{q²}; ψ). By Atkin–Lehner theory (Proposition 3.22) and Proposition 2.15, the multiplicity is the same as the dimension of slope zero subspace in S^{D,†}_{(k,ψ⁻¹)}. Using Corollary 3.21 again, we deduce that n_{k+1} − n⁻_{k+1} = r_ord(ψ⁻¹|_Δ·ω₀^k) = r_ord(ω⁻¹ω₀^{2k}) because ψ⁻¹|_Δ·ω₀^k = χ_k⁻¹|_Δ·ω₀^{2k} = ω⁻¹ω₀^{2k}."
>
> "To compute n⁺_{k+1} − n_{k+1}, we recall the following exact sequence (cf. [Jo11]) 0 → S^D_{k+2}(K^pIw_{q²}, ψ) → S^{D,†}_{(k,ψ)} —(d/dz)^{k+1}→ S^{D,†}_{(−k−2,ψ)} → 0. This exact sequence is equivariant for the U_p-action on the first two spaces, and the p^{k+1}U_p-action on the third space. It is clear that n⁺_{k+1} − n_{k+1} is equal to the codimension of S^D_{k+2}(K^pIw_{q²}, ψ) in the slope ≤ k + 1 subspace in S^{D,†}_{(k,ψ)}. The latter in turn is equal to the dimension of slope zero subspace of S^{D,†}_{(−k−2,ψ)} by the exact sequence. Using Corollary 3.21, we thus obtain n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ·ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})."
>
> "The final degree is computed by deg X_{k,ω} = n⁺_k − n⁻_k = (n⁺_k − n_k) + (n_k − n⁻_k) = { r_ord(ω), if k = 0, r_ord(ω⁻¹ω₀^{2k−2}) + r_ord(ωω₀^{−2k}), if k ≥ 1, and deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = n_{k+1} − n_k − (n_{k+1} − n⁻_{k+1}) − (n⁺_k − n_k) = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k}). This concludes the proof of Theorem 1.3."

**`n⁻_0`, `n⁺_0`** — `lwx.txt:1923–1927`:

> "For a uniform treatment later, we set n⁻_0 = 0 and n⁺_0 the maximal index in [0, t] such that b_{n⁺_0,0} is a p-adic unit."

**`t` and `r_ord`** — `lwx.txt:123–127`:

> "the constant t is equal to the dimension of the space of weight 2 automorphic forms with q-Iwahori level structure at p and tame level as above, and r_ord(ω) denotes the dimension of the ordinary subspace of automorphic forms of weight 2 and character ω."

**`ω₀^{ϕ(q)} = 1`** — `lwx.txt:2357–2360` (in §4.2; the same fact the corollary's periodicity uses):

> "In particular, since ω₀^{ϕ(q)} = ω₀^{q(p−1)/p} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) + ϕ(q)p^M/(2q²)."

## 1. Prose proofs (Step 1)

**R-A (the degrees at every weight, M1).**  Fix the family `F` and the neatness data.  For each weight `(ω, k)`
the family gives `AtkinLehnerData … (nebCharK ψ ω k ζ)` with the same `U_p`-representatives `vRepF F`, hence
H1 at the classical points of `(ω, k)` and its partner `(ω⁻¹ω₀^{2k}, k)` (`atkinLehnerHypothesis_of_atkinLehnerData`),
H2 at those points (`isThetaExact_classicalData`), and so the two gaps of Step III (`lwx.txt:2025–2078`):
`n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})` (D9) and `n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})` (D10), the level-`1`
lemmas `touchX_sub_leftIndex_eq_ordDim`, `rightIndex_sub_touchX_eq_ordDim` applied at `classicalData`,
`targetData_classicalPoint`.  Then (`lwx.txt:2079–2097`): `deg X_{k+1,ω} = n⁺_{k+1} − n⁻_{k+1}` is the sum of
the two gaps (D11, already assembled per weight by `degX_succ_of_atkinLehnerData`); `deg X_{(0,1),ω}` is
`degXint_zero` (D12; `n⁻_0 = 0`, `n⁺_0 = r_ord(ω)`); and `deg X_{(k+1,k+2),ω} = n⁻_{k+2} − n⁺_{k+1} =
(n_{k+2} − n_{k+1}) − (n_{k+2} − n⁻_{k+2}) − (n⁺_{k+1} − n_{k+1}) = pt − r_ord(ω⁻¹ω₀^{2k+2}) − r_ord(ωω₀^{−2k−2})`
(D13: the left gap at `k+2` from the data at weight `k+1`, the right gap at `k+1` from the data at weight `k`,
`n_{k+2} − n_{k+1} = pt`, and `n⁺_{k+1} ≤ n⁻_{k+2}` from the unit bands, `rightIndex_le_leftIndex_succ`, which
makes the subtraction exact).  The two interval cases assemble into the source's uniform formula (D14, with
`ωω₀^{−2n}` spelled `ω * (teichChar p ^ (2 * n))⁻¹`, D3/D4).  Positivity (`lwx.txt:160`, asserted without
proof): `r_ord ≤ t` (`lwx.txt:123–127`; D8 from `le_card_of_isUnit_charCoeff`) and `q = p ≥ 3` give
`qt − r − r' ≥ (q−2)t ≥ t > 0` (D15).

**R-B ([LWX, Cor 1.4], M2).**  The source gives no proof; the expansion: substituting `(n, ω) ↦ (n+1, ωω₀²)`
in Thm 1.3's formulas, `(ωω₀²)⁻¹ω₀^{2(n+1)−2} = ω⁻¹ω₀^{2n−2}` and `ωω₀²·ω₀^{−2(n+1)} = ωω₀^{−2n}` (D5, D6 at
the integers; D5, D7 on the intervals), so `deg X_{n,ω} = deg X_{n+1,ωω₀²}` for `n ≥ 1` (D16; false at `n = 0`,
which the source's list `(0,1), 1, (1,2), 2, …` excludes) and `deg X_{(n,n+1),ω} = deg X_{(n+1,n+2),ωω₀²}` for
`n ≥ 0` (D17).  Iterating `m` times (D18, D19; D1, D2) and taking `m = ϕ(q)/2 = (p−1)/2` with `ω₀^{p−1} = 1`
(`teichChar_pow_sub_one`; `lwx.txt:2357–2358`) gives the periodicity modulo `ϕ(q)/2` (D20, D21).

## 2. The tree (Step 2) and the leaves (Steps 2.5–4.6)

```
M1 degXint_pos_of_atkinLehnerFamily (D15)
  ├─ D14 degXint_of_atkinLehnerFamily
  │    ├─ D12 degXint_zero_of_atkinLehnerFamily   ← degXint_zero @ classicalData (lwx.txt:2089–2097, k = 0)
  │    ├─ D13 degXint_succ_of_atkinLehnerFamily   ← D9, D10, unit bands (lwx.txt:2089–2097)
  │    │    ├─ D9  left gap  ← touchX_sub_leftIndex_eq_ordDim @ classicalData (lwx.txt:2025–2047)
  │    │    └─ D10 right gap ← rightIndex_sub_touchX_eq_ordDim + isThetaExact_classicalData (lwx.txt:2048–2078)
  │    ├─ D3, D4 (character spellings)
  └─ D8 ordDim_le_card  ← le_card_of_isUnit_charCoeff (lwx.txt:123–127)
D11 degX_succ_of_atkinLehnerFamily ← degX_succ_of_atkinLehnerData @ toData (lwx.txt:151–155, 2079–2088)
M2 degXint_add_period (D21), degX_succ_add_period (D20)
  ├─ D19 / D18 iterates ← D17 / D16, D1, D2
  │    ├─ D17 degXint_mul_teichChar_sq ← D14, D5, D7 (lwx.txt:164–166)
  │    └─ D16 degX_succ_mul_teichChar_sq ← D11, D5, D6 (lwx.txt:164–166)
  └─ teichChar_pow_sub_one (project, lwx.txt:2357)
```

All 21 leaves are discharged from project code (sorry-free, standard axioms — `lwx-theta-h2`, `lwx-h1`,
`lwx-conductor` gate records) or mathlib; there is no API gap.  Every internal node's composition is
recorded under its own entry (D13, D14, D16–D21 are the internal nodes; their "composition attack" is
attack [1]).

### Leaves

- **D1** (`mul_teichChar_pow_zero`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:43`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- `ω·ω₀^{2·0} = ω`. -/
    theorem mul_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : ω * teichChar p ^ (2 * 0) = ω := by
      sorry
    ```
  - Source: `lwx.txt:121–122`; `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Let ω₀ : Δ → ℤ_p^× denote the inclusion map."
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: `ω·ω₀^{2·0} = ω` is the `m = 0` case of the `m`-fold shift `ω ↦ ωω₀^{2m}` behind "periodic modulo ϕ(q)/2"; pure group theory in `(ZMod p)ˣ →* ℤ_[p]ˣ`, no source content beyond the definition of `ω₀`.
  - Discharged by: mathlib: `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `pow_zero`, `mul_one` (≤ 3 lemmas after the two unfoldings; all verified by `#check`).
  - Attacks attempted:
    - [1] Counterexample search: `grep -rn 'teichChar p ^ (2 \* 0)'` in `PhD/LWX/` — only the inline `hω` of `slopeRatio_mul_teichChar_pow`, which proves this very identity; nothing contradicting.
    - [2] Edge cases: `p = 3` (`ω₀² = 1`, statement still `ω·1 = ω`), `ω = 1`: `1·ω₀^0 = 1` ✓.
    - [3] Hypothesis test: no hypothesis to weaken; `[Fact p.Prime]` is needed only to state `teichChar`.
    - [4] Source drift: none — a definitional identity.
    - [5] Discharge: `MonoidHom.pow_apply` needs `CommMonoid ℤ_[p]ˣ` ✓; the rewrite chain compiled verbatim in `ConductorSlopes.lean` (R16).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 2 lines; source: none (definitional)

- **D2** (`mul_teichChar_pow_succ`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:47`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- `ω·ω₀^{2(m+1)} = (ω·ω₀^{2m})·ω₀²`. -/
    theorem mul_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m : ℕ) :
        ω * teichChar p ^ (2 * (m + 1)) = ω * teichChar p ^ (2 * m) * teichChar p ^ 2 := by
      sorry
    ```
  - Source: `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: `ωω₀^{2(m+1)} = (ωω₀^{2m})·ω₀²`: the `(m+1)`-fold shift is the `m`-fold shift followed by one more `ω ↦ ωω₀²` — the step of the iteration that turns the corollary's one-step identity into periodicity.
  - Discharged by: mathlib: the listed lemmas, pointwise in `ℤ_[p]ˣ` (compiled verbatim on `lwx-conductor`).
  - Attacks attempted:
    - [1] Counterexample search: at `r`, `a·τ^{2m+2}` vs `a·τ^{2m}·τ²` — equal; no contradicting project statement (`grep teichChar p \^ (2 \*`).
    - [2] Edge cases: `m = 0`: `ωω₀² = ω·ω₀⁰·ω₀²` ✓ (with D1); `p = 3` ✓.
    - [3] Hypothesis test: nothing to weaken.
    - [4] Source drift: none (definitional).
    - [5] Discharge: the exact `rw` chain is in the tree, sorry-free (`ConductorSlopes.lean`, `slopeRatio_mul_teichChar_pow`).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 3 lines; source: none

- **D3** (`mul_inv_teichChar_pow_zero`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:52`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- `ω·ω₀^{−2·0} = ω`. -/
    theorem mul_inv_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
        ω * (teichChar p ^ (2 * 0))⁻¹ = ω := by
      sorry
    ```
  - Source: `lwx.txt:157–160`
  - Source claim (verbatim):
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
  - Lean ↔ source match: The second character of `deg X_{(n,n+1),ω}`, `ωω₀^{−2n}`, at `n = 0` is `ω`; this is the bridge between `degXint_zero` (stated with `ω`) and the uniform D14.
  - Discharged by: mathlib: `MonoidHom.inv_apply` (needs `CommGroup ℤ_[p]ˣ` ✓), `pow_zero`, `inv_one`, `mul_one`.
  - Attacks attempted:
    - [1] Counterexample search: `a·(τ⁰)⁻¹ = a` ✓; none contradicting.
    - [2] Edge cases: `ω = 1` ✓; `p = 3` ✓.
    - [3] Hypothesis test: none.
    - [4] Source drift: `ωω₀^{−2·0} = ω` — literal.
    - [5] Discharge: `MonoidHom.inv_apply : f⁻¹ x = (f x)⁻¹` for `CommGroup G` (verified `#check`).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 2 lines; source: none

- **D4** (`targetChar_eq_mul_inv_teichChar_pow`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:58`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- The target nebentypus `ωω₀^{−2k−2}` of weight `k` is `ωω₀^{−2(k+1)}`
    ([LWX, §3.23 Step III], `lwx.txt:2079–2097`: the second term of `deg X_{(k,k+1),ω}` at `k + 1`). -/
    theorem targetChar_eq_mul_inv_teichChar_pow (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        targetChar p ω k = ω * (teichChar p ^ (2 * (k + 1)))⁻¹ := by
      sorry
    ```
  - Source: `lwx.txt:2079–2097`; `lwx.txt:2048–2078`
  - Source claim (verbatim):
    > "The final degree is computed by deg X_{k,ω} = n⁺_k − n⁻_k = (n⁺_k − n_k) + (n_k − n⁻_k) = { r_ord(ω), if k = 0, r_ord(ω⁻¹ω₀^{2k−2}) + r_ord(ωω₀^{−2k}), if k ≥ 1, and deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = n_{k+1} − n_k − (n_{k+1} − n⁻_{k+1}) − (n⁺_k − n_k) = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k}). This concludes the proof of Theorem 1.3."
    > "To compute n⁺_{k+1} − n_{k+1}, we recall the following exact sequence (cf. [Jo11]) 0 → S^D_{k+2}(K^pIw_{q²}, ψ) → S^{D,†}_{(k,ψ)} —(d/dz)^{k+1}→ S^{D,†}_{(−k−2,ψ)} → 0. This exact sequence is equivariant for the U_p-action on the first two spaces, and the p^{k+1}U_p-action on the third space. It is clear that n⁺_{k+1} − n_{k+1} is equal to the codimension of S^D_{k+2}(K^pIw_{q²}, ψ) in the slope ≤ k + 1 subspace in S^{D,†}_{(k,ψ)}. The latter in turn is equal to the dimension of slope zero subspace of S^{D,†}_{(−k−2,ψ)} by the exact sequence. Using Corollary 3.21, we thus obtain n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ·ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})."
  - Lean ↔ source match: `targetChar p ω k = ωω₀^{−2k−2}` (`TargetPoint.lean`, from `lwx.txt:2070–2076`) and `deg X_{(k+1,k+2),ω}` needs `ωω₀^{−2(k+1)}`: the same character, exponent rewritten.
  - Discharged by: `rfl` (definitional) or the listed mathlib/project lemmas.
  - Attacks attempted:
    - [1] Counterexample search: exponents `2k+2` vs `2(k+1)` — equal for every `k`.
    - [2] Edge cases: `k = 0`: `ωω₀^{−2}` both sides ✓.
    - [3] Hypothesis test: none.
    - [4] Source drift: none; the statement is the bookkeeping between `lwx.txt:2076` (`ωω₀^{−2k−2}`) and `lwx.txt:2097` (`ωω₀^{−2k}` at the next index).
    - [5] Discharge: `2 * (k + 1) = 2 * k + 2` checked to be `rfl` at planning time.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 1–2 lines; source: none

- **D5** (`partnerChar_mul_teichChar_sq_succ`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:64`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- The partner nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
    `(ωω₀²)⁻¹ω₀^{2(k+1)} = ω⁻¹ω₀^{2k}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
    theorem partnerChar_mul_teichChar_sq_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        partnerChar p (ω * teichChar p ^ 2) (k + 1) = partnerChar p ω k := by
      sorry
    ```
  - Source: `lwx.txt:164–169`; `lwx.txt:148–155`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
    > "Moreover, if the tame level is neat, and we denote by X_{n,ω} and X_{(n,n+1),ω} the preimages of W^{>1/p}_ω in X_n and X_{(n,n+1)} respectively, then deg X_{n,ω} = { r_ord(ω), if n = 0, r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n}), if n ≥ 1,"
  - Lean ↔ source match: Under `I = n+1 = k+2`, `ω ↦ ωω₀²`, the first term `r_ord(ω⁻¹ω₀^{2n−2})` becomes `r_ord((ωω₀²)⁻¹ω₀^{2(k+1)})`; the lemma says this character is `ω⁻¹ω₀^{2k} = partnerChar p ω k`, the first term at `(k+1, ω)`.  This is the whole content of the corollary's integer case.
  - Discharged by: mathlib: `mul_inv` (`DivisionCommMonoid`, `ℤ_[p]ˣ` is a `CommGroup` ✓), `pow_add`, `inv_mul_cancel_left`; project: `partnerChar_apply`, `teichChar_apply` (verified `#check`).
  - Attacks attempted:
    - [1] Counterexample search: with `ω r = a`, `teichRes r = τ`: `(aτ²)⁻¹τ^{2k+2} = a⁻¹τ^{2k}` ✓ for all `a, τ` in an abelian group; `grep partnerChar` finds no contradicting statement.
    - [2] Edge cases: `k = 0`: `partnerChar p (ωω₀²) 1 = (ωω₀²)⁻¹ω₀² = ω⁻¹ = partnerChar p ω 0` ✓ (`invChar ω * teichChar p ^ 0`); `p = 3` (`ω₀² = 1`): both sides `ω⁻¹ω₀^{2k}` ✓.
    - [3] Hypothesis test: the shift by `+1` in `k` is necessary (at `k` unshifted the identity `partnerChar p (ωω₀²) k = partnerChar p ω k` fails: `ω⁻¹ω₀^{2k−2} ≠ ω⁻¹ω₀^{2k}` for `p > 3`).
    - [4] Source drift: the corollary's `deg X_{I+1,ωω₀²}` with Thm 1.3's formula gives exactly `(ωω₀²)⁻¹ω₀^{2(I+1)−2}` — matched.
    - [5] Discharge: `partnerChar_apply ω k r : partnerChar p ω k r = (ω r)⁻¹ * teichRes r ^ (2 * k)` (verified); `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹` (verified).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 3 lines; source: none

- **D6** (`targetChar_mul_teichChar_sq_succ`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:70`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- The target nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
    `ωω₀²·ω₀^{−2(k+1)−2} = ωω₀^{−2k−2}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
    theorem targetChar_mul_teichChar_sq_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        targetChar p (ω * teichChar p ^ 2) (k + 1) = targetChar p ω k := by
      sorry
    ```
  - Source: `lwx.txt:164–169`; `lwx.txt:148–155`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
    > "Moreover, if the tame level is neat, and we denote by X_{n,ω} and X_{(n,n+1),ω} the preimages of W^{>1/p}_ω in X_n and X_{(n,n+1)} respectively, then deg X_{n,ω} = { r_ord(ω), if n = 0, r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n}), if n ≥ 1,"
  - Lean ↔ source match: Under `I = k+2`, `ω ↦ ωω₀²`, the second term `r_ord(ωω₀^{−2n})` becomes `r_ord(ωω₀²·ω₀^{−2(k+2)}) = r_ord(ωω₀^{−2k−2}) = r_ord(targetChar p ω k)`.
  - Discharged by: mathlib: `pow_add`, `mul_inv`, `mul_inv_cancel_left`; project: `targetChar_apply`, `teichChar_apply`.
  - Attacks attempted:
    - [1] Counterexample search: `aτ²(τ^{2k+4})⁻¹ = a(τ^{2k+2})⁻¹` ✓ in any abelian group.
    - [2] Edge cases: `k = 0`: `targetChar p (ωω₀²) 1 = ωω₀²ω₀^{−4} = ωω₀^{−2} = targetChar p ω 0` ✓.
    - [3] Hypothesis test: as D5, the `+1` shift is necessary.
    - [4] Source drift: none.
    - [5] Discharge: `targetChar_apply ω k r : targetChar p ω k r = ω r * (teichRes r ^ (2 * k + 2))⁻¹` (verified).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 3 lines; source: none

- **D7** (`mul_teichChar_sq_mul_inv_teichChar_pow_succ`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:75`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- `ωω₀²·ω₀^{−2(n+1)} = ω·ω₀^{−2n}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
    theorem mul_teichChar_sq_mul_inv_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
        ω * teichChar p ^ 2 * (teichChar p ^ (2 * (n + 1)))⁻¹ = ω * (teichChar p ^ (2 * n))⁻¹ := by
      sorry
    ```
  - Source: `lwx.txt:164–169`; `lwx.txt:157–160`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
  - Lean ↔ source match: Under `I = (n+1, n+2)`, `ω ↦ ωω₀²`, the second term `r_ord(ωω₀^{−2n})` of `deg X_{(n,n+1),ω}` becomes `r_ord(ωω₀²·ω₀^{−2(n+1)})`; the lemma identifies the character with `ωω₀^{−2n}`.
  - Discharged by: mathlib: `MonoidHom.inv_apply`, `pow_add`, `mul_inv`, `mul_inv_cancel_left`; project: `teichChar_apply`.
  - Attacks attempted:
    - [1] Counterexample search: `aτ²(τ^{2n+2})⁻¹ = a(τ^{2n})⁻¹` ✓.
    - [2] Edge cases: `n = 0`: `ωω₀²·ω₀^{−2} = ω = ω·ω₀^{0}` ✓ (consistent with D3).
    - [3] Hypothesis test: none.
    - [4] Source drift: none.
    - [5] Discharge: all names verified by `#check`.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 3 lines; source: none

- **D8** (`ordDim_le_card`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:85`
  - Statement (verbatim from the skeleton):
    ```lean
    /-- `r_ord(ω) ≤ t`: the ordinary dimension is at most the number of blocks
    (`le_card_of_isUnit_charCoeff` at the unit coefficient `ordDim`). -/
    theorem ordDim_le_card (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
        ordDim D ω ≤ Fintype.card ι := by
      sorry
    ```
  - Source: `lwx.txt:123–127`
  - Source claim (verbatim):
    > "the constant t is equal to the dimension of the space of weight 2 automorphic forms with q-Iwahori level structure at p and tame level as above, and r_ord(ω) denotes the dimension of the ordinary subspace of automorphic forms of weight 2 and character ω."
  - Lean ↔ source match: `r_ord(ω) ≤ t` is implicit in the source (a subspace of a `t`-dimensional space); at the coefficient level `ordDim` is the top unit coefficient of `det(1 − X·U_p)` and `le_card_of_isUnit_charCoeff` bounds every unit-coefficient index by `t = card ι`.
  - Discharged by: project: `le_card_of_isUnit_charCoeff (D) (ω) {n} (hn : IsUnit (charCoeff (D.op ω) n)) : n ≤ Fintype.card ι` and `isUnit_charCoeff_ordDim D ω` (both verified `#check`, sorry-free).
  - Attacks attempted:
    - [1] Counterexample search: `ι` empty: `ordDim = 0 ≤ 0` ✓ (the lemma `le_card_of_isUnit_charCoeff` handles `IsEmpty ι` itself).
    - [2] Edge cases: `ω = 1`; `t = 1` ✓.
    - [3] Hypothesis test: no `Nonempty ι` needed (checked against the signature).
    - [4] Source drift: none.
    - [5] Discharge: two project lemmas, composition of length 2 ✓.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 1 line; source: implicit

- **D9** (`touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:121`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **The left gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2025–2047`:
    `n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})`), granted the family of Atkin–Lehner data. -/
    theorem touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        touchX p (Fintype.card ι) (k + 1)
            - leftIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
                hshape) ω (k + 1)
          = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (partnerChar p ω k) := by
      sorry
    ```
  - Source: `lwx.txt:2025–2047`
  - Source claim (verbatim):
    > "For k ≥ 0, first note that n_{k+1} − n⁻_{k+1} is equal to the dimension of slope k + 1 subspace in S^D_{k+2}(K^pIw_{q²}; ψ). By Atkin–Lehner theory (Proposition 3.22) and Proposition 2.15, the multiplicity is the same as the dimension of slope zero subspace in S^{D,†}_{(k,ψ⁻¹)}. Using Corollary 3.21 again, we deduce that n_{k+1} − n⁻_{k+1} = r_ord(ψ⁻¹|_Δ·ω₀^k) = r_ord(ω⁻¹ω₀^{2k}) because ψ⁻¹|_Δ·ω₀^k = χ_k⁻¹|_Δ·ω₀^{2k} = ω⁻¹ω₀^{2k}."
  - Lean ↔ source match: The source's `n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})` at the classical point of `(ω, k)`; `touchX p t (k+1) = n_{k+1}`, `leftIndex … (k+1) = n⁻_{k+1}`, `ordDim … (partnerChar p ω k) = r_ord(ω⁻¹ω₀^{2k})`.  The level-`1` lemma proves it from H1 (Atkin–Lehner, JL-free here) and the classical-slope reading in place of Prop 2.15 + Cor 3.21.
  - Discharged by: project: `touchX_sub_leftIndex_eq_ordDim` (`StepThree.lean:608`, sorry-free) at the classical data of the family's weight `(ω, k)` — one application.
  - Attacks attempted:
    - [1] Composition attack: the level-`1` lemma's `hAL` is at `(c₀.matrix idx, c₀'.matrix idx)` with `c₀'` at `partnerChar p ω k` and `hζ.inv`; `atkinLehnerHypothesis_of_atkinLehnerData` produces exactly that pair (its conclusion, `#check`ed) ✓.
    - [2] Edge cases: `k = 0`: `n_1 − n⁻_1 = r_ord(ω⁻¹)` with `partnerChar p ω 0 = invChar ω · ω₀⁰` ✓ (matches `degXint_zero`'s `ω'`).
    - [3] Hypothesis test: `hdet` is not slack (the level-`1` lemma requires it, via the complement bound); `[IsAlgClosed K]` required (roots of the classical factor).
    - [4] Source drift: the source's left gap is stated for `k ≥ 0` at `n_{k+1}` — matched index for index.
    - [5] Discharge: argument order `idx hp2 hψ hshape hdet c c' d d' hAL` verified by `#check`; the `vRepD (toData) ≡ vRepF` acceptance is the compiled pattern of R10/R13 (`ConductorSlopes.lean`).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~12 lines (five terms); source: 5 lines

- **D10** (`rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:135`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **The right gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2048–2078`:
    `n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})`), granted the family of Atkin–Lehner data (H2 is
    `isThetaExact_classicalData`). -/
    theorem rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        rightIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) ω (k + 1)
            - touchX p (Fintype.card ι) (k + 1)
          = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (targetChar p ω k) := by
      sorry
    ```
  - Source: `lwx.txt:2048–2078`
  - Source claim (verbatim):
    > "To compute n⁺_{k+1} − n_{k+1}, we recall the following exact sequence (cf. [Jo11]) 0 → S^D_{k+2}(K^pIw_{q²}, ψ) → S^{D,†}_{(k,ψ)} —(d/dz)^{k+1}→ S^{D,†}_{(−k−2,ψ)} → 0. This exact sequence is equivariant for the U_p-action on the first two spaces, and the p^{k+1}U_p-action on the third space. It is clear that n⁺_{k+1} − n_{k+1} is equal to the codimension of S^D_{k+2}(K^pIw_{q²}, ψ) in the slope ≤ k + 1 subspace in S^{D,†}_{(k,ψ)}. The latter in turn is equal to the dimension of slope zero subspace of S^{D,†}_{(−k−2,ψ)} by the exact sequence. Using Corollary 3.21, we thus obtain n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ·ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})."
  - Lean ↔ source match: The source's `n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})` through the theta exact sequence (H2, here `isThetaExact_classicalData`) and Cor 3.21; `rightIndex … (k+1) = n⁺_{k+1}`, `targetChar p ω k = ωω₀^{−2k−2}` (`lwx.txt:2070–2076`).
  - Discharged by: project: `rightIndex_sub_touchX_eq_ordDim` (`StepThree.lean:726`) + `isThetaExact_classicalData` — two applications.
  - Attacks attempted:
    - [1] Composition attack: `rightIndex_sub_touchX_eq_ordDim` wants `hH2 : IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k`; `isThetaExact_classicalData idx hshape hdet c d` has exactly that type (`#check`) ✓ — this composition is `degX_succ_of_targetData` (`DegreeFormula.lean:51`), compiled.
    - [2] Edge cases: `k = 0`: `n⁺_1 − n_1 = r_ord(ωω₀^{−2})` ✓.
    - [3] Hypothesis test: `hdet` needed twice (H2 and the complement bound).
    - [4] Source drift: the right gap is at `n_{k+1}` for `k ≥ 0` — matched.
    - [5] Discharge: argument orders verified by `#check`.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~12 lines; source: 8 lines

- **D11** (`degX_succ_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:148`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Thm 1.3]: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})` at every weight**
    (`lwx.txt:151–155`), granted the family of Atkin–Lehner data. -/
    theorem degX_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
            (k + 1)
          = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (partnerChar p ω k)
            + ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (targetChar p ω k) := by
      sorry
    ```
  - Source: `lwx.txt:148–155`; `lwx.txt:2079–2097`
  - Source claim (verbatim):
    > "Moreover, if the tame level is neat, and we denote by X_{n,ω} and X_{(n,n+1),ω} the preimages of W^{>1/p}_ω in X_n and X_{(n,n+1)} respectively, then deg X_{n,ω} = { r_ord(ω), if n = 0, r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n}), if n ≥ 1,"
    > "The final degree is computed by deg X_{k,ω} = n⁺_k − n⁻_k = (n⁺_k − n_k) + (n_k − n⁻_k) = { r_ord(ω), if k = 0, r_ord(ω⁻¹ω₀^{2k−2}) + r_ord(ωω₀^{−2k}), if k ≥ 1, and deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = n_{k+1} − n_k − (n_{k+1} − n⁻_{k+1}) − (n⁺_k − n_k) = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k}). This concludes the proof of Theorem 1.3."
  - Lean ↔ source match: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})` (`n = k+1` in `lwx.txt:153–154`: `ω⁻¹ω₀^{2n−2} = ω⁻¹ω₀^{2k}`, `ωω₀^{−2n} = ωω₀^{−2k−2}`); the per-weight version is `degX_succ_of_atkinLehnerData` (`lwx-h1`), and the family supplies its data at `(ω, k)`.
  - Discharged by: project: `degX_succ_of_atkinLehnerData` (`AtkinLehnerIdentity.lean:627`, sorry-free, std axioms) — one application.
  - Attacks attempted:
    - [1] Composition attack: could `exact` fail on `hshape`/`hdet` (stated with `vRepF_mem_levelM1`) vs the expected `vRepD_mem_levelM1 … (toData …)`? Proof irrelevance makes the `Prop` arguments defeq; the identical situation compiled in R10 (`hasUnitBand_of_atkinLehnerData … hshape`) and R13 ✓.
    - [2] Edge cases: `k = 0`: `deg X_{1,ω} = r_ord(ω⁻¹) + r_ord(ωω₀^{−2})` ✓ (source `n = 1`: `ω⁻¹ω₀⁰`, `ωω₀^{−2}`).
    - [3] Hypothesis test: `hζ : IsPrimitiveRoot ζ p` for the family's root is what `nebCharK ψ ω k ζ` needs; nothing slack.
    - [4] Source drift: the source's formula is for `n ≥ 1`; stated at `k + 1` ✓; `n = 0` is `degX_zero`, already unconditional (`StepThree.lean:910`) — not restated.
    - [5] Discharge: argument order verified by `#check`.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: 2 lines; source: 4 lines

- **D12** (`degXint_zero_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:162`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Thm 1.3]: `deg X_{(0,1),ω} = qt − r_ord(ω⁻¹) − r_ord(ω)`** (`lwx.txt:157–159` at
    `n = 0`), granted the family of Atkin–Lehner data. -/
    theorem degXint_zero_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω 0
          = p * Fintype.card ι
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (partnerChar p ω 0)
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) ω := by
      sorry
    ```
  - Source: `lwx.txt:157–160`; `lwx.txt:1923–1927`; `lwx.txt:2014–2022`
  - Source claim (verbatim):
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
    > "For a uniform treatment later, we set n⁻_0 = 0 and n⁺_0 the maximal index in [0, t] such that b_{n⁺_0,0} is a p-adic unit."
    > "Step III: It remains to compute the degrees of X_{I,ω}'s. It is clear that X_{0,ω} coincides with the restriction of X^ord_ω, which is introduced in the proof of Theorem 3.19, to W^{>1/p}_ω. Then by Corollary 3.21, deg X_{0,ω} is equal to the dimension of slope zero subspace in S^{D,†}_ω. That is, deg X_{0,ω} = n⁺_0 = r_ord(ω)."
  - Lean ↔ source match: `deg X_{(0,1),ω} = qt − r_ord(ω⁻¹) − r_ord(ω)`: `partnerChar p ω 0 = ω⁻¹ω₀⁰ = ω⁻¹` and `ωω₀^{−0} = ω`; `degXint_zero` (`StepThree.lean:955`) proves it from the left gap at `n_1` and `n⁺_0 = r_ord(ω)` (`rightIndex_zero_eq_ordDim`).
  - Discharged by: project: `degXint_zero` — one application at the family's data.
  - Attacks attempted:
    - [1] Composition attack: as D9 (same five terms at `k = 0`).
    - [2] Edge cases: `t = 1`, `p = 3`: `3 − r_ord(ω⁻¹) − r_ord(ω) ≥ 1` ✓ (consistent with positivity).
    - [3] Hypothesis test: `d₀'` is required by `degXint_zero`'s signature (it takes `d'`) even though the `k = 0` right gap does not use H2 — not slack from this board's side (the level-`1` signature is protected).
    - [4] Source drift: the source's `deg X_{(0,1),ω}` uses `ω⁻¹ω₀⁰`, `ωω₀⁰` — matched.
    - [5] Discharge: `degXint_zero idx hp2 hψ hshape hdet c c' d d' hAL` verified by `#check`.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~12 lines; source: 3 lines

- **D13** (`degXint_succ_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:178`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Thm 1.3]: `deg X_{(k+1,k+2),ω} = qt − r_ord(ω⁻¹ω₀^{2k+2}) − r_ord(ωω₀^{−2k−2})`**
    (`lwx.txt:2089–2097`: `n⁻_{k+2} − n⁺_{k+1} = (n_{k+2} − n_{k+1}) − (n_{k+2} − n⁻_{k+2})
    − (n⁺_{k+1} − n_{k+1})`), granted the family of Atkin–Lehner data. -/
    theorem degXint_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω (k + 1)
          = p * Fintype.card ι
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (partnerChar p ω (k + 1))
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (targetChar p ω k) := by
      sorry
    ```
  - Source: `lwx.txt:2079–2097`; `lwx.txt:157–160`
  - Source claim (verbatim):
    > "The final degree is computed by deg X_{k,ω} = n⁺_k − n⁻_k = (n⁺_k − n_k) + (n_k − n⁻_k) = { r_ord(ω), if k = 0, r_ord(ω⁻¹ω₀^{2k−2}) + r_ord(ωω₀^{−2k}), if k ≥ 1, and deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = n_{k+1} − n_k − (n_{k+1} − n⁻_{k+1}) − (n⁺_k − n_k) = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k}). This concludes the proof of Theorem 1.3."
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
  - Lean ↔ source match: The source's `deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = (n_{k+1} − n_k) − (n_{k+1} − n⁻_{k+1}) − (n⁺_k − n_k) = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k})`, re-indexed to `(k+1, k+2)`: `n_{k+2} − n_{k+1} = pt` (`touchX`), the left gap at `n_{k+2}` is `r_ord(ω⁻¹ω₀^{2(k+1)}) = ordDim (partnerChar p ω (k+1))` (D9 at `k+1`), the right gap at `n_{k+1}` is `r_ord(ωω₀^{−2k−2}) = ordDim (targetChar p ω k)` (D10 at `k`).
  - Discharged by: project: D9, D10, `hasUnitBand_of_atkinLehnerFamily` (`ConductorSlopes.lean`), `leftIndex_mem`, `rightIndex_mem`, `rightIndex_le_leftIndex_succ` (`Vertices.lean`, all verified `#check`); mathlib: `omega`.
  - Attacks attempted:
    - [1] Composition attack: could both gaps be right and the subtraction wrong?  Only if `r + r' > pt`, i.e. `rightIndex (k+1) > leftIndex (k+2)`; `rightIndex_le_leftIndex_succ` (needs both unit bands, supplied) excludes it ✓.  Could `omega` see `touchX (k+1+1)` and `touchX (k+2)` as different atoms?  Every term is at `k + 1 + 1` (D9 at `k+1`, `hb2` at `k + 1 + 1`, `degXint … (k+1)` unfolds to `leftIndex … (k + 1 + 1)`) — consistent by construction.
    - [2] Edge cases: `k = 0`: `deg X_{(1,2),ω} = pt − r_ord(ω⁻¹ω₀²) − r_ord(ωω₀^{−2})` = the source at `n = 1` ✓.
    - [3] Hypothesis test: the unit band at `k+2` is genuinely needed (`leftIndex` is `sInf` of a set that must be nonempty) ✓; `hle1`/`hle2` needed for the `ℕ`-subtractions in `hL`/`hR` to be exact ✓.
    - [4] Source drift: the source states the formula for all `n ≥ 0`; here `n = k + 1 ≥ 1`, with `n = 0` as D12 — together every `n` (D14).
    - [5] Discharge: `rightIndex_le_leftIndex_succ D ω hb hb' : rightIndex D ω k ≤ leftIndex D ω (k+1)` (verified); `leftIndex_mem`/`rightIndex_mem` conjunct shapes verified.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~18 lines; source: 4 lines (`lwx.txt:2089–2097`)

- **D14** (`degXint_of_atkinLehnerFamily`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:193`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` for every
    `n ≥ 0`** (`lwx.txt:157–159`), granted the family of Atkin–Lehner data. -/
    theorem degXint_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω n
          = p * Fintype.card ι
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (partnerChar p ω n)
            - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (ω * (teichChar p ^ (2 * n))⁻¹) := by
      sorry
    ```
  - Source: `lwx.txt:157–160`
  - Source claim (verbatim):
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
  - Lean ↔ source match: Literally `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` for all `n ≥ 0`, assembled from the `n = 0` (D12) and `n = k+1` (D13) cases.
  - Discharged by: project: D12, D13, D3, D4 — a two-case `rw`.
  - Attacks attempted:
    - [1] Composition attack: after `rcases`, are the cases `0` and `k + 1` (not `Nat.zero`/`Nat.succ k`)?  Mathlib's custom `cases_eliminator` gives `0`/`k + 1` ✓; `degXint_zero_of_atkinLehnerFamily` is stated at `0` ✓, D13 at `k + 1` ✓; D3 is stated with `2 * 0` and D4 with `2 * (k + 1)` — the exact shapes after `rcases` ✓.
    - [2] Edge cases: `n = 0` and `n = 1` recover D12 and D13 at `k = 0`.
    - [3] Hypothesis test: none beyond D12/D13.
    - [4] Source drift: none — this is the source's display verbatim.
    - [5] Discharge: two rewrites per case.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~6 lines; source: 3 lines

- **D15** (`degXint_pos_of_atkinLehnerFamily`) **[MILESTONE M1]**
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:208`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} > 0` for all `n ≥ 0`** (`lwx.txt:160`): `qt − r − r' ≥
    qt − 2t > 0` since `r_ord ≤ t` and `p ≥ 3`. -/
    theorem degXint_pos_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
        0 < degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω n := by
      sorry
    ```
  - Source: `lwx.txt:157–160`; `lwx.txt:123–127`
  - Source claim (verbatim):
    > "and deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n}). for all n ≥ 0. In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0."
    > "the constant t is equal to the dimension of the space of weight 2 automorphic forms with q-Iwahori level structure at p and tame level as above, and r_ord(ω) denotes the dimension of the ordinary subspace of automorphic forms of weight 2 and character ω."
  - Lean ↔ source match: The source asserts positivity without proof; the reason is `r_ord(·) ≤ t` and `q ≥ 3`, so `qt − r − r' ≥ (q − 2)t > 0`.  **Milestone M1**: with D11, D14 and `degX_zero`, every degree statement of [LWX, Thm 1.3] holds at the coefficient level at every classical weight, granted the family.
  - Discharged by: project: D14, D8; mathlib: `Fintype.card_pos`, `Nat.mul_le_mul_right`, `Nat.Prime.two_le`; `omega`.
  - Attacks attempted:
    - [1] Counterexample search: could `r + r' = pt`?  `r, r' ≤ t` and `p ≥ 3` give `r + r' ≤ 2t < pt` ✓; at `p = 2` (excluded) `2t − r − r'` could be `0` — consistent with the source's separate `q = 4` treatment.
    - [2] Edge cases: `t = 1`, `p = 3`, `r = r' = 1`: `3 − 1 − 1 = 1 > 0` ✓.
    - [3] Hypothesis test: `hp2` is necessary for the argument (not slack); `Nonempty ι` necessary (`t = 0` gives `0`).
    - [4] Source drift: the source claims `> 0` for all `n ≥ 0` — matched.
    - [5] Discharge: `omega` with atoms `N, t, a, b` and the linear facts `3t ≤ N`, `a ≤ t`, `b ≤ t`, `0 < t` closes `0 < N − a − b` ✓ (checked by hand).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~8 lines; source: 1 line

- **D16** (`degX_succ_mul_teichChar_sq`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:219`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Cor 1.4] at the integers** (`lwx.txt:164–166`): `deg X_{k+1,ω} = deg X_{k+2,ωω₀²}`. -/
    theorem degX_succ_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
            (k + 1)
          = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
              (ω * teichChar p ^ 2) (k + 2) := by
      sorry
    ```
  - Source: `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: `deg X_{k+1,ω} = deg X_{k+2,ωω₀²}`: both sides expand by D11 into `ordDim (partnerChar …) + ordDim (targetChar …)` and D5/D6 identify the characters — the corollary's substitution made explicit.
  - Discharged by: project: D11 (twice), D5, D6.
  - Attacks attempted:
    - [1] Counterexample search at the excluded index: `deg X_{0,ω} = r_ord(ω)` vs `deg X_{1,ωω₀²} = r_ord(ω⁻¹ω₀^{−2}) + r_ord(ω)` — differ when `r_ord(ω⁻¹ω₀^{−2}) ≠ 0`; the statement starts at `k + 1` ✓ (the source's `I = (0,1), 1, …` also excludes `0`).
    - [2] Edge cases: `k = 0`: `deg X_{1,ω} = r_ord(ω⁻¹) + r_ord(ωω₀^{−2})`, `deg X_{2,ωω₀²} = r_ord((ωω₀²)⁻¹ω₀²) + r_ord(ωω₀²ω₀^{−4})` — equal ✓; `p = 3` (`ω₀² = 1`): says `deg X_{k+1,ω} = deg X_{k+2,ω}` — consistent with periodicity of period `(3−1)/2 = 1` ✓.
    - [3] Hypothesis test: none beyond D11's.
    - [4] Source drift: `I + 1` for `I = n` is `n + 1` ✓; `ωω₀²` is `ω * teichChar p ^ 2` (the spelling of `slopeRatio_mul_teichChar_sq`).
    - [5] Discharge: `k + 2 = k + 1 + 1` verified `rfl`; the `rw` chain's second D11 instance matches `degX … (ω * teichChar p ^ 2) (k + 1 + 1)` ✓.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~3 lines; source: 2 lines

- **D17** (`degXint_mul_teichChar_sq`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:231`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Cor 1.4] on the open intervals** (`lwx.txt:164–166`):
    `deg X_{(n,n+1),ω} = deg X_{(n+1,n+2),ωω₀²}`. -/
    theorem degXint_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω n
          = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (ω * teichChar p ^ 2) (n + 1) := by
      sorry
    ```
  - Source: `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: `deg X_{(n,n+1),ω} = deg X_{(n+1,n+2),ωω₀²}`: both sides expand by D14 and D5/D7 identify the characters.
  - Discharged by: project: D14 (twice), D5, D7.
  - Attacks attempted:
    - [1] Counterexample search: at `n = 0`: `pt − r_ord(ω⁻¹) − r_ord(ω)` vs `pt − r_ord((ωω₀²)⁻¹ω₀²) − r_ord(ωω₀²ω₀^{−2})` — equal ✓ (so, unlike the integer case, no index is excluded).
    - [2] Edge cases: `p = 3` ✓ as D16.
    - [3] Hypothesis test: none.
    - [4] Source drift: `I + 1` for `I = (n, n+1)` is `(n+1, n+2)` ✓.
    - [5] Discharge: the second D14 instance is at `(ω * teichChar p ^ 2) (n + 1)`, producing `partnerChar p (ω * teichChar p ^ 2) (n + 1)` and `ω * teichChar p ^ 2 * (teichChar p ^ (2 * (n + 1)))⁻¹` — exactly D5's and D7's left-hand sides ✓.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~3 lines; source: 2 lines

- **D18** (`degX_succ_mul_teichChar_pow`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:242`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- [LWX, Cor 1.4] at the integers, iterated `m` times: `deg X_{k+1,ω} = deg X_{k+1+m,ωω₀^{2m}}`. -/
    theorem degX_succ_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m k : ℕ) :
        degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
            (k + 1)
          = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
              (ω * teichChar p ^ (2 * m)) (k + 1 + m) := by
      sorry
    ```
  - Source: `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: Iterating `deg X_{I,ω} = deg X_{I+1,ωω₀²}` `m` times gives `deg X_{I,ω} = deg X_{I+m,ωω₀^{2m}}` — the source's "in particular" step, spelled out.
  - Discharged by: project: D16, D1, D2; `omega` for the index identities.
  - Attacks attempted:
    - [1] Composition attack: `rw [ih]` rewrites the LHS `degX … ω (k+1)` into `degX … (ωω₀^{2m}) (k+1+m)`; the RHS `degX … (ω * teichChar p ^ (2 * (m+1))) (k + 1 + (m + 1))` is rewritten by D2 and the `show`s to `degX … (ωω₀^{2m}·ω₀²) (k + m + 2)`; D16's instance matches both sides after `k + 1 + m ↦ k + m + 1` ✓ (the `show` for `k + 1 + m` does not touch `k + 1 + (m + 1)` since the latter is not syntactically `k + 1 + m` applied to anything).
    - [2] Edge cases: `m = 0` (D1 + `rfl`), `m = 1` (D16 itself, up to `k + 1 + 1 = k + 2`).
    - [3] Hypothesis test: none.
    - [4] Source drift: none.
    - [5] Discharge: mirrors the compiled `slopeRatio_mul_teichChar_pow`.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~8 lines; source: 1 line

- **D19** (`degXint_mul_teichChar_pow`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:254`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- [LWX, Cor 1.4] on the open intervals, iterated `m` times:
    `deg X_{(n,n+1),ω} = deg X_{(n+m,n+m+1),ωω₀^{2m}}`. -/
    theorem degXint_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m n : ℕ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω n
          = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) (ω * teichChar p ^ (2 * m)) (n + m) := by
      sorry
    ```
  - Source: `lwx.txt:164–169`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
  - Lean ↔ source match: The `m`-fold iterate of the open-interval shift.
  - Discharged by: project: D17, D1, D2.
  - Attacks attempted:
    - [1] Composition attack: D17 at `(ωω₀^{2m}, n + m)` reads `degXint … (ωω₀^{2m}) (n + m) = degXint … (ωω₀^{2m}·ω₀²) (n + m + 1)` — matches the goal after `ih`, D2 and the `show` ✓.
    - [2] Edge cases: `m = 0`, `m = 1` ✓.
    - [3] Hypothesis test: none.
    - [4] Source drift: none.
    - [5] Discharge: as D18.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~6 lines; source: 1 line

- **D20** (`degX_succ_add_period`)
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:266`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Cor 1.4]: `deg X_{n,ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 1`**
    (`lwx.txt:168–169`): `deg X_{k+1+(p−1)/2,ω} = deg X_{k+1,ω}` ("since `ω₀^{ϕ(q)} = 1`"). -/
    theorem degX_succ_add_period [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
        degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
            (k + 1 + (p - 1) / 2)
          = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
              ω (k + 1) := by
      sorry
    ```
  - Source: `lwx.txt:164–169`; `lwx.txt:2357–2360`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
    > "In particular, since ω₀^{ϕ(q)} = ω₀^{q(p−1)/p} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) + ϕ(q)p^M/(2q²)."
  - Lean ↔ source match: At `m = (p−1)/2`, `ω₀^{2m} = ω₀^{p−1} = 1` (`teichChar_pow_sub_one`, [LWX]'s "since ω₀^{ϕ(q)} = 1"), so D18 reads `deg X_{k+1,ω} = deg X_{k+1+(p−1)/2,ω}` — periodicity modulo `ϕ(q)/2` at the integers `n ≥ 1`.
  - Discharged by: project: D18, `teichChar_pow_sub_one` (`AtkinLehnerFamily.lean`, sorry-free); mathlib: `Nat.Prime.odd_of_ne_two`.
  - Attacks attempted:
    - [1] Counterexample search: `p = 3`: period `1`, i.e. `deg X_{k+2,ω} = deg X_{k+1,ω}` — true because `ω₀² = 1` for `p = 3` makes D16 say exactly that ✓.
    - [2] Edge cases: `k = 0`: `deg X_{1+(p−1)/2,ω} = deg X_{1,ω}` ✓.
    - [3] Hypothesis test: `hp2` needed for `2·((p−1)/2) = p − 1`.
    - [4] Source drift: "periodic modulo ϕ(q)/2" with `ϕ(q) = p − 1` for odd `p` (`lwx.txt:50`) — matched; the source's periodicity is in the index `I`, as here.
    - [5] Discharge: `teichChar_pow_sub_one : teichChar p ^ (p - 1) = 1` (verified); the `hω` proof compiled verbatim on `lwx-conductor` (R17).
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~7 lines; source: 1 line

- **D21** (`degXint_add_period`) **[MILESTONE M2]**
  - Lean declaration: `PhD/LWX/DegreePeriodicity.lean:278`
  - Statement (verbatim from the skeleton):
    ```lean
    include hfin hv hvinj c hc hstab d hd hfact hdet in
    /-- **[LWX, Cor 1.4]: `deg X_{(n,n+1),ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 0`**
    (`lwx.txt:168–169`): `deg X_{(n+(p−1)/2, n+(p−1)/2+1),ω} = deg X_{(n,n+1),ω}`. -/
    theorem degXint_add_period [Nonempty ι] [IsAlgClosed K]
        (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
        (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
        degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
            ω (n + (p - 1) / 2)
          = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
              hshape) ω n := by
      sorry
    ```
  - Source: `lwx.txt:164–169`; `lwx.txt:2357–2360`
  - Source claim (verbatim):
    > "Corollary 1.4. If the tame level is neat, then for I = (0, 1), 1, (1, 2), 2, ..., we have deg X_{I,ω} = deg X_{I+1,ωω₀²}. In particular, the degree deg X_{I,ω} is periodic modulo ϕ(q)/2."
    > "In particular, since ω₀^{ϕ(q)} = ω₀^{q(p−1)/p} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) + ϕ(q)p^M/(2q²)."
  - Lean ↔ source match: Periodicity modulo `ϕ(q)/2` on the open intervals `(n, n+1)`, `n ≥ 0`.
  - Discharged by: project: D19, `teichChar_pow_sub_one`.
  - Attacks attempted:
    - [1] Counterexample search: `p = 3`: `deg X_{(n+1,n+2),ω} = deg X_{(n,n+1),ω}` ✓ (D17 with `ω₀² = 1`).
    - [2] Edge cases: `n = 0` ✓.
    - [3] Hypothesis test: `hp2` needed.
    - [4] Source drift: none.
    - [5] Discharge: as D20.
    - Verdict: SURVIVED (no flaw found).
  - Prior-B2 log consultation: `b2_log.jsonl` of the root board, `lwx-h1` (2), `lwx-theta` (6), `lwx-theta-h2` (0) and `lwx-conductor` (5) read: no match by name (every name here is new); no match by shape. The one inherited lesson — `lwx-conductor` R13–R17 (an `include` list omitting a structure the proof needs) and `lwx-h1` W5 (`hU` omitted) — is applied: every proof-only hypothesis of section `Family` is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`, and `F` occurs in every statement through `vRepF`.
  - Size: ~7 lines; source: 1 line

## 3. Confidence gate (Step 5)

1. Every leaf discharged from mathlib or project code: **yes** (no API gap).
2. Skeleton compiles: `lake build PhD.LWX.DegreePeriodicity` — **Build completed successfully (3830 jobs)**, 21 `sorry` warnings and no other warning or error in the new file (no unused-section-variable finding; the `include` lists are complete).
3. Verbatim source quote + match paragraph per leaf: **yes** (21/21; D1–D8's quotes are the definitions/
   statements the identities serve, the identities themselves being definitional).
4. Adversarial pass on every leaf and internal node: **yes** (≥ 5 attacks each, all survived).
5. Prior-B2 log consulted: **yes** (no name/shape match; the `include`-completeness lesson applied).
6. Tree mirrors the source: **yes** — Step III's two gaps → the degrees (`lwx.txt:2025–2097`) and Cor 1.4's
   substitution, expanded where the source is silent (the corollary, positivity), each expansion quoted
   against the source's statement; LOC estimates cite the source line counts.
7. Single-conclusion leaves: **yes** (no `∧`-chain anywhere).
