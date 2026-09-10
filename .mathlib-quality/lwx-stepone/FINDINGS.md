# lwx-stepone — first planning pass, 2026-09-06

`/develop` was invoked for [LWX, Theorem 1.3, proof Step I] and stopped at Phase 1e Step 1
without writing a ticket board, for three reasons recorded below.  References extracted for
this board live in `references/`.

> **STATUS UPDATE (2026-09-06, later the same day).**  Reasons 1 and 2 are **resolved**:
> `lwx-seam-m` has landed, so its files are free and Prop 2.17 now holds at every
> analyticity level `m`.  Reason 3 stands and has been promoted to the plan of record:
> Atkin–Lehner is hypothesis **H1** and right-exactness of the theta sequence is hypothesis
> **H2**; classicality is *not* a hypothesis, being derivable from H1 plus non-negativity of
> slopes.  See **`JL-AUDIT.md`** in this directory for the per-result Jacquet–Langlands
> audit, which every board in this development must cite.  Sections below are kept as the
> original evidence trail; where they say "paused", read "resolved" for Reasons 1 and 2.

---

## Reason 1 — file-ownership conflict with the running `lwx-seam-m` board (RESOLVED)

The user's standing instruction was to pause if Step I needs to edit a file owned by the
concurrent `lwx-seam-m` board.  It does.

`lwx-seam-m/tickets.md` declares its owned files:

> **Files owned by this board** (never touch the concurrent `tate-riesz` board's files):
> `PhD/TateFredholm/Unitriangular.lean`, `PhD/TateFredholm/BlockMap.lean`,
> `PhD/LWX/{AmiceValuation,PowSubOne,AmiceBasis,HaloWeightH,DiscModel,DiscForms,SeamH,QuaternionicH}.lean`.

Step I's mathematical content lands squarely inside four of those:

| Step I ingredient | Where it must live | Owner |
|---|---|---|
| classical subspace `S^D_{k+2}(K^p Iw_{p^m};ψ)` = locally-polynomial functions of degree ≤ k | `DiscModel.lean` / `AmiceBasis.lean` | seam-m |
| the theta operator `θ^{k+1}` and its `U_p`-intertwining | `DiscForms.lean` (`DiscForms`, `discHeckeOperator`) | seam-m |
| dimension formula (3.21.1) `= (k+1)q⁻¹pᵐt` | disc-model basis count | seam-m |

`AmiceBasis.lean` is additionally seam-m's **current** beastmode focus
(`beastmode_active`: "AB-16 `discEval_colmezToDisc_natCast`").  These files are skeletons
with 136 open tickets and an active `renames.jsonl`; building Step I on their present
statements would be building on sand.

Files Step I would need that are **not** contested: `PhD/LWX/Vertices.lean` (the
`HasUnitBand` target) and `PhD/LWX/TateRiesz.lean` (the `tate-riesz` board finished
2026-09-06; no sentinel remains).

## Reason 2 — Step I is logically downstream of `lwx-seam-m`, not parallel to it

Step I works at the classical weights `χ_k = (k,ψ)` of conductor `q² = p²`
[lwx.txt:1798–1802], i.e. at analyticity level **m = 2**.  The completed `lwx-seam`
board established [LWX, Prop 2.17] only at **m = 1**; `lwx-seam-m` is precisely the board
delivering every `m`.  Step I cannot state its own hypotheses until that lands.

## Reason 3 — under the "no Jacquet–Langlands" constraint, Step I is not fully plannable

This is the finding with the largest consequence, and it is independent of scheduling.

### 3a. LWX Prop 3.22 (Atkin–Lehner) — source proof *is* Jacquet–Langlands

[lwx.txt:1763–1789].  Statement:

> "Proposition 3.22 (Atkin–Lehner). We use α₀(ψ),…,α_{(k+1)q⁻¹pᵐt−1}(ψ) to denote the
> slopes of U_p acting on S^D_{k+2}(K^pIw_{pᵐ},ψ) in non-decreasing order.  Then we have
> α_i(ψ) = k + 1 − α_{(k+1)q⁻¹pᵐt−1−i}(ψ⁻¹)."

Its proof [lwx.txt:1775]:

> "Firstly note that the base change of S^D_{k+2}(K^pIw_{pᵐ};ψ) to ℂ is isomorphic to the
> corresponding classical space of automorphic forms for D.  Since ψ has conductor pᵐ
> while the level structure at p is Iw_{pᵐ}, by **applying Jacquet–Langlands** and [LW12,
> Proposition 2.8], we see that for every automorphic representation π appearing in
> S^D_{k+2}(K^pIw_{pᵐ};ψ), its p-component π_p is a principal series …"

No Jacquet–Langlands-free proof of this was found in the references available locally
(Buzzard 2004 and 2007, Johansson–Newton, Bellaïche, Loeffler, Pollack, Dembélé).
Dembélé's "perfect pairing" (`dembele.txt:990`) is the weight-2 forms ↔ `Div(X)` duality
giving transposes of Brandt matrices — Hecke *adjointness*, not the Atkin–Lehner
relation.  The repo's own `W`-identification in `PhD/JacobsSlash` is the **diamond**
operator `μ = diag(1,4)` (`B⁻¹WB = diag(1,ω,ω²)`), not an Atkin–Lehner involution.

### 3b. LWX Prop 2.15 (classicality) — one direction is JL-free, the other is not

LWX cites [Bu04, Proposition 4] = Buzzard, *On p-adic families of automorphic forms*.
`references/bu04.txt:1105–1129`:

> "Proposition 4. The kernel of θ^{1−k} is precisely the classical forms
> S^D_k(U₀ ∩ U₁(pⁿ))(ε_p).  Let 0 ≠ f ∈ S^D_κ(U;r) be an eigenvector for U_p with non-zero
> eigenvalue λ.  Then f ∈ S^D_κ(U;1).  Moreover, if v_p(λ) < k−1 then f is classical, and
> if v_p(λ) > k−1 then f is not classical."

**JL-free half** (`bu04.txt:1125–1129`):

> "if v_p(λ) < k − 1 then θ^{1−k}f is in S^D_{κ′}(U;1) and if it is non-zero then it is an
> eigenvector for U_p with eigenvalue λ/p^{k−1}, which has negative valuation.  On the
> other hand, U_p is an operator with norm at most 1, and hence θ^{1−k}f = 0.  Hence f is
> classical."

**JL-dependent half** (`bu04.txt:1122–1124`):

> "If f is classical then one can easily deduce from the classical theory (see for example
> Theorem 4.6.17 of [15], the fact that λ is an algebraic integer, and **the
> Jacquet-Langlands theorem**) that v_p(λ) ≤ k − 1."

([15] = Miyake, *Modular forms*; Thm 4.6.17 is the classical `|a_p|² = p^{k−1}` at
ramified nebentypus.)

Step I needs **both** halves: to say the classical slopes are *exactly* the first `n_{k+1}`
overconvergent slopes one needs small-slope ⟹ classical *and* classical ⟹ slope ≤ k+1.

---

## What Step I actually reduces to (useful even though the board wasn't written)

Reading [lwx.txt:1807–1846], Step I is a **squeeze**, not a computation:

1. Cor 3.18 (lower bound polygon) applies to *both* `ψ` and `ψ⁻¹`, giving
   `Σ(first n_{k+1} slopes) ≥ (k+1)²qt/2` for each.
2. Prop 3.22 pins the *total* over `ψ ⊕ ψ⁻¹` at `(k+1)²qt`.
3. Hence both inequalities are equalities — which is the touching at
   `P_k = (n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`.

Ingredient (1) is **already done** (`lwx-halo` board, complete 2026-09-04) and is the
`isNewtonPolygonOf_specCharSeries` / lower-bound layer consumed by `Vertices.lean`.
Ingredient (3) is elementary given (1) and (2).  The dimension input (3.21.1)
[lwx.txt:1755–1760] is an elementary disc-model count, JL-free.

So the entire JL dependency of Step I concentrates in **one statement**:

> `det(U_p | S(ψ)) · det(U_p | S(ψ⁻¹)) = p^{(k+1)·n}`, `n = dim = (k+1)q⁻¹pᵐt`
>
> equivalently `U_p ∘ U'_p = p^{k+1}` on the classical space, where
> `U'_p = [Iw diag(p,1) Iw]` and `w = (0,1;−pᵐ,0)` conjugates `U_p ↔ U'_p` and
> `ψ ↔ ψ⁻¹` (`w⁻¹ diag(1,p) w = diag(p,1)`, verified by hand).

That is the honest API gap.  A JL-free proof plausibly exists via the local double-coset
computation plus character orthogonality at conductor exactly `pᵐ` (the "U_p is invertible
at ramified nebentypus" fact), but **no source stating it was found**, and the
`/develop` quote-or-delete rule forbids ticketing an invented route.

## Options for the user

1. **Wait for `lwx-seam-m`, then plan a board for the JL-free part only** — the theta
   operator, `ker θ^{k+1} =` classical, the `U_p`-intertwining, small-slope ⟹ classical,
   (3.21.1), and the squeeze — leaving the determinant identity above as an explicit
   hypothesis (the established `HasUnitBand` / `hClassNumberOne` pattern).  This turns
   Step I from "out of scope" into "one determinant identity away".
2. **`/expert-review`** the determinant identity, asking specifically for a
   Jacquet–Langlands-free and Petersson-free proof for definite quaternion algebras.
3. **Accept JL as a hypothesis** and plan the full Step I conditional on it.

---

# Future work — the dependency ledger (added 2026-09-07)

Recorded while writing the blueprint chapters for this development
(`blueprint/src/chapter/LWXSlopes.tex`, §"The dependency ledger", label `sec:ledger`; the
narrative version is §"What Theorem 1.5 says, and what §4 proves", label `sec:what-15-says`).
Keep the two in sync: this file is the board's record, the blueprint is the public rendering.

## The finding that prompted this

The natural assumption — that **Step I + Step III gives the whole of [LWX] Theorems 1.3 and 1.5
modulo the geometric decomposition** — is **false**, and the error is easy to make.  Reading
[LWX, §3.23] and [LWX, §4.2] side by side:

* **Step I** [lwx.txt:1807–1846] supplies the touching, from Prop 3.22 (Atkin–Lehner) + Prop 2.15
  (classicality) + (3.21.1) (the dimension count), at classical weights `χ_k = (k,ψ)` of
  conductor **`q² = p²`** [lwx.txt:1798–1802].
* **Step II** [lwx.txt:1883–2013] is the vertex analysis.  **Done** (`Vertices.lean`,
  `UpperPolygon.lean`, `Claim.lean`, `SlopeRatios.lean`, `SlopeGrowth.lean`, `SlopesSeam.lean`).
* **Step III** [lwx.txt:2014–2098] computes **only the degrees** `deg X_{I,ω}` in terms of
  `r_ord`, using Cor 3.21 (Hida) and the theta exact sequence
  `0 → S^D_{k+2} → S^{D,†}_{(k,ψ)} --(d/dz)^{k+1}--> S^{D,†}_{(−k−2,ψ)} → 0`, **including its
  right-exactness** (= H2 of `JL-AUDIT.md`).
* **The second half of Thm 1.5** [lwx.txt:2295–2360] — (1.5.2), the arithmetic progressions —
  **uses neither Step III nor the theta operator**.  It re-uses Step I's two inputs, but at
  conductor **`p^M`** for `M` with `p^{−q/p^{M−1}(p−1)} > λ`, and then it is bookkeeping:
  the classical slopes at `(k,ψ)` are `q²p^{−M}·α̃_i(ψ|_Δ·ω₀^k)`, Atkin–Lehner reverses them
  against `ψ⁻¹`, and substituting `ψ ↦ ψω₀⁻¹`, `k ↦ k+1` gives (4.2.5), hence (4.2.6)
  `α̃_{j+q⁻¹p^M t}(ωω₀²) = α̃_j(ω) + p^M/q²`; `ω₀^{φ(q)} = 1` then iterates it into the
  progressions.

Confirmed by [LWX, Remark 1.6(4)] (`lwx.txt:247–249`): *"The second half of Theorem 1.5 follows
from the first half by classicality results and Atkin–Lehner theory.  This argument was
independently found by J. Bergdall and R. Pollack [BP15+]."*  Classicality and Atkin–Lehner —
not theta, not the degree formulas.

## Ledger

| Target | Input required | Status |
|---|---|---|
| `HasUnitBand D ω k` for all `k`; hence the **unconditional** form of everything already proved (`unitSlope_specCharSeries_eq_iff`, `unitSlope_specCharSeries_eq_slopeRatio`, `SlopesSeam.lean`) | Step I at conductor `q²`: Prop 2.15, Prop 3.22 (**H1**), (3.21.1), plus the initial-segment comparison | the single hook; `hasUnitBand_of_height_discHeckeCharPowerSeries_eq` is built to receive it |
| [LWX, Thm 1.3]'s degree formulas `deg X_{n,ω} = r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n})` | Step III: Cor 3.21 (Hida) + theta right-exactness (**H2**) | not formalised; H2 is the JL half of [Bu04, Prop 4] |
| [LWX, Thm 1.5] **second half**, (1.5.2) | Step I's inputs at conductor `p^M` for **every** admissible `M`, plus statements ranging over the `ω₀²`-orbit of nebentypi | not formalised; **not implied by Steps I and III as such** |
| `Spc^{>λ}_{D,ω} = ∐_i Y_{i,ω}` finite flat | rigid analytic geometry | out of scope for the thesis (eigenvarieties excluded by the blueprint introduction) |

Two properties of the third row worth keeping in view:

1. (1.5.2) is a statement about `α̃`, the slope-ratio sequence **counted with multiplicity** —
   i.e. about `LWX.slopeRatio`, which is already that sequence (`slopeRatio D ω j = φ(q)·α̃_j(ω)`).
   So it is a **polygon-level** statement and needs **none** of the rigid geometry of row 4.  It
   is a legitimate, statable Lean target today.
2. It nevertheless compares `ω` with `ωω₀²`, whereas every result in `PhD/LWX/` is proved at a
   single fixed `ω`.  No periodicity statement can currently even be *phrased*.

## The five objects that would have to be built

None exists yet.  Items 1–4 are Steps I and III; item 5 is the extra layer the second half of
Thm 1.5 needs on top of them.

1. **The classical space** `S^D_{k+2}(K^p Iw_{p^m}; ψ)` itself, at every `m`.  `Theta.lean`'s
   scope note already records this: "That space does not exist in Lean yet — it is built by the
   theta layer on the companion board — so the assembly here is stated for abstract matrices."
   The *overconvergent* side is available at every analyticity level
   (`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`, `lwx-seam-m`, complete); its classical
   subspace is not.
2. **H1's discharge**: `U_p ∘ U'_p = p^{k+1}` on the classical space, the standing hypothesis of
   `PhD/LWX/AtkinLehner.lean`.  See `JL-AUDIT.md` §1; no source found.
3. **`Theta.lean`'s remaining sorries** (10 as of 2026-09-07) and the `U_p` intertwining
   `θ U_p = p^{k+1} U_p θ`, by summing `thetaDisc_comp_discSlash` over the coset decomposition
   (recorded as T-AG2 on the `lwx-theta` board).  For Step III specifically, also **H2**, the
   right-exactness of the theta sequence.
4. **The initial-segment comparison (AG3)**: that a finite-dimensional `U_p`-stable summand
   contributes an *initial segment* of the Newton polygon.  This is what turns
   `TateFredholm.charPowerSeries_eq_mul_polynomial` (`FiniteFactor.lean`, 1 sorry) from a
   factorisation of the determinant into a statement about slopes, and it is what Step I needs to
   read "the classical slopes are the first `n_{k+1}`" off the polygon.
5. **A nebentypus-varying layer.**  The halo weight at the *classical* weights `(k,ψ)` with
   `cond ψ = p^M`; the computation `v(T_{(k,ψ)}) = q/((p−1)p^{M−1})` placing them in the small
   annulus `0 < v(T) < 8/((p²−1)t+8)`; and statements indexed by `ψ|_Δ·ω₀^k` rather than by one
   `ω`.  `PhD/LWX/ConjChar.lean` supplies `ω⁻¹` (3 sorries); the `ω₀²`-twist has no counterpart.
   [LWX, Cor 1.4]'s periodicity of `deg X_{I,ω}` modulo `φ(q)/2` needs the same layer.

## Consequence for planning

The options in the previous section are unchanged, but the *payoff* of each is now explicit:

* Option 1 (JL-free part only, H1 as hypothesis) buys **row 1** of the ledger — which is the
  whole conditional development becoming unconditional.  That is the highest-value single move
  and should be planned first.
* Adding H2 buys **row 2**.
* **Row 3 is a separate project** and should get its own board when the time comes; do not
  fold it into a Step I board on the assumption that it comes for free.
