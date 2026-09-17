# Jacquet–Langlands audit for [LWX, Theorem 1.3], Steps I and III

**Standing requirement (user, 2026-09-06).** Every board in this development must say, for each
classical result it imports, whether that result's *source proof* uses Jacquet–Langlands, and if
so how we avoid it.  Where the avoidance is not yet a concrete method, say so plainly rather than
implying a route exists.  Cite this file from each board's `plan.md`.

References cited by locator: `.mathlib-quality/tate-riesz/references/lwx.txt` (Liu–Wan–Xiao,
arXiv:1412.2584v4) and `.mathlib-quality/lwx-stepone/references/bu04.txt` (Buzzard, *On p-adic
families of automorphic forms*, Progr. Math. 224 (2004), 23–44).

---

## Summary

Every occurrence of Jacquet–Langlands in the two sources was enumerated by grep.  There are
**exactly two load-bearing uses**, and they exist for the *same reason*: to import the classical
Atkin–Lehner pseudo-eigenvalue theory from `GL₂/ℚ`, where it lives, onto the quaternionic side,
where we work.  The remaining occurrences are motivational or concern transferring LWX's
conclusions elsewhere, and are not consumed by Theorem 1.3.

**Consequence worth stating up front: the single hypothesis H1 removes both.**  Once the
Atkin–Lehner slope symmetry is assumed, the second load-bearing use becomes derivable, so no
separate assumption is needed for it.

| # | Result | Source locator | Load-bearing? | Status |
|---|---|---|---|---|
| 1 | LWX Prop 3.22, Atkin–Lehner slope symmetry | `lwx.txt:1763–1789` | **yes** | H1, hypothesis; avoidance **not yet concrete** |
| 2 | Buzzard Prop 4, second half | `bu04.txt:1122–1124` | **yes** | avoided **concretely**, derived from H1 |
| 3 | Buzzard Thm 2, JL/Shimizu/Arthur isomorphism | `bu04.txt:672–684` | only via #2 | not imported once #2 is derived from H1 |
| 4 | LWX Rmk 1.7(1), Chenevier's p-adic JL | `lwx.txt:228` | no | transfers LWX's results to elliptic forms; outside our scope |
| 5 | Buzzard intro remarks | `bu04.txt:100`, `440–442` | no | motivational |

---

## 1. LWX Proposition 3.22 (Atkin–Lehner) — load-bearing, avoidance not yet concrete

Statement, `lwx.txt:1763–1768`:

> "Proposition 3.22 (Atkin–Lehner). We use α₀(ψ),…,α_{(k+1)q⁻¹pᵐt−1}(ψ) to denote the slopes of
> U_p acting on S^D_{k+2}(K^pIw_{pᵐ},ψ) in non-decreasing order.  Then we have
> α_i(ψ) = k + 1 − α_{(k+1)q⁻¹pᵐt−1−i}(ψ⁻¹)."

The Jacquet–Langlands step, `lwx.txt:1773–1780`:

> "Firstly note that the base change of S^D_{k+2}(K^pIw_{pᵐ};ψ) to ℂ is isomorphic to the
> corresponding classical space of automorphic forms for D.  Since ψ has conductor pᵐ while the
> level structure at p is Iw_{pᵐ}, by **applying Jacquet–Langlands** and [LW12, Proposition 2.8],
> we see that for every automorphic representation π appearing in S^D_{k+2}(K^pIw_{pᵐ};ψ), its
> p-component π_p is a principal series of GL₂(ℚ_p) whose corresponding two characters of ℚ_p^×
> are unr(α) and unr(α⁻¹)⊗ω_p …  In conclusion, one can pair the U_p-eigenvalues of
> S^D_{k+2}(K^pIw_{pᵐ};ψ) and the U_p-eigenvalues of S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹) so that they
> multiply to p^{k+1}."

**How we avoid it.**  We do not.  Proposition 3.22 is taken as hypothesis **H1**, stated in the
full symmetry form above rather than the weaker slope-sum form, because Step III reads off the
end-of-range multiplicities while Step I needs only the total.

**The intended eventual discharge, and its honest status.**  The plan is to reduce H1 to a single
operator identity on the classical space:

> `U_p ∘ U'_p = p^{k+1}`,  where `U'_p = [Iw_{pᵐ} diag(p,1) Iw_{pᵐ}]`.

The reduction rests on the Atkin–Lehner element `w = (0, 1; −pᵐ, 0)`, which normalises `Iw_{pᵐ}`,
conjugates `U_p` to `U'_p`, and inverts the nebentypus.  The conjugation `w⁻¹ diag(1,p) w =
diag(p,1)` was verified by hand in session.  **This reduction is the board's own work and is
concrete.**  Given the operator identity, the slope symmetry follows by taking determinants and
transporting along `w`.

What is **not** concrete is the operator identity itself.  The expected argument is a local
double-coset computation: expanding `U_p U'_p` over coset representatives leaves, besides the
central term, contributions that are traces from level `pᵐ⁻¹`, and these vanish by character
orthogonality precisely because the conductor is exactly `pᵐ`.  This is the standard fact that
`U_p` is invertible at ramified nebentypus.  **No source stating it in the quaternionic or
algebraic-modular-forms setting was found** in the references available locally (Buzzard 2004 and
2007, Johansson–Newton, Bellaïche, Loeffler, Pollack, Dembélé).  The natural local reference to
chase is Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973); Gross,
*Algebraic modular forms*, is the other candidate.  Failing that, the reduced statement is what
goes to `/expert-review`.

Per the `/develop` quote-or-delete rule, the double-coset argument must **not** be ticketed until
a source is found or a reviewer confirms it.  Ticket the reduction; hypothesise the identity.

## 2. Buzzard Proposition 4, second half — load-bearing, avoided concretely

LWX Prop 2.15 (`lwx.txt:913–920`) is cited to [Bu04, Proposition 4].  Buzzard's proof splits.

**First half is already Jacquet–Langlands-free** (`bu04.txt:1125–1129`):

> "if v_p(λ) < k − 1 then θ^{1−k}f is in S^D_{κ′}(U;1) and if it is non-zero then it is an
> eigenvector for U_p with eigenvalue λ/p^{k−1}, which has negative valuation.  On the other hand,
> U_p is an operator with norm at most 1, and hence θ^{1−k}f = 0.  Hence f is classical."

We formalise this directly.  It is the theta argument, and it is the reason the theta layer is
shared infrastructure rather than a Step III input.

**Second half uses Jacquet–Langlands** (`bu04.txt:1122–1124`):

> "If f is classical then one can easily deduce from the classical theory (see for example Theorem
> 4.6.17 of [15], the fact that λ is an algebraic integer, and **the Jacquet-Langlands theorem**)
> that v_p(λ) ≤ k − 1."

([15] is Miyake, *Modular forms*; Thm 4.6.17 is the classical `|a_p|² = p^{k−1}` at nebentypus of
conductor equal to the level.  The Jacquet–Langlands input is Buzzard's own Theorem 2, item 3
below, transferring that from `Γ₁(M)`-forms to `S^D`.)

**How we avoid it — concretely.**  We never import this half.  Under H1 the slopes satisfy
`α_i(ψ) = k+1 − α_{n−1−i}(ψ⁻¹)`, and `U_p` has operator norm at most 1 so every slope is
non-negative; hence `α_i(ψ) ≤ k+1` for all `i`, which is exactly the second half.  Note Buzzard's
weight convention `k` is LWX's `k+2`, so his `k−1` is our `k+1`.

This is why classicality is **not** a hypothesis of this development, and why hypothesising it
alongside H1, as an earlier proposal suggested, would have been redundant.

## 3. Buzzard Theorem 2 — reached only through item 2

`bu04.txt:672–684`:

> "Theorem 2 (Jacquet-Langlands, Shimizu, Arthur).  If k ≥ 3 then the space S^D_k(U₁(M)) is
> isomorphic to the space S^{δ-new}_k(Γ₁(M) ∩ Γ₀(δ)) of classical δ-new forms, and this isomorphism
> commutes with the action of the standard Hecke operators defined above. …
> Proof.  This is a 'concrete' realisation of the Jacquet-Langlands theorem …"

Buzzard uses it for two things: the transfer in item 2, and attaching Galois representations to
eigenforms.  We need neither.  Once item 2 is derived from H1, Theorem 2 is not imported at all.

## 4. LWX Remark 1.7(1), Chenevier — not load-bearing

`lwx.txt:228–232`:

> "By G. Chenevier's p-adic Jacquet–Langlands correspondence [Ch05], we can translate results from
> the case of automorphic forms for definite quaternion algebras to the case of modular forms, and
> hence prove a large portion of Conjecture 1.2."

This runs in the opposite direction: it exports LWX's quaternionic theorems to elliptic modular
forms.  Theorem 1.3 does not consume it, and we do not formalise Conjecture 1.2.

---

## The other hard input, for contrast: not a Jacquet–Langlands issue

Hypothesis **H2**, right-exactness of the theta sequence, is cited by LWX at `lwx.txt:2049` to

> "[Jo11] O. Jones, *An analogue of the BGG resolution for locally analytic principal series*,
> Journal of Number Theory."

This is locally analytic representation theory, not Jacquet–Langlands.  It is recorded here only
so that no board mistakes it for one.  Step III needs it; Step I does not.  Because the disc model
is now built, a direct argument there should be attempted before importing BGG machinery.

**Addendum (2026-09-07).**  The same is true of the *second half* of [LWX, Thm 1.5] — (1.5.2),
the arithmetic progressions.  Its derivation [lwx.txt:2295–2360] uses classicality and
Atkin–Lehner only, so it needs **H1 but not H2**, and it does not use Step III's degree formulas
at all.  What it needs instead is Step I's inputs at conductor `p^M` for every admissible `M`,
plus statements ranging over the `ω₀²`-orbit of nebentypi.  See `FINDINGS.md`,
§"Future work — the dependency ledger", and the blueprint's
`blueprint/src/chapter/LWXSlopes.tex` §`sec:ledger`.

**Addendum (2026-09-10, board `lwx-theta-h2`).**  Hypothesis H2 **is discharged** by the direct
disc-model argument this section asked for (`LWX.isThetaExact_of_isClassicalShape` and
`LWX.isThetaExact_classicalData`, both sorry-free, standard axioms).  `PhD/LWX/ThetaExact.lean` writes
`θ^{k+1} = D ∘ σ` (diagonal of falling factorials after a coordinate shift), composes Buzzard's
elementary intertwining `θ^{k+1}∘U_p = p^{k+1}U_p'∘θ^{k+1}` (`bu04.txt:1093–1096`) with the
section `τ` of the shift, and reads the result as a diagonal intertwining of matrix coefficients
— which `TateFredholm.charPowerSeries_eq_of_diag_intertwine` turns into the determinant identity
`IsThetaExact` states.  Neither [Jo11] nor any exactness of spaces is imported; there is no
Jacquet–Langlands input.  The deliverable `LWX.degX_succ_classicalPoint` therefore depends on
**H1 alone**, as item 1 above anticipated.  With it, the only Jacquet–Langlands-shaped input left
in the whole Step I / Step III development is item 1 (LWX Prop 3.22 = H1), whose avoidance is
still "not yet concrete".

**Addendum (2026-09-10, board `lwx-h1` — planned, not yet executed).**  Item 1's avoidance is now
**concrete and ticketed**.  The board `.mathlib-quality/lwx-h1/` proves H1 at the classical points
by the elementary double-coset expansion that §1 above anticipated, whose matrix identities were
verified sorry-free in `PhD/Test/AtkinLehnerIdentity.lean`: with `W` the Atkin–Lehner map on the
classical disc forms of `(k, ψ)` at level `Iw_p`, conductor `p²`,

> `U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}`  (`LWX.discHeckeCl_comp_atkinLehner`, Part I),

so that `B := W⁻¹ U_p^{(ψ⁻¹)} W` satisfies both clauses of `AtkinLehnerHypothesis`
(`LWX.atkinLehnerHypothesis_of_atkinLehnerData`) and [LWX, Thm 1.3]'s degree formula follows with
no hypothesis left (`LWX.degX_succ_of_atkinLehnerData`).  The two ingredients LWX's proof
obtains from the automorphic representation are taken as *data* of the abstract group
(`LWX.AtkinLehnerData`): the central Hecke character `χ` of `lwx.txt:1783–1785` ("twist the
representation π by a central Hecke character associated to ψ⁻¹") and the triviality of the
central element `p_p` on the level (`p_p = p_global · (p^{(p)})⁻¹`), together with a section of
the `p`-component and the normalisation of the disc-`0` level by `w`.  For the definite
quaternion algebra these are theorems of class field theory and of the shape of `K^p·Iw_p`,
**not** of Jacquet–Langlands; instantiating them for `Dfx ℚ D` is a separate board.  The
classical statement the identity establishes is Miyake Thm 4.6.17 as cited at `bu04.txt:1122`,
whose proof is not used.  **On completion of `lwx-h1`, no result of the Step I / Step III
development depends on Jacquet–Langlands, granted the adelic data.**  Until then item 1 stays
"hypothesis, avoidance concrete and ticketed".

**Addendum (2026-09-10, board `lwx-h1` — EXECUTED).**  Item 1 is now **avoided concretely**.
`LWX.atkinLehnerHypothesis_of_atkinLehnerData` proves hypothesis H1 at the classical points and
`LWX.degX_succ_of_atkinLehnerData` gives [LWX, Thm 1.3]'s degree formula with no hypothesis
left, both sorry-free with standard axioms.  The proof is the double-coset expansion
`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` (`LWX.discHeckeCl_comp_atkinLehner`); no
Jacquet–Langlands input is used anywhere.  What remains assumed is the adelic data bundled in
`LWX.AtkinLehnerData` (a section of the `p`-component, the central `p` acting trivially on the
level, the Hecke character `ψ_A ∘ ν`, and `w` normalising the disc-`0` part of the level) together
with neatness and the certificates — all statements about `D^×` and its level provable by class
field theory and the shape of `K^p·Iw_p`, not by Jacquet–Langlands.  With this, the Step I /
Step III development contains **no** Jacquet–Langlands dependency, granted that data.

**Addendum (2026-09-11, board `lwx-conductor` — EXECUTED).**  [LWX, Prop 3.22] at **every**
conductor `p^{h+1}`, `h ≥ 1`, is avoided concretely: `LWX.atkinLehnerHypothesis_of_atkinLehnerDataH`
proves hypothesis H1 at the classical points of conductor `p^{h+1}` from the level-`h` adelic data
`LWX.AtkinLehnerDataH`, by the same double-coset expansion as at level `1`
(`LWX.discHeckeClH_comp_atkinLehnerH`, with `w_h = (0 p^h; −p 0)` and the factorisation
`w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b p^{h−1}}`); the non-central terms cancel because the
conductor is exactly `p^{h+1}` (`LWX.isPrimitiveRoot_nebCharH_oneAddPPowMul_one`,
`LWX.sum_inv_nebCharKH_eq_zero`).  The slope identification of [LWX, §4.2] ("the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)` are …") is done **without Prop 2.15**: the classical factor's slopes
are `≤ k+1` by H1 and `‖U_p‖ ≤ 1`, the complement's are `≥ k+1` through the theta target
(`LWX.unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH`).  The slope reflection
(`LWX.slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH`), (4.2.5)
(`LWX.slopeRatio_partnerChar_succ`), (4.2.6) = (1.5.2) (`LWX.slopeRatio_mul_teichChar_sq`) and
the arithmetic progressions of [LWX, Thm 1.5] (`LWX.slopeRatio_add_period`) follow with no
hypothesis beyond the adelic data families `LWX.AtkinLehnerFamily` / `LWX.AtkinLehnerFamilyH`
(class field theory and the shape of the level for `D^×`, not Jacquet–Langlands).  No
Jacquet–Langlands input is used anywhere on the board.

**Addendum (2026-09-11, board `lwx-degrees` — EXECUTED).**  [LWX, Thm 1.3]'s degree formulas at
every classical weight and [LWX, Cor 1.4] add **no** new input.  They are the level-`1` gap lemmas
of `StepThree.lean` (H2 = `LWX.isThetaExact_classicalData`, JL-free) with H1 from the adelic data
(`LWX.atkinLehnerHypothesis_of_atkinLehnerData`, JL-free), applied at the family
`LWX.AtkinLehnerFamily` (`LWX.degX_succ_of_atkinLehnerFamily`, `LWX.degXint_of_atkinLehnerFamily`,
`LWX.degXint_pos_of_atkinLehnerFamily`), followed by character algebra in `(ZMod p)ˣ →* ℤ_[p]ˣ`
(`LWX.degX_succ_mul_teichChar_sq`, `LWX.degXint_mul_teichChar_sq`, `LWX.degX_succ_add_period`,
`LWX.degXint_add_period`).  No Jacquet–Langlands input is used anywhere on the board.

**Addendum (2026-09-14, board `lwx-quaternion` — EXECUTED).**  Two assumptions of the adelic data are
removed and the data are instantiated for `D/ℚ`, still with **no** Jacquet–Langlands input.
(1) The field `AtkinLehnerData.central` (the tame scalar `p^{(p)}` lies in the level — false for
[LWX]'s neat levels in general) is replaced by `ιp_pGL_comm` and `central_pow`; hypothesis H1 now
reads `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z` with `Z` the tame central operator
(`LWX.translateOp`, `LWX.centralOpCl`, finite order and commuting with `U_p`), proved by the same
double-coset expansion (`LWX.discHeckeCl_comp_atkinLehner`, `LWX.atkinLehnerHypothesis_of_atkinLehnerData`
and their level-`h` twins).  The eigenvalue statement is the norm-multiset pairing
(`Matrix.norm_roots_charpoly_of_mul_eq_smul_mul`, via semisimplicity of `Z` and
`Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top`); the classical form
`a_p(f)·a_p(f|W) = χ_M(p)·p^{k+1}` (Miyake, Thm 4.6.17, cited at `bu04.txt:1120–1124`, which also
invokes Jacquet–Langlands) is **cited, not used**.  (2) The determinant certificate `det(u_{i,t} v_t) = p`
is proved from normalised class representatives (`LWX.QuaternionInput.det_certM1_eq`).  (3) For a
definite quaternion algebra over `ℚ` split at `p`, `LWX.QuaternionInput` (tame level, norm class,
normalised neat representatives) yields `LWX.QuaternionInput.atkinLehnerFamily`/`…H`, the `U_p`-datum,
and the headline theorems (`LWX.QuaternionInput.hasUnitBand`, `degX_succ`, `degXint_eq`, `degXint_pos`,
`degX_succ_add_period`, `degXint_add_period`, `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio`,
`slopeRatio_add_period`).  The inputs of `QuaternionInput` are the reduced norm's properties,
Hasse–Schilling–Maass plus weak approximation (Voight Thm 14.7.4, §28.5) and neatness — none is
Jacquet–Langlands.

