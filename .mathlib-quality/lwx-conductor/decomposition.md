# Decomposition — `lwx-conductor` (Step I / H1 at conductor `p^{h+1}`, and the slope reflection)

**BOARD PATH: `.mathlib-quality/lwx-conductor/`.**  Companion to `plan.md`; read both before working
a ticket.  Written 2026-09-11, after the adversarial planning pass.  References by locator:
`lwx.txt` = `.mathlib-quality/tate-riesz/references/lwx.txt`, `bu04.txt` =
`.mathlib-quality/lwx-stepone/references/bu04.txt`; level-`1` code by `File.lean:line`.

## 0. The goal, and what the sources actually say

**Targets** (`plan.md`): `atkinLehnerHypothesis_of_atkinLehnerDataH` (H1 at level `h`, **M1**),
`slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerDataH` (the slope reflection, **M2**), plus
`isStepOneTouching_of_atkinLehnerHypothesisH` (Step I at level `h`) and
`hasUnitBand_of_atkinLehnerData` (ledger row 1 at level `1`).

**The source statement of M2** — [LWX, §4.2], `lwx.txt:2322–2350`:

> "Let ψ be a character of conductor p^M. We look at weights of the form (k, ψ) for all k ≥ 0.
> First, note that v(T_{(k,ψ)}) = q/ϕ(p^M) = q/((p−1)p^{M−1}) by the assumption on M; thus
> (k,ψ) ∈ W^{>λ}_{ψ|Δ·ω₀^k}. Noting the equality q/((p−1)p^{M−1})·ϕ(q) = q²p^{−M}, it then follows
> that the U_p-slopes of S^D_{k+2}(K^p Iw_{p^M}, ψ) are q²p^{−M}α̃_0(ψ|Δ·ω₀^k), …,
> q²p^{−M}α̃_{(k+1)q^{−1}p^M t−1}(ψ|Δ·ω₀^k). Hence, by Atkin–Lehner theory (Proposition 3.22),
> in the U_p-slope sequence on S^D_{k+2}(K^p Iw_{p^M}; ψ^{−1}), from the (kq^{−1}p^M t+1)st to the
> (k+1)q^{−1}p^M t-th is given by k+1 − q²p^{−M}α̃_{q^{−1}p^M t−1}(ψ|Δ·ω₀^k), …,
> k+1 − q²p^{−M}α̃_0(ψ|Δ·ω₀^k). This implies the relations
> α̃_{(k+1)q^{−1}p^M t−1−i}(ψ^{−1}|Δ·ω₀^k) = q^{−2}p^M(k+1 − q²p^{−M}α̃_i(ψ|Δ·ω₀^k))
> = (k+1)q^{−2}p^M − α̃_i(ψ|Δ·ω₀^k) for 0 ≤ i ≤ q^{−1}p^M t − 1."

**"The assumption on M"** — [LWX, Thm 1.5], `lwx.txt:181–186`:

> "let M be a positive integer so that p^{−q/p^{M−1}(p−1)} > λ; we also require M ≥ 2 if p is odd
> and M ≥ 4 if p = 2."  with (`lwx.txt:179–180`) "if the tame level is neat, then we can take
> λ = p^{−8/((p²−1)t+8)} for p > 2".

**The classical points and their valuation** — [LWX, §2.1], `lwx.txt:462–478`:

> "a continuous character ψ : Z_p^× → E^× … is called a finite character of conductor p^m if it
> factors through (Z/p^mZ)^× but not (Z/p^{m−1}Z)^×. We say a continuous character χ of Z_p^× is
> classical if it sends x to x^k ψ(x) for an integer k ≥ 0 and a finite character ψ of conductor
> p^m. … (when p > 2) v(T_{(k,ψ)}) ≥ 1 if m = 1, and v(T_{(k,ψ)}) = 1/p^{m−2}(p−1) if m ≥ 2".

**The dimension** — [LWX, (3.21.1)], `lwx.txt:1755–1760`:

> "Let m ∈ N_{≥2}, and let ψ be a finite character of conductor p^m. For k ∈ Z_{≥0}, using an
> isomorphism analogous to (2.11.1), we see that S^D_{k+2}(K^pIw_{p^m}; ψ) is isomorphic to the
> direct sum of t copies of LP^{m−v(q),deg≤k}(Z_p; E). So in total,
> (3.21.1) dim S^D_{k+2}(K^pIw_{p^m}; ψ) = (k + 1)q^{−1}p^m t."

**Atkin–Lehner at conductor `p^m`** — [LWX, Prop 3.22], `lwx.txt:1763–1768`:

> "We use α₀(ψ), …, α_{(k+1)q^{−1}p^mt−1}(ψ) to denote the slopes of U_p acting on
> S^D_{k+2}(K^pIw_{p^m}, ψ) in non-decreasing order. Then we have
> α_i(ψ) = k + 1 − α_{(k+1)q^{−1}p^mt−1−i}(ψ^{−1}) for i = 0, …, (k+1)q^{−1}p^mt − 1."

whose proof (`lwx.txt:1770–1789`) is Jacquet–Langlands and is not transcribed (see `lwx-h1`'s
`decomposition.md` §0); what is transcribed is the pairing `(k,ψ) ↔ (k,ψ⁻¹)` with product
`p^{k+1}` and the twist by a central Hecke character.

**Classicality** — [LWX, Prop 2.15], `lwx.txt:913–920` — is what [LWX] use for "it then follows
that the U_p-slopes … are the first (k+1)q^{−1}p^Mt ratios":

> "Let χ = (k,ψ) : Z_p^× → E^× be a classical character of conductor p^m. Let 0 ≠ ϕ ∈ S^{D,†}_χ be
> an eigenvector for U_p with non-zero eigenvalue λ. If v(λ) < k + 1, then ϕ is classical, i.e.
> ϕ ∈ S^D_{k+2}(K^pIw_{p^m};ψ). If v(λ) > k + 1, then ϕ ∉ S^D_{k+2}(K^pIw_{p^m};ψ)."

It is **not used** here (its proof is [Bu04, Prop 4], half of which is Jacquet–Langlands): the
identification of the classical slopes with the first `N` overconvergent slopes is done as in
`Touching.lean`/`StepThree.lean` — classical slopes `≤ k+1` (H1 + `‖U_p‖ ≤ 1`), complement slopes
`≥ k+1` (theta intertwining), product polygon.

**Step I at conductor `q²`** — [LWX, §3.23], `lwx.txt:1794–1846` — is the template for Step I at
level `h`; the arithmetic (3.23.1) (`lwx.txt:1826–1838`) computes `λ((k+1)qt)·v(T_{χ_k}) =
(k+1)²qt/2`, which at conductor `p^{h+1}` becomes `λ((k+1)p^h t)·v(T) = (k+1)²p^h t/2` (T-b below).

## 1. The prose proof (the route the tickets transcribe)

Fix `h ≥ 1`, a nebentypus `ψ` of conductor `p^{h+1}`, `ζ := ψ(exp p)` a primitive `p^h`-th root
of unity, `k ≥ 0`, `T₀ := ζ·exp(pk) − 1 = classicalPoint p k ζ`, `N := t(k+1)p^h`.

**(a) The point.**  `‖ζ − 1‖^{ϕ(p^h)} = ‖p‖` (`Φ_{p^h}(1) = p`), so `p⁻¹ < ‖T₀‖ = ‖ζ − 1‖ < 1`;
`(1+T₀)^{p^h} − 1 = exp(p^{h+1}k) − 1` (since `ζ^{p^h} = 1`), so `‖T'_h‖ ≤ p^{−(h+1)}` and the
level-`h` halo exponent is `k`; hence the level-`h` halo weight at `T₀` has the classical shape of
exponent `k` with constants `nebCharKH(d) = κ(d)d^{−k}` (`ClassicalPointH.lean`, `classicalDataH`).
Likewise at the target `T₁ = weightPoint p (−k−2) ζ` with exponent `−(k+2)` and the same constants
(`TargetPointH.lean`, `targetData_classicalPointH`).

**(b) The nebentypus.**  `nebCharH(a) = ω(ā)·ζ^{ℓ⟨a⟩ mod p^h}·ω₀(ā)^{−k}` is multiplicative,
trivial on `1 + p^{h+1}ℤ_p`, and `nebCharH(1 + p^h)` is a primitive `p`-th root of unity
(`ℓ⟨1+p^h⟩ = log(1+p^h)/p` has valuation `h − 1`); so `∑_{c<p} nebCharH(1 + bcp^h)^{−1} = 0` for
`p ∤ b`.  At the partner `(ω⁻¹ω₀^{2k}, ζ⁻¹)` the nebentypus is the inverse (`NebCharH.lean`).

**(c) H1 at level `h`.**  In the disc model at level `h` (`p^h` discs, `t_a = (p^h a; 0 1)`), with
`w_h = (0 p^h; −p 0)` (so `t₀⁻¹ w_h t₀ = (0 1; −p^{h+1} 0)`), `w_h (a b; c d) w_h⁻¹ =
(d, −cp^{h−1}; −bp^{1−h}, a)` normalises `{u ∈ Iw_p : p^h ∣ b}`; the Atkin–Lehner map `W`
(`atkinLehnerMapH`) is an isomorphism from the classical forms of `(k,ψ)` to those of `(k,ψ⁻¹)`,
equivariant because `nebK(a)nebK(d) = nebK(det)` on that part (`bc/det ∈ p^{h+1}ℤ_p`).  The key
factorisation `w_h v_b w_h⁻¹ v_c = ℓ_{b,c}·(p·1)·s_{−bp^{h−1}}` with `ℓ_{b,c} = (1 − bcp^h,
−b²cp^{2h−1}; cp, 1 + bcp^h)` gives, on disc `0`, `U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = ∑_{b,c}
nebK(1 + bcp^h)^{−1}·p^k·(disc bp^{h−1} of φ)|n(−b/p) = p^{k+1}φ` by (b).  Transport to the
block matrices at a neat level gives `A B = p^{k+1}`, `A' = W B W⁻¹`: H1
(`AtkinLehnerLocalH/MapH/IdentityH.lean`).

**(d) Step I at level `h`** (consistency): with (3.23.1)-at-level-`h`, `2λ(N)v(T₀) = N(k+1)v(p)`,
and `det A · det A' = p^{(k+1)N}` from H1, the Minkowski bound `height_N ≤ v(det A)` and the lower
bound `λ(N)v(T₀) ≤ height_N` at both points squeeze to equality (`TouchingH.lean`).

**(e) The slope identification.**  In the region `v(T₀) < 8/((p²−1)t+8)` — i.e.
`(p²−1)t + 8 < 8p^{h−1}(p−1)` — the level-`h` slope reading `unitSlope_j(det) = v(T₀)·r_j`
(`r = slopeRatio D ω`) holds for every `j` given `hband`.  The determinant splits as
`R · det(1 − XA)`, the slopes of `det(1 − XA)` are `≤ (k+1)v(p)` (H1: every root `x` of `A` has
`‖x‖ ≥ ‖p‖^{k+1}` because `p^{k+1}/x` is a root of `A'`, of norm `≤ 1`), those of `R` are
`≥ (k+1)v(p)` (`le_unitSlope_compl` with the target of (a)), so the first `N` unit slopes of the
determinant are those of `det(1 − XA)`; the same at the partner (H1 is symmetric).

**(f) The reflection.**  `roots(A') = {p^{k+1}/x}`.  For real `σ`: `#{y ∈ roots(A'^{rev}) : ‖y‖ ≤ e^σ}
= n − #{x ∈ roots(A^{rev}) : ‖x‖ < e^{v(p^{k+1}) − σ}}`, i.e. `faceRight_{A'} σ = n − faceLeft_A
((k+1)v(p) − σ)`; by the face API, `unitSlope_{A'}(n−1−i) ≤ σ ⇔ (k+1)v(p) − unitSlope_A(i) ≤ σ`,
hence `s'_{n−1−i} = (k+1)v(p) − s_i`.

**(g) Assembly.**  `v(T₀) = v(T₀')` (both `= v(p)/(p^{h−1}(p−1))`), so
`v(T₀)·(r'_{N−1−i} + r_i) = (k+1)v(p) = v(T₀)·(k+1)p^{h−1}(p−1)`; divide by `v(T₀) > 0`.

**(h) The unit band at every vertex (the family).**  For a fixed disc `ω` and every `k`, Step I
at level `1` at the classical weight `(ω, k)` (`classicalData ψ ω … k`) and its partner gives
`HasUnitBand D ω (k+1)`; `HasUnitBand D ω 0` is free.  This needs H1 at every `(ω, k)`, hence a
Hecke character `χ ω k` for every `(ω, k)` — `AtkinLehnerFamily`, with one section `ιp` so that
`D = UpDatum.ofCerts … (vRepF F) …` is the same for all `(ω, k)`.  With the family, (e)'s
`hband`, `hband'` are discharged for every disc, in particular for `ω` and `ω⁻¹ω₀^{2k}`.

**(i) (4.2.5)–(4.2.6).**  (g) at `(ω, k)` and at `(ω, k+1)` (same disc, partner discs
`ω⁻¹ω₀^{2k}` and `ω⁻¹ω₀^{2k+2}`, `N_{k+1} = N_k + p^h t`) subtract to
`r_{N_{k+1}−1−i}(ω⁻¹ω₀^{2k+2}) = r_{N_k−1−i}(ω⁻¹ω₀^{2k}) + e`, `e = p^{h−1}(p−1)` — (4.2.5).
Given any disc `ω'` and `j`, put `k := j/(p^h t)`, `ω := ω'⁻¹ω₀^{2k}` (so `ω⁻¹ω₀^{2k} = ω'`),
`i := N_k − 1 − j` (`j < N_k`, `N_{k+1} − 1 − i = j + p^h t`): (4.2.5) reads
`r_{j+p^h t}(ω'ω₀²) = r_j(ω') + e` — (4.2.6) = (1.5.2).  Iterating `m` times:
`r_{j+m p^h t}(ω ω₀^{2m}) = r_j(ω) + m e`; at `m = (p−1)/2`, `ω₀^{p−1} = 1` gives the
arithmetic progressions.

## 2. Leaves, with source locators, Lean ↔ source match, and attacks

Format: leaf → declaration(s); **Source**; **Match**; **Attacks** (each attack tried and its
outcome — an attack that succeeded changed the skeleton before this document was written).

### Part T — `PhD/LWX/TouchingH.lean`

**T-a** `touchX_mul_prime_pow`.
**Source**: `lwx.txt:2340` "(k+1)q^{−1}p^M t" and `lwx.txt:1798` "Put n_k = kqt"; with `q = p`,
`M = h+1`: `(k+1)p^h t = ((k+1)p^{h−1})·pt = n_{(k+1)p^{h−1}}`.
**Match**: `touchX p t K = K * (p * t)` (`UpperPolygon.lean:34`) at `K = (k+1)p^{h−1}`.
**Attacks**: (1) `h = 0`: `p^{0−1} = p^0 = 1` and `(k+1)pt ≠ t(k+1)p^0` — the statement is false at
`h = 0`, hence `hh : 0 < h` is necessary and present. (2) associativity/commutativity only:
`(k+1)p^{h−1}·(pt) = t(k+1)p^{h−1}p`; `pow_succ` needs `h − 1 + 1 = h` (`Nat.sub_add_cancel hh`).
(3) is a new `touchXH` needed? No — every consumer (`IsStepOneTouching`, `HasUnitBand`) is indexed
by the level-`1` vertex index, and this lemma converts; a separate definition would only add a
bridge.

**T-b** `two_mul_lwxLambda_touchX_mul_eq_prime_pow` ((3.23.1) at level `h`).
**Source**: (3.23.1) `lwx.txt:1826–1838`: "when the x-coordinate is (k+1)qt, the y-coordinate of
the lower bound polygon is p/(q(p−1))·λ((k+1)qt) = … = (k+1)²qt/2"; at conductor `p^{h+1}`
`v(T) = 1/(p^{h−1}(p−1))` (`lwx.txt:2323`) and the same computation gives
`λ((k+1)p^h t)·v(T) = (k+1)²p^h t/2 = N(k+1)/2`.
**Match**: `2λ(touchX p t K) = K²p(p−1)t` (`two_mul_lwxLambda_touchX`, ℕ, general `K`) with
`K = (k+1)p^{h−1}`, and `−log‖c‖ = p^{h−1}(p−1)·(−log‖T₀‖)` from `hT` (`Real.log_pow`); then
`K²p(p−1)t·v = (k+1)²p^{2h−1}(p−1)t·v = t(k+1)p^h·(k+1)·p^{h−1}(p−1)v`.
**Attacks**: (1) `h = 0`: `K = k+1`, `2λ = (k+1)²p(p−1)t`, RHS `= t(k+1)·(k+1)·(p−1)·v·… ` — differs by
a factor `p`; false, so `hh` necessary. (2) the ℕ lemma's cast: `push_cast [Nat.cast_sub hp.out.one_le]`
as in the level-`1` proof (`Touching.lean:620–635`). (3) exponent bookkeeping: `p^(h−1)·p^(h−1)·p =
p^(2h−1)` and `p^(h−1)·p = p^h` need `hh`; `pow_succ`/`← pow_add` with `Nat.sub_add_cancel`.

**T-c** `ClassicalDataH` (structure), `weight`, `matrix`, `mul_neg_log_norm_eq`, `norm_eq`,
`ClassicalData.toH`, `toH_matrix`.
**Source**: `lwx.txt:476–478` (`v(T_{(k,ψ)}) = 1/p^{m−2}(p−1)`); `lwx.txt:2323–2325`.
**Match**: `hnorm : ‖T₀‖^{p^{h−1}(p−1)} = ‖ψ p‖`; `shape` at `haloWeightH h`.  `mul_neg_log_norm_eq`
is `Real.log_pow` on `hnorm`; `norm_eq` is injectivity of `x ↦ x^e` on `[0,∞)` for `e ≥ 1`
(`pow_left_injective`/`pow_left_inj₀`); `toH` rewrites `p^(1−1)·(p−1) = p−1` (`pow_zero`, `one_mul`).
**Attacks**: (1) `h = 0` makes `hnorm` the level-`1` condition — harmless (no consumer claims
anything at `h = 0` without `hh`); recorded in `plan.md` design decision 1. (2) `norm_eq` at `h = 0`:
`e = p − 1 ≥ 1` still, so the lemma holds; `hh` is kept for uniformity — **slack** (`_hx`
convention: rename `_hh` at cleanup or keep, note it). (3) `toH_matrix` is `rfl`: `c.toH.weight`
unfolds to `haloWeightH 1 ψ T₀ ω hp2 hψ c.h0 c.h1 c.hT` ≡ `c.weight`, and `shape := c.shape` —
verified by the skeleton build.

**T-d** `isStepOneTouching_of_atkinLehnerHypothesisH`, `hasUnitBand_of_atkinLehnerHypothesisH`.
**Source**: Step I, `lwx.txt:1807–1846`, at conductor `p^{h+1}` (the source runs it at `q²` only;
[LWX, §4.2] does not repeat it — it is not needed there).
**Match**: the level-`1` proof (`Touching.lean:695–770`) verbatim with `1 → h`, `hidx` replaced by
`touchX_mul_prime_pow`, `har` by T-b; `height_le_negLogNorm_det`, `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`,
`lwxLambda_mul_le_height_specCharSeries`, `neg_log_norm_det_add_of_mul_eq_smul`,
`det_ne_zero_of_mul_eq_smul'`, `det_ne_zero_of_mul_eq_smul_conj` are all general in `h`
(checked: `Touching.lean:552` takes `h`; `SeamH.lean:401` takes `h`).
**Attacks**: (1) `hidx`: `card ι * ((k+1) * p^h) = touchX p (card ι) ((k+1)*p^(h−1))` as integers —
T-a cast to `ℤ`. (2) `hsum` uses `Fintype.card_fin` on `Fin (card ι * ((k+1)*p^h))` and
`norm_pow`, `Real.log_pow` on `‖(ψ p)^(k+1)‖` — unchanged. (3) the conclusion is
`IsStepOneTouching … ((k+1)*p^(h−1))`, which `hasUnitBand_of_isStepOneTouching` accepts for any
index — the hand-off compiles in the skeleton (term given).

### Part C — `PhD/LWX/ClassicalPointH.lean`

**C-a** `norm_eq_one_of_pow_eq_one`.  **Source**: none needed.  **Match**: `‖ζ‖^n = 1`, `n ≠ 0`,
`‖ζ‖ ≥ 0` ⇒ `‖ζ‖ = 1` (`pow_eq_one_iff_of_nonneg`).  **Attacks**: (1) `n = 0` excluded (then
`ζ^0 = 1` says nothing) — `hn` present. (2) replaces `norm_of_isPrimitiveRoot` (`ClassicalPoint.lean:108`)
whose hypothesis is `IsPrimitiveRoot ζ p`; `(hζ.pow_eq_one)` bridges. (3) no ultrametricity needed.

**C-b** `norm_sub_one_lt_one_of_norm_pow_sub_one_lt`, `norm_sub_one_lt_one_of_pow_prime_pow_eq_one`.
**Source**: standard (`ζ ≡ 1 mod 𝔪` for `p`-power roots of unity); at level `1` this is
`norm_sub_one_lt_one_of_isPrimitiveRoot` (`ClassicalPoint.lean:51`, via `add_pow` and `p ∣ C(p,i)`).
**Match**: `(ζ − 1)^p − (ζ^p − 1) = ((−1)^p + 1) + ∑_{0<i<p} C(p,i) ζ^i (−1)^{p−i}` (`add_pow` on
`(ζ + (−1))^p`); each middle term has norm `≤ ‖p‖` (`Nat.Prime.dvd_choose_self`, `‖ζ‖ ≤ 1`), and
`(−1)^p + 1 ∈ {0, 2}` has norm `≤ ‖p‖` (`Nat.Prime.eq_two_or_odd'`); so `‖(ζ−1)^p‖ ≤ max(‖ζ^p − 1‖,
‖p‖) < 1` and `‖ζ − 1‖ < 1`.  Then induction on `h`: `h = 0` gives `ζ = 1`; step: `(ζ^p)^{p^h} = 1`.
**Attacks**: (1) tried deriving `‖ζ − 1‖ < 1` from the cyclotomic norm identity C-d — circular
(C-c's `≥` direction uses `‖ζ − 1‖ < 1` only through C-a? no: C-c uses only geometric sums and
`‖ζ‖ = 1`; but C-d's *statement* `‖ζ−1‖^e = ‖p‖ < 1` would give it — yet C-d needs C-c which is
fine, so C-b could be derived from C-d; kept as a separate leaf because `TH_weightPoint`-side lemmas
need only `ζ^{p^h} = 1`, not primitivity). (2) `p = 2`: `(−1)^2 + 1 = 2 = p` — the lemma is stated
without `hp2` and the proof handles it by cases. (3) `hζ : ‖ζ‖ ≤ 1` is needed for the middle terms
(`‖ζ^i‖ ≤ 1`); supplied by C-a in the induction.

**C-c** `norm_one_sub_pow_of_isPrimitiveRoot_prime_pow`.
**Source**: the level-`1` `norm_one_sub_pow_of_isPrimitiveRoot` (`ClassicalPoint.lean:151`);
mathematically, all primitive `p^h`-th roots are Galois conjugate.
**Match**: `‖1 − ζ^i‖ ≤ ‖1 − ζ‖` by `geom_sum_mul` and `‖∑ ζ^j‖ ≤ 1`; conversely `i` is coprime to
`p^h` (`Nat.Coprime.pow_right`, `Nat.Prime.coprime_iff_not_dvd`), so `∃ j, i·j ≡ 1 (mod p^h)`
(`Nat.exists_mul_mod_eq_one_of_coprime`, needs `1 < p^h`), whence `ζ = (ζ^i)^j`
(`pow_mul`, `hζ.pow_eq_one_iff_dvd`, `Nat.ModEq`) and `‖1 − ζ‖ ≤ ‖1 − ζ^i‖` by the same bound.
**Attacks**: (1) `h = 0`: `p^0 = 1`, `ζ = 1`, both sides `0` — true; `1 < p^h` fails for the Bezout
lemma, so the proof splits `h = 0` off (or takes the symmetric bound trivially). (2) the level-`1`
proof used the unit-cofactor argument (`‖∑_{j<i} ζ^j‖ = 1` via `‖i‖ = 1`); the symmetric argument
avoids `‖ζ − 1‖ < 1` entirely — chosen. (3) `IsPrimitiveRoot.pow_iff_coprime` is the alternative
route to `ζ^i` primitive; not needed.

**C-d** `norm_sub_one_pow_of_isPrimitiveRoot_prime_pow`.
**Source**: `lwx.txt:476–478` (`v(T) = 1/p^{m−2}(p−1)`, `m = h+1`), i.e. `v(ζ − 1) = 1/ϕ(p^h)`.
**Match**: `Polynomial.eval_one_cyclotomic_prime_pow (h−1) : eval 1 (cyclotomic (p^(h−1+1)) K) = p`
(rewrite `h − 1 + 1 = h`); `cyclotomic_eq_prod_X_sub_primitiveRoots hζ` and `Polynomial.eval_prod`
give `∏_{μ ∈ primitiveRoots (p^h) K} (1 − μ) = p`; `norm_prod`; each `μ` is `ζ^i` with `i` coprime
to `p^h` (`mem_primitiveRoots (pow_pos ..)`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one` with `[NeZero (p^h)]`,
`IsPrimitiveRoot.pow_iff_coprime`), hence `¬ p ∣ i` and `‖1 − μ‖ = ‖1 − ζ‖` (C-c);
`Finset.prod_const`, `IsPrimitiveRoot.card_primitiveRoots`, `Nat.totient_prime_pow hp.out hh`.
**Attacks**: (1) `h = 0`: `ϕ(1) = 1`, `‖ζ − 1‖ = 0 ≠ ‖p‖` — false; `hh` necessary and present.
(2) `eval_one_cyclotomic_prime_pow` is stated for `p^(k+1)` — instantiate `k := h − 1` and rewrite
with `Nat.sub_add_cancel hh`. (3) sign: `∏ (X − C μ)` evaluated at `1` is `∏ (1 − μ)`, and
`‖1 − ζ‖ = ‖ζ − 1‖` (`norm_sub_rev`). (4) `[NeZero (p ^ h)]` for `eq_pow_of_pow_eq_one`: from
`pow_ne_zero` (`NeZero.of_pos`).

**C-e** `inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow`.
**Source**: `lwx.txt:1796–1797` "`v(T_{χ_k}) = p/(q(p−1)) < 1`" at `m = 2`; in general
`v(ζ−1) = 1/(p^{h−1}(p−1)) < 1` since `p^{h−1}(p−1) ≥ 2` for odd `p`.
**Match**: the level-`1` proof (`ClassicalPoint.lean:242–260`) with the exponent
`e = p^{h−1}(p−1) ≥ p − 1 ≥ 2`: if `‖ζ − 1‖ ≤ p⁻¹` then `p⁻¹ = ‖ζ−1‖^e ≤ p^{−e} ≤ p^{−2} < p⁻¹`.
**Attacks**: (1) `p = 2`, `h = 1`: `e = 1`, `‖ζ − 1‖ = ‖2‖ = p⁻¹` — the strict inequality fails;
`hp2` is necessary and present. (2) `e ≥ 2` from `p ≥ 3` and `p^{h−1} ≥ 1` (`Nat.one_le_pow`).
(3) uses C-d (needs `hh`).

**C-f** `norm_weightPoint_prime_pow`, `norm_weightPoint_pow_prime_pow`, `inv_lt_norm_weightPoint_prime_pow`,
`norm_weightPoint_lt_one_prime_pow`.
**Source**: `lwx.txt:1794–1798` (`T_{χ_k}`), `2323`.
**Match**: `norm_weightPoint` (`TargetPoint.lean:133–152`) verbatim with C-e in place of
`inv_lt_norm_sub_one_of_isPrimitiveRoot`: `weightPoint = (ζ−1)e + (e−1)` with `‖e−1‖ ≤ p⁻¹ < ‖ζ−1‖`.
**Attacks**: (1) the level-`1` private helpers (`norm_p_mul_sq_lt`, `norm_padicExp_p_mul_sub_one_le`,
`inv_p_pos`) are `private` in `TargetPoint.lean` — must be re-proved locally (5 lines each) or
copied; ticket C7 notes it. (2) `‖ζ − 1‖ < 1` from C-d (`e`-th power `< 1`). (3) `s` arbitrary in
`ℤ`: `‖ps‖ ≤ p⁻¹` via `IsUltrametricDist.norm_intCast_le_one`.

**C-g** `TH_weightPoint`, `norm_TH_weightPoint_sq_lt`, `haloExponentH_weightPoint`.
**Source**: `lwx.txt:466–470` (`κ(a·x) = χ(a)·χ(exp(p^m))^{log x/p^m}`, the level-`m` halo
character; at `T = T_{(k,ψ)}`: `(1+T)^{p^h} = χ(exp p)^{p^h} = χ(exp p^{h+1}) = exp(p^{h+1}s)`).
**Match**: `TH p h T = (1+T)^{p^h} − 1 = (ζ exp(ps))^{p^h} − 1 = exp(p^{h+1}s) − 1` by `mul_pow`,
`hζ`, `PadicExpLog.padicExp_natCast_mul` (`exp(w)^n = exp(n w)`, on the disc `‖w‖² < ‖p‖`); the
norm bound via `norm_padicExp_sub_one_le` (`‖exp(p^{h+1}s) − 1‖ ≤ ‖p^{h+1}s‖ ≤ p^{−(h+1)} ≤ p⁻¹`,
squared `< p⁻¹`); the exponent via `padicLog_padicExp` and `field_simp`.
**Attacks**: (1) only `ζ^{p^h} = 1` is used — stated so (weaker hypothesis than primitivity).
(2) `h = 0`: `TH p 0 T = T = ζ exp(ps) − 1` and the RHS is `exp(ps) − 1` with `ζ = 1` — true;
no `hh`. (3) the disc condition for `padicExp_natCast_mul`: `‖ps‖² < ‖p‖` (`norm_p_mul_sq_lt`).

**C-h** `norm_classicalPoint_pow_prime_pow`, `inv_lt_norm_classicalPoint_prime_pow`,
`norm_classicalPoint_lt_one_prime_pow`, `norm_TH_classicalPoint_sq_lt`, `haloExponentH_classicalPoint`.
**Source**: as C-f/C-g at `s = k`.  **Match**: `rw [← weightPoint_natCast]` then the C-f/C-g lemma
at `(k : ℤ)`; for the exponent `Int.cast_natCast`.  **Attacks**: (1) `weightPoint_natCast :
weightPoint p (k : ℤ) ζ = classicalPoint p k ζ` (`TargetPoint.lean:84`) rewrites right-to-left —
fine. (2) the statement `= k` casts `k : ℕ` to `K`; the `ℤ`-version gives `((k:ℤ):K)`; `push_cast`.
(3) these are the fields of `classicalDataH` — compiled in the skeleton against them.

**C-i** `autFactor_haloWeightH_classicalPoint_prime_pow`, `isClassicalShape_haloWeightH_classicalPoint_prime_pow`,
`classicalDataH`.
**Source**: `lwx.txt:466–470` (the level-`m` halo weight) and (2.3.2) `lwx.txt:600–604`
(`(cz+d)^k` shape).
**Match**: `autFactor_haloWeightH_classicalPoint` (`ClassicalPoint.lean:412–436`) verbatim with
`1 → h` and `haloExponentH_classicalPoint` (C-h) in place of `haloExponentH_one_classicalPoint`;
`mk_choose_natCast_mul_pow` is level-free; `levelBounds_M1Kh h` gives `d ≠ 0`.
**Attacks**: (1) the shape statement uses `certConj θG h …` and `discConjK h …`, both general;
the term `fun i t a => autFactor_… (discConjK h (certM1 …) a ψ)` type-checks in the skeleton.
(2) `classicalDataH`'s `hnorm` closes by `rw [norm_classicalPoint_pow_prime_pow …, map_natCast]`
exactly as at level `1` — compiled. (3) `hT := norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k`:
`IsPrimitiveRoot.pow_eq_one : ζ ^ (p^h) = 1` — compiled.

### Part G — `PhD/LWX/TargetPointH.lean`

**G-a** `autFactor_haloWeightH_weightPoint_neg_prime_pow`, `isClassicalShape'_haloWeightH_weightPoint_neg_prime_pow`.
**Source**: Step III's target weight `(−k−2, ψ)`, `lwx.txt:2070–2076`; at level `h` the target is
needed only for the complement bound (`le_unitSlope_compl`).
**Match**: `autFactor_haloWeightH_weightPoint_neg` (`TargetPoint.lean:262–292`) verbatim with
`1 → h`, `haloExponentH_weightPoint` (C-g) at `s = −(k+2)`; `mk_choose_neg_natCast_mul_pow`
level-free.
**Attacks**: (1) only `ζ^{p^h} = 1` used — stated so. (2) `hcast : ((−(k+2 : ℤ)) : K) = −((k+2 : ℕ) : K)`
as at level `1`. (3) `omit [Fintype ι] [DecidableEq ι]` on the shape lemma as at level `1`
(`IsClassicalShape'` does not need them) — kept.

**G-b** `oneAddPow_weightPoint_mul_padicExp_prime_pow`.
**Source**: the identity `(1+T_s)^y·exp(p(t−s)y) = (1+T_t)^y` is the definition of the `T`-coordinate
(`lwx.txt:466–470`) read at two weights.
**Match**: `oneAddPow_weightPoint_mul_padicExp` (`TargetPoint.lean:387–426`) verbatim with
`norm_weightPoint_lt_one_prime_pow` for the two continuity hypotheses.
**Attacks**: (1) only `‖weightPoint‖ < 1` (continuity of `oneAddPow`) and the agreement on `ℕ`
are used — no root-of-unity property beyond the norm; `hζ, hh` are then **slack** hypotheses that
could be replaced by `‖ζ − 1‖ < 1`; kept for uniformity (recorded, `_hx` convention at cleanup).
(2) `PadicInt.denseRange_natCast` closure argument unchanged. (3) `hdisc` for `padicExp_add`
unchanged.

**G-c** `specialize_univChar_targetChar_prime_pow`, `targetConst_eq_classicalDataH_u`.
**Source**: `lwx.txt:2070–2076` ("`ψ|_Δ·ω₀^{−k−2} = ωω₀^{−2k−2}`"), the AG-ζ identity of `lwx-theta-h2`.
**Match**: `specialize_univChar_targetChar` (`TargetPoint.lean:429–476`) and
`targetConst_eq_classicalData_u` (`478–502`) verbatim with the level-`h` inputs (C-f, C-h, G-b,
`haloCharFunH_psi h`, `certConj_apply_one_one h`).
**Attacks**: (1) `specialize_univChar` (`Specialize.lean:217`) is level-free (it is about
`HaloInt.specialize` at a point) ✓. (2) `targetConst_…` unfolds `classicalDataH … .u` by `show`
— the `u` field is a lambda; `show` with the explicit expression as at level `1`. (3) the `h0 h1 hT`
arguments of `haloCharFunH_psi h` are the level-`h` ones (C-f/C-g).

**G-d** `TargetDataH`, `weight`, `targetData_classicalPointH`.
**Source**: `StepThree.lean:350–376` (`TargetData`), `TargetPoint.lean:504–526`.
**Match**: verbatim with `1 → h`; `shape` by `funext` + G-c and `G-a`.
**Attacks**: (1) `TargetDataH` is a `Prop` (all fields Props; `TargetData` is `Prop` — checked by
`#print`), so `theorem targetData_classicalPointH` is right. (2) `h` is inferred from `c`'s type
(implicit `{h}` in the section) — compiled. (3) `d.weight` has type `AnalyticWeight (haloUnitsH h ψ)
(M1Kh h ψ) (haloRhoH p h T₁)`, which is what `le_unitSlope_compl`'s `κ'` accepts (`{UK'} {ρ'}`
generic) ✓.

### Part N — `PhD/LWX/NebCharH.lean`

**N-a** `oneAddPPowMul`, `coe_oneAddPPowMul`, `oneAddPPowMul_one`.
**Source**: `lwx.txt:462–464` (conductor `p^m`: the subgroup `1 + p^{m−1}ℤ_p`).
**Match**: `oneAddPPowMul p h x := oneAddPMul p (p^(h−1) x) = 1 + p·p^{h−1}x = 1 + p^h x` for `h ≥ 1`.
**Attacks**: (1) defined through `oneAddPMul` so that no `0 < h` is needed inside a definition;
`h = 0` gives the junk `1 + px` — `coe_oneAddPPowMul` carries `hh`. (2) `oneAddPPowMul_one` is
`pow_zero, one_mul` — `simp [oneAddPPowMul]`. (3) `1 + p^h x` is a unit for all `h ≥ 1`
(`isUnit_one_add_p_mul` at `p^{h−1} x`) ✓.

**N-b** `nebCharKH`, `nebCharH`, `nebCharH_apply`, `classicalDataH_u_eq_nebCharH`,
`autFactor_haloWeightH_classicalPoint_eq_nebCharKH`.
**Source**: `lwx.txt:466–470` (`x ↦ x^k ψ(x)`; the nebentypus is `κ(x)x^{−k}`).
**Match**: `NebChar.lean:66–106` verbatim with `1 → h` and the C-h inputs; `haloCharFunH_psi h`.
**Attacks**: (1) `nebCharH_apply` uses `haloCharFunH_psi h ψ T₀ ω hp2 hψ h0 h1 hT a` with the
level-`h` `h0 h1 hT` — C-h. (2) `classicalDataH_u_eq_nebCharH`: `certConj_apply_one_one h` ✓
general. (3) `autFactor_…_eq_nebCharKH` is definitional from C-i (term given, compiled).

**N-c** `nebCharH_mul`, `nebCharH_one`, `nebCharH_ne_zero`.
**Source**: `ψ` is a character.  **Match**: `NebChar.lean:111–133` with `univChar_mul`,
`HaloInt.specialize_mul` at the level-`h` point.  **Attacks**: (1) `specialize_mul` needs
`p⁻¹ < ‖T₀‖ < 1` — C-h. (2) `nebCharH_ne_zero`: the specialisation is a unit times `(ψ a)^{−k}`,
non-zero — as at level `1`. (3) no `h` enters beyond the point.

**N-d** `nebCharH_of_norm_sub_one_le_pow`.
**Source**: `lwx.txt:462–464` ("factors through `(ℤ/p^mℤ)^×`", `m = h+1`).
**Match**: `NebChar.lean:134–160` with `specialize_univChar_eq_padicExp h` (hypothesis
`‖u − 1‖ ≤ p⁻¹^(h+1)`, `HaloWeightH.lean:458`) and `haloExponentH_classicalPoint`:
`[a]_T(ω) = exp(k·log a) = a^k` so `nebCharH a = a^k · a^{−k} = 1`.
**Attacks**: (1) at level `1` the hypothesis was `p⁻¹^2` — the general `p⁻¹^(h+1)` is exactly what
`specialize_univChar_eq_padicExp` takes ✓. (2) `PadicExpLog.padicExp_natCast_mul` for `exp(k L) =
exp(L)^k` on the disc — `‖L‖ ≤ ‖a − 1‖`… the level-`1` proof's `hL` bound adapts (`‖log a‖ ≤ ‖a−1‖`).
(3) `ω(ā) = 1` since `ā = 1` (`unitsMap_toZMod_eq_one_of_norm_sub_one_le`, needs `‖a−1‖ ≤ p⁻¹`,
implied by `p⁻¹^(h+1) ≤ p⁻¹`, `pow_le_inv_p`).

**N-e** `continuous_zeta_pow_toZModPow`, `oneAddPow_sub_one_intHom_prime_pow`.
**Source**: the wild part `ζ^{ℓ⟨a⟩}` of the character, `lwx.txt:466–470`.
**Match**: `NebChar.lean:169–196` with `PadicInt.toZModPow h` (locally constant: `ker_toZModPow`
is `span {p^h}`, so `‖ℓ − ℓ'‖ ≤ p^{−h}` ⇒ same image; `PadicInt.norm_le_pow_iff_mem_span_pow`),
and agreement on `ℕ`: `(1 + (ζ−1))^n = ζ^n = ζ^{n mod p^h}` (`hζ.pow_eq_one`, `pow_mod`-style via
`ZMod.val_natCast`, `Nat.mod_add_div`).
**Attacks**: (1) `h = 0`: `toZModPow 0` lands in `ZMod 1`, `val = 0`, `ζ^0 = 1`; the identity
`(1+T)^ℓ = 1` is false for `ζ ≠ 1` — but `IsPrimitiveRoot ζ 1` forces `ζ = 1`; still `hh` is kept
(needed by the norm facts used in `continuous_oneAddPow_intHom`'s hypothesis `‖ζ − 1‖ < 1`, C-d).
(2) the level-`1` file used `PadicInt.ker_toZMod` and `IsLocalRing.mem_maximalIdeal`; at level `h`
use `ker_toZModPow`/`norm_le_pow_iff_mem_span_pow` instead. (3) continuity of `ℓ ↦ ζ^{(toZModPow h ℓ).val}`:
locally constant ⇒ continuous (`continuous_of_discreteTopology`-free: prove `IsOpen (preimage)` or
use `continuous_iff_continuousAt` with the ball of radius `p^{−h}`).

**N-f** `nebCharH_oneAddPPowMul`, `norm_logQuot_oneAddPPowMul_one`, `isPrimitiveRoot_nebCharH_oneAddPPowMul_one`,
`nebCharH_oneAddPPowMul_natCast`.
**Source**: `lwx.txt:462–464` ("but not `(ℤ/p^{m−1}ℤ)^×`": the conductor is exactly `p^{h+1}`).
**Match**: `NebChar.lean:205–306` with `1 + px → 1 + p^h x`: `nebCharH(1 + p^h x) = ζ^{ℓ mod p^h}`
(N-e, `nebCharH_apply`, `specialize_univChar`, `oneAddPow_weightPoint_mul_padicExp_prime_pow` at
`(0, k)`, `intHom_oneUnitPart_eq_padicExp`, `oneUnitPart_oneAddPMul` at `p^{h−1}x`);
`‖ℓ⟨1+p^h⟩‖ = ‖log(1+p^h)/p‖ = p^{−(h−1)}` (`norm_padicLog_eq`: `‖log(1+w)‖ = ‖w‖` for `‖w‖ < p^{−1/(p−1)}`,
i.e. `‖w‖ ≤ p⁻¹` for odd `p`); hence `(toZModPow h ℓ).val = p^{h−1}·u` with `p ∤ u`
(`PadicInt.norm_le_pow_iff_mem_span_pow` at `h−1` and not at `h`), and `ζ^{p^{h−1}u}` is a
primitive `p`-th root (`IsPrimitiveRoot.pow_of_dvd` with `p^{h−1} ∣ p^h`, `p^h/p^{h−1} = p`, then
`pow_of_coprime`); `(1+p^h)^n ≡ 1 + p^h n (mod p^{h+1})` (`add_pow`, terms `i ≥ 2` divisible by
`p^{2h} ∣ p^{h+1}` for `h ≥ 1`) and N-d.
**Attacks**: (1) `h = 0` breaks `norm_logQuot…` (`p^{−(0−1)} = 1` but the true norm of
`log(2)/p` is `≥ …`); `hh` present. (2) the exponent bookkeeping `val = p^{h−1}u`: from
`‖ℓ‖ = p^{−(h−1)}` get `ℓ ∈ span{p^{h−1}}`, `ℓ ∉ span{p^h}`; write `ℓ = p^{h−1}u` with `u` a unit
(`PadicInt.unit_coeff` or `norm_eq_pow_val`) and `toZModPow h (p^{h−1} u) = p^{h−1}·(toZMod u)`
— the cleanest is to work with `IsPrimitiveRoot (ζ ^ (toZModPow h ℓ).val) p ↔ orderOf …`; ticket
N13 records the route via `IsPrimitiveRoot.pow_iff_coprime` on `ζ^{p^{h−1}}` **or** the direct
`hζ.pow_of_dvd` + `pow_of_coprime` after establishing `(toZModPow h ℓ).val = p^{h−1} * u'` with
`¬ p ∣ u'` by `ZMod.val`/`Nat` arithmetic (`Nat.eq_mul_of_div_eq_right`). (3)
`nebCharH_oneAddPPowMul_natCast` needs `oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1 =
oneAddPPowMul p h (n+1) * (1 + p^{2h} n …)`-type correction of norm `≤ p^{−(h+1)}`, killed by N-d —
same shape as `NebChar.lean:282–306`.

**N-g** `sum_nebCharH_oneAddPPowMul_mul_eq_zero`, `sum_inv_…`, `sum_inv_nebCharKH_eq_zero`.
**Source**: the vanishing of the non-central terms, `lwx-h1` I-f; here the `d`-entry is `1 + bcp^h`
(L-d).  **Match**: `NebChar.lean:309–345` verbatim (`geom_sum_eq_zero` at the primitive root
`nebCharH(1+p^h)^b`, `b` coprime to `p`), with the spelling `ψ(1 + b·c·p^h)`.
**Attacks**: (1) the spelling must match `atkinLehner_term_eqH`'s `nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h))`
— identical modulo `c : Fin p` vs `c : ℕ` (as at level `1`). (2) `coe_oneAddPPowMul hh` converts
`((1 + p^h(bc) : ℤ_[p]) : ℚ_[p]) = 1 + b c p^h` (`push_cast; ring`). (3) `hb : ¬ p ∣ b` for `b ∈ Fin p`,
`b ≠ 0` — `Nat.not_dvd_of_pos_of_lt`.

**N-h** `nebCharKH_psi_mul`, `nebCharKH_psi_ne_zero`, `nebCharKH_psi_of_norm_sub_one_le_pow`.
**Match**: `NebChar.lean:347–392` verbatim (`let z : ℤ_[p] := ⟨x, hx.le⟩`, `PadicInt.isUnit_iff`).
**Attacks**: (1) `hcond` at `p⁻¹^(h+1)` matches W's hypothesis shape ✓. (2) the `Norm` trap on
inline `⟨x, h⟩` — use `let` (recorded rule). (3) no other change.

**N-i** `oneAddPow_inv_sub_one_mul_prime_pow`, `nebCharH_eq`, `nebCharH_partnerChar`,
`nebCharKH_partnerChar`, `autFactor_haloWeightH_partner_eq_inv_nebCharKH`, `classicalDataH_partnerChar_u`.
**Source**: `lwx.txt:2028–2036` ("`ψ⁻¹|_Δ·ω₀^k = ω⁻¹ω₀^{2k}`"), `lwx.txt:1783–1785` (the pairing
with `ψ⁻¹`).  **Match**: `NebChar.lean:406–518` verbatim with `toZMod → toZModPow h` in `nebCharH_eq`
(from N-e), `hζ.inv : IsPrimitiveRoot ζ⁻¹ (p^h)`, `(ζ⁻¹)^v · ζ^v = 1` (`inv_pow`,
`inv_mul_cancel₀`), and `mem_M1Kh_iff h`, `mem_Mh_iff` for `g 1 1 = ψ d`, `d` a unit.
**Attacks**: (1) `partnerChar` is unchanged (the disc character of `(k, ψ⁻¹)` is `ω⁻¹ω₀^{2k}` at
every conductor — the wild part is carried by `ζ⁻¹`) ✓. (2) `classicalDataH_partnerChar_u` needs
`classicalDataH … hζ.inv …` to typecheck with `IsPrimitiveRoot ζ⁻¹ (p ^ h)` — `IsPrimitiveRoot.inv` ✓
(compiled in the skeleton). (3) `mem_Mh_iff` gives `‖g 1 1‖ = 1` (component `.2.2.1`) for the
unit `d` — as at level `1`.

### Part L — `PhD/LWX/AtkinLehnerLocalH.lean`

**L-a** the matrices `wQH`, `wQHinv`, `ℓQH`, `ℓQHinv`, `tMatH`, `tMatHInv`; `wQH_one`, `ℓQH_one`,
`tMatH_one`; determinants and inverses (L4–L12).
**Source**: `lwx.txt:481–490` (`Iw_{p^m}`), the level-`p^{m}` Atkin–Lehner element `(0 1; −p^m 0)`
(`AtkinLehner.lean:62`, `atkinLehner p m`); the disc-model coordinate `t_a = (p^h a; 0 1)`
(`DiscModel.lean:171`, docstring "`t_a = (pʰ a; 0 1)`").
**Match**: `wQH = (0 p^h; −p 0)` is the unique matrix with `t₀⁻¹ wQH t₀ = (0 1; −p^{h+1} 0)`:
`t₀⁻¹ (0 x; y 0) t₀ = (0 x/p^h; y p^h 0)`, so `x = p^h`, `y = −p`.  `det wQH = p^{h+1}`,
`det ℓQH = (1 − X)(1 + X) + (b²c p^h p^h/p)(cp) = 1 − X² + b²c²p^{2h} = 1` with `X = bcp^h`.
**Attacks**: (1) **defect found and repaired**: with the entry `−b²c p^{2h−1}` written via `p^(2h−1)`
(natural subtraction) the inverse identity and `det ℓQH = 1` fail at `h = 0`, and `ℓGLH` (W-a)
would need `0 < h` *inside a definition*; the `p^h·p^h/p` spelling makes every identity
unconditional — chosen. (2) `wQH_one : wQH p 1 = wQ p` — `pow_one`; `ℓQH_one`: `p^1 p^1/p = p`
(`field_simp`), matching `ℓQ`'s `−b²cp`; `tMatH_one`: `pow_one`. (3) inverses: `wQH wQHinv =
(p^h/p^h, 0; 0, p/p)` = `1` (`field_simp` with `p ≠ 0`); `tMatH tMatHInv = (p^h/p^h, −a/p^h·p^h + a;
0, 1) = 1`.

**L-b** translations and the coordinate change (L13–L16).
**Source**: `DiscModel.lean:171` (`t_a`), `AtkinLehnerLocal.lean:127–156`.
**Match**: `sQ b · tMatH a = (p^h, a + b; 0, 1)`; `tMatHInv 0 · sQ(−a) = (1/p^h, −a/p^h; 0, 1) =
tMatHInv a`; `tMatHInv 0 · sQ b · tMatH 0 = (1, b/p^h; 0, 1)`; `tMatHInv 0 · wQH · tMatH 0 =
(0, 1; −p^{h+1}, 0)`.
**Attacks**: (1) all are `ext i j; fin_cases i <;> fin_cases j <;> simp [...]; field_simp` as at
level `1`; the only new fact is `(p^h)⁻¹·p^h = 1` (`pow_ne_zero`). (2) `discConjMat_wQH` at `h = 1`
recovers `discConjMat_wQ` (`atkinLehner p 2`) ✓. (3) `atkinLehner p (h+1)` has entry `−p^(h+1)`;
`−p·p^h = −p^{h+1}` by `pow_succ`.

**L-c** the key factorisation (L17–L22).
**Source**: `lwx.txt:1783–1785` (the pairing), `lwx-h1` `decomposition.md` L-c/I-f (the
double-coset expansion); level `1`: `AtkinLehnerLocal.lean:157–199`.
**Match**: `wQH vQ_b wQHinv = (1, −bp^h; 0, p)` (the `U'_p`-representative);
`(1, −bp^h; 0, p)(p, 0; cp, 1) = (p − bcp^{h+1}, −bp^h; cp², p) = ℓQH b c · (p·(1, −bp^h/p; 0, 1))`:
`ℓQH·p·sQ(−β)` with `β = bp^h/p` has entries `(p(1 − X), −pβ(1 − X) − p·b²c p^{2h}/p ; cp², −cpβp + p(1+X))`
`= (p − bcp^{h+1}, −bp^h + b²cp^{h+1}·… )` — computed: `−pβ(1−X) − b²cp^{2h} = −bp^h + b²cp^{2h} − b²cp^{2h} = −bp^h` ✓,
`−cp²β + p + pX = −bcp^{h+1} + p + bcp^{h+1} = p` ✓.  Conjugation: `wQH g wQHinv = (d, −cp^h/p; −bp/p^h, a)`
(computed in `plan.md`'s derivation: `(0 p^h; −p 0)(a b; c d)(0 −1/p; 1/p^h 0)`).
**Attacks**: (1) `h = 0` check of `upAdjRepH_mul_vQ`: `(1 −b; 0 p)(p 0; cp 1) = (p − bcp, −b; cp², p)`
and `ℓQH_0 b c·p·sQ(−b/p) = (1 − bc, −b²c/p; cp, 1 + bc)(p, −b; 0, p) = (p − bcp, −b; cp², p)` ✓
— unconditional, as claimed. (2) `wQH_mul_mul_wQHinv` at `h = 1` is `(d, −c; −b, a)` ✓ =
`wQ_mul_mul_wQinv`. (3) `ℓQHinv_mul_…`: `ℓQHinv ℓQH = 1` (L-a) then `one_mul`.

**L-d** membership (L23–L25).
**Source**: `lwx.txt:481–490` (`Iw_{p^m}`), and `lwx-h1` W-b (`w` normalises the disc-`0` part).
**Match**: `ℓQH ∈ Iw p 1`: entries integral (`‖b²c p^h p^h/p‖ = ‖b‖²‖c‖ p^{−(2h−1)} ≤ 1` for `h ≥ 1`),
`‖cp‖ ≤ p⁻¹`, `det = 1`.  `wQH_conj_mem_Iw`: from `wQH_mul_mul_wQHinv`, the entries of
`(d, −cp^h/p; −bp/p^h, a)`: `‖cp^h/p‖ ≤ p⁻¹·p^{−h}·p = p^{−h} ≤ 1`, `‖bp/p^h‖ ≤ p^{−h}·p⁻¹·p^h = p⁻¹`,
`det = ad − bc` unchanged; the `(0,1)`-entry bound `≤ p^{−h}` ✓.
**Attacks**: (1) `h = 0` for `ℓQH_mem_Iw`: `‖b²c/p‖ = p·‖b²c‖` may exceed `1` — false; `hh` present.
(2) `wQH_conj_mem_Iw` at `h = 0`: `‖b‖ ≤ 1` hypothesis, `(1,0)`-entry `−bp` has norm `≤ p⁻¹` ✓,
`(0,1)`-entry `−c/p` has norm `≤ 1` ✓ — true unconditionally; no `hh`. (3) the level-`1` proof's
`hswap` uses `Matrix.det_fin_two_of` and `ring` — the level-`h` entries need `field_simp` first.

**L-e** the disc bookkeeping at level `h` (L26–L36).
**Source**: `DiscModel.lean:168–176` (`discImage h δ a = toZModPow h (mobius(δ)(a.val))`,
`discConjMat`), `AtkinLehnerLocal.lean:320–427`.
**Match**: `discImage h δ 0 = toZModPow h (b/d) = 0 ⇔ ‖b/d‖ ≤ p^{−h} ⇔ ‖b‖ ≤ p^{−h}`
(`PadicInt.norm_le_pow_iff_mem_span_pow`, `ker_toZModPow`, `d` a unit);
`discConjMat h δ a = t_{a'}⁻¹ δ t_a` entry-wise (definition `DiscModel.lean:172–178` against
`tMatHInv/tMatH`: `(1/p^h, −a'/p^h; 0, 1)(A B; C D)(p^h, a; 0, 1)`); `sQ(−a') δ sQ(a) = t₀ · conj · t₀⁻¹`;
`vQ c`, `ℓQH`, `ℓQHinv` fix disc `0` (their `b`-entries have norm `≤ p^{−h}`: `0`, and
`‖b²c p^{2h}/p‖ ≤ p^{−(2h−1)} ≤ p^{−h}` for `h ≥ 1`); the `d`-entries of the disc-`0` conjugates
are the `d`-entries of the matrices (`t₀⁻¹ δ t₀` has `(1,1)`-entry `D`); `sQ b` sends `0 ↦ b mod p^h`
(`mobius(sQ b)(0) = b`, `toZModPow h (b : ℤ_[p]) = (b : ZMod (p^h))`, `map_natCast`) with
trivial conjugate for `b < p^h` (`ZMod.val_natCast`, `Nat.mod_eq_of_lt`).
**Attacks**: (1) `discImage_zero_of_norm_apply_zero_one_le_pow` at `h = 0`: `ZMod 1` is trivial,
statement true for any `δ` ✓ unconditional. (2) the level-`1` proofs of L29–L39 (`AtkinLehnerLocal.lean:320–427`)
use `PadicInt.ker_toZMod` and `pow_one`; at level `h` the `toZModPow` API (`ker_toZModPow`,
`norm_le_pow_iff_mem_span_pow`) replaces them — the only real change. (3) `discConj_sQ_zero_prime_pow`
needs `b < p^h` (at level `1`: `b < p`); consumers pass `a.val` of `a : ZMod (p^h)` (`ZMod.val_lt`).

### Part W — `PhD/LWX/AtkinLehnerMapH.lean`

**W-a** `wGLH`, `ℓGLH`, `coe_*`, `coe_wGLH_inv`, `coe_ℓGLH_inv`, `wGLH_one`, `wGLH_mul_vGL_mul_wGLH_inv_mul_vGL`.
**Source**: as L-a/L-c.  **Match**: `mkOfDetNeZero` with `det_wQH`, `det_ℓQH`; the GL identity is
`Units.ext` of `wQH_mul_vQ_mul_wQHinv_mul_vQ` after `coe_wGLH_inv` (as `AtkinLehnerMap.lean:110–118`).
**Attacks**: (1) `ℓGLH` needs `det ℓQH ≠ 0` for every `h` — L-a's unconditional `det = 1` (the
repaired defect). (2) `coe_wGLH_inv`: `Units.inv` of `mkOfDetNeZero` is the adjugate/inverse
matrix; prove by `Units.inv_eq_of_mul_eq_one_right` / `Matrix.inv_eq_right_inv` from
`wQH_mul_wQHinv`, as at level `1` (`AtkinLehnerMap.lean:84–92`). (3) `sGL p (−(b p^h/p))` with
`sGL_inv`/`neg_neg` in `term_elt_eqH` (I-e) — consistent spelling `-(b * (p : ℚ_[p]) ^ h / p)`.

**W-b** `atkinLehnerKH`, `atkinLehnerKHinv`, products, `atkinLehnerKH_eq`, `atkinLehnerKHinv_eq`.
**Source**: `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)·η_p`); level `1`: `AtkinLehnerMap.lean:119–140, 261–278`.
**Match**: `atkinLehnerKH ψ h = ψ(0 1; −p^{h+1} 0)`, inverse `(0, −p^{−(h+1)}; 1, 0)`;
`= ψ(tMatHInv 0 · wQH · tMatH 0)` by `discConjMat_wQH` (L-b).
**Attacks**: (1) `(ψ p)^(h+1) ≠ 0` from `ψ p ≠ 0` (injective ring hom). (2) `atkinLehnerKHinv_eq`:
`tMatHInv 0 · wQHinv · tMatH 0 = (0, −1/p^{h+1}; 1, 0)` — compute (`field_simp`). (3) `map_pow`
for `ψ (p^(h+1)) = (ψ p)^(h+1)`.

**W-c** `AtkinLehnerDataH`, `AtkinLehnerData.toH`, `theta_ιp_pGLH`.
**Source**: `lwx.txt:1783–1785` (the twist by a central Hecke character), `lwx-h1` design decision 4.
**Match**: the level-`1` structure with `wGL → wGLH p h` and the normalisation on
`‖(θG u) 0 1‖ ≤ p⁻¹^h`.  `toH`: `wGLH_one` rewrites `χ_wGL` and `w_conj_mem_U` (with `pow_one` on
the norm bound).
**Attacks**: (1) is the level-`p^{h+1}` part the right domain of `w_conj_mem_U`? By L-d,
`w_h u w_h⁻¹ ∈ Iw_p` needs exactly `p^h ∣ b(θ u)` — yes; and the disc-shifted elements (W-d) satisfy
it. (2) for `Dfx ℚ D` with `U = K^p·Iw_p`, `χ(ιp w_h) = ψ_A(p^{h+1} at p) = ∏_{l≠p} ψ_l(p^{h+1})^{−1} = 1`
(unramified away from `p`) — consistent with `χ_wGLH` (instantiation out of scope). (3) `h` is a
structure parameter placed after `U` (section variable order) — `AtkinLehnerDataH θG ψ U h Γ nebK`;
recorded in `plan.md`.

**W-d** `discShiftH` and its five lemmas.
**Source**: `AtkinLehnerMap.lean:195–260` (Shapiro's lemma bookkeeping).
**Match**: verbatim with `1 → h`, `sQ_mem_Iw` for `‖a.val‖ ≤ 1`; `norm_theta_discShiftH_zero_one_le`:
`s_{−a'} θu s_a = t₀ · discConjMat h · t₀⁻¹` (L-e), whose `(0,1)`-entry is `p^h · (discConjMat) 0 1`,
of norm `≤ p^{−h}` (`discConjMat_mem_Mh h`, entries `≤ 1`); `discImage_discShiftH_zero` from
L-e; `discConjMat_discShiftH_zero` by `discConjMat_zero_of_discImage_zero_prime_pow` and
`tMatHInv_mul_tMatH`.
**Attacks**: (1) the level-`1` `norm_theta_discShift_zero_one_le` bound was `p⁻¹`; at level `h` it is
`p⁻¹^h` because `t₀ = (p^h ·)` — this is what feeds `w_conj_mem_U` ✓ consistent. (2) `mem_Mh_iff`'s
first component gives `‖g i j‖ ≤ 1` for all entries ✓. (3) `h01`-style computation
(`simp only [Matrix.mul_apply, Fin.sum_univ_two]; simp [tMatH, tMatHInv]`) unchanged.

**W-e** `cSpace_ext_blockProjH`, `nebK_one_of_cond_pow`, `nebK_mul_nebK_eq_nebK_detH`, `nebK_one_sub_eq_invH`.
**Source**: `AtkinLehnerMap.lean:280–346`.
**Match**: `ad = det + bc`, `‖bc/det‖ ≤ p^{−h}·p^{−1} = p^{−(h+1)}` ⇒ `nebK(1 + bc/det) = 1`;
`(1−x)(1+x) = 1 − x²`, `‖x²‖ ≤ p^{−2h} ≤ p^{−(h+1)}` for `h ≥ 1`.
**Attacks**: (1) `nebK_one_sub_eq_invH` at `h = 0`: `‖x‖ ≤ 1` gives `‖x²‖ ≤ 1 ≰ p⁻¹` — false;
`hh` present. (2) the level-`1` slack `_hne` is dropped (the proof never used it) — statement
weaker, fine. (3) `mem_Iw_iff` gives `‖g 1 0‖ ≤ p⁻¹^1`; `pow_one`.

**W-f** classical disc forms (`locPolyFormsH`, `ClassicalDiscFormsH`, `mem_…_iff`,
`discHeckeOperator_mem_classicalDiscFormsH`, `discHeckeOperatorClH`).
**Source**: `lwx.txt:655–662` (`LP^{m−1,≤k}`), (3.21.1); level `1`: `AtkinLehnerMap.lean:347–428`.
**Match**: verbatim with `1 → h`; `discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ` general ✓.
**Attacks**: (1) `locPolyFormsH`'s submodule proofs are pointwise (`add_mem`, `zero_mem`, `smul_mem`
of `locPolyDegSubmodule`) — copied from `AtkinLehnerMap.lean:349–354`. (2) `discHeckeOperatorClH`'s
`map_add'/map_smul'` are `Subtype.ext` + `change` + `map_add`/`map_smul` as at level `1`
(`AtkinLehnerMap.lean:402–428`). (3) `hφ.1 : φ ∈ DiscForms …` by `Submodule.mem_inf` (defeq) ✓
compiled.

**W-g** `apply_mul_of_theta_eq_oneH`, `blockProj_zero_apply_mul_mem_UH`, `shapiro_blockProjH`.
**Source**: `AtkinLehnerMap.lean:430–484`; Shapiro's lemma.
**Match**: verbatim with `1 → h`, `discImage_sQ_zero_prime_pow`, `discConj_sQ_zero_prime_pow`
(`a.val < p^h` by `ZMod.val_lt`), `kappaSlash_eq_smul_symAct_of_shape` (level-free).
**Attacks**: (1) `shapiro_blockProjH` needs `haveI : NeZero (p ^ h)` for `ZMod.val_natCast` — as at
level `1` (`⟨pow_ne_zero _ hp.out.ne_zero⟩`). (2) `blockProj_discSlash h` general ✓. (3) the
`discConj … 0 = 1` rewrite then `discConjK … = 1` — `Subtype.ext`, as at level `1`.

**W-h** `atkinLehnerFunH` and its four lemmas, `atkinLehnerFunH_slash`, `atkinLehnerMapH`.
**Source**: `bu04.txt:633`; `AtkinLehnerMap.lean:486–666`; `lwx-h1` `decomposition.md` W-f (the
full derivation of the slash identity).
**Match**: verbatim with `1 → h`, `wGL → wGLH p h`, `atkinLehnerK → atkinLehnerKH ψ h`,
`discShift → discShiftH`, `w_conj_mem_U` at the bound `p⁻¹^h` (W-d), `wQH_mul_mul_wQHinv` (L-c) for
the `d`-entry of `w_h u' w_h⁻¹` being the `a`-entry of `u'`, `nebK_mul_nebK_eq_nebK_detH` (W-e),
`atkinLehnerKH_eq` (W-b), `symAct_mul` (level-free).
**Attacks**: (1) the conjugate `w_h u' w_h⁻¹` has `(1,1)`-entry `a(u')` — from L-c's formula ✓
unchanged. (2) the `maxHeartbeats 1000000` of level `1` will be needed again — recorded in the
ticket. (3) `hh` enters `atkinLehnerFunH_slash` only through `nebK_one_sub_eq_invH`? No — through
`w_conj_mem_U`'s domain? That needs `‖b(θ u')‖ ≤ p^{−h}` (W-d, unconditional); `hh` is needed for
`discImage_ℓQH_zero`-type facts? Not in the slash lemma.  **Possibly slack** in W30/W31/W35–W38;
kept so that the four `hmul/hne/hcond/hκ/hκ'` + `hh` hypothesis block is uniform across Parts W
and I (`_hx` convention at cleanup if unused).

**W-i** `atkinLehnerFunHInv`, its lemmas, `atkinLehnerMapHInv`, the two inverse identities,
`atkinLehnerEquivH`.
**Source**: `AtkinLehnerMap.lean:668–936`.  **Match**: verbatim with `1 → h`; `χ_wGLH`,
`atkinLehnerKH_mul_atkinLehnerKHinv`, `symAct_one`, `shapiro_blockProjH`.
**Attacks**: (1) `W' ∘ W = 1` uses `χ(y w_h) = χ(y)` (`χ_wGLH`) and `w_h⁻¹ w_h = 1` in `G` ✓.
(2) `symAct K k (atkinLehnerKH) (symAct K k (atkinLehnerKHinv) f) = symAct (KHinv · KH) f = f` on
`polySubmodule` (`symAct_mul`, `symAct_one`) ✓ level-free. (3) `LinearEquiv.ofLinear` with the two
`LinearMap.ext` — compiled in the skeleton.

**W-j** `discEvalAtReps_mem_locPolyDegSubmoduleBlockH`, `discEvalAtRepsClH`, `discEvalAtRepsClH_apply`.
**Source**: `AtkinLehnerMap.lean:938–1002`; `bijective_discEvalAtReps_of_stabilizer_eq_bot`
(`DiscForms.lean`, general in `h`).
**Match**: verbatim with `1 → h`, `locPolyDegSubmoduleBlock p ι K h k`,
`discSlash_mem_locPolyDegSubmodule_of_shape h`.
**Attacks**: (1) `Submodule.inclusion inf_le_left` against the `def ClassicalDiscFormsH` — unfolds
by delta (compiled). (2) `discEvalAtRepsClH_apply` is `rfl` — compiled. (3) the bijectivity proof
(`AtkinLehnerMap.lean:965–988`) uses `DoubleCoset.rel_iff`, `left_invt'`, `mem_discForms_iff h` ✓.

### Part I — `PhD/LWX/AtkinLehnerIdentityH.lean`

**I-a** `vRepDH`, `vRepDH_mem_levelM1`, `upEltDH`, `upEltDH_mem_levelM1`, `discHeckeOperator_apply_eq_sumH`.
**Source**: `lwx.txt:705–716` (`U_p` with `v_j = (p 0; jq 1)`); `AtkinLehnerIdentity.lean:50–105`.
**Match**: identical formulas (`U_p`'s representatives do not depend on `h`); the naive Hecke
formula via `heckeOperatorSlash_eq_finsetSum` at level `h`.
**Attacks**: (1) `vQ_mem_M1`, `norm_natCast_le_one` unchanged. (2) the `discHeckeOperator θG h ψ κ U hU`
signature ✓ general. (3) nothing `h`-specific.

**I-b** `blockProj_zero_discSlash_of_shapeH`, `apply_mul_ιp_pGLH`, `apply_mul_ιp_pGL_invH`,
`blockProj_zero_apply_mul_ιpH`.
**Source**: `AtkinLehnerIdentity.lean:105–165`.  **Match**: verbatim with `1 → h`, W-g.
**Attacks**: (1) `apply_mul_ιp_pGLH` uses `D.central` (unchanged) and `apply_mul_of_theta_eq_oneH`.
(2) `blockProj_zero_apply_mul_ιpH`: `Iw_one_le_M1 hg` and `D.ιp_mem_U g hg` unchanged; the disc-`0`
condition is `discImage h … = 0`. (3) the `congr`-style `rintro _ _ rfl; rfl` closure unchanged.

**I-c** `term_elt_eqH`.
**Source**: `lwx-h1` I-f (the group element of the `(b,c)`-term); L-c/W-a at level `h`.
**Match**: from `wGLH_mul_vGL_mul_wGLH_inv_mul_vGL` inverted: `(ℓ (p s_{−β}))⁻¹ = s_β p⁻¹ ℓ⁻¹` with
`β = b p^h/p`, `sGL_inv`, `neg_neg`.  **Attacks**: (1) unconditional in `h` (L-c) ✓ no `hh`.
(2) the spelling `sGL p (b * (p : ℚ_[p]) ^ h / p)` must be reused verbatim in I-d. (3) `map_inv`,
`mul_inv_rev`, `inv_inv` as at level `1`.

**I-d** `blockProj_zero_apply_term_eltH`.
**Source**: `AtkinLehnerIdentity.lean:167–233`.
**Match**: verbatim with: `ℓQH_mem_Iw hh`, `ℓQHinv_mem_Iw hh`, `discImage_ℓQHinv_zero hh`,
`discConj_ℓQHinv_zero_one_one hh` (`d`-entry `1 − bcp^h`), `discConjMat_zero_of_discImage_zero_prime_pow`,
and `shapiro_blockProjH` at `a = (b p^{h−1} : ZMod (p^h))` with `a.val = b p^{h−1}`
(`ZMod.val_natCast`, `Nat.mod_eq_of_lt`: `b p^{h−1} < p·p^{h−1} = p^h`) and
`((b p^{h−1} : ℕ) : ℚ_[p]) = b p^h/p` (`hh`, `pow_succ`, `field_simp`).
**Attacks**: (1) **the disc index**: at level `1` the term lands in disc `b`; at level `h` in disc
`b p^{h−1}` — the translation is `s_{b p^{h−1}}` (L-c), and `shapiro_blockProjH` reads disc
`b p^{h−1}` of `φ(x)` as disc `0` of `φ(x s_{b p^{h−1}})` ✓ consistent. (2) `hh` needed for the
integrality of `ℓQH` and for `b p^{h−1} < p^h` ✓ present. (3) `hb : ‖(b : ℚ_p)‖ ≤ 1`, `hc` unchanged.

**I-e** `atkinLehner_term_eqH`.
**Source**: `AtkinLehnerIdentity.lean:235–325`; `lwx-h1` I-f.
**Match**: verbatim with `1 → h`: `atkinLehnerFunH_blockProj_zero`, `χ_wGLH`, `χ_vGL`, I-c, I-d,
`symAct_mul`; the matrix identity `disc-0-conj(vQ c) · KH · disc-0-conj(vQ b) · KHinv ·
ψ(tMatHInv 0 ℓQHinv tMatH 0)` `= p • (1, −b/p; 0, 1)`-type product computed entry-wise with
`tMatH/tMatHInv/ℓQHinv/wQH/wQHinv/vQ` (`field_simp; ring`, as at level `1` lines 300–316 with `p^h`);
`symAct_smul_one`; `nebK_one_sub_eq_invH hh` with `‖bcp^h‖ ≤ p^{−h}`.
**Attacks**: (1) the disc-coordinate translation is `(1, −b/p; 0, 1)` at every level (design
decision 5) — verified: `tMatHInv 0 · sQ(−b p^h/p) · tMatH 0 = (1, −(b p^h/p)/p^h; 0, 1) = (1, −b/p; 0, 1)`
by L-b's `tMatHInv_zero_mul_sQ_mul_tMatH_zero`. (2) `discConj h ⟨vQ p c, _⟩ 0 = tMatHInv 0 · vQ c · tMatH 0`
by L-e (`discImage_vQ_zero_prime_pow`, `discConjMat_zero_of_discImage_zero_prime_pow`) — the
`hMb/hMc` facts. (3) `‖bcp^h‖ ≤ p^{−h}`: `norm_mul`, `norm_pow`, `Padic.norm_p`, `‖b‖,‖c‖ ≤ 1`.
(4) the level-`1` proof used `maxHeartbeats`? (no: only the two big lemmas) — the entry-wise
`simp [...] <;> field_simp <;> ring` with `p^h` may need `pow_ne_zero`; record.

**I-f** `blockProj_zero_discHecke_atkinLehnerH`, `discHeckeClH_comp_atkinLehnerH`.
**Source**: `lwx.txt:1783–1785`; `AtkinLehnerIdentity.lean:327–465`; `lwx-h1` I-f.
**Match**: the double sum over `b, c : Fin p` of I-e; for `b = 0` the disc index `0·p^{h−1} = 0`,
the translation is `1`, `∑_c 1 = p`, and `p·p^k = p^{k+1}`; for `b ≠ 0`, `¬ p ∣ b` and `hsum` at
`b` (over `c ∈ range p`, converted from `Fin p` by `Fin.sum_univ_eq_sum_range`) kills the term
(the `c`-independent vector factors out); `shapiro_blockProjH` + `cSpace_ext_blockProjH` for the
operator identity.
**Attacks**: (1) `hsum`'s spelling `nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h))` with `c : ℕ` vs
I-e's `c : Fin p` cast — identical after `Fin.sum_univ_eq_sum_range` and `Nat.cast` — as at level `1`.
(2) `maxHeartbeats 1000000` both, as at level `1`. (3) the `b = 0` disc: `((0 * p^(h−1) : ℕ) : ZMod (p^h)) = 0`
by `simp` ✓; `symAct (mapMatrix ψ !![1, -(0/p); 0, 1]) = symAct 1 = id` on `polySubmodule`
(`symAct_one`) — as at level `1` with `b = 0`.

**I-g** `discEvalAtRepsClH_discHeckeOperatorClH`, `atkinLehnerHypothesis_of_conjH`,
`atkinLehnerHypothesis_of_atkinLehnerDataH` (**M1**).
**Source**: `AtkinLehnerIdentity.lean:467–626`; `lwx.txt:1763–1768`.
**Match**: verbatim with `1 → h`: `discEvalAtReps_discHeckeOperator` (general), the transport
through `discEvalAtRepsClH` and `atkinLehnerEquivH`, `finBasisOfFinrankEq` with
`finrank_locPolyDegSubmoduleBlock h k`, `LinearMap.toMatrix_comp`, `LinearEquiv.symm_comp`;
the H1 hypotheses discharged by N-h/N-g/N-i (`nebCharKH_psi_mul`, `_ne_zero`, `_of_norm_sub_one_le_pow`,
`sum_inv_nebCharKH_eq_zero`, `autFactor_haloWeightH_classicalPoint_eq_nebCharKH`,
`autFactor_haloWeightH_partner_eq_inv_nebCharKH`).
**Attacks**: (1) `_hS''` slack of level `1` dropped in `atkinLehnerHypothesis_of_conjH` (the proof
`AtkinLehnerIdentity.lean:504–526` never uses it) ✓. (2) `maxHeartbeats 2000000` for M1 as at
level `1` — recorded. (3) `cd.weight` is `haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ cd.h0 cd.h1 cd.hT`
and `hκ := autFactor_haloWeightH_classicalPoint_eq_nebCharKH h ψ ω k ζ hp2 hψ hζ.pow_eq_one cd.h0 cd.h1 cd.hT`
— proof-irrelevant match ✓; `hκ'` at `ζ⁻¹` with `partnerChar` ✓ (N-i).

### Part R — `PhD/LWX/ConductorSlopes.lean`

**R-a** `inv_pow_lt_norm_pow_of_norm_pow_eq`, `ClassicalDataH.inv_pow_lt_norm_pow`.
**Source**: [LWX, Thm 1.5] `lwx.txt:181–186` ("`p^{−q/p^{M−1}(p−1)} > λ`", `λ = p^{−8/((p²−1)t+8)}`),
`lwx.txt:2323` ("by the assumption on M").
**Match**: `hκ : p⁻¹^8 < ‖T₀‖^{(p²−1)t+8}` is `SlopesSeam.lean:147`'s hypothesis; with
`‖T₀‖^e = p⁻¹`, `e = p^{h−1}(p−1)`: `‖T₀‖^{N'} > ‖T₀‖^{8e} = p^{−8}` iff `N' < 8e` (as `‖T₀‖ < 1`),
`N' = (p²−1)t + 8` — `pow_lt_pow_right_of_lt_one₀`.  The datum version: `hnorm` and
`hψ p : ‖ψ p‖ = ‖(p : ℚ_p)‖ = p⁻¹` (`Padic.norm_p`).
**Attacks**: (1) `‖T₀‖ > 0` from `hnorm` (`p⁻¹ ≠ 0`, `pow_ne_zero`'s contrapositive) or from `h0`.
(2) `h = 1`: `8(p−1) > (p²−1)t + 8` fails for all `t ≥ 1` — consistent with [LWX]'s "M ≥ 2 …
by the assumption on M": the region requires `h` large; no claim at small `h`. (3) `hM` is stated
in `ℕ` — no casts needed until `Real`; `Nat.cast_lt`.

**R-b** `atkinLehnerHypothesis_symm`.
**Source**: the symmetry of Prop 3.22 in `ψ ↔ ψ⁻¹` (`lwx.txt:1765`, the relation is an involution
`i ↔ N−1−i`).  **Match**: `B' := P A Q`: `A' B' = P B Q P A Q = P B A Q = P (c•1) Q = c • 1`
(`B A = c • 1` from `A B = c • 1` by `mul_eq_one_comm` on `A (c⁻¹ B)`, `c ≠ 0`); `A = Q B' P`
(`Q P = 1`, `P Q = 1` by `mul_eq_one_comm`), i.e. `P' := Q`, `Q' := P`, `Q' P' = P Q = 1`.
**Attacks**: (1) `c = (ψ p)^(k+1) ≠ 0` ✓. (2) `Matrix.mul_eq_one_comm` is the root `mul_eq_one_comm`
(recorded trap). (3) the existential `B` is not `B⁻¹`-based, so no `Matrix.inv` — clean.

**R-c** `norm_pow_le_of_mem_roots_charpoly_matrixH`, `unitSlope_charpolyRev_matrix_leH`.
**Source**: `lwx.txt:2336–2340` (the classical slopes are the first `N`), via H1 + `‖U_p‖ ≤ 1`
(`JL-AUDIT.md` §2: never via [Bu04, Prop 4]'s converse).
**Match**: `StepThree.lean:415–450` verbatim with `ClassicalDataH`, `c'.weight` (level `h`),
`norm_le_one_of_isRoot_charpoly_upMatrix` (general), `norm_roots_charpoly_atkinLehner`,
`Matrix.roots_charpolyRev`, `exists_evalT_eq_zero_of_unitSlope_eq`, `coeff_charpolyRev_card`,
`Fintype.card_fin`.
**Attacks**: (1) the `Fin (card ι * ((k+1) * p^h))` size enters only through `Fintype.card_fin` ✓.
(2) the level-`1` statements' `(c.matrix idx).charpolyRev : PowerSeries K` coercion — kept
(`Polynomial.coe`). (3) `hj : j < N` needed for `unitSlope ≠ ⊤` (`unitSlope_ne_top_of_height_natCast`
with `coeff N ≠ 0` ⇔ `det ≠ 0`) ✓ as at level `1`.

**R-d** `specCharSeries_eq_mul_charpolyRevH`, `unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH`.
**Source**: `lwx.txt:2336–2340`; the route of `Touching.lean`'s module docstring ("a deliberate
weakening of the source's route").
**Match**: the private `specCharSeries_eq_mul_charpolyRev` (`StepThree.lean:576–583`) made public
at level `h`: `charPowerSeries_eq_mul_of_stable h k hcomp hst`,
`charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix h k`, and the seam
`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h …`; then
`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le` with `f = R`, `g = det(1 − XA)`, `n = N`,
`hle` from R-c (`≤ (k+1)v(p)`) and `le_unitSlope_compl θG h ψ U hU vRep hvΔ idx uu c.weight d.weight
c.shape d.shape hdet (haloRhoH_nonneg h T₀) (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape j`
(`≥ (k+1)v(p)`); `hf0`, `hg0` from `charCoeff_zero` and `Matrix.eval_charpolyRev`; restrictedness
from `charPowerSeries_isEntire` (compactoid, `isCompactoid_discHeckeBlockOp h`) and
`Polynomial.isRestricted_toPowerSeries`.
**Attacks**: (1) `le_unitSlope_compl` takes `κ` and `κ'` with *independent* `{UK} {ρ}` `{UK'} {ρ'}`
(`StepThree.lean:241`, after the `lwx-h1` B2 repair) — `c.weight`/`d.weight` fit ✓. (2) the
`WithBotTop ℝ` inequality chain: `unitSlope_G i ≤ ((k+1)v(p) : ℝ) ≤ unitSlope_R j` — both lemmas
are stated with the coercion `(((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ)` ✓ identical spelling
(copied). (3) `hdet` (`det certM1 = p`) is required by `le_unitSlope_compl` (through
`norm_le_of_eigen_compl`) — added to the hypotheses of R7/R9/R11 ✓.

**R-e** `toReal_unitSlope_charpolyRev_reflect`.
**Source**: `lwx.txt:1765` (Prop 3.22's displayed reflection of the *sorted* slopes) and
`lwx.txt:2340–2350`.
**Match**: with `f = A.charpolyRev`, `f' = A'.charpolyRev` (`coeff 0 = 1`, `Matrix.eval_charpolyRev`):
`roots f' = (roots (charpoly A')).map (·⁻¹)` (`Matrix.roots_charpolyRev`, `det A' ≠ 0` from
`hroots` and `hA`: `∏ roots ≠ 0`) `= (roots (charpoly A)).map (x ↦ x/c)`; so for `σ : ℝ`,
`faceRight_{f'} σ = #{x ∈ roots(charpoly A) : ‖x/c‖ ≤ e^σ} = #{x : ‖x⁻¹‖ ≥ (‖c‖e^σ)⁻¹}
= n − #{y ∈ roots f : ‖y‖ < e^{−log‖c‖ − σ}} = n − faceLeft_f(−log‖c‖ − σ)`
(`faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self`, `Multiset.card_filter`,
`Multiset.filter_map`, `Multiset.card_map`, `card roots = n` from `Polynomial.natDegree_eq_card_roots
(IsAlgClosed.splits _)` and `natDegree f = n` (`coeff_charpolyRev_card`, `det ≠ 0`)).
Then for `i < n`: `unitSlope_{f'}(n−1−i) ≤ σ ⇔ n−1−i < faceRight_{f'} σ` (`unitSlope_le_of_lt_faceRight`,
`lt_unitSlope_of_faceRight_le` + `SlopesUnbounded` from `slopesUnbounded_newtonPolygon₀OfPowerSeries`)
`⇔ faceLeft_f(τ) ≤ i ⇔ τ ≤ unitSlope_f(i)` (`le_unitSlope_of_faceLeft_le`, `faceLeft_le_of_le_unitSlope`),
`τ = −log‖c‖ − σ`; both unit slopes are real (`unitSlope_ne_top_of_lt_natDegree`, `unitSlope_ne_bot`),
so `toReal` and `le_antisymm` over all `σ` give the identity.
**Attacks**: (1) sign conventions: the polygon of `charpolyRev A` has slopes `log‖x‖` for the
roots `x = λ⁻¹` of `charpolyRev`, i.e. `−log‖λ‖` for the eigenvalues — `unitSlope_le_iff_lt_card_roots_le`'s
statement (`unitSlope j ≤ σ ↔ j < #{roots x : ‖x‖ ≤ e^σ}`) fixes it; the reflection
`s' = −log‖c‖ − s` then reads: eigenvalue `c/λ` has slope `−log‖c‖ + log‖λ‖ = −log‖c‖ − s` ✓.
(2) `n − 1 − i` with natural subtraction: `i < n` so `n − 1 − i + i = n − 1` (`omega`); the
counting identity `n−1−i < n − m ⇔ m ≤ i` needs `m ≤ n` (`faceLeft ≤ n`, from the card bound). (3) the
lemma is about arbitrary `n`-indexed matrices; instantiate at `Fin N` — `Fintype.card_fin`. (4)
`[IsAlgClosed K]` required by the `_self` counting lemmas ✓ present.

**R-f** `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` (abstract M2).
**Source**: `lwx.txt:2322–2350` (§0).
**Match**: for `j < N`: `v·r_j = unitSlope_j(det at T₀)` (`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θG U hU vRep hvΔ idx uu h hp2 c.h0 c.h1 c.hT (c.inv_pow_lt_norm_pow hh hM) hshape hband j`
+ seam) `= unitSlope_j(det(1 − XA))` (R-d); same at `T₀'` with `hAL` symmetrised (R-b) and `d'`;
R-e with `hroots := roots_charpoly_of_atkinLehnerHypothesis h k hAL`, `c := (ψ p)^(k+1)`;
`v = v'` (`ClassicalDataH.norm_eq hh c c'`); `−log‖(ψ p)^(k+1)‖ = (k+1)(−log‖ψ p‖)`; divide by
`v > 0` (`c.h0`, `inv_pos`) using `c.mul_neg_log_norm_eq`.
**Attacks**: (1) the two slope readings need `hκ` at `T₀` and `T₀'` — from R-a at both data
(`c'.inv_pow_lt_norm_pow`). (2) `slopeRatio` is `toReal` of the shape polygon's unit slope, and
the reading lemma's RHS is the coercion of `(−log‖T₀‖) * slopeRatio …` — `WithBotTop.coe_inj` to
extract the real identity; then `NewtonPolygon.toReal_coe`. (3) `N − 1 − i < N` ✓ `omega` from
`hi`. (4) all of `hband`, `hband'` are genuinely needed (the reading lemma quantifies over all
vertices) — cannot be weakened here; design decision 9.

**R-g** `hasUnitBand_of_atkinLehnerData`.
**Source**: `lwx.txt:1807–1846` (Step I); the ledger row 1 of `.mathlib-quality/lwx-stepone/FINDINGS.md`.
**Match**: `hasUnitBand_of_atkinLehnerHypothesis` at `classicalData` and its partner with
`atkinLehnerHypothesis_of_atkinLehnerData` (the term is the body of `degX_succ_of_atkinLehnerData`
minus the degree step).
**Attacks**: (1) `hasUnitBand_of_atkinLehnerHypothesis` needs no `[IsAlgClosed K]` and no `hdet` ✓
(its statement `Touching.lean:772`). (2) one `k` at a time, one disc at a time — the family
(F-a) is what turns it into `∀ ω n`. (3) `hζ : IsPrimitiveRoot ζ p` (level `1`) — the family's
`ζ₁`.

### Part F — `PhD/LWX/AtkinLehnerFamily.lean`

**F-a** `AtkinLehnerFamily`, `toData`, `vRepF`, `upEltF`, `vRepF_mem_levelM1`, `upEltF_mem_levelM1`,
`vRepD_toData`, `upEltD_toData`; `AtkinLehnerFamilyH`, `toDataH`, `vRepDH_toDataH`, `upEltDH_toDataH`.
**Source**: `lwx.txt:2322` ("weights of the form (k, ψ) for all k ≥ 0"), `2351` ("Replacing ψ by
ψω₀⁻¹ and k by k + 1"), `2356–2359` ("for any character ω of Δ … Choose ψ so that ψ|_Δ·ω₀^k = ω");
`lwx-h1/plan.md` design decision 4 (the data as hypotheses).
**Match**: `AtkinLehnerData` (`AtkinLehnerMap.lean:149–168`) with `χ` indexed by `(ω, k)` and the
nebentypus `nebCharK ψ ω k ζ`; `toData θG ψ U F ω k` is the structure literal over `F.ιp`, so
`vRepD θG ψ U (AtkinLehnerFamily.toData θG ψ U F ω k) c = (AtkinLehnerFamily.toData θG ψ U F ω k).ιp (vGL p c) = F.ιp (vGL p c) = vRepF θG ψ U F c`
by projection reduction — the `rfl` lemmas compile in the skeleton.  Same at level `h` over the
same section.
**Attacks**: (1) is one section for all `(ω, k)` a genuine restriction?  No: `ιp` is the
`p`-component section of `D^×(𝔸_f)`, independent of the weight; only `χ ω k = ψ_{A,ω,k} ∘ ν`
varies. (2) could the level-`h` family be indexed by `(h, ζh)` inside one structure?  Quantifying
over all `ζ` would make it uninhabitable (the nebentypus is a character only when `ζ^{p^h} = 1`);
so `ζh` is a parameter and the level-`h` family is a separate structure over `F` — one per
`(h, ζh)`. (3) `χ_U` for the family: `(χ ω k u : K) = nebCharK ψ ω k ζ (ψ (det θG u))` is the
level-`1` `AtkinLehnerData.χ_U` at `nebK := nebCharK ψ ω k ζ` verbatim, so `toData` needs no
proof. (4) `vRepF_mem_levelM1` is `vRepD_mem_levelM1` at `AtkinLehnerFamily.toData θG ψ U F 1 0` (any `(ω, k)` would do)
— compiled as a term.

**F-b** `invChar_eq_inv`, `partnerChar_succ`, `partnerChar_invChar_mul_teichChar_pow`, `teichChar_pow_sub_one`.
**Source**: `lwx.txt:2351–2363` (the substitutions `ψ ↦ ψω₀⁻¹`, `k ↦ k+1`; "Choose ψ so that
ψ|_Δ·ω₀^k = ω"; "since ω₀^{ϕ(q)} = 1").
**Match**: `invChar ω = ω⁻¹` in the commutative group `(ℤ/p)^× →* ℤ_p^×` (`invChar_apply`,
`MonoidHom.inv_apply`, both `rfl`); `partnerChar p ω k = invChar ω * teichChar p ^ (2k)`
(`NebChar.lean:397`), so `partnerChar p ω (k+1) = partnerChar p ω k * teichChar p ^ 2`
(`Nat.mul_succ`, `pow_add`) and `partnerChar p (invChar ω * τ^{2k}) k = (ω⁻¹τ^{2k})⁻¹ τ^{2k} = ω`
(`mul_inv`, `inv_inv`, `inv_mul_cancel_right`); `teichChar p ^ (p−1) = 1` by `MonoidHom.ext`,
`MonoidHom.pow_apply`, `← map_pow`, Fermat `r ^ (p−1) = 1` in `(ℤ/p)^×`
(`ZMod.units_pow_card_sub_one_eq_one`), `map_one`.
**Attacks**: (1) `teichChar` is a `MonoidHom` (`TargetPoint.lean:51`, `map_mul' := teichRes_mul`),
so `map_pow` applies — no analytic property of `teichmuller` is needed. (2) the `CommGroup`
instance on `MonoidHom`s into `ℤ_p^×` is the one `partnerChar`'s `*`/`^` already use ✓.
(3) `2 * (k+1) = 2*k + 2` in the exponent — `Nat.mul_succ`/`omega` inside `pow_add`.

**R-h** `hasUnitBand_of_atkinLehnerFamily`, `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily`.
**Source**: ledger row 1; [LWX, Thm 1.5 (1.5.1)] `lwx.txt:175–180`.
**Match**: `n = 0`: `hasUnitBand_zero`; `n = k+1`: R-g at `AtkinLehnerFamily.toData θG ψ U F ω k`, whose `UpDatum`
`UpDatum.ofCerts … (vRepD θG ψ U (AtkinLehnerFamily.toData θG ψ U F ω k)) …` is `UpDatum.ofCerts … (vRepF θG ψ U F) …`
by `vRepD_toData` (`rfl`; the `hvΔ`/`hshape` arguments are Props).  The unconditional (1.5.1) is
`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (`SlopesSeam.lean:145`) with
`hband := hasUnitBand_of_atkinLehnerFamily … ω`.
**Attacks**: (1) the coset hypotheses `hfin`, `hv`, `hvinj`, `hfact` are stated for
`upEltF`/`vRepF` and passed where `upEltD (AtkinLehnerFamily.toData θG ψ U F ω k)`/`vRepD (AtkinLehnerFamily.toData θG ψ U F ω k)` are expected —
defeq (`upEltD_toData`, `vRepD_toData` are `rfl`); if `exact` is slow, `simpa only [upEltD_toData,
vRepD_toData] using …`. (2) `include hfin hv hvinj c hc hstab d hd hfact in`: these section
variables are not in the statements — the `include` is mandatory (the `lwx-h1` B2 on
`theta_mem_Iw`). (3) `ζ₁` (level `1`) and `ζ` (level `h`) are distinct roots of unity; the
family's `χ_U` is at `ζ₁` only.

**R-i** `slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH` (**M2**).
**Source**: `lwx.txt:2322–2350`.
**Match**: R-f at `classicalDataH ψ ω … (vRepF F) … hζ … k`, its partner at `hζ.inv`,
`targetData_classicalPointH` at both, `hAL := atkinLehnerHypothesis_of_atkinLehnerDataH … (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k) …`
(its type mentions `vRepDH θG ψ U h (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k)`, which is `vRepF θG ψ U F` by
`vRepDH_toDataH`, `rfl`), `hband`/`hband'` from R-h at `ω` and `partnerChar p ω k`.
**Attacks**: (1) the partner's target `targetData_classicalPointH ψ (partnerChar p ω k) … hζ.inv …`
has `ω₁ = targetChar p (partnerChar p ω k) k` — unconstrained in R-f ✓. (2) `hshape`/`hdet` are
stated once for `vRepF F` and consumed by R-f whose section `vRep` is instantiated at `vRepF F` ✓.
(3) the level-`h` family is used only at the one `(ω, k)`; its other characters are needed by R-j.

**R-j** `slopeRatio_partnerChar_succ` ((4.2.5)), `slopeRatio_mul_teichChar_sq` ((4.2.6) = (1.5.2)).
**Source**: `lwx.txt:2351–2360` (verbatim in `plan.md`, "The source ranges over every classical
weight").
**Match**: (4.2.5): R-i at `(ω, k, i)` and `(ω, k+1, i)` (`i < N_k ≤ N_{k+1}`), `linarith` with
`((k+2 : ℕ) : ℝ) = (k+1) + 1`.  (4.2.6): `T := p^h · t > 0` (`[Nonempty ι]`), `k := j / T`,
`hj : j < N_k` (`Nat.lt_div_mul_add`; `N_k = (k+1)·T` up to `ring`), `i := N_k − 1 − j`,
`ω := invChar ω' * teichChar p ^ (2*k)`; R-j(4.2.5) at `(ω, k, i)`; rewrite
`partnerChar p ω k = ω'` (F-b), `partnerChar p ω (k+1) = ω' * teichChar p ^ 2` (F-b),
`N_k − 1 − i = j` and `N_{k+1} − 1 − i = j + T` (`omega` after `N_{k+1} = N_k + T` by `ring`).
**Attacks**: (1) the index bookkeeping is `ℕ`-subtraction: `j ≤ N_k − 1` from `hj` makes
`N_k − 1 − (N_k − 1 − j) = j` valid (`omega`). (2) [LWX] restrict (4.2.5) to `i ≤ q^{−1}p^Mt − 1`
so that the same `i` serves both `k` and `k+1` blocks; our (4.2.5) holds for every `i < N_k`
(the reflection is valid on the whole classical block), which covers theirs. (3) `t = 0` would
break `Nat.lt_div_mul_add` — excluded by `[Nonempty ι]` (`Fintype.card_pos`).

**R-k** `slopeRatio_mul_teichChar_pow`, `slopeRatio_add_period` (**M3**).
**Source**: `lwx.txt:2361–2366` ("since ω₀^{ϕ(q)} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) =
α̃_j(ω) + ϕ(q)p^M/(2q²) … disjoint union of arithmetic progressions").
**Match**: induction on `m` with (4.2.6) at `ω * teichChar p ^ (2m)`: `ω τ^{2m} τ² = ω τ^{2(m+1)}`
(`pow_succ`, `pow_add`, `mul_assoc`), `j + m T + T = j + (m+1) T` (`Nat.succ_mul`); then
`m := (p−1)/2`: `2 * ((p−1)/2) = p − 1` (`Nat.two_mul_div_two_of_even`, `p − 1` even for odd `p`:
`hp.out.eq_two_or_odd'`, `hp2`, `Nat.Odd.sub_odd`), `teichChar_pow_sub_one`, `mul_one`.
**Attacks**: (1) the difference constant `((p−1)/2 : ℕ) · e` in `ℝ` is [LWX]'s `ϕ(q)p^M/(2q²)`
times `ϕ(q)`: `(p−1)/2 · p^{h−1}(p−1) = (p−1)²p^{h−1}/2` ✓ (`plan.md`). (2) the period
`(p−1)/2 · p^h t` is [LWX]'s `(p−1)p^{M−1}t/2` with `M = h+1` ✓. (3) [LWX]'s "disjoint union of
`(p−1)p^{M−1}t/2` arithmetic progressions" is exactly the periodicity statement; the residue-class
decomposition is not formalised separately (it is a restatement).

## 3. Prior-B2 consultation

`.mathlib-quality/lwx-h1/b2_log.jsonl` (2 entries, both repaired in place): (i) `theta_mem_Iw`
lost `hU` — here every statement mentioning `hU` is checked (`discShiftH_mem_U`, `theta_discShiftH`,
… all mention `hU` in their types; `theta_mem_Iw` itself is reused, not restated); (ii) `κ'` must
carry its own `{UK'} {ρ'}` — every level-`h` statement with a second weight does
(`AtkinLehnerMapH.lean`, `AtkinLehnerIdentityH.lean`, `le_unitSlope_compl`'s use in R-d).
`.mathlib-quality/lwx-theta/b2_log.jsonl` (6 entries): no `ν`-equivariance is used (all
equivariance through `hκ`/`hκ'` shape hypotheses); no slope statement quantifies past a degree
(R-c/R-e carry `j < N`, `i < n`).  `.mathlib-quality/lwx-theta-h2/b2_log.jsonl`,
`.mathlib-quality/lwx-atkinlehner/b2_log.jsonl`: empty.  Root `.mathlib-quality/b2_log.jsonl`:
NewtonPolygons, unrelated.  Three defects were found by this pass and repaired in the skeleton
before ticketing (L-a, T-a, R-b); this board's `b2_log.jsonl` starts empty.

## 4. Confidence gate

- Every leaf has a source locator and a Lean ↔ source match paragraph: **yes** (T-a … R-g).
- Every leaf survived ≥ 3 attacks or was repaired: **yes**; three defects repaired in the skeleton.
- No leaf needs infrastructure absent from mathlib: **yes** — prime-power cyclotomic facts, `toZModPow`,
  and the root-counting lemmas of `RootFaces.lean` all exist; the reflection lemma R-e is ~120 lines
  of bookkeeping on existing API.
- Skeleton builds with sorry warnings only: recorded in `tickets.md`'s header (the build result of
  2026-09-11).
- Out-of-scope items named in `plan.md`: Step III at level `h`; instantiation of
  `AtkinLehnerFamily`/`AtkinLehnerFamilyH`; the rigid-analytic packaging; `p = 2`.
- Revision 2026-09-11 (user): the unit bands are no longer hypotheses — Part F and R-h…R-k added;
  every leaf above re-checked against the family statements (the `UpDatum` is `vRepF F`'s
  throughout, by `rfl`).

## Post-execution notes (2026-09-11, `/beastmode`)

Two defects this adversarial pass did not catch, both found while proving:

- **R13–R17 `include` lists** omitted the level-`h` family `X : AtkinLehnerFamilyH θG ψ U F h ζ`,
  which no binder mentions, so the elaborated statements had no level-`h` Hecke characters and were
  unprovable for abstract data.  Repaired in place by adding `X` to the five include lists (B2
  entries in `b2_log.jsonl`).  Attack to add to the checklist: for every `include … in` theorem,
  list the section structures its proof must consume and check each one is mentioned or included.
- **R-e (R8) sketch** wrote the roots of `A'.charpolyRev` as `y/c` with `y` a root of
  `A.charpolyRev`; they are `x/c` with `x` a root of `A.charpoly`.  The statement was right; the
  proof counts over the roots of `A.charpoly` directly.
