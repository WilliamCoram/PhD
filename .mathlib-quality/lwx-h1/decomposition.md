# Decomposition — `lwx-h1` (hypothesis H1 at the classical points)

**BOARD PATH: `.mathlib-quality/lwx-h1/`.**  Companion to `plan.md`; read both before working a
ticket.  Written 2026-09-10, after the adversarial planning pass.  References by locator:
`lwx.txt` = `.mathlib-quality/tate-riesz/references/lwx.txt`, `bu04.txt` =
`.mathlib-quality/lwx-stepone/references/bu04.txt`, `scratch` = `PhD/Test/AtkinLehnerIdentity.lean`.

## 0. The goal, and what the sources actually say

**Target.** `LWX.AtkinLehnerHypothesis ψ 1 k A B A'` (`PhD/LWX/AtkinLehnerInst.lean:221`)
at `A = (classicalData ψ ω …).matrix idx`, `A' = (classicalData ψ (partnerChar p ω k) … ζ⁻¹ …).matrix idx`:

```
A * B = (ψ p)^(k+1) • 1  ∧  ∃ P Q, Q * P = 1 ∧ A' = P * B * Q.
```

**The source statement** (`lwx.txt:1763–1768`):

> "Proposition 3.22 (Atkin–Lehner). We use α₀(ψ),…,α_{(k+1)q⁻¹pᵐt−1}(ψ) to denote the slopes of
> U_p acting on S^D_{k+2}(K^pIw_{pᵐ},ψ) in non-decreasing order. Then we have
> α_i(ψ) = k + 1 − α_{(k+1)q⁻¹pᵐt−1−i}(ψ⁻¹) for i = 0,…,(k+1)q⁻¹pᵐt − 1."

**The source proof** (`lwx.txt:1770–1789`) is by Jacquet–Langlands and is *not* transcribed:

> "Since ψ has conductor pᵐ while the level structure at p is Iw_{pᵐ}, by applying
> Jacquet–Langlands and [LW12, Proposition 2.8], we see that for every automorphic
> representation π appearing in S^D_{k+2}(K^pIw_{pᵐ};ψ), its p-component π_p is a principal
> series of GL₂(Q_p) whose corresponding two characters of Q_p^× are unr(α) and unr(α⁻¹)⊗ω_p
> … But we can twist the representation π by a central Hecke character associated to ψ⁻¹; then
> the resulting automorphic representation would appear in S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹) …
> In conclusion, one can pair the U_p-eigenvalues of S^D_{k+2}(K^pIw_{pᵐ};ψ) and the
> U_p-eigenvalues of S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹) so that they multiply to p^{k+1}."

What *is* transcribed from this passage: (i) the pairing is between `(k, ψ)` and `(k, ψ⁻¹)`
with product `p^{k+1}` — our `A * B = p^{k+1}`; (ii) the passage from `ψ` to `ψ⁻¹` is
**a twist by a central Hecke character** — our `AtkinLehnerData.χ` (design decision 4 of
`plan.md`).  The mechanism that replaces the representation theory is the elementary
double-coset expansion, whose matrix identities are *proved* in `scratch` (sorry-free); the
classical statement it establishes is Miyake Thm 4.6.17 as cited at `bu04.txt:1122–1124`
("Theorem 4.6.17 of [15], the fact that λ is an algebraic integer" — the `|a_p|² = p^{k−1}`
relation at conductor = level).

**Where H1 is consumed.** `degX_succ_classicalPoint` (`PhD/LWX/DegreeFormula.lean:56`) takes
`hAL : ∃ B, AtkinLehnerHypothesis ψ 1 k (c.matrix idx) B (c'.matrix idx)` with `c, c'` the
classical data at `(ω, ζ)` and `(ω', ζ')`; Step III (`lwx.txt:2028–2036`) needs `ω' = ω⁻¹ω₀^{2k}`:

> "By Atkin–Lehner theory (Proposition 3.22) and Proposition 2.15, the multiplicity is the same
> as the dimension of slope zero subspace in S^{D,†}_{(k,ψ⁻¹)}. Using Corollary 3.21 again, we
> deduce that n_{k+1} − n⁻_{k+1} = r_ord(ψ⁻¹|_Δ · ω₀^k) = r_ord(ω⁻¹ω₀^{2k})".

So the partner datum must carry the nebentypus `ψ⁻¹` — Part N's `nebChar_partnerChar`.

## 1. The prose proof (the route the tickets transcribe)

Work at level `h = 1` (conductor `p²`, `lwx.txt:2028`: "classical weights χ_k = (k,ψ) of
conductor q²"), in the disc model of `DiscModel.lean`: a form is `φ : G → c(ℤ/p × ℕ, K)`,
left-`Γ`-invariant, with `φ(xu) = φ(x) ∣ θ(u)` for `u ∈ U` (`mem_discForms_iff`), and
*classical* when every `φ(x)` is locally polynomial of degree `≤ k` on each disc
(`lwx.txt:655–662`: "those functions whose restriction to a + q⁻¹pᵐZ_p is a polynomial function
of degree ≤ k for all a ∈ Z_p").

**Step A (the `Sym^k` action).**  At a classical-shape matrix `g` (`autFactor g · L = C u ·
L^{k+1}`), `kappaSlash g` acts on polynomials of degree `≤ k` by `u · symAct k g` where
`symAct k g : z^i ↦ (cz+d)^{k−i}(az+b)^i` — this is (2.3.2) at `lwx.txt:600–604`,
`h|_χ γ (z) = χ(cz+d) h((az+b)/(cz+d))`, with `χ(cz+d) = ψ_neb(d) (cz+d)^k` on polynomials.
`symAct` is a right action: `symAct γ' (symAct γ f) = symAct (γγ') f` (the cocycle
`hsub_linX_pow_mul_numX_pow`).

**Step B (the nebentypus).**  `nebChar a = haloCharFunH(a)·a^{−k}` is the constant `u` of the
classical shape at the classical point (`autFactor_haloWeightH_classicalPoint`,
`ClassicalPoint.lean:412`).  It is multiplicative, trivial on `1 + p²ℤ_p`
(`specialize_univChar_eq_padicExp` at `h = 1`), and `nebChar(1+p)` is a primitive `p`-th root of
unity (`nebChar_oneAddPMul` + `norm_padicLog_eq`).  Hence for `p ∤ b`,
`∑_{c<p} nebChar(1 + pbc)⁻¹ = 0` (`IsPrimitiveRoot.geom_sum_eq_zero`).  At `ζ⁻¹` with tame
character `ω⁻¹ω₀^{2k}` the nebentypus is `nebChar⁻¹` (`oneAddPow_inv_sub_one_mul`,
`teichRes^{2k}` cancels the `a^{−k}` twice).

**Step C (local matrices, disc-model coordinate, `h = 1`).**  `U_p`-representatives
`vQ c = (p 0; cp 1)` (`lwx.txt:684–688`, `v_j = (p 0; jq 1)`), `wQ = (0 p; −p 0)`,
`sQ b = (1 b; 0 1)`.  The key factorisation (`scratch`, `upRep_mul_upAdjRep` +
`obstruction_mul_lowerUni`, transported by `t₀`):

```
wQ · vQ b · wQ⁻¹ · vQ c = ℓQ b c · (p • sQ (−b)),   ℓQ b c = (1−bcp, −b²cp; cp, 1+bcp) ∈ Iw_p.
```

`ℓQ b c` fixes disc `0` and its disc-`0` conjugate has `d`-entry `1 + bcp`; `sQ b` moves disc
`0` to disc `b` with trivial conjugate.

**Step D (the Atkin–Lehner map).**  With the data `D` (section `ιp`, `ιp(Iw_p) ⊆ U`, the central
decomposition of `ιp(p·1)`, the Hecke character `χ`), define on disc `a`:

```
(Wφ)(x)|_a := χ(x s_a)⁻¹ · symAct k w₂ ( φ(x s_a w⁻¹)|_0 ),    w₂ = t₀⁻¹ wQ t₀ = (0 1; −p² 0),
```

(`shapiro_blockProj`: `φ(x)|_a = φ(x s_a)|_0`).  `W` is left-`Γ`-invariant (from `χ|_Γ = 1`),
locally polynomial (`symAct_mem_polySubmodule`), and `(Wφ)(xu) = (Wφ)(x) ∣_{κ'} u` for `u ∈ U`
where `κ'` has nebentypus `nebK⁻¹`: on disc `0`, for `u` fixing disc `0`, `w u w⁻¹ ∈ Iw_p` has
`d`-entry `= a(u)` (`atkinLehnerConj_apply_one_one`), and `nebK(a)·nebK(d) = nebK(det u) = χ(u)`
cancels — this is exactly the "twist by a central Hecke character associated to ψ⁻¹" of
`lwx.txt:1783–1785`.  `W' := ` the same with `w`, `χ`, `w₂⁻¹`; `W'W = 1 = WW'` from `χ(w) = 1`,
`symAct_mul`, `symAct_one`.

**Step E (the identity on disc `0`).**  `(U_p φ)(x) = ∑_c φ(x v_c⁻¹) ∣ v_c` (the naive Hecke
formula, `heckeOperatorSlash_apply_rep` with the trivial factorisation; `bu04.txt:645–649`:
"[UηU]f = ∑_i f|η_i" with `(f|η)(g) = f(gη⁻¹)η_p`, `bu04.txt:633`).  Expanding
`U_p W' U_p^{ψ⁻¹} W φ` on disc `0` gives a double sum over `(b, c)`, whose `(b,c)`-term is, after
the factorisation of Step C and the level-equivariance at `ℓ_{b,c}` (read on disc `0`,
`blockProj_zero_apply_mul_ιp`) and the triviality of the central `p` (`apply_mul_ιp_pGL`):

```
nebK(1 + bcp)⁻¹ · p^k · symAct k (1 −b/p; 0 1) ( φ(x)|_b ).
```

The `b = 0` terms sum to `p · p^k · φ(x)|_0`; for `b ≠ 0` the sum over `c` of `nebK(1+bcp)⁻¹`
vanishes (Step B).  Hence `U_p W' U_p^{ψ⁻¹} W φ (x)|_0 = p^{k+1} φ(x)|_0`, and by
`shapiro_blockProj` on every disc.

**Step F (transport).**  At a neat level (`lwx.txt:841–848`: "The condition (Neat) implies that
the natural map D^× × K^pIw_q → D^×γ_iK^pIw_q for each i sending (δ,u) to δγ_iu is bijective";
our `hstab`), evaluation at the representatives is an isomorphism of the classical disc forms
onto `locPolyDegSubmoduleBlock` (`bijective_discEvalAtReps_of_stabilizer_eq_bot`), carrying
`U_p` to the block operator of the certificates (`discEvalAtReps_discHeckeOperator`).  The
matrices `A = upMatrix(discHeckeBlockOp κ)`, `A' = upMatrix(discHeckeBlockOp κ')` are
`LinearMap.toMatrix` of the restrictions; put `B := toMatrix(W_b⁻¹ ∘ T_{κ'} ∘ W_b)` with `W_b` the
block-transported `W`; `A B = p^{k+1}` is Step E and `A' = W_b B W_b⁻¹` by construction.

## 2. Leaves, with source locators, Lean ↔ source match, and attacks

Format: leaf → declaration(s); **Source**; **Match**; **Attacks** (each attack tried and its
outcome — an attack that succeeded changed the skeleton before this document was written).

### Part S — `PhD/LWX/SymPow.lean`

**S-a** `hsub`, `hsub_mul`, `hsub_linX`, `hsub_numX`, `hsub_pow_of_degree_le_one`.
**Source**: pure algebra, no source needed; the binary-form reading of a degree-`≤k` polynomial
is the standard model of `Sym^k` (implicit in `lwx.txt:604`: `h((az+b)/(cz+d))` times
`(cz+d)^k` is a polynomial in `z` of degree `≤ k`).
**Match**: `hsub k P N L = ∑_{i≤k} P_i L^{k−i} N^i` is `L^k · P(N/L)`.
**Attacks**: (1) is `hsub` multiplicative without the degree hypotheses? No — `hsub (k₁+k₂)` of
a product only sees coefficients `≤ k₁+k₂`; with `P` of degree `> k₁` the identity fails
(e.g. `k₁ = 0`, `P = X`, `Q = 1`); hence `hP, hQ` are necessary and present.  (2) `k − i` with
natural subtraction: all sums range over `i ≤ k`, truncation never triggers; `hsub_pow` uses
`n · 1 = n` consistently.  (3) `hsub_linX` for `k = 1` needs `coeff 1 (linX γ) = γ 1 0` and
`coeff 0 = γ 1 1` — matches `linX γ = C(γ 1 1) + C(γ 1 0) X` (`QMF/Weight/Series.lean:167`).

**S-b** `hsub_linX_pow_mul_numX_pow` (the cocycle).
**Source**: the right-action law of (2.3.2), `lwx.txt:560–562`: "the right action of h ∈ Iw_q
by sending f to f||_χ h : g ↦ f(gh∗)" — a right action, and `(2.3.2)` is its explicit form.
**Match**: substituting `z ↦ (a'z+b')/(c'z+d')` into `(cz+d)^{k−i}(az+b)^i` and clearing
`(c'z+d')^k` gives `(c''z+d'')^{k−i}(a''z+b'')^i` for `γγ'` — computed: `c(a'z+b') + d(c'z+d')
= (ca'+dc')z + (cb'+dd')`, the second row of `γγ'`.  **This is the order convention check: the
matrix product is `γ * γ'`, the second substitution acts first.**
**Attacks**: (1) tried the opposite order (`γ' * γ`): the linear factor would be
`(c'a+d'c)z + …`, which is not what the substitution produces — rejected, `γ * γ'` is right.
(2) `hsub_mul` with `k₁ = k − i`, `k₂ = i` and `hsub_pow` on each factor: degrees match
(`(k−i) + i = k` by `hi`).  (3) `i = k`: `linX^0 = 1`, `hsub 0 1 = 1` — consistent.

**S-c** `polySeq`, `polySeq_apply`, `coeff_linX_pow_mul_numX_pow_eq_zero`, `symAct`,
`symAct_apply`, `symAct_mem_polySubmodule`.
**Source**: `lwx.txt:655–662` (the algebraic subspace is degree `≤ k` polynomials).
**Match**: `symAct k γ f j = ∑_{i≤k} f i · coeff j ((cz+d)^{k−i}(az+b)^i)`, the matrix of
`Sym^k` in the monomial basis, extended by `0` on `z^i`, `i > k`.
**Attacks**: (1) the `sorry` in `symAct` is `i ∈ range (k+1) → i < k+1`: `Finset.mem_range`.
(2) continuity: `polySeq` is a finitely-supported sequence — `cSpace.ofTendsto` with the
`Tendsto … cofinite` proof already written and compiling.  (3) `symAct` is `→L[K]`: a finite
sum of `evalCLM i |>.smulRight v`, each continuous — fine.

**S-d** `symAct_mul`, `symAct_one`, `symAct_smul_one`.
**Source**: right action, `lwx.txt:560–562`; scalar matrices act by `(xz·0 + x)^k = x^k` on
polynomials of degree `≤ k` (the weight-`k` central character).
**Match**: `symAct_mul` on `polySubmodule K k`: both sides are `∑_{i≤k} f i · coeff j (…)`; the
cocycle S-b identifies the column polynomials.  `symAct_one`: `linX 1 = 1`, `numX 1 = X`, so
`z^i ↦ z^i`.  `symAct_smul_one`: `linX (x•1) = C x`, `numX (x•1) = C x · X`, so
`z^i ↦ x^{k−i} x^i z^i = x^k z^i`.
**Attacks**: (1) does `symAct_mul` hold off `polySubmodule`? No: `symAct γ f` ignores `f i` for
`i > k`, and `symAct (γγ') f` too, but `symAct γ' (symAct γ f)` … also ignores them; in fact the
identity may hold for all `f` — the hypothesis `hf` is possibly slack (`_hx` convention: keep it,
note it at cleanup).  (2) `symAct_one` genuinely needs `hf` (`f i` for `i > k` is killed).
(3) `x = 0`: `symAct (0) f = (f 0 · 0^k …)`; for `k = 0` `0^0 = 1` — `x^k • f` with `k = 0` is
`f`, and `symAct 0 f j = f 0 · coeff j 1 = f 0 · [j = 0]`, equal to `f` on `polySubmodule 0`. OK.

**S-e** `kappaSlash_eq_smul_symAct_of_shape`.
**Source**: (2.3.2) `lwx.txt:600–604` and `Touching.lean:181` (`autFactor_mul_mobius_pow_of_shape`:
`autFactor g · mobius g^i = C u · (cz+d)^{k−i}(az+b)^i` for `i ≤ k`).
**Match**: `kappaSlash_apply` (`SlashAction.lean:462`): `(κ.kappaSlash g f) j = ∑' i, coeff j
(autFactor · mobius^i) · f i`; on `polySubmodule` the `tsum` is the finite sum over `i ≤ k`, and
each term is `u · coeff j (column polynomial) · f i`.
**Attacks**: (1) the `tsum` over `ℕ` vs. finite sum: `tsum_eq_sum` with support in `range (k+1)`
(from `hf`).  (2) is `hd : g 1 1 ≠ 0` needed by `autFactor_mul_mobius_pow_of_shape`? Yes, and it
follows from `g ∈ S` via `κ.toWeightSeries.bounds.d_ne_zero g.2` (as in `kappaSlash_apply`'s
proof). (3) name check: `AnalyticWeight.kappaSlash_def` (`Char.lean:813`) rewrites to the
`WeightSeries` slash.

### Part N — `PhD/LWX/NebChar.lean`

**N-a** `isUnit_one_add_p_mul`, `oneAddPMul`, `coe_oneAddPMul`.
**Source**: `lwx.txt:413–414` ("Z_p^× as Δ × (1+qZ_p)^×").  **Match**: `‖1 + px − 1‖ ≤ p⁻¹ < 1`.
**Attacks**: `PadicInt.isUnit_iff` (`‖x‖ = 1`); ultrametric `‖1 + px‖ = 1` since `‖px‖ < 1 = ‖1‖`.

**N-b** `nebCharK`, `nebChar`, `nebChar_apply`, `classicalData_u_eq_nebChar`,
`autFactor_haloWeightH_classicalPoint_eq_nebCharK`.
**Source**: `ClassicalPoint.lean:412–419` (verbatim: `autFactor g · linX g = C (haloCharFunH … (g 1 1)
· (g 1 1)⁻¹^k) · linX g^(k+1)`) and `:461–466` (`classicalData.u i t a = haloCharFunH(certConj … 1 1)
· (…)⁻¹^k`); `haloCharFunH_psi` (`HaloWeightH.lean:731`).
**Match**: `nebCharK x = haloCharFunH 1 ψ (classicalPoint p k ζ) ω x * x⁻¹^k` is literally the
constant; `classicalData_u_eq_nebChar` is `certConj_apply_one_one` (`TargetPoint.lean:312`:
`certConj … 1 1 = intHom ψ (toLocalMat (discConj …)).d`) plus `rfl`.
**Attacks**: (1) `nebChar_apply` needs `haloCharFunH_psi`'s `h0 h1 hT` — supplied by
`inv_lt_norm_classicalPoint`, `norm_classicalPoint_lt_one`, `norm_TH_one_classicalPoint_sq_lt`
(all take `hp2 hζ hpK k`).  (2) `(intHom ψ a)⁻¹ ^ k` vs `(x⁻¹)^k`: `inv_pow` either way.

**N-c** `nebChar_mul`, `nebChar_one`, `nebChar_ne_zero`.
**Source**: `lwx.txt:470–472` ("a continuous character ψ : Z_p^× → E^×").
**Match**: `haloCharFunH_mul` (`HaloWeightH.lean:575`) on `haloUnitsH`, and `intHom ψ a ∈
haloUnitsH` for a unit `a` (`mem_haloUnitsH_of_mem_M1Kh` or directly `‖ψ a‖ = 1`); `a⁻¹^k` is
multiplicative; `nebChar_one` from `nebChar_mul` at `1·1` and non-vanishing; non-vanishing from
`nebChar_mul` at `a·a⁻¹ = 1` with `nebChar 1 ≠ 0` (`haloCharFunH 1 = specialize (univChar 1) =
1`, `univChar_one`).
**Attacks**: (1) `haloCharFunH_mul` requires `x y : Kˣ` in `haloUnitsH h ψ`: build the units from
`‖intHom ψ a‖ = 1` (`hψ`, `PadicInt.norm_units`).  (2) Does `nebChar_one` need `hpK`? Only through
the reuse of `nebChar_mul`; keep the hypotheses as stated (`_hx` slack allowed).

**N-d** `nebChar_of_norm_sub_one_le_sq` (conductor `∣ p²`).
**Source**: `lwx.txt:470–474` (conductor); `HaloWeightH.lean:458–465`
(`specialize_univChar_eq_padicExp`: for `‖u − 1‖ ≤ p^{−(h+1)}`, `specialize (univChar ω u) =
padicExp (haloExponentH … · intHom ψ (logQuot u))` … ).
**Match**: at `h = 1`, `‖a − 1‖ ≤ p⁻²` gives `specialize (univChar ω a) = padicExp(haloExponentH p 1
T₀ · log-quotient)`, and `haloExponentH_one_classicalPoint` (`ClassicalPoint.lean`) evaluates the
exponent to `p·k`, so the value is `padicExp(p k · ℓ) = (oneUnitPart a)^k = a^k`
(`intHom_oneUnitPart_eq_padicExp`, `TargetPoint.lean:359`; `teichRes` of `a ≡ 1 (mod p)` is `1`,
`teichmuller_eq_one_of_norm_sub_one_le`) — times `a⁻¹^k` gives `1`.
**Attacks**: (1) the exact statement of `specialize_univChar_eq_padicExp`'s right-hand side must be
read at ticket time (its second factor); the sketch names the two lemmas that evaluate it.
(2) `‖a − 1‖ ≤ p⁻²` also forces `toZMod a = 1` so `ω(…) = 1` — needed if the lemma's RHS keeps
the `ω` factor; `toZMod_eq_one_of_norm_sub_one_le`-style fact: `PadicInt.norm_le_pow_iff_mem_span_pow`
+ `ZMod` reduction.

**N-e** `oneAddPow_sub_one_intHom`, `nebChar_oneAddPMul`, `norm_logQuot_oneAddPMul_one`,
`isPrimitiveRoot_nebChar_oneAddPMul_one`, `nebChar_oneAddPMul_natCast` (conductor exactly `p²`).
**Source**: `lwx.txt:2028–2030` ("classical weights χ_k = (k,ψ) of conductor q²"); `lwx.txt:430–433`
(`T_χ = χ(exp(q)) − 1`, so `χ(exp(p)) = 1 + T`; at `T = ζ·exp(pk) − 1` the finite-order part is `ζ`).
**Match**: `nebChar (1 + px) = specialize(univChar ω (1+px)) · (1+px)^{−k}`; `specialize_univChar`
(`Specialize.lean:217`): `= ψ(ω(toZMod)) · oneAddPow T₀ (ψ (logQuot a))`; `toZMod (1+px) = 1`;
`oneAddPow_weightPoint_mul_padicExp` at `(s,t) = (0,k)` (`TargetPoint.lean:387`) splits
`oneAddPow (classicalPoint) ℓ = oneAddPow (ζ−1) ℓ · padicExp(p k ℓ)`; `intHom_oneUnitPart_eq_padicExp`
turns `padicExp(p k ℓ)` into `(1+px)^k`; `oneAddPow_sub_one_intHom` evaluates `oneAddPow (ζ−1) ℓ =
ζ^{ℓ mod p}` (continuity in `ℓ` + `oneAddPow_natCast` + `hζ.pow_eq_one`).  The unit
`‖logQuot(1+p)‖ = 1` is `norm_padicLog_eq` (`PadicExpLog.lean:753`: `‖log u‖ = ‖u−1‖` when
`‖u−1‖² < ‖p‖`) divided by `p`.  Primitive root: `ζ^{u}` with `u = toZMod ℓ ≠ 0` is primitive
(`IsPrimitiveRoot.pow_of_coprime`).
**Attacks**: (1) `weightPoint p 0 ζ = ζ − 1`? `weightPoint p s ζ = ζ · padicExp(p·s) − 1`, at
`s = 0` is `ζ·1 − 1` — needs `padicExp 0 = 1` (`PadicExpLog.padicExp_zero`); and `weightPoint p k ζ
= classicalPoint p k ζ` for `k : ℕ` cast to `ℤ` (`TH_one_weightPoint`-family; check
`weightPoint_natCast` or prove inline).  (2) continuity of `ℓ ↦ oneAddPow (ζ−1) (intHom ψ ℓ)`:
`oneAddPow` is continuous in `u` on the closed unit disc for `‖T‖ < 1` — project lemma
`continuous_oneAddPow`-style exists in `PowSubOne.lean`/`Specialize.lean` (verify at ticket time;
fallback: `oneAddPow_add` multiplicativity + density of `ℕ` in `ℤ_p` via
`PadicInt.denseRange_natCast`).  Also the RHS `ζ^{(toZMod ℓ).val}` is locally constant in `ℓ`
(`toZMod` continuous to a discrete space).  (3) `nebChar_oneAddPMul_natCast`: from
`nebChar_oneAddPMul` at `x = n` and `x = 1` plus `logQuot` additivity mod `p`: `logQuot(1+pn) ≡
n · logQuot(1+p) (mod p)` — true since `log(1+pn) ≡ pn (mod p²)`; proof via
`nebChar_of_norm_sub_one_le_sq` applied to `(1+p)^n / (1+pn)` (which is `≡ 1 (mod p²)`) and
`nebChar_mul`.  This second route avoids `logQuot` arithmetic entirely and is the one ticketed.

**N-f** `sum_nebChar_oneAddPMul_mul_eq_zero`, `sum_inv_nebChar_oneAddPMul_mul_eq_zero`,
`sum_inv_nebCharK_eq_zero` (the character sums).
**Source**: `scratch`, `sum_diagUnit_eq_zero` (proved): "for χ … whose restriction to `1 +
p^(h+1)` is non-trivial … ∑_{c : ZMod p} χ(1 − b c p^(h+1)) = 0".
**Match**: `nebChar(1 + pbc) = nebChar(1+p)^{bc}` (N-e), `= (nebChar(1+p)^b)^c`; `nebChar(1+p)^b`
is a primitive `p`-th root for `p ∤ b` (`IsPrimitiveRoot.pow_of_coprime`), and
`IsPrimitiveRoot.geom_sum_eq_zero` gives `∑_{c<p} (ξ)^c = 0`.  Inverses: `nebChar⁻¹` of a
primitive root is primitive (`IsPrimitiveRoot.inv`).  The `nebCharK` spelling:
`nebCharK (ψ(1 + bcp)) = nebChar (oneAddPMul p (bc))` by `coe_oneAddPMul` and `intHom_apply`.
**Attacks**: (1) `geom_sum_eq_zero` needs `1 < p` — `hp.out.one_lt`.  (2) the sum index: `c ∈
range p` as a natural number cast to `ℤ_p` — `Nat.cast` commutes (`push_cast`).  (3) `b * c` vs
`b * c * p` orderings in the statement `ψ (1 + (b:ℚ_p) * c * p)` — matches `1 + p·(b c)` up to
`mul_comm`/`mul_assoc`; the ticket proves the bridge by `ring_nf`.

**N-g** `partnerChar`, `partnerChar_apply`, `oneAddPow_inv_sub_one_mul`, `nebChar_partnerChar`,
`classicalData_partnerChar_u` (AG-ω₀, second half).
**Source**: `lwx.txt:2028–2036` (`ω' = ψ⁻¹|_Δ·ω₀^k = ω⁻¹ω₀^{2k}`).
**Match**: `nebChar ψ ω k ζ a = ω(ā)·ω₀(ā)^{−k}·ζ^{ℓ mod p}·(1+…)^k·a^{−k}`… precisely:
`nebChar a = ψ(ω(ā)) · oneAddPow(ζ−1)(ℓ) · padicExp(pkℓ) · a^{−k}`, and `a = teich(ā)·oneUnitPart a`
(`coe_eq_teichRes_mul_oneUnitPart`, `TargetPoint.lean:319`) with `padicExp(pkℓ) = oneUnitPart^k`,
so `nebChar a = ψ(ω(ā)) · ζ^{ℓ mod p} · teich(ā)^{−k}`.  Replacing `ω ↦ ω⁻¹·ω₀^{2k}`, `ζ ↦ ζ⁻¹`
gives `ψ(ω(ā))⁻¹ · teich(ā)^{2k} · ζ^{−ℓ} · teich(ā)^{−k} = (nebChar a)⁻¹`.
**Attacks**: (1) `teichChar` is `teichRes` (`TargetPoint.lean:51`); `teichRes (toZMod a) =
teichmuller a` (`teichRes_toZMod`).  (2) `IsPrimitiveRoot ζ⁻¹ p` is `hζ.inv` — used in the
statement.  (3) `classicalData_partnerChar_u`: unfold `classicalData.u` (`ClassicalPoint.lean:461`)
and apply `nebChar_partnerChar` at `a = (toLocalMat (discConj …)).d` via
`classicalData_u_eq_nebChar` (N-b) twice.  `oneAddPow_inv_sub_one_mul` is `oneAddPow_add`-type
multiplicativity in `T`: `oneAddPow (T) u · oneAddPow (T') u = oneAddPow ((1+T)(1+T') − 1) u`
— verify the project has `oneAddPow_mul_oneAddPow`-style lemma; fallback: continuity in `ℓ` and
`ℕ`-density as in N-e (both sides `ζ^{-n} ζ^{n} = 1` on `ℕ`).

### Part L — `PhD/LWX/AtkinLehnerLocal.lean`

**L-a** `vQ, sQ, wQ, wQinv, ℓQ`, determinants, `wQ_mul_wQinv`, `wQinv_mul_wQ`, `discConjMat_wQ`.
**Source**: `lwx.txt:684–688` (`v_j = (p 0; jq 1)`); `AtkinLehner.lean:62` (`atkinLehner p m =
(0 1; −p^m 0)`).  **Match**: `t₀ = (p 0; 0 1)`, `t₀⁻¹ wQ t₀ = (0 p·1/p ; −p·p 0)`… computed:
`(1/p 0; 0 1)(0 p; −p 0)(p 0; 0 1) = (0 1; −p 0)(p 0; 0 1) = (0 1; −p² 0)` ✓ `= atkinLehner p 2`.
**Attacks**: all are `Matrix.det_fin_two_of`/`Matrix.mul_fin_two`/`ext i j; fin_cases` with
`field_simp`; `ℓQ` determinant `(1−bcp)(1+bcp) + b²cp·cp = 1 − b²c²p² + b²c²p² = 1` ✓.

**L-b** `wQ_mul_vQ_mul_wQinv`, `upAdjRep_mul_vQ`, `wQ_mul_vQ_mul_wQinv_mul_vQ` (the key
factorisation).
**Source**: `scratch` `upRep_mul_upAdjRep` and `obstruction_mul_lowerUni` (proved), in the
original coordinate: `(1,b;0,p)(p,0;cp^m,1) = (p,b;0,p)(1,0;cp^m,1)` and `(p,b;0,p)(1,0;cp^{h+2},1)
= conjTwist b c h (p,b;0,p)`.  **Match** (disc coordinate, `h = 1`, after `wQ`-conjugation):
`wQ vQ b wQ⁻¹ = (0 p; −p 0)(p 0; bp 1)(0 −1/p; 1/p 0)`: first `(0 p;−p 0)(p 0; bp 1) = (bp² p;
−p² 0)`, then `·(0 −1/p; 1/p 0) = (p·1/p, −bp²/p; 0, p) = (1, −bp; 0, p)` ✓.  Then
`(1 −bp; 0 p)(p 0; cp 1) = (p − bcp², −bp; cp², p)` and `ℓQ b c · (p • sQ(−b)) = (1−bcp, −b²cp;
cp, 1+bcp)(p −bp; 0 p) = (p − bcp², −bp + b²cp² − b²cp²… )`: entry (0,1): `(1−bcp)(−bp) +
(−b²cp)(p) = −bp + b²cp² − b²cp² = −bp` ✓; (1,0): `cp·p = cp²` ✓; (1,1): `cp(−bp) + (1+bcp)p =
−bcp² + p + bcp² = p` ✓.
**Attacks**: (1) sign of `sQ(−b)`: checked above — `(p • sQ (−b)) = (p, −bp; 0, p)` ✓.
(2) `wQinv` vs `wQ⁻¹` as `Matrix` inverse: the file avoids `Matrix.inv` entirely (explicit
`wQinv`), `wQ_mul_wQinv` justifies; Part W uses `Units` inverses (`wGL⁻¹`) with `Units.ext`.

**L-c** memberships: `vQ_mem_M1`, `norm_vQ_zero_zero`, `sQ_mem_Iw`, `ℓQ_mem_Iw`, `Iw_one_le_M1`.
**Source**: `lwx.txt:606–610` (`M₁ = {(a b; c d) ∈ M₂(Z_p) | q | c, p ∤ d, ad − bc ≠ 0}`),
`lwx.txt:481–484` (`Iw_{p^m}`).  **Match**: `M1` (`IntegralModel.lean:226`): entries `≤ 1`,
`‖c‖ ≤ p⁻¹`, `‖d‖ = 1`, `det ≠ 0`; `Iw p 1` (`AtkinLehner.lean:140`): entries `≤ 1`, `‖c‖ ≤ p⁻¹`,
`‖det‖ = 1`.  `Iw_one_le_M1`: `‖d‖ = 1` from `det ≡ ad (mod p)` — `AtkinLehner.lean:171`
("On the Iwahori subgroup both diagonal entries are units") is the existing lemma.
**Attacks**: (1) `vQ c ∉ Iw` (det `p`) — correct, it's only in `M1`.  (2) `ℓQ b c ∈ Iw` needs
`‖b²cp‖ ≤ 1`, `‖1 ± bcp‖ ≤ 1`, `‖cp‖ ≤ p⁻¹`, `‖det‖ = ‖1‖ = 1` ✓.  (3) `norm_vQ_zero_zero`:
`‖p‖ = p⁻¹` (`Padic.norm_p`) — equality, so `≤` ✓.

**L-d** disc bookkeeping: `discImage_vQ_zero`, `discImage_ℓQ_zero`, `discConj_ℓQ_zero_one_one`,
`discImage_sQ_zero`, `discConj_sQ_zero`.
**Source**: `DiscModel.lean:168` (`discImage h δ a = toZModPow h (mobiusFun (toLocalMat δ) a)`),
`:172` (`discConjMat`), `:200` (`discConjMat_apply_one_one`).  **Match**: `mobiusFun δ 0 = b/d`;
for `vQ c`, `b = 0` so disc `0 ↦ 0`; for `ℓQ`, `b = −b²cp ∈ pℤ_p` so `toZModPow 1 = 0`; for
`sQ b`, `b/1 = b ↦ b mod p`.  `discConjMat h δ a` at `a = 0`, `a' = 0`: `= (a, b/p^h; c p^h, d)`
— for `ℓQ b c`: `d = 1 + bcp` ✓ (`discConjMat_apply_one_one` gives the `(1,1)` entry as
`δ 1 0 · a + δ 1 1` up to the `a'`-correction; at `a = a' = 0` it is `δ 1 1`).  For `sQ b`
(`b : ℕ`), `a' = b mod p`, `discConjMat = (1 − (b mod p)·0, (1·b + b − (b mod p)(0·b + 1))/p; 0, 1)`
`= (1, (b − (b mod p))/p; 0, 1)` — **not `1`** unless `b < p`!
**Attack outcome — statement repaired in the skeleton (planning phase, nothing ticketed yet, so
no B2)**: the first draft's `discConj_sQ_zero (b : ℕ)` was **false for `b ≥ p`** (the conjugate is
`(1, ⌊b/p⌋; 0, 1)`); its only consumer (`shapiro_blockProj`) uses `b = a.val < p`.  The skeleton
now reads `discConj_sQ_zero {b : ℕ} (hb : b < p)`.  `discImage_sQ_zero` is correct for every `b`.
The pass also added the general disc-`0` API the later parts need: `tMat`, `tMatInv`,
`discConjMat_eq_tMatInv_mul_mul_tMat` (the entry-wise definition of `discConjMat` **is**
`t_{a'}⁻¹ δ t_a` — checked entry by entry: `(a − a'c, (a·a_v + b − a'(c·a_v + d))/p; cp, c·a_v + d)`),
`discConjMat_zero_of_discImage_zero`, `discImage_zero_of_norm_apply_zero_one_le`, `ℓQinv` and
its lemmas, `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`, `tMatInv_zero_mul_sQ_mul_tMat_zero`.

### Part W — `PhD/LWX/AtkinLehnerMap.lean`

**W-a** `vGL, sGL, wGL, pGL, ℓGL`, `coe_*`, `wGL_mul_vGL_mul_wGL_inv_mul_vGL`,
`atkinLehnerK(inv)` and their products.
**Source**: L-b.  **Match**: `Units.ext` + `coe_*` + L-b; `(wGL)⁻¹` coerces to `wQinv` because
`wQ · wQinv = 1` (`Units.inv_eq_of_mul_eq_one_right`); `atkinLehnerK ψ = ψ.mapMatrix (0 1; −p² 0)`,
inverse `(0 −p⁻²; 1 0)`: `(0 1; −p² 0)(0 −p⁻²; 1 0) = (1, 0; 0, −p²·(−p⁻²)) = 1` ✓.
**Attacks**: (1) `pGL`'s det obligation: `det (p • 1) = p²` (`Matrix.det_smul`, `Fintype.card
(Fin 2) = 2`) `≠ 0`.  (2) `(ψ p)^2 ≠ 0` from `ψ` injective (field hom) and `p ≠ 0`.

**W-b** `AtkinLehnerData` (with the `w`-normalisation axiom `w_conj_mem_U` added by the
adversarial pass: without it `W` does not preserve the level — `(Wφ)(xu)` needs `w u' w⁻¹ ∈ U`
for `u'` fixing disc `0`, which for `U = K^p·Iw_p` is the local identity `w (a b; c d) w⁻¹ =
(d, −c; −b, a)` and is **not** derivable from the other fields in an abstract `G`).  **Source**: `lwx.txt:671–676` (D ⊗ Q_p ≅ M₂(Q_p) — the section
`ιp`), `lwx.txt:1783–1785` (the central Hecke character), `bu04.txt:633` (`η_p ∈ M_α`).
**Attacks on the structure (design, not a theorem)**: (1) is `χ_U : χ u = nebK(ψ(det θ u))`
consistent with `χ_vGL : χ(ιp v_c) = 1` when `v_c ∈ U`?  `v_c ∉ U` since `θ(v_c) = vQ c ∉ Iw`
(det `p`); consistent.  (2) is `χ_wGL` consistent with `χ_U` on `Iw`? `w ∉ Iw`; consistent.
(3) is `central` satisfiable with `χ`? `χ(ιp(p·1)) = χ(γ)χ(u) = nebK(ψ(det θ u)) = nebK(1) = 1`
requires `χ(ιp(p·1)) = 1`: from `χ_vGL`? `p·1 = v_0 · (1 0; 0 p)`, no; from `χ` being a
character of `ψ_A∘ν` trivial on `ℚ^×`: `χ(p_p) = ψ_A(ν(p_p)) = ψ_A(p²) = ψ_p(p²)·∏_{l≠p}ψ_l(p²)
= 1·1` — fine for the genuine `Dfx` instance; **inside the abstract structure it is a
consequence of `central` + `χ_Γ` + `χ_U` + `hcond`** (`θ u = 1 ⇒ det = 1 ⇒ nebK 1 = 1`), so no
extra axiom.  (4) `nebK` is a bare function; its properties are hypotheses of the theorems that
need them (`hmul hne hcond hsum`), discharged in Part N — deliberately not bundled, so `W` is
free of the classical-point specifics.

**W-c** `locPolyForms`, `ClassicalDiscForms`, `mem_classicalDiscForms_iff`,
`discHeckeOperator_mem_classicalDiscForms`, `discHeckeOperatorCl`.
**Source**: `lwx.txt:676–682` (`S^D_{k+2}(K^pIw_{p^m};ψ)`: values in `Ind^{m,alg}`) and
`lwx.txt:694–696` ("U_p … preserves the subspace S^D_{k+2}(K^pIw_{p^m};ψ) if χ is a classical
character").  **Match**: `DiscForms ⊓ locPolyForms`; `U_p` preserves the classical subspace by
`discSlash_mem_locPolyDegSubmodule_of_shape` (`Touching.lean:244`) at each certificate,
through the naive Hecke formula (I4) or directly through `heckeOperatorSlash_apply_rep` with the
trivial factorisation and the closure of `locPolyDegSubmodule` under finite sums.
**Attacks**: (1) `discHeckeOperator_mem_classicalDiscForms` is stated for *any* `η ∈ levelM1`
with finite double coset — the abstract Hecke operator's values are sums of `discSlash (θ(u v))`
over representatives, and each `discSlash` at a classical-shape weight preserves
`locPolyDegSubmodule` (hypothesis `hκ` at *every* `g ∈ M1Kh`, which is what
`autFactor_haloWeightH_classicalPoint_eq_nebCharK` supplies) ✓.  (2) `map_add'/map_smul'` of
`discHeckeOperatorCl`: `Subtype.ext` + `map_add` of `discHeckeOperator` ✓.

**W-d** `shapiro_blockProj`.  **Source**: `lwx.txt:841–846` (the explicit presentation reads a
form through its values; on the `p` discs, `s_a ∈ Iw_p` permutes the discs) and L-d.
**Match**: `φ(x s_a) = φ(x) ∣ sQ a` (`mem_discForms_iff`, `ιp_mem_U`, `theta_ιp`), and
`blockProj_discSlash` (`DiscModel.lean:482`): `blockProj 0 (discSlash δ f) = kappaSlash
(discConjK δ 0) (blockProj (discImage δ 0) f)`; with `discImage (sQ a) 0 = a`
(`discImage_sQ_zero`) and `discConj (sQ a) 0 = 1` (L22′, `a.val < p`), `kappaSlash 1 = id`
(`discSlash_one`/`kappaSlash_one`).
**Attacks**: (1) `a.val : ℕ` cast to `ℚ_p` — `discImage_sQ_zero` is stated for `b : ℕ` with
`(b : ZMod (p^1))`; `ZMod.natCast_zmod_val` closes `((a.val : ℕ) : ZMod (p^1)) = a` ✓.
(2) direction: `blockProj a (φ x) = blockProj 0 (φ (x s_a))` — with `φ(x s_a) = discSlash (sQ a)
(φ x)` and `blockProj 0 (discSlash (sQ a) f) = blockProj (discImage (sQ a) 0) f = blockProj a f` ✓.

**W-e** `atkinLehnerFun` and its `blockProj` lemmas, `_left_invt`, `_mem_locPolyDegSubmodule`.
**Source**: Step D.  **Match**: `cSpace.blockProj_blockIncl` (`BlockOp.lean:611`) collapses the
sum; `blockProj_zero` is the `a = 0` case with `sGL 0 = 1` (`sQ 0 = 1`, `map_one`, `mul_one`).
Left invariance: `χ(γ x s_a) = χ(γ)χ(x s_a) = χ(x s_a)` (`χ_Γ`) and `φ(γ …) = φ(…)`
(`AutomorphicFunction.left_invt`).  Locally polynomial: each block is `symAct k w₂ (…)` which
lies in `polySubmodule K k` (`symAct_mem_polySubmodule`); membership in `locPolyDegSubmodule`
is blockwise (`Theta.lean:140`, `IsLocPolyDeg`).
**Attacks**: (1) `sGL p ((0 : ZMod (p^1)).val)`: `ZMod.val_zero`, `Nat.cast_zero`, `sQ 0 = !![1,0;0,1]
= 1` — `Matrix.one_fin_two` ✓.  (2) `(D.χ x : Kˣ) : K` inverse vs `Units.inv`: use `Units.val_inv_eq_inv_val` ✓.

**W-f** `atkinLehnerFun_slash` (the equivariance, `ψ ↦ ψ⁻¹`).
**Source**: `lwx.txt:1783–1785` (twist), `AtkinLehner.lean:109` (`atkinLehnerConj_apply_one_one:
(w⁻¹γw) 1 1 = γ 0 0`), `AtkinLehner.lean:113` ("`a d = det γ + b c`, so modulo `p^m` …").
**Match**: Let `u ∈ U`, `a` a disc, `s := s_a`.  Write `u s_a = s_{a'} u'` with `a' = discImage (θu)
a`… precisely `θ(u) s_a = s_{a'} · (t_{a'}⁻¹ θ(u) t_a)`-type identity: the disc conjugate
`discConjMat 1 (θu) a = t_{a'}⁻¹ θ(u) t_a` with `t_a = (p a; 0 1) = sQ a · (p 0; 0 1)`, so
`s_{a'}⁻¹ θ(u) s_a = t₀ · discConjMat · t₀⁻¹ =: u'` which is in `Iw_p` and fixes disc `0`,
with `d(u') = d(discConj) = discConj 1 1`.  Then `(Wφ)(xu)|_a = χ(xu s_a)⁻¹ symAct w₂
(φ(x u s_a w⁻¹)|_0) = χ(x s_{a'} u')⁻¹ symAct w₂ (φ(x s_{a'} · u' w⁻¹)|_0)`; `u' w⁻¹ = w⁻¹ (w u' w⁻¹)`
and `w u' w⁻¹ ∈ Iw_p` fixes disc `0` with `d(wu'w⁻¹) = a(u')`; level-equivariance on disc `0`
(`blockProj_zero_apply_mul_mem_U`, now in Part W where W-f can use it; the `ιp`-form
`blockProj_zero_apply_mul_ιp` in Part I is its corollary) gives
`φ(x s_{a'} w⁻¹ (wu'w⁻¹))|_0 = nebK(a(u')) · symAct (wu'w⁻¹) (φ(x s_{a'} w⁻¹)|_0)`; then
`symAct w₂ ∘ symAct (wu'w⁻¹)` … `= symAct (wu'w⁻¹ · w₂)`, and `w u' w⁻¹ · w₂`
vs `w₂ · u'`: `w₂ u' = (w u' w⁻¹) w₂` in the disc-`0` coordinate ✓ (`w₂ = t₀⁻¹ w t₀`, and
`u' = t₀ (discConj) t₀⁻¹`… the coordinates must be tracked carefully — the ticket sketch does
it in the `K`-matrices via `symAct_mul`).  Finally `χ(x s_{a'} u') = χ(x s_{a'}) nebK(det θu')`
and `nebK(det) = nebK(a(u')) nebK(d(u'))` (from `ad = det + bc`, `p ∣ c`, `p ∣ b`?? — **no**: for
`u'` fixing disc `0` we only know `p ∣ b(u')` *in the disc coordinate*, i.e. `b(discConj) ∈ ℤ_p`
and `c(discConj) ∈ p²ℤ_p`… ) — **this is where `hcond` (conductor `∣ p²`) enters**: `ad − det
= bc` and in the disc-`0` conjugate of a level-`Iw_p` element the product `bc ∈ p²ℤ_p`?  With
`discConjMat = (a − a'c, (ab + … )/p; cp, d)`: `c(disc) = c(u)·p ∈ p²ℤ_p` and `b(disc) ∈ ℤ_p`, so
`b c ∈ p²ℤ_p` ✓ and `nebK(ad) = nebK(det + bc) = nebK(det)·nebK(1 + bc/det) = nebK(det)` by
`hcond` (`‖bc/det‖ ≤ p⁻²`) ✓ and `hmul`.  So `(Wφ)(xu)|_a = χ(x s_{a'})⁻¹ nebK(d(u'))⁻¹
symAct(w₂ u')(φ(x s_{a'} w⁻¹)|_0) = nebK(d(u'))⁻¹ · symAct u' ((Wφ)(x)|_{a'})` — and that is
`blockProj a (discSlash κ' (θu) (Wφ x))` by `blockProj_discSlash` with `hκ'` (`u ↦ nebK(d)⁻¹`),
`kappaSlash_eq_smul_symAct_of_shape`, since `discImage (θu) a = a'` and the disc conjugate is
`u'` (as a `K`-matrix) ✓.
**Attacks**: (1) the coordinate bookkeeping between `u' ∈ Iw_p ⊂ GL₂(ℚ_p)` (needed to move it
through `ιp` and `w`) and `discConj 1 (θu) a ∈ M1` (what `blockProj_discSlash` produces): they
are related by `u' = t₀ · discConj · t₀⁻¹`?? — **checked**: `discConjMat h δ a = t_{a'}⁻¹ δ t_a`
with `t_a = (p^h a; 0 1)`; and `s_a = t_a t₀⁻¹` (`(p a;0 1)(1/p 0; 0 1) = (1 a; 0 1)` ✓).  So
`s_{a'}⁻¹ δ s_a = t₀ t_{a'}⁻¹ δ t_a t₀⁻¹ = t₀ · discConjMat · t₀⁻¹`.  For the *level* action on
disc `0` we need the disc-`0` conjugate of `s_{a'}⁻¹ δ s_a`, which is `t₀⁻¹ (s_{a'}⁻¹ δ s_a) t₀ =
discConjMat h δ a` ✓ — the two coordinates are consistent, and the ticket works with
`g := s_{a'}⁻¹ δ s_a ∈ Iw_p` whose disc-`0` conjugate is `discConj 1 δ a`.  This is the
content of a helper `discConj_eq_discConj_conj` (sub-ticket W17a, listed).  (2) `w₂ u'` vs
`(wu'w⁻¹) w₂` as `K`-matrices: `atkinLehnerK ψ · ψ(discConj) = ψ(atkinLehnerConj-ish) ·
atkinLehnerK ψ` — a 2×2 identity in `K` (helper W17b).  (3) the `d`-entry of `w u' w⁻¹` (in
`GL₂(ℚ_p)`, disc-`0` coordinate `w₂ g w₂⁻¹` with `w₂ = (0 1; −p² 0)`): `atkinLehnerConj p 2 g` has
`(1,1)`-entry `g 0 0` ✓ (`atkinLehnerConj_apply_one_one`).

**W-g** `atkinLehnerMap`, `atkinLehnerFunInv(_blockProj_zero)`, `atkinLehnerMapInv`,
`atkinLehnerMapInv_atkinLehnerMap`, `atkinLehnerMap_atkinLehnerMapInv`, `atkinLehnerEquiv`.
**Source**: `w² = −p²·1` central; `lwx.txt:520–537` for the flavour (the anti-involution) — but
we use `W' := ` mirror with `w`, not `W` twice.  **Match**: `(W'Wφ)(x)|_0 = χ(x) symAct w₂⁻¹
((Wφ)(xw)|_0) = χ(x) symAct w₂⁻¹ (χ(xw)⁻¹ symAct w₂ (φ(xww⁻¹)|_0)) = χ(x)χ(xw)⁻¹ · φ(x)|_0`
and `χ(xw) = χ(x)χ(w) = χ(x)` (`χ_wGL`); `symAct w₂⁻¹ ∘ symAct w₂ = symAct (w₂ w₂⁻¹) = symAct 1 = id`
on polynomials (`symAct_mul`, `atkinLehnerK_mul_atkinLehnerKinv`, `symAct_one`).  On disc `a`:
`shapiro_blockProj` both sides.  `W ∘ W'` symmetric.  The equivariance of `W'` (needed for
`atkinLehnerMapInv`'s first `sorry`) is W-f with `(κ, κ')` swapped and `w ↦ w⁻¹`: a separate
ticket (W19) with the same proof shape, or derived from `W' = W^{-1}` … no — `W'` must be shown
to land in `ClassicalDiscForms κ` *before* it is a map; ticket W19 proves `atkinLehnerFunInv_slash`
directly (mirror of W17; the helper lemmas are shared).
**Attacks**: (1) `W'` uses `symAct (atkinLehnerKinv ψ)` and `φ(x s_a w)`: `(W'φ)(xu)` mirror
needs the `d`-entry of `w⁻¹ u' w`, which is again `a(u')` (`w⁻¹ = −p⁻² w`, scalars don't change
conjugation) ✓.  (2) `LinearEquiv.ofLinear` argument order: `(f g) (h₁ : f ∘ g = id) (h₂ : g ∘ f
= id)`; the skeleton compiles, so it's right.

**W-h** `discEvalAtReps_mem_locPolyDegSubmoduleBlock`, `discEvalAtRepsCl`, `discEvalAtRepsCl_apply`.
**Source**: `lwx.txt:841–866` ((2.11.1) `φ ↦ (φ(γ_i))_i`), neatness `lwx.txt:676–680`.
**Match**: `discEvalAtReps_apply` (`DiscForms.lean:111`): `(E φ)(i, x) = φ(c i) x`, so `E φ ∈
locPolyDegSubmoduleBlock` iff each `φ(c i) ∈ locPolyDegSubmodule` ✓.  `discEvalAtRepsCl`:
`LinearEquiv.ofBijective` of the restriction/corestriction of `discEvalAtReps` — injective
(from `bijective_discEvalAtReps_of_stabilizer_eq_bot`), surjective: given `f ∈ Block`, the
preimage `φ` under `discEvalAtReps` is a disc form with `φ(c i) = f|_i ∈ locPolyDegSubmodule`;
**is `φ` classical at every `x`?**  `x = γ c_i u` (bijectivity of the double-coset map) so
`φ(x) = φ(c_i) ∣ θ(u)`, and `discSlash_mem_locPolyDegSubmodule_of_shape` with `hκ` ✓ — this is
why `discEvalAtRepsCl` carries `hκ`.
**Attacks**: (1) `DoubleCoset.Quotient` bijectivity gives *some* `γ, u` with `x = γ c_i u` —
`DoubleCoset.mk_eq`-style API (`Doset.mk_eq_of_doset_eq` / `Doset.rel_iff`); verified to exist
in mathlib as `Doset.rel_iff` (`x ≈ y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b`) — name to re-verify
at ticket time (`DoubleCoset.rel_iff` vs `Doset.rel_iff` after the bump).  (2) `discEvalAtRepsCl`
is a `def … := by sorry` producing a `LinearEquiv`; the ticket replaces the `by sorry` with a
term (`LinearEquiv.ofBijective (LinearMap.codRestrict …) ⟨inj, surj⟩`), and
`discEvalAtRepsCl_apply` is then `rfl`-ish (`LinearEquiv.ofBijective_apply`).

### Part I — `PhD/LWX/AtkinLehnerIdentity.lean`

**I-a** `vRepD`, `vRepD_mem_levelM1`, `upEltD`, `upEltD_mem_levelM1`.
**Source**: `lwx.txt:684–688`.  **Match**: `θ(ιp v) = vQ c ∈ M1` (`theta_ιp`, `vQ_mem_M1`).
**Attacks**: `levelM1 = Submonoid.comap θ (M1 p)` (`IntegralModel.lean:1356`) ✓; `(c : Fin p) → ℕ → ℚ_p`
norm `≤ 1` by `IsUltrametricDist.norm_natCast_le_one` ✓.

**I-b** `discHeckeOperator_apply_eq_sum` (the naive Hecke formula).
**Source**: `bu04.txt:645–649`: "write UηU = ∐_i Uη_i (a finite union) and define the Hecke
operator [UηU] : L(U,A) → L(U,A) by [UηU]f = ∑_i f|η_i"; `bu04.txt:633`: "(f|η)(g) = f(gη⁻¹)η_p";
`lwx.txt:690–692` ((2.5.1): `U_p(ϕ) := ∑_{j} ϕ|_χ v_j, (ϕ|_χ v_j)(g) := ϕ(g v_j⁻¹)||_χ v_j`).
**Match**: `heckeOperatorSlash_apply_rep` (`HeckeMatrix.lean:57`) with `c := x`, `c' t := x
(v_t)⁻¹`, `d t := 1`, `u t := 1`, `hfact : x v_t⁻¹ = 1 · (x v_t⁻¹) · 1` gives `(U_p φ)(x) = ∑_t
φ(x v_t⁻¹) ∣ₛ ⟨1 · v_t, _⟩`, and `∣ₛ` under `discLevelSlashAction` (`DiscForms.lean:53`,
`RightSlashAction.comap (levelM1ToM1 θ) (discSlashAction …)`) is `discSlash 1 ψ κ ⟨θ(1·v_t), _⟩`;
`one_mul` and `Subtype.ext` finish.
**Attacks**: (1) the `hv`/`hvinj` hypotheses are exactly `heckeOperatorSlash_apply_rep`'s
(`Set.BijOn (Quotient.mk'') (range vRep) (image of {η}·U)`) ✓ — the statement was copied from
`discEvalAtReps_discHeckeOperator`.  (2) is `x v_t⁻¹` with `v_t = ιp(vQ t)` the right side? Our
slash is the *right* slash `(φ ∣ δ)(g) = φ(g δ⁻¹) ∣ δ` (`AutomorphicFunction.slash_apply`,
`Slash/AutomorphicFunction.lean:56`) ✓ matching Buzzard's `f(gη⁻¹)η_p`.

**I-c** `blockProj_zero_discSlash_of_shape`.  **Source**: S-e + `blockProj_discSlash`.
**Match**: `blockProj 0 (discSlash δ f) = kappaSlash (discConjK δ 0) (blockProj (discImage δ 0) f)`
`= kappaSlash (discConjK δ 0) (blockProj 0 f)` (by `hδ`) `= u(d) • symAct (ψ(discConj δ 0))
(blockProj 0 f)` (S-e with `hκ` at `g = discConjK δ 0 ψ`, `f = blockProj 0 f ∈ polySubmodule`
since `f ∈ locPolyDegSubmodule` blockwise).
**Attacks**: `coe_discConjK` (`DiscModel.lean:333`) is `rfl` for `(discConjK … ψ : Matrix) =
ψ.mapMatrix (discConj …).1` ✓; `discConjK _ _ _ ψ` has `g.1 1 1 = ψ ((discConj …) 1 1)`
(`RingHom.mapMatrix_apply`, `Matrix.map_apply`) ✓.

**I-d** `apply_mul_ιp_pGL`, `apply_mul_ιp_pGL_inv`.  **Source**: design decision (plan.md, "Where
the central element comes from"); `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p` with `η_p = 1` acting
trivially).  **Match**: `ιp(p·1) = γ u`, `φ(x γ u) = φ(γ x u)` (`γ` central) `= φ(x u)` (left
invariance) `= φ(x) ∣ θ(u) = φ(x) ∣ 1 = φ(x)` (`mem_discForms_iff`, `θ u = 1`, `discSlash_one`).
**Attacks**: (1) `discSlash 1 ψ κ ⟨1, _⟩ = id`: `discSlash_one` exists (`DiscModel.lean:537` uses it) ✓
— but the element is `⟨θ u, hU u.2⟩` with `θ u = 1`; a `Subtype.ext`/`congrArg` step to rewrite
to `⟨1, one_mem⟩` — or `discSlash` is defined via `blockOp` and `kappaSlash (discConjK 1 a)`;
easiest: `have : (⟨θG u, hU u.2⟩ : M1 p) = 1 := Subtype.ext hθu` then `rw [this, discSlash_one]`.
(2) inverse version: `x = (x p⁻¹) p` and the first version at `x p⁻¹` ✓.

**I-e** `blockProj_zero_apply_mul_ιp`.  **Source**: `lwx.txt:676–680` (`ϕ(xu_p) = ϕ(x)||_χ u_p`).
**Match**: `φ(x ιp g) = φ(x) ∣ θ(ιp g) = discSlash ⟨g, _⟩ (φ x)` (`ιp_mem_U`, `theta_ιp`,
`mem_discForms_iff`), then I-c at `f = φ x` ✓.
**Attacks**: `Iw_one_le_M1 hg` gives the `M1`-membership of `g`, and `hU (ιp_mem_U g hg)`
gives the `levelM1` one — they must be defeq-compatible (`⟨θ(ιp g), hU _⟩ = ⟨g, Iw_one_le_M1 hg⟩`
by `Subtype.ext (theta_ιp g)`) ✓.

**I-f** `atkinLehner_term_eq` (the `(b,c)`-term).  **Source**: Step E; `scratch`
`obstruction_mul_lowerUni` + `obstruction_zero` ("The `b = 0` term is central … where `p · p^k =
p^{k+1}` comes from").  **Match** (all on disc `0`): the LHS is `symAct (ψ(discConj (vQ c) 0))
( χ(x v_c⁻¹) · symAct w₂⁻¹ ( (Wφ)(x v_c⁻¹ w v_b⁻¹)|_0 ) )`.  Unfold `(Wφ)(y)|_0 = χ(y)⁻¹ symAct w₂
(φ(y w⁻¹)|_0)` at `y = x v_c⁻¹ w v_b⁻¹`: `y w⁻¹ = x v_c⁻¹ w v_b⁻¹ w⁻¹ = x · (w v_b w⁻¹ v_c)⁻¹ =
x · (ℓ_{b,c} · p · s_{−b})⁻¹ = x s_{−b}⁻¹ p⁻¹ ℓ⁻¹ = x s_b p⁻¹ ℓ⁻¹` (`wGL_mul_vGL_mul_wGL_inv_mul_vGL`,
`mul_inv_rev`, `sGL (−b)⁻¹ = sGL b`).  `φ(x s_b p⁻¹ ℓ⁻¹)`: `p⁻¹` acts trivially (I-d, `x s_b`
then `ℓ⁻¹` — order: `φ((x s_b) · p⁻¹ · ℓ⁻¹)`; `p⁻¹` central in `G`? `ιp(p·1)⁻¹ = u⁻¹γ⁻¹` and `γ`
central: `φ(z u⁻¹ γ⁻¹ ℓ⁻¹) = φ(γ⁻¹ z u⁻¹ ℓ⁻¹) = φ(z u⁻¹ ℓ⁻¹) = φ(z ℓ⁻¹ · (ℓ u⁻¹ ℓ⁻¹))` — hmm,
`u⁻¹` and `ℓ⁻¹` don't commute in `G`; but `u ∈ U` with `θ u = 1`, and `ℓ u⁻¹ ℓ⁻¹ ∈ U` with
`θ(ℓ u⁻¹ ℓ⁻¹) = ℓ · 1 · ℓ⁻¹ = 1` — so `φ(z ℓ⁻¹ · (ℓ u⁻¹ ℓ⁻¹)) = φ(z ℓ⁻¹) ∣ 1 = φ(z ℓ⁻¹)` ✓; the
ticket proves a general helper **`apply_mul_of_theta_eq_one` (`u ∈ U`, `θ u = 1` ⇒ `φ(x u) =
φ x`)** and uses `central` as `ιp(p)⁻¹ = u⁻¹ γ⁻¹` — sub-ticket I7a).  Then `φ(x s_b ℓ⁻¹)|_0 =
nebK(d(ℓ⁻¹ conj))·symAct(ℓ⁻¹ conj)(φ(x s_b)|_0)` (I-e at `g = ℓ⁻¹`, which is in `Iw_p` and
fixes disc `0`; `d(disc-conj of ℓ⁻¹) = (1+bcp)⁻¹`… **careful**: `ℓ⁻¹ = (1+bcp, b²cp; −cp, 1−bcp)`
(det 1), whose disc-`0` conjugate has `d = 1 − bcp`, and `nebK(1 − bcp) = nebK(1+bcp)⁻¹` by
`hmul`+`hcond` (`(1−bcp)(1+bcp) = 1 − b²c²p² ≡ 1 (mod p²)`) — the statement's
`nebK(ψ(1 + bcp))⁻¹` is therefore correct but the proof goes through `1 − bcp`; sub-ticket I7b:
`nebK (1 − bcp) = (nebK (1 + bcp))⁻¹`).  Then `φ(x s_b)|_0 = φ(x)|_b` (`shapiro_blockProj`,
reversed).  Collect the `symAct`s: `symAct(ψ(discConj (vQ c) 0)) ∘ symAct w₂⁻¹ ∘ symAct w₂ ∘
symAct(disc-conj of ℓ⁻¹)` … `= symAct( (disc-conj ℓ⁻¹) · w₂ · w₂⁻¹ · (disc-conj vQ c) )` by
`symAct_mul` (right action: `symAct γ' (symAct γ f) = symAct (γ γ') f`, so the *outermost* map
is the *rightmost* factor).  The resulting matrix is `(disc-conj ℓ⁻¹) · (disc-conj vQ c)` whose
product in `GL₂` is the disc-`0` conjugate of `ℓ⁻¹ vQ c` … and `ℓ⁻¹ v_c = p · s_{−b} · (w v_b w⁻¹)⁻¹`?
From the factorisation `w v_b w⁻¹ v_c = ℓ p s_{−b}`: `ℓ⁻¹ · (w v_b w⁻¹) · v_c = p s_{−b}`, not
`ℓ⁻¹ v_c`.  **Re-derivation of the target**: the composite matrix acting on `φ(x)|_b` should be
the disc-`0`-coordinate of `s_b · (p s_{−b})⁻¹ … ` — the statement says `p^k • symAct(1, −b/p;
0, 1)`.  Check with scalars: the total group element between `x s_b` and the evaluation is
`(x s_b)(p⁻¹ ℓ⁻¹) …`; we evaluated `φ(x s_b p⁻¹ ℓ⁻¹)` and then applied `symAct w₂ ∘ symAct w₂⁻¹ ∘
symAct(disc-conj vQ c)`?? — no: `symAct w₂` came from `W` and is applied to `φ(y w⁻¹)|_0`, and
`symAct w₂⁻¹` from `W'`… wait, the LHS has `symAct(disc-conj vQ c) ( χ · symAct w₂⁻¹ (Wφ(…)|_0))`
and `Wφ(…)|_0 = χ⁻¹ symAct w₂ (φ(…)|_0)`, so the `symAct`s compose to `symAct(w₂ · w₂⁻¹ ·
disc-conj vQ c) = symAct(disc-conj vQ c)` applied to `φ(x s_b p⁻¹ ℓ⁻¹)|_0 = nebK(1−bcp)·
symAct(conj ℓ⁻¹)(φ(x)|_b)`, total `symAct(conj(ℓ⁻¹) · conj(vQ c)) = symAct(conj(ℓ⁻¹ vQ c))` (disc
conjugation at disc `0` is multiplicative for elements fixing disc `0`: `discConj_mul`-type lemma,
sub-ticket I9a — the disc model's `discSlash_mul` gives it at the level of slashes).  And
`ℓ⁻¹ vQ c`: from `wv_bw⁻¹ v_c = ℓ p s_{−b}` we get `v_c = (w v_b w⁻¹)⁻¹ ℓ p s_{−b}`, so `ℓ⁻¹ v_c ≠`
anything nice.  **So the expansion order in the statement must be re-examined**: the `(b,c)`
term has `x v_c⁻¹ w v_b⁻¹ w⁻¹ = x (w v_b w⁻¹ v_c)⁻¹ = x s_{−b}⁻¹ p⁻¹ ℓ⁻¹ = x s_b p⁻¹ ℓ⁻¹` ✓ (as
computed).  The *slashes* accumulated on the *right* are: from the outer `U_p` (`∣ v_c`, giving
`symAct(conj vQ c)` on disc 0 — **but `blockProj 0 (discSlash (vQ c) f) = kappaSlash (conj) (blockProj
(discImage (vQ c) 0) f) = … (blockProj 0 f)` ✓ since `vQ c` fixes disc `0`**), from `W'` (`symAct w₂⁻¹`),
from the inner `U_p^{ψ⁻¹}` (`∣ v_b`: `blockProj 0 (discSlash (vQ b) g) = kappaSlash(conj vQ b)(blockProj 0 g)`
— **the statement's LHS omits this factor!**).  Re-reading the skeleton's LHS: `symAct(conj vQ c)
( χ(x v_c⁻¹) • symAct w₂⁻¹ ( blockProj 0 ( (Wφ)(x v_c⁻¹ w v_b⁻¹) ) ) )` — the inner `U_p^{ψ⁻¹}`
contributes `discSlash (vQ b)` applied to `(Wφ)(z v_b⁻¹)` with `z = x v_c⁻¹ w`, and on disc `0`
that is `(nebK(1))⁻¹ · symAct(conj vQ b)(blockProj 0 ((Wφ)(z v_b⁻¹)))` — so **the term as stated
in the skeleton is missing the `symAct (conj (vQ b))` factor**, unless it is meant as the term
*before* applying that slash.  The `U_p^{ψ⁻¹}`-slash at `v_b` is applied to the whole sum over
`b`… no: `(U'ψ)(z) = ∑_b ψ(z v_b⁻¹) ∣ v_b`, each summand carries its own `∣ v_b`.  Then `W'` acts
on the sum, and the outer `U_p` on that.  On disc `0`: `(U_p W' U' W φ)(x)|_0 = ∑_c nebK(1)·
symAct(conj v_c)( (W' U' W φ)(x v_c⁻¹)|_0 )`, `(W' g)(y)|_0 = χ(y) symAct w₂⁻¹ (g(y w)|_0)`, so
`= ∑_c symAct(conj v_c)( χ(x v_c⁻¹) symAct w₂⁻¹ ( (U'Wφ)(x v_c⁻¹ w)|_0 ) )` and `(U'Wφ)(z)|_0 =
∑_b symAct(conj v_b)( (Wφ)(z v_b⁻¹)|_0 )` (with `nebK(1)⁻¹ = 1`).  **Therefore the correct
`(b,c)`-term is `symAct(conj v_c)( χ(x v_c⁻¹) symAct w₂⁻¹ ( symAct(conj v_b) ( (Wφ)(x v_c⁻¹ w v_b⁻¹)|_0 ) ) )`**,
and the skeleton's `atkinLehner_term_eq` LHS lacks the inner `symAct (conj v_b)`.
**Attack outcome — statement repaired in the skeleton (planning phase; no B2)**: the first
draft's `atkinLehner_term_eq` LHS lacked the inner `symAct (conj v_b)`; the skeleton now has it.
The RHS is re-derived with the factor restored: the accumulated matrix is
`conj(ℓ⁻¹)·w₂·conj(v_b)·w₂⁻¹·conj(v_c)` — with `conj(δ) = t₀⁻¹ δ t₀` for every factor
(`discConjMat_zero_of_discImage_zero`, `atkinLehnerK_eq`, `atkinLehnerKinv_eq`) this is
`t₀⁻¹ (ℓ⁻¹ · w v_b w⁻¹ · v_c) t₀ = t₀⁻¹ (p s_{−b}) t₀ = p • (1, −b/p; 0, 1)`
(`ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`, `tMatInv_zero_mul_sQ_mul_tMat_zero`), and
`symAct (p • m) = p^k • symAct m` (`symAct_smul_one`, `symAct_mul`) — **confirming the skeleton's
RHS `p^k • symAct (1, −b/p; 0, 1) (φ(x)|_b)`; only the LHS was missing a factor.**  The scalar is
`nebK(1 − bcp) = nebK(1+bcp)⁻¹` (`nebK_one_sub_eq_inv`; the disc-`0` conjugate of `ℓ⁻¹` has
`d = 1 − bcp`, `discConj_ℓQinv_zero_one_one`) and the `χ`'s cancel:
`χ(x v_c⁻¹) · χ(x v_c⁻¹ w v_b⁻¹)⁻¹ = χ(w)⁻¹ χ(v_b) = 1` (`χ_wGL`, `χ_vGL`).  The `b`-dependence of
the RHS through `(1, −b/p; 0, 1)` is harmless: the `c`-sum is taken at fixed `b`, and only the
scalar `nebK(1+bcp)⁻¹` depends on `c`.  Two further repairs from the same pass, both recorded in
the skeleton: (i) **the central element in the middle of a word** — `φ(x s_b P⁻¹ ℓ⁻¹)` needs
`P⁻¹ = u⁻¹γ⁻¹` moved out: `γ⁻¹` to the far left by centrality and `u⁻¹` to the far right as
`ℓ u⁻¹ ℓ⁻¹ ∈ U` with trivial `θ` (`apply_mul_of_theta_eq_one`) — ticketed as `term_elt_eq` +
`blockProj_zero_apply_term_elt`; (ii) **the abstract `nebK`-hypotheses are now on `ψ`-images of
`p`-adic units** (`hmul : ∀ x y : ℚ_p, ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x y)) = …`), because for a
general `K ⊋ ℚ_p` the function `nebCharK` is **not** multiplicative on all norm-one elements of
`K` (`haloCharFunH` vanishes off the `p⁻²`-neighbourhood of `ψ(ℤ_p^×)`, so `x = √u` for a
non-residue `u` has `nebCharK x = 0` but `nebCharK (x·x) ≠ 0`) — the first draft's
`hmul : ∀ x y : K, …` would have been **undischargeable** at the classical point.  Every use of
`hmul`/`hne`/`hcond` is at a `ψ`-image, so nothing else changes; Part N gains
`nebCharK_psi_mul`, `nebCharK_psi_ne_zero`, `nebCharK_psi_of_norm_sub_one_le_sq`.

**I-g** `blockProj_zero_discHecke_atkinLehner` (the identity on disc `0`).
**Source**: Step E; `scratch` "What remains, Step 2".  **Match**: expand with I-b three times
(outer `U_p` on `W'U'Wφ`, inner `U'` on `Wφ`), `blockProj_zero` lemmas for `W'` and `W`
(`atkinLehnerFunInv_blockProj_zero`, `atkinLehnerFun_blockProj_zero`), I-c for the two slashes
(`discImage_vQ_zero`), linearity of `symAct`/`blockProj` over finite sums, then I9′ termwise:
`∑_c ∑_b nebK(1+bcp)⁻¹ • p^k • symAct(m_b)(φ(x)|_b) = ∑_b (∑_c nebK(1+bcp)⁻¹) • p^k symAct(m_b)
(φ(x)|_b)`; `b = 0`: `nebK(1)⁻¹ = 1`, `∑_c 1 = p`, `m_0 = 1`, `symAct_one`, total `p · p^k = p^{k+1}`
(`ψ p` in `K`; `(p : K) = ψ p` by `map_natCast`); `b ≠ 0` (`¬ p ∣ b` for `0 < b < p`): `hsum` ✓.
**Attacks**: (1) `Finset.sum_comm` and `Finset.sum_eq_single 0`; `Fin p` vs `range p` indexing
in `hsum` — `Fin.sum_univ_eq_sum_range` ✓.  (2) `(nebK (ψ 1))⁻¹ = 1`: `hcond` at `x = 1` (`‖1 − 1‖
= 0 ≤ p⁻²`) ✓, `map_one`.  (3) `p • (…)` vs `(ψ p)^(k+1) • …`: `pow_succ`, `ψ (p : ℚ_p) = (p : K)`
(`map_natCast`), `Finset.sum_const`, `Finset.card_fin`/`card_range`, `nsmul_eq_mul` ✓.

**I-h** `discHeckeCl_comp_atkinLehner` (operators).  **Source**: Step E last line.
**Match**: `LinearMap.ext`, `Subtype.ext`, `AutomorphicFunction.ext`, then `cSpace` block-ext
(`sum_blockIncl_blockProj`-type: `f = ∑_a blockIncl a (blockProj a f)`, or `ext ⟨a, j⟩` with
`blockProj_apply`), and for disc `a` apply `shapiro_blockProj` on both sides to reduce to I-g at
`x s_a` — both `U_p W' U' W φ` and `φ` are disc forms so `shapiro_blockProj` applies to each ✓.
**Attacks**: `shapiro_blockProj` needs `D` — available ✓; the composite is in
`ClassicalDiscForms κ` ✓ (it is the value of the composite linear map).

**I-i** `discEvalAtRepsCl_discHeckeOperatorCl`.  **Source**: `discEvalAtReps_discHeckeOperator`
(`DiscForms.lean:202`).  **Match**: `discEvalAtRepsCl_apply` twice + the existing transport ✓
(all hypotheses copied from it).

**I-j** `atkinLehnerHypothesis_of_conj`.  **Source**: linear algebra.  **Match**: `(SAS₁)(SBS₁) =
S(AB)S₁ = c·SS₁ = c·1` using `S₁S = 1 ⇒ SS₁ = 1` (`Matrix.mul_eq_one_comm`); `S'A'S₁' = (S'PS₁)(SBS₁)
(SQS₁')` with `Q'P' = SQ(S₁'S')PS₁ = S(QP)S₁ = 1`.  **Attacks**: `hS''` is slack (`_hx`); noted.

**I-k** `atkinLehnerHypothesis_of_atkinLehnerData` (H1).  **Source**: Step F.
**Match**: `A = (classicalData ψ ω …).matrix idx = upMatrix 1 k (discHeckeBlockOp κ_ω) _ =
LinearMap.toMatrix b b (restrict …)` (`AtkinLehnerInst.lean:204`, `Touching.lean:283,677`);
similarly `A'` at `κ' := (classicalData ψ (partnerChar) … ζ⁻¹ …).weight`.  `hκ`/`hκ'` for
`κ = weight` and `κ'` are `autFactor_haloWeightH_classicalPoint_eq_nebCharK` (N-b) and its
partner form via `nebChar_partnerChar`/`classicalData_partnerChar_u` (N-g) — **note `hκ'` needs
the shape at *every* `g ∈ M1Kh`, with constant `(nebCharK ψ ω k ζ (g 1 1))⁻¹`; N-g's
`nebChar_partnerChar` is stated on units `a : ℤ_[p]ˣ`, and `g 1 1 = ψ(d)` with `d` a unit for
`g ∈ M1Kh` — sub-ticket I14a: `nebCharK_partnerChar` on `x ∈ haloUnitsH`/`‖x‖ = 1` of the form
`intHom ψ a`.**  Then with `E := discEvalAtRepsCl` (both weights), `Wb := E_κ.symm ≫ W ≫ E_κ'`,
`B := toMatrix b b (restrict (T_{κ'}) conjugated by Wb)`, and `LinearMap.toMatrix_comp`,
`LinearMap.toMatrix_id`, `LinearMap.toMatrix_smul`… (`I-j` available for the change of basis if
`upMatrix`'s `finBasisOfFinrankEq` basis must be matched — it is the *same* basis on both sides
since `A, A', B` are all `toMatrix b b` on `locPolyDegSubmoduleBlock`, so `S = S₁ = 1`).
**Attacks**: (1) `restrict hT` of `discHeckeBlockOp` vs `E ∘ U_p^{Cl} ∘ E⁻¹`: equal as linear
maps on `locPolyDegSubmoduleBlock` by I-i + `LinearEquiv.symm_apply_apply` ✓.  (2) `ψ p` in
`AtkinLehnerHypothesis` is `ψ (p : ℚ_p)`; I-h's scalar is `(ψ p)^(k+1)` with the same cast ✓
(the skeleton compiles with both).  (3) `[Nonempty ι]` needed by `upMatrix` ✓ present.

**I-l** `degX_succ_of_atkinLehnerData` (milestone).  **Match**: `degX_succ_classicalPoint`
(`DegreeFormula.lean:56`) with `ω' := partnerChar p ω k`, `ζ' := ζ⁻¹`, `hζ' := hζ.inv`, and
`hAL := atkinLehnerHypothesis_of_atkinLehnerData …` — the `hpK` there is `norm_natCast_p ψ hψ`;
the skeleton's `D : AtkinLehnerData … (nebCharK ψ ω k ζ)` matches.  **Attacks**: `vRep :=
vRepD`, `hvΔ := vRepD_mem_levelM1` are what `classicalData` is instantiated with ✓ (the
statement is written with them).

## 3. Prior-B2 consultation

`.mathlib-quality/lwx-theta/b2_log.jsonl` (6 entries: the `ν`-equivariance family T-AG1a/b,
T-AG2, AL2, AL3 and the slope-past-degree S7.10), `.mathlib-quality/lwx-atkinlehner/b2_log.jsonl`
(empty), `.mathlib-quality/lwx-theta-h2/b2_log.jsonl` (empty), root `.mathlib-quality/b2_log.jsonl`
(NewtonPolygons, unrelated).  No leaf above re-creates a retired statement: no `ν`-family
equivariance is used (all equivariance is through `autFactor`-shape hypotheses `hκ`, `hκ'`,
exactly the `_of_autFactor` interface the retirement prescribed), and no slope statement
quantifies past a degree.  Three defects (two false statements, one undischargeable hypothesis shape) and one missing
axiom were found by this pass and **repaired in the skeleton before ticketing**; this board's
`b2_log.jsonl` starts empty.

## 4. Confidence gate

- Every leaf has a source locator and a Lean ↔ source match paragraph: **yes** (S-a…I-l).
- Every leaf survived ≥ 3 attacks or was repaired: **yes**; four defects were found and repaired
  in the skeleton (§2, L-d, W-b, I-f).
- No leaf needs infrastructure absent from mathlib: **yes** — the only "new" objects are
  `symAct` (finite-rank, 60 lines) and the `AtkinLehnerData` structure.
- Skeleton builds (`lake build PhD`, 3911 jobs, 2026-09-10, sorry warnings only): **yes**.
- Out-of-scope items named in `plan.md`: instantiation of `AtkinLehnerData`; `p^M`; `p = 2`.
