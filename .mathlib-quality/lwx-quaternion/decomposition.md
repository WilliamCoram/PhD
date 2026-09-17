# Decomposition — `lwx-quaternion` (the tame central operator, the determinant certificate, and the adelic data of `D/ℚ`)

**BOARD PATH: `.mathlib-quality/lwx-quaternion/`.**  Companion to `plan.md`; read both before working a
ticket.  Written 2026-09-14 with the adversarial pass.  Locators: `lwx.txt` =
`.mathlib-quality/lwx-seam-m/references/lwx.txt`; `bu04.txt` =
`.mathlib-quality/lwx-stepone/references/bu04.txt`; project code by `File.lean:line` (paths relative
to `PhD/Main/`); mathlib by declaration name (verified by `grep` in
`.lake/packages/mathlib` on 2026-09-14).  The Lean skeleton (every leaf a `:= by sorry`
declaration) builds: `lake build PhD` exit 0, sorries only (2026-09-14).

**Skeleton location**: `TateFredholm/02_CharpolyPairingZ.lean` (new), `LWX/23_QuaternionData.lean`
(new), `LWX/25_QuaternionSlopes.lean` (new), and additive insertions in `LWX/05_AtkinLehner.lean`,
`10_AtkinLehnerLocal.lean`, `10_DiscForms.lean`, `13_AtkinLehnerInst.lean`, `14_Touching.lean`,
`18_AtkinLehnerMap.lean`, `19_AtkinLehnerIdentity.lean`, `20_AtkinLehnerMapH.lean`,
`21_AtkinLehnerIdentityH.lean`, `22_AtkinLehnerFamily.lean` (new fields `ιp_pGL_comm`,
`central_pow` alongside the old `central`, removed by the SWAP ticket).

**Prior-B2 log**: this board's `b2_log.jsonl` is empty.  The project-wide logs (`lwx-theta`: the
five `ν`-equivariance statements; `lwx-h1`: `theta_mem_Iw` needed `include hU`, `κ'` needed its own
`{UK'} {ρ'}`; `lwx-conductor`: R13–R17 needed `include X`) were checked leaf by leaf below: no
name match, no shape match.  The `include`-list lesson is applied: every new declaration whose
proof needs a section hypothesis not in its statement is listed with its `include`.

## 0. The goal, and what the sources say

**What the data assume today** — `18_AtkinLehnerMap.lean:149–168`, field `central`:
`∃ γ ∈ Γ, ∃ u ∈ U, ιp (pGL p) = γ * u ∧ θG u = 1 ∧ ∀ x, γ * x = x * γ`.  In `(D ⊗ 𝔸_f)ˣ` this
says the tame scalar `p^{(p)}` lies in the level, which [LWX]'s neat levels do not satisfy in
general (full level `l` contains it iff `p ≡ 1 (mod l)`).  Decision 1(b) replaces it by centrality
of `ιp(p·1)` and finite order of the tame scalar modulo the level, both true for every open tame
level.

**[LWX, §2.4], the tame level** — `lwx.txt:665–673`:

> "We fix a definite quaternion algebra D over Q which splits at p, and we fix an isomorphism D⊗Q_p ≃ M_2(Q_p) and identify them, so that the groups considered in Subsection 2.2 may be viewed as subgroups of (D⊗Q_p)^×. We fix the tame level structure K^p to be an open compact subgroup of (D⊗A_f^{(p)})^×. We call K^p neat if it satisfies the following condition (see [Bu04, Section 4]): (Neat) for any x∈(D⊗A_f)^×, we have x^{−1}D^×x∩K^pIw_q = {1}. The neat condition is cofinal in the direct system of all tame level structures. For instance, for any l ≥ 3, the full l level structure is neat."

**[LWX, Hypothesis 2.10]** — `lwx.txt:838–840`: "For simplicity, from now on we assume that K^p is neat. But we shall insert discussions throughout on reducing the argument from the general case to the neat case."

**[LWX, §2.5], the `U_p`-cosets** — `lwx.txt:706–716`:

> "We choose a decomposition of the double coset: Iw_q (p 0; 0 1) Iw_q = ∐_{j=0}^{p−1} Iw_q v_j, for example with v_j = (p 0; jq 1), and define (2.5.1) U_p(ϕ) := ∑_{j=0}^{p−1} ϕ|_χ v_j, with (ϕ|_χ v_j)(g) := ϕ(g v_j^{−1})||_χ v_j."

**[LWX, §2.11], the representatives** — `lwx.txt:843–847`:

> "we decompose (D⊗A_f)^× into (a disjoint union of) double cosets ∐_{i=0}^{t−1} D^×γ_iK^pIw_q, for some elements γ_0, γ_1, …, γ_{t−1} ∈ (D⊗A_f)^×. The condition (Neat) implies that the natural map D^× × K^pIw_q → D^×γ_iK^pIw_q for each i sending (δ, u) to δγ_iu is bijective. Since D^× is dense in (D⊗Q_p)^×, we may and will take each γ_i so that its p-component γ_{i,p} is just 1."

**[LWX, Prop 3.1], the certificates** — `lwx.txt:1038–1084`:

> "(1) Each entry of U_p is a sum of operators of the form ||^{[−]}_{δ_p}, where δ_p is the p-component of a global element δ∈D^×. … (3) Each δ_p appearing above belongs to (pZ_p Z_p; qZ_p Z_p^×)"; "For each γ_i, we have (U_pϕ)(γ_i) = ∑_{j=0}^{p−1} ϕ(γ_iv_j^{−1})||^{[−]}_{v_j}. Write each γ_iv_j^{−1} uniquely as δ_{i,j}^{−1}γ_{λ_{i,j}}u_{i,j} with δ_{i,j}∈D^×, λ_{i,j}∈{0,…,t−1}, and u_{i,j}∈K^pIw_q. Then we have (U_pϕ)(γ_i) = ∑_{j=0}^{p−1} ϕ(δ^{−1}_{i,j}γ_{λ_{i,j}}u_{i,j})||_{v_j} = ∑_{j=0}^{p−1} ϕ(γ_{λ_{i,j}})||^{[−]}_{u_{i,j,p}v_j}, where u_{i,j,p} is the p-component of u_{i,j}. Substitute back in u_{i,j}v_j = γ^{−1}_{λ_{i,j}}δ_{i,j}γ_i and note the fact that both γ_i and γ_{λ_{i,j}} have trivial p-component by our choice in Subsection 2.11."

**[LWX, Prop 3.22]'s proof, the Hecke character** — `lwx.txt:1775–1786`:

> "by applying Jacquet–Langlands and [LW12, Proposition 2.8], we see that for every automorphic representation π appearing in S^D_{k+2}(K^pIw_{p^m};ψ), its p-component π_p is a principal series of GL_2(Q_p) whose corresponding two characters of Q_p^× are unr(α) and unr(α^{−1})⊗ω_p, where unr(?) is an unramified character of Q_p^× sending p to ? and ω_p is the p-component of the Hecke character associated to ψ. Moreover, the U_p-eigenvalue on the Iw_{p^m} fixed vector of π_p is αp^{(k+1)/2}. But we can twist the representation π by a central Hecke character associated to ψ^{−1}; then the resulting automorphic representation would appear in S^D_{k+2}(K^pIw_{p^m};ψ^{−1}) … In conclusion, one can pair the U_p-eigenvalues of S^D_{k+2}(K^pIw_{p^m};ψ) and the U_p-eigenvalues of S^D_{k+2}(K^pIw_{p^m};ψ^{−1}) so that they multiply to p^{k+1}. Our assertion on slopes follows from this."

At a general neat level the central character of `π` at `p` need not be `ω_p`: its value at `p` is the product over `ℓ ≠ p` of the inverses of the tame components (product formula), a root of unity — the `χ_M(p)` of the classical statement.  [LWX] draw only the slope conclusion, which is insensitive to it.  The classical statement cited by Buzzard — `bu04.txt:1120–1123`: "If f is classical then one can easily deduce from the classical theory (see for example Theorem 4.6.17 of [15], the fact that λ is an algebraic integer, and the Jacquet–Langlands theorem) that v_p(λ) ≤ k − 1" — is Miyake, *Modular Forms*, Thm 4.6.17: for a `p`-primitive eigenform of level `N p^ν` and character `χ = χ_N χ_{p^ν}`, `a_p(f)·a_p(f|W_{p^ν}) = χ_N(p)·p^{k−1}` (weight `k`; our `k+2` gives `p^{k+1}`).  **Our Lean route does not use this statement**: the identity is proved by the double-coset expansion of `19_AtkinLehnerIdentity.lean`, in which the only change is that the `b = 0` term is `Z` instead of `1`.

**Buzzard's operators** — `bu04.txt:631–650`: "(f|η)(g) = f(gη^{−1})η_p. … L(U,A) = {f : D^×\D^×_f → A : f|η = f for all η ∈ U}. … [UηU]f = ∑_i f|η_i."  Right translation by a central element commutes with every `f|η`: this is the whole content of `translateOp_discHeckeOperator`.

## 1. Part Z — the abstract pairing up to a finite-order operator (`TateFredholm/02_CharpolyPairingZ.lean`)

**R_Z**: `Matrix.norm_roots_charpoly_of_mul_eq_smul_mul` (`02_CharpolyPairingZ.lean:130`): for `A B = c•Z`,
`Z A = A Z`, `Z^N = 1`, `c ≠ 0`, over `[NormedField K] [IsAlgClosed K] [CharZero K]`:
`B.charpoly.roots.map ‖·‖ = A.charpoly.roots.map (‖c‖ / ‖·‖)`.

**Prose proof.** `A` is invertible (Z1–Z3).  Put `M := c • A⁻¹`; then `A M = c • 1`, so
`Matrix.roots_charpoly_of_mul_eq_smul` (`01_CharpolyPairing.lean:180`) gives
`roots(charpoly M) = roots(charpoly A).map (c / ·)`.  From `A B = c Z`, `B = A⁻¹ (c Z) = M Z`, and
`M` commutes with `Z` because `A` does.  It remains to show (Z12) that a commuting factor `Z` of
finite order does not change the norms of the characteristic roots: `Z^N = 1` makes `toLin' Z` a root
of the squarefree polynomial `X^N − 1` (`CharZero`), hence semisimple (Z8), so `K^n` is the direct
sum of the eigenspaces of `Z` (mathlib), each eigenvalue `μ` satisfies `μ^N = 1`, `‖μ‖ = 1` (Z9), and
`M` preserves each eigenspace (mathlib).  Induction on the dimension (Z10): if `Z` is the scalar `μ`,
`M Z = μ • M` and the roots scale by `μ` (Z7); otherwise split off one eigenspace
`V_μ ⊕ W = V`, both `M`- and `Z`-invariant, use `charpoly(f) = charpoly(f|V_μ)·charpoly(f|W)`
(mathlib's `LinearMap.charpoly_prodMap` through `Submodule.prodEquivOfIsCompl` and
`LinearEquiv.charpoly_conj`, the pattern of `Mathlib/LinearAlgebra/Eigenspace/Zero.lean:160–182`)
for `f = M` and `f = M Z`, and recurse on `W`.  Finally (Z14, Z15) transport along the conjugation
`A' = P B Q` (`Matrix.charpoly_conj`) and specialise `c = (ψ p)^{k+1}`.

### Leaves

- **Z1** (leaf, mathlib): `Matrix.det_mul_det_of_mul_eq_smul_mul` (`02_CharpolyPairingZ.lean:41`)
  `(h : A * B = c • Z) : A.det * B.det = c ^ Fintype.card n * Z.det`.
  - Source: `Matrix.det_mul`, `Matrix.det_smul` (mathlib docstring: "`det (c • A) = c ^ Fintype.card n * det A`"); the existing `Matrix.det_mul_det_of_mul_eq_smul` (`01_CharpolyPairing.lean:57`) is the case `Z = 1`.
  - Lean ↔ source: `det (A * B) = det A * det B`, `det (c • Z) = c^n det Z`; rewrite `h`.
  - Attacks: [1] counterexample search — none: `Matrix.det_mul` is unconditional over a commutative ring. [2] edge `n = ∅`: `det = 1` on both sides, `c^0 = 1` ✓. [3] hypothesis test: `[Field K]` is more than needed (a `CommRing` suffices); kept for uniformity with the rest of the file — recorded, not a defect. [5] discharge: two mathlib lemmas, composition of length 2 ✓.  Verdict: SURVIVED.  Prior-B2: none.
- **Z2** (leaf, mathlib): `Matrix.det_ne_zero_of_pow_eq_one` (`:46`) `(hN : 0 < N) (hZ : Z ^ N = 1) : Z.det ≠ 0`.
  - Source: `Matrix.det_pow` (`det (M ^ n) = det M ^ n`), `Matrix.det_one`, `pow_ne_zero_iff`.
  - Lean ↔ source: `det Z ^ N = det (Z^N) = 1 ≠ 0`, so `det Z ≠ 0` (`pow_ne_zero_iff hN.ne'`).
  - Attacks: [2] `N = 0` would make the hypothesis `Z^0 = 1` vacuous and the conclusion false for `Z = 0`: `0 < N` is necessary ✓. [3] over a field only; fine. [5] `pow_eq_zero_iff` needs `N ≠ 0` ✓ supplied.  SURVIVED.
- **Z3** (leaf, project): `Matrix.det_ne_zero_of_mul_eq_smul_mul` (`:50`), `…'` (`:55`): `A.det ≠ 0`, `B.det ≠ 0`.
  - Discharged by: Z1, Z2, `mul_ne_zero`, `pow_ne_zero`.
  - Attacks: [1] if `c = 0` then `A B = 0` and `A` may be singular: `hc` necessary ✓. [2] `Z = 1`, `N = 1` recovers `Matrix.det_ne_zero_of_mul_eq_smul` (`01:110`) ✓ consistent. [5] composition of length 3 ✓.  SURVIVED.
- **Z4** (leaf, mathlib): `Matrix.mul_comm_of_mul_eq_smul_mul` (`:60`) `Z * B = B * Z`; `Matrix.mul_eq_smul_mul_symm` (`:65`) `B * A = c • Z`.
  - Source: `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv` (`A⁻¹ * A = 1` for `IsUnit A.det`), `Matrix.isUnit_iff_isUnit_det`.
  - Lean ↔ source: `B = A⁻¹ * (A * B) = A⁻¹ * (c • Z)`; `A⁻¹ Z = Z A⁻¹` from `Z A = A Z` (multiply by `A⁻¹` on both sides); then `Z B = Z A⁻¹ (c Z) = A⁻¹ Z (c Z) = A⁻¹ (cZ) Z = B Z`, and `B A = A⁻¹ (c Z) A = A⁻¹ c A Z = c Z`.
  - Attacks: [1] without `Z A = A Z`: `A = (0 1; 1 0)`, `Z = diag(1, −1)`, `B = A⁻¹ Z`: then `A B = Z` but `Z B = Z A Z ≠ B Z = A Z Z = A` — the commutation hypothesis is necessary ✓. [2] `Z = 1`: recovers the scalar case ✓. [5] `Matrix.nonsing_inv` API verified by grep (`Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul` in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`) ✓.  SURVIVED.
- **Z5** (leaf, mathlib): `Matrix.norm_det_eq_one_of_pow_eq_one` (`:76`) `‖Z.det‖ = 1`.
  - Source: `norm_pow`, `Matrix.det_pow`, `pow_eq_one_iff_of_nonneg` (`0 ≤ a → n ≠ 0 → (a ^ n = 1 ↔ a = 1)`).
  - Lean ↔ source: `‖det Z‖^N = ‖det Z^N‖ = ‖1‖ = 1`; `‖det Z‖ ≥ 0`, `N ≠ 0`.
  - Attacks: [2] `N = 0` excluded ✓. [3] `NormedField` is needed for `norm_pow` (multiplicativity) — a `NormedRing` would not do; correct typeclass. [5] `pow_eq_one_iff_of_nonneg` exists (`Mathlib/Algebra/Order/Monoid/Lemmas`/`Ring`) ✓.  SURVIVED.
- **Z6** (leaf, mathlib): `Matrix.roots_charpolyRev_smul` (`:88`) `(hμ : μ ≠ 0) : (μ • A).charpolyRev.roots = A.charpolyRev.roots.map (μ⁻¹ * ·)`.
  - Source: `Matrix.charpolyRev` (`det (1 - (X : R[X]) • A.map C)`), `RingHom.map_det` (`f (det M) = det (f.mapMatrix M)`), `Polynomial.compRingHom`, `Polynomial.roots_comp_C_mul_X_add_C` (`Mathlib/Algebra/Polynomial/Roots.lean:244`, used at `01_CharpolyPairing.lean:180` in exactly this way).
  - Lean ↔ source: `(charpolyRev A).comp (C μ * X) = det ((1 − X • A.map C).map (compRingHom (C μ * X))) = det (1 − (C μ * X) • A.map C) = det (1 − X • (μ • A).map C) = charpolyRev (μ • A)`; roots of a composite with `C μ * X + C 0` are `Ring.inverse μ * (r − 0)`.
  - Attacks: [1] `μ = 0` gives `charpolyRev 0 = 1`, no roots, while the RHS has the roots of `A`: `hμ` necessary ✓. [2] `A = 0`: both sides empty ✓. [4] the `comp` direction: `p.comp q` substitutes `q` for `X`; substituting `μX` in `det(1 − X A)` gives `det(1 − μ X A)` ✓ (not `μ⁻¹`), hence roots divide by `μ` ✓. [5] `roots_comp_C_mul_X_add_C` requires `IsUnit a` — `isUnit_iff_ne_zero.2 hμ` ✓.  SURVIVED.
- **Z7** (leaf, mathlib+Z6): `Matrix.roots_charpoly_smul` (`:93`) `(hμ : μ ≠ 0) : (μ • A).charpoly.roots = A.charpoly.roots.map (μ * ·)`.
  - Source: `Matrix.charpoly`, `Matrix.charmatrix`, `Matrix.det_smul`, `Polynomial.roots_C_mul`, `Polynomial.roots_comp_C_mul_X_add_C`.
  - Lean ↔ source: `(charpoly A).comp (C μ⁻¹ * X) = det (μ⁻¹ X • 1 − A.map C) = det (μ⁻¹ • (X • 1 − μ • A.map C)) = μ^{−n} · charpoly (μ • A)`; so `charpoly (μ•A) = C (μ^n) * (charpoly A).comp (C μ⁻¹ * X)` and the roots are `(μ⁻¹)⁻¹ · r = μ r`.  (Alternative route: `Matrix.roots_charpolyRev` on both sides when `A.det ≠ 0`; the `comp` route has no determinant hypothesis.)
  - Attacks: [1] `μ = 0` (before the hypothesis was added): `charpoly 0 = X^n` has `n` roots `0` while `roots(A).map (0 * ·)` has `card roots(A)` roots `0` — equal over an algebraically closed field, but the proof would need the root count; the hypothesis `μ ≠ 0` was **added to the skeleton** on 2026-09-14 (the only consumer, Z10's scalar step, has `‖μ‖ = 1`). [2] `n = ∅` ✓ trivial. [4] direction of scaling checked on `A = diag(a)`: `charpoly (μ a) = X − μ a`, root `μ a` ✓.  SURVIVED (after the edit).
- **Z8** (leaf, mathlib): `Matrix.isSemisimple_toLin'_of_pow_eq_one` (`:110`) `Module.End.IsSemisimple (toLin' Z)`.
  - Source: `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` (`Mathlib/LinearAlgebra/Semisimple.lean:218`: "an endomorphism that is a root of a square-free polynomial is semisimple (in finite dimensions over a field)"); `Polynomial.separable_X_pow_sub_C` (`Mathlib/FieldTheory/Separable.lean:414`: `(hn : (n : F) ≠ 0) (ha : a ≠ 0) : Separable (X ^ n - C a)`); `Polynomial.Separable.squarefree`; `Matrix.toLin'_pow`, `Matrix.toLin'_one`, `Polynomial.aeval_X_pow`/`aeval_one`.
  - Lean ↔ source: `aeval (toLin' Z) (X^N − C 1) = (toLin' Z)^N − 1 = toLin' (Z^N) − 1 = 0`; `X^N − C 1` separable since `(N : K) ≠ 0` (`CharZero`, `0 < N`) and `1 ≠ 0`.
  - Attacks: [1] in characteristic `p ∣ N` the statement can fail (`Z` unipotent of order `p`): `[CharZero K]` is necessary and present ✓. [2] `N = 1`: `Z = 1`, semisimple ✓. [5] the exact name and hypotheses were read from the mathlib source (`isSemisimple_of_squarefree_aeval_eq_zero {p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0)`) ✓; `FiniteDimensional K (n → K)` instance ✓.  SURVIVED.
- **Z9** (leaf, mathlib): `Matrix.norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one` (`:115`) `(hμ : Module.End.eigenspace (toLin' Z) μ ≠ ⊥) : ‖μ‖ = 1`.
  - Source: `Submodule.ne_bot_iff`, `Module.End.mem_eigenspace_iff` (`x ∈ f.eigenspace μ ↔ f x = μ • x`), `LinearMap.pow_apply`, `Matrix.toLin'_pow`, `smul_left_injective`, `pow_eq_one_iff_of_nonneg`.
  - Lean ↔ source: pick `v ≠ 0` with `Z v = μ v`; by induction `Z^N v = μ^N v`; `Z^N = 1` gives `v = μ^N v`, so `μ^N = 1` (`v ≠ 0`), hence `‖μ‖^N = 1`, `‖μ‖ = 1`.
  - Attacks: [2] `μ = 0` would need `v = 0`: excluded by `hμ` ✓. [3] `IsAlgClosed` is not needed here (only `NormedField`, `CharZero` for the section) — over-specified section variables; harmless (a `Type` of the section), noted for cleanup. [5] `pow_eq_one_iff_of_nonneg` ✓.  SURVIVED.
- **Z10** (leaf, mathlib — the core): `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top` (`:102`).
  - Statement (verbatim): `(f g : Module.End K V) (hfg : Commute f g) (hg : ⨆ μ : K, g.eigenspace μ = ⊤) (hnorm : ∀ μ : K, g.eigenspace μ ≠ ⊥ → ‖μ‖ = 1) : (f * g).charpoly.roots.map ‖·‖ = f.charpoly.roots.map ‖·‖` over `[FiniteDimensional K V]`.
  - Source: `Module.End.eigenspaces_iSupIndep` (`Mathlib/LinearAlgebra/Eigenspace/Basic.lean:720`, the eigenspaces of an endomorphism are independent), `Module.End.mapsTo_genEigenspace_of_comm` (`:367`: `(h : Commute f g) (μ) (k) : MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k)`, with `eigenspace_def`: `eigenspace f μ = genEigenspace f μ 1`), `Submodule.prodEquivOfIsCompl` (`Mathlib/LinearAlgebra/Projection.lean:76`), `LinearMap.charpoly_prodMap` (`Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean:63`: `(f₁.prodMap f₂).charpoly = f₁.charpoly * f₂.charpoly`), `LinearEquiv.charpoly_conj` (used as `e.symm.charpoly_conj φ` at `Eigenspace/Zero.lean:177`), `Submodule.finrank_add_eq_of_isCompl` (`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:243`), `Polynomial.roots_mul`, `Multiset.map_add`, Z7 through `LinearMap.charpoly_toMatrix`.
  - Prose (the source's own proof structure is the standard one; the mathlib pattern for one split is quoted from `Eigenspace/Zero.lean:160–182`: "let F := φ.restrict hφV; let G := φ.restrict hφW; let ψ := F.prodMap G; let e := Submodule.prodEquivOfIsCompl V W hVW … have hψ : ψ = e.symm.conj φ … rw [← e.symm.charpoly_conj φ, ← hψ, charpoly_prodMap]"): strong induction on `finrank K V`.  (a) If some eigenspace of `g` is `⊤`, `g = μ • 1`, `f * g = μ • f`, and the roots scale by `μ` with `‖μ‖ = 1` (Z7 on `toMatrix b b f`). (b) Otherwise choose `μ` with `V_μ ≠ ⊥`, `W := ⨆_{ν ≠ μ} V_ν`; `IsCompl V_μ W` from independence and `hg`; `f`, `g` map `V_μ`, `W` into themselves (`mapsTo_genEigenspace_of_comm`, `Submodule.map_iSup`); `charpoly f = charpoly (f|V_μ) * charpoly (f|W)` and likewise for `f * g`; on `V_μ`, `(f*g)|V_μ = μ • f|V_μ`; on `W`, apply the induction hypothesis to `f|W`, `g|W` (`finrank W < finrank V`; `⨆ eigenspace (g|W) = ⊤` since each `V_ν`, `ν ≠ μ`, lies in `W` and in the `ν`-eigenspace of `g|W`; `hnorm` descends since an eigenvector of `g|W` is one of `g`).
  - Attacks: [1] children true, parent false? The multiset of roots of `charpoly (f * g)` is the union over the eigenspaces of the roots of the restrictions **only if** the space is the direct sum of `f*g`-invariant pieces — it is (`V_μ`, `W` are invariant under both `f` and `g`). ✓ [2] `V = 0`: every eigenspace is `⊤ = ⊥`, case (a) applies, both charpolys `1` ✓; `dim V = 1`: `g` scalar, case (a) ✓. [3] `Commute f g` necessary: `f = (0 1; 1 0)`, `g = diag(1, −1)` (norm-one eigenvalues, diagonalisable): `f g = (0 −1; 1 0)` has roots `±i` while `f` has roots `±1` — norms agree here (all `1`), so take `f = diag(2, 1)`, `g = (0 1; 1 0)`: `f g = (0 2; 1 0)`, roots `±√2`, norms `√2, √2`, while `f` has norms `2, 1` — the hypothesis is necessary ✓. `hnorm` necessary: `g = 2 • 1` scales all norms by `2` ✓. [4] no source drift: the statement is our own, at the generality the consumer needs; mathlib's `IsSemisimple.iSup_eigenspace_eq_top` provides `hg` for `g` semisimple over an algebraically closed field ✓. [5] each cited name grepped in the mathlib sources on 2026-09-14 (`Semisimple.lean:92`, `Eigenspace/Basic.lean:367,720`, `Projection.lean:76`, `Charpoly/ToMatrix.lean:63`, `FiniteDimensional/Lemmas.lean:243`); the restriction API `LinearMap.restrict`, `LinearMap.charpoly` on submodules (`FiniteDimensional` instances) ✓.  Size: the one-split pattern is 22 lines in `Zero.lean`; with the induction and the descent of the hypotheses to `W`, expect ~150 LOC.  SURVIVED; this is the board's one genuinely new piece of linear algebra.
- **Z11** (leaf, mathlib+Z8–Z10): `Matrix.norm_roots_charpoly_mul_of_commute_of_pow_eq_one` (`:121`).
  - Discharged by: Z10 at `f := toLin' M`, `g := toLin' Z` (`Commute` from `hMZ` and `Matrix.toLin'_mul`), `hg` from Z8 + `Module.End.IsSemisimple.iSup_eigenspace_eq_top` (`Semisimple.lean:92`, `[IsAlgClosed K] [FiniteDimensional K V]`), `hnorm` from Z9; conclusion transported by `Matrix.charpoly_toLin'` (`Charpoly/ToMatrix.lean:94`: `A.toLin'.charpoly = A.charpoly`) and `Matrix.toLin'_mul`.
  - Attacks: [2] `Z = 1` ✓ trivial. [3] `IsAlgClosed` is used exactly once (the eigenspace decomposition) ✓ necessary: over `ℝ`, `Z = (0 −1; 1 0)` has `Z^4 = 1` but no eigenspaces; the statement is still true there (a coincidence of the complexification), but the route needs algebraic closure ✓. [5] four-lemma composition; the leaf is the assembly, not a discharge — acceptable as an internal node with sorried children.  SURVIVED.
- **Z12** (leaf, project): `Matrix.norm_roots_charpoly_of_mul_eq_smul_mul` (`:130`) — R_Z.  Discharged by Z3, `Matrix.roots_charpoly_of_mul_eq_smul` (`01:180`), Z11, `norm_div`, `Multiset.map_map`.
  - Attacks: [1] children true, parent false? `B = M Z` needs `A B = c Z` and `A M = c 1`: `A (M Z) = (A M) Z = c Z` and `A` injective ⇒ `B = M Z` ✓. [2] `Z = 1` recovers `Matrix.roots_charpoly_of_mul_eq_smul` up to norms ✓. [4] the shape `‖c‖ / ‖x‖` matches `norm_roots_charpoly_atkinLehner` (`05_AtkinLehner.lean:277`) exactly, so consumers see the same multiset expression ✓.  SURVIVED.
- **Z13** (leaf, project): `LWX.norm_roots_charpoly_atkinLehnerZ` (`05_AtkinLehner.lean:295`): adds `Q P = 1`, `A' = P B Q`; discharged by `Matrix.charpoly_conj P Q B hQP` (`01:67`) and Z12.
  - Attacks: [2] `P = Q = 1` ✓. [3] section requires `[CharZero K]` (new in `section SlopesZ`) — needed by Z12 ✓. [5] two lemmas ✓.  SURVIVED.
- **Z14** (leaf, project): `LWX.AtkinLehnerHypothesis.toZ` (`13_AtkinLehnerInst.lean:245`: `Z := 1, N := 1`) and `LWX.norm_roots_charpoly_of_atkinLehnerHypothesisZ` (`:256`, Z13 at `c = (ψ p)^{k+1} ≠ 0`).
  - Attacks: [3] `(ψ p)^{k+1} ≠ 0` from `ψ` injective, `p ≠ 0` ✓ (pattern at `13:238–240`). [4] the definition `AtkinLehnerHypothesisZ` (`13:234`) is the source; `A B = (ψ p)^{k+1} • Z` with `Z` existentially quantified inside the `Prop` — the consumers destructure it (`obtain ⟨⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩`) ✓.  SURVIVED.
- **Z15** (leaf, project): `LWX.neg_log_norm_det_add_of_mul_eq_smul_mul` (`14_Touching.lean:156`), `LWX.det_ne_zero_of_mul_eq_smul_mul_conj` (`:164`).
  - Source: the originals `14_Touching.lean:107–128` (quoted: "**H1 on determinants** … from `A·B = c·1`, `Q·P = 1` and `A' = P·B·Q`, `−log‖det A‖ − log‖det A'‖ = card·(−log‖c‖)`"), Z1, Z5, Z3'.
  - Lean ↔ source: `log‖det A‖ + log‖det B‖ = n log‖c‖ + log‖det Z‖ = n log‖c‖`; `det A' = det B`.
  - Attacks: [1] `‖det Z‖ = 1` is exactly what removes `Z` from the determinant identity; without finite order (`Z = 2 • 1`) the identity fails ✓ hypothesis necessary. [2] `Z = 1` ✓.  SURVIVED.

## 2. Part C — the tame central operator and the identity with `Z`

**R_C**: `LWX.atkinLehnerHypothesisZ_of_atkinLehnerData` (`19_AtkinLehnerIdentity.lean:596`) and its
level-`h` twin (`21_AtkinLehnerIdentityH.lean:652`): H1 in the `Z`-form at the classical points,
from the data with `central` replaced by `ιp_pGL_comm` + `central_pow`.

**Prose proof.** The double-coset expansion of `19_AtkinLehnerIdentity.lean` (docstring, lines 8–30,
quoted: "the `(b,c)`-term into `ψ_neb(1 + bcp)⁻¹ · (p^k · (disc b of φ(x)) ∣_k n(−b/p))`: the
level-equivariance at `ℓ_{b,c}⁻¹` produces the nebentypus value, the central `p` acts trivially
(`AtkinLehnerData.central`) and `Sym^k(p·1) = p^k`. Summing over `c`: the `b = 0` terms give
`p · p^k · φ(x)`, and for `b ≠ 0` the sum `∑_c ψ_neb(1 + bcp)⁻¹` vanishes") is unchanged except at
one point: `term_elt_eq` rewrites the argument of `φ` as `x s_b p⁻¹ ℓ⁻¹`, and where the old proof
used `central` to drop `p⁻¹` (`apply_mul_ιp_pGL_inv`), the new one moves `p⁻¹` to the end
(`ιp_pGL_comm`) and reads `φ(x s_b ℓ⁻¹ p⁻¹) = (Zφ)(x s_b ℓ⁻¹)` with `Z := translateOp (ιp(p·1))`.
Everything downstream applies to `Zφ` in place of `φ` (`Zφ` is again a classical disc form), so the
identity reads `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z`.  `Z` commutes with `U_p` because
`ιp(p·1)` is central (Buzzard's `[UηU]f = ∑ f|η_i` with `(f|η)(g) = f(gη⁻¹)η_p`, `bu04.txt:633–650`),
and `Z^N = 1` on disc forms because `ιp(p·1)^N = γ u` with `γ ∈ Γ` central and `u ∈ U`, `θ u = 1`
(`central_pow`; the old argument for `N = 1`).  The matrix `Zmat := toMatrix bas bas (E ∘ Zcl ∘ E⁻¹)`
on the block model then satisfies `A B = p^{k+1} Zmat`, `Zmat A = A Zmat`, `Zmat^N = 1`, and H1a is
unchanged.

### Leaves — `10_DiscForms.lean` (generic level `h`)

- **C1** (leaf, project): `translateOp` (`10_DiscForms.lean:305`, a `def` with the one-line `left_invt` proof) and its API `translateOp_add` (`:314`), `translateOp_smul` (`:318`), `translateOp_one` (`:322`), `translateOp_translateOp` (`:326`).
  - Source: Buzzard's `(f|η)(g) = f(gη⁻¹)η_p` (`bu04.txt:633`) with the trivial weight action — `translateOp z φ = φ(· z⁻¹)`.
  - Lean ↔ source: pointwise definitions; `AutomorphicFunction.ext`, `AutomorphicFunction.add_apply`/`smul_apply` (used at `19:452`), `mul_inv_rev`, `mul_assoc`.
  - Attacks: [2] `z = 1` ✓; composition order: `translateOp z (translateOp z' φ) x = φ (x z⁻¹ z'⁻¹) = φ (x (z' z)⁻¹)` ✓ (`mul_inv_rev`). [3] no hypothesis on `z` ✓ (left invariance is about `Γ` on the left). [5] `AutomorphicFunction` API names verified in `QMF/01_AutomorphicFunction.lean` (`structure … toFun, left_invt`; `left_invt'`, `ext`, `smul_apply` used in `19`).  SURVIVED.
- **C2** (leaf, project): `apply_mul_of_theta_eq_one'` (`:331`) — the level-`h` generic copy of `18:430` / `20:428`.
  - Discharged by: `mem_discForms_iff θ h ψ κ U hU φ` (`10:79`), `discSlash_one` (as at `20:432`).
  - Attacks: [4] identical statement to `apply_mul_of_theta_eq_oneH` (`20:428`) with `h` generic ✓. [5] the proof is four lines at `20:429–433` ✓.  SURVIVED.
- **C3** (leaf, project): `translateOp_mem_discForms` (`:337`) `(hz : ∀ u ∈ U, z * u = u * z)`.
  - Source: `mem_discForms_iff` (`10:79`: `φ ∈ DiscForms ↔ ∀ (u : U) (g : G), φ.toFun (g * u) = discSlash h ψ κ ⟨θ u, hU u.2⟩ (φ.toFun g)`).
  - Lean ↔ source: `(Zφ)(x u) = φ(x u z⁻¹) = φ(x z⁻¹ u)` (`hz`) `= discSlash (θ u) (φ (x z⁻¹)) = discSlash (θ u) ((Zφ) x)`.
  - Attacks: [3] centrality with respect to `U` is exactly what is used; `z` central in `G` is not needed here ✓ minimal. [1] without `hz`, `Zφ` need not be level-equivariant (translate by a non-normalising element) ✓ necessary.  SURVIVED.
- **C4** (leaf, project): `translateOp_eq_self_of_eq_mul` (`:344`).
  - Discharged by: `AutomorphicFunction.left_invt'` (`γ⁻¹ ∈ Γ`), `hγc`, `inv_mem hu`, `θ u⁻¹ = 1` (as at `19:207–210`), C2.
  - Lean ↔ source: `φ(x (γu)⁻¹) = φ(x u⁻¹ γ⁻¹) = φ(γ⁻¹ x u⁻¹) = φ(x u⁻¹) = φ x`.  This is the old `apply_mul_ιp_pGL_inv` (`19:130`) made generic in `z`.
  - Attacks: [4] the old proof at `19:193–215` is exactly this computation ✓ no drift.  SURVIVED.
- **C5** (leaf, project): `translateOp_discHeckeOperator` (`:351`) `(hz : ∀ x, z * x = x * z)`.
  - Source: `discHeckeOperator` (`10:179`) is `AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη hfin`; its value is the finite sum over representatives of `f|η_i` (Buzzard `bu04.txt:648–650`; the project's `discHeckeOperator_apply_eq_sum` (`19:74`) is the instance at `vRepD` under `hv`).
  - Lean ↔ source: `(U_p (Zφ))(x) = ∑ (Zφ)(x η_i⁻¹)|η_i = ∑ φ(x η_i⁻¹ z⁻¹)|η_i = ∑ φ(x z⁻¹ η_i⁻¹)|η_i = (U_p φ)(x z⁻¹)`.
  - Attacks: [1] children/parent: the identity uses only `z` central and the shape "sum of translates-then-slash" — true for any choice of representatives (the abstract operator is independent of the choice, `heckeOperatorSlash` is defined via `hfin.toFinset`/`Quotient.out`; the proof must go through the `apply` lemma of `AbstractHeckeOperatorSlash.heckeOperatorSlash` — `heckeOperatorSlash_apply_rep` is cited in `10:200`'s docstring; if only a representative-indexed formula exists, prove the statement for the fixed system `Quotient.out`). [3] `hz` for all `x` is more than needed (commuting with the representatives and `U` suffices), but central is what `ιp(p·1)` is; fine. [2] `z = 1` ✓.  Risk: medium (API shape of the abstract Hecke operator); SURVIVED.

### Leaves — `18_AtkinLehnerMap.lean` (level 1) and `20_AtkinLehnerMapH.lean` (level `h`)

- **C6** (leaf, project): `centralOp` (`18:440`, `def`), `centralOp_mem_classicalDiscForms` (`18:449`), `centralOpCl` (`18:455`, `map_add'`, `map_smul'`), `centralOpCl_apply` (`18:461`, rfl).
  - Discharged by: C3 with `hz := fun u _ => D.ιp_pGL_comm u` (the new field), `mem_classicalDiscForms_iff` (`18:364`), C1.
  - Attacks: [4] `ClassicalDiscForms = DiscForms ⊓ locPolyForms` (`18:360`); the second component is pointwise (`φ(x z⁻¹) ∈ locPolyDegSubmodule`) ✓. [3] the explicit argument order is `centralOpCl θG ψ U hU k D κ` (declaration order of the section variables; `D` before `κ`) — recorded, found by the skeleton build. [5] `translateOp` applies at `h = 1` ✓ (`variable {h}` in the `Translate` section).  SURVIVED.
- **C7** (leaf, project): `centralOpCl_pow_eq_one` (`18:467`) `∃ N, 0 < N ∧ centralOpCl … ^ N = 1`.
  - Discharged by: `D.central_pow` (new field), `LinearMap.pow_apply`, C1 (`translateOp_translateOp` iterated: `(translateOp z)^[N] φ = translateOp (z^N) φ`), C4 (`z^N = γ u`), `Subtype.ext`.
  - Attacks: [1] children/parent: `Z^N φ = translateOp (ιp(p·1)^N) φ` needs the iteration lemma with `z` self-commuting — trivial ✓. [2] `N = 1` is the old `central` ✓. [3] `hγc` in `central_pow` is used (moving `γ⁻¹` to the left) ✓ necessary.  SURVIVED.
- **C8** (leaf, project): `discHeckeOperatorCl_comp_centralOpCl` (`18:471`).  Discharged by C5 (`hz := D.ιp_pGL_comm`) and `Subtype.ext`; `discHeckeOperatorCl` is `discHeckeOperator` on the first component (`18:402–408`).
  - Attacks: [4] `LinearMap.comp` order: `(U_p ∘ Z) φ = Z (U_p φ)` ✓ both sides read on the underlying automorphic function.  SURVIVED.
- **C9–C11** (leaves, project): the level-`h` copies `centralOpH_mem_classicalDiscFormsH` (`20:447`), `centralOpClH` (`20:453`), `centralOpClH_pow_eq_one` (`20:466`), `discHeckeOperatorClH_comp_centralOpClH` (`20:470`).  Same discharges with `mem_classicalDiscFormsH_iff` (`20:363`), `ClassicalDiscFormsH` (`20:356`), `discHeckeOperatorClH` (`20:399`).  Attacks as C6–C8; the explicit order is `centralOpClH θG ψ U hU h k D κ`.  SURVIVED.

### Leaves — `19_AtkinLehnerIdentity.lean` / `21_AtkinLehnerIdentityH.lean`

- **C12** (leaf, project): `blockProj_zero_apply_term_eltZ` (`19:470`).
  - Source: the original `blockProj_zero_apply_term_elt` (`19:183–233`), quoted docstring: "**Disc `0` of `φ(x s_b p⁻¹ ℓ⁻¹)`**: the central `p` acts trivially and `ℓ⁻¹` fixes disc `0` with `d`-entry `1 − bcp`, so it is `nebK(1 − bcp) · symAct(conj ℓ⁻¹)(φ(x)|_b)`."
  - Lean ↔ source: the same statement with `centralOp θG ψ U D φ x` in place of `φ x` on the right.  Proof: as the original, replacing `hmove : φ (y * (ιp p)⁻¹ * ℓ⁻¹) = φ (y * ℓ⁻¹)` (lines 212–215, which used `D.central`) by `hmove : φ (y * (ιp p)⁻¹ * ℓ⁻¹) = (centralOp … φ) (y * ℓ⁻¹)` from `ιp_pGL_comm` (`(ιp p)⁻¹ ℓ⁻¹ = ℓ⁻¹ (ιp p)⁻¹`) and `centralOp_apply`; then `hmain := blockProj_zero_apply_mul_ιp … (centralOp_mem_classicalDiscForms … hφ) y hg hg0` and `hsh` via `shapiro_blockProj` for `centralOp φ`.
  - Attacks: [1] children/parent: `blockProj_zero_apply_mul_ιp` and `shapiro_blockProj` need `Zφ ∈ ClassicalDiscForms`/`DiscForms` — C6 ✓. [2] `Z = 1` (old data) reproduces the old statement ✓. [4] no drift: the only change is where `p⁻¹` lands.  SURVIVED.
- **C13** (leaf, project): `atkinLehner_term_eqZ` (`19:484`) — as `atkinLehner_term_eq` (`19:242–326`) with C12 in the `hin` step (`19:301`).  Attacks: [4] the `χ` factors are evaluated at `x v_c⁻¹`, `w`, `v_b` only (`hχ`, `19:295–298`), never at `ιp(p·1)` — so no `χ(ιp p)` appears ✓ (this was the one place a spurious root of unity could have entered).  SURVIVED.
- **C14** (leaf, project): `blockProj_zero_discHecke_atkinLehnerZ` (`19:511`) — as the original (`19:328–427`): the `b = 0` terms give `p·p^k • blockProj 0 (Zφ x)`, the `b ≠ 0` sums vanish by `hsum` unchanged.  Attacks: [1] the character sum `∑_c ψ_neb(1+bcp)⁻¹ = 0` is independent of `Z` ✓. [2] `Z = 1` ✓.  SURVIVED.
- **C15** (leaf, project): `discHeckeCl_comp_atkinLehnerZ` (`19:540`) — as the original (`19:429–466`) with `shapiro_blockProj` applied to `centralOpCl … φ` on the right; `centralOpCl_apply`.  SURVIVED.
- **C16** (leaf, project): `atkinLehnerHypothesisZ_of_atkinLehnerData` (`19:596`).
  - Source: the original assembly `19:528–622` (quoted: "`A B = p^{k+1}` is `discHeckeCl_comp_atkinLehner` in the block model, and `A' = W B W⁻¹` by construction"); the new witnesses `Zmat := LinearMap.toMatrix bas bas (E ∘ₗ centralOpCl … ∘ₗ E.symm)`, `N` from C7.
  - Lean ↔ source: `hkey : T ∘ (Wb.symm ∘ T' ∘ Wb) = (ψ p)^{k+1} • (E ∘ Zcl ∘ E⁻¹)` pointwise from C15 as before (`19:595–614`, with `h3` now `= (ψ p)^{k+1} • E (Zcl g)`); `A B = c • Zmat` by `LinearMap.toMatrix_comp`, `map_smul`; `Zmat A = A Zmat` from C8 conjugated by `E` (`hTE`, `19:587–590`); `Zmat^N = 1` from C7 (`(E ∘ Z ∘ E⁻¹)^N = E ∘ Z^N ∘ E⁻¹`, `LinearMap.toMatrix_id`); `P, Q` unchanged.
  - Attacks: [1] the transport `T = E ∘ U_p ∘ E⁻¹` is `hTE`; the commutation transports because `E` is an equivalence ✓. [3] `[Nonempty ι]`, `hstab`, `hc` as before ✓. [4] the conclusion is the Z-form at the same matrices as the old milestone ✓.  Size: the original is 95 lines; expect ~110.  SURVIVED.
- **C17–C21** (leaves, project): `21:518, 536, 566, 596, 652` — the level-`h` twins, from the originals `21:182–512, 577–` with `centralOpH`, `atkinLehnerMapH`, `wGLH`, `ℓGLH`, `discEvalAtRepsClH`.  Same attacks.  SURVIVED.

### The SWAP and the repairs (statements textually unchanged; not skeleton leaves)

- **S0 SWAP** — after Z1–Z15, C1–C21, L1–L2: in `13`, delete `AtkinLehnerHypothesis` (scalar), `roots_charpoly_of_atkinLehnerHypothesis`, `AtkinLehnerHypothesis.toZ`; rename `AtkinLehnerHypothesisZ → AtkinLehnerHypothesis`, `norm_roots_charpoly_of_atkinLehnerHypothesisZ → norm_roots_charpoly_of_atkinLehnerHypothesis`.  In `18`, `20`, `22`, delete the field `central` (and `central := …` lines of `toData`, `toDataH`, `toH`; `central := sorry` of `23:407`).  In `19`/`21`, delete `apply_mul_ιp_pGL(_inv)(H)`, the four old term/identity lemmas and `atkinLehnerHypothesis_of_atkinLehnerData(H)`; rename the `Z`-suffixed ones to the old names.  In `14`, delete the three scalar determinant lemmas (Z15 replaces them).  Keep `05`'s scalar `roots_charpoly_atkinLehner` (still true, still used by the `AtkinLehner` reduction section).  Then `lake build PhD` fails exactly at the repair sites below.
- **R1** `14_Touching.lean`: `isStepOneTouching_of_atkinLehnerHypothesis`, `hasUnitBand_of_atkinLehnerHypothesis` — destructure `⟨B, ⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩`; `det_ne_zero_of_mul_eq_smul' hcne hAB ↦ Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hN hZN`; `det_ne_zero_of_mul_eq_smul_conj … ↦ det_ne_zero_of_mul_eq_smul_mul_conj hcne hAB hN hZN hQP hA'`; `neg_log_norm_det_add_of_mul_eq_smul … ↦ neg_log_norm_det_add_of_mul_eq_smul_mul hcne hAB hN hZN hQP hA'` (sites `14:702, 709, 710, 754`).
- **R2** `15_TouchingH.lean:200–251`: the same two edits.
- **R3** `15_StepThree.lean`: `norm_pow_le_of_mem_roots_charpoly_matrix` (`:415–427`), `unitSlope_charpolyRev_matrix_le` (`:447–452`), `faceLeft_charpolyRev_matrix_eq` (`:517–547`): destructure; `norm_roots_charpoly_atkinLehner hcne hAB hQP hA' ↦ norm_roots_charpoly_atkinLehnerZ hcne hAB hZA hN hZN hQP hA'`; determinant lemmas as R1.  `rightIndex_sub_touchX_eq_ordDim` (`:746–747`): the `hA0` line.
- **R4** `17_DegreeFormula.lean`, `15_StepThree` `degX_succ`, `degXint_zero`, `touchX_sub_leftIndex_eq_ordDim`: pass-through (they only forward `hAL`); recompile.
- **R5** `19:500` `atkinLehnerHypothesis_of_conj`: with `A B = c Z`: `(S A S₁)(S B S₁) = S (A B) S₁ = c • (S Z S₁)`; `(S Z S₁)(S A S₁) = S Z A S₁ = S A Z S₁ = (S A S₁)(S Z S₁)`; `(S Z S₁)^N = S Z^N S₁ = 1` (`hS : S₁ * S = 1`); `P, Q` as before.  `21:547` `atkinLehnerHypothesis_of_conjH` likewise.
- **R6** `23_ConductorSlopes.lean:113` `atkinLehnerHypothesis_symm`: `B' := P A Q`, `Z' := P Z Q`; `A' B' = P (B A) Q = c • (P Z Q)` (`Matrix.mul_eq_smul_mul_symm`); `Z' A' = P Z B Q = P B Z Q = A' Z'` (`Matrix.mul_comm_of_mul_eq_smul_mul`); `Z'^N = P Z^N Q = P Q = 1` (`mul_eq_one_comm`, induction with `hQP`); the conjugation `A = Q B' P` as before (`23:139–144`).
- **R7** `23:152–187` `norm_pow_le_of_mem_roots_charpoly_matrixH`, `unitSlope_charpolyRev_matrix_leH`: as R3.
- **R8** `23:325` `toReal_unitSlope_charpolyRev_reflect`: **restate** `hroots` as `A'.charpoly.roots.map ‖·‖ = A.charpoly.roots.map (‖c‖ / ‖·‖)` (the norm form; the old exact form is `norm_roots` after `Multiset.map`, so the new hypothesis is weaker and the conclusion unchanged).  Repair: `hA' : A'.det ≠ 0` now from "no root of norm `0`" (`Matrix.det_eq_prod_roots_charpoly`, membership transported through `Multiset.mem_map`, `div_ne_zero`); in `hcount` (`23:355–366`) apply the `hnormOnly` trick of `15_StepThree.lean:540–548` (`countP` of a predicate on `‖y⁻¹‖` equals `countP` of the predicate on `r⁻¹` over the norm multiset), then rewrite with the new `hroots`.  Then `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` (`23:459–481`): `roots_charpoly_of_atkinLehnerHypothesis (hAL := hB) ↦ norm_roots_charpoly_of_atkinLehnerHypothesis (hAL := hB)`.
- **R9** `23:508` `hasUnitBand_of_atkinLehnerData` and the family theorems of `23`/`24`: pass-through.
- **R10** `22`: `toData`, `toDataH` transports already carry the new fields; delete the `central` lines at SWAP.
- Attack on the swap as a whole: every consumer was listed by `grep AtkinLehnerHypothesis` on 2026-09-14 (`13`: 4 sites, `14`: 3, `15_StepThree`: 8, `15_TouchingH`: 3, `17`: 2, `19`: 3, `21`: 3, `23`: 6); each uses the hypothesis only through determinants and norms of roots (audit in `plan.md`, "Generality decisions" 2).  No statement in `24_DegreePeriodicity`, `25` mentions `AtkinLehnerHypothesis`.

## 3. Part L — the Iwahori decomposition (`10_AtkinLehnerLocal.lean`)

- **L1** (leaf, project): `exists_mem_Iw_mul_vQ` (`10_AtkinLehnerLocal.lean:433`) `(hk : k ∈ Iw p 1) : ∃ c : Fin p, ∃ k' ∈ Iw p 1, vQ p 0 * k = k' * vQ p (c : ℕ)`.
  - Source: [LWX, §2.5] `lwx.txt:706–711` (quoted in §0): "`Iw_q (p 0; 0 1) Iw_q = ∐_{j=0}^{p−1} Iw_q v_j`, for example with `v_j = (p 0; jq 1)`" (`q = p` at level `1`; `vQ p c = !![p, 0; c * p, 1]`, `10:41`).
  - Lean ↔ source: the source asserts the decomposition; the computation: for `k = (a b; c d) ∈ Iw_p` (`a`, `d` units: `norm_apply_zero_zero_of_mem_Iw`, `05:172`), `(p 0; 0 1) k = (pa pb; c d)`, and with `j ∈ {0, …, p−1}` the residue of `(c/p)·d⁻¹` (`‖c/p‖ ≤ 1`; `PadicInt.toZMod`, `PadicInt.toZMod_spec`), `k' := (pa pb; c d)·vQ(j)⁻¹ = (a − jpb, pb; c/p − jd, d)` has integral entries, `‖c/p − jd‖ ≤ p⁻¹` by the choice of `j`, and unit determinant (`det = p·det k / p`).
  - Attacks: [1] is `c/p − j d ∈ pℤ_p` achievable? `c/p ∈ ℤ_p`, `d ∈ ℤ_p^×`, so `(c/p) d⁻¹ ∈ ℤ_p` has a residue `j` mod `p` and `c/p − j d = d((c/p)d⁻¹ − j) ∈ pℤ_p` ✓. [2] `k = 1`: `c = 0`, `j = 0`, `k' = (1 0; 0 1)` ✓; `p = 2` is not excluded and the computation is valid there too. [3] `Iw p 1` requires entries `≤ 1`, `‖c‖ ≤ p⁻¹`, `‖det‖ = 1` (`05:140`) — all three used ✓. [5] `PadicInt.toZMod_spec : x - (toZMod x).val ∈ maximalIdeal ℤ_[p]` (mathlib `Mathlib/NumberTheory/Padics/RingHoms.lean`) ✓; `Padic.norm_le_one_iff`… the passage `ℚ_p ↔ ℤ_p` for the residue is the fiddly part (expect ~80 LOC).  SURVIVED.
- **L2** (leaf, project): `eq_of_vQ_eq_mul_vQ` (`:438`) `(hk : k ∈ Iw p 1) (h : vQ p b = k * vQ p c) : b = c` for `b c : Fin p`.
  - Lean ↔ source: uniqueness of the coset in `∐`: `k = vQ b · vQ c⁻¹ = (1 0; b − c 1)`, so `‖(b − c : ℚ_p)‖ ≤ p⁻¹`, i.e. `p ∣ (b − c)` with `|b − c| < p`, hence `b = c`.
  - Attacks: [2] `b = c` trivial ✓. [3] only the lower-left bound of `Iw` is used ✓. [5] `Padic.norm_int_le_pow_iff_dvd`/`padicNorm` API: `‖(n : ℚ_p)‖ ≤ p⁻¹ ↔ (p : ℤ) ∣ n` (`Padic.norm_int_le_pow_iff_dvd` with exponent `1`) ✓ exists; `Nat.eq_of_lt_of_dvd`-style finish (`Int.eq_zero_of_abs_lt_dvd`).  SURVIVED.

## 4. Part Q — the instantiation for `D/ℚ` (`23_QuaternionData.lean`)

**R_Q**: `QuaternionInput.atkinLehnerFamily` (`23:407`), `atkinLehnerFamilyH` (`23:425`), `upDatum` (`23:527`) with `det_certM1_eq` (`23:521`).

**Prose.** `G = (D ⊗ 𝔸_f)ˣ`, `Γ = D^×` (`globalUnits`), `θ = thetaInt` (`08:100`).  (i) The section: `ιp g := unitAt (E g)` is the adelic unit with `p`-component `g` and every other component `1` (`QMF/04_UpiElement.lean:255–300`, docstrings quoted: "The `v`-component matrix of `unitAt m` is `m`"; "Away from `v`, `unitAt m` has component `1`: it is a genuinely single-place unit"); it is a homomorphism because `(1 + ι(a−1))(1 + ι(b−1)) = 1 + ι(ab−1)` (`iotaV_mul`). (ii) Single-place elements commute with elements of trivial `p`-component: `ι(x)·y = ι(x)·ι(toLocal y)` (the restricted-product identity `single(a)·b = single(a·b_v)`), so `ι(x) y = 0 = y ι(x)` when `toLocal y = 0`, and `(1 + ι x)(1 + y') = 1 + ι x + y'` symmetrically. (iii) The tame part `g ιp(θ g)⁻¹` has trivial `p`-component and is multiplicative (by (ii)); the level `U := {θ g ∈ Iw_p, tamePart g ∈ Kt}` is [LWX]'s `K^p Iw_q` (`lwx.txt:671`), contains `ιp(Iw_p)`, and is normalised by `w`, `w_h` on its disc-`0` part (`wQ_conj_mem_Iw`, `wQH_conj_mem_Iw`) since conjugation by `p`-local elements fixes the tame part. (iv) `ιp(p·1)` is central (a scalar at `p`, `1` elsewhere); `ιp(p·1)^N = (p_global)^N · (tameScalar)^N` with `tameScalar^N ∈ Kt` by hypothesis. (v) The Hecke character `χ(g) = ψ_neb(det θ(g)·q(g)⁻¹)`: a unit since `‖det θ g‖ = ‖q g‖`, multiplicative by `nebCharK_psi_mul`, trivial on `D^×` (`q = det θ` there), `ψ_neb(det θ u)` on `U` (`q u = 1`: `q(ιp(θu)) = p^{v(det θu)} = 1` for `θu ∈ Iw`, `q(tamePart u) = 1`), and `1` at `v_c`, `w`, `w_h` (`q = p^{v(det)}` there). (vi) The cosets: `U η U = ∐ U v_c` from L1–L2 via (iii). (vii) The factorisation from the class-set bijection (`DoubleCoset.rel_iff`). (viii) `det = p`: from `c_i v_t⁻¹ = d c_j u`, `θ(c_i) = θ(c_j) = 1` gives `θ(u)θ(v_t) = θ(d)⁻¹`, and `q(c_i) q(v_t)⁻¹ = q(d) q(c_j) q(u)` gives `q(d) = p⁻¹`, hence `det θ(d) = p⁻¹` (`normClass_global`) and `det(θ(u)θ(v_t)) = p`.

### Leaves

- **Q1** (leaf, project): `det_thetaInt_ne_zero` (`23:54`), `thetaIntGL` (`:58`, `map_one'`, `map_mul'`), `coe_thetaIntGL` (`:63`, rfl).
  - Discharged by: `thetaInt` is a `MonoidHom` (`08:100`): `θ g · θ g⁻¹ = θ 1 = 1`, `Matrix.det_mul`, `mul_ne_zero_iff`; `Matrix.GeneralLinearGroup.mkOfDetNeZero` (`Units.ext` + `map_one`, `map_mul`).
  - Attacks: [1] the first skeleton attempt built `thetaIntGL` by re-composing the algebra homs at `F = ℚ` and failed with an instance mismatch (`DivisionRing.toRatAlgebra` vs `instAlgebraAdicCompletion`); the present definition through `thetaInt` avoids every explicit `Algebra ℚ` instance ✓ — recorded as a trap for the whole file: **never write `D ⊗[ℚ] K_p` or `RigidificationAt.equiv (F := ℚ)` explicitly at `F = ℚ`**. [5] `mkOfDetNeZero` exists (`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`) ✓.  SURVIVED.
- **Q2** (leaf, project): `ιpD` (`:69`, `map_one'`, `map_mul'`).
  - Source: `unitAt` (`04_UpiElement.lean:255–266`), `one_add_iotaV_mul` (`:144`, quoted: "`(1 + iotaV F D v (a - 1)) * (1 + iotaV F D v (b - 1)) = 1`" for `a * b = 1`; its `expand`/`collapse` computation gives the general product `1 + iotaV (ab − 1)`), `iotaV_mul` (`:107`), `Matrix.GeneralLinearGroup.map` (`Defs.lean:170`, a `MonoidHom`).
  - Lean ↔ source: `unitAt 1 = 1`: `E⁻¹ 1 − 1 = 0`, `iotaV 0 = 0`; `unitAt (m m') = unitAt m · unitAt m'`: `Units.ext`, the `expand`/`collapse` identity with `a := E⁻¹ m`, `b := E⁻¹ m'`, `map_mul` of `E⁻¹`.  Sub-lemma to state and prove first: `unitAt_mul (m m') : unitAt F A v (m * m') = unitAt F A v m * unitAt F A v m'` (generic `F`, in the `Generic` section of `23` or upstream).
  - Attacks: [1] `unitAt_mul` is not in `04_UpiElement` (only `unitAt_inv`, `:286`) — a genuine small gap, ~15 LOC ✓ planned. [4] the `Matrix.GeneralLinearGroup.map (padicComparison p)` step is a hom ✓.  SURVIVED.
- **Q3** (leaf, project): `thetaInt_ιpD` (`:79`), `thetaIntGL_ιpD` (`:83`), `ιpD_injective` (`:86`).
  - Discharged by: `toMatrix_unitAt` (`04:294`: `toMatrix F D v (unitAt F D v m) = m`), `padicComparisonSymm_comp` (`08:67`), `RingHom.mapMatrix` composition (`Matrix.map_map`), `Units.ext`, `Function.LeftInverse.injective`.
  - Attacks: [2] `g = 1` ✓. [5] `thetaInt = (mapMatrix padicComparisonSymm).toMonoidHom.comp toMatrix` (`08:100–101`) ✓; `mapMatrix (f.comp g) = (mapMatrix f).comp (mapMatrix g)` (`RingHom.mapMatrix_comp`) ✓.  SURVIVED.
- **Q4** (leaf, project — generic): `QMF.iotaV_mul_eq_zero_of_toLocal_eq_zero` (`23:104`, section `Generic`, arbitrary `F`).
  - Source: `singleₗ_mul_singleₗ` (`04:79`: `singleₗ F v a * singleₗ F v b = singleₗ F v (a * b)`), `singleₗ_apply_same/_ne` (`:66,70`), `iotaV_tmul` (`:102`), `toLocal_tmul` (`:120`), `evalAlgHom_apply` (`:90`), `TensorProduct.induction_on`, `Algebra.TensorProduct.tmul_mul_tmul`.
  - Lean ↔ source: first the identity `iotaV x * y = iotaV x * iotaV (toLocal y)` (and the symmetric one): on pure tensors, `(d ⊗ single a)(d' ⊗ b) = dd' ⊗ (single a · b) = dd' ⊗ single (a · b_v) = (d ⊗ single a)(d' ⊗ single b_v)` with the restricted-product identity `single a * b = single (a * b v)` (sub-lemma `singleₗ_mul : singleₗ F v a * b = singleₗ F v (a * b v)`, by `FiniteAdeleRing.ext` componentwise as in `singleₗ_mul_singleₗ`); then `hy` gives `iotaV x * iotaV 0 = 0`.
  - Attacks: [1] children/parent: bilinearity in `y` ✓ (`toLocal` is linear, `iotaV` linear); the identity is checked on pure tensors and extended by `TensorProduct.induction_on` twice ✓. [2] `x = 0` ✓. [3] stated generically to avoid the `F = ℚ` instance trap ✓ (the first skeleton attempt at `F = ℚ` failed for exactly that reason). [5] `singleₗ_mul` is a new sub-lemma (~15 LOC) ✓ planned inside the ticket.  SURVIVED.
- **Q5** (leaf, project): `ιpD_comm_of_thetaInt_eq_one` (`:117`).
  - Discharged by: `thetaInt y = 1 ⇒ toLocal (y : D ⊗ 𝔸) = 1` (`mapMatrix padicComparisonSymm` and `E` are injective; `toMatrix_apply` `04:228`), `toLocal (y − 1) = 0`, Q4 at `x := E⁻¹(g) − 1`, `y − 1`; `Units.ext`, `mul_add`/`add_mul`.
  - Lean ↔ source: `(1 + ιx)(1 + y') = 1 + ιx + y' + ιx·y' = 1 + ιx + y'` and symmetrically.
  - Attacks: [1] the hypothesis "trivial `p`-component" is on the *unit* `y`; its inverse also has trivial `p`-component (used nowhere here) ✓. [2] `y = 1` ✓. [4] this is the abstract fact behind [LWX]'s "both `γ_i` and `γ_λ` have trivial `p`-component" (`lwx.txt:1083–1084`) being usable ✓.  SURVIVED.
- **Q6** (leaf, project): `ιpD_pGL_comm` (`:122`).
  - Discharged by: `unitAt (p • 1)`: `E⁻¹ (p • 1) = p • 1` (`map_smul`/`map_natCast` of the algebra equivalence), `iotaV ((p − 1) • 1) = (p − 1) • (1 ⊗ singleₗ 1)`; `1 ⊗ e` is central in `D ⊗ 𝔸_f` (`Algebra.TensorProduct.tmul_mul_tmul`, `mul_comm` in the commutative `𝔸_f`, `TensorProduct.induction_on`); `Units.ext`.
  - Attacks: [1] centrality of `1 ⊗ e`: `(d ⊗ b)(1 ⊗ e) = d ⊗ be = d ⊗ eb = (1 ⊗ e)(d ⊗ b)` ✓ needs only commutativity of `𝔸_f`. [4] `pGL p` is `(p : ℚ_p) • 1` (`18:69`) and `Matrix.GeneralLinearGroup.map` sends it to `(p : K_p) • 1` ✓; `E⁻¹` of a scalar matrix is the scalar (`AlgEquiv.map_smul`, `map_one`) ✓ — but beware the instance trap: state the scalar as `(p : ℕ) • 1` or `algebraMap`, not through `Algebra ℚ`.  SURVIVED.
- **Q7** (leaf, project): `tameSubgroup` (`:126`, closure proofs), `tamePart_mem_tameSubgroup` (`:138`), `eq_ιpD_mul_tamePart` (`:145`).
  - Discharged by: `map_mul`, `map_one` of `thetaInt`; inverse: `θ g · θ g⁻¹ = 1`; `thetaInt_ιpD`, `coe_thetaIntGL`, `Matrix.coe_units_inv`; for `eq_ιpD_mul_tamePart`: `g = tamePart g · ιp(θ g)` by definition (`inv_mul_cancel_right`), and `tamePart g` commutes with `ιp(θ g)` by Q5.
  - Attacks: [4] **caught by the attack pass**: `g = ιp(θ g) · tamePart g` is *not* the definitional identity (which is `g = tamePart g · ιp(θ g)`); it holds by Q5 — the sketch says so ✓ statement kept (it is the form the coset argument uses). [2] `g = 1` ✓.  SURVIVED.
- **Q8** (leaf, project): `tamePart_mul` (`:149`), `tamePart_one` (`:153`), `tamePart_inv` (`:156`), `tamePart_ιpD` (`:159`), `tamePart_eq_self_of_thetaInt_eq_one` (`:162`), `tamePart_conj_ιpD` (`:167`).
  - Discharged by: Q5 (`ιp(θ g)⁻¹` commutes with `tamePart g'`), `map_mul` of `thetaIntGL`, `thetaIntGL_ιpD`, `mul_inv_cancel`; `tamePart_conj_ιpD` from `tamePart_mul`, `tamePart_inv`, `tamePart_ιpD`.
  - Attacks: [1] `tamePart_mul`: `g g' ιp(θg')⁻¹ ιp(θg)⁻¹ = g ιp(θg)⁻¹ g' ιp(θg')⁻¹` iff `ιp(θ g)⁻¹` commutes with `g' ιp(θg')⁻¹ = tamePart g'` ✓ (Q5, `θ(tamePart g') = 1`). [2] `g = 1`, `g = ιp x` ✓.  SURVIVED.
- **Q9** (leaf, project): `levelOf` (`:177`, closure), `levelOf_subset_levelM1` (`:187`), `ιpD_mem_levelOf` (`:191`), `mem_levelOf_of_thetaInt_eq_one` (`:195`).
  - Discharged by: `Iw p 1` is a submonoid (`05:140`), `Iw_one_le_M1` (`10:297`), Q8; **sub-lemma** `inv_mem_Iw : g ∈ Iw p 1 → g⁻¹ ∈ Iw p 1` (for `θ(u⁻¹) = (θ u)⁻¹`: the inverse of `(a b; c d)` with unit determinant is `det⁻¹ (d −b; −c a)`, `Matrix.inv_fin_two`/`Matrix.adjugate_fin_two`; entries `≤ 1`, lower-left `‖−c/det‖ ≤ p⁻¹`, `‖det⁻¹‖ = 1`).
  - Attacks: [1] `inv_mem_Iw` is not in `05`/`10` (grep 2026-09-14) — sub-leaf, ~25 LOC ✓ planned. [2] `Kt = ⊥`: `levelOf ⊥ = ιp(Iw_p)` ✓ consistent. [3] `Kt ≤ tameSubgroup` is not needed for the subgroup structure (only for `Kt`'s elements to have trivial `p`-component when used) — it is used in `normClass_level` (`q(tamePart u) = 1` needs `tamePart u ∈ Kt`, fine) and nowhere for closure ✓.  SURVIVED.
- **Q10** (leaf, project): `levelOf_wGL_conj` (`:201`), `levelOf_wGLH_conj` (`:207`).
  - Source: `wQ_conj_mem_Iw` (`10:280`, quoted: "**`w` normalises the disc-`0` part of `Iw_p`**: for `g ∈ Iw_p` with `p ∣ b`, both `wQ g wQ⁻¹` and `wQ⁻¹ g wQ` (each equal to `(d, −c; −b, a)`) lie in `Iw_p` with `p ∣ b`"), `wQH_conj_mem_Iw` (`11:325`), `coe_wGL_inv` (`18:84`), `coe_wGLH_inv` (`20:69`), Q8 (`tamePart_conj_ιpD`).
  - Lean ↔ source: `θ(w u w⁻¹) = wQ · θu · wQinv ∈ Iw_p` and `tamePart(w u w⁻¹) = tamePart u ∈ Kt`; the second conjugate with `g := (wGL p)⁻¹`.
  - Attacks: [2] `u = 1` ✓. [3] the field `w_conj_mem_U` (`18:163–166`) has exactly this shape (both conjugates, hypothesis `‖(θG u) 0 1‖ ≤ p⁻¹`) ✓ no drift; at level `h` the bound is `p⁻¹^h` (`20:160–162`) ✓.  SURVIVED.
- **Q11** (leaf, project): `pUnit` (`:216`), `thetaInt_unitsIncl_pUnit` (`:219`), `unitsIncl_pUnit_comm` (`:223`), `tameScalar` (`:228`), `thetaInt_tameScalar` (`:230`), `tameScalar_comm` (`:233`).
  - Discharged by: `unitsIncl = Units.map includeLeftRingHom` (`03:53`), `Algebra.TensorProduct.includeLeft_apply`, `toLocal_tmul`, `Algebra.smul_def`/`algebraMap` in `D ⊗ K_p`, `E` is `ℚ`-linear; `Algebra.commutes` (the image of `algebraMap ℚ` is central); Q6.
  - Attacks: [4] the instance trap again: `algebraMap ℚ D p ⊗ 1 = p • (1 ⊗ 1)` uses `Algebra.TensorProduct`'s `algebraMap`; keep the scalar as `((p : ℕ) : _)` where possible. [2] `x = 1` ✓.  SURVIVED.
- **Q12** (leaf, project): `central_pow_of_tameScalar_pow_mem` (`:238`).
  - Lean ↔ source: `γ := (unitsIncl pUnit)^N ∈ globalUnits` (a subgroup, `MonoidHom.range`), `u := tameScalar^N`; `ιp(pGL)^N = (unitsIncl pUnit · tameScalar)^N = γ · u` by `mul_pow` of commuting elements (`Commute.mul_pow`); `u ∈ levelOf`: `θ u = 1` (`thetaInt_tameScalar`, `map_pow`) and `tamePart u = u ∈ Kt` (`mem_levelOf_of_thetaInt_eq_one`); `γ` central: powers of a central element.
  - Attacks: [1] the field asks `∃ N, 0 < N ∧ …` and the input gives `∃ N, 0 < N ∧ tameScalar^N ∈ Kt` ✓ same `N`. [4] matches the new field `central_pow` (`18:157–159`) verbatim with `Γ = globalUnits`, `U = levelOf` ✓.  SURVIVED.
- **Q13** (leaf, project): `norm_det_mul_inv_normClass` (`:294`), `normClass_level` (`:299`).
  - Discharged by: `norm_det_thetaInt`, `norm_mul`, `norm_inv`, `Units.ne_zero`; for the level: `u = ιp(θGL u) · tamePart u` (Q7), `map_mul`, `normClass_ιpD` at `θGL u` with `‖det θ u‖ = 1` (`Iw`), `Padic.norm_eq_zpow_neg_valuation` ⇒ valuation `0` ⇒ `p^0 = 1`; `normClass_tame` at `tamePart u ∈ Kt`.
  - Attacks: [1] `Padic.valuation` of a unit is `0`: from `‖x‖ = p^{−v}` and `‖x‖ = 1` (`zpow` injective in the exponent, `p > 1`) ✓. [3] uses `Kt_le`? No: `tamePart u ∈ Kt` is the level condition ✓.  SURVIVED.
- **Q14** (leaf, project): `normClass_ιpD_vGL` (`:302`), `_wGL` (`:306`), `_wGLH` (`:309`), `_pGL` (`:313`).
  - Discharged by: `normClass_ιpD`, `coe_vGL`, `det_vQ` (`10:78`: `= p`), `det_wQ` (`05`), `det_wQH` (`11:88`: `= p^(h+1)`), `Matrix.det_smul` for `pGL`, `Padic.valuation_p`, `Padic.valuation_pow`? (`valuation (p^k) = k` via `Padic.valuation_p_pow` or `norm_eq_zpow_neg_valuation`), `zpow_natCast`.
  - Attacks: [3] the earlier `hc : ‖c‖ ≤ 1` in `normClass_ιpD_vGL` was unused (`det (vGL c) = p` for every `c`) — **removed from the skeleton 2026-09-14** ✓. [5] `Padic.valuation_p : valuation (p : ℚ_[p]) = 1` ✓ exists.  SURVIVED.
- **Q15** (leaf, project): `heckeChar` (`:327`: the unit proof, `map_one'`, `map_mul'`).
  - Source: `lwx.txt:1783` ("a central Hecke character associated to `ψ`"); the nebentypus API `nebCharK_psi_mul` (`17:348`), `nebCharK_psi_ne_zero` (`17:364`), `nebCharK_psi_of_norm_sub_one_le_sq` (`17:376`), `norm_natCast_p ψ hψ`.
  - Lean ↔ source: unit: `nebCharK_psi_ne_zero` at the norm-one element (Q13); one: `det θ 1 · q(1)⁻¹ = 1`, `nebCharK (ψ 1) = 1` (`…of_norm_sub_one_le_sq` at `x = 1`); mul: `det θ(gh) q(gh)⁻¹ = (det θ g q(g)⁻¹)(det θ h q(h)⁻¹)` (commutative), `nebCharK_psi_mul` on the two norm-one factors.
  - Attacks: [1] `nebCharK` is a character only on norm-one arguments (`17` docstrings: "multiplicative … trivial on `1 + p²ℤ_p`"); every argument here has norm one by Q13 ✓. [2] `g = 1` ✓. [4] `χ_U`'s right-hand side `nebK (ψ (θG u).det)` (`18:161`) is met verbatim by `heckeChar_level` ✓.  SURVIVED.
- **Q16** (leaf, project): `heckeChar_global` (`:343`), `heckeChar_level` (`:349`), `heckeChar_ιpD_vGL` (`:355`), `heckeChar_ιpD_wGL` (`:360`).
  - Discharged by: `normClass_global` (⇒ argument `1`), `normClass_level` (⇒ `q u = 1`, `inv_one`, `mul_one`), Q14 with `det_vQ`, `det_wQ` (⇒ argument `p · p⁻¹ = 1`, `p² · (p²)⁻¹ = 1`), `nebCharK_psi_of_norm_sub_one_le_sq` at `1`; `Units.ext`.
  - Attacks: [1] `heckeChar_global` uses `normClass_global` **in `ℚ_p`** (`(q γ : ℚ_p) = det θ γ`), so `det θ γ · (q γ)⁻¹ = 1` needs `q γ ≠ 0` (a unit) ✓. [4] the fields `χ_Γ`, `χ_U`, `χ_vGL`, `χ_wGL` of `AtkinLehnerFamily` (`22:65–69`) are matched verbatim ✓.  SURVIVED.
- **Q17–Q18** (leaves, project): `heckeCharH` (`:366`) and `heckeCharH_global/level/ιpD_vGL/ιpD_wGLH` (`:375–391`): as Q15–Q16 with `nebCharKH_psi_mul` (`19_NebCharH:413`), `nebCharKH_psi_of_norm_sub_one_le_pow` (`:442`), `sum`… not needed; `det_wQH = p^{h+1}`, `normClass_ιpD_wGLH`.  Attacks: [4] `χ_wGLH` field (`22:128`) matched ✓; `hh : 0 < h` threads through the `H` API ✓.  SURVIVED.
- **Q19** (leaf, project): `atkinLehnerFamily` (`:407`) — after SWAP delete `central := sorry`; every other field is discharged by name (`thetaInt_ιpD`, `ιpD_mem_levelOf`, `ιpD_pGL_comm`, Q12, Q10, Q15–Q16); `atkinLehnerFamilyH` (`:425`) by Q10, Q17–Q18.
  - Attacks: [5] the skeleton already elaborates these definitions with the field types (2026-09-14 build), so the field/lemma shapes match ✓; the only sorry is `central`.  SURVIVED.
- **Q20** (leaf, project): `vRepQ_mem_levelM1` (`:444`), `bijOn_vRepQ` (`:472`), `injective_vRepQ` (`:479`), `finite_image_upEltQ` (`:482`).
  - Source: [LWX, §2.5] (`lwx.txt:706–711`) through L1–L2; the JacobsSlash precedent `bijOn_etaRep` (`JacobsSlash/U3/3_EtaDecomposition.lean:486`) for the shape of the `Set.BijOn` statement.
  - Lean ↔ source: `MapsTo`: `v_c = η · ιp((p 0;0 1)⁻¹ (p 0; cp 1)) = η · ιp(1 0; c 1)` with `(1 0; c 1) ∈ Iw_p` (`ℓQ_mem_Iw`-type; `10:227`), so `v_c ∈ {η}·U`; `SurjOn`: for `η u`, write `u = ιp(θGL u) · tamePart u` (Q7), `vQ 0 · θu = k' v_c` (L1), so `η u = ιp(k') · tamePart u · v_c` with `ιp(k')·tamePart u ∈ U` (Q9, Q8) — same right coset (`QuotientGroup.rightRel_apply`); `InjOn`: `U v_b = U v_c ⇒ v_b v_c⁻¹ ∈ U ⇒ vQ b (vQ c)⁻¹ ∈ Iw` (`thetaInt_ιpD`, `map_inv`) ⇒ `b = c` (L2 at `k := vQ b (vQ c)⁻¹`, `h : vQ b = k vQ c`).  `injective_vRepQ`: `ιpD_injective` and `vGL p b = vGL p c ⇒ b = c` (entry `(1,0)`: `b p = c p`, `Nat.cast` injective).  `finite_image_upEltQ`: `Set.BijOn.image_eq` + `Set.finite_range`.
  - Attacks: [1] `η u ∈ U v_c` needs `tamePart u` to commute past `ιp(v_c)` — Q5 ✓. [2] `c = 0` ✓. [3] `Kt_le` is not needed ✓. [4] `RightCosets U` is the quotient by `QuotientGroup.rightRel` (`12`'s statements use the same spelling) ✓.  SURVIVED.
- **Q21** (leaf, project): `exists_factorisation` (`:490`) and the chosen data `idx`, `dElt`, `uElt` (`:496–502`, `Classical.choose`), `dElt_mem`, `c_mul_vRepQ_inv` (`:505–508`, `choose_spec`).
  - Source: [LWX, Prop 3.1] `lwx.txt:1075`: "Write each `γ_i v_j⁻¹` uniquely as `δ⁻¹_{i,j} γ_{λ_{i,j}} u_{i,j}` with `δ_{i,j} ∈ D^×`, `λ_{i,j} ∈ {0, …, t−1}`, and `u_{i,j} ∈ K^pIw_q`."
  - Lean ↔ source: `X.hc.2` (surjectivity onto the double-coset quotient) at `Quotient.mk'' (c_i v_t⁻¹)` gives `j` with `mk'' (c j) = mk'' (c_i v_t⁻¹)`; `DoubleCoset.rel_iff` (as at `18:970–971`: `obtain ⟨γ, hγ, v, hv, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)`) yields `d ∈ Γ`, `u ∈ U` with `c_i v_t⁻¹ = d c_j u`.  Uniqueness (the source's "uniquely") is not needed: the data are *chosen*.
  - Attacks: [3] `hstab` (neatness) is not used here ✓ (it enters through `discEvalAtRepsCl`). [2] `t` arbitrary ✓.  SURVIVED.
- **Q22** (leaf, project): `hshape` (`:513`) — `isUpShape_certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D) X.uElt (hη := vRepQ_mem_levelM1 p D 0) (hηa : ‖θ η 0 0‖ ≤ p⁻¹) X.bijOn_vRepQ i t` with `θ η = vQ 0 = (p 0; 0 1)`, `‖p‖ = p⁻¹` (`Padic.norm_p`).
  - Attacks: [4] `isUpShape_certM1`'s `hv` is stated for `η` and `vRep` (`05_Certificates.lean:169–174`); `upEltQ = vRepQ 0` definitionally (`vGL p (0 : ℕ)` vs `vGL p 0`: `Nat.cast_zero` — may need `show`) ✓ noted.  SURVIVED.
- **Q23** (leaf, project — decision 2): `det_certM1_eq` (`:521`).
  - Source: [LWX, Prop 3.1] `lwx.txt:1084`: "Substitute back in `u_{i,j}v_j = γ⁻¹_{λ_{i,j}} δ_{i,j} γ_i` and note the fact that both `γ_i` and `γ_{λ_{i,j}}` have trivial `p`-component"; the normalisation of `plan.md` (decision 2).
  - Lean ↔ source: apply `thetaIntGL` to `c_mul_vRepQ_inv`: `θGL(c_i) θGL(v_t)⁻¹ = θGL(d) θGL(c_j) θGL(u)` with `θGL(c_i) = θGL(c_j) = 1` (`c_thetaInt`, `Units.ext`), so `θGL(u) θGL(v_t) = θGL(d)⁻¹` and `det θ(u v_t) = (det θ d)⁻¹`; apply `normClass`: `q(c_i) q(v_t)⁻¹ = q(d) q(c_j) q(u)` with `q(c) = 1` (`c_normClass`), `q(u) = 1` (Q13), `q(v_t) = p` (Q14) ⇒ `q(d) = p⁻¹` in `ℚˣ`; `normClass_global` (`dElt_mem`) ⇒ `det θ d = (p⁻¹ : ℚ_p)`; hence `det(certM1 i t) = det θ(u · v_t) = p` (`coe_certM1`, `10:63`; `Matrix.det_mul`).
  - Attacks: [1] children/parent: the cast `((p⁻¹ : ℚ) : ℚ_p) = (p : ℚ_p)⁻¹` (`Rat.cast_inv`, `Rat.cast_natCast`) and `inv_inv` ✓. [2] `t = 0` ✓ (`vQ 0` has determinant `p` too). [3] `c_normClass` **and** `c_thetaInt` are both used — the "normalised representatives" hypothesis is exactly what the source's `γ_{i,p} = 1` plus unit norms give; without `c_normClass`, `q(d) = p⁻¹·q(c_j)/q(c_i)` and `det = p · q(c_i)/q(c_j)` — a unit multiple of `p`, the general case discussed in `plan.md`. [4] the conclusion is exactly `hdet` of `15_StepThree.lean:209` ✓ no statement change downstream.  SURVIVED.
- **Q24** (leaf, project): `upDatum` (`:527`) — a `def`; nothing to prove.  Its `hshape` argument is Q22.

### API gaps recorded as inputs (fields of `QuaternionInput`; not ticketed)

- **AG-nrd** — the reduced norm on `D ⊗ 𝔸_f` and the norm class `q = ∏_ℓ ℓ^{v_ℓ(nrd)}`; mathlib has no reduced norm on a central simple algebra (grep `reducedNorm` 2026-09-14: 0 files), the FLT fork none.  The four fields `normClass_global`, `norm_det_thetaInt`, `normClass_ιpD`, `normClass_tame` are the properties such a norm provides (Voight, *Quaternion Algebras*, §3.3, §7.7 for `nrd` and its behaviour under base change and at split places).
- **AG-HSM** — normalised representatives (`c_thetaInt`, `c_normClass`): existence from Hasse–Schilling–Maass (`nrd(D^×) = ℚ_{>0}`, Voight Thm 14.7.4) to fix the norms away from `p`, and weak approximation for `D^1` at `p` (Voight §28.5; elements of norm `p^n` are dense in `{det = p^n}`) to restore `γ_{i,p} = 1`; see `plan.md`, decision 2.
- **AG-neat** — `hstab` ([LWX, Hypothesis 2.10]).
- **AG-compact** — `tameScalar_pow_mem`: for an open `Kt`, the tame scalar generates a relatively compact subgroup of the tame unit idèles, so some power lies in `Kt`; provable with the fork's topology on `Dfx` (`IsCompact.tendsto_subseq` or finite index of an open subgroup of a compact group) — recorded as an optional follow-up (ticket `Q-OPT`), not needed for any milestone.

## 5. Part M — the milestones for `D/ℚ` (`25_QuaternionSlopes.lean`)

- **M1** `hasUnitBand` (`25:38`): `hasUnitBand_of_atkinLehnerFamily (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape hp2 hψ hζ ω n` — the arguments `hfin`, `hv`, `hvinj`, `hfact` are stated for `vRepF … (X.atkinLehnerFamily …)`, which is `vRepQ p D` by `rfl` (`vRepF_atkinLehnerFamily`), so `exact` closes it up to defeq; `X.upDatum` unfolds to the `UpDatum.ofCerts` of the statement.
- **M2** `degX_succ` (`:43`), `degXint_eq` (`:50`): `degX_succ_of_atkinLehnerFamily`, `degXint_of_atkinLehnerFamily` with the same arguments plus `X.det_certM1_eq`.
- **M3** `degXint_pos` (`:58`): `degXint_pos_of_atkinLehnerFamily …`.
- **M4** `degX_succ_add_period` (`:64`), `degXint_add_period` (`:70`): `degX_succ_add_period`, `degXint_add_period` of `24_DegreePeriodicity.lean`.
- **M5** `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (`:78`): `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily … (hζ₁ := hζ) ω h0 h1 hT hκ j`.
- **M6** `slopeRatio_add_period` (`:91`): `slopeRatio_add_period … (X.atkinLehnerFamilyH ψ hp2 hψ hζ h hh hζh) X.det_certM1_eq hp2 hψ hh hζ hζh hM ω j`.
- Attacks on the assembly: [1] each family theorem's `include` list (`hfin hv hvinj c hc hstab d hd hfact (hdet) (X)`) is matched by an explicit argument ✓ (orders recorded in `plan.md`). [2] the field `K` appears only in hypotheses; the conclusions are about `X.upDatum : UpDatum p ι` ✓. [3] `[Nonempty ι]`, `[IsAlgClosed K]` exactly as the family theorems require (`hasUnitBand` needs neither `IsAlgClosed` nor `hdet`) ✓. [4] the statements are the family theorems' conclusions with the datum substituted; `degXint_eq`'s second character is `ω * (teichChar p ^ (2 * n))⁻¹` as in `24:193–202` ✓.  SURVIVED.

## 6. Confidence gate

1. Every leaf is discharged from mathlib (Z1–Z2, Z5–Z9 …), from project code (the rest), or is an
   explicit input (AG-nrd, AG-HSM, AG-neat, AG-compact — fields of `QuaternionInput`, not leaves).
2. The skeleton compiles: `lake build PhD` exit 0 on 2026-09-14 (sorries only; the non-sorry warnings are
   five `unusedSectionVars` on `rfl` lemmas, for the cleanup tickets).
3. Every leaf above carries a source quote (or the project declaration it generalises, quoted) and a
   Lean ↔ source paragraph.
4. Every leaf and internal node carries an attack block; two attacks changed the skeleton
   (`roots_charpoly_smul` gained `μ ≠ 0`; `normClass_ιpD_vGL` lost `‖c‖ ≤ 1`) and one changed a
   sketch (`eq_ιpD_mul_tamePart` is not definitional).
5. Prior-B2 logs consulted: no match.
6. The tree mirrors the sources: [LWX, §2.4/2.5/2.11, Prop 3.1] for Part Q, the project's own
   double-coset proof for Part C (the source of the *generalisation*; the classical statement is
   Miyake 4.6.17, not used), mathlib's semisimple/eigenspace API for Part Z.  LOC estimates cite the
   corresponding source lengths.
7. Single-conclusion: the only `∧`-conclusions are `iotaV_mul_eq_zero_of_toLocal_eq_zero` (two
   symmetric equalities of one computation — kept as a documented two-sided bundle; its consumer uses
   both) and the normaliser lemmas `levelOf_wGL_conj`/`levelOf_wGLH_conj`, which transcribe the
   two-sided field `w_conj_mem_U` of the data verbatim (documented exception: the field is
   consumed as a bundle).

## 7. Ticket map (added 2026-09-14 when `tickets.md` was written)

Leaf labels above are the ticket IDs, with three adjustments: leaf **Q20** is split into tickets
**Q20a** (`vRepQ_mem_levelM1`, `injective_vRepQ`), **Q20b** (`bijOn_vRepQ`) and **Q20c**
(`finite_image_upEltQ`); the sub-leaf `inv_mem_Iw` of Q9 is ticket **L3** (`[NEW DECL]` in
`10_AtkinLehnerLocal.lean`); the sub-lemmas of Q2 (`unitAt_mul`) and Q4 (`singleₗ_mul`, `mul_singleₗ`,
`iotaV_mul_eq_iotaV_mul_toLocal`, `mul_iotaV_eq_iotaV_toLocal_mul`) are `[NEW DECL]`s inside those
tickets; AG-compact is the optional ticket **Q-OPT** (blocked, user decision).  Every one of the 121
`sorry`-blocks of the skeleton is the protected statement of exactly one ticket (checked by script).
