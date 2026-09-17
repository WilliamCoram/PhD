# Development Plan — `lwx-quaternion` (the Atkin–Lehner identity at every neat tame level, the determinant certificate from normalised representatives, and the adelic data for a definite quaternion algebra over `ℚ`)

**BOARD PATH: `.mathlib-quality/lwx-quaternion/`.**  The default `.mathlib-quality/` board belongs
to the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them.  Every `/beastmode` run
names this board path explicitly and deletes only this board's sentinels (cat before rm).

**STATUS: COMPLETE 2026-09-14** (`/beastmode`; all tickets done except the optional Q-OPT; `lake build PhD` green, 3929 jobs, sorry-free, standard axioms — see the execution record in `tickets.md`).

## Goal

Three targets, in one board because they share the data types `AtkinLehnerData` /
`AtkinLehnerFamily` (and their level-`h` twins) of `PhD/Main/LWX/`:

1. **Decision 1, option (b) — the tame central operator.**  The field `central` of the
   Atkin–Lehner data (`ιp(p·1) = γ·u`, `γ ∈ Γ` central, `u ∈ U`, `θ u = 1`: "the tame scalar
   `p^{(p)}` lies in the level") is replaced by the two weaker fields
   `ιp_pGL_comm : ∀ x, ιp (pGL p) * x = x * ιp (pGL p)` and
   `central_pow : ∃ N, 0 < N ∧ ∃ γ ∈ Γ, ∃ u ∈ U, ιp (pGL p) ^ N = γ * u ∧ θG u = 1 ∧ ∀ x, γ * x = x * γ`,
   both true for **every** open tame level of a definite quaternion algebra.  The operator
   identity becomes `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z` with `Z = translateOp (ιp (p·1))`
   (`(Zφ)(x) = φ(x·ιp(p·1)⁻¹)`), a finite-order operator commuting with `U_p`; hypothesis H1
   (`AtkinLehnerHypothesis`) becomes `A B = p^{k+1}·Z`, `Z A = A Z`, `Z^N = 1`, plus the
   conjugation `A' = P B Q`; and the abstract pairing becomes the **norm-multiset** identity
   `‖roots(charpoly A')‖ = ‖c‖ / ‖roots(charpoly A)‖`, which is all the slope, gap, degree and
   reflection arguments ever used.  This is the classical Atkin–Li form
   `a_p(f)·a_p(f|W) = χ_M(p)·p^{k+1}` (Miyake, Thm 4.6.17; `bu04.txt:1122–1124`) — `Z`'s
   eigenvalues are the values `χ_M(p)` of the tame central characters — and it covers every
   neat tame level, as [LWX] assume (Hypothesis 2.10, `lwx.txt:838`).
2. **Decision 2, the canonical fix — `det = p` from normalised representatives.**  With class
   representatives `cᵢ` of trivial `p`-component and unit reduced norm away from `p`
   ([LWX, §2.11]'s "we may and will take each `γᵢ` so that its `p`-component is just 1",
   `lwx.txt:845–847`, sharpened by unit norms), the factorisation `cᵢ v_t⁻¹ = d·c_j·u` of
   [LWX, Prop 3.1] forces `nrd(d) = p⁻¹` exactly, hence `det(u_{i,t} v_t) = p` on the nose
   (`QuaternionInput.det_certM1_eq`).  **No statement changes**: `hdet` stays the hypothesis of
   `StepThree.lean`; the instantiation discharges it.  The *existence* of normalised
   representatives is Hasse–Schilling–Maass (surjectivity of `nrd : D^× → ℚ_{>0}`) plus weak
   approximation for the norm-one group at `p` (Voight, *Quaternion Algebras*, Thm 14.7.4 and
   §28.5); neither is in mathlib or the FLT fork, so the normalised representatives are carried
   as **input** (`QuaternionInput.c`, `c_thetaInt`, `c_normClass`), exactly as `c`/`hc` are
   carried today.
3. **The instantiation for `D/ℚ`.**  For a definite quaternion algebra `D` over `ℚ` split at
   `p` (`[RigidificationAt ℚ D (padicPlace p)]`, `Dfx ℚ D`, `thetaInt`, as in
   `08_Quaternionic.lean`), granted an **arithmetic input** `QuaternionInput p D ι`
   (a tame level `Kt` of trivial `p`-component containing a power of the tame scalar, the
   norm class `q : Dfx ℚ D →* ℚˣ` with its four compatibilities, and neat normalised class
   representatives), **everything else is proved**: the section `ιp` (`unitAt`), its
   centrality properties, the tame part and the level `U = Kt·Iw_p` with `ιp(Iw_p) ⊆ U` and
   the `w`-normaliser property at every level `h`, `central_pow`, the Hecke characters
   `χ = ψ_neb ∘ (det θ_p / q)` at every `(ω, k)` and every conductor `p^{h+1}`, the coset
   decomposition `U η U = ∐ U v_c` from the local Iwahori decomposition, the factorisation
   data `(idx, d, u)`, the shape and determinant certificates, hence the families
   `AtkinLehnerFamily` / `AtkinLehnerFamilyH` and the `U_p`-datum `QuaternionInput.upDatum`.
   The milestones read every headline theorem of boards `lwx-conductor` and `lwx-degrees` off
   this datum: `hasUnitBand`, `degX_succ`, `degXint_pos` (Thm 1.3), `degX_succ_add_period`
   (Cor 1.4), `slopeRatio_add_period` (Thm 1.5 second half) and (1.5.1) for the genuine `U_p`.

**Out of scope** (recorded, not ticketed): the reduced norm on a central simple algebra
(mathlib has none; `q` and its axioms are the interface it would discharge); Hasse–Schilling–Maass
and weak approximation (existence of normalised representatives); neatness of a chosen level;
`p = 2`; the rigid-analytic packaging.

## References

| Locator | Content used |
|---|---|
| `lwx.txt:667–673` (`.mathlib-quality/lwx-seam-m/references/lwx.txt`) | §2.4: `K^p` an arbitrary open compact tame level; (Neat); full level `l ≥ 3` is neat |
| `lwx.txt:706–716` | §2.5: `Iw_q (p 0;0 1) Iw_q = ∐_{j<p} Iw_q v_j`, `v_j = (p 0; jq 1)`, `U_p(ϕ) = ∑ ϕ‖v_j` |
| `lwx.txt:838–840`, `903–910` | Hypothesis 2.10 (neat), Remark 2.14 (reduction to neat) |
| `lwx.txt:843–847` | §2.11: double cosets `∐ D^×γ_iK^pIw_q`, (Neat) ⇒ bijectivity, `γ_{i,p} = 1` |
| `lwx.txt:1038–1092` | Prop 3.1: `γ_i v_j⁻¹ = δ_{i,j}⁻¹ γ_λ u_{i,j}`, certificates `u_{i,j,p}v_j`, shape (3) |
| `lwx.txt:1775–1786` | Prop 3.22's proof: the central Hecke character twist (the `χ_M(p)` phenomenon) |
| `bu04.txt:631–650` | Buzzard's `(f|η)(g) = f(gη⁻¹)η_p`, `L(U,A)`, `[UηU]f = ∑ f|η_i` |
| `bu04.txt:1116–1124` | Miyake Thm 4.6.17 cited for the classical Atkin–Lehner eigenvalue relation |
| Miyake, *Modular Forms*, Thm 4.6.17 | `a_p(f)·a_p(f|W_{p^ν}) = χ_M(p)·p^{k−1}` (weight-`k` normalisation) — the general form of the identity |
| Voight, *Quaternion Algebras*, Thm 14.7.4; §28.5 | Hasse–Schilling–Maass; strong/weak approximation — the inputs behind the normalised representatives (hypotheses here) |
| mathlib `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`, `Module.End.IsSemisimple.iSup_eigenspace_eq_top`, `Module.End.mapsTo_genEigenspace_of_comm`, `LinearMap.charpoly_prodMap`, `LinearEquiv.charpoly_conj`, `Submodule.prodEquivOfIsCompl`, `Polynomial.separable_X_pow_sub_C`, `Polynomial.roots_comp_C_mul_X_add_C`, `Matrix.charpoly_toLin'` | the eigenspace decomposition behind the norm-multiset pairing |
| project `PhD/Main/QMF/04_UpiElement.lean` (`unitAt`, `toMatrix_unitAt`, `toLocal_unitAt_ne`, `iotaV_mul`, `one_add_iotaV_mul`) | the section `ιp` and the tame commutation |
| project `10_AtkinLehnerLocal.lean` (`wQ_conj_mem_Iw`), `11_AtkinLehnerLocalH.lean` (`wQH_conj_mem_Iw`) | the normaliser property of the constructed level |
| project `17_NebChar.lean` (`nebCharK_psi_mul`, `_ne_zero`, `_of_norm_sub_one_le_sq`), `19_NebCharH.lean` | the Hecke character is a character |

## Mathlib inventory

| Concept | Status | Action |
|---|---|---|
| eigenspace decomposition of a semisimple endomorphism | `Module.End.IsSemisimple.iSup_eigenspace_eq_top` (alg. closed, fin. dim.) | USE |
| `Z^N = 1 ⇒ Z` semisimple | `isSemisimple_of_squarefree_aeval_eq_zero` + `separable_X_pow_sub_C` (needs `(N : K) ≠ 0`: `CharZero K`) | USE |
| commuting map preserves eigenspaces | `Module.End.mapsTo_genEigenspace_of_comm` (`eigenspace = genEigenspace _ 1`, `eigenspace_def`) | USE |
| charpoly of a map preserving `V = V₁ ⊕ V₂` | `LinearMap.charpoly_prodMap` + `LinearEquiv.charpoly_conj` + `Submodule.prodEquivOfIsCompl` (pattern of `Mathlib/LinearAlgebra/Eigenspace/Zero.lean:160–182`) | USE (one split per induction step) |
| charpoly of `μ • A` | absent | DEFINE `Matrix.roots_charpolyRev_smul` via `Polynomial.roots_comp_C_mul_X_add_C` + `RingHom.map_det` |
| norm-multiset pairing for `A B = c Z` | absent | DEFINE (`02_CharpolyPairingZ.lean`) |
| reduced norm of a quaternion/central simple algebra | absent (mathlib, FLT fork) | INPUT field `normClass` with axioms; recorded gap |
| single-place adelic units | project `unitAt` | USE |
| Iwahori decomposition `Iw η Iw = ∐ Iw v_c` | absent (JacobsSlash has the `U₃` case only) | DEFINE (`10_AtkinLehnerLocal.lean`) |
| class-set finiteness | `QMF.finite_classSet`, `finite_image_etaAdelic'_of_isOpen_of_isCompact` | not needed (representatives are input; `hfin` from the coset bijection) |

## File structure

New:
- `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean` — the abstract pairing up to a finite-order
  operator (norms of roots).
- `PhD/Main/LWX/23_QuaternionData.lean` — `ιpD`, tame part, `levelOf`, tame scalar, the input
  structure `QuaternionInput`, the Hecke characters, the families, the certificates, `upDatum`.
- `PhD/Main/LWX/25_QuaternionSlopes.lean` — the milestones for `D/ℚ`.

Modified (additive in the skeleton; the SWAP tickets delete the superseded declarations):
- `05_AtkinLehner.lean` (Z-reduction), `10_AtkinLehnerLocal.lean` (Iwahori decomposition),
  `10_DiscForms.lean` (`translateOp`), `13_AtkinLehnerInst.lean` (`AtkinLehnerHypothesisZ`),
  `14_Touching.lean` (determinant lemmas with `Z`), `18_AtkinLehnerMap.lean` /
  `20_AtkinLehnerMapH.lean` (new fields, `centralOp` / `centralOpH`),
  `19_AtkinLehnerIdentity.lean` / `21_AtkinLehnerIdentityH.lean` (the identity with `Z`),
  `22_AtkinLehnerFamily.lean` (fields, transports).
- Repairs after the swap (statements textually unchanged): `14_Touching`, `15_TouchingH`,
  `15_StepThree`, `17_DegreeFormula`, `23_ConductorSlopes`.

## Dependency graph

```
Part Z  (02_CharpolyPairingZ) ─┬─► 05 norm_roots_charpoly_atkinLehnerZ ─► 13 AtkinLehnerHypothesisZ ─► SWAP
                               └─► 14 det lemmas with Z                                              │
Part C  (10_DiscForms translateOp) ─► 18/20 centralOp(H) ─► 19/21 identity with Z ─► 19/21 H1(Z) ─┘
                                                                                                    ▼
                                                            Part R: repairs of 14/15/15H/17/23 (in dependency order)
Part Q  (23_QuaternionData: ιpD, tamePart, levelOf, tameScalar, input, heckeChar, families, certificates, upDatum)
        needs Part C's fields and the SWAP (for `atkinLehnerFamily`) and 10_AtkinLehnerLocal's Iwahori decomposition
Part M  (25_QuaternionSlopes) needs Part Q + Part R
```

## Generality decisions

1. `Z` is *not* assumed to be scalar or diagonalisable in the data; finite order (`central_pow`)
   is what every open tame level provides, and semisimplicity is derived (`CharZero K`).
2. The abstract pairing is stated for `[NormedField K] [IsAlgClosed K] [CharZero K]` and any
   `Fintype n`, in `namespace Matrix`, mirroring `01_CharpolyPairing.lean`; the conclusion is the
   multiset of **norms** — the exact multiset identity is false with `Z ≠ 1` and was never used
   beyond norms (audit: `14_Touching` uses determinants, `15_StepThree` and `23_ConductorSlopes`
   use `norm_roots_charpoly_atkinLehner` and root counts by norm; the reflection lemma
   `toReal_unitSlope_charpolyRev_reflect` takes the exact form only for convenience and is
   restated in the norm form).
3. `translateOp` is generic (any `z : G`, any level `h`); centrality hypotheses are supplied
   per lemma, so the same operator serves levels `1` and `h`.
4. The level `U = Kt·Iw_p` is **constructed** from a tame level `Kt ≤ {θ = 1}`; its
   `p`-component is exactly `Iw_p` by construction, which is what the normaliser property and
   the coset decomposition need.  A general open compact `U` with `θ(U) ⊆ M₁` would not have
   `ιp(Iw_p) ⊆ U`.
5. The Hecke character is built from the norm class `q` alone; no idèles, no valuations on the
   adele ring, no topology: `χ(g) = ψ_neb(det θ_p(g)·q(g)⁻¹)`, a unit by `norm_det_thetaInt`, a
   character by `nebCharK_psi_mul`, trivial on `D^×` by `normClass_global` (the product formula
   for a positive rational), equal to `ψ_neb ∘ det ∘ θ` on the level by `normClass_tame` and
   `theta_mem_Iw`, and `1` at `v_c`, `w`, `w_h` by `normClass_ιpD`.
6. The class representatives and the factorisation are handled as in `12_QuaternionicH`: the
   representatives are input; `idx`, `d`, `u` are **chosen** from the class-set bijection
   (`Classical.choose`), so `hfact` is a theorem.
7. Neatness (`hstab`) is input: it is a property of the chosen `Kt` ([LWX, Hypothesis 2.10]).

## Engineering notes (for the worker)

- Argument orders: `certM1 θ U hU vRep hvΔ u i t`; `UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape`;
  `discHeckeOperatorCl θG ψ U hU k κ hκ hη hfin`; `discHeckeOperatorClH θG ψ U hU h k κ hκ hη hfin`;
  `ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ`; `DiscForms (Γ := Γ) θ h ψ κ U hU`;
  `discHeckeOperator θ h ψ κ U hU hη hfin`; `unitAt F D v m`; `nebCharK ψ ω k ζ`,
  `nebCharK_psi_mul ψ ω k ζ hp2 hψ hζ hpK hx hy`; `nebCharKH h ψ ω k ζh`;
  `hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hp2 hψ hζ ω n`;
  `degXint_pos_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω n`.
- `AutomorphicFunction` is a structure `⟨toFun, left_invt⟩` with a `FunLike` coercion;
  `AutomorphicFunction.left_invt' φ hγ`, `AutomorphicFunction.ext`.
- In `Module.End`, `f ^ N` and `1` are available for `M →ₗ[K] M`; `LinearMap.pow_apply`.
- `Matrix.charpoly_toLin' A : (toLin' A).charpoly = A.charpoly`; `Matrix.toLin'_mul`.
- The MonoidHom-product trap of `lwx-conductor` (prove character identities pointwise) applies
  to `heckeChar` too.
- `omega` not `lia`; no `timeout`; `lake exe runLinter PhD.Main.LWX.«NN_Name»` and
  `#lint in` are the cleanup gates; French quotes in every module name.
- Build: `lake build PhD.Main.LWX.«25_QuaternionSlopes»` (pulls everything), and
  `lake build PhD` at the gates.

**2026-09-14, later**: `decomposition.md` (adversarial pass) and `tickets.md` (112 tickets: 72 proof/def/check,
11 swap/repair, 29 cleanup) written; awaiting the user's approval before `/beastmode`.
