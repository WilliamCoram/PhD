# Plan — jacobs-explog (refactor JacobsSlash onto the general `LWX.PadicExpLog`)

**Origin**: ticket [FUTURE-JacobsExpLog] on the (completed) `lwx-halo` board.
Its precondition — F2/F3/H5 landed — is satisfied (lwx-halo BOARD COMPLETE
2026-09-04). This board executes it.

## Goal

`PhD/LWX/PadicExpLog.lean` (namespace `LWX.PadicExpLog`) is the `p`-generic port
of the `p = 3` exp/log development in `PhD/JacobsSlash/1_PadicAnalytic.lean`
(same lemma names; created by lwx-halo B3). Delete the duplicated
§§ResidueChar/NatAux/LogExp of 1_PadicAnalytic.lean and make JacobsSlash consume
the general file at `p := 3`, keeping only the `p = 3`-specific
§§UnitPow/Binomial (rebased on the imported general lemmas). Pure deduplication:
no statement changes on the JacobsSlash side beyond namespace/instantiation.

## Verified facts (2026-09-04 recon)

1. **No import cycle**: `PhD/LWX/PadicExpLog.lean` imports only Mathlib.
2. **Defs are p-free**: `LWX.PadicExpLog.padicLog/padicExp` do not mention `p`
   in their bodies (only the norm/summability lemmas do), so
   `export LWX.PadicExpLog (padicLog padicExp …)` gives JacobsSlash the *same*
   declarations — downstream `rw [padicLog]`-style unfolds keep working, and the
   `@[simp]` attributes on `padicLog_one`/`padicExp_zero` carry over (same decl,
   imported).
3. **Cast seam is rfl**: general lemmas are stated with `‖((p : ℕ) : K)‖`;
   at `p := 3` that is `((3 : ℕ) : K)`, and `Nat.cast_ofNat : ((3:ℕ):K) = (3:K)`
   is `rfl` in mathlib — so old-style `h3 : ‖(3 : K)‖ < 1` terms should be
   accepted by defeq. If elaboration balks anywhere, bridge with
   `show` / `Nat.cast_ofNat ▸` in the shim, never at downstream call sites.
4. **`Fact (Nat.Prime 3)`**: `Nat.fact_prime_three` is a mathlib instance
   (Mathlib/Data/Nat/Prime/Defs.lean) — no local instance needed.
   `hp2` obligations discharge with `(by norm_num : (3:ℕ) ≠ 2)`.
5. **CharZero is NOT a new constraint**: 1_PadicAnalytic.lean *already* has
   `[CharZero K]` in its variable block (line 44), as do 2_U3Data and
   3_BinomialTheorem. The general file's `[CharZero K]` changes nothing.
6. **Downstream footprint** (grep census, everything else is internal):
   - direct importers of 1_PadicAnalytic: `2_U3Data.lean`, `U3/1_Setting.lean`
     (LegacyCode also imports its own copies — NEVER touch `PhD/LegacyCode/`).
   - old names referenced by surviving code (= §§UnitPow/Binomial of
     1_PadicAnalytic + all downstream JacobsSlash files):
     * export (p-free): `padicLog`, `padicExp`, `padicLog_one`, `padicExp_zero`,
       `norm_eq_one_of_norm_sub_one_lt_one`
     * shim with old signature (h3 : ‖(3:K)‖ < 1 explicit first arg, no hp2):
       `norm_natCast_eq_one_of_coprime`, `sq_norm_factorial_ge`,
       `norm_padicLog_le`, `norm_padicExp_sub_one_le`, `padicExp_add`,
       `norm_padicLog_eq`, `padicExp_padicLog`, `padicLog_mul`
     * re-add private (used by §§UnitPow/Binomial): `norm_three_pos`
     * `3_Slopes.lean` has its own private `norm_three_pos'` — leave alone.
   - unused publics → delete + renames.jsonl entry pointing at the LWX name:
     `norm_natCast_eq_pow_padicValNat`, `summable_padicLog_term`,
     `norm_padicExp_term_le`, `summable_padicExp_term`,
     `summable_norm_padicExp_term`, `norm_padicExp_sub_one_sub_self`,
     `norm_cube_sub_one` (→ `norm_pow_p_sub_one`), `norm_pow_three_pow_sub_one`,
     `padicExp_pow_three_pow`, `tendsto_padicLog`, `eq_of_padicLog_eq`,
     `padicLog_padicExp`.
7. **Divergences in the general file**: `norm_cube_sub_one` was generalised to
   `norm_pow_p_sub_one`; `padicExp_natCast_mul` is new (no old counterpart);
   `hp2 : p ≠ 2` threaded through most LogExp lemmas; sections carry
   `omit`-managed `[CharZero K]`.

## Shim design (decided)

In 1_PadicAnalytic.lean, after deleting §§ResidueChar/NatAux/LogExp:
`import PhD.LWX.PadicExpLog`; inside `namespace JacobsSlash` an
`export LWX.PadicExpLog (…)` for the five p-free decls, then eight one-line shim
theorems with the exact old signatures delegating to the general lemmas at
`(p := 3)`, discharging `hp2` via `by norm_num`. §§UnitPow/Binomial and all
downstream files then compile unchanged. Shims are legitimate API surface (the
JacobsSlash-side `p = 3` instantiation, cf. laweights' oneUnits pattern), not
dead weight; inlining them at call sites is NOT planned (keeps the diff minimal
and the seam in one file).

## Verification gates

- `lake build PhD.JacobsSlash.«1_PadicAnalytic»` green after R1.
- Full downstream tree green after R2 (2_U3Data, 3_*, 4_*, 5_*, U3/*, CN1/* —
  build the leaves listed in PROGRESS.md).
- `lake exe runLinter PhD.JacobsSlash.«1_PadicAnalytic»` clean (R3).
- No file under `PhD/LegacyCode/` or `PhD/PR'd/` touched.
- Every deleted/moved name recorded in this board's `renames.jsonl`.
