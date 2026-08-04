# test.lean inventory (2026-08-03, agent-generated; [T] = PhD/Test/test.lean, reference-only)

Sections: 5.4 @392–413 · 5.5 stub @414 (body @1175) · 5.6 @420–626 · 5.7 @627–1225 ·
5.8 @1226–1305 · 5.9 @1306–1350 · 5.10 @1351–1486 · 5.11 @1487–1920 · header @1921–1968 ·
radius infra @1969–2099 · 5.12–5.14 @2100–3553 (single header; 5.13 @2795, 5.14 @3271+3387).
File is sorry-free; 37 public + 13 private decls past line 700. test.lean does NOT compile
(imports moved to LegacyCode/bad); use as proof-route source only.

Public decls (line · name · blueprint):
735 isPureSeries_of_bounds 5.6 · 807 aeval_ne_zero_of_dominant_const 5.7 ·
845 aeval_ne_zero_of_dominant_lt 5.7 · 934 memDivisibleValueGroup_exp_slope [DELETE] ·
974 exists_memDivisibleValueGroup_between [DELETE] · 1051 exists_factorisation_of_firstBreak' 5.7 ·
1153 exists_factorisation_of_firstBreak 5.7 · 1175 isPureSeries_of_irreducible 5.5 ·
1237 coeff_mul_pow_le_of_lt_firstBreak 5.8 · 1258 gaussNorm_eq_one_of_lt_firstBreak 5.8 ·
1315 aeval_ne_zero_of_lt_firstBreak 5.9 · 1363 aeval_ne_zero_of_norm_lt_firstBreak 5.10a ·
1384 card_roots_firstBreak 5.10b · 1537 vertex_line_le 5.11 · 1601 vertex_line_lt 5.11 ·
1617 aeval_ne_zero_of_dominant_top 5.11 · 1670 card_roots_le_of_distinguished 5.11 ·
1730 card_roots_le_slope 5.11 · 1765 card_roots_lt_slope 5.11 · 1883 card_roots_slope 5.11 ·
1973 isRestricted_of_le infra · 1985 summable_of_isRestricted infra ·
2003 isRestricted_iff_summable infra · 2018 isRestricted_of_summable infra ·
2031 radiusOfConvergence (def) infra · 2038 le_radiusOfConvergence_of_summable infra ·
2051 summable_of_lt_radiusOfConvergence infra · 2065 isRestricted_of_lt_radiusOfConvergence infra ·
2085 le_radiusOfConvergence_of_isRestricted infra · 2145 isRestricted_of_lt_slope 5.12 ·
2217 not_isRestricted_of_slopes_le 5.12 · 2496 ofReal_exp_le_radiusOfConvergence 5.12 ·
2519 radiusOfConvergence_le_ofReal_exp 5.12 · 2551 memDivisibleValueGroup_exp_slope' [DELETE] ·
2795 exists_weierstrass_factorisation 5.13 · 3271 hasSum_zero_iff_aeval_eq_zero 5.14a ·
3387 norm_eq_exp_slope_of_hasSum_zero 5.14b.
Privates: 884, 1007, 1514, 1524, 2103, 2120, 2209, 2538, 2588, 2646, 2703, 2715, 3229.

Lines 1–733 (already-read base layer): addVal setup 79–125 (RankOne.addVal — replace with new
AddVal negLog bridge) · coeffVal 133 · slopeReal_real 142 · HasFirstBreak 153 (algorithm form —
replace with constructed-polygon slopes/lengths data) · findFirstFinite_zero 156 ·
newtonPolygon_zero_eq 176 · step_slope_le 184 [ALREADY PORTED: SpecConstruction.nextStep_slope_le]
· firstBreak_slope_le 207 [PORTED: Spec.unitSlope_zero_mul_le] · step inversions 221–270
[PORTED: Construction + SpecConstruction] · polynomial driving 272–388 (coeffVal_coe lemmas,
slopeSet finite, exists_nextStep_coe_eq_nextVertex, nextVertex_coe_data, anchor lemmas) ·
IsPure 402 [PORTED: NewtonPolygon₀.IsPure] · IsPureSeries 411 · 5.6 isPureSeries_iff_distinguished
476 (proved) · term_* privates 435–452, 661–684 · distinguished_of_firstBreak 689 (5.7 core).

Old-API usage hotspots: newtonPolygon/nextStep throughout 5.7 and 5.11 and 2100–EOF (~110 hits);
addVals2's addVal ONLY in 2100–EOF (23 hits); gaussNorm in 5.7/5.8 and 2703–3342;
WPrep in 5.7/5.11/5.13; AlgebraicClosure only 1155–1920 (5.12–5.14 use abstract complete L).
Caveats: 5.13 proved in scale-corrected form |f−g|_c < |f|_c; 5.14 via HasSum over L.
