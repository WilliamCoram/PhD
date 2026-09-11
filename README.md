Ongoing PhD project to formalise quaternionic modular forms and results on the slopes of compact Hecke operators.

More information and progress can be found in the [blueprint](https://williamcoram.github.io/PhD/blueprint/sect0001.html).

## Layout

- `PhD/ForMathlib/` — mathlib-targeted foundations: restricted power series and Gauss norms, Weierstrass preparation and division (uni- and multivariate, at every radius), additive valuations, and the Newton polygon combinatorics.
- `PhD/NewtonPolygons/` — Newton polygons of power series over ultrametric fields: convexity and height API, slopes ↔ valuations of zeros with multiplicity, slope factorisation.
- `PhD/TateFredholm/` — compact operators and Fredholm determinants `det(1 − Tu)` over commutative nonarchimedean Banach–Tate rings (Johansson–Newton's setting), single-zero Riesz theory, and slope bounds for the determinant coefficients. See its `README.md`.
- `PhD/QMF/` — quaternionic automorphic forms: Buzzard's `S^D_{k,w}(U)` at classical weights and `S^D_κ(U)` at general locally analytic weights, Hecke operators `[UηU]`, compactness of `U_p`, Fredholm determinants, and the general-weight slope bound. See its `README.md`.
- `PhD/LWX/` — Liu–Wan–Xiao, *The eigencurve over the boundary of weight space* (arXiv:1412.2584v4): the halo ring `Λ^{>1/p}` and the universal character, the integral model of `U_p` and its entry streams (Prop 3.4), Theorem 3.16 / Corollary 3.18 on the halo estimate, and **Proposition 2.17 at every analyticity level** — `det(1 − X·U_p)` on `S^{D,†,m}` equals `det(I∞ − X·P)` in Colmez's basis (`11_SeamH.lean`, `12_QuaternionicH.lean`), which covers the whole boundary annulus `p⁻¹ < ‖T₀‖ < 1`.  The slope theorems (Thm 1.3 Step II, Thm 1.5 (1.5.1), both conditional on the touching hypothesis) are read on the genuine `U_p` through that seam in `13_SlopesSeam.lean`.  Boards: `.mathlib-quality/lwx-halo/`, `lwx-slopes/`, `lwx-seam/`, `lwx-seam-m/`.
- `PhD/JacobsSlash/` — the worked application (Jacobs' thesis Ch. 2: `p = 3`, level `U₁(9)`): the explicit `U₃`-matrix over the class set, `det(1 − T·U₃)` and its factorisation, and unconditional `U₃`-eigenvalues of valuation `j + ½` for every `j`. See its `PROGRESS.md`.
- `PhD/Mathlib/` — small patches pending upstream.
- `PhD/BirkovichWP/`, `PhD/Bryce/`, `PhD/LegacyCode/` — superseded or frozen history (kept on purpose; do not develop there).
- `PhD/Test/` — reference blueprints and design notes (some files are deliberately non-building references); `PhD/Explanations/` — prose notes on design decisions.

Status (2026-09-06): the live directories (`ForMathlib`, `NewtonPolygons`, `TateFredholm`, `QMF`, `LWX`, `JacobsSlash`) build sorry-free on the standard axioms.

Project boards live under `.mathlib-quality/` (one directory per work tranche; each `tickets.md` records its own status).
