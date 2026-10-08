#!/usr/bin/env python3
"""Reflow over-long comment paragraphs to 100 columns and apply the listed code-line fixes."""
import re, textwrap, sys
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
FILES = ['NegLog', 'RatLog', 'Basic', 'RankOne', 'Commensurable', 'Discrete', 'Normed', 'Padic',
         'LaurentSeries', 'Extension', 'PadicComplex', 'Examples']
FIX = {
 "@[simp] lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by sorry":
 "@[simp] lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by\n  sorry",
 "    AddCommGroup.IsCommensurableWith (Additive.ofMul (commGen v π)) (Additive.ofMul g) := by sorry":
 "    AddCommGroup.IsCommensurableWith (Additive.ofMul (commGen v π)) (Additive.ofMul g) := by\n  sorry",
 "    (hmn : v x ^ n = v π ^ m) : v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry":
 "    (hmn : v x ^ n = v π ^ m) :\n    v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry",
 "theorem addValQ_unique (w : AddValuation R (WithTop ℚ)) (hw : ∀ x y, w x ≤ w y ↔ v y ≤ v x)":
 "theorem addValQ_unique (w : AddValuation R (WithTop ℚ))\n    (hw : ∀ x y, w x ≤ w y ↔ v y ≤ v x)",
 "    RankOne.addVal v x\n      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log (RankOne.hom v (v.restrict π))))\n          (v.addValQ π x) := by sorry":
 "    RankOne.addVal v x =\n      WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log (RankOne.hom v (v.restrict π))))\n        (v.addValQ π x) := by sorry",
 "theorem RankOne.hom_eq_rpow_addValQ {x : R} {q : ℚ} (hq : v.addValQ π x = (q : WithTop ℚ)) :\n    ((RankOne.hom v (v.restrict x) : ℝ)) = ((RankOne.hom v (v.restrict π) : ℝ)) ^ (q : ℝ) := by\n  sorry":
 "theorem RankOne.hom_eq_rpow_addValQ {x : R} {q : ℚ}\n    (hq : v.addValQ π x = (q : WithTop ℚ)) :\n    ((RankOne.hom v (v.restrict x) : ℝ)) = ((RankOne.hom v (v.restrict π) : ℝ)) ^ (q : ℝ) := by\n  sorry",
 "    (hπ : IsUniformizer v π) {e : ℝ≥0} (he : e ≠ 0) (hπe : RankOne.hom v (v.restrict π) = e⁻¹)":
 "    (hπ : IsUniformizer v π) {e : ℝ≥0} (he : e ≠ 0)\n    (hπe : RankOne.hom v (v.restrict π) = e⁻¹)",
 "    normAddVal ℚ_[p] x = WithTop.map (fun k : ℤ ↦ (k : ℝ) * Real.log p) (normAddValZ ℚ_[p] x) := by\n  sorry":
 "    normAddVal ℚ_[p] x\n      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * Real.log p) (normAddValZ ℚ_[p] x) := by sorry",
 "instance isRankOneDiscrete_valued : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).IsRankOneDiscrete :=\n  by sorry":
 "instance isRankOneDiscrete_valued :\n    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).IsRankOneDiscrete := by sorry",
 "    generator (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) = Units.mk0 (exp (-1 : ℤ)) exp_ne_zero := by\n  sorry":
 "    generator (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)\n      = Units.mk0 (exp (-1 : ℤ)) exp_ne_zero := by sorry",
 "    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f = (f.order : WithTop ℤ) := by sorry":
 "    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f = (f.order : WithTop ℤ) := by\n  sorry",
 "@[simp] lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (t : ℝ) : toNNReal he (exp t) = e ^ t := by sorry":
 "@[simp] lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (t : ℝ) : toNNReal he (exp t) = e ^ t := by\n  sorry",
 "    ‖x‖ = ((RankOne.hom (valuation (K := K)) ((valuation (K := K)).restrict x) : ℝ≥0) : ℝ) := by\n  sorry":
 "    ‖x‖ = ((RankOne.hom (valuation (K := K)) ((valuation (K := K)).restrict x) : ℝ≥0) : ℝ) :=\n  by sorry",
 "lemma normAddVal_le_normAddVal {x y : K} : normAddVal K x ≤ normAddVal K y ↔ ‖y‖ ≤ ‖x‖ := by\n  sorry":
 "lemma normAddVal_le_normAddVal {x y : K} :\n    normAddVal K x ≤ normAddVal K y ↔ ‖y‖ ≤ ‖x‖ := by sorry",
 "    normAddVal K x = WithTop.map (fun k : ℤ ↦ (k : ℝ) * (-Real.log ‖π‖)) (normAddValZ K x) := by\n  sorry":
 "    normAddVal K x\n      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * (-Real.log ‖π‖)) (normAddValZ K x) := by sorry",
 "    (h : ‖x‖ ^ n = ‖π‖ ^ m) : normAddValQ K π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by\n  sorry":
 "    (h : ‖x‖ ^ n = ‖π‖ ^ m) :\n    normAddValQ K π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry",
 "theorem norm_eq_norm_rpow_normAddValQ {x : K} {q : ℚ} (hq : normAddValQ K π x = (q : WithTop ℚ)) :":
 "theorem norm_eq_norm_rpow_normAddValQ {x : K} {q : ℚ}\n    (hq : normAddValQ K π x = (q : WithTop ℚ)) :",
 "      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log ‖π‖)) (normAddValQ K π x) := by sorry":
 "      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log ‖π‖)) (normAddValQ K π x) := by\n  sorry",
 "instance isCyclic_valueGroup : IsCyclic (valueGroup (.ofClass (NormedField.valuation (K := ℚ_[p])))) := by\n  sorry":
 "instance isCyclic_valueGroup :\n    IsCyclic (valueGroup (.ofClass (NormedField.valuation (K := ℚ_[p])))) := by sorry",
 "theorem isRankOneDiscrete_valuation : (NormedField.valuation (K := ℚ_[p])).IsRankOneDiscrete := by sorry":
 "theorem isRankOneDiscrete_valuation : (NormedField.valuation (K := ℚ_[p])).IsRankOneDiscrete := by\n  sorry",
 "theorem coe_generator_eq : (generator (NormedField.valuation (K := ℚ_[p])) : ℝ≥0) = (p : ℝ≥0)⁻¹ := by sorry":
 "theorem coe_generator_eq :\n    (generator (NormedField.valuation (K := ℚ_[p])) : ℝ≥0) = (p : ℝ≥0)⁻¹ := by sorry",
 "theorem isUniformizer_p : IsUniformizer (NormedField.valuation (K := ℚ_[p])) (p : ℚ_[p]) := by sorry":
 "theorem isUniformizer_p : IsUniformizer (NormedField.valuation (K := ℚ_[p])) (p : ℚ_[p]) := by\n  sorry",
 "instance isCommensurable_p : (NormedField.valuation (K := ℚ_[p])).IsCommensurable (p : ℚ_[p]) := by sorry":
 "instance isCommensurable_p : (NormedField.valuation (K := ℚ_[p])).IsCommensurable (p : ℚ_[p]) := by\n  sorry",
 "theorem normedField_valuation_eq : (valuation (K := ℂ_[p])) = (PadicComplex.valued p).v := by sorry":
 "theorem normedField_valuation_eq : (valuation (K := ℂ_[p])) = (PadicComplex.valued p).v := by\n  sorry",
 "    (hq : normAddValQ ℂ_[p] p x = (q : WithTop ℚ)) : ‖x‖ = (p : ℝ) ^ (-(q : ℝ)) := by sorry":
 "    (hq : normAddValQ ℂ_[p] p x = (q : WithTop ℚ)) : ‖x‖ = (p : ℝ) ^ (-(q : ℝ)) := by\n  sorry",
 "    Set.range (normAddValQ ℂ_[p] p) = insert ⊤ (Set.range ((↑) : ℚ → WithTop ℚ)) := by sorry":
 "    Set.range (normAddValQ ℂ_[p] p) = insert ⊤ (Set.range ((↑) : ℚ → WithTop ℚ)) := by\n  sorry",
 "    {m n : ℤ} (hn : 0 < n) (hmn : n • a = m • a₀) : ratCoeff h a = (m : ℚ) / (n : ℚ) := by sorry":
 "    {m n : ℤ} (hn : 0 < n) (hmn : n • a = m • a₀) : ratCoeff h a = (m : ℚ) / (n : ℚ) := by\n  sorry",
 "noncomputable def ratLog (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) : M →+ ℚ where":
 "noncomputable def ratLog (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :\n    M →+ ℚ where",
 "    (hn : 0 < n) (hmn : n • a = m • a₀) : ratLog ha₀ h a = -((m : ℚ) / (n : ℚ)) := by sorry":
 "    (hn : 0 < n) (hmn : n • a = m • a₀) : ratLog ha₀ h a = -((m : ℚ) / (n : ℚ)) := by\n  sorry",
}
def reflow(lines):
    """Reflow paragraphs inside comment blocks that contain a line > 100 chars."""
    out = []; i = 0; incomment = False
    while i < len(lines):
        l = lines[i]
        if not incomment:
            if l.lstrip().startswith('/-'):
                incomment = True
            else:
                out.append(l); i += 1; continue
        # collect a paragraph
        j = i; para = []
        while j < len(lines) and lines[j].strip() != '' and not lines[j].strip().startswith('```'):
            para.append(lines[j]); j += 1
            if lines[j-1].rstrip().endswith('-/'): break
            if j < len(lines) and re.match(r'^\s*(\* |- |\d+\. )', lines[j]): break
        if not para:
            if i < len(lines) and lines[i].strip().startswith('```'):
                # skip fenced block verbatim
                out.append(lines[i]); i += 1
                while i < len(lines) and not lines[i].strip().startswith('```'):
                    out.append(lines[i]); i += 1
                if i < len(lines): out.append(lines[i]); i += 1
                continue
            out.append(l); i += 1
            if l.rstrip().endswith('-/'): incomment = False
            continue
        ends = para[-1].rstrip().endswith('-/')
        if max(len(p) for p in para) > 100:
            first = para[0]
            m = re.match(r'^(\s*)(/-- |/-! |/- |\* |- |\d+\. )?', first)
            indent, marker = m.group(1), (m.group(2) or '')
            body = ' '.join(p.strip() for p in para)
            if marker: body = body[len(marker.strip()):].strip() if body.startswith(marker.strip()) else body
            trail = ''
            if ends and body.endswith('-/'):
                body = body[:-2].rstrip(); trail = ' -/'
            sub = indent + ('  ' if marker.strip() in ('*', '-') or re.match(r'\d+\.', marker.strip() or 'x') else '')
            wrapped = textwrap.wrap(body + trail, width=100, initial_indent=indent + marker, subsequent_indent=sub, break_long_words=False, break_on_hyphens=False)
            out.extend(wrapped)
        else:
            out.extend(para)
        i = j
        if ends: incomment = False
    return out
for name in FILES:
    path = D + name + '.lean'
    src = open(path).read()
    for k, v in FIX.items():
        if k in src: src = src.replace(k, v)
    lines = reflow(src.split('\n'))
    open(path, 'w').write('\n'.join(lines))
    long = [(n+1, len(l)) for n, l in enumerate(lines) if len(l) > 100]
    if long: print(name, 'still long:', long)
print('done')
