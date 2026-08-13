"""Tests ISOLÉS — `...iv_2_morphismes_structures_derivees.ensembles_cst8_inversible_iso`.

CST8 (IV.2.1, E IV.12) : « un morphisme inversible (g σ-morphisme inverse bilatère de
f) est un isomorphisme ».  On certifie :
  • la CONCLUSION == est_iso_morph(E,𝒮,E',𝒮',f) LITTÉRALEMENT (PAS de tautologie) ;
  • les HYPOTHÈSES sont EXACTEMENT {morph(f), morph(g), g=f⁻¹} — aucune parasite,
    donc pas d'affaibli déguisé ;
  • le théorème APPELLE bien la machinerie du noyau (théorème non clos, conditionnel) ;
  • theorie_ensembles() reste à 22 axiomes (rien postulé).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees import ensembles_cst8_inversible_iso as M
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import est_morphisme
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_chap4_props_restantes import est_iso_morph


# ── theorie intangible ────────────────────────────────────────────────────────
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── conclusion EXACTE : est_iso_morph(E,𝒮,E',𝒮',f) ───────────────────────────
def test_cst8_conclusion_exacte_est_iso():
    t = M.cst8_morphisme_inversible_est_iso()
    exp = est_iso_morph("E", "S", "Ep", "Sp", "f")
    assert t.conclusion == exp                  # = morph(E,𝒮,E',𝒮',f) ET morph(E',𝒮',E,𝒮,f⁻¹)


def test_cst8_conclusion_non_tautologie():
    """La conclusion est la CONJONCTION de deux clauses DISTINCTES (morph sur f vs morph
    sur f⁻¹) : pas un P∧P trivial.  (Le `et` est normalisé De Morgan en
    non(ou(non c1, non c2)) ; on compare donc à et(c1, c2) plutôt qu'aux sous-nœuds.)"""
    t = M.cst8_morphisme_inversible_est_iso()
    c1 = est_morphisme(var("E"), var("S"), var("Ep"), var("Sp"), var("f"))
    c2 = est_morphisme(var("Ep"), var("Sp"), var("E"), var("S"), E.reciproque(var("f")))
    assert c1 != c2                             # les deux conjoints sont DISTINCTS
    assert var("f") != E.reciproque(var("f"))
    assert t.conclusion == et(c1, c2)          # conclusion = c1 ∧ c2 (pas P∧P)


# ── hypothèses EXACTES : {morph(f), morph(g), g=f⁻¹} ─────────────────────────
def test_cst8_hypotheses_explicites():
    ve, vs, vep, vsp = var("E"), var("S"), var("Ep"), var("Sp")
    vf, vg = var("f"), var("g")
    morph_f = est_morphisme(ve, vs, vep, vsp, vf)        # f : (E,𝒮)→(E',𝒮')
    morph_g = est_morphisme(vep, vsp, ve, vs, vg)        # g : (E',𝒮')→(E,𝒮)
    g_eq_finv = egal(vg, E.reciproque(vf))               # g = f⁻¹  (II.18 corollaire)
    t = M.cst8_morphisme_inversible_est_iso()
    assert t.hypotheses == frozenset({morph_f, morph_g, g_eq_finv})
    assert not t.est_clos                                # conditionnel (II.18 reporté)
    assert len(t.hypotheses) == 3


# ── le théorème UTILISE bien g=f⁻¹ (sinon morph(g) suffirait, hyp parasite) ──
def test_cst8_seconde_clause_porte_sur_f_inverse():
    """La seconde clause de l'iso est morph(E',𝒮',E,𝒮, f⁻¹) — issue de morph(g) RÉÉCRIT
    par g=f⁻¹ ; c'est le « g est l'isomorphisme réciproque » de Bourbaki.  On la
    reconstruit explicitement et on vérifie qu'elle figure dans la conclusion (via la
    forme conjonctive c1 ∧ c2 = est_iso_morph)."""
    t = M.cst8_morphisme_inversible_est_iso()
    c1 = est_morphisme(var("E"), var("S"), var("Ep"), var("Sp"), var("f"))
    clause_finv = est_morphisme(var("Ep"), var("Sp"), var("E"), var("S"),
                                E.reciproque(var("f")))
    assert t.conclusion == et(c1, clause_finv)  # 2ᵉ clause = morph(…, f⁻¹) LITTÉRAL
