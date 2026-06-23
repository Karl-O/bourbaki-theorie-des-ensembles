"""Tests ISOLÉS — `bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_chap4_props_restantes`.

Critères de structures (CST) RESTANTS du chapitre IV : CST3 (réciproque du transport),
MO_III (caractérisation des isos + réciproque d'un iso est un iso), CST12 (restriction
aux sous-structures), CST20 (passage aux quotients).  On certifie :
  • la STRUCTURE LOGIQUE (théorème conditionnel aux hypothèses EXPLICITES correctes,
    AUCUNE hypothèse parasite), donc PAS d'affaibli déguisé ;
  • la CONCLUSION == cible attendue LITTÉRALEMENT (PAS de tautologie vide) ;
  • MO_III (équivalence) est CLOS (0 hypothèse) ;
  • theorie_ensembles() reste à 22 axiomes (rien postulé).
"""
from bourbaki.logique.formule import var, egal, et, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres import ensembles_chap4_props_restantes as M
from bourbaki.structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import est_morphisme


# ── theorie intangible ────────────────────────────────────────────────────────
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── CST3 — réciproque du transport ────────────────────────────────────────────
def test_cst3_conclusion_exacte_non_tautologie():
    t = M.cst3_reciproque_transport()
    c = t.conclusion
    # conclusion = ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U  ; égalité NON triviale (lhs ≠ rhs), rhs == U
    assert c.tag == "="                        # c'est bien une égalité
    assert c.termes[0] != c.termes[1]          # PAS U=U (pas de tautologie vide)
    assert c.termes[1] == var("U")             # membre de droite = U


def test_cst3_hypotheses_exactes():
    vf, ve, vu = var("f"), var("E"), var("U")
    finv = E.reciproque(vf)
    finv_f = E.composee(finv, vf)
    DE = E.diagonale(ve)
    cst1 = M.axiome_CST1_composition("S", vf, finv, vu)
    bij = egal(finv_f, DE)
    idax = M.axiome_CST1_identite("S", ve, vu)
    t = M.cst3_reciproque_transport()
    # EXACTEMENT les 3 axiomes-schémas explicites (CST1 + bijection + CST1-id), rien d'autre
    assert t.hypotheses == frozenset({cst1, bij, idax})
    assert not t.est_clos                       # conditionnel (méta CST1 en hypothèse)


# ── (NEUTRALISÉ, audit Fable) réflexivité triviale, PAS le MO_III de Bourbaki ──
def test_est_iso_morph_reflexivite_est_triviale():
    """_est_iso_morph_reflexivite_triviale prouve P⇔P (réflexivité), PAS MO_III.
    On certifie EXPLICITEMENT la trivialité : les deux membres de l'équivalence sont
    la MÊME formule.  Le vrai MO_III (reliant est_isomorphisme IV.1.5 à morph∧morph⁻¹)
    est REPORTÉ."""
    t = M._est_iso_morph_reflexivite_triviale()
    assert t.est_clos
    iso = M.est_iso_morph("E", "S", "Ep", "Sp", "f")
    assert t.conclusion == equiv(iso, iso)      # P⇔P : les deux côtés IDENTIQUES


def test_reciproque_iso_extrait_morphisme():
    t = M.reciproque_iso_extrait_morphisme()
    # conclusion = morph(E',𝒮',E,𝒮, f⁻¹)  (le « morphisme réciproque » de CST4)
    exp = est_morphisme(var("Ep"), var("Sp"), var("E"), var("S"), E.reciproque(var("f")))
    assert t.conclusion == exp
    assert len(t.hypotheses) == 1               # sous est_iso(…,f)


def test_reciproque_iso_est_iso_conclusion_exacte():
    t = M.reciproque_iso_est_iso()
    exp = M.est_iso_morph("Ep", "Sp", "E", "S", E.reciproque(var("f")))
    assert t.conclusion == exp                  # est_iso(E',𝒮',E,𝒮, f⁻¹) LITTÉRAL
    assert not t.est_clos                       # sous est_iso(…,f) + involutivité
    # non-trivial : f ≠ f⁻¹
    assert var("f") != E.reciproque(var("f"))


# ── CST12 — restriction d'un morphisme aux sous-structures ────────────────────
def test_cst12_conclusion_exacte():
    t = M.cst12_restriction_morphisme()
    g = E.restriction(var("f"), var("B"))
    sB = M._struct_induite(var("S"), var("B"))
    sBp = M._struct_induite(var("Sp"), var("Bp"))
    exp = est_morphisme(var("B"), sB, var("Bp"), sBp, g)
    assert t.conclusion == exp                  # morph(B,𝒮_B,B',𝒮'_B', f|B) LITTÉRAL
    assert not t.est_clos                       # sous (IN) induite + EQ + (MO_II)
    assert len(t.hypotheses) == 3


def test_cst12_hypotheses_explicites():
    """Les 3 hypothèses sont EXACTEMENT (IN_B') ⇔, l'égalité j'∘g=f∘j, et la composée
    morphisme — aucune hypothèse parasite (donc pas d'affaibli déguisé)."""
    vb, vbp = var("B"), var("Bp")
    vap, vsp = var("Ap"), var("Sp")
    vs, vf = var("S"), var("f")
    sB = M._struct_induite(vs, vb)
    sBp = M._struct_induite(vsp, vbp)
    j = E.diagonale(vb)
    jp = E.diagonale(vbp)
    g = E.restriction(vf, vb)
    jp_g = E.composee(jp, g)
    f_j = E.composee(vf, j)
    cible = est_morphisme(vb, sB, vbp, sBp, g)
    rhs_jpg = est_morphisme(vb, sB, vap, vsp, jp_g)
    rhs_fj = est_morphisme(vb, sB, vap, vsp, f_j)
    IN_Bp = equiv(cible, rhs_jpg)
    EQ = egal(jp_g, f_j)
    t = M.cst12_restriction_morphisme()
    assert t.hypotheses == frozenset({IN_Bp, EQ, rhs_fj})


# ── CST20 — passage des morphismes aux quotients ──────────────────────────────
def test_cst20_conclusion_exacte():
    t = M.cst20_passage_quotient()
    from bourbaki.logique.formule import app
    va, vs, vap, vsp = var("A"), var("S"), var("Ap"), var("Sp")
    vr, vrp, vf = var("R"), var("Rp"), var("f")
    AR = E.quotient(vr, va)
    ARp = E.quotient(vrp, vap)
    s0 = M._struct_quotient(vs, AR)
    s0p = M._struct_quotient(vsp, ARp)
    g = app("passage_quotient", vf, vr, vrp)
    exp = est_morphisme(AR, s0, ARp, s0p, g)
    assert t.conclusion == exp                  # morph(A/R,𝒮₀,A'/R',𝒮'₀, g) LITTÉRAL
    assert not t.est_clos                       # sous (FI) quotient + EQ + (MO_II)
    assert len(t.hypotheses) == 3


def test_cst20_hypotheses_explicites():
    from bourbaki.logique.formule import app
    va, vs, vap, vsp = var("A"), var("S"), var("Ap"), var("Sp")
    vr, vrp, vf = var("R"), var("Rp"), var("f")
    AR = E.quotient(vr, va)
    ARp = E.quotient(vrp, vap)
    s0 = M._struct_quotient(vs, AR)
    s0p = M._struct_quotient(vsp, ARp)
    phi = E.application_canonique(vr, va)
    phip = E.application_canonique(vrp, vap)
    g = app("passage_quotient", vf, vr, vrp)
    g_phi = E.composee(g, phi)
    phip_f = E.composee(phip, vf)
    cible = est_morphisme(AR, s0, ARp, s0p, g)
    rhs_gphi = est_morphisme(va, vs, ARp, s0p, g_phi)
    rhs_phif = est_morphisme(va, vs, ARp, s0p, phip_f)
    FI_AR = equiv(cible, rhs_gphi)
    EQ = egal(g_phi, phip_f)
    t = M.cst20_passage_quotient()
    assert t.hypotheses == frozenset({FI_AR, EQ, rhs_phif})
