"""Tests §IV — CRITÈRES DE STRUCTURES (CST) : cœurs logiques certifiés.

On vérifie que chaque palier logique des critères CST est correctement certifié par
le noyau : soit CLOS (purement logique, 0 hypothèse), soit CONDITIONNEL avec les
hypothèses EXACTEMENT attendues (= axiomes-schémas (IN)/(FI)/(AU)/(MO) instanciés),
et que la conclusion est bien la formule fidèle visée — JAMAIS une tautologie P⇒P.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, app, non, alpha_egal)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres import ensembles_CST_criteres as C
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees import ensembles_universel_morphismes as M
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees import ensembles_universel_finale as F


def _af(t): return app("A", t)
def _sf(t): return app("Sig", t)
def _ff(t): return app("f", t)


# ════════════════════════════════════════════════════════════════════════════
#  CST9 — unicité de la structure initiale
# ════════════════════════════════════════════════════════════════════════════
def test_initiales_mutuellement_plus_fines_certifie():
    """{(IN_𝓘),(IN_𝓘'),2×(id morph)} ⊢ plus_fine(E,𝓘,𝓘') et plus_fine(E,𝓘',𝓘)."""
    t = C.initiales_mutuellement_plus_fines()
    assert not t.est_clos
    assert len(t.hypotheses) == 4          # 2 (IN) + 2 (MO_III id)
    # conclusion = conjonction des deux « plus fine »
    mor = M._morph_defaut()
    pfIJ = M.plus_fine("E", var("I"), var("J"), mor)
    pfJI = M.plus_fine("E", var("J"), var("I"), mor)
    assert alpha_egal(t.conclusion, et(pfIJ, pfJI))
    # non dégénéré : la conclusion n'est PAS une hypothèse
    assert t.conclusion not in t.hypotheses


def test_cst9_hypotheses_sont_les_axiomes_attendus():
    """Les 4 hypothèses du cœur = (IN_𝓘),(IN_𝓘') + id-morph (E,𝓘) et (E,𝓘')."""
    t = C.initiales_mutuellement_plus_fines()
    mor = M._morph_defaut()
    inI = M.propriete_IN(var("E"), var("I"), var("I0"), _af, _sf, _ff, morph=mor)
    inJ = M.propriete_IN(var("E"), var("J"), var("I0"), _af, _sf, _ff, morph=mor)
    idI = C.id_est_morphisme("E", "I", mor)
    idJ = C.id_est_morphisme("E", "J", mor)
    for h in (inI, inJ, idI, idJ):
        assert h in t.hypotheses


def test_cst9_unicite_initiale_conclut_egalite():
    """{(IN),(IN'),2×id-morph, ANTISYM} ⊢ 𝓘 = 𝓘' (unicité de Bourbaki)."""
    t = C.cst9_unicite_initiale()
    assert not t.est_clos
    assert t.conclusion == egal(var("I"), var("J"))
    # non dégénéré
    assert t.conclusion not in t.hypotheses
    # l'antisymétrie (MO_III) est bien une hypothèse explicite
    mut = C.initiales_mutuellement_plus_fines()
    antisym = impl(mut.conclusion, egal(var("I"), var("J")))
    assert antisym in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  CST18 — unicité de la structure finale (dual)
# ════════════════════════════════════════════════════════════════════════════
def test_finales_mutuellement_plus_fines_certifie():
    t = C.finales_mutuellement_plus_fines()
    assert not t.est_clos
    assert len(t.hypotheses) == 4
    mor = M._morph_defaut()
    pfFG = M.plus_fine("E", var("F"), var("G"), mor)
    pfGF = M.plus_fine("E", var("G"), var("F"), mor)
    assert alpha_egal(t.conclusion, et(pfFG, pfGF))
    assert t.conclusion not in t.hypotheses


def test_cst18_unicite_finale_conclut_egalite():
    t = C.cst18_unicite_finale()
    assert not t.est_clos
    assert t.conclusion == egal(var("F"), var("G"))
    assert t.conclusion not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  Transport préserve les morphismes (IV.1.5 / cœur CST4) — (MO_II)
# ════════════════════════════════════════════════════════════════════════════
def test_axiome_MO_II_forme():
    """(MO_II) instancié = (morph(E,𝒮,E',𝒮',f) et morph(E',𝒮',E'',𝒮'',g)) ⇒
    morph(E,𝒮,E'',𝒮'', g∘f)."""
    mor = M._morph_defaut()
    mo2 = C.axiome_MO_II("E", "S", "Ep", "Sp", "Epp", "Spp", "f", "g", mor)
    # implication ; conséquent contient la composée g∘f
    assert mo2.tag == "ou"   # impl = ¬∨
    assert "composee" in repr(mo2)


def test_transport_preserve_morphisme_certifie():
    """{(MO_II), morph f, morph g} ⊢ morph(E,𝒮,E'',𝒮'', g∘f)."""
    t = C.transport_preserve_morphisme()
    assert not t.est_clos
    assert len(t.hypotheses) == 3          # (MO_II) + morph f + morph g
    mor = M._morph_defaut()
    cible = M.est_morphisme(var("E"), var("S"), var("Epp"), var("Spp"),
                            E.composee(var("g"), var("f")), mor)
    assert alpha_egal(t.conclusion, cible)
    # non dégénéré
    assert t.conclusion not in t.hypotheses


def test_cst4_alias():
    a = C.cst4_compose_isos_morphisme_aller()
    b = C.transport_preserve_morphisme()
    assert alpha_egal(a.conclusion, b.conclusion)


# ════════════════════════════════════════════════════════════════════════════
#  CST5 — unicité du transport de structure
# ════════════════════════════════════════════════════════════════════════════
def test_cst5_unicite_transport_certifie():
    """{V=⟨f,Id⟩^S(U), V'=⟨f,Id⟩^S(U)} ⊢ V = V'."""
    t = C.cst5_unicite_transport()
    assert not t.est_clos
    assert len(t.hypotheses) == 2
    assert t.conclusion == egal(var("V"), var("V2"))
    # non dégénéré : V=V' n'est pas une hypothèse
    assert t.conclusion not in t.hypotheses
    # les hypothèses sont les deux relations (4) (égalités au transporté commun)
    transporte = app("extension_echelon", var("S"), var("f"), var("U"))
    assert egal(var("V"), transporte) in t.hypotheses
    assert egal(var("V2"), transporte) in t.hypotheses


def test_relation_transport_iso_forme():
    rel = C.relation_transport_iso("E", "U", "Ep", "V", "f")
    transporte = app("extension_echelon", var("S"), var("f"), var("U"))
    assert rel == egal(var("V"), transporte)


# ════════════════════════════════════════════════════════════════════════════
#  CST22/CST23/CST8 — unicité de la solution universelle
# ════════════════════════════════════════════════════════════════════════════
def test_factorisation_unique_des_solutions_certifie():
    """{(AU_I′) croisé H1,H2, ANTISYM=(AU_II′)} ⊢ f₂∘f₁=Id et f₁∘f₂=Id."""
    t = C.factorisation_unique_des_solutions()
    assert not t.est_clos
    assert len(t.hypotheses) == 3          # H1, H2, ANTISYM
    inv1 = egal(E.composee(var("f2"), var("f1")), E.diagonale(var("FE")))
    inv2 = egal(E.composee(var("f1"), var("f2")), E.diagonale(var("FEp")))
    assert alpha_egal(t.conclusion, et(inv1, inv2))
    assert t.conclusion not in t.hypotheses


def test_contraposition_injection_ponctuelle_CLOS():
    """⊢ contraposition pure (¬eq⇒neq)⇒(eq⇒eq_back) — helper logique trivial, PAS CST23."""
    t = C._contraposition_injection_ponctuelle()
    assert t.est_clos                       # purement logique : contraposition
    # conclusion = ( (¬(x=y) ⇒ φx≠φy) ⇒ ( (φx=φy) ⇒ x=y) )
    assert t.conclusion.tag == "ou"         # implication
    # conclusion fidèle : implication (séparation pt) ⇒ (injection pt)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl, non, egal
    vx, vy, vphi = var("x"), var("y"), var("phiE")
    sep = non(egal(E.valeur(vphi, vx), E.valeur(vphi, vy)))   # φ_E(x) ≠ φ_E(y)
    diff = non(egal(vx, vy))                                  # x ≠ y
    inj = impl(egal(E.valeur(vphi, vx), E.valeur(vphi, vy)), egal(vx, vy))
    cible = impl(impl(diff, sep), inj)
    assert alpha_egal(t.conclusion, cible)
