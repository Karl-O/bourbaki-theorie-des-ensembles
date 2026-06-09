"""Tests §IV.3 (complément) — Parties Σ-permises, cardinal à possibilité Σ-permise,
conditions (CU_I)–(CU_III), critères CST22 / CST8.

Vérifie la fidélité des DÉFINITIONS introduites (formes attendues) et la
certification par le noyau des LEMMES logiques directs (extraction des conditions
(CU_k) de la conjonction des hypothèses de CST22).
"""
from bourbaki.logique.formule import (var, et, impl, equiv, existe, pourtout,
                                       appartient, inclus, egal, app, alpha_egal)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, est_cardinal,
                                                    inf_egal_card)
from bourbaki.structures import ensembles_structures_complements as C


# ── partie Σ-permise ──────────────────────────────────────────────────────────
def test_partie_sigma_permise_est_conjonction_inclusion_induit():
    induit = C._induit_defaut()
    d = C.est_partie_sigma_permise(var("F"), var("S"), var("G"), induit)
    cible = et(inclus(var("G"), var("F")), induit(var("F"), var("S"), var("G")))
    assert alpha_egal(d, cible)


def test_partie_sigma_permise_contient_inclusion():
    d = C.est_partie_sigma_permise(var("F"), var("S"), var("G"))
    # la conjonction (et) est normalisée De Morgan en non(ou(non…,non…)).  On
    # vérifie la forme COMPLÈTE : inclusion G ⊂ F  ET  « 𝒮 induit Σ sur G ».
    assert d == et(inclus(var("G"), var("F")),
                   C._induit_defaut()(var("F"), var("S"), var("G")))


# ── conditions (CU_I), (CU_II) ────────────────────────────────────────────────
def test_condition_CU_I_implication_vers_structure_produit():
    cu1 = C.condition_CU_I(var("I0"), lambda t: app("A", t),
                           lambda t: app("Sig", t))
    # (∀ι sigma-ens) ⇒ sigma_ens(∏A, Sprod) : tête = ou (impl)
    assert cu1.tag == "ou"
    assert "produit_fam" in repr(cu1)


def test_condition_CU_II_mentionne_produit_et_alpha():
    cu2 = C.condition_CU_II(var("E"), var("I0"), lambda t: app("A", t),
                            lambda t: app("Sig", t), lambda t: app("phi", t))
    assert cu2.tag == "ou"            # implication
    assert "produit_fam" in repr(cu2)
    assert "Alpha" in repr(cu2)       # prédicat alpha par défaut


# ── (CU_III) et cardinal à possibilité Σ-permise ──────────────────────────────
def test_possibilite_sigma_permise_existe_partie():
    p = C.possibilite_sigma_permise(var("a"), var("E"), var("F"), var("S"),
                                    var("phi"))
    # (∃G)(…) : nœud existentiel
    assert p.tag == "exists"
    # contient la borne de cardinal Card(G) ≤ 𝔞 et l'image directe φ(E)
    r = repr(p)
    assert "image" in r


def test_condition_CU_III_quantifie_F_S_phi():
    cu3 = C.condition_CU_III(var("a"), var("E"))
    # (∀F)(∀S)(∀φ)(…) : tête non (pourtout abrégé)
    assert cu3.tag == "non"


def test_cardinal_a_possibilite_sigma_permise_existe_cardinal():
    cps = C.cardinal_a_possibilite_sigma_permise(var("E"))
    # (∃a)(est_cardinal(a) et propriété) : nœud existentiel
    assert cps.tag == "exists"
    # la clause est_cardinal(a) apparaît (cardinal use τ_Z(Eq))
    assert "tau" in repr(cps)


# ── CST22 ─────────────────────────────────────────────────────────────────────
def test_hypotheses_CST22_est_conjonction_des_trois_CU():
    ff, sf, phif = (lambda t: app("A", t), lambda t: app("Sig", t),
                    lambda t: app("phi", t))
    hyp = C.hypotheses_CST22(var("E"), var("I0"), ff, sf, phif, var("a"))
    # hyp = ((CU_I) et (CU_II)) et (CU_III) — comparaison structurelle complète
    cu1 = C.condition_CU_I(var("I0"), ff, sf)
    cu2 = C.condition_CU_II(var("E"), var("I0"), ff, sf, phif)
    cu3 = C.condition_CU_III(var("a"), var("E"))
    assert hyp == et(et(cu1, cu2), cu3)


def test_critere_CST22_est_implication_vers_solution():
    crit = C.critere_CST22(var("E"), var("I0"), lambda t: app("A", t),
                           lambda t: app("Sig", t), lambda t: app("phi", t),
                           var("a"), var("FE"), var("SE"), var("phiE"))
    # hyp ⇒ solution : tête = ou (impl)
    assert crit.tag == "ou"


def test_cst22_extrait_CU_I_certifie():
    """{(CU_I) et (CU_II) et (CU_III)} ⊢ (CU_I) — lemme logique certifié."""
    t = C.cst22_extrait_CU_I()
    assert t.est_clos
    # conclusion = hyp ⇒ (CU_I)
    assert t.conclusion.tag == "ou"   # impl


def test_cst22_extrait_CU_III_certifie():
    """{(CU_I) et (CU_II) et (CU_III)} ⊢ (CU_III) — lemme logique certifié."""
    t = C.cst22_extrait_CU_III()
    assert t.est_clos
    assert t.conclusion.tag == "ou"   # impl
    # le conséquent EST bien (CU_III)
    cu3 = C.condition_CU_III(var("a"), var("E"))
    assert t.conclusion.sous[1] == cu3


# ── CST8 : unicité à isomorphisme unique près ─────────────────────────────────
def test_solution_isomorphisme_unique_forme():
    iso = C.solution_isomorphisme_unique(var("FE"), var("SE"), var("phiE"),
                                         var("FEp"), var("SEp"), var("phiEp"))
    # (∃f₁)(∃f₂)(…) : nœud existentiel
    assert iso.tag == "exists"
    r = repr(iso)
    # les égalités d'inversion f₂∘f₁ = Id et les compositions apparaissent
    assert "composee" in r and "diagonale" in r
