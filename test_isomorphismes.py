"""Tests §IV.1.5 — isomorphismes (fragment objet, structure relationnelle).

Chaque théorème : conclusion == cible EXACTE et démonstration CLOSE (certifiée
par le noyau).  Les définitions sont vérifiées bien formées."""
from bourbaki.logique.formule import var, appartient, equiv, et, existe
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.fonctions import ensembles_isomorphismes as I
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de


def _G_relation():
    """Relation relationnelle générique R{x,y} := (x,y) ∈ G  (graphe G arbitraire)."""
    vG = var("G")
    return lambda a, b: appartient(E.couple(a, b), vG)


# ── définitions bien formées ──────────────────────────────────────────────────
def test_definitions_bien_formees():
    r = _G_relation()
    vE, vEp, vF = var("E"), var("Ep"), var("F")
    assert I.compatible(vF, vE, r, r) is not None
    iso = I.est_isomorphisme(vF, vE, vEp, r, r)
    # est_isomorphisme = bijection ET compatibilité
    assert iso == et(est_bijection_de(vF, vE, vEp), I.compatible(vF, vE, r, r))
    # structure transportée : renvoie bien une relation (Terme,Terme)->Formule
    rt = I.structure_transportee(vF, r)
    assert rt(var("u"), var("v")) is not None
    # sont_isomorphes = (∃F) est_isomorphisme(F,…)
    assert I.sont_isomorphes(vE, vEp, r, r) == existe("F", I.est_isomorphisme(var("F"), vE, vEp, r, r))


# ── théorème : Δ_E est un isomorphisme de (E,R) sur (E,R) ──────────────────────
def test_identite_est_isomorphisme():
    r = _G_relation()
    vE = var("E")
    thm = I.identite_est_isomorphisme("E", r)
    assert thm.est_clos
    cible = I.est_isomorphisme(E.diagonale(vE), vE, vE, r, r)
    assert thm.conclusion == cible


# ── théorème : réflexivité de « isomorphe » ───────────────────────────────────
def test_isomorphes_reflexive():
    r = _G_relation()
    vE = var("E")
    thm = I.isomorphes_reflexive("E", r)
    assert thm.est_clos
    assert thm.conclusion == I.sont_isomorphes(vE, vE, r, r)


# ── généralité : marche pour une relation d'ordre x≤y := (x,y)∈G (E.III.1.3) ──
def test_identite_iso_ordre():
    vG = var("G")
    leq = lambda a, b: appartient(E.couple(a, b), vG)
    vE = var("E")
    thm = I.identite_est_isomorphisme("E", leq)
    assert thm.est_clos
    assert thm.conclusion == I.est_isomorphisme(E.diagonale(vE), vE, vE, leq, leq)
