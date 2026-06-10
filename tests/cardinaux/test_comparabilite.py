"""Tests — Théorème de comparabilité des cardinaux (E.III.3, via Zorn).

Vérifie, palier par palier, que la construction du poset des injections
PARTIELLES, son inductivité (réunion d'une chaîne = injection partielle),
l'application de Zorn, l'extension g∪{(x,y)} et la conclusion disjonctive sont
toutes des théorèmes du noyau strict, theorie_ensembles() restant = 22.
"""
from bourbaki.logique.formule import var, ou, egal, inclus, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.ensembles_ordre_relation import est_ordre, element_maximal
from bourbaki.ordre.ensembles_zorn import est_inductif
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.cardinaux import ensembles_comparabilite as C


# ── ÉTAPE 1 — poset des injections partielles ────────────────────────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_Inj_membre():
    assert C.Inj_membre().est_clos


def test_Gamma_membre():
    assert C.Gamma_membre().est_clos


def test_Gamma_est_ordre():
    th = C.Gamma_est_ordre()
    assert th.est_clos
    assert th.conclusion == est_ordre(C.Gamma(var("X"), var("Y")),
                                      C.Inj(var("X"), var("Y")))


# ── ÉTAPE 2 — le CŒUR : la réunion d'une chaîne d'inj. partielles est inj. ───
def test_Union_inclus_produit():
    th = C.Union_inclus_produit()
    assert inclus(var("D"), C.Inj(var("X"), var("Y"))) in th.hypotheses


def test_Union_fonctionnel():
    assert len(C.Union_fonctionnel().hypotheses) == 2


def test_Union_injectif():
    assert len(C.Union_injectif().hypotheses) == 2


def test_Union_dans_Inj():
    assert len(C.Union_dans_Inj().hypotheses) == 2


def test_Inj_inductif_inconditionnel():
    th = C.Inj_inductif()
    assert th.est_clos
    assert th.conclusion == est_inductif(C.Gamma(var("X"), var("Y")),
                                         C.Inj(var("X"), var("Y")))


# ── ÉTAPE 3 — Inj≠∅ + Zorn ───────────────────────────────────────────────────
def test_vide_dans_Inj():
    assert C.vide_dans_Inj().est_clos


def test_maximal_existe():
    th = C.maximal_existe()
    assert th.est_clos


# ── ÉTAPE 4 — g maximal ⇒ dom g=X ou img g=Y ─────────────────────────────────
def test_maximal_dom_ou_img():
    th = C.maximal_dom_ou_img()
    g, X, Y = var("g"), var("X"), var("Y")
    assert th.conclusion == ou(egal(E.dom(g), X), egal(E.img(g), Y))
    assert element_maximal(C.Gamma(X, Y), C.Inj(X, Y), g, "x") in th.hypotheses


# ── ÉTAPE 5 — conclusion : injections totales dans les deux sens ─────────────
def test_g_injecte_X_dans_Y():
    th = C.g_injecte_X_dans_Y()
    assert th.conclusion == inf_egal_card(var("X"), var("Y"))


def test_reciproque_inj_partielle():
    th = C.reciproque_inj_partielle()
    assert th.conclusion == C.inj_partielle(E.reciproque(var("g")),
                                            var("Y"), var("X"))


def test_g_reciproque_injecte_Y_dans_X():
    th = C.g_reciproque_injecte_Y_dans_X()
    assert th.conclusion == inf_egal_card(var("Y"), var("X"))


# ── 🎯 LE THÉORÈME ────────────────────────────────────────────────────────────
def test_comparabilite_cardinaux_close():
    th = C.comparabilite_cardinaux()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    target = ou(inf_egal_card(var("X"), var("Y")), inf_egal_card(var("Y"), var("X")))
    assert th.conclusion == target


def test_theorie_ensembles_toujours_22_apres():
    C.comparabilite_cardinaux()
    assert len(E.theorie_ensembles().axiomes) == 22
