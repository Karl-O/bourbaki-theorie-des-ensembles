"""Tests de ensembles_zermelo.py — THÉORÈME DE ZERMELO (E.III.2) : « tout
ensemble peut être bien ordonné », via le THÉORÈME DE ZORN.

On vérifie palier par palier (SALVAGE GRADUÉ) :
  • ÉTAPE 0 : Θ (end-extension) est un ORDRE sur W (bons ordres partiels de X).
  • ÉTAPE 1 : (Θ,W) est INDUCTIF — la réunion d'une Θ-chaîne bien ordonne. [CŒUR]
  • ÉTAPE 2 : W ≠ ∅ (le graphe vide ∅ est un bon ordre partiel).
  • ÉTAPE 3 : ZORN ⇒ (∃M) element_maximal(Θ,W,M).
  • ÉTAPE 4 : champ(M)=X (par l'absurde, extension au sommet).
  • ÉTAPE 5 : 🎯 zermelo() ⊢ (∃R) est_bien_ordonne(R,X) — CLOS.

INVARIANT : theorie_ensembles() reste = 22 (axiomes de W/Θ/Union en théories
DÉDIÉES).  🚫 JAMAIS postuler le bon ordre : il est CONSTRUIT.
"""
from bourbaki.logique.formule import var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre, transitivite_rel
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo import ensembles_zermelo as Z


X = var("X")


# ── theorie_ensembles INTANGIBLE = 22 ; théories dédiées séparées ─────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theories_dediees_un_axiome():
    assert len(Z.theorie_W().axiomes) == 1
    assert len(Z.theorie_Theta().axiomes) == 1
    assert Z.axiome_W() not in E.theorie_ensembles().axiomes
    assert Z.axiome_Theta() not in E.theorie_ensembles().axiomes


# ── ÉTAPE 0 — Θ est un ordre sur W ────────────────────────────────────────────
def test_Theta_reflexive_sur():
    th = Z.Theta_reflexive_sur("X", "x")
    assert th.est_clos


def test_Theta_antisymetrique():
    th = Z.Theta_antisymetrique("X", "x", "y")
    assert th.est_clos


def test_Theta_transitive():
    th = Z.Theta_transitive("X", "x", "y", "z")
    assert th.est_clos
    assert th.conclusion == transitivite_rel(Z.Theta(X), "x", "y", "z")


def test_Theta_est_ordre():
    th = Z.Theta_est_ordre("X")
    assert th.est_clos
    assert th.conclusion == est_ordre(Z.Theta(X), Z.W(X), "x", "y", "z")


def test_theorie_Union_dediee():
    assert len(Z.theorie_Union().axiomes) == 1
    assert Z.axiome_Union() not in E.theorie_ensembles().axiomes


# ── ÉTAPE 1 — (Θ,W) inductif (le CŒUR : réunion d'une chaîne bien ordonne) ────
def test_Union_inclus_produit():
    th = Z.Union_inclus_produit("X", "D")
    assert len(th.hypotheses) == 1               # 𝔇⊂W


def test_Union_transitif():
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import ordre_transitif
    th = Z.Union_transitif("X", "D")
    assert th.conclusion == ordre_transitif(Z.R_de(Z.Union(X, var("D"))), "a", "b", "c")
    assert len(th.hypotheses) == 2


def test_Union_bien_ordonne_corps():
    # 🎯 LE CŒUR DUR : toute partie non vide de champ ⋃𝔇 a un plus petit élément.
    th = Z.Union_bien_ordonne_corps("X", "D")
    assert len(th.hypotheses) == 2               # 𝔇⊂W et totalement_ordonne(Θ,𝔇)


def test_Union_bop_match():
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zermelo import bon_ordre_partiel
    th = Z.Union_bop("X", "D")
    Ut = Z.Union(X, var("D"))
    assert th.conclusion == bon_ordre_partiel(Ut, X)
    assert len(th.hypotheses) == 2


def test_Union_dans_W():
    from bourbaki.logique.formule import appartient
    th = Z.Union_dans_W("X", "D")
    assert th.conclusion == appartient(Z.Union(X, var("D")), Z.W(X))
    assert len(th.hypotheses) == 2


def test_Union_majorant():
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import majorant
    th = Z.Union_majorant("X", "D")
    Ut = Z.Union(X, var("D"))
    assert th.conclusion == majorant(Z.Theta(X), var("D"), Ut, Z.W(X), "x")
    assert len(th.hypotheses) == 2


def test_W_inductif():
    # 🎯🎯 (Θ,W) EST INDUCTIF — assemblage du cœur, INCONDITIONNEL.
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
    th = Z.W_inductif("X")
    assert th.est_clos
    assert th.conclusion == est_inductif(Z.Theta(X), Z.W(X))


# ── ÉTAPE 2 — W ≠ ∅ (∅ est un bon ordre partiel) ─────────────────────────────
def test_vide_bon_ordre_partiel():
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zermelo import bon_ordre_partiel
    th = Z.vide_bon_ordre_partiel("X")
    assert th.est_clos
    assert th.conclusion == bon_ordre_partiel(E.VIDE, X)


def test_vide_dans_W():
    from bourbaki.logique.formule import appartient
    th = Z.vide_dans_W("X")
    assert th.est_clos
    assert th.conclusion == appartient(E.VIDE, Z.W(X))


def test_W_non_vide():
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import enonce_non_vide
    th = Z.W_non_vide("X", "w")
    assert th.est_clos
    assert th.conclusion == enonce_non_vide(Z.W(X), "w")


# ── ÉTAPE 3 — ZORN ⇒ (∃M) element_maximal(Θ,W,M) ─────────────────────────────
def test_maximal_existe():
    th = Z.maximal_existe("X", "m")
    assert th.est_clos
    assert th.conclusion.lieur == "m"            # (∃m) element_maximal(Θ,W,m)


# ── ÉTAPE 4 — extension au sommet : M' ∈ W, champ(M maximal) = X ──────────────
def test_theorie_Ext_dediee():
    assert len(Z.theorie_Ext().axiomes) == 1
    assert Z.axiome_Ext() not in E.theorie_ensembles().axiomes


def test_Ext_seg_initial():
    import bourbaki.logique.noyau_abrege as N
    from bourbaki.logique.formule import var, non, appartient
    vX, vM, vx0 = var("X"), var("M"), var("x0")
    Hx0nd = N.assume(non(appartient(vx0, Z.champ(vM))))
    th = Z.Ext_seg_initial(vX, vM, vx0, Hx0nd, p="p", q="q")
    assert th.conclusion == Z.seg_initial(vM, Z.Ext(vX, vM, vx0))


def test_Ext_dans_W():
    # 🎯 LE BON-ORDRE DU GRAPHE ÉTENDU : M' (x₀ au sommet) ∈ W.
    from bourbaki.logique.formule import var, appartient
    th = Z.Ext_dans_W("X", "M", "x0")
    assert len(th.hypotheses) == 3               # M∈W, x₀∉champ M, x₀∈X
    assert th.conclusion == appartient(Z.Ext(var("X"), var("M"), var("x0")), Z.W(var("X")))


def test_maximal_champ_eq_X():
    from bourbaki.logique.formule import egal
    th = Z.maximal_champ_eq_X("X", "M", "x0")
    assert len(th.hypotheses) == 1               # element_maximal(Θ,W,M)
    assert th.conclusion == egal(Z.champ(var("M")), X)


# ── ÉTAPE 5 — 🎯🎯🎯🎯 ZERMELO : (∃R) est_bien_ordonne(R, X) ─────────────────
def test_zermelo():
    from bourbaki.logique.formule import existe
    th = Z.zermelo("X")
    assert th.est_clos
    assert len(th.hypotheses) == 0
    expected = existe("R", Z.est_bien_ordonne_graphe(var("R"), X, X="S"))
    assert th.conclusion == expected
