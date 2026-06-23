"""Tests — §IV.2 CST produit/quotient : CST13/15/16/17/21.

Vérifie pour CHAQUE critère :
  • la fonction produit bien un théorème du noyau (assertions internes passées) ;
  • la CONCLUSION est exactement la cible attendue ;
  • le non-vacuité (conclusion ∉ hypothèses) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.logique.formule import egal, equiv
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import est_morphisme, _t
from bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst_produit_quotient import (
    cst16_famille_morphismes_produit, cst15_imrec_produit_egales,
    cst13_produit_associatif_egales, cst17_morphisme_caracterise_par_graphe,
    est_iso_morph, cst21_quotients_egales)


def test_theorie_reste_22():
    assert len(theorie_ensembles().axiomes) == 22


# ── CST16 — famille de morphismes → morphisme dans le produit ──────────────────
def test_cst16_conclusion():
    th = cst16_famille_morphismes_produit()
    cible = est_morphisme(_t("Ep"), _t("Sp"), _t("E"), _t("P"), _t("f"))
    assert th.conclusion == cible
    # non vacuité : la conclusion n'est aucune des hypothèses
    assert cible not in th.hypotheses


# ── CST15 — image réciproque / produit (palier d'unicité) ──────────────────────
def test_cst15_conclusion():
    th = cst15_imrec_produit_egales()
    cible = egal(_t("R"), _t("J"))
    assert th.conclusion == cible
    assert cible not in th.hypotheses


# ── CST13 — associativité du produit (palier d'unicité) ────────────────────────
def test_cst13_conclusion():
    th = cst13_produit_associatif_egales()
    cible = egal(_t("P"), _t("Pp"))
    assert th.conclusion == cible
    assert cible not in th.hypotheses


# ── CST17 — morphisme caractérisé par son graphe ───────────────────────────────
def test_cst17_conclusion():
    th = cst17_morphisme_caracterise_par_graphe()
    cible = est_iso_morph(_t("F"), _t("SF"), _t("A"), _t("SA"), _t("pr1"))
    assert th.conclusion == cible
    # conjonction → la cible elle-même n'est aucune hypothèse isolée
    assert cible not in th.hypotheses
    assert len(th.hypotheses) == 2   # M et Mr


# ── CST21 — transitivité des structures quotient (palier d'unicité) ────────────
def test_cst21_conclusion():
    th = cst21_quotients_egales()
    cible = egal(_t("F"), _t("G"))
    assert th.conclusion == cible
    assert cible not in th.hypotheses


def test_theorie_reste_22_apres_tout():
    cst16_famille_morphismes_produit()
    cst15_imrec_produit_egales()
    cst13_produit_associatif_egales()
    cst17_morphisme_caracterise_par_graphe()
    cst21_quotients_egales()
    assert len(theorie_ensembles().axiomes) == 22
