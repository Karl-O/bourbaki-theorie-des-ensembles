"""Tests miroir de bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props (§III.5).

Vérifie que chaque THÉORÈME inconditionnel est CLOS (est_clos, 0 hypothèse), que sa
CONCLUSION est EXACTEMENT la cible visée (anti-affaibli : pas de tautologie déguisée),
que les ÉNONCÉS-CIBLES reportés sont des formules bien formées (non postulées), et que
theorie_ensembles() reste à 22 axiomes (INTANGIBLE).
"""
from bourbaki.logique.formule import (var, egal, et, impl, non, existe, libres_f)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire

import bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props as M


A, B, C, D = var("a"), var("b"), var("c"), var("d")


# ════════════════════════════════════════════════════════════════════════════
#  theorie_ensembles() INTANGIBLE = 22 axiomes
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  PONT  (X ≤ Y) ⇒ (Card X ≤ Card Y)
# ════════════════════════════════════════════════════════════════════════════
def test_le_ens_implique_le_card_clos():
    thm = M.le_ens_implique_le_card(var("X"), var("Y"))
    assert thm.est_clos
    cible = impl(inf_egal_card(var("X"), var("Y")),
                 inf_egal_card(cardinal(var("X")), cardinal(var("Y"))))
    assert thm.conclusion == cible


# ════════════════════════════════════════════════════════════════════════════
#  MONOTONIE de la somme cardinale binaire  (Prop. 3, cas binaire LARGE)
# ════════════════════════════════════════════════════════════════════════════
def test_somme_binaire_monotone_clos_et_cible():
    thm = M.somme_binaire_monotone()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = impl(et(inf_egal_card(A, B), inf_egal_card(C, D)),
                 inf_egal_card(somme_cardinale_binaire(A, C),
                               somme_cardinale_binaire(B, D)))
    assert thm.conclusion == cible


def test_somme_binaire_monotone_non_tautologie():
    # contenu non trivial : l'antécédent n'est pas la conclusion entière
    thm = M.somme_binaire_monotone()
    ante = et(inf_egal_card(A, B), inf_egal_card(C, D))
    assert thm.conclusion != ante
    # dépendance paramétrique réelle
    thm2 = M.somme_binaire_monotone("p", "q", "r", "s")
    assert thm.conclusion != thm2.conclusion


def test_somme_binaire_monotone_gauche_clos_et_cible():
    thm = M.somme_binaire_monotone_gauche()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = impl(inf_egal_card(A, B),
                 inf_egal_card(somme_cardinale_binaire(A, C),
                               somme_cardinale_binaire(B, C)))
    assert thm.conclusion == cible


def test_somme_binaire_monotone_droite_clos_et_cible():
    thm = M.somme_binaire_monotone_droite()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = impl(inf_egal_card(A, B),
                 inf_egal_card(somme_cardinale_binaire(C, A),
                               somme_cardinale_binaire(C, B)))
    assert thm.conclusion == cible


# ════════════════════════════════════════════════════════════════════════════
#  BORNES de la somme cardinale binaire  (a ≤ a+b, b ≤ a+b ; socle Prop. 2 ⇐)
# ════════════════════════════════════════════════════════════════════════════
def test_inf_egal_somme_gauche_binaire_clos_et_cible():
    thm = M.inf_egal_somme_gauche_binaire()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = inf_egal_card(cardinal(A), somme_cardinale_binaire(A, B))
    assert thm.conclusion == cible


def test_inf_egal_somme_droite_binaire_clos_et_cible():
    thm = M.inf_egal_somme_droite_binaire()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = inf_egal_card(cardinal(B), somme_cardinale_binaire(A, B))
    assert thm.conclusion == cible


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 2 (sens ⇐) :  (est_cardinal a et b = a+c) ⇒ a ≤ b
# ════════════════════════════════════════════════════════════════════════════
def test_prop2_somme_implique_inf_egal_clos_et_cible():
    thm = M.prop2_somme_implique_inf_egal()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = impl(est_cardinal(A),
                 impl(egal(B, somme_cardinale_binaire(A, C)), inf_egal_card(A, B)))
    assert thm.conclusion == cible


# ════════════════════════════════════════════════════════════════════════════
#  BORNE du PRODUIT cardinal binaire :  b ≠ ∅ ⇒ Card a ≤ a·b
# ════════════════════════════════════════════════════════════════════════════
def test_inf_egal_produit_binaire_clos_et_cible():
    thm = M.inf_egal_produit_binaire()
    assert thm.est_clos and len(thm.hypotheses) == 0
    cible = impl(non(egal(B, E.VIDE)),
                 inf_egal_card(cardinal(A), produit_cardinal_binaire(A, B)))
    assert thm.conclusion == cible


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS-CIBLES REPORTÉS / CONDITIONNELS — formules bien formées, NON postulées
# ════════════════════════════════════════════════════════════════════════════
def test_report_cibles_bien_formees():
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini

    f1 = M.somme_binaire_entier_cible()
    assert f1 == impl(et(est_fini(A), est_fini(B)),
                      est_fini(somme_cardinale_binaire(A, B)))

    f2 = M.produit_binaire_entier_cible()
    assert f2 == impl(et(est_fini(A), est_fini(B)),
                      est_fini(produit_cardinal_binaire(A, B)))

    f3 = M.prop3_somme_stricte_cible()
    assert f3 == impl(et(inf_egal_card(A, B), inf_strict_card(C, D)),
                      inf_strict_card(somme_cardinale_binaire(A, C),
                                      somme_cardinale_binaire(B, D)))

    f4 = M.cor4_difference_existe_unique_cible()
    assert f4 == impl(inf_egal_card(A, B),
                      existe("c", et(est_cardinal(var("c")),
                                     egal(B, somme_cardinale_binaire(A, var("c"))))))


def test_report_cibles_libres():
    assert sorted(libres_f(M.somme_binaire_entier_cible())) == ["a", "b"]
    assert sorted(libres_f(M.produit_binaire_entier_cible())) == ["a", "b"]
    assert sorted(libres_f(M.prop3_somme_stricte_cible())) == ["a", "b", "c", "d"]
    assert sorted(libres_f(M.cor4_difference_existe_unique_cible())) == ["a", "b"]
