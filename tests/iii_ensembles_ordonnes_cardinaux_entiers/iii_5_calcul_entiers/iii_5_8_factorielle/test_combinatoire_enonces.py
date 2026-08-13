# -*- coding: utf-8 -*-
"""Tests §III.5.8 — énoncés combinatoires (E III.42-44), forme multiplicative."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, app
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur, DEUX)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire as PCB)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SCB)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_combinatoire_enonces import (
    enonce_prop10_injections, enonce_permutations, enonce_cor1_binomial,
    enonce_symetrie_binomiale, enonce_prop13_pascal,
    enonce_prop14_couples_larges, enonce_prop14_couples_stricts,
    enonce_prop14_lien, enonce_somme_premiers_entiers,
    enonce_prop15_recurrence)


def fact(t):
    return app("factorielle", t)


def C(n, p):
    return app("binom", n, p)


n, p = var("n"), var("p")
nm, npq = var("nmoinsm"), var("nmoinsp")


def test_prop10_forme_multiplicative():
    e = enonce_prop10_injections(var("Inm"), fact, n, nm)
    assert e == egal(PCB(var("Inm"), fact(nm)), fact(n))


def test_permutations():
    assert enonce_permutations(var("Perm"), fact, n) == egal(var("Perm"), fact(n))


def test_cor1_binomial_multiplicatif():
    e = enonce_cor1_binomial(C(n, p), fact, n, p, npq)
    assert e == egal(PCB(C(n, p), PCB(fact(p), fact(npq))), fact(n))


def test_symetrie():
    assert enonce_symetrie_binomiale(C, n, p, npq) == egal(C(n, p), C(n, npq))


def test_pascal():
    e = enonce_prop13_pascal(C, n, p)
    assert e == egal(C(successeur(n), successeur(p)),
                     SCB(C(n, successeur(p)), C(n, p)))


def test_prop14_et_lien():
    assert enonce_prop14_couples_larges(var("an"), n) == \
        egal(PCB(DEUX, var("an")), PCB(n, successeur(n)))
    assert enonce_prop14_couples_stricts(var("bn"), n, var("nm1")) == \
        egal(PCB(DEUX, var("bn")), PCB(n, var("nm1")))
    assert enonce_prop14_lien(var("an"), var("bn"), n) == \
        egal(var("an"), SCB(n, var("bn")))


def test_somme_premiers_entiers():
    # 2·Σi = n(n+1) — la forme multiplicative du célèbre n(n+1)/2
    e = enonce_somme_premiers_entiers(var("Si"), n)
    assert e == egal(PCB(DEUX, var("Si")), PCB(n, successeur(n)))


def test_prop15_recurrence():
    def A(h, x):
        return app("Acount", h, x)
    e = enonce_prop15_recurrence(A, var("h"), n, var("hm1"), var("nm1"))
    assert e == egal(A(var("h"), n),
                     SCB(A(var("h"), var("nm1")), A(var("hm1"), n)))


def test_convention_binomiale_nulle():
    """E III.43 L.4-6 : p > n ⇒ (n p) = 0 (garde d'ordre cardinal)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_strict_card)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        ZERO)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl, egal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_combinatoire_enonces import (
        enonce_convention_binomiale_nulle)
    e = enonce_convention_binomiale_nulle(C, n, p)
    assert e == impl(inf_strict_card(n, p), egal(C(n, p), ZERO))
