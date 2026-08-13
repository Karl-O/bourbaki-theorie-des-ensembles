# -*- coding: utf-8 -*-
"""Tests §III.5.7 — énoncés du développement de base b (E III.40)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, pourtout, app)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    est_isomorphisme_ordre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, UN)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_7_developpement_base_b.ensembles_developpement_base_b import (
    enonce_prop8_iso, enonce_majoration_a_inf_b_puiss_a, enonce_developpement,
    enonce_chiffre_borne, enonce_premier_chiffre_non_nul)


def test_prop8_est_l_iso_verbatim():
    fk, Ek, iv = var("fk"), var("Ek"), var("Iv")

    def R_lex(u, w):
        return app("ordre_lex", u, w)

    def R_int(u, w):
        return app("ordre_int", u, w)

    assert enonce_prop8_iso(fk, Ek, R_lex, iv, R_int) == \
        est_isomorphisme_ordre(fk, Ek, iv, R_lex, R_int)


def test_majoration():
    b = var("b")
    a = var("adev")
    attendu = pourtout("adev", impl(
        est_fini(a), inf_strict_card(a, exposant_cardinal_binaire(b, a))))
    assert enonce_majoration_a_inf_b_puiss_a("adev", b) == attendu


def test_developpement_et_bornes():
    a, s = var("a"), app("somme_dev", var("rh"), var("b"))
    assert enonce_developpement(a, s) == egal(a, s)
    assert enonce_chiffre_borne(var("rh"), var("bm1")) == \
        inf_egal_card(var("rh"), var("bm1"))
    assert enonce_premier_chiffre_non_nul(var("r0")) == \
        inf_egal_card(UN, var("r0"))
