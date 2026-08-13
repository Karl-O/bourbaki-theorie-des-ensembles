# -*- coding: utf-8 -*-
"""Tests — disjonctions de produits (support du cadre-RÉUNION Hessenberg).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, appartient, pourtout,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_produits_disjoints import (
    produits_disjoints_premiere, produits_disjoints_seconde,
    disjoint_reunion_droite, inter_vide_depuis_disjonction,
    carre_disjoint_cadre_reunion,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_produits_disjoints_premiere():
    """{A∩B=∅ ∀-forme} ⊢ (∀u)¬(u∈A×C ∧ u∈B×D) — 1 hyp, non vacueux."""
    th = produits_disjoints_premiere()
    assert len(th.hypotheses) == 1
    assert th.conclusion not in th.hypotheses


def test_produits_disjoints_seconde():
    th = produits_disjoints_seconde()
    assert len(th.hypotheses) == 1
    assert th.conclusion not in th.hypotheses


def test_disjoint_reunion_droite():
    th = disjoint_reunion_droite()
    assert len(th.hypotheses) == 2
    assert th.conclusion not in th.hypotheses


def test_inter_vide_depuis_disjonction():
    """{disj} ⊢ A∩B=∅ — la forme ÉGALITÉ, par extensionnalité."""
    th = inter_vide_depuis_disjonction()
    assert th.conclusion == egal(E.intersection(var("A"), var("B")), E.VIDE)
    assert len(th.hypotheses) == 1


def test_carre_disjoint_cadre_reunion():
    """🎯 L5 : {(∀z)(z∈U⇒¬z∈S)} ⊢ (∀u)¬(u∈S² ∧ u∈F_r) — l'hyp 12 de B0 en réunion."""
    th = carre_disjoint_cadre_reunion()
    vS, vU, vu = var("S0"), var("Ucadre"), var("upd")
    F_r = E.reunion(E.produit(vS, vU),
                    E.reunion(E.produit(vU, vS), E.produit(vU, vU)))
    cible = pourtout("upd", non(et(appartient(vu, E.produit(vS, vS)),
                                   appartient(vu, F_r))))
    assert th.conclusion == cible
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22
