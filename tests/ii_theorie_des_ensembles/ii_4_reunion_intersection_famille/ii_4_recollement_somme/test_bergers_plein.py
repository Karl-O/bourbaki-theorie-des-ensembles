# -*- coding: utf-8 -*-
"""Tests — T2 principe des BERGERS PLEIN Card(E)=Card(c×F) (Cor.2 E III.27 ∘
recollement S3).  Un test par palier P5-P7 ; theorie_ensembles()==22 (invariant)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    famille_fibres, somme_fibres, hypothese_fonctionnelle, hypothese_domaine,
    hypothese_valeurs, hypothese_pont_fam)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_bergers_plein import (
    hypothese_fibres_constantes, fam_fibre_constante,
    somme_fibres_egale_produit, bergers_plein)


def test_theorie_22():
    """L'invariant : AUCUN axiome ajouté aux 22 par ce chantier."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p5_fam_fibre_constante():
    """P5 : Γ⊢t∈F ⟹ Γ∪{HF,Hc} ⊢ valeur_famille(Xfib,t)=c — fibres au TERME."""
    tt = var("tcs")
    thm_in = N.assume(appartient(tt, var("Ffb")))
    thm = fam_fibre_constante(thm_in, tt)
    assert thm.conclusion == egal(E.valeur_famille(famille_fibres(), tt),
                                  var("cbg"))
    assert thm.hypotheses == frozenset({appartient(tt, var("Ffb")),
                                        hypothese_pont_fam(),
                                        hypothese_fibres_constantes()})


def test_p6_somme_fibres_egale_produit():
    """P6 {HF, Hc} ⊢ somme_famille(Xfib,F) = c×F — exactement 2 hypothèses."""
    thm = somme_fibres_egale_produit()
    assert thm.conclusion == egal(somme_fibres(),
                                  E.produit(var("cbg"), var("Ffb")))
    assert thm.hypotheses == frozenset({hypothese_pont_fam(),
                                        hypothese_fibres_constantes()})


def test_p7_bergers_plein():
    """🎯 T2 {Hf1,Hf2,Hf3,HF,Hc} ⊢ Card(E) = Card(c×F) = c·F — 5 hyps exactes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire)
    thm = bergers_plein()
    assert thm.conclusion == egal(cardinal(var("Efb")),
                                  produit_cardinal_binaire(var("cbg"), var("Ffb")))
    assert thm.hypotheses == frozenset({
        hypothese_fonctionnelle(), hypothese_domaine(), hypothese_valeurs(),
        hypothese_pont_fam(), hypothese_fibres_constantes()})
    assert len(E.theorie_ensembles().axiomes) == 22
