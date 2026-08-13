# -*- coding: utf-8 -*-
"""Tests — T3b somme d'une famille CONSTANTE = a×I (Prop.6 Cor.2, E III.27).
Un test par palier P1-P4 ; theorie_ensembles() reste à 22 axiomes (invariant)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_constante import (
    famille_constante, hypothese_pont_const, famille_constante_valeur,
    fam_const_egale, somme_constante_egale_produit, card_somme_constante)


def test_theorie_22():
    """L'invariant : AUCUN axiome ajouté aux 22 par ce chantier."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p1_famille_constante_valeur():
    """P1 {i0∈I} ⊢ fam_const(i0) = a — valeur nom-basée, 1 hypothèse."""
    thm = famille_constante_valeur()
    assert thm.conclusion == egal(E.valeur(famille_constante(), var("i0cs")),
                                  var("Acs"))
    assert thm.hypotheses == frozenset({appartient(var("i0cs"), var("Ics"))})


def test_p2_fam_const_egale():
    """P2 : Γ⊢t∈I ⟹ Γ∪{HFc} ⊢ valeur_famille(fam_const,t)=a — au TERME."""
    tt = var("tcs")
    thm_in = N.assume(appartient(tt, var("Ics")))
    thm = fam_const_egale(thm_in, tt)
    assert thm.conclusion == egal(E.valeur_famille(famille_constante(), tt),
                                  var("Acs"))
    assert thm.hypotheses == frozenset({appartient(tt, var("Ics")),
                                        hypothese_pont_const()})


def test_p3_somme_constante_egale_produit():
    """🎯 T3b {HFc} ⊢ somme_famille(fam_const,I) = a×I — égalité d'ENSEMBLES."""
    thm = somme_constante_egale_produit()
    assert thm.conclusion == egal(
        E.somme_famille(famille_constante(), var("Ics")),
        E.produit(var("Acs"), var("Ics")))
    assert thm.hypotheses == frozenset({hypothese_pont_const()})


def test_p4_card_somme_constante():
    """P4 {HFc} ⊢ Σ_{ι∈I} a = Card(a×I) — LHS/RHS terme-à-terme (Cor.2 : ab)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        somme_cardinale)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire)
    thm = card_somme_constante()
    assert thm.conclusion == egal(
        somme_cardinale(famille_constante(), var("Ics")),
        produit_cardinal_binaire(var("Acs"), var("Ics")))
    assert thm.hypotheses == frozenset({hypothese_pont_const()})
    assert len(E.theorie_ensembles().axiomes) == 22
