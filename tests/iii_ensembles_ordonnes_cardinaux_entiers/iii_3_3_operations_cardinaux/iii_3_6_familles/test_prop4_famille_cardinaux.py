# -*- coding: utf-8 -*-
"""Test §III.3.3 Prop.4 (n°101) — énoncés posés ; dérivation bloquée par verrou-τ.

Les ÉNONCÉS de Prop.4 (Card(∏E)=∏Card E, Card(∑E)=∑Card E) sont posés fidèlement.
La dérivation est reportée (verrou-τ : graphe_terme_valeur casse sur le terme-valeur
Card(E_ι) binder-riche) — cf. docstring de carte_cardinaux_valeur."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_prop4_famille_cardinaux import (
    _famille_cardinaux, enonce_carte_cardinaux_valeur,
    enonce_prop4_produit, enonce_prop4_somme, carte_cardinaux_valeur)


def test_enonces_bien_formes():
    """Les énoncés de Prop.4 (produit/somme) et de la famille des cardinaux se CONSTRUISENT."""
    assert _famille_cardinaux("E", "I") is not None
    assert enonce_carte_cardinaux_valeur().tag == "="
    assert enonce_prop4_produit().tag == "="
    assert enonce_prop4_somme().tag == "="


def test_carte_cardinaux_valeur_debloquee():
    """✅ {i0∈I} ⊢ A(i0)=Card(E_i0) — le « verrou-τ » était un artefact pré-fix subst."""
    th = carte_cardinaux_valeur()
    assert th.conclusion == enonce_carte_cardinaux_valeur()
    assert len(th.hypotheses) == 1


def _ancien_test_verrou_tau_obsolete():
    """La dérivation de la valeur est BLOQUÉE (verrou-τ) — lève explicitement (documenté)."""
    with pytest.raises(NotImplementedError):
        carte_cardinaux_valeur()


def test_theorie_inchangee():
    _famille_cardinaux("E", "I")
    enonce_prop4_produit()
    assert len(E.theorie_ensembles().axiomes) == 22
