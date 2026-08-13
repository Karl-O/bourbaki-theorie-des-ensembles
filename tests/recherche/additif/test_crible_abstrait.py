# -*- coding: utf-8 -*-
"""Tests — le crible abstrait, et la thèse qu'il porte.

Ces tests ne vérifient pas seulement que des théorèmes ferment. Ils vérifient
une AFFIRMATION SUR NOS PROPRES RÉSULTATS : que la symétrie du crible ne
contient aucune arithmétique. La façon de le vérifier est de la rejouer sur
des prédicats sans aucun rapport entre eux — si elle ferme à chaque fois, elle
ne parlait pas des nombres premiers."""
from __future__ import annotations

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    est_pair_propre,
)
from outils_ia.conjectures.goldbach import est_premier
from recherche.additif.crible_abstrait import (
    appartenance, cible_partenaire, rencontre, symetrie_additive,
)


def _clos(th):
    return th.est_clos and not th.hypotheses


def test_symetrie_sur_un_predicat_totalement_opaque():
    """⊢ la symétrie, avec `S(x) := x ∈ 𝕊` et `𝕊` sans aucune propriété.

    C'est le cas le plus général : rien n'est supposé de `S`. Que la preuve
    ferme ici signifie qu'elle n'a jamais eu besoin d'ouvrir `S`."""
    th = symetrie_additive()
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_goldbach_est_une_instance():
    """LA MÊME preuve, avec `S := est_premier`. Aucune ligne ne change.

    « Goldbach est une instance » n'est donc pas une affirmation de la prose :
    c'est une exécution. Le module de `recherche/goldbach/` démontre le même
    énoncé, en payant en plus un pont d'habit α — lequel est un artefact de
    notation, pas une étape mathématique."""
    th = symetrie_additive(S=lambda x: est_premier(x, d="d1", q="q1"))
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_un_predicat_sans_rapport_ferme_aussi():
    """La même preuve avec `S := être pair` — un ensemble pour lequel la
    question additive est TRIVIALE.

    C'est le test qui porte la thèse : une démonstration qui ne distingue pas
    les nombres premiers d'un ensemble sans structure ne peut pas servir à
    démontrer Goldbach. Ce n'est pas un défaut de la preuve, c'est une
    propriété de l'énoncé qu'elle établit."""
    th = symetrie_additive(S=lambda x: est_pair_propre(x, q="qpa"))
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_les_enonces_sont_bien_formes():
    """Garde-fou de forme : la rencontre et la cible partenaire sont des ∃."""
    assert rencontre().tag == "exists"
    assert cible_partenaire().tag == "exists"
    assert appartenance(E.VIDE).tag == "in"
