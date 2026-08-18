# -*- coding: utf-8 -*-
"""Tests — la commande de vérification unique.

Ce qu'on teste ici n'est pas que le dépôt va bien : c'est que le VÉRIFICATEUR
dit la vérité. Un vérificateur qui ment est pire que pas de vérificateur, et
ce projet en a la preuve — trois notifications « exit 0 » se sont avérées
être des timeouts. Les tests ci-dessous verrouillent les deux propriétés qui
comptent : il n'annonce jamais vert ce qui n'a pas tourné, et un échec réel
est bloquant."""
from __future__ import annotations

from outils_ia.audit.verifie import (
    AXIOMES_ATTENDUS, Ligne, rapport, verifie_axiomes, verifie_marqueurs,
    verifie_tests,
)


def test_une_suite_non_lancee_n_est_JAMAIS_verte():
    """🎯 LA RÈGLE CARDINALE.

    Sans `--tests`, la suite n'a pas tourné : la ligne doit dire NON_LANCE,
    jamais OK, et le verdict global doit le refuser explicitement. C'est
    exactement l'erreur qui a coûté trois faux « tout va bien » à ce projet."""
    L = verifie_tests(False, False)
    assert L.etat == "NON_LANCE"
    assert L.etat != "OK"
    txt = rapport([Ligne("axiomes", "OK", "22"), L])
    assert "NON LANCE" in txt
    assert "VERT" not in txt


def test_tout_vert_ne_se_dit_que_si_TOUT_a_tourne():
    """Le verdict VERT exige qu'aucune ligne ne soit en attente."""
    txt = rapport([Ligne("axiomes", "OK", "22"), Ligne("tests", "OK", "4204 passed")])
    assert "VERT" in txt


def test_un_echec_est_bloquant_et_nomme():
    """Un ÉCHEC doit apparaître dans le verdict AVEC le nom de la ligne —
    un rapport qui dit « quelque chose ne va pas » sans dire quoi oblige à
    tout relire, donc ne sert à rien."""
    L = Ligne("axiomes", "ECHEC", "23 au lieu de 22")
    assert L.bloquant
    txt = rapport([L, Ligne("tests", "OK", "4204 passed")])
    assert "ECHEC" in txt and "axiomes" in txt


def test_une_alerte_n_est_pas_bloquante():
    """Les reports suspects ALERTENT sans bloquer : ce sont des pistes à
    vérifier, pas des cassures. Les confondre ferait crier au loup à chaque
    commit et le vérificateur serait ignoré — c'est ainsi qu'une barrière
    meurt."""
    L = Ligne("reports", "ALERTE", "51 suivis, 6 suspects")
    assert not L.bloquant
    txt = rapport([L, Ligne("tests", "OK", "4204 passed")])
    assert "VERT" in txt


def test_l_invariant_des_22_axiomes_est_verifie_pour_de_vrai():
    """🎯 Le seul test de ce fichier qui touche le dépôt réel.

    `theorie_ensembles()` doit valoir 22 : c'est l'invariant que CLAUDE.md
    déclare intouchable. S'il bouge, tout le reste devient suspect."""
    L = verifie_axiomes()
    assert L.etat == "OK", L.detail
    assert L.detail == str(AXIOMES_ATTENDUS)


def test_les_marqueurs_sont_comptes_sans_planter():
    """Le compte de trous est un indicateur de DIRECTION, pas un seuil : on
    ne fige donc aucune valeur ici (elle monte quand on formalise sans
    annoter, et c'est normal). On vérifie seulement que la mesure existe."""
    L = verifie_marqueurs()
    assert L.etat == "OK", L.detail
    assert "marqueurs" in L.detail and "trous" in L.detail
