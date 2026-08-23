# -*- coding: utf-8 -*-
"""Miroir du PARAMÉTRAGE de division_pas_recomposition (R-12, étape 4).

`division_pas_recomposition` accepte désormais une différence quelconque, sous
la forme (terme, preuve de « b + diff = a »). Par défaut elle retrouve
`diff_somme` et son comportement historique ; avec `diff_cardinale` elle porte
la même conclusion, ce qui ouvre le recâblage de la division euclidienne sur une
différence dont le τ garantit `est_cardinal`.

Le premier test est une NON-RÉGRESSION ; le second établit que la preuve
n'utilise de la différence que son ÉQUATION, jamais sa construction — c'est
pourquoi le port est mécanique.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.soustraction_cardinale.ensembles_diff_cardinale import (
    diff_cardinale, diff_cardinale_equation,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_pas import (
    division_pas_recomposition, division_pas_recomposition_cible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import (
    _pas_grand, enonce_pas_grand,
)


def _diff_et_equation():
    """(diff_cardinale, preuve de « b + diff = a ») — le couple que les
    fonctions paramétrées attendent."""
    va, vb = var("a"), var("b")
    d = diff_cardinale(va, vb)
    rec = N.modus_ponens(diff_cardinale_equation(va, vb),
                         symetrie(va, somme_cardinale_binaire(vb, d)))
    return d, rec


def test_non_regression_appel_historique():
    """L'appel sans `diff` retrouve exactement le comportement d'origine. [~6 s]"""
    t = division_pas_recomposition("a", "b", "q", "r")
    assert t.conclusion == division_pas_recomposition_cible("a", "b", "q", "r")
    assert len(t.hypotheses) == 2, "hyps : %d" % len(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_port_sur_diff_cardinale():
    """🎯 La même conclusion avec `diff_cardinale`.   [instantané]

    La recomposition n'utilise de la différence que « b + diff = a ». Fournir
    une AUTRE différence munie de cette équation suffit donc — et c'est ce qui
    rend le recâblage de la division mécanique plutôt que coûteux."""
    va, vb = var("a"), var("b")
    d = diff_cardinale(va, vb)
    rec = N.modus_ponens(diff_cardinale_equation(va, vb),
                         symetrie(va, somme_cardinale_binaire(vb, d)))
    t = division_pas_recomposition("a", "b", "q", "r", diff=d, rec=rec)
    assert t.conclusion == division_pas_recomposition_cible("a", "b", "q", "r"), \
        "le port doit conclure la MÊME cible"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_non_regression_pas_grand():
    """`_pas_grand` sans `diff` reste identique.   [~23 s]"""
    t = _pas_grand("a", "b")
    assert t.conclusion == enonce_pas_grand("a", "b")[1]
    assert len(t.hypotheses) == 4, "hyps : %d" % len(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pas_grand_porte_sur_diff_cardinale():
    """🎯 `_pas_grand` conclut la MÊME relation avec `diff_cardinale`.  [~21 s]

    Le pas « a ≥ b » de la récurrence forte ne dépend donc pas du choix de la
    différence — seulement de son équation. C'est ce qui permettra de porter
    `_strong_step` sans réécrire la démonstration de Bourbaki."""
    d, rec = _diff_et_equation()
    t = _pas_grand("a", "b", diff=d, rec_bd=rec)
    assert t.conclusion == enonce_pas_grand("a", "b")[1],         "le port doit conclure la MÊME relation R{a}"
    assert len(E.theorie_ensembles().axiomes) == 22
