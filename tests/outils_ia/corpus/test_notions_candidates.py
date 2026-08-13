# -*- coding: utf-8 -*-
"""Tests — l'organe qui PROPOSE des définitions.

Ces tests vérifient une capacité, pas un théorème : la machine retrouve-t-elle
seule les notions que nous avons posées à la main ? C'est un test qu'on peut
perdre, ce qui en fait un test."""
from __future__ import annotations

import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from outils_ia.conjectures.goldbach import est_premier
from outils_ia.corpus.notions_candidates import (
    abreviation, candidates, corpus_recherche, normalise, sous_formules,
)


def test_les_abreviations_sont_reconnues():
    """`et`, `⇒`, `∀` sont des ABRÉVIATIONS — leurs entrailles n'en sont pas.

    Défaut mesuré à la première version : miner les sous-formules brutes
    remontait des `¬¬(¬… ∨ ¬…)` de 60 nœuds vus 24 fois — de l'échafaudage
    syntaxique, pas des notions. Ce test verrouille la correction."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, et, impl, pourtout,
    )
    a, b = egal(var("a"), var("a")), egal(var("b"), var("b"))
    assert abreviation(et(a, b))[0] == "et"
    assert abreviation(impl(a, b))[0] == "impl"
    assert abreviation(pourtout("x", a))[0] == "pourtout"
    #   une conjonction ne doit produire QUE le sommet, pas ses intermédiaires
    noms = [abreviation(s)[0] if abreviation(s) else s.tag
            for s in sous_formules(et(a, b))]
    assert "ou" not in noms, "un intermédiaire d'abréviation a été remonté"


@pytest.mark.slow
def test_la_machine_retrouve_les_notions_posees_a_la_main():
    """🎯 Les notions du dépôt remontent SEULES du minage du corpus.

    `est_premier`, `est_fini` et `premier_ent` ont été définies par des humains.
    L'organe ne les connaît pas : il compte des sous-formules récurrentes et les
    score par compression. Qu'elles arrivent en tête est la mesure qu'il
    fonctionne.

    Lent : il reconstruit tout le corpus `recherche/`."""
    from recherche.goldbach.crible import premier_ent

    enonces, _ = corpus_recherche()
    assert len(enonces) >= 10, "corpus trop maigre pour conclure"
    top = candidates(enonces, top=30)
    trouve = {c for (_g, _n, _t, c) in top}

    for nom, ref in (
        ("est_premier (habit d1/q1)", normalise(est_premier(var("z"), d="d1", q="q1"))),
        ("est_fini", normalise(est_fini(var("z")))),
        ("premier_ent", normalise(premier_ent(var("z"), d="d1", q="q1"))),
    ):
        assert ref in trouve, "notion non retrouvée : %s" % nom


@pytest.mark.slow
def test_les_deux_habits_alpha_comptent_pour_deux_notions():
    """LE RÉSULTAT INATTENDU, et il faut le garder.

    `est_premier` apparaît DEUX FOIS au classement — une par graphie de liants
    (`d1/q1` et `d2/q2`). L'organe redécouvre donc seul le problème des habits
    α, et il le CHIFFRE : c'est la plus grosse redondance du corpus.

    C'est exactement ce qui a coûté des heures le 12 août (pont d'habit à
    paramétrer). Si ce test tombe un jour parce que les deux graphies ont été
    unifiées, ce sera une bonne nouvelle — il faudra alors le réécrire, pas le
    supprimer."""
    enonces, _ = corpus_recherche()
    top = candidates(enonces, top=30)
    trouve = {c for (_g, _n, _t, c) in top}
    h1 = normalise(est_premier(var("z"), d="d1", q="q1"))
    h2 = normalise(est_premier(var("z"), d="d2", q="q2"))
    assert h1 in trouve and h2 in trouve
    assert h1 != h2, "les deux habits sont devenus la même formule"
