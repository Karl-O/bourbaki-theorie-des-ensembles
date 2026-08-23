# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_hessenberg_final.py — 🏆 Hessenberg a·a = a.

Ce que le test verrouille : l'énoncé de Bourbaki (Th. 2, E III.47) est obtenu
sous DEUX hypothèses seulement, toutes deux explicites — l'existence du
maximal (que `hess_maximal` prouve, certifié) et les trois résidus honnêtes
quantifiés sur le maximal."""
import pytest

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_unpack_garde import (
    existence_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_hessenberg_final import (
    residus_maximal, hessenberg_par_extension, _residus,
)


def test_un_seul_residu_honnete():
    """🎯 Le CLAIM ne laisse plus qu'UN résidu : le garde ∀U (le paquet ψ).

    Les deux autres sont tombés le 2026-08-23 — l'absorption 𝔟+𝔟=𝔟 est DÉRIVÉE
    de la bijection φ₀ (LEÇON 16), le transport était déjà CLOS en amont
    (GAP B).  Et ce résidu unique EST exactement `donnees_extension`."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_endgame import (
        donnees_extension,
    )
    residus = _residus("E")
    assert len(residus) == 1
    assert residus[0] == donnees_extension("E", "Smx", "phimx")


def test_hessenberg_par_extension():
    """🏆🏆 { existence_maximal, residus_maximal } ⊢ E infini ⇒ Card E·Card E = Card E."""
    t = hessenberg_par_extension("E")
    assert t.conclusion == enonce_hessenberg("E")
    assert set(t.hypotheses) == {existence_maximal("E"), residus_maximal("E")}, \
        "hypothèses inattendues : l'assemblage a fui"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_chemin_complet_un_seul_residu():
    """🏆 Hessenberg SANS le paquet ψ et SANS hypothèse fausse.   [~400 s]

    Depuis le recâblage de `z_infini_derive` sur la version GARDÉE de la
    downward-closure (ANOMALIES 2026-08-23), le chemin complet ne porte plus
    qu'UN résidu, CLOS : `predecesseur_fini_universel` (Prop. 2 §III.5), une
    hypothèse VRAIE quoique non encore prouvée.

    Ce test garde les deux propriétés qui comptent : le résidu est clos (il ne
    mentionne aucun témoin, donc rien n'obstrue les éliminations), et
    l'hypothèse NON SATISFAITE — la ∀∀-clôture nue de `cardinal_pas_entre` —
    est absente."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, pourtout, libres_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
        cardinal_pas_entre,
    )
    t = hessenberg_par_extension("E", paquet_derive=True)
    assert t.conclusion == enonce_hessenberg("E")
    assert len(t.hypotheses) == 2
    assert existence_maximal("E") in t.hypotheses

    residus = _residus("E", paquet_derive=True)
    assert len(residus) == 1, "un seul résidu attendu : %d" % len(residus)
    assert not libres_f(residus[0]), "le résidu doit être CLOS"

    nue = pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))
    assert nue not in t.hypotheses, "l'hypothèse non satisfaite est revenue"
    assert nue != residus[0], "le résidu EST l'hypothèse non satisfaite"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_hess_maximal_clos():
    """🎯🎯🎯 { est_infini(Card E) } ⊢ (∃m) element_maximal.   [~1 h 25]

    hess_maximal portait DEUX hypothèses ; la seconde, donnees_recollement,
    est devenue un théorème via les onze données du recollement."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_hessenberg_final import (
        hess_maximal_clos,
    )
    t = hess_maximal_clos("E")
    assert len(t.hypotheses) == 1, "hyps : %d" % len(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_hessenberg_final():
    """🏆🏆🏆 { E infini, predecesseur_fini_universel } ⊢ enonce_hessenberg(E).

    L'aboutissement : l'hypothèse même du théorème de Bourbaki, plus un unique
    résidu CLOS et vrai (Prop. 2 §III.5), non encore dérivé.   [~10 min]"""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_hessenberg_final import (
        hessenberg_final,
    )
    t = hessenberg_final("E")
    assert t.conclusion == enonce_hessenberg("E")
    assert len(t.hypotheses) == 2, "hyps : %d" % len(t.hypotheses)
    #  l'une ne parle que de E, l'autre est CLOSE : aucun témoin résiduel
    formes = sorted(len(libres_f(h)) for h in t.hypotheses)
    assert formes == [0, 1], "profil des hypothèses inattendu : %s" % formes
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
