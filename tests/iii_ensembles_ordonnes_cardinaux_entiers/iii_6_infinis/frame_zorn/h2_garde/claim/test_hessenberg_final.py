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
def test_chemin_complet_sans_aucun_residu():
    """🏆 Hessenberg SANS le paquet ψ et SANS AUCUN résidu.   [~400 s]

    ÉVOLUTION 2026-08-23 : ce test attendait UN résidu,
    `predecesseur_fini_universel`.  Le dépôt le PROUVE (Prop. 2 §III.5) — il
    n'était pas branché ; déchargé à la source dans `fini_downward_cardinal`,
    il a disparu de la chaîne.  Il ne reste donc QUE l'existence du maximal,
    que `hess_maximal_clos` décharge à son tour.

    Le test garde les deux propriétés qui comptent : plus aucun résidu (donc
    `residus_maximal` rend `None` — une conjonction vide n'a pas de formule),
    et l'hypothèse NON SATISFAITE, la ∀∀-clôture nue de `cardinal_pas_entre`,
    est absente."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
        cardinal_pas_entre,
    )
    t = hessenberg_par_extension("E", paquet_derive=True)
    assert t.conclusion == enonce_hessenberg("E")
    assert set(t.hypotheses) == {existence_maximal("E")},         "seule l'existence du maximal doit subsister : %d" % len(t.hypotheses)

    residus = _residus("E", paquet_derive=True)
    assert residus == [], "plus aucun résidu attendu : %d" % len(residus)
    assert residus_maximal("E", paquet_derive=True) is None,         "sans résidu, residus_maximal doit rendre None"

    nue = pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))
    assert nue not in t.hypotheses, "l'hypothèse non satisfaite est revenue"
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
    """🏆🏆🏆 { est_infini(Card E) } ⊢ enonce_hessenberg(E).   [~1 h 50]

    L'ABOUTISSEMENT : l'hypothèse du théorème de Bourbaki, et RIEN d'autre.

    ÉVOLUTION 2026-08-23 : ce test attendait DEUX hypothèses (profil [0,1]),
    la seconde étant `predecesseur_fini_universel`.  Elle est déchargée depuis
    que le dépôt la branche, et le profil tombe à [1] — une seule hypothèse,
    de surcroît la seule variable libre étant E.  C'est le critère « FAIT » du
    projet : 0 hypothèse non déchargée hors l'énoncé de Bourbaki lui-même."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_hessenberg_final import (
        hessenberg_final,
    )
    t = hessenberg_final("E")
    assert t.conclusion == enonce_hessenberg("E")
    assert len(t.hypotheses) == 1, "hyps : %d" % len(t.hypotheses)
    #  l'unique hypothèse ne mentionne que E : aucun témoin résiduel
    formes = sorted(len(libres_f(h)) for h in t.hypotheses)
    assert formes == [1], "profil des hypothèses inattendu : %s" % formes
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
