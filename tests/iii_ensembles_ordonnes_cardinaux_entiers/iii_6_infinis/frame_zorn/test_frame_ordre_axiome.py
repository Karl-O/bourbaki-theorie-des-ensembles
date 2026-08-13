"""Tests — axiome DÉFINITIONNEL du graphe d'ordre Γ𝔉 (Hessenberg, Zorn E.III.48)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, equiv
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_ordre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import (
    frame_ordre_membre, frame_ordre_membre_t, theorie_frame_ordre,
    _corps_frame_ordre,
)


def test_theorie_ensembles_reste_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_theorie_frame_ordre_dediee_un_axiome():
    assert len(theorie_frame_ordre().axiomes) == 1


def test_frame_ordre_membre_clos_et_correct():
    th = frame_ordre_membre()
    assert th.est_clos
    assert th.hypotheses == frozenset()
    vE, vp, vq = var("E"), var("p"), var("q")
    expected = equiv(appartient(E.couple(vp, vq), frame_ordre(vE)),
                     _corps_frame_ordre(vE, vp, vq))
    assert th.conclusion == expected


def test_frame_ordre_membre_t_terme_safe():
    vE, vp, vq = var("Ebis"), var("pbis"), var("qbis")
    th = frame_ordre_membre_t(vE, vp, vq)
    assert th.est_clos
    expected = equiv(appartient(E.couple(vp, vq), frame_ordre(vE)),
                     _corps_frame_ordre(vE, vp, vq))
    assert th.conclusion == expected
