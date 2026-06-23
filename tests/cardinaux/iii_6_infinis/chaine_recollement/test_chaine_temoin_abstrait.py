"""Tests — §III.6.3 Hessenberg/Zorn : construction du témoin-majorant de chaîne
abstraite (union des projections ⋃S=⋃pr₁(C), ⋃φ=⋃pr₂(C))."""
from bourbaki.logique.i_1_termes_relations.formule import egal, et, existe, pourtout, appartient, impl, equiv, inclus, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.cardinaux.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, union_seconde,
    membre_union_premiere, membre_union_seconde,
    membre_donne_inclus_premiere, membre_donne_inclus_seconde,
    temoin_majore_membre,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_union_premiere_caracterisation():
    th = membre_union_premiere("Cch", "xch")
    vC, vx = var("Cch"), var("xch")
    gauche = appartient(vx, union_premiere(vC))
    droite = existe("punionpr", et(appartient(var("punionpr"), vC),
                                   appartient(vx, E.pr1(var("punionpr")))))
    assert th.conclusion == equiv(gauche, droite)
    assert not th.hypotheses


def test_membre_union_seconde_caracterisation():
    th = membre_union_seconde("Cch", "xch")
    vC, vx = var("Cch"), var("xch")
    gauche = appartient(vx, union_seconde(vC))
    droite = existe("punionpr", et(appartient(var("punionpr"), vC),
                                   appartient(vx, E.pr2(var("punionpr")))))
    assert th.conclusion == equiv(gauche, droite)
    assert not th.hypotheses


def test_inclus_premiere():
    th = membre_donne_inclus_premiere("Cch", "pmemb")
    vC, vp = var("Cch"), var("pmemb")
    assert th.conclusion == inclus(E.pr1(vp), union_premiere(vC))
    assert appartient(vp, vC) in th.hypotheses
    assert th.conclusion not in th.hypotheses


def test_inclus_seconde():
    th = membre_donne_inclus_seconde("Cch", "pmemb")
    vC, vp = var("Cch"), var("pmemb")
    assert th.conclusion == inclus(E.pr2(vp), union_seconde(vC))
    assert appartient(vp, vC) in th.hypotheses
    assert th.conclusion not in th.hypotheses


def test_temoin_majore_membre():
    th = temoin_majore_membre("E", "Cch", "pmemb")
    vE, vC, vp = var("E"), var("Cch"), var("pmemb")
    m = E.couple(union_premiere(vC), union_seconde(vC))
    assert th.conclusion == appartient(E.couple(vp, m), frame_ordre(vE))
    assert th.conclusion not in th.hypotheses
    # frame-memberships portées en hyps honnêtes
    assert appartient(vp, frame_pair(vE)) in th.hypotheses
    assert appartient(m, frame_pair(vE)) in th.hypotheses
