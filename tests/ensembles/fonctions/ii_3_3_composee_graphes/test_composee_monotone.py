"""Tests §II.3.3 — MONOTONIE de la composée (Bourbaki E II.13, Remarque).

On APPELLE le théorème, on vérifie : conditionnel HONNÊTE (est_clos == False,
hypothèses == { G1⊂G2, G1'⊂G2' } reconstruites à la main), conclusion == cible
G1'∘G1 ⊂ G2'∘G2 (mêmes constructeurs : ∘ = composee, ⊂ = inclus), theorie == 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
import bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee_monotone as M


def test_composee_monotone_cible_et_hyps():
    t = M.composee_monotone()
    assert not t.est_clos                              # conditionnel honnête
    G1, G1p, G2, G2p = var("G1"), var("G1p"), var("G2"), var("G2p")
    # cible : G1'∘G1 ⊂ G2'∘G2   (∘ = composee(G', G))
    cible = inclus(E.composee(G1p, G1), E.composee(G2p, G2))
    assert t.conclusion == cible == M.composee_monotone_cible()
    # hypothèses == { G1⊂G2, G1'⊂G2' } reconstruites à la main
    assert set(t.hypotheses) == {inclus(G1, G2), inclus(G1p, G2p)}


def test_composee_monotone_theorie_inchangee():
    M.composee_monotone()
    assert len(theorie_ensembles().axiomes) == 22
