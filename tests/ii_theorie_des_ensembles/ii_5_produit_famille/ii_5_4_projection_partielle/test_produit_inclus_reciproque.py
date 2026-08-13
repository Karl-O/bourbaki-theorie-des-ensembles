"""Tests §II.5.4 — Cor. 3 : réciproque de la monotonie du produit (pointwise).

Vérifie la conclusion EXACTE (== cible reconstruite), les hypothèses (séquent
clos : aucune hypothèse pendante — le conditionnel est porté par l'antécédent)
et l'invariant theorie_ensembles() == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, appartient, inclus)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_4_projection_partielle import (
    ensembles_produit_inclus_reciproque as R)


def test_facteur_inclus_si_produit_inclus_conclusion():
    thm = R.facteur_inclus_si_produit_inclus("f", "g", "I", "F", "alpha", "a")
    vf, vg, vI, vF, valpha, va = (var("f"), var("g"), var("I"), var("F"),
                                  var("alpha"), var("a"))
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    Y_alpha = E.valeur_famille(vg, valpha)
    Fa = E.valeur(vF, valpha)
    hyp = et(et(et(inclus(prodX, prodY), appartient(valpha, vI)),
                appartient(vF, prodX)),
             egal(Fa, va))
    cible = impl(hyp, appartient(va, Y_alpha))
    assert thm.conclusion == cible


def test_cible_coincide():
    thm = R.facteur_inclus_si_produit_inclus()
    assert thm.conclusion == R._cible()


def test_est_clos_et_hypotheses_vides():
    # Le théorème est CLOS : les 4 antécédents honnêtes sont déchargés en
    # implication (loi_deduction).  Le statut CONDITIONNEL tient à l'antécédent
    # (témoin F = surjectivité de pr_α, Cor. 1), pas à une hypothèse pendante.
    thm = R.facteur_inclus_si_produit_inclus()
    assert thm.est_clos is True
    assert thm.hypotheses == frozenset()


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
