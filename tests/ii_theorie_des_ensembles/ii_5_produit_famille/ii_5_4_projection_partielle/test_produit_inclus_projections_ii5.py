"""Tests §II.5.3 (remarque A ⊂ ∏_ι pr_ι⟨A⟩) — brique pointwise.

  ⊢ ( A ⊂ ∏(f,I) ∧ F∈A ∧ α∈I ) ⇒ ( pr_α(F) ∈ X_α ).

Vérifie la conclusion EXACTE (== cible reconstruite à la main ET == _cible du
module), la clôture (0 hypothèse honnête déchargée) et l'invariant
theorie_ensembles()==22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, appartient, inclus)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_4_projection_partielle import (
    ensembles_produit_inclus_projections_ii5 as P)


def _cible_attendue():
    vf, vI, vA, vF, valpha = var("f"), var("I"), var("A"), var("F"), var("alpha")
    prod = E.produit_famille(vf, vI)
    X_alpha = E.valeur_famille(vf, valpha)
    pr_alpha_F = E.valeur(vF, valpha)
    hyp = et(et(inclus(vA, prod), appartient(vF, vA)), appartient(valpha, vI))
    return impl(hyp, appartient(pr_alpha_F, X_alpha))


def test_coordonnee_dans_facteur_conclusion():
    thm = P.coordonnee_dans_facteur()
    assert thm.conclusion == _cible_attendue()


def test_conclusion_egale_cible_du_module():
    thm = P.coordonnee_dans_facteur()
    assert thm.conclusion == P._cible()


def test_est_clos_et_zero_hypothese():
    thm = P.coordonnee_dans_facteur()
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    # la conclusion n'est jamais une hypothèse
    assert thm.conclusion not in thm.hypotheses


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
