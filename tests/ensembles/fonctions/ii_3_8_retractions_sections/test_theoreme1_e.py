"""Tests §II.3.8 — Théorème 1 e) : descente d'injectivité de f' vers f (valeurs).

Module testé :
bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_theoreme1_e.

Contrôles : conclusion == cible (construite indépendamment), ENSEMBLE EXACT de
l'hypothèse C46 honnête résiduelle {(∀v)(v∈A ⇒ f(v)∈B)} (jamais postulée, jamais
la conclusion en hyp, aucune hyp parasite, injective_dans(F',B) déchargée), et
invariant theorie_ensembles()==22.
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient,
                                       impl, pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections import ensembles_theoreme1_e as TE


def test_theoreme1_e_conclusion_egale_cible():
    th = TE.theoreme1_e_injective_valeur()
    assert th.conclusion == TE.cible_theoreme1_e_injective_valeur()


def test_theoreme1_e_forme_explicite():
    # injective_dans(F',B) ⇒ (∀x,x')((x∈A ∧ x'∈A ∧ f'(f(x))=f'(f(x'))) ⇒ f(x)=f(x'))
    vF, vFp, vA, vB = var("F"), var("Fp"), var("A"), var("B")
    vx, vxp = var("x"), var("xp")
    fx, fxp = E.valeur(vF, vx), E.valeur(vF, vxp)
    fpfx, fpfxp = E.valeur(vFp, fx), E.valeur(vFp, fxp)
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), egal(fpfx, fpfxp))
    inner = impl(ante, egal(fx, fxp))
    attendu = impl(E.injective_dans(vFp, vB),
                   pourtout("x", pourtout("xp", inner)))
    assert TE.theoreme1_e_injective_valeur().conclusion == attendu


def test_theoreme1_e_hypotheses_C46_honnetes():
    # hyp résiduelle EXACTE : {(∀v)(v∈A ⇒ f(v)∈B)} (happlique « f applique A dans B »).
    th = TE.theoreme1_e_injective_valeur()
    vF, vA, vB, vv = var("F"), var("A"), var("B"), var("v")
    happlique = pourtout("v", impl(appartient(vv, vA),
                                   appartient(E.valeur(vF, vv), vB)))
    assert set(th.hypotheses) == {happlique}
    assert set(th.hypotheses) == TE.hypotheses_theoreme1_e_injective_valeur()
    # garde-fou : injective_dans(F',B) DÉCHARGÉE (pas en hyp), conclusion pas en hyp.
    assert E.injective_dans(var("Fp"), vB) not in th.hypotheses
    assert th.conclusion not in th.hypotheses
    assert not th.est_clos   # séquent honnête : happlique résiduel


def test_theoreme1_e_autres_lettres():
    th = TE.theoreme1_e_injective_valeur("g", "h", "E", "C")
    assert th.conclusion == TE.cible_theoreme1_e_injective_valeur("g", "h", "E", "C")
    assert set(th.hypotheses) == TE.hypotheses_theoreme1_e_injective_valeur("g", "E", "C")


def test_theorie_ensembles_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
