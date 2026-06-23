"""Tests §II.3.8 — Théorème 1 f) : descente d'injectivité de f''=f'∘f vers f
(forme repliée) et rétraction de f'' propagée sous f(·) (forme repliée).

Module testé :
bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_theoreme1_f.

Contrôles, pour CHAQUE théorème : conclusion == cible (construite indépendamment),
ENSEMBLE EXACT des hypothèses résiduelles (ici ∅ : les deux théorèmes sont CLOS,
toutes leurs prémisses étant déchargées dans les implications), et invariant
theorie_ensembles()==22.
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient,
                                       impl, pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections import ensembles_theoreme1_f as TF


# ── Théorème 1 f) — descente d'injectivité de f''=f'∘f vers f (valeurs) ────────
def test_theoreme1_f_injective_conclusion_egale_cible():
    th = TF.theoreme1_f_injective_valeur()
    assert th.conclusion == TF.cible_theoreme1_f_injective_valeur()


def test_theoreme1_f_injective_forme_explicite():
    # injective_dans(F'',A) ⇒ (∀x,x')((x∈A ∧ x'∈A ∧ f''(x)=f''(x')) ⇒ x=x')
    vF, vFp, vA = var("F"), var("Fp"), var("A")
    vx, vxp = var("x"), var("xp")
    comp = E.composee(vFp, vF)
    fppx, fppxp = E.valeur(comp, vx), E.valeur(comp, vxp)
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), egal(fppx, fppxp))
    inner = impl(ante, egal(vx, vxp))
    attendu = impl(E.injective_dans(comp, vA),
                   pourtout("x", pourtout("xp", inner)))
    assert TF.theoreme1_f_injective_valeur().conclusion == attendu


def test_theoreme1_f_injective_clos_sans_hyp_parasite():
    th = TF.theoreme1_f_injective_valeur()
    # CLOS : injective_dans(F'',A) déchargée, conclusion jamais en hyp, ∅ résiduel.
    assert th.est_clos
    assert set(th.hypotheses) == set()
    assert set(th.hypotheses) == TF.hypotheses_theoreme1_f_injective_valeur()
    assert E.injective_dans(E.composee(var("Fp"), var("F")), var("A")) not in th.hypotheses
    assert th.conclusion not in th.hypotheses


def test_theoreme1_f_injective_autres_lettres():
    th = TF.theoreme1_f_injective_valeur("g", "h", "E")
    assert th.conclusion == TF.cible_theoreme1_f_injective_valeur("g", "h", "E")
    assert th.est_clos


# ── Théorème 1 f) — rétraction de f''=f'∘f propagée sous f(·) (valeurs) ────────
def test_theoreme1_f_retraction_conclusion_egale_cible():
    th = TF.theoreme1_f_retraction_valeur()
    assert th.conclusion == TF.cible_theoreme1_f_retraction_valeur()


def test_theoreme1_f_retraction_forme_explicite():
    # est_retraction(R'',F'',A) ⇒ ((x∈A) ⇒ f(r''(f''(x))) = f(x))
    vR, vF, vFp, vA = var("Rpp"), var("F"), var("Fp"), var("A")
    vx = var("x")
    comp = E.composee(vFp, vF)
    fppx = E.valeur(comp, vx)
    lhs = E.valeur(vF, E.valeur(vR, fppx))
    inner = impl(appartient(vx, vA), egal(lhs, E.valeur(vF, vx)))
    attendu = impl(E.est_retraction(vR, comp, vA), inner)
    assert TF.theoreme1_f_retraction_valeur().conclusion == attendu


def test_theoreme1_f_retraction_clos_sans_hyp_parasite():
    th = TF.theoreme1_f_retraction_valeur()
    # CLOS : est_retraction(R'',F'',A) déchargée, x∈A déchargée, ∅ résiduel.
    assert th.est_clos
    assert set(th.hypotheses) == set()
    assert set(th.hypotheses) == TF.hypotheses_theoreme1_f_retraction_valeur()
    comp = E.composee(var("Fp"), var("F"))
    assert E.est_retraction(var("Rpp"), comp, var("A")) not in th.hypotheses
    assert th.conclusion not in th.hypotheses


def test_theoreme1_f_retraction_autres_lettres():
    th = TF.theoreme1_f_retraction_valeur("s", "g", "h", "E")
    assert th.conclusion == TF.cible_theoreme1_f_retraction_valeur("s", "g", "h", "E")
    assert th.est_clos


# ── garde-fou : les deux conclusions sont distinctes (non triviales) ───────────
def test_theoreme1_f_conclusions_distinctes():
    c1 = TF.theoreme1_f_injective_valeur().conclusion
    c2 = TF.theoreme1_f_retraction_valeur().conclusion
    assert c1 != c2


def test_theorie_ensembles_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
