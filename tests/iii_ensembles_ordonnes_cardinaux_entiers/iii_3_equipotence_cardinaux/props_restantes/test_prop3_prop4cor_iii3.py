"""Tests — §III.3 Proposition 3 (surjection ⇒ Card≤) et Corollaire de la Prop 4
(Card(⋃E_ι) ≤ ∑ Card(E_ι))."""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop3_prop4cor_iii3 import (
    prop3_surjection_inf_egal, cible_prop3_surjection_inf_egal,
    prop4cor_card_reunion_inf_egal_somme, cible_prop4cor_card_reunion_inf_egal_somme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import somme_cardinale, cardinal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


def _hyps_set(thm):
    return set(thm.hypotheses)


# ── PROPOSITION 3 ─────────────────────────────────────────────────────────────
def test_prop3_conclusion_est_inf_egal_card():
    t = prop3_surjection_inf_egal()
    assert t.conclusion == cible_prop3_surjection_inf_egal()  # inf_egal_card(Y, X)


def test_prop3_hypotheses_honnetes_exactes():
    """Exactement 4 hyps honnêtes ; l'injectivité de s est DÉRIVÉE, non supposée."""
    t = prop3_surjection_inf_egal()
    vS, vF, vX, vY = E.var('S'), E.var('F'), E.var('X'), E.var('Y')
    attendu = {
        E.est_retraction(vF, vS, vY),          # s section de f sur Y
        E.est_fonctionnel(vS),                 # s fonctionnel
        E.egal(E.dom(vS), vY),                 # dom s = Y
        E.inclus(E.image(vS, vY), vX),         # image(s,Y) ⊂ X
    }
    assert _hyps_set(t) == attendu


def test_prop3_non_vacuous():
    """La conclusion n'est PAS l'une des hypothèses (non trivial/vacuous)."""
    t = prop3_surjection_inf_egal()
    assert t.conclusion not in _hyps_set(t)


# ── COROLLAIRE de la PROPOSITION 4 ───────────────────────────────────────────
def test_prop4cor_conclusion():
    t = prop4cor_card_reunion_inf_egal_somme()
    assert t.conclusion == cible_prop4cor_card_reunion_inf_egal_somme()


def test_prop4cor_cible_est_card_reunion_inf_egal_somme():
    """somme_cardinale(A,I) = Card(⊔E_ι) : la cible est Card(⋃) ≤ ∑ Card(E_ι)."""
    A, I = E.var('A'), E.var('I')
    assert somme_cardinale(A, I) == cardinal(E.somme_famille(A, I))


def test_prop4cor_non_vacuous():
    t = prop4cor_card_reunion_inf_egal_somme()
    assert t.conclusion not in _hyps_set(t)


# ── Garde noyau ──────────────────────────────────────────────────────────────
def test_theorie_inchangee_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
