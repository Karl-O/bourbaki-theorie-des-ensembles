"""Tests — §III.1.8 REMARQUE (E.III.1.8) : « plus grand élément ⟺ partie cofinale
réduite à un seul élément ».

On APPELLE chacun des trois théorèmes et on vérifie que :
  • sa conclusion est EXACTEMENT la cible reconstruite avec les MÊMES
    constructeurs (impl/equiv de plus_grand_element et est_cofinale) ;
  • il porte EXACTEMENT ses hypothèses HONNÊTES (jamais la conclusion en
    hypothèse → jamais vacuité) ;
  • theorie_ensembles reste = 22 axiomes."""
from __future__ import annotations

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_8_filtrants.ensembles_cofinale_plus_grand as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, equiv, appartient
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    plus_grand_element,
)


# ── cibles reconstruites avec les MÊMES constructeurs ─────────────────────────
def _pge():
    return plus_grand_element("Gcf", "Ecf", var("acf"), x="x")


def _cof():
    return M.cofinale_singleton("Gcf", "Ecf", "acf")


def _a_in_E():
    return appartient(var("acf"), var("Ecf"))


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── SENS DIRECT : plus_grand_element ⇒ est_cofinale(R_G,{a},E) ────────────────
def test_direct_conclusion_est_cible():
    t = M.plus_grand_implique_cofinale_singleton()
    assert t.conclusion == _cof()


def test_direct_une_hypothese_honnete():
    t = M.plus_grand_implique_cofinale_singleton()
    assert t.conclusion not in t.hypotheses           # pas de vacuité
    assert t.hypotheses == frozenset({_pge()})        # exactement plus_grand_element


# ── RÉCIPROQUE : a∈E et est_cofinale ⇒ plus_grand_element ─────────────────────
def test_reciproque_conclusion_est_cible():
    t = M.cofinale_singleton_implique_plus_grand()
    assert t.conclusion == _pge()


def test_reciproque_deux_hypotheses_honnetes():
    t = M.cofinale_singleton_implique_plus_grand()
    assert t.conclusion not in t.hypotheses
    assert t.hypotheses == frozenset({_a_in_E(), _cof()})


# ── ÉQUIVALENCE : a∈E ⊢ (plus_grand_element ⇔ est_cofinale) ───────────────────
def test_equivalence_conclusion_est_cible():
    t = M.plus_grand_equivaut_cofinale_singleton()
    # ⇔ := (pge⇒cof) et (cof⇒pge)
    assert t.conclusion == equiv(_pge(), _cof())
    assert t.conclusion == et(impl(_pge(), _cof()), impl(_cof(), _pge()))


def test_equivalence_une_hypothese_honnete():
    t = M.plus_grand_equivaut_cofinale_singleton()
    assert t.conclusion not in t.hypotheses
    assert t.hypotheses == frozenset({_a_in_E()})     # uniquement a∈E
