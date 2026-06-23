"""Tests — §III.5 PROPOSITION 2 : « tout entier ≠ 0 est un successeur » (INCONDITIONNEL).

Ferme le résidu `predecesseur_fini_universel` (Prop. 2) à 0 HYPOTHÈSE, via la surgery
`eq_retire_ajoute` (Eq(m, (m∖{x0})⊔{∅})) dont le cœur — la bijectivité du recollement
canonique de deux ensembles disjoints (Prop. 10 §II.4, eq_reunion_somme) — est CLOS.
Puis N_existe ⊢ coll(x, Fini x) à 0 hyp : ℕ EXISTE, INCONDITIONNEL."""
import pytest

from bourbaki.logique.formule import var, egal, et, impl, non, existe, pourtout, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal

from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    predecesseur_fini, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import _coll_fini

import bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 as P
from bourbaki.cardinaux.ensembles_reunion_somme_bijection import eq_reunion_somme


# ────────────────────────────────────────────────────────────────────────────
#  INVARIANT : theorie inchangée = 22
# ────────────────────────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  Prop. 10 §II.4 (binaire) : A∩B=∅ ⇒ Eq(A∪B, A⊔B)  — CLOS
# ────────────────────────────────────────────────────────────────────────────
def test_eq_reunion_somme_clos():
    ers = eq_reunion_somme(var("At"), var("Bt"))
    assert ers.est_clos and len(ers.hypotheses) == 0


# ────────────────────────────────────────────────────────────────────────────
#  helpers de surgery
# ────────────────────────────────────────────────────────────────────────────
def test_disjoint_diff_singleton_clos():
    d = P._disjoint_diff_singleton("Xt", "x0t")
    assert d.est_clos and len(d.hypotheses) == 0
    assert d.conclusion == egal(
        E.intersection(E.difference(var("Xt"), E.singleton(var("x0t"))),
                       E.singleton(var("x0t"))), E.VIDE)


def test_singleton_inclus_clos():
    s = P.singleton_inclus("x0t", "Et")
    assert s.est_clos and len(s.hypotheses) == 0


def test_eq_retire_ajoute_clos():
    """eq_retire_ajoute : (x0∈X) ⇒ Eq(X, (X∖{x0})⊔{∅})  est INCONDITIONNEL (0 hyp)."""
    era = P.eq_retire_ajoute("Xt", "x0t")
    assert era.est_clos and len(era.hypotheses) == 0


def test_m_egal_successeur_card_diff_clos():
    me = P.m_egal_successeur_card_diff("mt", "x0t")
    assert me.est_clos and len(me.hypotheses) == 0


def test_k_inf_strict_m_clos():
    """k < m (depuis Fini m, est_cardinal(k), m=successeur(k)) est INCONDITIONNEL."""
    ks = P._k_inf_strict_m("mks", "kks")
    assert ks.est_clos and len(ks.hypotheses) == 0


# ────────────────────────────────────────────────────────────────────────────
#  🎯 PROPOSITION 2 — predecesseur_fini_universel  (INCONDITIONNEL)
# ────────────────────────────────────────────────────────────────────────────
def test_predecesseur_fini_universel_conclusion_exacte():
    """conclusion ÉGALE LITTÉRALEMENT predecesseur_fini_universel(k='kpred') — la VRAIE
    Prop. 2 (vraie pour TOUT m fini > 0), PAS une tautologie."""
    pf = P.predecesseur_fini_universel_preuve()
    assert pf.conclusion == predecesseur_fini_universel(k="kpred")
    # NON vacuité : la conclusion n'est aucune des hypothèses (et il n'y en a aucune)
    assert pf.conclusion not in pf.hypotheses


def test_predecesseur_fini_universel_clos():
    """Prop. 2 CLOSE, 0 hyp (theorie=22, rien postulé)."""
    pf = P.predecesseur_fini_universel_preuve()
    assert pf.est_clos and len(pf.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  🎯🎯🎯 ℕ EXISTE — INCONDITIONNEL
# ────────────────────────────────────────────────────────────────────────────
def test_N_existe_conclusion_coll_fini():
    n = P.N_existe()
    assert n.conclusion == _coll_fini("x")
    assert n.conclusion not in n.hypotheses


def test_N_existe_clos_inconditionnel():
    """coll(x, Fini x) à 0 HYPOTHÈSE : ℕ existe INCONDITIONNELLEMENT.  theorie=22."""
    n = P.N_existe()
    assert n.est_clos and len(n.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22
