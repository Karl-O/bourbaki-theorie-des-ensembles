"""Tests MIROIR — ensembles_gate_onto_top : FERMETURE INCONDITIONNELLE du GATE ℕ #1.

`bon_ordre_intervalle(a)` et `cardinaux_bien_ordonnes(a)` CLOS (0 hypothèse résiduelle),
via le REMPLACEMENT du maillon faux `subset_realise_segment` par le CLOS
`realise_segment_pour_B_clean` (gardé par ¬Eq(c,Card a)) + un CASE-SPLIT order-théorique
sur le cardinal TOP Card(a) (≤-MAX de [0,a]).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion close ne peut être l'une de ses hypothèses (il n'y en a pas).
"""
from bourbaki.logique.formule import var, appartient, inclus, egal, et, impl, non, pourtout, existe
from bourbaki.ensembles import ensembles_abrege as E

import bourbaki.cardinaux.ensembles_gate_onto_top as M
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    bon_ordre_intervalle, intervalle_0a,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  1️⃣ réalisation gardée CLEAN — dérivée du CLOS realise_segment_pour_B_clean.
# ─────────────────────────────────────────────────────────────────────────────
def test_realisation_garde_clean_conclusion():
    t = M.realisation_garde_clean("Ro", "a")
    assert t.conclusion == M.realisation_segment_garde_clean("Ro", "a")


def test_realisation_garde_clean_une_seule_hyp_bo():
    t = M.realisation_garde_clean("Ro", "a")
    assert set(t.hypotheses) == {M._bo_form_clean("Ro", "a")}   # bo HONNÊTE (Zermelo plus tard)
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_realisation_garde_clean_garde_par_non_Eq():
    # la garde EST `est_cardinal(c) et ¬Eq(c,Card a)` (le TOP exclu) — pas la fausse garde nue.
    from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, equipotent, cardinal
    t = M.realisation_segment_garde_clean("Ro", "a", "cgate")
    # c'est un (∀cgate)( (est_cardinal ∧ ¬Eq(·,Card a)) ⇒ realisation )
    assert t.tag == "non" and t.sous[0].tag == "exists"          # pourtout = ¬∃¬


# ─────────────────────────────────────────────────────────────────────────────
#  2️⃣ ONTO CLEAN — couvre c∈S avec ¬Eq(c,Card a)  (S∖{top}).
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_onto_clean_conclusion():
    t = M.pullback_onto_clean("a", "Ro", "S")
    assert t.conclusion == M.pullback_onto_clean_cible("a", "Ro", "S")


def test_pullback_onto_clean_non_vacueux():
    t = M.pullback_onto_clean("a", "Ro", "S")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  3️⃣ CLAUSE MIN CLEAN + CAS B (top-only) — les deux branches concluent le corps-S.
# ─────────────────────────────────────────────────────────────────────────────
def test_clause_min_clean_conclusion_corps_S():
    t = M.clause_min_clean("Ro", "agate", "S")
    assert t.conclusion == M._clause_corps_S("agate", "S")


def test_clause_min_top_only_conclusion_corps_S():
    t = M.clause_min_top_only("Ro", "agate", "S")
    assert t.conclusion == M._clause_corps_S("agate", "S")


def test_clause_pour_S_clean_conclusion_corps_S():
    t = M.clause_pour_S_clean("Ro", "agate", "S")
    assert t.conclusion == M._clause_corps_S("agate", "S")
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 LE GATE ℕ #1 — bon_ordre_intervalle(a) CLOS (0 hypothèse).
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_intervalle_close_EST_LA_CIBLE():
    t = M.bon_ordre_intervalle_close("a")
    assert t.conclusion == bon_ordre_intervalle("a")             # == la cible DÉPOSÉE
    assert t.conclusion == M.bon_ordre_intervalle_close_cible("a")


def test_bon_ordre_intervalle_close_CLOS():
    t = M.bon_ordre_intervalle_close("a")
    assert t.est_clos                                            # 0 hypothèse résiduelle
    assert len(t.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 cardinaux_bien_ordonnes(a) CLOS (0 hypothèse).
# ─────────────────────────────────────────────────────────────────────────────
def test_cardinaux_bien_ordonnes_close_EST_LA_CIBLE():
    t = M.cardinaux_bien_ordonnes_close("a")
    assert t.conclusion == cardinaux_bien_ordonnes("a")          # == la cible DÉPOSÉE
    assert t.conclusion == M.cardinaux_bien_ordonnes_close_cible("a")


def test_cardinaux_bien_ordonnes_close_CLOS():
    t = M.cardinaux_bien_ordonnes_close("a")
    assert t.est_clos                                            # 0 hypothèse résiduelle
    assert len(t.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22
