"""Tests des CLAUSES résiduelles (P2),(P3),(P4) de l'existence C60 (§III.2).

Couvre :
  • (P2) clause_P2 CLOSE (0 hyp) ;
  • (P3) clause_P3_ambiant CLOSE sous { est_bien_ordonne } SEUL ;
  • (P4) clause_P4_ambiant CLOSE (0 hyp) ;
  • l'EXISTENCE C60 complète, avec (P2) déchargée : { bo, clause_P3, clause_P4 } ;
  • non-vacuité, conclusions == énoncés nominaux, theorie_ensembles() == 22.
"""
from __future__ import annotations

from bourbaki.logique.formule import app, var
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import est_essai
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    clause_P2, clause_P3, clause_P4,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import couverture_totale
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_clauses import (
    coincidence_segment_realise,
    recursion_segment_realise, clause_P4_ambiant,
    couverture_segment_realise, clause_P3_ambiant,
    recursion_transfinie_existence_complet,
)


def _vh():
    """Règle OPAQUE Terme→Terme (motif du test déposé : app('rule', t))."""
    return lambda t: app("rule", t)


# ── (P2) clause_P2 CLOSE, 0 hyp ───────────────────────────────────────────────
def test_P2_clause_close():
    vh = _vh()
    p2 = coincidence_segment_realise(vh)
    assert p2.est_clos
    assert len(p2.hypotheses) == 0
    assert p2.conclusion == clause_P2(vh)


# ── (P4) clause_P4_ambiant CLOSE, 0 hyp ───────────────────────────────────────
def test_P4_clause_ambiant_close():
    vh = _vh()
    p4 = recursion_segment_realise(vh)
    assert p4.est_clos
    assert len(p4.hypotheses) == 0
    assert p4.conclusion == clause_P4_ambiant(vh)


# ── (P3) clause_P3_ambiant sous { est_bien_ordonne } SEUL ─────────────────────
def test_P3_clause_ambiant_bon_ordre():
    vh = _vh()
    p3 = couverture_segment_realise(vh)
    assert not p3.est_clos
    bo = E.est_bien_ordonne(_graphe_R("G"), var("E"))
    assert bo in p3.hypotheses
    assert len(p3.hypotheses) == 1
    assert p3.conclusion == clause_P3_ambiant(vh)
    # non vacuous
    assert p3.conclusion not in p3.hypotheses


# ── EXISTENCE C60 complète : (P2) déchargée, { bo, clause_P3, clause_P4 } ──────
def test_existence_complet_P2_dechargee():
    vh = _vh()
    r = recursion_transfinie_existence_complet(vh)
    ve = var("E")
    R = _graphe_R("G")
    couvert = couvert_essai(vh, R, ve)
    # conclusion EXACTE = existence (couverture totale)
    assert r.conclusion == couverture_totale(couvert, ve, "x0tf")
    # hypothèses restantes == { bo, clause_P3, clause_P4 } EXACTEMENT
    bo = E.est_bien_ordonne(R, ve)
    assert bo in r.hypotheses
    # les clauses sont bâties avec le binder x="x0tf" du théorème d'existence
    assert clause_P3(vh, x="x0tf") in r.hypotheses
    assert clause_P4(vh, x="x0tf") in r.hypotheses
    assert len(r.hypotheses) == 3
    # (P2) bien déchargée
    assert clause_P2(vh, x="x0tf") not in r.hypotheses
    # non vacuous
    assert r.conclusion not in r.hypotheses


# ── INVARIANT : theorie_ensembles() == 22 (noyau intact) ──────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22
