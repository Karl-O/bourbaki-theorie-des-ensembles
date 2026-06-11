"""Tests MIROIR — LEMME L3 : { L0, L2 } ⊢ bon_ordre_intervalle(a).

Couvre le module NEUF ensembles_bien_ordonne_lemme_2_ordre_clause :
  • lemme_0_ordre_predicat / lemme_2_clause : L0_pred, L2 == les deux conjoints de L3.
  • bon_ordre_intervalle_de_ordre_et_clause : { L0_pred, L2 } ⊢ L3   [SEQUENT VISÉ].
  • bon_ordre_intervalle_conditionnelle_close : ⊢ ( L0 ⇒ ( L2 ⇒ L3 ) ) [THÉORÈME CLOS].
  • bon_ordre_intervalle_depuis_clause : { L2 } ⊢ L3 (L0 fourni par preuve, SALVAGE).

INVARIANT vérifié : theorie_ensembles() = 22 ; aucune tautologie/affaibli ; L3 ==
bon_ordre_intervalle(a) == la conjonction stricte de ses deux moitiés.
"""
from bourbaki.logique.formule import impl
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import composantes_conjonction

import bourbaki.cardinaux.ensembles_bien_ordonne_lemme_2_ordre_clause as L3M
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    bon_ordre_intervalle,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal import (
    report_clause_plus_petit,
)


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  L0_pred et L2 sont EXACTEMENT les deux conjoints de L3 = bon_ordre_intervalle(a)
# ─────────────────────────────────────────────────────────────────────────────
def test_moities_sont_les_conjoints_de_L3():
    g, d = composantes_conjonction(bon_ordre_intervalle("a"))
    assert L3M.lemme_0_ordre_predicat("a") == g
    assert L3M.lemme_2_clause("a") == d


def test_L0_pred_est_la_conclusion_du_theoreme_ordre_clos():
    """L0_pred == conclusion de relation_ordre_dans_intervalle(a) (la partie ORDRE, CLOS)."""
    L0 = relation_ordre_dans_intervalle("a")
    assert L0.est_clos                       # la partie ORDRE est INCONDITIONNELLE
    assert L3M.lemme_0_ordre_predicat("a") == L0.conclusion


def test_L2_est_report_clause_plus_petit():
    assert L3M.lemme_2_clause("a") == report_clause_plus_petit("a")


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 SEQUENT VISÉ : { L0_pred, L2 } ⊢ bon_ordre_intervalle(a)
# ─────────────────────────────────────────────────────────────────────────────
def test_sequent_vise_ordre_et_clause():
    thm = L3M.bon_ordre_intervalle_de_ordre_et_clause("a")
    L0_pred = L3M.lemme_0_ordre_predicat("a")
    L2 = L3M.lemme_2_clause("a")
    # EXACTEMENT 2 hypothèses : les deux moitiés.
    assert not thm.est_clos
    assert thm.hypotheses == frozenset({L0_pred, L2})
    # conclusion EXACTEMENT L3.
    assert thm.conclusion == bon_ordre_intervalle("a")
    # garde-fou : la conclusion N'EST PAS l'une des prémisses (pas une identité affaiblie).
    assert thm.conclusion != L0_pred
    assert thm.conclusion != L2


# ─────────────────────────────────────────────────────────────────────────────
#  CONDITIONNELLE CLOSE : ⊢ ( L0 ⇒ ( L2 ⇒ L3 ) )   [THÉORÈME SANS HYPOTHÈSE]
# ─────────────────────────────────────────────────────────────────────────────
def test_conditionnelle_close():
    cond = L3M.bon_ordre_intervalle_conditionnelle_close("a")
    assert cond.est_clos                       # plus AUCUNE hypothèse
    assert not cond.hypotheses
    L0_pred = L3M.lemme_0_ordre_predicat("a")
    L2 = L3M.lemme_2_clause("a")
    L3 = bon_ordre_intervalle("a")
    assert cond.conclusion == impl(L0_pred, impl(L2, L3))
    # NON vacueux : L3 ≠ L0_pred et L3 ≠ L2, donc pas une tautologie.
    assert L3 != L0_pred and L3 != L2


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 SALVAGE : { L2 } ⊢ bon_ordre_intervalle(a) — L0 fourni PAR PREUVE
# ─────────────────────────────────────────────────────────────────────────────
def test_depuis_clause_seule_hyp_est_L2():
    thm = L3M.bon_ordre_intervalle_depuis_clause("a")
    # CONDITIONNEL à la SEULE clause L2 (l'ordre étant prouvé) — exactement 1 hypothèse.
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    assert thm.hypotheses == frozenset({report_clause_plus_petit("a")})
    # conclusion EXACTEMENT L3.
    assert thm.conclusion == bon_ordre_intervalle("a")
    # garde-fou : la cible n'est PAS la clause (pas une identité affaiblie).
    assert thm.conclusion != report_clause_plus_petit("a")


def test_robuste_autre_variable():
    """Le lemme fonctionne pour un nom de cardinal arbitraire (paramétrage propre)."""
    thm = L3M.bon_ordre_intervalle_de_ordre_et_clause("c")
    g, d = composantes_conjonction(bon_ordre_intervalle("c"))
    assert thm.hypotheses == frozenset({g, d})
    assert thm.conclusion == bon_ordre_intervalle("c")
