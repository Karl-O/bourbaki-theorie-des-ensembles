"""Tests MIROIR — LEMME L0 (PRÉ-REQUIS) :
    ⊢ est_relation_ordre_dans( ≤_induit , [0,a] )   CLOS (INCONDITIONNEL).

Couvre le module NEUF ensembles_bien_ordonne_lemme_0_ordre_total (preuve INDÉPENDANTE
de la « partie ORDRE » de est_bien_ordonne(≤_induit,[0,a]), 1er des deux conjoints) :
  • les 4 paliers (transitif, antisymétrique, réflexif-implicite, réflexif-dans-[0,a])
    sont CLOS et == les prédicats correspondants ;
  • lemme_0_ordre_total(a) == est_relation_ordre_dans(R_induit,[0,a],xo,yo,zo) == le
    1er conjoint de bon_ordre_intervalle(a)  [SEQUENT VISÉ, INCONDITIONNEL].

INVARIANT vérifié : theorie_ensembles() = 22 ; aucune tautologie/affaibli (la
conclusion est une CONJONCTION stricte des 4 prédicats d'ordre, pas une hypothèse).
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    ordre_induit_intervalle, intervalle_0a, bon_ordre_intervalle,
)
import bourbaki.cardinaux.ensembles_bien_ordonne_lemme_0_ordre_total as L0M


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  LES 4 PALIERS, chacun CLOS et == son prédicat d'ordre
# ─────────────────────────────────────────────────────────────────────────────
def test_transitivite_close_et_exacte():
    R = ordre_induit_intervalle("a")
    thm = L0M.transitivite_induit("a")
    assert thm.est_clos
    assert thm.conclusion == E.ordre_transitif(R, "xo", "yo", "zo")


def test_antisymetrie_close_et_exacte():
    R = ordre_induit_intervalle("a")
    thm = L0M.antisymetrie_induit("a")
    assert thm.est_clos
    assert thm.conclusion == E.ordre_antisymetrique(R, "xo", "yo")


def test_reflexif_implicite_clos_et_exact():
    R = ordre_induit_intervalle("a")
    thm = L0M.reflexif_implicite_induit("a")
    assert thm.est_clos
    assert thm.conclusion == E.ordre_reflexif_implicite(R, "xo", "yo")


def test_reflexive_dans_intervalle_close_et_exacte():
    R = ordre_induit_intervalle("a")
    interv = intervalle_0a("a")
    thm = L0M.reflexive_dans_intervalle("a")
    assert thm.est_clos
    assert thm.conclusion == E.est_reflexive_dans_ordre(R, interv, "xo")


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 SEQUENT VISÉ : ⊢ est_relation_ordre_dans( ≤_induit , [0,a] )  INCONDITIONNEL
# ─────────────────────────────────────────────────────────────────────────────
def test_sequent_vise_clos_et_inconditionnel():
    thm = L0M.lemme_0_ordre_total("a")
    assert thm.est_clos                    # 0 hypothèse — INCONDITIONNEL
    assert not thm.hypotheses


def test_conclusion_est_le_predicat_ordre_dans():
    R = ordre_induit_intervalle("a")
    interv = intervalle_0a("a")
    thm = L0M.lemme_0_ordre_total("a")
    assert thm.conclusion == E.est_relation_ordre_dans(R, interv, "xo", "yo", "zo")


def test_conclusion_est_le_premier_conjoint_de_bon_ordre_intervalle():
    """L0 == 1er conjoint de bon_ordre_intervalle(a) (la « partie ORDRE » du bon ordre)."""
    bo = bon_ordre_intervalle("a")
    # bo = et(L0, clause) = non(ou(non L0, non clause)) ; extraire le 1er conjoint.
    premier = bo.sous[0].sous[0].sous[0]
    thm = L0M.lemme_0_ordre_total("a")
    assert thm.conclusion == premier


# ─────────────────────────────────────────────────────────────────────────────
#  GARDE-FOU anti-tautologie / anti-affaibli : la conclusion est la CONJONCTION
#  STRICTE des 4 prédicats, distincte de chacun d'eux pris isolément.
# ─────────────────────────────────────────────────────────────────────────────
def test_non_tautologie_conjonction_stricte():
    R = ordre_induit_intervalle("a")
    interv = intervalle_0a("a")
    c = L0M.lemme_0_ordre_total("a").conclusion
    assert c != E.ordre_transitif(R, "xo", "yo", "zo")
    assert c != E.ordre_antisymetrique(R, "xo", "yo")
    assert c != E.ordre_reflexif_implicite(R, "xo", "yo")
    assert c != E.est_reflexive_dans_ordre(R, interv, "xo")
    assert c != E.est_relation_ordre(R, "xo", "yo", "zo")  # ≠ la moitié sans réflexif-dans-E


# ─────────────────────────────────────────────────────────────────────────────
#  ROBUSTESSE : autre nom de cardinal
# ─────────────────────────────────────────────────────────────────────────────
def test_robuste_autre_variable():
    R = ordre_induit_intervalle("c")
    interv = intervalle_0a("c")
    thm = L0M.lemme_0_ordre_total("c")
    assert thm.est_clos
    assert thm.conclusion == E.est_relation_ordre_dans(R, interv, "xo", "yo", "zo")
