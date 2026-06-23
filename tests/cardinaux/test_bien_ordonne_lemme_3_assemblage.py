"""Tests MIROIR — LEMME L4 : { L3 } ⊢ cardinaux_bien_ordonnes(a).

Couvre le module NEUF ensembles_bien_ordonne_lemme_3_assemblage :
  • lemme_3_hypothese            : L3 == bon_ordre_intervalle(a).
  • lemme_3_conditionnelle_close : ⊢ ( L3 ⇒ cible )   [THÉORÈME CLOS].
  • L4_cardinaux_bien_ordonnes   : { L3 } ⊢ cardinaux_bien_ordonnes(a)   [SEQUENT VISÉ].

INVARIANT vérifié : theorie_ensembles() = 22 ; aucune tautologie/affaibli ; la SEULE
hypothèse résiduelle de L4 est la pièce ordinale L3 = bon_ordre_intervalle(a).
"""
from bourbaki.logique.formule import impl
from bourbaki.ensembles import ensembles_abrege as E

import bourbaki.cardinaux.ensembles_bien_ordonne_lemme_3_assemblage as L4M
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    cardinaux_bien_ordonnes_de_bon_ordre, bon_ordre_intervalle,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  L3 == bon_ordre_intervalle(a) (la pièce ordinale, unique report)
# ─────────────────────────────────────────────────────────────────────────────
def test_lemme_3_hypothese_est_bon_ordre_intervalle():
    assert L4M.lemme_3_hypothese("a") == bon_ordre_intervalle("a")
    # garde-fou : ce N'EST PAS la cible elle-même (sinon réduction triviale).
    assert L4M.lemme_3_hypothese("a") != cardinaux_bien_ordonnes("a")


# ─────────────────────────────────────────────────────────────────────────────
#  PRÉCONDITION empirique : la réduction réutilisée a bien 1 hyp == L3, concl == cible
# ─────────────────────────────────────────────────────────────────────────────
def test_reduction_reutilisee_est_conditionnelle_a_L3():
    red = cardinaux_bien_ordonnes_de_bon_ordre("a")
    assert not red.est_clos
    assert len(red.hypotheses) == 1
    assert list(red.hypotheses)[0] == bon_ordre_intervalle("a")
    assert red.conclusion == cardinaux_bien_ordonnes("a")


# ─────────────────────────────────────────────────────────────────────────────
#  CONDITIONNELLE CLOSE : ⊢ ( L3 ⇒ cible )   [THÉORÈME SANS HYPOTHÈSE]
# ─────────────────────────────────────────────────────────────────────────────
def test_conditionnelle_close():
    cond = L4M.lemme_3_conditionnelle_close("a")
    assert cond.est_clos                       # plus AUCUNE hypothèse
    assert not cond.hypotheses
    L3 = bon_ordre_intervalle("a")
    cible = cardinaux_bien_ordonnes("a")
    assert cond.conclusion == impl(L3, cible)  # exactement L3 ⇒ cible
    # NON vacueux : L3 ≠ cible, donc ce n'est pas une tautologie cible⇒cible.
    assert L3 != cible


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 L4 — SEQUENT VISÉ : { bon_ordre_intervalle(a) } ⊢ cardinaux_bien_ordonnes(a)
# ─────────────────────────────────────────────────────────────────────────────
def test_L4_sequent_vise():
    L4 = L4M.L4_cardinaux_bien_ordonnes("a")
    # conditionnel à L3 (la pièce ordinale) — exactement 1 hypothèse.
    assert not L4.est_clos
    assert len(L4.hypotheses) == 1
    # hypothèse EXACTEMENT { L3 }.
    assert L4.hypotheses == frozenset({bon_ordre_intervalle("a")})
    # conclusion EXACTEMENT la cible.
    assert L4.conclusion == cardinaux_bien_ordonnes("a")
    # garde-fou : la cible n'est PAS L3 (pas une identité affaiblie).
    assert L4.conclusion != bon_ordre_intervalle("a")


def test_L4_robuste_autre_variable():
    """Le lemme fonctionne pour un nom de cardinal arbitraire (paramétrage propre)."""
    L4 = L4M.L4_cardinaux_bien_ordonnes("c")
    assert L4.hypotheses == frozenset({bon_ordre_intervalle("c")})
    assert L4.conclusion == cardinaux_bien_ordonnes("c")
