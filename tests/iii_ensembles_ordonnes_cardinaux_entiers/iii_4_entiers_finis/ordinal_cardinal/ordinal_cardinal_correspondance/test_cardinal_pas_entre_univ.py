"""Tests — UNIVERSALISATION du LEMME N « pas de cardinal STRICTEMENT entre c et c+1 »
(gate #2 de ℕ — report #2 de N_collectivise_final).

Vérifie :
  • cardinal_pas_entre_garde : ⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b,c)  (clos, 0 hyp) ;
  • cardinal_pas_entre_univ  : ⊢ (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )
                               (clos, 0 hyp) == cible gardée, ≠ bare universel ;
  • le résidu honnête est EXACTEMENT la garde est_cardinal(b) (le théorème gardé et le
    bare universel ne diffèrent QUE par cette garde) ;
  • non-vacuité (la conclusion n'est pas dans les hypothèses) ;
  • theorie_ensembles() = 22  (intangible).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl, pourtout
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinal_pas_entre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_cardinal_pas_entre_univ import (
    cardinal_pas_entre_garde, cardinal_pas_entre_univ,
    cible_cardinal_pas_entre_univ, cible_bare_universel,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_garde_clos():
    """⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b,c)  (clos, 0 hyp)."""
    t = cardinal_pas_entre_garde()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    ante, cons = antecedent_consequent(t.conclusion)
    assert ante == est_cardinal(var("b"))
    assert cons == cardinal_pas_entre(var("b"), var("c"))


def test_univ_clos_et_cible():
    """⊢ (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )  (clos, 0 hyp, == cible)."""
    t = cardinal_pas_entre_univ()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    # match LITTÉRAL avec la cible gardée
    assert t.conclusion == cible_cardinal_pas_entre_univ()
    # forme explicite : (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )
    attendu = pourtout("c", pourtout("b",
                       impl(est_cardinal(var("b")),
                            cardinal_pas_entre(var("b"), var("c")))))
    assert t.conclusion == attendu


def test_univ_n_est_pas_le_bare_universel():
    """Le théorème CLOS est la forme GARDÉE, PAS le bare (∀c)(∀b)cardinal_pas_entre(b,c)
    (qui n'est pas un théorème) ; le résidu honnête est EXACTEMENT la garde est_cardinal(b)."""
    t = cardinal_pas_entre_univ()
    bare = cible_bare_universel()
    assert t.conclusion != bare
    # le résidu se réduit EXACTEMENT à la garde : sous (∀c)(∀b), le corps gardé est
    # impl(est_cardinal(b), corps_bare), où corps_bare = cardinal_pas_entre(b,c).
    corps_garde = impl(est_cardinal(var("b")), cardinal_pas_entre(var("b"), var("c")))
    assert cible_cardinal_pas_entre_univ() == pourtout("c", pourtout("b", corps_garde))
    assert bare == pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))


def test_non_vacuite():
    """La conclusion n'est PAS parmi les hypothèses (théorème non vide / non vacueux)."""
    t = cardinal_pas_entre_univ()
    assert t.conclusion not in set(t.hypotheses)


def test_le_bare_universel_est_la_forme_attendue_en_aval():
    """Le bare (∀c)(∀b)cardinal_pas_entre(b,c) que nous N'apportons PAS est EXACTEMENT
    la formule assumée par ensembles_recurrence_C61._preuve_step (report #2)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n import ensembles_recurrence_C61 as C61
    attendu_aval = pourtout("c", pourtout("b",
                            C61.cardinal_pas_entre(var("b"), var("c"))))
    assert cible_bare_universel() == attendu_aval
