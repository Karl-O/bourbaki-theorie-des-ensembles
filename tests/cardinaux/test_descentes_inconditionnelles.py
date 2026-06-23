"""Tests — §III.6.3 DESCENTES INCONDITIONNELLES 2𝔟=𝔟 et 3𝔟=𝔟.

Vérifie que les deux théorèmes
  deux_b_egal_b_inconditionnel(b)  : (est_card 𝔟 et est_infini 𝔟 et 𝔟·𝔟=𝔟) ⇒ 𝔟+𝔟=𝔟
  trois_b_egal_b_inconditionnel(b) : (est_card 𝔟 et est_infini 𝔟 et 𝔟·𝔟=𝔟) ⇒ 𝔟+(𝔟+𝔟)=𝔟
sont CLOS (0 hypothèse ouverte : l'antécédent 3-conjoint est déchargé par
loi_deduction), de conclusion exactement l'énoncé attendu, non vacueux, et que le
noyau reste à theorie_ensembles() == 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire as _pcb,
)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire, somme_disjointe,
)

from bourbaki.cardinaux.ensembles_descentes_inconditionnelles import (
    deux_b_egal_b_inconditionnel, trois_b_egal_b_inconditionnel,
)


def _antecedent(vb):
    return et(et(est_cardinal(vb), est_infini(vb)),
              egal(_pcb(vb, vb), vb))


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_deux_b_egal_b_inconditionnel():
    thm = deux_b_egal_b_inconditionnel("b")
    vb = var("b")
    bb = somme_cardinale_binaire(vb, vb)
    cible = impl(_antecedent(vb), egal(bb, vb))
    assert thm.est_clos, f"deux_b_egal_b_inconditionnel non clos : {thm.hypotheses}"
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible, "conclusion ≠ énoncé attendu"
    assert thm.conclusion not in thm.hypotheses
    # theorie inchangée après construction
    assert len(E.theorie_ensembles().axiomes) == 22


def test_trois_b_egal_b_inconditionnel():
    thm = trois_b_egal_b_inconditionnel("b")
    vb = var("b")
    # 3𝔟 = somme_cardinale_binaire(𝔟, 𝔟⊔𝔟)  (forme EXACTE de trois_b_egal_b ; 2ᵉ sommant = ENSEMBLE)
    threeb = somme_cardinale_binaire(vb, somme_disjointe(vb, vb))
    cible = impl(_antecedent(vb), egal(threeb, vb))
    assert thm.est_clos, f"trois_b_egal_b_inconditionnel non clos : {thm.hypotheses}"
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible, "conclusion ≠ énoncé attendu"
    assert thm.conclusion not in thm.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
