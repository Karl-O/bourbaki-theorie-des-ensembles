"""Tests — §III.3.6 : PROPOSITION 13 sens DIRECT, EXISTENCE DU COMPLÉMENT CARDINAL.

Ferme le report `existe_complement_cardinal` (seule hypothèse résiduelle du sens
direct de Prop 13) en CONSTRUISANT le complément c = a ∖ f⟨b⟩, puis DÉCHARGE le
report dans prop13_forward_conditionnel pour obtenir Prop 13 forward « fermée » sous
la SEULE garde honnête « a, b cardinaux et b ≤ a » (l'antécédent du Théorème 1).

Chaque test vérifie : la conclusion EST EXACTEMENT la cible, la clôture (.est_clos),
l'absence d'hypothèse résiduelle, la non-vacuité, et que le consequent dérivé EST
LITTÉRALEMENT le report `existe_complement_cardinal`.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, existe, impl, et
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes import ensembles_prop13_complement as P13
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
    existe_complement_cardinal,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card, cardinal,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire


def test_theorie_inchangee():
    """INVARIANT : la théorie reste à 22 axiomes (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


# ── EXISTENCE DU COMPLÉMENT CARDINAL — le cœur combinatoire ────────────────────
def test_existe_complement_depuis_inf_egal_clos():
    """⊢ (est_cardinal(b) et b≤a) ⇒ existe_complement_cardinal(b,a)   (CLOS, 0 hyp)."""
    t = P13.existe_complement_depuis_inf_egal("Bp13", "Ap13", "Cp13")
    assert t.est_clos
    assert t.hypotheses == frozenset()
    assert t.conclusion == P13.existe_complement_depuis_inf_egal_cible("Bp13", "Ap13", "Cp13")


def test_existe_complement_decharge_le_report():
    """Le consequent dérivé EST LITTÉRALEMENT le report existe_complement_cardinal."""
    t = P13.existe_complement_depuis_inf_egal("Bp13", "Ap13", "Cp13")
    ante, cons = antecedent_consequent(t.conclusion)
    # antécédent = (est_cardinal(b) et b≤a)
    assert ante == et(est_cardinal(var("Bp13")), inf_egal_card(var("Bp13"), var("Ap13")))
    # consequent = (∃c) Card(a) = somme_cardinale_binaire(b, c)  (le report EXACT)
    assert cons == existe_complement_cardinal("Bp13", "Ap13", "Cp13")


def test_existe_complement_non_vacuous():
    """NON vacueux : la conclusion n'est pas une simple hypothèse réintroduite."""
    t = P13.existe_complement_depuis_inf_egal("Bp13", "Ap13", "Cp13")
    assert t.conclusion not in t.hypotheses


# ── PROPOSITION 13 sens DIRECT — FERMÉE (report déchargé) ───────────────────────
def test_prop13_forward_ferme_clos():
    """⊢ (est_cardinal(a) et est_cardinal(b) et b≤a) ⇒ (∃c) a = b + c   (CLOS, 0 hyp)."""
    t = P13.prop13_forward_ferme("Bp13", "Ap13", "Cp13")
    assert t.est_clos
    assert t.hypotheses == frozenset()
    assert t.conclusion == P13.prop13_forward_ferme_cible("Bp13", "Ap13", "Cp13")


def test_prop13_forward_ferme_conclusion_est_prop13():
    """Le consequent EST EXACTEMENT le but Bourbaki de Prop 13 forward : (∃c) a = b + c."""
    t = P13.prop13_forward_ferme("Bp13", "Ap13", "Cp13")
    _, cons = antecedent_consequent(t.conclusion)
    but = existe("Cp13", egal(var("Ap13"),
                              somme_cardinale_binaire(var("Bp13"), var("Cp13"))))
    assert cons == but


def test_prop13_forward_ferme_non_vacuous():
    """NON vacueux : la conclusion n'est pas une simple hypothèse réintroduite."""
    t = P13.prop13_forward_ferme("Bp13", "Ap13", "Cp13")
    assert t.conclusion not in t.hypotheses
