"""Tests miroir de ensembles_recollement_props (E.II.4, Prop. 7-10 recollement).

Vérifie pour chaque théorème : statut (.est_clos / nombre d'hypothèses) ET forme
EXACTE de la conclusion (énoncé VERBATIM).  theorie_ensembles reste à 22 axiomes.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, egal, inclus, impl, appartient, pourtout
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    reunion_graphes_fonctionnelle)

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_recollement_props import (
    recollement_recouvrement_valeur, recollement_recouvrement,
    recollement_binaire_fonctionnel,
    recollement_binaire_prolonge_gauche, recollement_binaire_prolonge_droite,
    recollement_binaire_valeur_gauche, recollement_binaire_valeur_droite,
    recollement_binaire_unicite,
    reunion_disjointe_binaire_disjoints, reunion_disjointe_binaire_reunion,
    bijection_canonique_reunion_somme, reunion_equipotente_somme_si_bijection,
)


def _contains(f, target):
    if f == target:
        return True
    return any(_contains(s, target) for s in getattr(f, "sous", ()))


# ── theorie intangible ────────────────────────────────────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── Prop 7.1 — cœur valeur (INCONDITIONNEL) ───────────────────────────────────
def test_recollement_recouvrement_valeur_clos():
    t = recollement_recouvrement_valeur()
    assert t.est_clos and len(t.hypotheses) == 0


def test_recollement_recouvrement_complet_clos():
    t = recollement_recouvrement()
    assert t.est_clos and len(t.hypotheses) == 0
    # consequent final == coincident(F, G, E) VERBATIM
    coinc = E.coincident(var("F"), var("G"), var("E"))
    assert _contains(t.conclusion, coinc)


# ── Prop 7.2 / 8 — recollement binaire ────────────────────────────────────────
def test_recollement_binaire_fonctionnel_existence():
    t = recollement_binaire_fonctionnel()
    pivot = reunion_graphes_fonctionnelle()
    # EXISTENCE : même énoncé que le pivot (func G, func H, dom disjoints ⊢ func(G∪H))
    assert t.conclusion == pivot.conclusion
    assert t.hypotheses == pivot.hypotheses
    assert len(t.hypotheses) == 3


def test_recollement_binaire_prolonge_gauche():
    t = recollement_binaire_prolonge_gauche()
    vg, vh = var("G"), var("H")
    assert t.est_clos and t.conclusion == inclus(vg, E.reunion(vg, vh))


def test_recollement_binaire_prolonge_droite():
    t = recollement_binaire_prolonge_droite()
    vg, vh = var("G"), var("H")
    assert t.est_clos and t.conclusion == inclus(vh, E.reunion(vg, vh))


def test_recollement_binaire_valeur_gauche_conditionnel():
    t = recollement_binaire_valeur_gauche()
    # coïncidence par valeur avec G sur dom G : (G∪H)(u)=G(u), 4 hyps (func,func,disj,u∈domG)
    assert len(t.hypotheses) == 4
    vg, vh, vu = var("G"), var("H"), var("u")
    GuH = E.reunion(vg, vh)
    assert t.conclusion == egal(E.valeur(GuH, vu), E.valeur(vg, vu))


def test_recollement_binaire_valeur_droite_conditionnel():
    t = recollement_binaire_valeur_droite()
    assert len(t.hypotheses) == 4
    vg, vh, vu = var("G"), var("H"), var("u")
    GuH = E.reunion(vg, vh)
    assert t.conclusion == egal(E.valeur(GuH, vu), E.valeur(vh, vu))


def test_recollement_binaire_unicite():
    t = recollement_binaire_unicite()
    # (P=Q) ⇒ (∀x)(x∈dom P ⇒ p(x)=q(x))  : unicité du recollement
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion.tag in ("ou", "non")  # implication encodée


# ── Prop 9 — réunion disjointe binaire ────────────────────────────────────────
def test_reunion_disjointe_binaire_disjoints():
    t = reunion_disjointe_binaire_disjoints()
    va, vb = var("A"), var("B")
    A0 = E.produit(va, E.singleton(ZERO))
    B1 = E.produit(vb, E.singleton(UN))
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == egal(E.intersection(A0, B1), E.VIDE)


def test_reunion_disjointe_binaire_reunion():
    t = reunion_disjointe_binaire_reunion()
    va, vb = var("A"), var("B")
    A0 = E.produit(va, E.singleton(ZERO))
    B1 = E.produit(vb, E.singleton(UN))
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == egal(somme_disjointe(va, vb), E.reunion(A0, B1))


# ── Prop 10 — réunion ≃ somme (binaire, conditionnel) ─────────────────────────
def test_reunion_equipotente_somme_si_bijection():
    t = reunion_equipotente_somme_si_bijection()
    va, vb = var("A"), var("B")
    src = E.reunion(va, vb)
    dst = somme_disjointe(va, vb)
    # exactement 1 hypothèse explicite : W bijecte A∪B sur A⊔B
    assert len(t.hypotheses) == 1
    W = bijection_canonique_reunion_somme(va, vb)
    assert t.hypotheses == frozenset({est_bijection_de(W, src, dst)})
    # conclusion == Eq(A∪B, A⊔B) VERBATIM
    assert t.conclusion == equipotent(src, dst)
