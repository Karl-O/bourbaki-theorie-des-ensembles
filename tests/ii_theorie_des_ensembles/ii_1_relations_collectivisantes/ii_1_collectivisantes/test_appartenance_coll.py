"""Tests — E.II.3, §1.4 Ex.1 : ⊢ Coll_x(x ∈ y) (x ∈ y collectivisante en x).

Le test APPELLE le théorème et vérifie : conclusion == cible (égalité STRUCTURELLE),
théorème CLOS (0 hypothèse), invariant theorie_ensembles() == 22 axiomes, et que la
preuve est un VRAI contenu d'existence (∃ présent), pas une tautologie (∀x)(f ⇔ f).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, coll, libres_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes.ensembles_appartenance_coll import (
    appartenance_collectivisante)


def _cible():
    # Coll_x(x ∈ y) = (∃Y)(∀x)((x ∈ Y) ⇔ (x ∈ y))   (Y = liant frais choisi par coll)
    return coll("x", appartient(var("x"), var("y")))


def test_appartenance_coll_conclusion():
    # ⊢ Coll_x(x ∈ y) : conclusion == cible (égalité STRUCTURELLE).
    t = appartenance_collectivisante()
    assert t.conclusion == _cible()


def test_appartenance_coll_clos():
    # Théorème CLOS : zéro hypothèse non déchargée (preuve directe, témoin Y := y).
    t = appartenance_collectivisante()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_appartenance_coll_est_un_existentiel():
    # Le contenu EST l'existence d'un témoin : la conclusion est bien un ∃ (Coll),
    # PAS la tautologie (∀x)(f ⇔ f). y reste libre (Coll_x lie x et le témoin Y).
    t = appartenance_collectivisante()
    assert t.conclusion.tag == "exists"          # (∃Y) … : ∃-introduction effective
    assert "x" not in libres_f(t.conclusion)     # x est lié (collectivisante EN x)
    assert "y" in libres_f(t.conclusion)         # y libre (paramètre de la relation)


def test_theorie_reste_22_axiomes():
    # Invariant projet : AUCUNE théorie dédiée / schéma S8 — preuve pure 22 axiomes.
    assert len(E.theorie_ensembles().axiomes) == 22
