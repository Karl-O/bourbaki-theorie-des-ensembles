"""Tests V9 — §I.5.3 « Relations fonctionnelles » : univocité (E.I.40) + C45 direct (E.I.41).

Énoncés vérifiés verbatim sur le PDF :
  Déf. (E.I.40) : R univoque en x  ⇔  (∀y)(∀z)( ((y|x)R et (z|x)R) ⇒ (y=z) ) théorème.
  C45 direct (E.I.41 L.5-13) : R univoque ⟹ R ⇒ (x = τ_x(R)) théorème de 𝒯.

Les tests APPELLENT réellement les deux livrables et comparent par égalité
STRUCTURELLE (==), pas par simple succès d'import.

  PYTHONIOENCODING=utf-8 python -m pytest tests/logique/i_4_egalitaires/test_relations_fonctionnelles_c45.py -q
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, tau, impl, et, pourtout, appartient, subst_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_4_egalitaires.relations_fonctionnelles_c45 import (
    relation_univoque_x, c45_avant,
)

# Relation de travail : R = (x ∈ a), avec x libre (à substituer) et `a` paramètre.
R = appartient(var("x"), var("a"))
X = "x"


# ── 1. CONSTRUCTEUR : forme exacte de relation_univoque_x ──────────────────────

def test_relation_univoque_forme():
    """relation_univoque_x(R) == (∀y)(∀z)( ((y|x)R et (z|x)R) ⇒ (y=z) ) (structurel)."""
    uni = relation_univoque_x(R, X, "y", "z")
    Ry = subst_f(var("y"), X, R)                 # (y|x)R
    Rz = subst_f(var("z"), X, R)                 # (z|x)R
    attendu = pourtout("y", pourtout("z", impl(et(Ry, Rz), egal(var("y"), var("z")))))
    assert uni == attendu
    # x n'est PAS libre dans l'univocité (consommé par la substitution).
    from bourbaki.logique.i_1_termes_relations.formule import libres_f
    assert X not in libres_f(uni)


def test_relation_univoque_fraicheur():
    """y, z non fraîches ⇒ refus ; choix automatique sinon."""
    import pytest
    with pytest.raises(ValueError):
        relation_univoque_x(R, X, "x", "z")       # y == x interdit
    with pytest.raises(ValueError):
        relation_univoque_x(R, X, "y", "y")       # y == z interdit
    # appel sans y,z : doit produire une formule close en x avec deux ∀ imbriqués
    auto = relation_univoque_x(R, X)
    assert auto.tag == "non" and auto.sous[0].tag == "exists"   # (∀y) = ¬(∃y)¬


# ── 2. THÉORÈME : C45 sens direct ─────────────────────────────────────────────

def test_c45_avant_conclusion_est_cible():
    """conclusion == R ⇒ (x = τ_x(R))  (égalité structurelle)."""
    t = c45_avant(R, X, "y", "z")
    cible = impl(R, egal(var(X), tau(X, R)))
    assert t.conclusion == cible


def test_c45_avant_hypotheses_exactes():
    """hypotheses == { relation_univoque_x(R) } exactement ; non clos ; cible ∉ hyps."""
    t = c45_avant(R, X, "y", "z")
    uni = relation_univoque_x(R, X, "y", "z")
    assert t.hypotheses == frozenset({uni})
    assert not t.est_clos
    cible = impl(R, egal(var(X), tau(X, R)))
    assert cible not in t.hypotheses             # pas de tautologie déguisée


def test_c45_avant_certifie_par_noyau():
    """Le résultat est un Theoreme du noyau abrégé (frontière de confiance)."""
    t = c45_avant(R, X)
    assert isinstance(t, N.Theoreme)


if __name__ == "__main__":
    print("Univocité :", relation_univoque_x(R, X, "y", "z"))
    print("C45 direct :", c45_avant(R, X, "y", "z"))
