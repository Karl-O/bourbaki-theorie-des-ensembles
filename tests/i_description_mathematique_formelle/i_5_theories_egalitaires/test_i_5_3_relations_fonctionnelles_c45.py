"""Tests V9 — §I.5.3 « Relations fonctionnelles » : univocité (E.I.40) + C45 direct (E.I.41).

Énoncés vérifiés verbatim sur le PDF :
  Déf. (E.I.40) : R univoque en x  ⇔  (∀y)(∀z)( ((y|x)R et (z|x)R) ⇒ (y=z) ) théorème.
  C45 direct (E.I.41 L.5-13) : R univoque ⟹ R ⇒ (x = τ_x(R)) théorème de 𝒯.

Les tests APPELLENT réellement les deux livrables et comparent par égalité
STRUCTURELLE (==), pas par simple succès d'import.

  PYTHONIOENCODING=utf-8 python -m pytest tests/logique/i_4_egalitaires/test_relations_fonctionnelles_c45.py -q
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, tau, impl, et, pourtout, appartient, subst_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c45 import (
    relation_univoque_x, c45_avant, c45_arriere,
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
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
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


# ── 3. SCHÉMA : C45 sens RÉCIPROQUE (E.I.41 L.14-19) ──────────────────────────

def test_c45_arriere_produit_univocite():
    """D'un théorème CLOS ⊢ R ⇒ (x=T), c45_arriere produit ⊢ relation_univoque_x(R),
    CLOS (0 hyp).  Ici R := (x=a), T := a, ⊢ R⇒(x=a) = a_implique_a."""
    Req = egal(var("x"), var("a"))                    # R = (x = a)
    T = var("a")                                      # terme sans x
    thm = a_implique_a(Req)                            # ⊢ (x=a) ⇒ (x=a) = R ⇒ (x=T)
    res = c45_arriere(Req, "x", T, thm, "y", "z")
    assert res.conclusion == relation_univoque_x(Req, "x", "y", "z")
    assert res.est_clos and not res.hypotheses
    assert isinstance(res, N.Theoreme)


def test_c45_arriere_refuse_T_contient_x():
    """Garde de fidélité : T ne doit pas contenir x, et thm doit conclure R⇒(x=T)."""
    import pytest
    Req = egal(var("x"), var("a"))
    Tbad = var("x")                                   # T contient x → refus
    thm = a_implique_a(Req)
    with pytest.raises(ValueError):
        c45_arriere(Req, "x", Tbad, thm)
    with pytest.raises(ValueError):
        c45_arriere(Req, "x", var("a"), a_implique_a(appartient(var("x"), var("b"))))


if __name__ == "__main__":
    print("Univocité :", relation_univoque_x(R, X, "y", "z"))
    print("C45 direct :", c45_avant(R, X, "y", "z"))


def test_relation_fonctionnelle_en_x_definition():
    """Def E I.41 L.20-23 : « (∃x)R et il existe au plus un x tel que R »."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, et, existe)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c45 import (
        relation_fonctionnelle_en_x, relation_univoque_x)
    R = egal(var("x"), var("a"))
    assert relation_fonctionnelle_en_x(R, "x") == \
        et(existe("x", R), relation_univoque_x(R, "x"))
