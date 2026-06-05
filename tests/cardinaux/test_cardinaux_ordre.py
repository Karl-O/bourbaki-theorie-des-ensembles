"""Tests — §III.3.2 : ordre ≤ des cardinaux (ensembles_cardinaux_ordre).

Chaque test vérifie que la conclusion certifiée par le noyau EST EXACTEMENT la
cible Bourbaki, et que le théorème est CLOS (aucune hypothèse).
"""
from bourbaki.logique.formule import var, impl, et
from bourbaki.cardinaux import ensembles_cardinaux_ordre as O
from bourbaki.cardinaux.ensembles_cardinaux import equipotent, inf_egal_card


def test_equipotence_implique_inf_egal():
    """⊢ Eq(X, Y) ⇒ (X ≤ Y)   (une bijection est une injection, E.III.3.2)."""
    t = O.equipotence_implique_inf_egal("F", "X", "Y")
    cible = impl(equipotent(var("X"), var("Y")), inf_egal_card(var("X"), var("Y")))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_egal_transitive():
    """⊢ (X ≤ Y et Y ≤ Z) ⇒ (X ≤ Z)   (transitivité de ≤, E.III.3.2)."""
    t = O.inf_egal_transitive("F", "G", "X", "Y", "Z")
    vX, vY, vZ = var("X"), var("Y"), var("Z")
    cible = impl(et(inf_egal_card(vX, vY), inf_egal_card(vY, vZ)),
                 inf_egal_card(vX, vZ))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── briques de la transitivité (composée de deux injections) ──────────────────
def test_composee_domaine_incl():
    """⊢_{dom F=X, image(F,X)⊂Y, dom G=Y}  dom(G∘F) = X."""
    t = O.composee_domaine_incl("G", "F", "X", "Y")
    from bourbaki.logique.formule import egal
    from bourbaki.ensembles import ensembles_abrege as E
    assert t.conclusion == egal(E.dom(E.composee(var("G"), var("F"))), var("X"))


def test_composee_image_incl():
    """⊢_{image(F,X)⊂Y, image(G,Y)⊂Z}  image(G∘F, X) ⊂ Z."""
    t = O.composee_image_incl("G", "F", "X", "Y", "Z")
    from bourbaki.logique.formule import inclus
    from bourbaki.ensembles import ensembles_abrege as E
    assert t.conclusion == inclus(E.image(E.composee(var("G"), var("F")), var("X")),
                                  var("Z"))


def test_composee_injective_incl():
    """⊢ injective_dans(G∘F, X)  (sous les hyps F,G fonctionnels/inj, dom, image⊂)."""
    t = O.composee_injective_incl("G", "F", "X", "Y")
    from bourbaki.ensembles import ensembles_abrege as E
    assert t.conclusion == E.injective_dans(E.composee(var("G"), var("F")), var("X"))
