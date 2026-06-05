"""Tests — §III.3.2 : borne « 1 ≤ x pour x ≠ 0 » (ensembles_cardinaux_un_borne).

Énoncé Bourbaki (E.III.3.2) : « … et 1 ≤ x pour tout cardinal x ≠ 0. »  On
certifie ¬(X=∅) ⇒ ({∅} ≤ X) (1 = Card{∅}), via l'injection CONSTANTE {∅}→X, ∅↦e
(e = τ_w(w∈X) témoin de X≠∅).  Chaque test vérifie la conclusion EXACTE + clôture.
"""
from bourbaki.logique.formule import var, egal, non, impl, appartient, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux import ensembles_cardinaux_un_borne as M


def _G():
    return M._G(var("X"))


def test_temoin_dans():
    """⊢ ¬(X=∅) ⇒ (e∈X)  (X non vide a un élément ; e = τ_w(w∈X))."""
    t = M.temoin_dans("X")
    e = M._temoin(var("X"))
    assert t.conclusion == impl(non(egal(var("X"), E.VIDE)), appartient(e, var("X")))
    assert t.est_clos


def test_un_fonctionnel():
    """⊢ est_fonctionnel(G),  G = graphe constant {(∅,e)}  (C54)."""
    t = M.un_fonctionnel("X")
    assert t.conclusion == E.est_fonctionnel(_G())
    assert t.est_clos


def test_un_domaine():
    """⊢ dom(G) = {∅}  (le graphe constant est défini sur tout {∅})."""
    t = M.un_domaine("X")
    assert t.conclusion == egal(E.dom(_G()), M.UN)
    assert t.est_clos


def test_un_injective():
    """⊢ injective_dans(G, {∅})  (trivial : {∅} n'a qu'un élément)."""
    t = M.un_injective("X")
    assert t.conclusion == E.injective_dans(_G(), M.UN)
    assert t.est_clos


def test_un_image_inclus():
    """⊢_{e∈X} image(G, {∅}) ⊂ X  (l'image {e} est dans X via e∈X)."""
    t = M.un_image_inclus("X")
    assert t.conclusion == inclus(E.image(_G(), M.UN), var("X"))
    # conditionnel : l'unique hypothèse est e∈X
    assert len(t.hypotheses) == 1


def test_un_inf_egal():
    """⊢ ¬(X=∅) ⇒ ({∅} ≤ X)   (« 1 ≤ x » pour x ≠ 0, E.III.3.2)."""
    t = M.un_inf_egal("X")
    cible = impl(non(egal(var("X"), E.VIDE)), inf_egal_card(M.UN, var("X")))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_un_inf_egal():
    """⊢ ¬(Card X=∅) ⇒ (1 ≤ Card X)   (« 1 ≤ x » sur les cardinaux, E.III.3.2)."""
    t = M.cardinal_un_inf_egal("X")
    cardX = cardinal(var("X"))
    cible = impl(non(egal(cardX, E.VIDE)), inf_egal_card(M.UN, cardX))
    assert t.conclusion == cible
    assert t.est_clos
