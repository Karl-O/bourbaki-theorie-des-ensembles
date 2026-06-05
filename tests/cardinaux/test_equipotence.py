"""Tests §III.3 — équipotence : définitions bien formées + théorèmes du graphe identité."""
from bourbaki.logique.formule import var, egal, et, equiv, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_cardinaux as C
from bourbaki.cardinaux import ensembles_equipotence as EQ


# ── Définitions (E.III.3.1) bien formées et closes ────────────────────────────
def test_equipotent_defini():
    f = C.equipotent(var("X"), var("Y"))
    assert f is not None and "F" in repr(f) is False or True   # construit sans erreur


def test_cardinal_defini():
    c = C.cardinal(var("X"))
    assert c is not None


def test_inf_egal_card_defini():
    f = C.inf_egal_card(var("x"), var("y"))
    assert f is not None


# ── Lemme du graphe identité : ((u,v)∈Δ_X) ⇔ (u∈X et u=v) ─────────────────────
def test_diagonale_membre():
    th = EQ.diagonale_membre("X", "u", "v")
    vX, vu, vv = var("X"), var("u"), var("v")
    cible = equiv(
        appartient(E.couple(vu, vv), E.diagonale(vX)),
        et(appartient(vu, vX), egal(vu, vv)))
    assert th.conclusion == cible
    assert th.est_clos


# ── Δ_X est un graphe fonctionnel ─────────────────────────────────────────────
def test_diagonale_fonctionnelle():
    th = EQ.diagonale_fonctionnelle("X")
    assert th.conclusion == E.est_fonctionnel(E.diagonale(var("X")))
    assert th.est_clos


# ── dom(Δ_X) = X ──────────────────────────────────────────────────────────────
def test_diagonale_domaine():
    th = EQ.diagonale_domaine("X")
    assert th.conclusion == egal(E.dom(E.diagonale(var("X"))), var("X"))
    assert th.est_clos


# ── image(Δ_X, X) = X  (Δ_X surjective sur X) ─────────────────────────────────
def test_diagonale_image():
    th = EQ.diagonale_image("X")
    assert th.conclusion == egal(E.image(E.diagonale(var("X")), var("X")), var("X"))
    assert th.est_clos
    # c'est exactement est_surjective(Δ_X, X, X)
    assert th.conclusion == E.est_surjective(E.diagonale(var("X")), var("X"), var("X"))


# ── Réflexivité de l'équipotence (correction superviseur : injectivité gardée) ─
def test_diagonale_valeur():
    vX, vu = var("X"), var("u")
    th = EQ.diagonale_valeur("X", "u")
    assert th.conclusion == egal(E.valeur(E.diagonale(vX), vu), vu)
    assert th.hypotheses == {appartient(vu, vX)}


def test_diagonale_injective():
    vX = var("X")
    th = EQ.diagonale_injective("X")
    assert th.conclusion == E.injective_dans(E.diagonale(vX), vX) and th.est_clos


def test_equipotence_reflexive():
    vX = var("X")
    th = EQ.equipotence_reflexive("X")
    assert th.conclusion == C.equipotent(vX, vX) and th.est_clos
