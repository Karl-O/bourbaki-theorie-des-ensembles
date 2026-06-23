"""Tests §III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : CLÔTURE FINALE.

Verrouille la bijection caractéristique χ : 𝔓(X) → 𝓕(X;2) (Y ↦ ((χ_Y,X),2)) et
l'égalité de cardinaux Card(𝔓X) = 2^Card X (Proposition 12), assemblées depuis le
crux χ∘ρ = id (chi_eq_graphe : χ_{Pre(G)} = G) et ρ∘χ = id (Pre(χ_Y)=Y, round 27).
"""
import pytest
from bourbaki.logique.formule import (var, egal, et, non, ou, impl, equiv,
                                       appartient, inclus, pourtout, existe)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique import ensembles_prop12_card as P
from bourbaki.cardinaux.arithmetique.ensembles_prop12_card import _bijection as B
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import deux
from bourbaki.cardinaux.arithmetique.ensembles_powerset_deux import preimage_un
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, equipotent,
                               est_bijection_de)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import injective_dans
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire


def _W(x="X"):
    return B._W(var(x))


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX — χ∘ρ = id sur les graphes : χ_{Pre(G)} = G
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_eq_graphe():
    """{G∈2^X} ⊢ χ_{Pre(G)} = G, CLOS  (χ∘ρ = id : recoller Pre(G) reconstruit G)."""
    vG, vX = var("G"), var("X")
    t = P.chi_eq_graphe("G", "X")
    Y = preimage_un(vG, vX)
    attendu = impl(appartient(vG, E.exposant(vX, deux())), egal(P.chi(Y, vX), vG))
    assert t.conclusion == attendu
    assert t.est_clos


def test_round_trip_rho_chi():
    """{Y⊂X} ⊢ Pre(χ_Y) = Y, CLOS  (ρ∘χ = id ; réexposé du round 27)."""
    vY, vX = var("Y"), var("X")
    t = P.round_trip_rho_chi("Y", "X")
    attendu = impl(inclus(vY, vX), egal(preimage_un(P.chi(vY, vX), vX), vY))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# Les quatre conjoints de la bijection χ : 𝔓X → 𝓕(X;2)
# ═══════════════════════════════════════════════════════════════════════════════
def test_W_fonctionnel():
    """⊢ est_fonctionnel(W), CLOS."""
    t = P.W_fonctionnel("X")
    assert t.conclusion == E.est_fonctionnel(_W())
    assert t.est_clos


def test_W_domaine():
    """⊢ dom(W) = 𝔓X, CLOS."""
    vX = var("X")
    t = P.W_domaine("X")
    assert t.conclusion == egal(E.dom(_W()), E.parties(vX))
    assert t.est_clos


def test_W_injective():
    """⊢ injective_dans(W, 𝔓X), CLOS  (ρ∘χ=id ⇒ χ injective)."""
    vX = var("X")
    t = P.W_injective("X")
    assert t.conclusion == injective_dans(_W(), E.parties(vX))
    assert t.est_clos


def test_W_image_egale_applications():
    """⊢ image(W, 𝔓X) = 𝓕(X;2), CLOS  (χ∘ρ=id ⇒ χ surjective)."""
    vX = var("X")
    t = P.W_image_egale_applications("X")
    assert t.conclusion == egal(E.image(_W(), E.parties(vX)), E.applications(vX, deux()))
    assert t.est_clos


def test_chi_bijection():
    """⊢ est_bijection_de(W, 𝔓X, 𝓕(X;2)), CLOS  (χ est une BIJECTION)."""
    vX = var("X")
    t = P.chi_bijection("X")
    attendu = est_bijection_de(_W(), E.parties(vX), E.applications(vX, deux()))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# Eq(𝔓X, 𝓕(X;2))  et  Card(𝔓X) = 2^Card X   (PROPOSITION 12)
# ═══════════════════════════════════════════════════════════════════════════════
def test_powerset_equipotent_applications():
    """⊢ Eq(𝔓X, 𝓕(X;2)), CLOS  (𝔓X équipotent à l'espace des applications X→2)."""
    vX = var("X")
    t = P.powerset_equipotent_applications("X")
    assert t.conclusion == equipotent(E.parties(vX), E.applications(vX, deux()))
    assert t.est_clos


def test_card_parties_egale_deux_exp():
    """⊢ Card(𝔓X) = 2^Card X, CLOS  (PROPOSITION 12 : le cardinal de 𝔓X est 2^a)."""
    vX = var("X")
    t = P.card_parties_egale_deux_exp("X")
    attendu = egal(cardinal(E.parties(vX)), exposant_cardinal_binaire(deux(), vX))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# BONUS Cantor (REPORTÉ — pont SET→CARDINAL non disponible)
# ═══════════════════════════════════════════════════════════════════════════════
def test_cantor_deux_exp_reporte():
    """Cantor restaté 2^Card X > Card X : explicitement REPORTÉ (pont set→cardinal)."""
    with pytest.raises(NotImplementedError):
        P.cantor_deux_exp("X")
