"""Tests §III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : FINITION.

Verrouille l'EMBALLAGE TRIPLE de la fonction caractéristique χ_Y (ÉTAPE 1) et UN
SENS du round-trip ρ∘χ = id sur 𝔓X (ÉTAPE 2), assemblés depuis l'infra des rounds
24/25/26 (rien postulé) :

  ÉTAPE 1 — χ_Y est une APPLICATION X → 2 (triple ((χ_Y,X),2) ∈ 𝓕(X;2)) :
    • chi_inclus_produit       Y⊂X ⇒ χ_Y ⊂ X×2 ;
    • chi_dans_exposant        Y⊂X ⇒ χ_Y ∈ 2^X ;
    • chi_appli                le triple ((χ_Y,X),2) ;
    • chi_dans_applications    Y⊂X ⇒ chi_appli(Y) ∈ 𝓕(X;2).

  ÉTAPE 2 — ρ∘χ = id sur 𝔓X (ρ lit le graphe sous-jacent χ_Y) :
    • couple_un_dans_chi       ((z,1)∈χ_Y) ⇔ (z∈Y) ;
    • rho_chi_identite         Y⊂X ⇒ Pre(χ_Y) = Y.
"""
from bourbaki.logique.formule import (var, egal, et, non, ou, impl, equiv,
                                       appartient, inclus, pourtout, existe)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles.ensembles_somme_disjointe import ZERO, UN
from bourbaki.cardinaux.arithmetique import ensembles_prop12_fin as P
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import deux
from bourbaki.cardinaux.arithmetique.ensembles_powerset_deux import preimage_un


def _chi(y="Y", x="X"):
    return P.chi(var(y), var(x))


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1a — χ_Y ⊂ X × 2
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_inclus_produit():
    """⊢ Y⊂X ⇒ χ_Y ⊂ X×2, CLOS  (χ_Y est un graphe de couples (z∈X, w∈2))."""
    vy, vx = var("Y"), var("X")
    t = P.chi_inclus_produit("Y", "X")
    attendu = impl(inclus(vy, vx), inclus(_chi("Y", "X"), E.produit(vx, deux())))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1b — χ_Y ∈ 2^X
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_dans_exposant():
    """⊢ Y⊂X ⇒ χ_Y ∈ 2^X, CLOS  (graphe fonctionnel de X dans 2 = {0,1})."""
    vy, vx = var("Y"), var("X")
    t = P.chi_dans_exposant("Y", "X")
    attendu = impl(inclus(vy, vx), appartient(_chi("Y", "X"), E.exposant(vx, deux())))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1c — chi_appli(Y) = ((χ_Y, X), 2) ∈ 𝓕(X; 2)   (EMBALLAGE TRIPLE)
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_appli_terme():
    """chi_appli(Y) est bien le triple ((χ_Y, X), 2)."""
    vx = var("X")
    assert P.chi_appli("Y", "X") == E.couple(E.couple(_chi("Y", "X"), vx), deux())


def test_chi_dans_applications():
    """⊢ Y⊂X ⇒ chi_appli(Y) ∈ 𝓕(X;2), CLOS  (l'EMBALLAGE TRIPLE est une APPLICATION)."""
    vy, vx = var("Y"), var("X")
    t = P.chi_dans_applications("Y", "X")
    attendu = impl(inclus(vy, vx),
                   appartient(P.chi_appli("Y", "X"), E.applications(vx, deux())))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 2a — (z, 1) ∈ χ_Y  ⇔  z ∈ Y
# ═══════════════════════════════════════════════════════════════════════════════
def test_couple_un_dans_chi():
    """⊢ ((z,1)∈χ_Y) ⇔ (z∈Y), CLOS  (la valeur 1 repère EXACTEMENT Y)."""
    vz, vy = var("z"), var("Y")
    t = P.couple_un_dans_chi("Y", "X", "z")
    attendu = equiv(appartient(E.couple(vz, UN), _chi("Y", "X")), appartient(vz, vy))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 2b — ROUND-TRIP  ρ(χ_Y) = Pre(χ_Y) = Y
# ═══════════════════════════════════════════════════════════════════════════════
def test_rho_chi_identite():
    """⊢ Y⊂X ⇒ Pre(χ_Y) = Y, CLOS  (ρ∘χ = id : ρ appliqué au graphe χ_Y rend Y)."""
    vy, vx = var("Y"), var("X")
    t = P.rho_chi_identite("Y", "X")
    attendu = impl(inclus(vy, vx), egal(preimage_un(_chi("Y", "X"), vx), vy))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ
# ═══════════════════════════════════════════════════════════════════════════════
def test_bijection_prop12_reporte():
    """Le CRUX (bijection complète + Card= + Cantor) est explicitement REPORTÉ."""
    import pytest
    with pytest.raises(NotImplementedError):
        P.bijection_prop12_REPORTE()
