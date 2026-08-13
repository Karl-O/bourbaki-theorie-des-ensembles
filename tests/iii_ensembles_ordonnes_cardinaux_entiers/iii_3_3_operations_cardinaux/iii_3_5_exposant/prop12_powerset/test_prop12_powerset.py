"""Tests §III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12) : SENS DIFFICILE.

Ce module verrouille le PALIER 1 du SENS DIFFICILE : la FONCTION CARACTÉRISTIQUE
χ : 𝔓(X) → 𝓕(X; 2), Y ↦ χ_Y (x↦1 si x∈Y, 0 sinon), construite par RECOLLEMENT de
deux graphes constants à domaines disjoints (round 25) :

    χ_Y := (Y × {1}) ∪ ((X∖Y) × {0})
         = recollement(graphe_terme(Y, 1), graphe_terme(X∖Y, 0)).

On certifie (rien postulé) que χ_Y est une vraie FONCTION X → {0,1} :
  • domaines_recolle_disjoints  : ¬(u∈Y et u∈X∖Y)                    [Y∩(X∖Y)=∅] ;
  • chi_domaines_disjoints      : (∀u)¬(u∈dom(Y×{1}) et u∈dom((X∖Y)×{0})) ;
  • chi_fonctionnel             : est_fonctionnel(χ_Y)               [PIVOT recollement] ;
  • chi_est_graphe              : est_un_graphe(χ_Y) ;
  • chi_valeur_dans_Y           : {z∈Y} ⊢ (z,1)∈χ_Y                  [χ_Y(z)=1 sur Y] ;
  • chi_valeur_hors_Y           : {z∈X∖Y} ⊢ (z,0)∈χ_Y               [χ_Y(z)=0 hors Y] ;
  • reunion_Y_diff_egale_X      : ⊢ Y⊂X ⇒ (Y∪(X∖Y))=X ;
  • chi_domaine                 : ⊢ Y⊂X ⇒ dom(χ_Y)=X                 [χ_Y total sur X].

Le CRUX (bijection χ ⇄ ρ complète + Card(𝔓X)=2^Card X) reste REPORTÉ (emballage
triple χ_Y∈𝓕(X;2) + alignement graphe/triple entre χ et le ρ du round 24).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, non, ou, impl, equiv,
                                       appartient, inclus, pourtout)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset import ensembles_prop12_powerset as P


# ═══════════════════════════════════════════════════════════════════════════════
# Le terme χ_Y et ses deux morceaux
# ═══════════════════════════════════════════════════════════════════════════════
def _G(y="Y"):
    """χ_gauche = graphe_terme(Y, 1) = Y × {1}."""
    return E.graphe_terme(var(y), UN, "x")


def _H(y="Y", x="X"):
    """χ_droite = graphe_terme(X∖Y, 0) = (X∖Y) × {0}."""
    return E.graphe_terme(E.difference(var(x), var(y)), ZERO, "x")


def test_chi_terme():
    """χ_Y est bien le recollement (Y×{1}) ∪ ((X∖Y)×{0})."""
    chi = P.chi("Y", "X")
    assert chi == E.reunion(_G("Y"), _H("Y", "X"))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1a — DISJONCTION DES DOMAINES (Y ∩ (X∖Y) = ∅)
# ═══════════════════════════════════════════════════════════════════════════════
def test_domaines_recolle_disjoints():
    """⊢ ¬(u∈Y et u∈X∖Y), CLOS  (Y et X∖Y disjoints, via AXIOME_DIFF)."""
    vu, vy, vx = var("u"), var("Y"), var("X")
    t = P.domaines_recolle_disjoints("Y", "X", "u")
    attendu = non(et(appartient(vu, vy), appartient(vu, E.difference(vx, vy))))
    assert t.conclusion == attendu
    assert t.est_clos


def test_chi_domaines_disjoints():
    """⊢ (∀u)¬(u∈dom(Y×{1}) et u∈dom((X∖Y)×{0})), CLOS  (hyp. du PIVOT recollement)."""
    vu = var("u")
    G, H = _G("Y"), _H("Y", "X")
    t = P.chi_domaines_disjoints("Y", "X")
    attendu = pourtout("u", non(et(appartient(vu, E.dom(G)), appartient(vu, E.dom(H)))))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1b — χ_Y FONCTIONNEL (PIVOT du recollement)
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_fonctionnel():
    """⊢ est_fonctionnel(χ_Y), CLOS  (graphes fonctionnels à domaines disjoints recollés)."""
    chi = P.chi("Y", "X")
    t = P.chi_fonctionnel("Y", "X")
    assert t.conclusion == E.est_fonctionnel(chi)
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1c — χ_Y EST UN GRAPHE
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_est_graphe():
    """⊢ est_un_graphe(χ_Y), CLOS  (tout élément de la réunion est un couple)."""
    chi = P.chi("Y", "X")
    t = P.chi_est_graphe("Y", "X")
    assert t.conclusion == E.est_un_graphe(chi)
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1d — VALEURS de χ_Y
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_valeur_dans_Y():
    """{z∈Y} ⊢ (z,1)∈χ_Y  (χ_Y vaut 1 = {∅} sur Y)."""
    vz, vy = var("z"), var("Y")
    chi = P.chi("Y", "X")
    t = P.chi_valeur_dans_Y("Y", "X", "z")
    assert t.conclusion == appartient(E.couple(vz, UN), chi)
    assert appartient(vz, vy) in t.hypotheses


def test_chi_valeur_hors_Y():
    """{z∈X∖Y} ⊢ (z,0)∈χ_Y  (χ_Y vaut 0 = ∅ hors Y)."""
    vz, vy, vx = var("z"), var("Y"), var("X")
    chi = P.chi("Y", "X")
    t = P.chi_valeur_hors_Y("Y", "X", "z")
    assert t.conclusion == appartient(E.couple(vz, ZERO), chi)
    assert appartient(vz, E.difference(vx, vy)) in t.hypotheses


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1e — dom(χ_Y) = X
# ═══════════════════════════════════════════════════════════════════════════════
def test_reunion_Y_diff_egale_X():
    """⊢ Y⊂X ⇒ (Y∪(X∖Y))=X, CLOS  (réunion d'une partie et de son complémentaire)."""
    vy, vx = var("Y"), var("X")
    t = P.reunion_Y_diff_egale_X("Y", "X")
    attendu = impl(inclus(vy, vx), egal(E.reunion(vy, E.difference(vx, vy)), vx))
    assert t.conclusion == attendu
    assert t.est_clos


def test_chi_domaine():
    """⊢ Y⊂X ⇒ dom(χ_Y)=X, CLOS  (χ_Y est total sur X ; domaines recollés Y∪(X∖Y)=X)."""
    vy, vx = var("Y"), var("X")
    chi = P.chi("Y", "X")
    t = P.chi_domaine("Y", "X")
    attendu = impl(inclus(vy, vx), egal(E.dom(chi), vx))
    assert t.conclusion == attendu
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# Robustesse : termes composés
# ═══════════════════════════════════════════════════════════════════════════════
def test_chi_fonctionnel_terme_compose():
    """Robustesse : χ_Y fonctionnel quand X, Y sont des TERMES composés."""
    vY = E.intersection(var("A"), var("B"))
    vX = E.reunion(var("A"), var("B"))
    chi = P.chi(vY, vX)
    t = P.chi_fonctionnel(vY, vX)
    assert t.conclusion == E.est_fonctionnel(chi)
    assert t.est_clos


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ
# ═══════════════════════════════════════════════════════════════════════════════
def test_bijection_chi_complete_reporte():
    """Le CRUX (bijection χ complète + Card=) est explicitement REPORTÉ."""
    import pytest
    with pytest.raises(NotImplementedError):
        P.bijection_chi_complete_REPORTE()
