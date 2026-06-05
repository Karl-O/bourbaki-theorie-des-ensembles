"""Tests §III.3.3 — Commutativité de la somme disjointe (équipotence) : Eq(A⊔B, B⊔A).

La bijection K : A⊔B → B⊔A flippe le marqueur : (u,0)↦(u,1) et (v,1)↦(v,0).
On vérifie ses paliers : fonctionnel, domaine, valeur sur chaque copie, injectif,
image, assemblage bijection, et l'équipotence finale.
"""
import ensembles_abrege as E
import ensembles_somme_commute as C
from ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from ensembles_cardinaux import est_bijection_de, equipotent
from formule import var, egal, appartient


def _K():
    return C._commute_graphe("A", "B", "k")


def test_commute_graphe_fonctionnel_clos():
    """K fonctionnel : conclusion EXACTE, théorème CLOS."""
    thm = C.commute_graphe_fonctionnel()
    assert thm.conclusion == E.est_fonctionnel(_K())
    assert thm.est_clos


def test_commute_graphe_domaine_clos():
    """dom(K) = A⊔B : conclusion EXACTE, théorème CLOS."""
    thm = C.commute_graphe_domaine()
    cible = egal(E.dom(_K()), somme_disjointe(var("A"), var("B")))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_commute_graphe_valeur_gauche():
    """{u∈A} ⊢ K((u,0)) = (u,1) : la copie gauche s'envoie sur la copie droite."""
    thm = C.commute_graphe_valeur_gauche()
    vu = var("u")
    cible = egal(E.valeur(_K(), E.couple(vu, ZERO)), E.couple(vu, UN))
    assert thm.conclusion == cible
    assert list(thm.hypotheses) == [appartient(vu, var("A"))]


def test_commute_graphe_valeur_droite():
    """{v∈B} ⊢ K((v,1)) = (v,0) : la copie droite s'envoie sur la copie gauche."""
    thm = C.commute_graphe_valeur_droite()
    vv = var("v")
    cible = egal(E.valeur(_K(), E.couple(vv, UN)), E.couple(vv, ZERO))
    assert thm.conclusion == cible
    assert list(thm.hypotheses) == [appartient(vv, var("B"))]


def test_commute_graphe_injective_clos():
    """⊢ injective_dans(K, A⊔B) : CLOS (pas d'hypothèse, valeur = identité)."""
    thm = C.commute_graphe_injective()
    AB = somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == E.injective_dans(_K(), AB, "s", "sp")
    assert thm.est_clos


def test_commute_graphe_image_clos():
    """⊢ image(K, A⊔B) = B⊔A : CLOS (surjectivité)."""
    thm = C.commute_graphe_image()
    AB = somme_disjointe(var("A"), var("B"))
    BA = somme_disjointe(var("B"), var("A"))
    assert thm.conclusion == egal(E.image(_K(), AB), BA)
    assert thm.est_clos


def test_commute_est_bijection_clos():
    """⊢ est_bijection_de(K, A⊔B, B⊔A) : CLOS."""
    thm = C.commute_est_bijection()
    AB = somme_disjointe(var("A"), var("B"))
    BA = somme_disjointe(var("B"), var("A"))
    assert thm.conclusion == est_bijection_de(_K(), AB, BA)
    assert thm.est_clos


def test_eq_somme_commute_clos():
    """⊢ Eq(A⊔B, B⊔A) : COMMUTATIVITÉ de la somme à équipotence près, CLOS."""
    thm = C.eq_somme_commute()
    AB = somme_disjointe(var("A"), var("B"))
    BA = somme_disjointe(var("B"), var("A"))
    assert thm.conclusion == equipotent(AB, BA)
    assert thm.est_clos


def test_eq_somme_commute_termes():
    """La commutativité tient sur des TERMES composés (ex. A = Card U)."""
    CU = E.app("card", var("U"))
    thm = C.eq_somme_commute(CU, "B")
    AB = somme_disjointe(CU, var("B"))
    BA = somme_disjointe(var("B"), CU)
    assert thm.conclusion == equipotent(AB, BA)
    assert thm.est_clos
