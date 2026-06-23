"""Tests §III.3.3 — ASSOCIATIVITÉ de la SOMME disjointe (équipotence) :
bijection de réassociation des copies K : (A⊔B)⊔C → A⊔(B⊔C).

La bijection envoie ((u,0),0)↦(u,0), ((v,1),0)↦((v,0),1), (w,1)↦((w,1),1).
On certifie ici tout le THÉORÈME, ASSEMBLAGE COMPLET :
  • K fonctionnel, dom K = (A⊔B)⊔C, valeur de K sur chacune des trois copies ;
  • membre_assoc3 (caractérisation à 3 feuilles de l'appartenance) ;
  • injective_dans(K, (A⊔B)⊔C) (analyse 3×3) ;
  • image(K, (A⊔B)⊔C) = A⊔(B⊔C) (surjectivité, 3 antécédents) ;
  • est_bijection_de, Eq((A⊔B)⊔C, A⊔(B⊔C)), Card((A⊔B)⊔C)=Card(A⊔(B⊔C)).
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.iii_3_3_somme import ensembles_somme_associe as A
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, et, ou, existe, equiv


def _K():
    return A._assoc_graphe("A", "B", "C", "k")


def test_assoc_graphe_fonctionnel_clos():
    thm = A.assoc_graphe_fonctionnel()
    assert thm.conclusion == E.est_fonctionnel(_K())
    assert thm.est_clos


def test_assoc_graphe_domaine_clos():
    thm = A.assoc_graphe_domaine()
    ABC = A._ABC_gauche("A", "B", "C")
    assert thm.conclusion == egal(E.dom(_K()), ABC)
    assert thm.est_clos


def test_assoc_graphe_valeur_A():
    """{u∈A} ⊢ K(((u,0),0)) = (u,0)."""
    thm = A.assoc_graphe_valeur_A()
    vu = var("u")
    cpl = E.couple(E.couple(vu, ZERO), ZERO)
    assert thm.conclusion == egal(E.valeur(_K(), cpl), E.couple(vu, ZERO))
    assert list(thm.hypotheses) == [appartient(vu, var("A"))]


def test_assoc_graphe_valeur_B():
    """{v∈B} ⊢ K(((v,1),0)) = ((v,0),1)."""
    thm = A.assoc_graphe_valeur_B()
    vv = var("v")
    cpl = E.couple(E.couple(vv, UN), ZERO)
    assert thm.conclusion == egal(E.valeur(_K(), cpl), E.couple(E.couple(vv, ZERO), UN))
    assert list(thm.hypotheses) == [appartient(vv, var("B"))]


def test_assoc_graphe_valeur_C():
    """{w∈C} ⊢ K((w,1)) = ((w,1),1)."""
    thm = A.assoc_graphe_valeur_C()
    vw = var("wc")
    cpl = E.couple(vw, UN)
    assert thm.conclusion == egal(E.valeur(_K(), cpl), E.couple(E.couple(vw, UN), UN))
    assert list(thm.hypotheses) == [appartient(vw, var("C"))]


def test_membre_assoc3_clos():
    """⊢ s∈(A⊔B)⊔C ⇔ (caseA ou (caseB ou caseC))   (caractérisation à 3 feuilles)."""
    thm = A.membre_assoc3("A", "B", "C", "s")
    vs = var("s")
    ABC = A._ABC_gauche("A", "B", "C")
    cA = existe("u", et(appartient(var("u"), var("A")),
                        egal(vs, E.couple(E.couple(var("u"), ZERO), ZERO))))
    cB = existe("v", et(appartient(var("v"), var("B")),
                        egal(vs, E.couple(E.couple(var("v"), UN), ZERO))))
    cC = existe("r", et(appartient(var("r"), var("C")),
                        egal(vs, E.couple(var("r"), UN))))
    assert thm.conclusion == equiv(appartient(vs, ABC), ou(cA, ou(cB, cC)))
    assert thm.est_clos


def test_assoc_graphe_injective_clos():
    """⊢ injective_dans(K, (A⊔B)⊔C)   (analyse de cas 3×3, clos)."""
    thm = A.assoc_graphe_injective()
    ABC = A._ABC_gauche("A", "B", "C")
    assert thm.conclusion == E.injective_dans(_K(), ABC, "s", "sp")
    assert thm.est_clos


def test_assoc_graphe_image_clos():
    """⊢ image(K, (A⊔B)⊔C) = A⊔(B⊔C)   (surjectivité, clos)."""
    thm = A.assoc_graphe_image()
    ABC = A._ABC_gauche("A", "B", "C")
    ABCd = A._ABC_droite("A", "B", "C")
    assert thm.conclusion == egal(E.image(_K(), ABC), ABCd)
    assert thm.est_clos


def test_assoc_est_bijection_clos():
    """⊢ est_bijection_de(K, (A⊔B)⊔C, A⊔(B⊔C))   (clos)."""
    thm = A.assoc_est_bijection()
    ABC = A._ABC_gauche("A", "B", "C")
    ABCd = A._ABC_droite("A", "B", "C")
    assert thm.conclusion == est_bijection_de(_K(), ABC, ABCd)
    assert thm.est_clos


def test_eq_somme_associatif_clos():
    """⊢ Eq((A⊔B)⊔C, A⊔(B⊔C))   (associativité à équipotence près, clos)."""
    thm = A.eq_somme_associatif()
    ABC = A._ABC_gauche("A", "B", "C")
    ABCd = A._ABC_droite("A", "B", "C")
    assert thm.conclusion == equipotent(ABC, ABCd)
    assert thm.est_clos


def test_somme_cardinale_associative_clos():
    """⊢ Card((A⊔B)⊔C) = Card(A⊔(B⊔C))   (associativité de la somme cardinale, clos)."""
    thm = A.somme_cardinale_associative()
    ABC = A._ABC_gauche("A", "B", "C")
    ABCd = A._ABC_droite("A", "B", "C")
    assert thm.conclusion == egal(cardinal(ABC), cardinal(ABCd))
    assert thm.est_clos
