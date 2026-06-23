"""Tests §III.3.3/§III.3.4 — 0 élément neutre de la somme : Eq(∅⊔B, B), Card(∅⊔B)=Card B.

La bijection K : B → ∅⊔B est l'injection droite v↦(v,1) (la copie gauche ∅×{0} est
vide).  On vérifie ses paliers, l'équipotence Eq(∅⊔B, B), et l'égalité cardinale.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.iii_3_3_somme import ensembles_somme_zero as Z
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, UN
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient


def _K():
    return Z._neutre_graphe("B", "k")


def test_neutre_graphe_fonctionnel_clos():
    thm = Z.neutre_graphe_fonctionnel()
    assert thm.conclusion == E.est_fonctionnel(_K())
    assert thm.est_clos


def test_neutre_graphe_domaine_clos():
    thm = Z.neutre_graphe_domaine()
    assert thm.conclusion == egal(E.dom(_K()), var("B"))
    assert thm.est_clos


def test_neutre_graphe_valeur():
    """{u∈B} ⊢ K(u) = (u,1)."""
    thm = Z.neutre_graphe_valeur()
    vu = var("u")
    assert thm.conclusion == egal(E.valeur(_K(), vu), E.couple(vu, UN))
    assert list(thm.hypotheses) == [appartient(vu, var("B"))]


def test_neutre_graphe_injective_clos():
    thm = Z.neutre_graphe_injective()
    assert thm.conclusion == E.injective_dans(_K(), var("B"))
    assert thm.est_clos


def test_neutre_graphe_image_clos():
    """⊢ image(K, B) = ∅⊔B : surjectivité (la copie gauche est vide), CLOS."""
    thm = Z.neutre_graphe_image()
    AB = somme_disjointe(E.VIDE, var("B"))
    assert thm.conclusion == egal(E.image(_K(), var("B")), AB)
    assert thm.est_clos


def test_neutre_est_bijection_clos():
    thm = Z.neutre_est_bijection()
    AB = somme_disjointe(E.VIDE, var("B"))
    assert thm.conclusion == est_bijection_de(_K(), var("B"), AB)
    assert thm.est_clos


def test_eq_somme_zero_neutre_clos():
    """⊢ Eq(∅⊔B, B) : 0 élément neutre à équipotence près, CLOS."""
    thm = Z.eq_somme_zero_neutre()
    AB = somme_disjointe(E.VIDE, var("B"))
    assert thm.conclusion == equipotent(AB, var("B"))
    assert thm.est_clos


def test_card_somme_zero_neutre_clos():
    """⊢ Card(∅⊔B) = Card(B) : 0 + b = b au niveau cardinal, CLOS."""
    thm = Z.card_somme_zero_neutre()
    AB = somme_disjointe(E.VIDE, var("B"))
    assert thm.conclusion == egal(cardinal(AB), cardinal(var("B")))
    assert thm.est_clos
