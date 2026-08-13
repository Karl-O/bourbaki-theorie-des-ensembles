"""Tests §II.3 — neutralité de Id pour la composition (Bourbaki E II.13, Déf.8 : Γ∘Id_A=Γ).

On APPELLE le théorème : conditionnel HONNÊTE (est_clos==False, hypothèses ==
{ est_graphe(G), pr₁G⊂A } reconstruites à la main), conclusion == cible G∘Δ_A=G
(rebuild raw : composee, diagonale), theorie == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_graphe_inclus_produit import est_graphe
import bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_identite_neutre as M


def test_composee_diagonale_neutre():
    """⊢ G∘Δ_A = G  sous { est_graphe(G), pr₁G⊂A }  (Γ∘Id_A=Γ)."""
    t = M.composee_diagonale_neutre()
    G, A = var("G"), var("A")
    cible = egal(E.composee(G, E.diagonale(A)), G)
    assert t.conclusion == cible == M.composee_diagonale_neutre_cible()
    assert not t.est_clos                                 # conditionnel honnête
    assert set(t.hypotheses) == {est_graphe(G), inclus(E.dom(G), A)}
    assert len(theorie_ensembles().axiomes) == 22


def test_diagonale_composee_neutre():
    """⊢ Δ_B∘G = G  sous { est_graphe(G), pr₂G⊂B }  (Id_B∘Γ=Γ, dual)."""
    t = M.diagonale_composee_neutre()
    G, B = var("G"), var("B")
    cible = egal(E.composee(E.diagonale(B), G), G)
    assert t.conclusion == cible == M.diagonale_composee_neutre_cible()
    assert not t.est_clos
    assert set(t.hypotheses) == {est_graphe(G), inclus(E.img(G), B)}
    assert len(theorie_ensembles().axiomes) == 22


def test_composee_diagonale_neutre_valeur():
    """⊢ (G∘Δ_A)(x) = G(x)  sous { est_graphe(G), pr₁G⊂A }  (f∘id=f, niveau valeur)."""
    t = M.composee_diagonale_neutre_valeur()
    G, A, x = var("G"), var("A"), var("x")
    cible = egal(E.valeur(E.composee(G, E.diagonale(A)), x), E.valeur(G, x))
    assert t.conclusion == cible == M.composee_diagonale_neutre_valeur_cible()
    assert set(t.hypotheses) == {est_graphe(G), inclus(E.dom(G), A)}
    assert len(theorie_ensembles().axiomes) == 22


def test_diagonale_composee_neutre_valeur():
    """⊢ (Δ_B∘G)(x) = G(x)  sous { est_graphe(G), pr₂G⊂B }  (id∘f=f, niveau valeur, dual)."""
    t = M.diagonale_composee_neutre_valeur()
    G, B, x = var("G"), var("B"), var("x")
    cible = egal(E.valeur(E.composee(E.diagonale(B), G), x), E.valeur(G, x))
    assert t.conclusion == cible == M.diagonale_composee_neutre_valeur_cible()
    assert set(t.hypotheses) == {est_graphe(G), inclus(E.img(G), B)}
    assert len(theorie_ensembles().axiomes) == 22
