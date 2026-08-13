"""Tests §II.3 — caractérisation au COUPLE de la diagonale Δ_X (Bourbaki E II.13, Déf.8).

On APPELLE le théorème, on vérifie : CLÔTURE (0 hypothèse — équivalence pure),
conclusion == cible reconstruite depuis primitives BRUTES (⇔, couple, diagonale,
appartient, =), theorie == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, equiv
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
import bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple as M


def test_couple_diagonale_cible_litterale():
    t = M.couple_diagonale()
    a, b, X = var("a"), var("b"), var("X")
    # cible : (a,b)∈Δ_X ⇔ (a∈X et a=b)
    cible = equiv(appartient(E.couple(a, b), E.diagonale(X)), et(appartient(a, X), egal(a, b)))
    assert t.conclusion == cible == M.couple_diagonale_cible()
    assert t.est_clos and not t.hypotheses           # équivalence pure (0 hypothèse)
    assert len(theorie_ensembles().axiomes) == 22


def test_couple_diagonale_non_tautologie():
    """Les deux membres de l'équivalence sont distincts (pas une tautologie)."""
    a, b, X = var("a"), var("b"), var("X")
    gauche = appartient(E.couple(a, b), E.diagonale(X))
    droite = et(appartient(a, X), egal(a, b))
    assert gauche != droite


def test_diagonale_auto_reciproque():
    """⊢ Δ_X⁻¹ = Δ_X  (Id_X est sa propre réciproque, E II.13 Déf.8) — CLOS."""
    t = M.diagonale_auto_reciproque()
    X = var("X")
    cible = egal(E.reciproque(E.diagonale(X)), E.diagonale(X))
    assert t.conclusion == cible == M.diagonale_auto_reciproque_cible()
    assert t.est_clos and not t.hypotheses           # inconditionnel
    assert len(theorie_ensembles().axiomes) == 22


def test_projections_diagonale():
    """⊢ pr₁Δ_X = X  et  pr₂Δ_X = X  (E II.13 Déf.8) — CLOS."""
    X = var("X")
    t1, t2 = M.pr1_diagonale(), M.pr2_diagonale()
    assert t1.conclusion == egal(E.dom(E.diagonale(X)), X) == M.pr1_diagonale_cible()
    assert t2.conclusion == egal(E.img(E.diagonale(X)), X) == M.pr2_diagonale_cible()
    assert t1.est_clos and not t1.hypotheses
    assert t2.est_clos and not t2.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_composee_diagonale():
    """⊢ ((x,z)∈G∘Δ_A) ⇔ (x∈A et (x,z)∈G)  (cœur de Γ∘Id_A=Γ, E II.13 Déf.8) — CLOS."""
    G, A, x, z = var("G"), var("A"), var("x"), var("z")
    t = M.couple_composee_diagonale()
    cible = equiv(appartient(E.couple(x, z), E.composee(G, E.diagonale(A))),
                  et(appartient(x, A), appartient(E.couple(x, z), G)))
    assert t.conclusion == cible == M.couple_composee_diagonale_cible()
    assert t.est_clos and not t.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_diagonale_composee():
    """⊢ ((x,z)∈Δ_B∘G) ⇔ ((x,z)∈G et z∈B)  (dual : Id à gauche, E II.13 Déf.8) — CLOS."""
    G, B, x, z = var("G"), var("B"), var("x"), var("z")
    t = M.diagonale_composee_couple()
    cible = equiv(appartient(E.couple(x, z), E.composee(E.diagonale(B), G)),
                  et(appartient(E.couple(x, z), G), appartient(z, B)))
    assert t.conclusion == cible == M.diagonale_composee_couple_cible()
    assert t.est_clos and not t.hypotheses
    assert len(theorie_ensembles().axiomes) == 22
