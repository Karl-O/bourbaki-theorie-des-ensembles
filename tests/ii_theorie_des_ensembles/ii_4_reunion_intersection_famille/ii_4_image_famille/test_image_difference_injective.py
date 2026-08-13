"""Tests §II.4.5 — Cor. de la Prop. 6 (E.II.27) : image directe d'une différence
sous injection.   Injective(f) ⇒ f⟨A∖X⟩ = f⟨A⟩ ∖ f⟨X⟩."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal, var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille import (
    ensembles_image_difference_injective as M)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cor_prop6_egalite_sous_injection():
    t = M.image_difference_injective()
    # CLOS : injective(f) déchargée par loi_deduction (0 hypothèse non déchargée).
    assert t.est_clos and len(t.hypotheses) == 0
    # conclusion == cible (à l'identique).
    assert t.conclusion == M.cible_image_difference_injective()
    # forme : Injective(f) ⇒ (L = R)  (impl == ou avec non à gauche).
    assert t.conclusion.tag == "ou"
    f, a, x = var("f"), var("A"), var("X")
    L = E.image(f, E.difference(a, x))
    R = E.difference(E.image(f, a), E.image(f, x))
    assert t.conclusion.sous[1] == egal(L, R)
    # invariant : theorie inchangée.
    assert len(E.theorie_ensembles().axiomes) == 22


if __name__ == "__main__":
    for n in list(globals()):
        if n.startswith("test_"):
            globals()[n]()
    print("OK Cor. Prop 6 — image directe différence sous injection")
