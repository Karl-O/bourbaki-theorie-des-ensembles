"""Tests §II.4 — image / image réciproque d'une famille (Prop. 3/4/6, E.II.25-27)."""
from bourbaki.logique.formule import egal, var
from bourbaki.logique.formule import libres_f
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_image_recip_famille_ii4 as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── Prop. 6 (E.II.27) — image réciproque d'une différence ─────────────────────
def test_prop6_arriere_inconditionnel():
    t = M.image_recip_diff_arriere()
    assert t.est_clos and len(t.hypotheses) == 0   # f⁻¹⟨B⟩∖f⁻¹⟨Y⟩ ⊂ f⁻¹⟨B∖Y⟩


def test_prop6_egalite():
    t = M.image_recip_difference()
    assert t.est_clos and len(t.hypotheses) == 0
    g, b, y = var("f"), var("B"), var("Y")
    L = M.image_recip(g, E.difference(b, y))
    R = E.difference(M.image_recip(g, b), M.image_recip(g, y))
    assert t.conclusion.tag == "ou"           # Fonctionnelle(f) ⇒ (L = R)
    cons = t.conclusion.sous[1]
    assert cons == egal(L, R)


if __name__ == "__main__":
    test_theorie_inchangee()
    test_prop6_arriere_inconditionnel()
    test_prop6_egalite()
    print("OK Prop 6")
