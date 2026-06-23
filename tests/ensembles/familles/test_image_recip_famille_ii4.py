"""Tests §II.4 — image / image réciproque d'une famille (Prop. 3/4/6, E.II.25-27)."""
from bourbaki.logique.i_1_termes_relations.formule import egal, var
from bourbaki.logique.i_1_termes_relations.formule import libres_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_image_famille import ensembles_image_recip_famille_ii4 as M


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


# ── Prop. 4 (E.II.25) — image réciproque d'une intersection ───────────────────
def test_prop4_incluse_inconditionnel():
    t = M.image_recip_inter_incluse()
    assert t.est_clos and len(t.hypotheses) == 0   # f⁻¹⟨⋂Y⟩ ⊂ ⋂f⁻¹⟨Y_ι⟩


def test_prop4_arriere():
    t = M.image_recip_inter_arriere()
    assert t.est_clos and len(t.hypotheses) == 0   # {Fonct, α∈I} ⊃


def test_prop4_egalite():
    t = M.image_recip_inter_egal()
    assert t.est_clos and len(t.hypotheses) == 0
    g, fam, i = var("f"), var("Y"), var("I")
    inter = E.inter_famille(fam, i)
    L = M.image_recip(g, inter)
    R = E.inter_famille(M.famille_image_recip(g, fam), i)
    assert t.conclusion.tag == "ou"              # Fonct ⇒ (α∈I ⇒ (L=R))
    inner = t.conclusion.sous[1]
    assert inner.tag == "ou"
    assert inner.sous[1] == egal(L, R)


# ── Prop. 3 (E.II.25) — image directe d'une réunion / intersection ────────────
def test_prop3_reunion_egalite_inconditionnelle():
    t = M.image_reunion_egal()
    assert t.est_clos and len(t.hypotheses) == 0
    g, fam, i = var("G"), var("X"), var("I")
    reun = E.reunion_famille(fam, i)
    L = E.image(g, reun)
    R = E.reunion_famille(M.famille_image(g, fam), i)
    assert t.conclusion == egal(L, R)


def test_prop3_inter_incluse_inconditionnelle():
    t = M.image_inter_incluse()
    assert t.est_clos and len(t.hypotheses) == 0   # Γ⟨⋂X⟩ ⊂ ⋂Γ⟨X_ι⟩


# ── Cor. de la Prop. 4 (E.II.25) — image directe d'une inter sous injection ───
def test_cor_arriere_si_injective():
    t = M.image_inter_arriere_si_inj()
    assert t.est_clos and len(t.hypotheses) == 0


def test_cor_egalite_si_injective():
    t = M.image_inter_egal_si_injective()
    assert t.est_clos and len(t.hypotheses) == 0
    g, fam, i = var("G"), var("X"), var("I")
    inter = E.inter_famille(fam, i)
    L = E.image(g, inter)
    R = E.inter_famille(M.famille_image(g, fam), i)
    assert t.conclusion.tag == "ou"
    inner = t.conclusion.sous[1]
    assert inner.tag == "ou"
    assert inner.sous[1] == egal(L, R)


# ── Prop. 4 (E.II.25) — image réciproque d'une RÉUNION (inconditionnelle) ─────
def test_prop4_reunion_egal_inconditionnel():
    t = M.image_recip_reunion_egal()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.cible_image_recip_reunion()
    assert len(E.theorie_ensembles().axiomes) == 22


if __name__ == "__main__":
    for n in list(globals()):
        if n.startswith("test_"):
            globals()[n]()
    print("OK Prop 3/4/6 + Cor")
