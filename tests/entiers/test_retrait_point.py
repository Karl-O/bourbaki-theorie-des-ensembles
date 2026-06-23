"""Tests §III.4 — SURGERY « RETRAIT D'UN POINT » (ferme retrait_point_hyp du LEMME N).

Discipline LCF stricte : chaque test vérifie la CONCLUSION EXACTE et l'ensemble des
HYPOTHÈSES (clos pour les PONTS inconditionnels ; report ISOLÉ et précis pour
l'unique maillon dur — la surgery effective b → (C⊔{∅})∖{*}).

INVARIANT vérifié : theorie_ensembles() = 22 (aucun axiome nouveau ; rien postulé).

PALIERS :
  ✅ INCONDITIONNELS (.est_clos) :
       eq_succ_ensemble, inf_egal_via_eq_codom, diff_marqueur_egal_copie,
       eq_diff_marqueur_c, inf_egal_diff_marqueur_implique.
  ⚙️ CONDITIONNELS (report ISOLÉ, jamais postulé) :
       retrait_point_hyp_assemble (sous retrait_surgery_hyp), conclusion ==
           le report retrait_point_hyp de ensembles_cardinal_pas_entre LITTÉRALEMENT ;
       retrait_point_hyp_mod_surgery (CLOS 0 hyp : la surgery en antécédent explicite).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, non
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.cardinaux.ensembles_cardinaux import (
    equipotent, cardinal, inf_egal_card, est_injection_de,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_cardinal_pas_entre import retrait_point_hyp as REPORT
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery import ensembles_retrait_point as R


# ── INVARIANT : theorie_ensembles() intangible = 22 ──────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── PONTS INCONDITIONNELS ─────────────────────────────────────────────────────
def test_eq_succ_ensemble_clos():
    """⊢ Eq(c+1, C⊔{∅}) — CLOS (le successeur cardinal ≃ l'ensemble augmenté)."""
    vc = var("c")
    S = R._S("c")
    thm = R.eq_succ_ensemble("c")
    assert thm.est_clos
    # c+1 = Card(S) (def. du successeur) : Eq(c+1, S) = Eq(Card S, S)
    assert thm.conclusion == equipotent(cardinal(S), S)
    assert cardinal(S) == successeur(vc)


def test_inf_egal_via_eq_codom_clos():
    """⊢ ( b ≤ Y et Eq(Y,Z) ) ⇒ b ≤ Z — CLOS (transport de ≤ par équipotence)."""
    vb, vY, vZ = var("b"), var("Y"), var("Z")
    thm = R.inf_egal_via_eq_codom("b", "Y", "Z")
    assert thm.est_clos
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == et(inf_egal_card(vb, vY), equipotent(vY, vZ))
    assert cons == inf_egal_card(vb, vZ)


def test_diff_marqueur_egal_copie_clos():
    """⊢ (C⊔{∅}) ∖ {*} = C×{0} — CLOS (retrait du point marqué * = (∅,1))."""
    diff = E.difference(R._S("c"), E.singleton(R._STAR))
    thm = R.diff_marqueur_egal_copie("c")
    assert thm.est_clos
    assert thm.conclusion == egal(diff, R._C0("c"))


def test_eq_diff_marqueur_c_clos():
    """⊢ Eq((C⊔{∅})∖{*}, C) — CLOS (S privé du marqueur ≃ C ; le « c-ensemble »)."""
    vc = var("c")
    diff = E.difference(R._S("c"), E.singleton(R._STAR))
    thm = R.eq_diff_marqueur_c("c")
    assert thm.est_clos
    assert thm.conclusion == equipotent(diff, vc)


def test_inf_egal_diff_marqueur_implique_clos():
    """⊢ ( b ≤ (C⊔{∅})∖{*} ) ⇒ ( b ≤ c ) — CLOS (PONT FINAL de la branche)."""
    vb, vc = var("b"), var("c")
    diff = E.difference(R._S("c"), E.singleton(R._STAR))
    thm = R.inf_egal_diff_marqueur_implique("b", "c")
    assert thm.est_clos
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == inf_egal_card(vb, diff)
    assert cons == inf_egal_card(vb, vc)


# ── SURGERY ISOLÉE : énoncé exact ─────────────────────────────────────────────
def test_retrait_surgery_hyp_enonce():
    """Énoncé exact de l'unique maillon dur (surgery effective b → (C⊔{∅})∖{*})."""
    vb, vc, vf = var("b"), var("c"), var("F")
    succ_c = successeur(vc)
    diff = E.difference(R._S("c"), E.singleton(R._STAR))
    enonce = R.retrait_surgery_hyp("b", "c", "F")
    expected = impl(et(est_injection_de(vf, vb, succ_c),
                       non(egal(E.image(vf, vb), succ_c))),
                    inf_egal_card(vb, diff))
    assert enonce == expected


def test_surgery_n_est_pas_tautologie():
    """La surgery NE conclut PAS « b ≤ c » : son consequent (b ≤ S∖{*}) DIFFÈRE de
    celui du report (b ≤ c).  L'assemblage est un VRAI travail (ponts clos), pas un
    P⇒P déguisé."""
    sg = R.retrait_surgery_hyp("b", "c", "F")
    rep = R.retrait_point_hyp_enonce("b", "c", "F")
    _, sg_cons = antecedent_consequent(sg)
    _, rep_cons = antecedent_consequent(rep)
    assert sg_cons != rep_cons


# ── ASSEMBLAGE = retrait_point_hyp modulo la surgery isolée ───────────────────
def test_retrait_point_hyp_assemble_conclusion_litterale():
    """⊢ { retrait_surgery_hyp } ⊢ retrait_point_hyp(b,c,F)
       — conclusion ÉGALE LITTÉRALEMENT au report de ensembles_cardinal_pas_entre."""
    thm = R.retrait_point_hyp_assemble("b", "c", "F")
    assert thm.conclusion == REPORT("b", "c", "F")


def test_retrait_point_hyp_assemble_report_isole():
    """L'unique hypothèse résiduelle est EXACTEMENT la surgery isolée
    retrait_surgery_hyp (jamais postulée ; le théorème n'est PAS clos — honnêteté)."""
    thm = R.retrait_point_hyp_assemble("b", "c", "F")
    sg = R.retrait_surgery_hyp("b", "c", "F")
    assert thm.hypotheses == frozenset({sg})
    assert not thm.est_clos


# ── FORME CONDITIONNELLE CLOSE (surgery en antécédent explicite) ──────────────
def test_retrait_point_hyp_mod_surgery_clos():
    """⊢ retrait_surgery_hyp(b,c,F) ⇒ retrait_point_hyp(b,c,F) — CLOS 0 hyp.

    La conséquence EST le report retrait_point_hyp de ensembles_cardinal_pas_entre."""
    thm = R.retrait_point_hyp_mod_surgery("b", "c", "F")
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == R.retrait_surgery_hyp("b", "c", "F")
    assert cons == REPORT("b", "c", "F")
