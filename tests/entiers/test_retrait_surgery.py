"""Tests miroir de bourbaki/entiers/ensembles_retrait_surgery.py.

Ferme l'unique maillon dur retrait_surgery_hyp de la branche non surjective du
LEMME N (« pas de cardinal strictement entre c et c+1 »), réduit au SEUL résidu
GÉNÉRAL GEN (équipotence des retraits ponctuels).

INVARIANTS vérifiés : .est_clos / nombre d'hypothèses / conclusion ÉGALE à l'énoncé
visé ; theorie_ensembles() = 22 INTANGIBLE.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, et, non, impl, inclus, appartient,
                                       existe, egal)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_surgery import (
    image_evite_inclus_diff,
    injection_evite_implique_inf_egal_diff,
    non_surjective_donne_point_rate,
    injection_non_surj_donne_inf_egal_diff,
    retrait_un_point_hypothese,
    retrait_surgery_assemble,
    retrait_surgery_mod_HD,
    equipotence_retrait_un_point_general,
    retrait_un_point_depuis_general,
    retrait_surgery_mod_general,
    retrait_point_hyp_mod_general,
    cardinal_pas_entre_mod_general,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import retrait_surgery_hyp


# ── theorie_ensembles INTANGIBLE = 22 axiomes ─────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── ÉTAPE B : re-ciblage inconditionnel ───────────────────────────────────────
def test_image_evite_inclus_diff_clos():
    th = image_evite_inclus_diff("G", "b", "E", "q")
    assert th.est_clos and len(th.hypotheses) == 0


def test_injection_evite_implique_inf_egal_diff_clos():
    th = injection_evite_implique_inf_egal_diff("G", "b", "E", "q")
    assert th.est_clos and len(th.hypotheses) == 0
    vG, vb, vE, vq = var("G"), var("b"), var("E"), var("q")
    img = E.image(vG, vb)
    diff = E.difference(vE, E.singleton(vq))
    attendu = impl(et(est_injection_de(vG, vb, vE), non(appartient(vq, img))),
                   inf_egal_card(vb, diff))
    assert th.conclusion == attendu


# ── ÉTAPE P1 : non-surjectivité ⇒ point raté ──────────────────────────────────
def test_non_surjective_donne_point_rate_clos():
    th = non_surjective_donne_point_rate("G", "b", "E")
    assert th.est_clos and len(th.hypotheses) == 0
    vG, vb, vE = var("G"), var("b"), var("E")
    img = E.image(vG, vb)
    attendu = impl(et(inclus(img, vE), non(egal(img, vE))),
                   existe("q", et(appartient(var("q"), vE),
                                  non(appartient(var("q"), img)))))
    assert th.conclusion == attendu


# ── COMBINAISON (P1 + B) ──────────────────────────────────────────────────────
def test_injection_non_surj_donne_inf_egal_diff_clos():
    th = injection_non_surj_donne_inf_egal_diff("F", "b", "E")
    assert th.est_clos and len(th.hypotheses) == 0
    vF, vb, vE, vq = var("F"), var("b"), var("E"), var("q")
    img = E.image(vF, vb)
    diff_q = E.difference(vE, E.singleton(vq))
    attendu = impl(et(est_injection_de(vF, vb, vE), non(egal(img, vE))),
                   existe("q", et(appartient(vq, vE), inf_egal_card(vb, diff_q))))
    assert th.conclusion == attendu


# ── ASSEMBLAGE : retrait_surgery_hyp modulo HD ────────────────────────────────
def test_retrait_surgery_assemble_concl_egale_cible():
    th = retrait_surgery_assemble("b", "c", "F")
    assert th.conclusion == retrait_surgery_hyp("b", "c", "F")
    # une seule hypothèse résiduelle : HD
    assert len(th.hypotheses) == 1
    assert list(th.hypotheses)[0] == retrait_un_point_hypothese("b", "c", "q")


def test_retrait_surgery_mod_HD_clos():
    th = retrait_surgery_mod_HD("b", "c", "F")
    assert th.est_clos and len(th.hypotheses) == 0
    HD = retrait_un_point_hypothese("b", "c", "q")
    assert th.conclusion == impl(HD, retrait_surgery_hyp("b", "c", "F"))


# ── RÉDUCTION FINALE : retrait_surgery_hyp modulo le résidu GÉNÉRAL GEN ────────
def test_retrait_un_point_depuis_general_clos():
    th = retrait_un_point_depuis_general("b", "c", "q")
    assert th.est_clos and len(th.hypotheses) == 0
    GEN = equipotence_retrait_un_point_general()
    HD = retrait_un_point_hypothese("b", "c", "q")
    assert th.conclusion == impl(GEN, HD)


def test_retrait_surgery_mod_general_clos():
    th = retrait_surgery_mod_general("b", "c", "F")
    assert th.est_clos and len(th.hypotheses) == 0
    GEN = equipotence_retrait_un_point_general()
    assert th.conclusion == impl(GEN, retrait_surgery_hyp("b", "c", "F"))


# ── CAPSTONE : retrait_point_hyp et LEMME N modulo (est_cardinal(b) et GEN) ────
def test_retrait_point_hyp_mod_general_clos():
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_cardinal_pas_entre import retrait_point_hyp
    th = retrait_point_hyp_mod_general("b", "c", "F")
    assert th.est_clos and len(th.hypotheses) == 0
    GEN = equipotence_retrait_un_point_general()
    assert th.conclusion == impl(GEN, retrait_point_hyp("b", "c", "F"))


def test_cardinal_pas_entre_mod_general_clos():
    from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
    from bourbaki.logique.i_1_termes_relations.formule import ou
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    th = cardinal_pas_entre_mod_general("b", "c", "F")
    assert th.est_clos and len(th.hypotheses) == 0
    ante, cons = antecedent_consequent(th.conclusion)
    GEN = equipotence_retrait_un_point_general()
    assert ante == et(est_cardinal(var("b")), GEN)
    vb, vc = var("b"), var("c")
    succ = successeur(vc)
    # consequent EXACTEMENT cardinal_pas_entre(b,c) = (b≤c+1) ⇒ (b≤c OU b=c+1)
    assert cons == impl(inf_egal_card(vb, succ), ou(inf_egal_card(vb, vc), egal(vb, succ)))
