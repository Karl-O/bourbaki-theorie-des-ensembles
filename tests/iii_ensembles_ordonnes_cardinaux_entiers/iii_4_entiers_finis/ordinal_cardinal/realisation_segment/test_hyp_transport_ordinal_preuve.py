"""Tests MIROIR — ensembles_hyp_transport_ordinal_preuve : DÉCHARGE des conjoints du
PULLBACK de hyp_transport_ordinal (le GATE ℕ).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, inclus, egal, et, impl, non, pourtout, existe
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.realisation_segment.ensembles_hyp_transport_ordinal_preuve as P
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_bon_ordre_intervalle_ordinal as BOIO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import intervalle_0a


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22  (l'axiome de sélection du pullback est en
#  THÉORIE DÉDIÉE, n'altère PAS theorie_ensembles)
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_pullback_un_seul_axiome_dediee():
    th = P.theorie_pullback()
    assert len(th.axiomes) == 1
    assert len(E.theorie_ensembles().axiomes) == 22   # INCHANGÉE


def test_pullback_membre_equivalence():
    t = P.pullback_membre("a", "Ro", "S", "t")
    PB = P.pullback("a", "Ro", "S")
    vt = var("t")
    corps = et(appartient(vt, var("a")), appartient(cardinal(seg("Ro", "a", vt)), var("S")))
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    assert t.conclusion == equiv(appartient(vt, PB), corps)


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ INTO  — pullback_into : CLOS, == hyp_realisation_min.
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_into_egale_hyp_realisation_min():
    t = P.pullback_into("a", "Ro", "S")
    PB = P.pullback("a", "Ro", "S")
    assert t.conclusion == BOIO.hyp_realisation_min("Ro", "a", "S", PB, "tt")


def test_pullback_into_CLOS():
    t = P.pullback_into("a", "Ro", "S")
    assert len(t.hypotheses) == 0
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ PB ⊂ a  — pullback_inclus_a : CLOS.
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_inclus_a_conclusion():
    t = P.pullback_inclus_a("a", "Ro", "S")
    PB = P.pullback("a", "Ro", "S")
    assert t.conclusion == inclus(PB, var("a"))


def test_pullback_inclus_a_CLOS():
    t = P.pullback_inclus_a("a", "Ro", "S")
    assert len(t.hypotheses) == 0
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ ONTO  — pullback_onto : == hyp_realisation_onto, sous {S⊂[0,a], real}.
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_onto_egale_hyp_realisation_onto():
    t = P.pullback_onto("a", "Ro", "S")
    PB = P.pullback("a", "Ro", "S")
    assert t.conclusion == BOIO.hyp_realisation_onto("Ro", "a", "S", PB, "x", "xw")


def test_pullback_onto_hypotheses_exactes():
    t = P.pullback_onto("a", "Ro", "S")
    exp = {
        inclus(var("S"), intervalle_0a("a")),                          # S⊂[0,a]
        pourtout("x", P.realisation_segment("Ro", "a", "x", "xw")),     # (∀c) realisation
    }
    assert set(t.hypotheses) == exp
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ PB ≠ ∅  — pullback_non_vide : sous {S⊂[0,a], S≠∅, real}.
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_non_vide_conclusion():
    t = P.pullback_non_vide("a", "Ro", "S")
    PB = P.pullback("a", "Ro", "S")
    assert t.conclusion == non(egal(PB, E.VIDE))


def test_pullback_non_vide_hypotheses_exactes():
    t = P.pullback_non_vide("a", "Ro", "S")
    exp = {
        inclus(var("S"), intervalle_0a("a")),                          # S⊂[0,a]
        non(egal(var("S"), E.VIDE)),                                    # S≠∅
        pourtout("x", P.realisation_segment("Ro", "a", "x", "xw")),     # (∀c) realisation
    }
    assert set(t.hypotheses) == exp
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 LE CORPS du ∀S — hyp_transport_corps_preuve : == cible, sous 3 hyps honnêtes.
# ─────────────────────────────────────────────────────────────────────────────
def test_corps_conclusion_EST_LA_CIBLE():
    t = P.hyp_transport_corps_preuve("a", "Ro", "S")
    assert t.conclusion == P.hyp_transport_corps_cible("a", "Ro", "S")


def test_corps_hypotheses_exactes():
    t = P.hyp_transport_corps_preuve("a", "Ro", "S")
    exp = {
        inclus(var("S"), intervalle_0a("a")),
        non(egal(var("S"), E.VIDE)),
        pourtout("x", P.realisation_segment("Ro", "a", "x", "xw")),
    }
    assert set(t.hypotheses) == exp
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 LE CONJOINT ∀S — hyp_transport_prop_all_S_preuve : sous le SEUL maillon real.
# ─────────────────────────────────────────────────────────────────────────────
def test_prop_all_S_hypothese_unique_realisation():
    t = P.hyp_transport_prop_all_S_preuve("a", "Ro", "S")
    assert set(t.hypotheses) == {pourtout("x", P.realisation_segment("Ro", "a", "x", "xw"))}
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 LE TRANSPORT — hyp_transport_ordinal_preuve : conclusion == cible LITTÉRALE,
#  2 hypothèses HONNÊTES (realisation + bo_form artefact dégénéré).
# ─────────────────────────────────────────────────────────────────────────────
def test_hyp_transport_ordinal_preuve_conclusion_EST_LA_CIBLE():
    t = P.hyp_transport_ordinal_preuve("a")
    assert t.conclusion == BOIO.hyp_transport_ordinal("a")        # == la cible DÉPOSÉE


def test_hyp_transport_ordinal_preuve_hypotheses_exactes():
    t = P.hyp_transport_ordinal_preuve("a")
    assert set(t.hypotheses) == P.hyp_transport_ordinal_preuve_hypotheses("a")
    assert len(set(t.hypotheses)) == 2


def test_hyp_transport_ordinal_preuve_non_vacueux():
    t = P.hyp_transport_ordinal_preuve("a")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_realisation_segment_est_le_maillon():
    # le maillon NON prouvé est bien une implication c≤a ⇒ (∃t∈a) Card(seg t)=c.
    r = P.realisation_segment("Ro", "a", "cc", "xs")
    vc, vt = var("cc"), var("xs")
    expected = impl(inf_egal_card(vc, var("a")),
                    existe("xs", et(appartient(vt, var("a")),
                                    egal(cardinal(seg("Ro", "a", vt)), vc))))
    assert r == expected


def test_bo_form_artefact_contient_liant_terme():
    # l'artefact bloquant : un TERME (pullback) en position de LIANT — non dérivable.
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    bf = P.bo_form_artefact("a", "Ro", "S")

    def term_binders(f):
        res = [f.lieur] if isinstance(f.lieur, Terme) else []
        for s in f.sous:
            res += term_binders(s)
        return res
    tbs = term_binders(bf)
    assert len(tbs) == 1 and tbs[0].nom == "pullback_seg_card"
