"""Tests §III.5 Prop 5 (forme [0,b]) + briques.

Prop 5 (E III.38) forme a=0 : est_entier(b) ⇒ Card([0,b]) = successeur(b).
Cœur τ-hygiène : decomp_zero [0,b+1]=[0,b]∪{b+1} CLOS (corrige le résidu déposé)."""
import bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 as M
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles


def test_decomp_zero_clos():
    t = M.decomp_zero("b")
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.decomp_zero_enonce("b")


def test_prop5_base_clos():
    t = M.prop5_base()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.prop5_base_enonce()


def test_prop5_intervalle_zero_clos():
    """🎯 est_entier(b) ⇒ Card([0,b]) = successeur(b)  CLOS, 0 hyp."""
    t = M.prop5_intervalle_zero("b")
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.prop5_intervalle_zero_enonce("b")


def test_prop4_translation_bien_definie_clos():
    """🎯 (est_cardinal(a) et x∈[0,b]) ⇒ a+x ∈ [a,a+b]  CLOS, 0 hyp (Prop 4 well-defined)."""
    t = M.prop4_translation_bien_definie("a", "b", "x")
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.prop4_translation_bien_definie_enonce("a", "b", "x")


def test_prop4_translation_croissante_clos():
    """🎯 (x≤x') ⇒ a+x ≤ a+x'  CLOS, 0 hyp (Prop 4 croissance large)."""
    t = M.prop4_translation_croissante("a", "x", "xp")
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.prop4_translation_croissante_enonce("a", "x", "xp")


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
