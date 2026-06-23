"""Tests §II.6 — C56 (relation déduite par passage au quotient) et C57 (propriété
universelle du quotient, bien-définition de h).

On vérifie que les deux lemmes se construisent, ont EXACTEMENT les hypothèses
HONNÊTES documentées (P/f compatible, t non vide + membres R-liés, C55), que la
conclusion N'EST PAS dans les hypothèses (non-vacuité), et que theorie_ensembles
reste à 22 axiomes (aucun axiome neuf)."""
from bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_c56_c57 import (
    c56_quotient_existe_ssi_pourtout, c57_bien_definie, membres_t_R_lies)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.formule import var, egal, equiv, existe, appartient


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_c56_se_construit_et_hyps_honnetes():
    P = lambda u: appartient(u, var("GP"))
    R = E.rel_graphe("G")
    th = c56_quotient_existe_ssi_pourtout()
    hyps = set(th.hypotheses)
    # exactement 3 hypothèses honnêtes
    assert len(th.hypotheses) == 3
    assert E.est_compatible(P, R, "x", "a") in hyps
    assert membres_t_R_lies("G", var("t"), "x", "a") in hyps
    assert existe("yc", appartient(var("yc"), var("t"))) in hyps
    # non-vacuité : la conclusion (équivalence) n'est pas une hypothèse
    assert th.conclusion not in hyps


def test_c57_bien_definie_hyps_honnetes():
    th = c57_bien_definie()
    hyps = set(th.hypotheses)
    R = E.rel_graphe("G")
    p = E.application_canonique(var("G"), var("E"))
    px, py = E.valeur(p, var("x")), E.valeur(p, var("yb"))
    assert len(th.hypotheses) == 2
    # f compatible avec R  +  C55 (p(x)=p(y) ⇔ R{x,y})
    assert E.est_compatible_application(var("f"), R, "x", "yb") in hyps
    assert equiv(egal(px, py), R(var("x"), var("yb"))) in hyps
    # non-vacuité : conclusion (p(x)=p(y) ⇒ f(x)=f(y)) hors hypothèses
    assert th.conclusion not in hyps
