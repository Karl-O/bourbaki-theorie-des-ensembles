"""Tests du PONT bare→ambiant C60 (`ensembles_c60_pont`)."""
from bourbaki.logique.i_1_termes_relations.formule import app, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_pont as P
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import couverture_totale
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R


def _vh():
    return lambda t: app("rule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_essai_dans_parties():
    vh = _vh()
    th = P.essai_dans_parties(vh)
    R, ve, vp = _graphe_R("G"), var("E"), var("ppont")
    assert th.conclusion == E.appartient(vp, P.ambiant("E", "Vval"))
    # exactement 4 hyps honnêtes
    assert len(th.hypotheses) == 4
    assert P.est_essai(vp, vh, R, ve, var("ypont"), "zrc") in th.hypotheses
    assert E.est_un_graphe(vp) in th.hypotheses
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_essai_dans_parties_depuis_bien_formes():
    vh = _vh()
    th = P.essai_dans_parties_depuis_bien_formes(vh)
    assert len(th.hypotheses) == 3
    assert th.conclusion == E.appartient(var("ppont"), P.ambiant("E", "Vval"))


def test_antecedent_ambiant_depuis_bare():
    vh = _vh()
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_clauses import antecedent_couverture_ambiant
    th = P.antecedent_ambiant_depuis_bare(vh)
    assert th.conclusion == antecedent_couverture_ambiant(
        vh, "E", "G", var("x0"), "Vval", "ytf", "pcf", "zess")
    assert len(th.hypotheses) == 3


def test_recursion_transfinie_existence_final():
    vh = _vh()
    th = P.recursion_transfinie_existence_final(vh)
    R, ve = _graphe_R("G"), var("E")
    # conclusion = existence C60
    cible = couverture_totale(couvert_essai(vh, R, ve), ve, "x0tf")
    assert th.conclusion == cible
    # EXACTEMENT 3 hyps honnêtes : bo, essais_bien_formes, rule_codomain
    hs = set(th.hypotheses)
    assert len(hs) == 3
    assert E.est_bien_ordonne(R, ve) in hs
    assert P.essais_bien_formes(vh, "E", "G", "Vval", "qwf", "wwf", "zess") in hs
    assert P.rule_codomain(vh, "Vval", "zess") in hs
    assert th.conclusion not in hs
    assert len(E.theorie_ensembles().axiomes) == 22
