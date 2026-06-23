"""Tests — §III.2 C60 EXISTENCE, RÉALISATION DE LA FAMILLE
(`bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation`).

Vérifie la CONSTRUCTION S8 de la famille concrète des essais des y<x et la DÉCHARGE
des clauses de `realisation_famille` :
  • 🎯 (P1) `membres_fonctionnels_realise` ⊢ membres_fonctionnels(Dfam_real(x))  [CLOS] ;
  • 🎯 (P5) `equation_au_point_realise`     ⊢ vh(x)=vh(x)                          [CLOS] ;
  • 🎯 `realisation_famille_reduite`        { P2,P3,P4 } ⊢ realisation_famille(Dfam_real) ;
  • 🎯🎯 `recursion_transfinie_existence_reduite`
        { bon ordre, P2, P3, P4 } ⊢ (∀x∈E)(∃p)( est_essai(p,x) ).

INVARIANT vérifié partout : theorie_ensembles() = 22 ; conclusions non vacuous ; le
résidu est EXACTEMENT (P2)+(P3)+(P4) (et le bon ordre pour l'existence).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation as Rz
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final import (
    membres_fonctionnels, equation_au_point, realisation_famille,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import couverture_totale
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R


def _vh(t):
    """Règle-test : valeur-règle OPAQUE vh(t) := app('c60_rule', t) (sans τ interne)."""
    return E.app("c60_rule", t)


def _Dfam(t):
    """La famille concrète Dfam_real(t) pour la règle-test."""
    return Rz.Dfam_real(_vh, "E", "G", t, "Vval")


def test_theorie_reste_22():
    """L'import et l'usage du module n'altèrent PAS theorie_ensembles() (=22)."""
    assert len(E.theorie_ensembles().axiomes) == 22
    Rz.membres_fonctionnels_realise(_vh)
    Rz.equation_au_point_realise(_vh)
    Rz.realisation_famille_reduite(_vh)
    Rz.recursion_transfinie_existence_reduite(_vh)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_Dfam_real_axiome():
    """L'axiome S8 de Dfam_real est instanciable (équivalence membership), via la
    forme attendue (p∈Dfam_real(x)) ⇔ (p∈𝔓(E×V) et (∃y∈seg)est_essai(p,y))."""
    from bourbaki.logique.i_1_termes_relations.formule import equiv
    eq = Rz.membre_Dfam_real(_vh)
    vp, vx = var("pD"), var("x0")
    Dx = Rz.Dfam_real(_vh, "E", "G", vx, "Vval")
    cible = equiv(appartient(vp, Dx),
                  Rz._corps_Dfam_real(_vh, "E", "G", vx, vp, "Vval", "yD"))
    assert eq.conclusion == cible
    assert len(E.theorie_ensembles().axiomes) == 22


def test_P1_membres_fonctionnels_realise():
    """🎯 (P1) ⊢ membres_fonctionnels(Dfam_real(x))  [CLOS, 0 hyp]."""
    r = Rz.membres_fonctionnels_realise(_vh)
    Dx = Rz.Dfam_real(_vh, "E", "G", var("x0"), "Vval")
    assert r.conclusion == membres_fonctionnels(Dx, "pmf")
    assert r.est_clos
    assert len(r.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


def test_P5_equation_au_point_realise():
    """🎯 (P5) ⊢ vh(x)=vh(x)  ( = equation_au_point(vh(x),vh,x) )  [CLOS, 0 hyp]."""
    r = Rz.equation_au_point_realise(_vh)
    vx = var("x0")
    assert r.conclusion == equation_au_point(_vh(vx), _vh, vx)
    assert r.conclusion == egal(_vh(vx), _vh(vx))
    assert r.est_clos


def test_realisation_famille_reduite():
    """🎯 { P2, P3, P4 } ⊢ realisation_famille(Dfam_real, vh, vh, R, E)  [3 hyps honnêtes]."""
    r = Rz.realisation_famille_reduite(_vh)
    cible = realisation_famille(_Dfam, _vh, _vh, "G", "E", "x0", "ytf")
    assert r.conclusion == cible
    # EXACTEMENT 3 clauses résiduelles : (P2),(P3),(P4)
    assert len(r.hypotheses) == 3
    assert Rz.clause_P2(_vh, "E", "G", "x0", "Vval", "ytf") in r.hypotheses
    assert Rz.clause_P3(_vh, "E", "G", "x0", "Vval", "ytf") in r.hypotheses
    assert Rz.clause_P4(_vh, "E", "G", "x0", "Vval", "ytf") in r.hypotheses
    # (P1) et (P5) ne sont PAS des hypothèses (déchargées par construction)
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_capstone_existence_reduite():
    """🎯🎯 EXISTENCE C60 : { bon ordre, P2, P3, P4 } ⊢ (∀x∈E)(∃p)(est_essai(p,x))."""
    r = Rz.recursion_transfinie_existence_reduite(_vh)
    R = _graphe_R("G")
    ve = var("E")
    couvert = couvert_essai(_vh, R, ve)
    # conclusion EXACTE = couverture totale par essais (l'existence de la solution)
    assert r.conclusion == couverture_totale(couvert, ve, "x0tf")
    # QUATRE hypothèses honnêtes : bon ordre + (P2)+(P3)+(P4) — PLUS de realisation_famille
    assert len(r.hypotheses) == 4
    assert E.est_bien_ordonne(R, ve) in r.hypotheses
    assert Rz.clause_P2(_vh, "E", "G", "x0tf", "Vval", "ytf") in r.hypotheses
    assert Rz.clause_P3(_vh, "E", "G", "x0tf", "Vval", "ytf") in r.hypotheses
    assert Rz.clause_P4(_vh, "E", "G", "x0tf", "Vval", "ytf") in r.hypotheses
    # le bundle monolithique realisation_famille N'EST PLUS une hypothèse
    Dfam = lambda t: Rz.Dfam_real(_vh, "E", "G", t, "Vval")
    rf = realisation_famille(Dfam, _vh, _vh, "G", "E", "x0tf", "ytf")
    assert rf not in r.hypotheses
    # non vacuous + theorie intangible
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
