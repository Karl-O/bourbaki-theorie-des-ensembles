"""Tests §III.2 — dom(h) est un SEGMENT de E (initialité) pour l'iso MAXIMAL h.

On certifie la clause d'INITIALITÉ de dom(h) et est_segment(dom h, R, E), SOUS
l'hypothèse de codomaine explicite val_dans_F (φ(p)∈F le long des isos témoins),
JAMAIS postulée comme théorème.  theorie_ensembles() reste = 22 ; conclusions non
tautologiques (y∈dom h / est_segment ∉ hypothèses).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, appartient, Formule
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_dom_segment as DS


def test_val_dans_F_est_formule():
    """L'hypothèse de codomaine est une FORMULE (posée, non un théorème)."""
    f = DS.val_dans_F()
    assert isinstance(f, Formule)


def test_dom_h_initial_sous_val():
    """{ val_dans_F } ⊢ initialité de dom(h)  — CONDITIONNEL, NON vacueux."""
    init = DS.dom_h_initial_sous_val()
    assert not init.est_clos                       # CONDITIONNEL (1 hypothèse explicite)
    assert len(init.hypotheses) == 1
    assert DS.val_dans_F() in init.hypotheses
    assert init.conclusion == DS.dom_h_initial_cible()
    assert init.conclusion not in init.hypotheses


def test_dom_h_est_segment_sous_val():
    """{ val_dans_F } ⊢ est_segment(dom h, R, E)  — CONDITIONNEL, NON vacueux."""
    seg = DS.dom_h_est_segment_sous_val()
    assert not seg.est_clos                        # CONDITIONNEL (1 hypothèse explicite)
    assert len(seg.hypotheses) == 1
    assert DS.val_dans_F() in seg.hypotheses
    assert seg.conclusion == DS.dom_h_est_segment_cible()
    assert seg.conclusion not in seg.hypotheses


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_parametrable():
    init = DS.dom_h_initial_sous_val("A", "Ra", "B", "Rb")
    assert not init.est_clos
    assert len(init.hypotheses) == 1
    assert DS.val_dans_F("A", "Ra", "B", "Rb") in init.hypotheses
    assert init.conclusion == DS.dom_h_initial_cible("A", "Ra", "B", "Rb")


def test_dom_h_est_segment_prouve():
    """🎯 est_segment(dom h, R, E) CLOS — val_dans_F DÉRIVÉE (pont via_pont)."""
    th = DS.dom_h_est_segment_prouve()
    assert th.conclusion == DS.dom_h_est_segment_cible()
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22
