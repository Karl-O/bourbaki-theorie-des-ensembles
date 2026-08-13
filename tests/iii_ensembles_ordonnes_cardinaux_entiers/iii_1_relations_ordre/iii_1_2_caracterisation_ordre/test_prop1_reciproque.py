"""Tests — PROPOSITION 1 (E.III.2), RÉCIPROQUE (suffisance) et ÉQUIVALENCE.

Chaque test APPELLE la fonction-théorème, puis vérifie :
  • la conclusion EXACTE == cible reconstruite avec les MÊMES constructeurs ;
  • les hypothèses == exactement les conditions load-bearing (aucune parasite ;
    le CHAMP n'apparaît PAS dans la réciproque ; la conclusion n'est pas une hyp) ;
  • l'invariant theorie_ensembles().axiomes == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, equiv
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import graphe_identite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    reflexivite_sur, antisymetrie, transitivite_rel, est_ordre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_2_caracterisation_ordre import (
    ensembles_prop1_caracterisation as D)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_2_caracterisation_ordre import (
    ensembles_prop1_reciproque as R)

G, Es = var("G"), var("E")


def _cond_a():
    """composee(G,G) = G."""
    return E.egal(E.composee(G, G), G)


def _cond_b():
    """inter(G, reciproque(G)) = graphe_identite(E)  (= Δ_E)."""
    return E.egal(E.intersection(G, E.reciproque(G)), graphe_identite(Es))


def _hyps_reciproque():
    """Les SEULES conditions honnêtes de la suffisance (PAS le champ)."""
    return {_cond_a(), _cond_b()}


# Les liants de la réciproque sont « u, v, s » (≠ « x » que graphe_identite laisse
# libre dans la condition b ; on ne peut C27-généraliser sur ce nom-là).
UU, VV, SS = "u", "v", "s"


# ── transitivité (de a) ───────────────────────────────────────────────────────
def test_transitivite_conclusion():
    t = R.reciproque_transitivite("G", "E")
    assert t.conclusion == transitivite_rel(G, UU, VV, SS)
    assert t.hypotheses == {_cond_a()}
    assert t.conclusion not in t.hypotheses


# ── antisymétrie (de b) ───────────────────────────────────────────────────────
def test_antisymetrie_conclusion():
    t = R.reciproque_antisymetrie("G", "E")
    assert t.conclusion == antisymetrie(G, UU, VV)
    assert t.hypotheses == {_cond_b()}
    assert t.conclusion not in t.hypotheses


# ── réflexivité sur E (de b) ──────────────────────────────────────────────────
def test_reflexivite_conclusion():
    t = R.reciproque_reflexivite("G", "E")
    assert t.conclusion == reflexivite_sur(G, Es, UU)
    assert t.hypotheses == {_cond_b()}
    assert t.conclusion not in t.hypotheses


# ── RÉCIPROQUE complète : est_ordre(G,E,u,v,s) ────────────────────────────────
def test_reciproque_conclusion():
    t = R.caracterisation_ordre_reciproque("G", "E")
    assert t.conclusion == est_ordre(G, Es, UU, VV, SS)
    # exactement les deux conditions a) et b) ; AUCUN champ ; conclusion ∉ hyps
    assert t.hypotheses == _hyps_reciproque()
    assert D.champ(G, Es) not in t.hypotheses
    assert t.conclusion not in t.hypotheses


# ── ÉQUIVALENCE complète (bonus) sous le champ ────────────────────────────────
def test_equivalence_conclusion():
    t = R.proposition1_equivalence("G", "E")
    cible = equiv(est_ordre(G, Es), et(_cond_a(), _cond_b()))
    assert t.conclusion == cible
    # le champ est la SEULE hypothèse résiduelle (requise par le sens direct)
    assert t.hypotheses == {D.champ(G, Es)}
    assert t.conclusion not in t.hypotheses


# ── Invariant : aucun axiome ajouté ───────────────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
