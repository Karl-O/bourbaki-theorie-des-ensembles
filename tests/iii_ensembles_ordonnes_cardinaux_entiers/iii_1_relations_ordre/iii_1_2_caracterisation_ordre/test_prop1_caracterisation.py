"""Tests — PROPOSITION 1 (E.III.2), sens direct : G∘G=G et G∩G⁻¹=Δ_E.

Chaque test APPELLE la fonction-théorème, puis vérifie :
  • la conclusion EXACTE == cible reconstruite avec les MÊMES constructeurs ;
  • les hypothèses == exactement { est_ordre(G,E), champ(G,E) } (aucune parasite ;
    la conclusion n'est pas elle-même une hypothèse) ;
  • l'invariant theorie_ensembles().axiomes == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_2_caracterisation_ordre import (
    ensembles_prop1_caracterisation as P)

G, Es = var("G"), var("E")


def _cible_a():
    """composee(G,G) = G."""
    return E.egal(E.composee(G, G), G)


def _cible_b():
    """inter(G, reciproque(G)) = graphe_identite(E)  (= Δ_E)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import graphe_identite
    return E.egal(E.intersection(G, E.reciproque(G)), graphe_identite(Es))


def _hyps_attendues():
    return {est_ordre(G, Es), P.champ(G, Es)}


# ── champ(G,E) = G ⊆ E×E ──────────────────────────────────────────────────────
def test_champ_construit():
    assert P.champ(G, Es) == E.inclus(G, E.produit(Es, Es))


# ── (a)  composee(G,G) = G ────────────────────────────────────────────────────
def test_composee_idempotente_conclusion():
    t = P.composee_idempotente("G", "E")
    assert t.conclusion == _cible_a()


def test_composee_idempotente_hypotheses():
    t = P.composee_idempotente("G", "E")
    assert t.hypotheses == _hyps_attendues()
    assert t.conclusion not in t.hypotheses


# ── (b)  inter(G, G⁻¹) = Δ_E ──────────────────────────────────────────────────
def test_intersection_reciproque_conclusion():
    t = P.intersection_reciproque_est_diagonale("G", "E")
    assert t.conclusion == _cible_b()


def test_intersection_reciproque_hypotheses():
    t = P.intersection_reciproque_est_diagonale("G", "E")
    assert t.hypotheses == _hyps_attendues()
    assert t.conclusion not in t.hypotheses


# ── (a) et (b) réunies ────────────────────────────────────────────────────────
def test_caracterisation_sens_direct():
    t = P.caracterisation_ordre_sens_direct("G", "E")
    assert t.conclusion == et(_cible_a(), _cible_b())
    assert t.hypotheses == _hyps_attendues()
    assert t.conclusion not in t.hypotheses


# ── Invariant : aucun axiome ajouté ───────────────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
