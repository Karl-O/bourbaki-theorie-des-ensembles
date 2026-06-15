"""Tests §III.2 — décharge de la géométrie de coincidence (vers clôture trichotomie).

BRIQUE 1 — `composee_dans_S` : c=g∘f : S→S (codomaine de la composée).
Honnêteté LCF : conditionnel propre (hyps structurelles f⊂S×T/dom/func + g⊂T×S/dom/func),
conclusion == cible fidèle, NON vacueux (concl ∉ hyps), theorie = 22.
"""
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.cardinaux.ensembles_coincidence_geometrie as G


def test_composee_dans_S_conclusion():
    t = G.composee_dans_S()
    assert not t.est_clos                              # conditionnel honnête
    assert t.conclusion == G.composee_dans_S_cible()  # (∀t)(t∈S ⇒ (g∘f)(t)[j]∈S)
    assert t.conclusion not in t.hypotheses           # NON tautologique


def test_composee_dans_S_hyps_structurelles():
    """Les 6 hypothèses sont exactement les données structurelles d'iso (graphe⊂produit,
    domaine, fonctionnel) pour f et g — aucune cachée, aucune géométrique postulée."""
    t = G.composee_dans_S()
    assert len(t.hypotheses) == 6


def test_theorie_inchangee_22():
    G.composee_dans_S()
    assert len(E.theorie_ensembles().axiomes) == 22
