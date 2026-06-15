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


def test_raccord_phip_conclusion():
    """BRIQUE 4 — raccord φ'(c(u))=φ(u), c=φ'⁻¹∘φ.  Conditionnel propre, fidèle, non vacueux."""
    t = G.raccord_phip()
    assert not t.est_clos
    assert t.conclusion == G.raccord_phip_cible()
    assert t.conclusion not in t.hypotheses


def test_raccord_phip_hyps():
    t = G.raccord_phip()
    assert len(t.hypotheses) == 5


def test_retraction_phi_conclusion():
    """Sous-lemme BRIQUE 3 — φ⁻¹(φ(x))=x (retraction de φ).  Point φ(x) en « j » pour
    éviter la capture du liant « y » de valeur_caracterisation.  2 hyps {dom φ=S, φ⁻¹ func}."""
    t = G.retraction_phi()
    assert not t.est_clos
    assert t.conclusion == G.retraction_phi_cible()
    assert t.conclusion not in t.hypotheses
    assert len(t.hypotheses) == 2


def test_theorie_inchangee_22():
    G.composee_dans_S()
    G.raccord_phip()
    G.retraction_phi()
    assert len(E.theorie_ensembles().axiomes) == 22
