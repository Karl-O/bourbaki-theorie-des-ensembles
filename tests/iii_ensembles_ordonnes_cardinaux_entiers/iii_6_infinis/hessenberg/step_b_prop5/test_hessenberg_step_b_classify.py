"""Tests — CLASSIFICATION du résidu STEP B de Hessenberg (`ensembles_hessenberg_step_b_classify`).

Vérifie que la classification des 12 hyps est MÉCANIQUEMENT exacte (invariants internes),
que le seul échange latéral honnête (`discharge_u_disjoint`) ne FAUSSE rien (compte
inchangé, conclusion préservée), et que theorie=22.  AUCUNE clôture truquée n'est testée :
le résidu irréductible est EXPOSÉ.
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_step_b_classify import (
    classification, discharge_u_disjoint,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_classification_12_hyps():
    thm, table = classification()
    assert len(thm.hypotheses) == 12
    assert len(table) == 12
    # exactement UNE hyp est déchargeable (latéralement) ; 11 irréductibles.
    lat = [r for r in table if "LATÉRAL" in r["dischargeable"]]
    assert len(lat) == 1
    irr = [r for r in table if r["dischargeable"] == "irreducible"]
    assert len(irr) == 11
    # aucune hyp non classée
    assert all("???" not in r["label"] for r in table)


def test_discharge_u_disjoint_is_lateral():
    """L'échange latéral préserve conclusion et NE réduit PAS le compte (12→12)."""
    thm, _ = classification()
    d = discharge_u_disjoint()
    assert d.conclusion == thm.conclusion
    assert len(d.hypotheses) == 12          # échange, pas réduction
    assert d.conclusion not in d.hypotheses  # non vacuous


def test_blocker_is_somme_disjointe():
    """Le blocker architectural (HYP 2 / HYP 11) porte bien les tags somme-disjointe."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import afficher_f as af
    thm, _ = classification()
    tagged = [h for h in thm.hypotheses if "paire(vide(), vide())" in af(h)]
    # au moins les 2 hyps cadre⊔ (S₀²∪cadre⊔=Z² et ψ sur cadre⊔)
    assert len(tagged) >= 2
