"""§II.5 — PROPOSITION 10 (E II.37) : commutation intersection/produit, K-générale :
   ⋂_{κ∈K}(∏_{ι∈I} X_{ι,κ}) = ∏_{ι∈I}(⋂_{κ∈K} X_{ι,κ}),  K ≠ ∅.

Vérifie (un import NE PROUVE RIEN) : on APPELLE le théorème, et on contrôle que sa
conclusion EST la cible (mêmes constructeurs : implication des 4 hypothèses honnêtes
vers l'égalité ⋂P = ∏Φ), qu'il est CLOS (0 hypothèse pendante, tout déchargé en
implication comme le gabarit binaire), et que la théorie reste à 22 axiomes."""
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import ensembles_prop10_inter_produit_ii5 as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import antecedent_consequent


def test_inter_produit_egal_produit_inter_close():
    th = M.inter_produit_egal_produit_inter()
    # CLOS : 0 hypothèse pendante (tout déchargé en implication, comme le binaire)
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    # théorie inchangée (aucun axiome neuf)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_conclusion_est_la_cible():
    th = M.inter_produit_egal_produit_inter()
    # conclusion EXACTE == cible (mêmes constructeurs)
    assert th.conclusion == M._cible()


def test_conclusion_structure_bourbaki():
    """Le membre droit de l'implication EST l'égalité ⋂_{κ∈K}P_κ = ∏_{ι∈I}Φ_ι,
    construite avec les MÊMES constructeurs (inter_famille / produit_famille)."""
    th = M.inter_produit_egal_produit_inter()
    ante, cons = antecedent_consequent(th.conclusion)
    gauche = E.inter_famille(var("P"), var("K"))       # ⋂_{κ∈K} P_κ
    droite = E.produit_famille(var("Phi"), var("I"))   # ∏_{ι∈I} Φ_ι
    assert cons == egal(gauche, droite)
    # l'antécédent EST la conjonction des 4 hypothèses honnêtes (K≠∅ ∧ H_P ∧ H_Φ ∧ H_coh)
    hyp = M._hypotheses(var("P"), var("Phi"), var("COL"), var("ROW"), var("I"), var("K"))
    assert ante == hyp
    # et donc la conclusion entière est bien l'implication hyps ⇒ égalité
    assert th.conclusion == impl(hyp, egal(gauche, droite))
