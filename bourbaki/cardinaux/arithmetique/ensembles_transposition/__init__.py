"""§III.3 — La TRANSPOSITION τ_{S,p,q} : Δ_S modifiée en deux points.

La transposition d'un ensemble S échangeant deux points distincts p, q ∈ S est
la bijection identité Δ_S (diagonale) MODIFIÉE : on retire les deux paires fixes
(p,p), (q,q) du graphe identité et on ajoute les deux paires croisées (p,q), (q,p).

    τ := (Δ_S ∖ {(p,p), (q,q)}) ∪ {(p,q), (q,p)}.

C'est le terme le plus proche de Δ_S (le MODÈLE, ensembles_equipotence) : Δ_S relie
chaque u à lui-même, et la transposition ne change que les images de p et q (échange).

Sous-package :
  • _membre   : `transpo_membre`  ⊢ (x,y)∈τ ⇔ (clauses de cas) — la brique CLÉ ;
  • _bijection: les 4 conjoints de est_bijection_de(τ,S,S) + `transpo_valeur_q`.

Re-exporte l'API publique : transpo, transpo_membre, transposition_existe,
transpo_valeur_q (selon ce qui est CLOS).
"""
from __future__ import annotations

from bourbaki.cardinaux.arithmetique.ensembles_transposition._membre import (
    transpo, transpo_membre)

__all__ = ["transpo", "transpo_membre"]

# Les théorèmes de bijection / existence sont ré-exportés s'ils sont clos.
try:
    from bourbaki.cardinaux.arithmetique.ensembles_transposition._bijection import (
        transpo_fonctionnel, transpo_domaine, transpo_injective, transpo_image,
        transpo_valeur_q, transposition_existe)
    __all__ += ["transpo_fonctionnel", "transpo_domaine", "transpo_injective",
                "transpo_image", "transpo_valeur_q", "transposition_existe"]
except ImportError:
    pass
