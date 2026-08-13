"""§III.3 — La TRANSPOSITION τ_{S,p,q} : Δ_S modifiée en deux points.

La transposition d'un ensemble S échangeant deux points distincts p, q ∈ S est
la bijection identité Δ_S (diagonale) MODIFIÉE : on retire les deux paires fixes
(p,p), (q,q) du graphe identité et on ajoute les deux paires croisées (p,q), (q,p).

    τ := (Δ_S ∖ {(p,p), (q,q)}) ∪ {(p,q), (q,p)}.

C'est le terme le plus proche de Δ_S (le MODÈLE, ensembles_equipotence) : Δ_S relie
chaque u à lui-même, et la transposition ne change que les images de p et q (échange).

Sous-package :
  • _membre      : `transpo_membre`  ⊢ (x,y)∈τ ⇔ (clauses de cas) — la brique CLÉ ;
  • _bijection   : transpo_fonctionnel, transpo_domaine (CLOS) ;
  • _injective   : transpo_injective (CLOS) ;
  • _valeur_image: transpo_valeur_q, transpo_image (CLOS) ;
  • _existence   : transposition_existe (les 4 conjoints + τ(q)=p + S5 témoin).

Re-exporte l'API publique complète : transpo, transpo_membre, transpo_fonctionnel,
transpo_domaine, transpo_injective, transpo_image, transpo_valeur_q,
transposition_existe.
"""
from __future__ import annotations

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._membre import (
    transpo, transpo_membre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._bijection import (
    transpo_fonctionnel, transpo_domaine)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._injective import (
    transpo_injective)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._valeur_image import (
    transpo_valeur_q, transpo_image)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._existence import (
    transposition_existe)

__all__ = ["transpo", "transpo_membre", "transpo_fonctionnel", "transpo_domaine",
           "transpo_injective", "transpo_image", "transpo_valeur_q",
           "transposition_existe"]
