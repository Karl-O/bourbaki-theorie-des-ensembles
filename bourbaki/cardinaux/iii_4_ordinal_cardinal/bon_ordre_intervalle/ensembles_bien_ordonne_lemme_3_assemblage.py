"""§III.3 — LEMME L4 : assemblage final  { L3 } ⊢ cardinaux_bien_ordonnes(a).

────────────────────────────────────────────────────────────────────────────────
BUT GLOBAL (E.III.3, Théorème : ≤ bien-ordonne les cardinaux) :

    cardinaux_bien_ordonnes(a) =
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ).

CE MODULE clôt l'ULTIME maillon d'assemblage de la ROUTE R3 : la réduction du but
entier à l'unique pièce ordinale L3 = bon_ordre_intervalle(a) (« [0,a] est bien
ordonné par l'ordre (induit) des cardinaux »).

L3 (= bon_ordre_intervalle(a), ensembles_ordinal_cardinal_correspondance.py) :

        est_bien_ordonne( ≤_induit , [0,a] ).

MACHINERIE RÉUTILISÉE (déjà valide, vérifiée empiriquement) :

  • cardinaux_bien_ordonnes_de_bon_ordre(a)  (ensembles_ordinal_cardinal_correspondance)
        est un THÉORÈME CONDITIONNEL :  { bon_ordre_intervalle(a) } ⊢ cardinaux_bien_ordonnes(a).
        Vérifié : il a EXACTEMENT 1 hypothèse == bon_ordre_intervalle('a'), et sa
        conclusion == cardinaux_bien_ordonnes('a') (les deux par égalité de Formule).

ASSEMBLAGE (pur LCF, INCONDITIONNEL en tant que MÉTA-construction) :

  1. red  = cardinaux_bien_ordonnes_de_bon_ordre(a)        # { L3 } ⊢ cible
  2. cond = loi_deduction(L3, red)                         # ⊢ ( L3 ⇒ cible )   [CLOS, théorème]
  3. l3   = assume(L3)                                     # { L3 } ⊢ L3
  4. L4   = modus_ponens(l3, cond)                         # { L3 } ⊢ cible

Étape 2 décharge l'unique hypothèse L3 → la conditionnelle L3 ⇒ cible est un
THÉORÈME CLOS (est_clos=True). Étape 4 est le « modus ponens direct » sur le
théorème conditionnel demandé par la mission : on réintroduit L3 comme hypothèse
explicite et on conclut la cible.

STATUT du résultat L4 :
  • Sequent VISÉ atteint LITTÉRALEMENT :  { bon_ordre_intervalle(a) } ⊢ cardinaux_bien_ordonnes(a).
  • CONDITIONNEL (1 seule hypothèse résiduelle = L3 = bon_ordre_intervalle(a)).
  • La conditionnelle CLOSE  ⊢ ( L3 ⇒ cardinaux_bien_ordonnes(a) )  est exportée
    (lemme_3_conditionnelle_close) : c'est un théorème SANS hypothèse — toute la
    combinatoire en aval de L3 est ainsi prouvée INCONDITIONNELLEMENT, ne reste que
    L3 lui-même (la pièce ordinale §III.2, reportée ailleurs).

INVARIANT : theorie_ensembles() = 22.  Rien postulé, aucune tautologie/affaibli :
la cible est strictement DÉRIVÉE de L3 via la réduction déjà valide.  Aucun fichier
existant n'est modifié (module + test NEUFS).
"""
from __future__ import annotations

from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import (
    cardinaux_bien_ordonnes_de_bon_ordre,
    bon_ordre_intervalle,
)


def lemme_3_hypothese(a="a"):
    """L3 = bon_ordre_intervalle(a) (Formule) — l'unique hypothèse de la réduction.

        est_bien_ordonne( ≤_induit , [0,a] ).

    C'est, AVEC SES BINDERS PAR DÉFAUT, LITTÉRALEMENT l'unique hypothèse résiduelle
    de cardinaux_bien_ordonnes_de_bon_ordre(a) (vérifié par égalité de Formule)."""
    return bon_ordre_intervalle(a)


def lemme_3_conditionnelle_close(a="a"):
    """⊢ ( bon_ordre_intervalle(a) ⇒ cardinaux_bien_ordonnes(a) )   [THÉORÈME CLOS].

    On décharge (loi_deduction, C6) l'unique hypothèse L3 du théorème conditionnel
    déjà valide cardinaux_bien_ordonnes_de_bon_ordre(a).  Le résultat n'a PLUS aucune
    hypothèse (est_clos=True) : toute la machinerie en aval de L3 est prouvée
    INCONDITIONNELLEMENT.  Seule la pièce ordinale L3 reste à fournir (ailleurs)."""
    L3 = lemme_3_hypothese(a)
    red = cardinaux_bien_ordonnes_de_bon_ordre(a)          # { L3 } ⊢ cible
    return N.loi_deduction(L3, red)                         # ⊢ ( L3 ⇒ cible )   [CLOS]


def L4_cardinaux_bien_ordonnes(a="a"):
    """🎯 LEMME L4 (CIBLE DE LA MISSION) :

        { bon_ordre_intervalle(a) }  ⊢  cardinaux_bien_ordonnes(a).

    Modus ponens direct sur le théorème conditionnel (CLOS) L3 ⇒ cible : on
    réintroduit L3 comme hypothèse explicite (assume) et on détache la cible.

    Le sequent VISÉ est atteint LITTÉRALEMENT (test miroir) :
      • hypotheses == { bon_ordre_intervalle(a) }   (l'unique pièce ordinale, L3),
      • conclusion == cardinaux_bien_ordonnes(a).

    CONDITIONNEL au seul L3 (report ordinal↔cardinal §III.2).  theorie=22, rien
    postulé, aucune tautologie : cible STRICTEMENT dérivée de L3."""
    L3 = lemme_3_hypothese(a)
    cond = lemme_3_conditionnelle_close(a)                  # ⊢ ( L3 ⇒ cible )   [CLOS]
    l3 = N.assume(L3)                                       # { L3 } ⊢ L3
    return N.modus_ponens(l3, cond)                         # { L3 } ⊢ cible


__all__ = [
    "lemme_3_hypothese",
    "lemme_3_conditionnelle_close",
    "L4_cardinaux_bien_ordonnes",
]
