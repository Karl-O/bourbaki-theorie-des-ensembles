"""§III.2 — LEMME L3 : { L0, L2 } ⊢ bon_ordre_intervalle(a).

────────────────────────────────────────────────────────────────────────────────
BUT GLOBAL (E.III.3, Théorème : ≤ bien-ordonne les cardinaux) :

    cardinaux_bien_ordonnes(a) =
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ).

ROUTE R3 — la cible se réduit (cardinaux_bien_ordonnes_de_bon_ordre, déjà valide,
puis L4 ensembles_bien_ordonne_lemme_3_assemblage) à L'UNIQUE pièce ordinale

    L3 = bon_ordre_intervalle(a) = est_bien_ordonne( ≤_induit , [0,a] ).

CE MODULE prouve L3 PROPREMENT DIT par sa décomposition (Définition 1, E.III.2.1).
PAR CONSTRUCTION (E.est_bien_ordonne) :

    bon_ordre_intervalle(a) = est_bien_ordonne( ≤_induit , [0,a] )
        =  est_relation_ordre_dans( ≤_induit , [0,a] )      [L0 — la partie ORDRE]
       et  clause_plus_petit( ≤_induit , [0,a] )            [L2 — la CLAUSE de plus
                                                              petit élément]

(vérifié par décomposition de conjonction : les DEUX conjoints de
bon_ordre_intervalle(a) sont EXACTEMENT, dans l'ordre, la conclusion de L0 et la
formule L2 — cf. test miroir).

────────────────────────────────────────────────────────────────────────────────
LE SEQUENT VISÉ — assemblage LITTÉRAL des deux moitiés :

    bon_ordre_intervalle_de_ordre_et_clause :
        { L0_pred , L2 }  ⊢  bon_ordre_intervalle(a),

où L0_pred := est_relation_ordre_dans(≤_induit,[0,a]) (= conclusion de L0) et
L2 := clause_plus_petit(≤_induit,[0,a]) (= report_clause_plus_petit(a)).  C'est la
pure CONJONCTION (conjonction_intro) des deux hypothèses : « E ordonné par R » ET
« toute partie non vide de E a un plus petit élément » donnent « E bien ordonné par
R » (Déf. 1).  Aucune autre hypothèse, aucune tautologie : la conclusion est
strictement la conjonction des deux prémisses.

────────────────────────────────────────────────────────────────────────────────
SALVAGE GRADUÉ — la partie ORDRE (L0) étant DÉJÀ PROUVÉE INCONDITIONNELLEMENT
(relation_ordre_dans_intervalle, CLOS : transitivité + ANTISYMÉTRIE Cantor–Bernstein
+ réflexivité-implicite + réflexivité-dans-[0,a]), on l'INJECTE et on n'a plus que la
clause en report :

  ✅ bon_ordre_intervalle_conditionnelle_close :
        ⊢ ( L0_pred ⇒ ( L2 ⇒ bon_ordre_intervalle(a) ) )   [THÉORÈME CLOS].
     Toute la combinatoire d'assemblage est ainsi prouvée SANS hypothèse.

  ⊢ bon_ordre_intervalle_depuis_clause :
        { L2 }  ⊢  bon_ordre_intervalle(a).
     L0 fourni PAR PREUVE (relation_ordre_dans_intervalle, INCONDITIONNEL) ; la SEULE
     hypothèse résiduelle est la CLAUSE de plus petit élément L2 (= report_clause_
     plus_petit(a), le bottleneck ordinal↔cardinal irréductible).

INVARIANT : theorie_ensembles() = 22.  Rien postulé, aucune tautologie/affaibli :
L3 est strictement la conjonction de L0 et L2 (Déf. 1).  Aucun fichier existant
modifié (module + test NEUFS).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, composantes_conjonction,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import (
    bon_ordre_intervalle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal import (
    report_clause_plus_petit,
)


def lemme_0_ordre_predicat(a="a"):
    """L0_pred = la conclusion de la partie ORDRE :  est_relation_ordre_dans(≤_induit,[0,a]).

    C'est EXACTEMENT le 1ᵉʳ conjoint de bon_ordre_intervalle(a) (= est_bien_ordonne)
    et la conclusion du théorème CLOS relation_ordre_dans_intervalle(a) (partie ORDRE
    PROUVÉE INCONDITIONNELLEMENT : transitivité + antisymétrie Cantor–Bernstein +
    réflexivité-implicite + réflexivité-dans-[0,a])."""
    return composantes_conjonction(bon_ordre_intervalle(a))[0]


def lemme_2_clause(a="a"):
    """L2 = la CLAUSE de plus petit élément :  clause_plus_petit(≤_induit,[0,a]).

        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ R_induit{m,x}) ) ).

    C'est EXACTEMENT le 2ᵉ conjoint de bon_ordre_intervalle(a), et c'est
    report_clause_plus_petit(a) (le report ordinal↔cardinal irréductible)."""
    return report_clause_plus_petit(a)


def bon_ordre_intervalle_de_ordre_et_clause(a="a"):
    """🎯 LEMME L3 (SEQUENT VISÉ) :

        { L0_pred , L2 }  ⊢  bon_ordre_intervalle(a).

    Pur assemblage de la Définition 1 (E.III.2.1) : « E ordonné par R » (L0_pred) ET
    « toute partie non vide de E a un plus petit élément » (L2) donnent « E bien
    ordonné par R » (= bon_ordre_intervalle(a)).  C'est la CONJONCTION littérale
    (conjonction_intro) des deux hypothèses supposées.

    Vérifié (test miroir) :
      • hypotheses == { L0_pred , L2 }   (exactement 2 hypothèses, les deux moitiés),
      • conclusion == bon_ordre_intervalle(a) LITTÉRALEMENT.

    Aucune tautologie : la conclusion est la conjonction stricte des deux prémisses,
    distinctes de la conclusion.  theorie=22, rien postulé."""
    L0_pred = lemme_0_ordre_predicat(a)
    L2 = lemme_2_clause(a)
    return conjonction_intro(N.assume(L0_pred), N.assume(L2))   # { L0, L2 } ⊢ L3


def bon_ordre_intervalle_conditionnelle_close(a="a"):
    """⊢ ( L0_pred ⇒ ( L2 ⇒ bon_ordre_intervalle(a) ) )   [THÉORÈME CLOS].

    On décharge (loi_deduction, C6) les DEUX hypothèses du sequent L3.  Le résultat
    n'a PLUS aucune hypothèse (est_clos=True) : toute la combinatoire d'assemblage de
    est_bien_ordonne à partir de ses deux moitiés est prouvée INCONDITIONNELLEMENT.
    Restent à fournir (ailleurs) L0 (DÉJÀ prouvé, relation_ordre_dans_intervalle) et
    L2 (le report ordinal↔cardinal)."""
    L0_pred = lemme_0_ordre_predicat(a)
    L2 = lemme_2_clause(a)
    thm = bon_ordre_intervalle_de_ordre_et_clause(a)           # { L0, L2 } ⊢ L3
    cond2 = N.loi_deduction(L2, thm)                           # { L0 } ⊢ ( L2 ⇒ L3 )
    return N.loi_deduction(L0_pred, cond2)                     # ⊢ ( L0 ⇒ ( L2 ⇒ L3 ) ) [CLOS]


# @livre Ch.III §3.2 Demo.1 | E III.24 L.16-30 | PDF p.127
def bon_ordre_intervalle_depuis_clause(a="a"):
    """⊢ { L2 }  ⊢  bon_ordre_intervalle(a).

    🎯 SALVAGE — la partie ORDRE L0 est fournie PAR PREUVE (relation_ordre_dans_
    intervalle, CLOS, INCONDITIONNEL) ; on la conjugue avec la clause L2 supposée.
    La SEULE hypothèse résiduelle est la CLAUSE de plus petit élément L2 (= report_
    clause_plus_petit(a)), le bottleneck ordinal↔cardinal irréductible.

    Vérifié (test miroir) :
      • hypotheses == { L2 }   (l'unique report, la clause),
      • conclusion == bon_ordre_intervalle(a) LITTÉRALEMENT.

    theorie=22, rien postulé : L0 vient d'un théorème CLOS, L2 est l'unique report."""
    L0 = relation_ordre_dans_intervalle(a)                     # est_relation_ordre_dans  CLOS
    L2 = lemme_2_clause(a)
    return conjonction_intro(L0, N.assume(L2))                 # { L2 } ⊢ L3


__all__ = [
    "lemme_0_ordre_predicat",
    "lemme_2_clause",
    "bon_ordre_intervalle_de_ordre_et_clause",
    "bon_ordre_intervalle_conditionnelle_close",
    "bon_ordre_intervalle_depuis_clause",
]
