"""§III.4 — ORDINAL↔CARDINAL : ASSEMBLAGE FINAL vers cardinaux_bien_ordonnes(a).

🎯 BUT (bottleneck #1 de la campagne ℕ, ensembles_recurrence_C61) :

    cardinaux_bien_ordonnes(a) =
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ),

« toute partie non vide de [0,a] a un plus petit cardinal ».  ÉTAPE 1 de l'arc
qui débloque principe_recurrence ⇒ C61 ⇒ fini_downward ⇒ ℕ inconditionnel.

────────────────────────────────────────────────────────────────────────────────
RÉSULTAT DE CE CHANTIER (salvage fort gradué) — la cible est RÉDUITE à UN report
minimal, PUR et CONCRET, la partie « ordre » étant entièrement ACQUISE :

  ✅ INCONDITIONNEL (paquet ensembles_ordinal_cardinal_*) :
     • plus_petit_de_bon_ordre        — ENGINE : extraction du plus petit élément d'un
                                         bon ordre (clause Déf.1 E.III.2.1).  [bon_ordre]
     • cardinaux_bien_ordonnes_de_bon_ordre :
            { est_bien_ordonne(≤_induit,[0,a]) } ⊢ cardinaux_bien_ordonnes(a).
       LA RÉDUCTION — conclusion == la cible LITTÉRALEMENT.  [correspondance]
     • relation_ordre_dans_intervalle — est_relation_ordre_dans(≤_induit,[0,a]) CLOS :
       transitivité + ANTISYMÉTRIE (Cantor–Bernstein) + réflexivité-implicite +
       réflexivité-dans-[0,a], les 4 paliers fermés == leurs prédicats.  [ordre]

  ⊢ DÉRIVÉ ICI :  cardinaux_bien_ordonnes_de_clause :
        { clause_plus_petit(≤_induit,[0,a]) } ⊢ cardinaux_bien_ordonnes(a).
     La partie ORDRE de est_bien_ordonne est fournie PAR PREUVE (relation_ordre_dans_
     intervalle) ; le SEUL report restant est la CLAUSE DE PLUS PETIT ÉLÉMENT.

  ⚠️ REPORTÉ (le BOTTLENECK irréductible, isolé comme HYPOTHÈSE — clause_plus_petit) :
     • clause_plus_petit(≤_induit,[0,a]) = « toute partie non vide de [0,a] a un plus
       petit élément pour ≤ ».  C'est le BON ORDRE proprement dit.  Voie ordinal↔cardinal
       (Zermelo) : bon ordre R du SET a → chaque cardinal ≤a = Card d'un segment initial
       de (a,R) → ces segments, bien ordonnés par inclusion (sous-segments d'un bon
       ordre), induisent le bon ordre des cardinaux ≤a.  La correspondance
       segment_initial ↦ Card(segment) (et sa monotonie) n'est pas encore construite
       (théorie ordinale représentationnelle) → reportée comme formule-énoncé
       `report_clause_plus_petit`.  JAMAIS postulée comme théorème.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la cible est DÉRIVÉE de l'unique
hypothèse clause_plus_petit (vérifié : c'est la SEULE hypothèse résiduelle).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_bon_ordre import (
    clause_plus_petit, plus_petit_de_bon_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import (
    ordre_induit_intervalle, intervalle_0a, bon_ordre_intervalle,
    cardinaux_bien_ordonnes_de_bon_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def report_clause_plus_petit(a="a"):
    """ÉNONCÉ du SEUL report restant : la CLAUSE DE PLUS PETIT ÉLÉMENT de [0,a] pour
    l'ordre (induit) des cardinaux :

        clause_plus_petit(≤_induit,[0,a]) =
            (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ R_induit{m,x}) ) ).

    ⚠️ NON PROUVÉ (bottleneck ordinal↔cardinal).  AVEC SES BINDERS PAR DÉFAUT, c'est
    LITTÉRALEMENT l'unique hypothèse de cardinaux_bien_ordonnes_de_clause (vérifié,
    test miroir).  La partie ORDRE de est_bien_ordonne étant ACQUISE
    (relation_ordre_dans_intervalle), c'est désormais le SEUL maillon manquant."""
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    return clause_plus_petit(Rind, interv, X="S", a="m", w="x")


# @livre Ch.III §3.2 Demo.1 | E III.24 L.16-30 | PDF p.127
def cardinaux_bien_ordonnes_de_clause(a="a", S="S", m="m", x="x"):
    """⊢ { clause_plus_petit(≤_induit,[0,a]) } ⊢ cardinaux_bien_ordonnes(a).

    🎯 RÉDUCTION FINALE — la cible cardinaux_bien_ordonnes(a) est DÉRIVÉE de l'UNIQUE
    report `clause_plus_petit(≤_induit,[0,a])` (la clause de plus petit élément), la
    partie ORDRE de est_bien_ordonne étant fournie PAR PREUVE
    (relation_ordre_dans_intervalle, INCONDITIONNEL).

    Mécanique :  est_bien_ordonne(≤_induit,[0,a]) = est_relation_ordre_dans(≤_induit,[0,a])
    [PROUVÉ] et clause_plus_petit(≤_induit,[0,a]) [hyp report].  On conjugue les deux,
    obtenant est_bien_ordonne(≤_induit,[0,a]) sous la SEULE hypothèse clause_plus_petit ;
    on l'injecte dans cardinaux_bien_ordonnes_de_bon_ordre (qui décharge le bon ordre).
    Conclusion == cardinaux_bien_ordonnes(a) LITTÉRALEMENT ; SEULE hyp = clause_plus_petit.
    theorie=22, rien postulé."""
    # est_bien_ordonne(≤_induit,[0,a]) = ordre [PROUVÉ] et clause [report]
    rod = relation_ordre_dans_intervalle(a)               # est_relation_ordre_dans  CLOS
    clause = report_clause_plus_petit(a)                  # la clause (report)
    bo = conjonction_intro(rod, N.assume(clause))         # est_bien_ordonne(≤_induit,[0,a]) [clause]
    assert bo.conclusion == bon_ordre_intervalle(a), \
        "l'assemblage ordre+clause ne reconstruit pas est_bien_ordonne(≤_induit,[0,a])"
    # cardinaux_bien_ordonnes_de_bon_ordre : { est_bien_ordonne(≤_induit,[0,a]) } ⊢ cible
    cbo = cardinaux_bien_ordonnes_de_bon_ordre(a, S, m, x)
    # décharge l'hypothèse est_bien_ordonne par bo (qui ne dépend QUE de clause)
    return N.modus_ponens(bo, N.loi_deduction(bon_ordre_intervalle(a), cbo))  # cible [clause]


__all__ = [
    "report_clause_plus_petit",
    "cardinaux_bien_ordonnes_de_clause",
]
