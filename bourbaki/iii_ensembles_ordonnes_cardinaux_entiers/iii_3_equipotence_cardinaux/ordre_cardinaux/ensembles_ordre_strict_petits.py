"""§III.3.2 — ORDRE STRICT des petits cardinaux :  ⊢ 0 < 1  et  ⊢ 1 < 2.

Énoncé VERBATIM (E.III.3.2, « Relation d'ordre ≤ entre cardinaux ») :
    x < y  :⇔  (x ≤ y  et  x ≠ y).

C'est exactement la définition `inf_strict_card(x, y) := et(inf_egal_card(x, y),
non(egal(x, y)))` d'ensembles_cardinaux (relevée VERBATIM avant codage).  On en
certifie les deux instances concrètes des petits entiers, chacune obtenue par
ASSEMBLAGE de lemmes DÉJÀ CLOS (rien postulé) :

  (1) `zero_strict_un`  ⊢ 0 < 1   (= inf_strict_card(0, 1)) :
        • 0 ≤ 1   (`zero_inf_egal_un`)  — l'application VIDE injecte ∅ dans 1 ;
            on part de ∅ ≤ 1 (zero_inf_egal généralisé puis instancié au TERME 1),
            et on réécrit le membre GAUCHE ∅ → Card(∅) = 0 (cardinal_vide_egale_vide
            + Leibniz S6), exactement le patron de cardinal_zero_inf_egal ;
        • 0 ≠ 1   (`zero_distinct_un`)  — c'est zero_distinct_successeur_zero,
            ⊢ ¬(0 = 0+1), et 1 = successeur(0) = UN par définition (Ent.UN) ;
        • assemblage : et(0≤1, 0≠1) EST inf_strict_card(0, 1).

  (2) `un_strict_deux`  ⊢ 1 < 2   (= inf_strict_card(1, 2)) :
        • 1 ≤ 2   (`un_inf_egal_deux`)  — 2 = successeur(1) = Card(1 ⊔ {∅}).
            inf_egal_successeur(1) donne 1 ≤ (1 ⊔ {∅}) [SET] ; tout ensemble est
            équipotent à son cardinal (equipotent_son_cardinal), d'où (1⊔{∅}) ≤
            Card(1⊔{∅}) = 2 (equipotence_implique_inf_egal) ; la TRANSITIVITÉ de ≤
            (inf_egal_transitive) chaîne 1 ≤ (1⊔{∅}) ≤ 2, donc 1 ≤ 2 ;
        • 1 ≠ 2   (`un_distinct_deux`)  — c'est un_distinct_successeur_un,
            ⊢ ¬(1 = 1+1), et 2 = successeur(1) = DEUX par définition (Ent.DEUX) ;
        • assemblage : et(1≤2, 1≠2) EST inf_strict_card(1, 2).

Tout est CERTIFIÉ par le noyau (aucun axiome nouveau, aucun postulat) et TESTÉ
(test_ordre_strict_petits.py).  Les lemmes intermédiaires (0≤1, 0≠1, 1≤2, 1≠2)
sont exposés séparément pour réutilisation.

⚠ τ-CARDINAUX NESTÉS : 1 = successeur(0) = Card(0 ⊔ {∅}) et 2 = successeur(1) sont
des τ-cardinaux imbriqués.  Comme dans fini_un/fini_deux, on n'APPELLE JAMAIS les
lemmes paramétrés DIRECTEMENT sur ces termes : on les GÉNÉRALISE sur des NOMS de
variables puis on les INSTANCIE par une unique substitution déterministe au terme,
ce qui traverse sans collision des liants internes.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, instancie,
                               equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (inf_egal_card, inf_strict_card, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_bornes import zero_inf_egal, inf_egal_successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import (equipotence_implique_inf_egal,
                               inf_egal_transitive)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN, DEUX
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (cardinal_vide_egale_vide,
                               zero_distinct_successeur_zero)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import un_distinct_successeur_un
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe


# ── Objets : 0 = Card(∅), 1 = successeur(0), 2 = successeur(1) = Card(1 ⊔ {∅}) ──
_VIDE = E.VIDE                            # ∅
_SING = E.singleton(_VIDE)                # {∅}
_UNSOMME = somme_disjointe(UN, _SING)     # 1 ⊔ {∅}   ;   DEUX = Card(1 ⊔ {∅})


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  0 < 1
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.1 Ex.2 | E III.24 L.1-4 | PDF p.127
#   (« 2) Tous les ensembles à un élément sont équipotents … On note 1 le cardinal
#    Card({∅}) = τ_Z(Eq({∅}, Z)). » — la distinction stricte 0 < 1 est certifiée ici.)
# @livre Ch.III §3.1 Ex.4 | E III.24 L.7-8 | PDF p.127
#   (« 4) * Un espace hilbertien de type dénombrable est équipotent à l'ensemble
#    des nombres réels. * » — prose hors théorie des ensembles, rien à formaliser.)
def zero_inf_egal_un():
    """⊢ 0 ≤ 1.   (= inf_egal_card(0, 1) ; l'application vide injecte ∅ dans 1.)

    zero_inf_egal généralisé en (∀A)(∅ ≤ A) puis instancié au TERME 1 donne ∅ ≤ 1 ;
    on réécrit le membre GAUCHE ∅ → Card(∅) = 0 (cardinal_vide_egale_vide + Leibniz
    S6), d'où Card(∅) ≤ 1 = 0 ≤ 1.  (Même patron que cardinal_zero_inf_egal, mais
    instancié au TERME 1 plutôt qu'à Card(A).)"""
    zero_all = N.generalisation("A", zero_inf_egal("A"))          # (∀A)(∅ ≤ A)
    le = instancie(zero_all, UN)                                  # ∅ ≤ 1
    cve = cardinal_vide_egale_vide()                              # Card(∅) = ∅
    # ∅ = Card(∅)  (symétrie), puis Leibniz réécrit ∅ → Card(∅) dans « ∅ ≤ 1 »
    vide_eq_cardvide = N.modus_ponens(cve, symetrie(cardinal(_VIDE), _VIDE))   # ∅ = Card(∅)
    leib = N.s6(_VIDE, cardinal(_VIDE), "w", inf_egal_card(var("w"), UN))
    equiv = N.modus_ponens(vide_eq_cardvide, leib)               # (∅≤1) ⇔ (Card(∅)≤1)
    return N.modus_ponens(le, equivalence_avant(equiv))          # Card(∅) ≤ 1  =  0 ≤ 1


def zero_distinct_un():
    """⊢ ¬(0 = 1).   (= non(egal(0, 1)) ; 0 ≠ 1.)

    1 = successeur(0) = Ent.UN PAR DÉFINITION ; donc ¬(0 = 0+1) (= ¬(0 = successeur(0)),
    zero_distinct_successeur_zero) EST LITTÉRALEMENT ¬(0 = 1)."""
    return zero_distinct_successeur_zero()                        # ¬(0 = successeur(0)) = ¬(0 = 1)


def zero_strict_un():
    """⊢ 0 < 1.   (ORDRE STRICT des petits cardinaux, E.III.3.2 ; = inf_strict_card(0, 1).)

    x < y :⇔ (x ≤ y et x ≠ y).  Pour (0, 1) : 0 ≤ 1 (zero_inf_egal_un) ET 0 ≠ 1
    (zero_distinct_un).  Leur conjonction EST inf_strict_card(0, 1)."""
    le = zero_inf_egal_un()                                       # 0 ≤ 1
    ne = zero_distinct_un()                                       # 0 ≠ 1
    return conjonction_intro(le, ne)                             # 0 < 1


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  1 < 2
# ═══════════════════════════════════════════════════════════════════════════════
def somme_inf_egal_deux():
    """⊢ (1 ⊔ {∅}) ≤ 2.   (le SET « 1 ⊔ {∅} » s'injecte dans son cardinal 2.)

    Tout ensemble est équipotent à son cardinal : Eq(1⊔{∅}, Card(1⊔{∅}))
    (equipotent_son_cardinal généralisé puis instancié au TERME 1⊔{∅}).  Comme
    2 = successeur(1) = Card(1⊔{∅}), c'est Eq(1⊔{∅}, 2) ; toute équipotence donne une
    injection (equipotence_implique_inf_egal généralisé puis instancié aux TERMES),
    d'où (1⊔{∅}) ≤ 2."""
    eq_all = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    eqXY = instancie(eq_all, _UNSOMME)                             # Eq(1⊔{∅}, Card(1⊔{∅})) = Eq(1⊔{∅}, 2)
    imp_all = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))             # (∀X)(∀Y)(Eq(X,Y) ⇒ X≤Y)
    imp = instancie(instancie(imp_all, _UNSOMME), DEUX)            # Eq(1⊔{∅}, 2) ⇒ (1⊔{∅} ≤ 2)
    return N.modus_ponens(eqXY, imp)                              # (1⊔{∅}) ≤ 2


# @livre Ch.III §3.1 Ex.3 | E III.24 L.5-6 | PDF p.127
#   (« 3) On note 2 le cardinal Card({∅, {∅}}) ; c'est le cardinal de tout ensemble
#    à deux éléments dont les éléments sont différents. » — 1 < 2 certifié ici.)
def un_inf_egal_deux():
    """⊢ 1 ≤ 2.   (= inf_egal_card(1, 2) ; 2 = successeur(1) = Card(1 ⊔ {∅}).)

    inf_egal_successeur(1) donne 1 ≤ (1⊔{∅}) [le membre droit est le SET somme
    disjointe].  somme_inf_egal_deux donne (1⊔{∅}) ≤ 2.  La TRANSITIVITÉ de ≤
    (inf_egal_transitive généralisée sur (X,Y,Z) puis instanciée aux TERMES
    (1, 1⊔{∅}, 2)) chaîne 1 ≤ (1⊔{∅}) ≤ 2, d'où 1 ≤ 2.

    ⚠ inf_egal_successeur est appliqué par GÉNÉRALISATION-puis-INSTANCIATION au terme 1
    (et non DIRECTEMENT sur le τ-cardinal nesté 1 = Card(0⊔{∅}), qui ferait collisionner
    les liants internes du τ-cardinal dans la machinerie graphe_terme du témoin u↦(u,0))."""
    succ_all = N.generalisation("A", inf_egal_successeur("A"))    # (∀A)(A ≤ A⊔{∅})
    le1 = instancie(succ_all, UN)                                 # 1 ≤ (1 ⊔ {∅})
    le2 = somme_inf_egal_deux()                                   # (1 ⊔ {∅}) ≤ 2
    trans_all = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))           # (∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z)
    trans = instancie(instancie(instancie(trans_all, UN), _UNSOMME), DEUX)   # (1≤(1⊔{∅}) et (1⊔{∅})≤2) ⇒ 1≤2
    return N.modus_ponens(conjonction_intro(le1, le2), trans)    # 1 ≤ 2


def un_distinct_deux():
    """⊢ ¬(1 = 2).   (= non(egal(1, 2)) ; 1 ≠ 2.)

    2 = successeur(1) = Ent.DEUX PAR DÉFINITION ; donc ¬(1 = 1+1) (= ¬(1 = successeur(1)),
    un_distinct_successeur_un) EST LITTÉRALEMENT ¬(1 = 2)."""
    return un_distinct_successeur_un()                            # ¬(1 = successeur(1)) = ¬(1 = 2)


def un_strict_deux():
    """⊢ 1 < 2.   (ORDRE STRICT des petits cardinaux, E.III.3.2 ; = inf_strict_card(1, 2).)

    x < y :⇔ (x ≤ y et x ≠ y).  Pour (1, 2) : 1 ≤ 2 (un_inf_egal_deux) ET 1 ≠ 2
    (un_distinct_deux).  Leur conjonction EST inf_strict_card(1, 2)."""
    le = un_inf_egal_deux()                                       # 1 ≤ 2
    ne = un_distinct_deux()                                       # 1 ≠ 2
    return conjonction_intro(le, ne)                             # 1 < 2


__all__ = ["zero_inf_egal_un", "zero_distinct_un", "zero_strict_un",
           "somme_inf_egal_deux", "un_inf_egal_deux", "un_distinct_deux",
           "un_strict_deux"]
