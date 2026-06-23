"""§III.4.2 — ENSEMBLES FINIS, propositions SUPPLÉMENTAIRES (salvage gradué, module NEUF).

Ce module COMPLÈTE ensembles_finis_props (ordre des cardinaux finis) et
ensembles_calcul_entiers_props (arithmétique binaire) en salvant — au MAXIMUM
INCONDITIONNELLEMENT — les énoncés de E.III.4.2 (Proposition 2 et Corollaires 1-3)
portant sur les ENSEMBLES (et non plus seulement les cardinaux) :

  • un ensemble ÉQUIPOTENT à un ensemble fini est fini (transport de la finitude) ;
  • un SOUS-ENSEMBLE d'un ensemble fini a un cardinal ≤ (Card X ≤ Card E) ;
  • une PARTIE STRICTE d'un ensemble fini a un cardinal STRICTEMENT plus petit
    (Cor. 2 ; la moitié « ≤ » INCONDITIONNELLE, la moitié « ≠ » reportée à la surgery) ;
  • la RÉUNION de deux ensembles finis DISJOINTS est finie (Cor. ⊂ Prop. 1 §III.5.1
    cas binaire ; conditionnée à la bijection de recollement + finitude de la somme) ;
  • l'IMAGE d'un ensemble fini est finie / sous-finie (Cor. 3 ; la moitié « image ⊂ but »
    INCONDITIONNELLE, la finitude reportée à la surjection ⇒ ≤).

Il s'appuie SANS rien postuler sur les grands théorèmes DÉJÀ prouvés :
  • Proposition 1 §III.3 (sens direct, version terme) : Eq(U,V) ⇒ Card U = Card V
    [_prop1_direct_t] — le NOYAU de tous les transports de finitude ;
  • symétrie de l'équipotence [equipotence_symetrique] ;
  • brique monotone « X ⊂ E ⇒ X ≤ E » [partie_inf_egal_card] + pont ≤ensembles→≤cardinaux
    [le_ens_implique_le_card] ;
  • Prop. 10 §II.4 (réunion disjointe ≃ somme, sous bijection de recollement)
    [reunion_equipotente_somme_si_bijection].

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉS DE BOURBAKI VISÉS (E.III.4.2) :

   Prop. 2 : « Soit n un entier.  Tout cardinal 𝔞 ≤ n est un entier. […] »
   Cor. 1  : Toute partie d'un ensemble fini est finie.        [ensembles_finis_props]
   Cor. 2  : X ⊂ E, X ≠ E, E fini  ⇒  Card X < Card E.
   Cor. 3  : f : E → F, E fini  ⇒  f(E) partie FINIE de F.

────────────────────────────────────────────────────────────────────────────────
SALVAGE GRADUÉ — état des paliers (cf. __all__) :

  ✅ INCONDITIONNEL (rien postulé, theorie_ensembles()=22) :
     • equipotent_implique_fini_cardinal(a,b)   — Eq(a,b) ⇒ (Fini a ⇒ Fini b)  [transport
       de la finitude au niveau CARDINAL, via Card a = Card b + S6] ;
     • equipotent_implique_fini_ensemble(U,V)   — Eq(U,V) ⇒ (U fini ⇒ V fini)  [niveau
       ENSEMBLES : « U fini » = Fini(Card U)] ;
     • equipotent_ssi_fini_ensemble(U,V)        — Eq(U,V) ⇒ (U fini ⇔ V fini)  [un ensemble
       équipotent à un fini est fini, ET RÉCIPROQUEMENT] ;
     • sous_ensemble_card_inf_egal(X,E)         — (X ⊂ E) ⇒ Card X ≤ Card E  [un
       sous-ensemble a un cardinal ≤ ; socle de Cor. 1 et Cor. 2] ;
     • image_card_inf_egal_but(f,E,F)           — ( image(f,E) ⊂ F ) ⇒ Card(image(f,E)) ≤ Card F
       [moitié INCONDITIONNELLE de Cor. 3 : l'image directe, partie du but, a un cardinal ≤].

  ⚠️ CONDITIONNEL (report ISOLÉ déchargé en antécédent explicite, JAMAIS postulé) :
     • cor2_partie_stricte_card_strict_cond(X,E) — (Card X ≠ Card E reporté) ⇒
       ( (X⊂E et X≠E et E fini) ⇒ Card X < Card E )  [Cor. 2 ; la moitié « ≤ »
       inconditionnelle, le « ≠ » = surgery « retrait d'un point » / cardinal_pas_entre] ;
     • reunion_disjointe_finie_cond(A,B)         — ( bijection de recollement + somme-de-finis )
       ⇒ ( (A fini et B fini) ⇒ A∪B fini )  [Cor. ⊂ Prop. 1 §III.5.1 cas binaire] ;
     • cor3_image_finie_cond(f,E,F)              — ( image ⊂ F + surjection⇒≤ + Cor. 1 )
       ⇒ ( E fini ⇒ f(E) partie finie de F )  [Cor. 3].

  ⚠️ ÉNONCÉS REPORTÉS (formules-cibles, jamais prouvées ni postulées) :
     • cor3_image_finie_cible(f,E,F)             — ( E fini ) ⇒ ( image(f,E) ⊂ F et Fini(image)).

⚠️ INVARIANT : aucun N.axiome n'est ajouté à theorie_ensembles() (= 22).  Les seuls
   « givens » sont des HYPOTHÈSES explicites (Eq, X⊂E, bijection de recollement,
   reports déchargés par loi_deduction).  Anti-tautologie/anti-affaibli STRICT : chaque
   énoncé inconditionnel a un CONTENU non trivial — le transport de la finitude par
   équipotence n'est PAS P⇒P (il passe par Card U = Card V puis Leibniz S6), et les
   formes conditionnelles ont un antécédent (report) STRICTEMENT distinct du conséquent.

⚠️ NOTE TECHNIQUE (capture du liant interne de est_cardinal).  est_cardinal(a) =
   (∃X)(a = Card X) lie X ; lorsqu'on substitue un terme contenant X libre (p.ex.
   Card X), la substitution α-renomme ce liant, et la forme obtenue n'est PAS
   structurellement la forme littérale attendue.  On construit donc les lemmes de
   transport sur des noms FRAIS (collision-free), puis on GÉNÉRALISE et INSTANCIE aux
   termes de l'utilisateur — l'instanciation traite hypothèse et conclusion de manière
   cohérente.  C'est le patron déjà éprouvé de _prop1_direct_t.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, impl, equiv, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, equipotent, inf_egal_card, inf_strict_card,
    est_bijection_de,
)
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import _prop1_direct_t
from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.ensembles_clause_plus_petit_monotonie import inf_egal_card_de_inclus_terme

from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_fini_ensemble
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import partie_inf_egal_card
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import le_ens_implique_le_card

from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_recollement_props import (
    reunion_equipotente_somme_si_bijection, bijection_canonique_reunion_somme,
)

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


def _eq_sym_t(tx, ty):
    """⊢ Eq(X, Y) ⇒ Eq(Y, X)  pour des TERMES X, Y  (symétrie de l'équipotence, version terme).

    equipotence_symetrique(F,X,Y) généralisée sur X,Y puis instanciée aux termes."""
    gen = N.generalisation("X", N.generalisation("Y", equipotence_symetrique("F", "X", "Y")))
    return instancie(instancie(gen, _t(tx)), _t(ty))


# ════════════════════════════════════════════════════════════════════════════
#  (1) TRANSPORT DE LA FINITUDE PAR ÉQUIPOTENCE — niveau CARDINAL (INCONDITIONNEL)
#
#  Eq(a,b) ⇒ Card a = Card b (Prop. 1 sens direct) ; S6 Leibniz sur le prédicat
#  Fini(·) avec le trou w : (Card a = Card b) ⇒ (Fini(Card a) ⇔ Fini(Card b)).
#  Le cœur de TOUS les transports de finitude ci-dessous.
#
#  ⚠ On bâtit sur des noms FRAIS u, v (collision-free avec le liant interne X de
#  est_cardinal) puis on GÉNÉRALISE/INSTANCIE — cf. note du module.
# ════════════════════════════════════════════════════════════════════════════
def _equipotent_implique_fini_core(tu, tv):
    """⊢ Eq(U, V) ⇒ ( Fini(Card U) ⇒ Fini(Card V) )  pour des TERMES U, V (cœur de transport).

    Eq(U,V) ⇒ Card U = Card V (Prop. 1, _prop1_direct_t) ; S6 sur Fini(·) donne
    Fini(Card U) ⇔ Fini(Card V) ; le sens AVANT envoie Fini(Card U) sur Fini(Card V).
    INCONDITIONNEL.  Les deux côtés de l'équivalence S6 sont produits par la MÊME
    substitution (cohérence structurelle garantie)."""
    vu, vv = _t(tu), _t(tv)
    cu, cv = cardinal(vu), cardinal(vv)
    p1 = _prop1_direct_t(vu, vv)                            # Eq(U,V) ⇒ Card U = Card V
    h_eq = N.assume(equipotent(vu, vv))                    # Eq(U,V)
    card_eq = N.modus_ponens(h_eq, p1)                     # Card U = Card V
    # S6 : (Card U = Card V) ⇒ ( Fini(Card U) ⇔ Fini(Card V) )
    s6 = N.s6(cu, cv, "w", est_fini(var("w")))
    equ = N.modus_ponens(card_eq, s6)                      # Fini(Card U) ⇔ Fini(Card V)
    h_fin = N.assume(est_fini(cu))                         # Fini(Card U)
    fin_v = N.modus_ponens(h_fin, equivalence_avant(equ))  # Fini(Card V)
    inner = N.loi_deduction(est_fini(cu), fin_v)          # Fini(Card U) ⇒ Fini(Card V)
    return N.loi_deduction(equipotent(vu, vv), inner)     # Eq(U,V) ⇒ (Fini(Card U) ⇒ Fini(Card V))


def equipotent_implique_fini_cardinal(a="a", b="b"):
    """⊢ Eq(a, b) ⇒ ( est_fini(a) ⇒ est_fini(b) )   sous a, b CARDINAUX implicites.

    🎯 TRANSPORT DE LA FINITUDE (E.III.4) au niveau des CARDINAUX, version où l'on
    identifie est_fini(a) = Fini(Card a) lorsque a est un cardinal (Card a = a).  En
    pratique on l'expose sur les ENSEMBLES (equipotent_implique_fini_ensemble) où
    « a fini » est littéralement Fini(Card a).  Ici on fournit la forme générale
    Eq(a,b) ⇒ (Fini(Card a) ⇒ Fini(Card b)) — ré-exposée pour a, b paramètres.

    NB : la conclusion porte sur Fini(Card a) / Fini(Card b) (= est_fini_ensemble).
    INCONDITIONNEL — repose sur Prop. 1 §III.3 + Leibniz S6, jamais P⇒P."""
    return _equipotent_implique_fini_core(a, b)            # Eq(a,b) ⇒ (Fini(Card a) ⇒ Fini(Card b))


def equipotent_implique_fini_ensemble(U="U", V="V"):
    """⊢ Eq(U, V) ⇒ ( U fini ⇒ V fini ).   (un ensemble équipotent à un FINI est FINI ; INCONDITIONNEL.)

    🎯 « Tout ensemble équipotent à un ensemble fini est fini » (E.III.4).  « U fini » =
    est_fini_ensemble(U) = Fini(Card U).  De Eq(U,V) (Prop. 1 sens direct) on tire
    Card U = Card V ; la finitude, propriété du cardinal, se transporte par Leibniz S6 :
    Fini(Card U) ⇒ Fini(Card V).  INCONDITIONNEL — contenu réel (PAS P⇒P : passe par
    l'égalité des cardinaux).  Pierre angulaire de l'invariance de la finitude par
    équipotence."""
    return _equipotent_implique_fini_core(U, V)            # Eq(U,V) ⇒ (U fini ⇒ V fini)


def equipotent_ssi_fini_ensemble(U="U", V="V"):
    """⊢ Eq(U, V) ⇒ ( U fini ⇔ V fini ).   (la finitude est INVARIANTE par équipotence ; INCONDITIONNEL.)

    Renforcement de equipotent_implique_fini_ensemble en ÉQUIVALENCE : deux ensembles
    équipotents sont finis ENSEMBLE.  Sens AVANT = equipotent_implique_fini_ensemble(U,V) ;
    sens ARRIÈRE = idem sur Eq(V,U) (obtenue par symétrie de l'équipotence, _eq_sym_t).
    Sous Eq(U,V), déchargée — l'équivalence vaut pour tout couple équipotent."""
    vu, vv = _t(U), _t(V)
    h_eq = N.assume(equipotent(vu, vv))                    # Eq(U,V)
    # sens AVANT : U fini ⇒ V fini
    avant = N.modus_ponens(h_eq, equipotent_implique_fini_ensemble(U, V))   # U fini ⇒ V fini
    # sens ARRIÈRE : V fini ⇒ U fini  (via Eq(V,U) = symétrie de Eq(U,V))
    eq_vu = N.modus_ponens(h_eq, _eq_sym_t(vu, vv))        # Eq(V, U)
    arriere = N.modus_ponens(eq_vu, _equipotent_implique_fini_core(vv, vu))  # V fini ⇒ U fini
    equ = conjonction_intro(avant, arriere)               # (U fini ⇒ V fini) et (V fini ⇒ U fini) = ⇔
    return N.loi_deduction(equipotent(vu, vv), equ)       # Eq(U,V) ⇒ (U fini ⇔ V fini)


# ════════════════════════════════════════════════════════════════════════════
#  (2) SOUS-ENSEMBLE : Card X ≤ Card E   (INCONDITIONNEL ; socle Cor. 1 / Cor. 2)
#
#  X ⊂ E ⇒ X ≤ E (partie_inf_egal_card, diagonale Δ_X) ; le pont ≤ensembles→≤cardinaux
#  (le_ens_implique_le_card) donne Card X ≤ Card E.
# ════════════════════════════════════════════════════════════════════════════
def sous_ensemble_card_inf_egal(X="X", Eens="E"):
    """⊢ ( X ⊂ E ) ⇒ ( Card X ≤ Card E ).   (un SOUS-ENSEMBLE a un cardinal ≤ ; INCONDITIONNEL.)

    🎯 SOCLE des Corollaires 1 et 2 (E.III.4.2) au niveau des CARDINAUX : un
    sous-ensemble d'un ensemble fini (ou de n'importe quel ensemble) a un cardinal au
    plus égal.  X ⊂ E ⇒ X ≤ E (la diagonale Δ_X injecte X dans E, partie_inf_egal_card),
    puis Card X ≤ Card E (pont ≤ENSEMBLES → ≤CARDINAUX, le_ens_implique_le_card).
    INCONDITIONNEL, contenu réel — distinct de toute tautologie.

    ⚠️ Le second argument ne doit PAS être la variable littérale « F » (nom de liant
    interne — variable de graphe — du pont le_ens_implique_le_card) : utiliser un autre
    nom (cf. image_card_inf_egal_but qui note le codomaine « Co »).  Tout TERME composé
    (p.ex. image(f,E), un Card·) passe sans collision."""
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)
    h_incl = N.assume(inclus(vX, vE))                      # X ⊂ E
    le_XE = N.modus_ponens(h_incl, partie_inf_egal_card(X, Eens))   # X ≤ E   (ENSEMBLES)
    le_card = N.modus_ponens(le_XE, le_ens_implique_le_card(vX, vE))   # Card X ≤ Card E
    return N.loi_deduction(inclus(vX, vE), le_card)        # (X⊂E) ⇒ Card X ≤ Card E


# ════════════════════════════════════════════════════════════════════════════
#  (3) COROLLAIRE 2 — PARTIE STRICTE : Card X < Card E   (CONDITIONNEL, ≠ reporté)
#
#  Card X < Card E = (Card X ≤ Card E et Card X ≠ Card E).  La moitié « ≤ » est
#  INCONDITIONNELLE (sous_ensemble_card_inf_egal).  La moitié « ≠ » — qu'une partie
#  STRICTE d'un FINI ait un cardinal STRICTEMENT plus petit — est précisément le
#  Corollaire 2, voisin de la Prop. 8 / cardinal_pas_entre (surgery « retrait d'un
#  point »).  On la DÉCHARGE en hypothèse explicite ISOLÉE, jamais postulée.
# ════════════════════════════════════════════════════════════════════════════
def cor2_partie_stricte_card_strict_cond(X="X", Eens="E"):
    """⊢ ( (X⊂E et X≠E et E fini) ⇒ Card X ≠ Card E )
            ⇒ ( ( X⊂E et X≠E et E fini ) ⇒ Card X < Card E ).

    🎯 COROLLAIRE 2 §III.4.2, forme CONDITIONNELLE au contenu non trivial (PAS P⇒P) :
    « si X ⊂ E, X ≠ E et E fini, alors Card X < Card E ».  Card X < Card E =
    (Card X ≤ Card E et Card X ≠ Card E) :
      • « ≤ » : sous_ensemble_card_inf_egal — INCONDITIONNEL ;
      • « ≠ » : la STRICTE chute du cardinal d'une partie stricte d'un FINI — surgery
        « retrait d'un point » (E.III.4, voisine Prop. 8 / cardinal_pas_entre) — RÉSERVÉE
        comme report H, déchargé en antécédent EXPLICITE.
    H = ( (X⊂E et X≠E et E fini) ⇒ Card X ≠ Card E ) est le SEUL maillon reporté.  Dès
    qu'il est prouvé (la surgery), le Corollaire 2 est inconditionnel.  Jamais postulé.

    Anti-tautologie : H (antécédent) DIFFÈRE de la conclusion (conséquent porte sur
    Card X < Card E, pas sur Card X ≠ Card E) — le contenu réel est la conjonction avec
    le « ≤ » inconditionnel."""
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)
    ante = et(et(inclus(vX, vE), non(egal(vX, vE))), est_fini(cE))   # X⊂E et X≠E et E fini
    # report H : la STRICTE chute (Card X ≠ Card E)
    H = impl(ante, non(egal(cX, cE)))                     # (…) ⇒ Card X ≠ Card E
    h_H = N.assume(H)
    h = N.assume(ante)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(h))   # X ⊂ E
    # ≤ : INCONDITIONNEL
    le_card = N.modus_ponens(h_incl, sous_ensemble_card_inf_egal(X, Eens))   # Card X ≤ Card E
    # ≠ : report H appliqué à l'antécédent complet
    ne_card = N.modus_ponens(h, h_H)                      # Card X ≠ Card E
    lt = conjonction_intro(le_card, ne_card)              # Card X < Card E = (≤ et ≠)
    assert lt.conclusion == inf_strict_card(cX, cE), \
        "Card X < Card E mal reconstruit (≤ ∧ ≠)"
    inner = N.loi_deduction(ante, lt)                     # (X⊂E et X≠E et E fini) ⇒ Card X < Card E  [H]
    return N.loi_deduction(H, inner)                      # H ⇒ ( … ⇒ Card X < Card E )


# ════════════════════════════════════════════════════════════════════════════
#  (4) RÉUNION DE DEUX FINIS DISJOINTS EST FINIE   (CONDITIONNEL — Cor. ⊂ Prop. 1 §III.5.1)
#
#  A ∪ B ≃ A ⊔ B  (réunion disjointe ≃ somme, Prop. 10 §II.4, SOUS la bijection de
#  recollement W).  Donc A∪B est fini ⇔ A⊔B est fini (transport par équipotence).  Et
#  A⊔B fini suit de A, B finis PAR la finitude de la somme (Prop. 1 §III.5.1 cas
#  binaire, REPORTÉE à la récurrence C61).  Deux maillons reportés, déchargés.
# ════════════════════════════════════════════════════════════════════════════
def reunion_disjointe_finie_cond(A="A", B="B"):
    """⊢ ( est_bijection_de(W, A∪B, A⊔B)
            et ( (A fini et B fini) ⇒ A⊔B fini ) )
       ⇒ ( ( A fini et B fini ) ⇒ A∪B fini ).

    🎯 « La RÉUNION de deux ensembles FINIS DISJOINTS est finie » (E.III.4 / Prop. 1
    §III.5.1 cas binaire), forme CONDITIONNELLE au contenu non trivial.  W :=
    bijection_canonique_reunion_somme(A,B) est le RECOLLEMENT des injections canoniques
    a↦(a,0), b↦(b,1) ; sous l'hypothèse qu'il bijecte A∪B sur A⊔B (acquise dès A∩B=∅,
    Prop. 10 §II.4, reportée), on a Eq(A∪B, A⊔B), d'où — par transport de la finitude
    (equipotent_implique_fini_ensemble) — A∪B fini ⇐ A⊔B fini.  Et A⊔B fini ⇐ A,B finis
    par la finitude de la somme (report H_sum = Prop. 1 §III.5.1, récurrence C61).

    DEUX maillons reportés, ISOLÉS, déchargés en antécédent (jamais postulés) :
      • bij = est_bijection_de(W, A∪B, A⊔B) — la bijection de recollement (A∩B=∅) ;
      • H_sum = (A fini et B fini) ⇒ A⊔B fini — la finitude de la somme disjointe.
    Dès que ces deux maillons sont prouvés, la réunion de deux finis disjoints est
    INCONDITIONNELLEMENT finie.  Anti-tautologie : l'antécédent (bijection + somme finie)
    DIFFÈRE du conséquent (réunion finie)."""
    va, vb = _t(A), _t(B)
    union = E.reunion(va, vb)                              # A ∪ B
    somme = somme_disjointe(va, vb)                        # A ⊔ B
    W = bijection_canonique_reunion_somme(va, vb)          # recollement des injections canoniques
    bij = est_bijection_de(W, union, somme)               # W bijecte A∪B sur A⊔B
    # report finitude de la somme (cas binaire, niveau ENSEMBLES)
    fini_AB = et(est_fini_ensemble(va), est_fini_ensemble(vb))   # A fini et B fini
    H_sum = impl(fini_AB, est_fini_ensemble(somme))       # (A fini et B fini) ⇒ A⊔B fini
    ante = et(bij, H_sum)
    h = N.assume(ante)
    h_bij = conjonction_elim_gauche(h)                    # bijection W
    h_sum = conjonction_elim_droite(h)                    # finitude de la somme
    # corps : (A fini et B fini) ⇒ A∪B fini
    h_fin = N.assume(fini_AB)                             # A fini et B fini
    fini_somme = N.modus_ponens(h_fin, h_sum)            # A⊔B fini   (= Fini(Card somme))
    # Eq(A∪B, A⊔B) sous la bijection ; puis Eq(A⊔B, A∪B) (symétrie)
    eq_us_imp = N.loi_deduction(bij, reunion_equipotente_somme_si_bijection(va, vb))   # bij ⇒ Eq(A∪B,A⊔B)
    eq_us = N.modus_ponens(h_bij, eq_us_imp)             # Eq(A∪B, A⊔B)
    eq_su = N.modus_ponens(eq_us, _eq_sym_t(union, somme))   # Eq(A⊔B, A∪B)
    # A⊔B fini ⇒ A∪B fini   (transport de la finitude)
    transp = N.modus_ponens(eq_su, _equipotent_implique_fini_core(somme, union))   # A⊔B fini ⇒ A∪B fini
    fini_union = N.modus_ponens(fini_somme, transp)     # A∪B fini
    assert fini_union.conclusion == est_fini_ensemble(union), \
        "la conclusion n'est pas « A∪B fini »"
    inner = N.loi_deduction(fini_AB, fini_union)        # (A fini et B fini) ⇒ A∪B fini  [ante]
    return N.loi_deduction(ante, inner)                 # (bij et H_sum) ⇒ ( … ⇒ A∪B fini )


# ════════════════════════════════════════════════════════════════════════════
#  (5) COROLLAIRE 3 — IMAGE D'UN FINI EST SOUS-FINIE   (moitié ≤ INCONDITIONNELLE)
#
#  Cor. 3 : f : E → F, E fini ⇒ f(E) partie FINIE de F.  Deux contenus :
#    (a) f(E) = image(f,E) est une PARTIE de F  ⇒  Card(image) ≤ Card F  [INCONDITIONNEL
#        dès qu'on a image(f,E) ⊂ F, qui est un conjoint de « f application de E dans F »] ;
#    (b) f(E) est FINIE — exige E ↠ f(E) (surjection canonique) ⇒ Card f(E) ≤ Card E,
#        puis Cor. 1 (sous-ensemble d'un fini est fini).  La surjection ⇒ ≤ (choix d'une
#        section) est REPORTÉE.
# ════════════════════════════════════════════════════════════════════════════
def image_card_inf_egal_but(f="f", Eens="E", Co="Co"):
    """⊢ ( image(f, E) ⊂ Co ) ⇒ ( Card(image(f, E)) ≤ Card Co ).
       (l'IMAGE, partie du but, a un cardinal ≤ ; moitié INCONDITIONNELLE de Cor. 3.)

    🎯 Moitié INCONDITIONNELLE du Corollaire 3 (E.III.4.2) : l'image directe f(E) =
    image(f,E) d'une application f : E → Co (codomaine Co, le « F » de Bourbaki) est une
    PARTIE de Co (conjoint « image⊂Co » de est_application_de), donc son cardinal est ≤
    Card Co (sous_ensemble_card_inf_egal au terme image(f,E)).  C'est « f(E) est une
    partie du but » + sa borne cardinale ; la FINITUDE de f(E) (l'autre moitié de Cor. 3)
    exige la surjection canonique E ↠ f(E) ⇒ ≤ (report) + Cor. 1 — cf.
    cor3_image_finie_cond.  INCONDITIONNEL.

    NB : on note le codomaine « Co » (et non « F ») pour ÉVITER la collision avec le nom
    de liant interne F (variable de graphe) des lemmes d'ordre des cardinaux — le « F »
    de Bourbaki ; le nom du codomaine est cosmétique."""
    vf, vE, vCo = _t(f), _t(Eens), _t(Co)
    img = E.image(vf, vE)                                 # f(E) = image(f, E)
    return sous_ensemble_card_inf_egal(img, vCo)          # (image⊂Co) ⇒ Card(image) ≤ Card Co


def cor3_image_finie_cond(f="f", Eens="E", F="F"):
    """⊢ ( ( E fini ⇒ image(f,E) ≤ E )   [surjection canonique E ↠ f(E) ⇒ ≤, report]
            et ( (image(f,E) ≤ E et E fini) ⇒ image(f,E) fini )   [Cor. 1, report] )
       ⇒ ( E fini ⇒ image(f,E) fini ).

    🎯 COROLLAIRE 3 §III.4.2, forme CONDITIONNELLE : « f : E → F, E fini ⇒ f(E) finie ».
    On enchaîne deux maillons reportés ISOLÉS, déchargés en antécédent :
      • H_surj = ( E fini ⇒ image(f,E) ≤ E ) — la surjection canonique E ↠ f(E)
        (e ↦ f(e)) donne Card f(E) ≤ Card E (besoin d'une SECTION / du choix) — REPORTÉ ;
      • H_cor1 = ( (image(f,E) ≤ E et E fini) ⇒ image(f,E) fini ) — l'instance de Cor. 1
        (un objet de cardinal ≤ celui d'un fini est fini ; fini_downward, REPORTÉ C61).
    De E fini : image(f,E) ≤ E (H_surj), puis image(f,E) fini (H_cor1).  Aucun maillon
    postulé.  Anti-tautologie : antécédent (les deux reports) ≠ conséquent (image finie).

    NB : « image(f,E) ≤ E » et « ≤ » sont ici au niveau des cardinaux (inf_egal_card)."""
    vf, vE, vF = _t(f), _t(Eens), _t(F)
    img = E.image(vf, vE)                                 # f(E)
    fini_E = est_fini_ensemble(vE)                        # E fini
    le_img_E = inf_egal_card(img, vE)                     # image(f,E) ≤ E   (cardinal)
    fini_img = est_fini_ensemble(img)                     # f(E) fini
    # reports
    H_surj = impl(fini_E, le_img_E)                       # E fini ⇒ image ≤ E
    H_cor1 = impl(et(le_img_E, fini_E), fini_img)         # (image≤E et E fini) ⇒ image fini
    ante = et(H_surj, H_cor1)
    h = N.assume(ante)
    h_surj = conjonction_elim_gauche(h)
    h_cor1 = conjonction_elim_droite(h)
    h_finiE = N.assume(fini_E)                            # E fini
    le_thm = N.modus_ponens(h_finiE, h_surj)             # image ≤ E
    fini_img_thm = N.modus_ponens(conjonction_intro(le_thm, h_finiE), h_cor1)   # image fini
    inner = N.loi_deduction(fini_E, fini_img_thm)        # E fini ⇒ image fini  [ante]
    return N.loi_deduction(ante, inner)                  # (H_surj et H_cor1) ⇒ (E fini ⇒ image fini)


def cor3_image_finie_cible(f="f", Eens="E", F="F"):
    """ÉNONCÉ (formule-cible, NON théorème) du Corollaire 3 §III.4.2 :
        ( E fini ) ⇒ ( image(f, E) ⊂ F  et  image(f, E) fini ).

    « Si f est une application d'un ensemble fini E dans F, alors f(E) est une partie
    FINIE de F. »  ⚠ La FINITUDE de f(E) exige la surjection canonique E ↠ f(E) ⇒
    Card f(E) ≤ Card E (choix / section) + Cor. 1 (fini_downward, C61) → REPORTÉE.
    La moitié « partie de F » est inconditionnelle (conjoint « image⊂F » de
    est_application_de) ; la borne Card(image) ≤ Card F est image_card_inf_egal_but.
    Renvoie la FORMULE-cible — JAMAIS prouvée ni postulée."""
    vf, vE, vF = _t(f), _t(Eens), _t(F)
    img = E.image(vf, vE)
    return impl(est_fini_ensemble(vE),
                et(inclus(img, vF), est_fini_ensemble(img)))


__all__ = [
    # ✅ INCONDITIONNELS — transport de la finitude par équipotence
    "equipotent_implique_fini_cardinal",
    "equipotent_implique_fini_ensemble",
    "equipotent_ssi_fini_ensemble",
    # ✅ INCONDITIONNELS — sous-ensemble / image : bornes cardinales
    "sous_ensemble_card_inf_egal",
    "image_card_inf_egal_but",
    # ⚠️ CONDITIONNELS au contenu non trivial (reports ISOLÉS déchargés en antécédent)
    "cor2_partie_stricte_card_strict_cond",
    "reunion_disjointe_finie_cond",
    "cor3_image_finie_cond",
    # ⚠️ ÉNONCÉ REPORTÉ (formule-cible, jamais postulée)
    "cor3_image_finie_cible",
]
