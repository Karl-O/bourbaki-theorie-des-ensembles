"""§III.4.1 — PROPOSITION 1 :  ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞+1)).

Énoncé VERBATIM (E.III.4.1, Proposition 1) :

    « Pour qu'un cardinal 𝔞 soit fini, il faut et il suffit que 𝔞 + 1 soit fini. »

Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 est un cardinal) ∧ (𝔞 ≠ 𝔞 + 1), où 𝔞 + 1 =
successeur(𝔞) = Card(𝔞 ⊔ {∅}) (successeur cardinal fidèle).  Bourbaki SUPPOSE 𝔞
cardinal (« Pour qu'un cardinal 𝔞 … ») ; on respecte cette hypothèse — elle est
indispensable au sens réciproque (𝔞+1 cardinal n'entraîne PAS, à lui seul, que 𝔞 le
soit).  L'énoncé certifié est donc :

        ⊢ est_cardinal(𝔞)  ⇒  ( Fini(𝔞)  ⇔  Fini(𝔞+1) ).

──────────────────────────────────────────────────────────────────────────────────
CLÉ = PROPOSITION 8 (ensembles_prop8_fini2.prop8_successeur_injectif, round 21) :

        ⊢ (successeur(A) = successeur(B)) ⇒ (Card A = Card B)   (le successeur cardinal
                                                                  est injectif).

Tout le travail logique passe par l'équivalence des deux conjoints « ≠ successeur » :

        (𝔞 ≠ 𝔞+1)  ⇔  (𝔞+1 ≠ 𝔞+2)         [SOUS l'hypothèse est_cardinal(𝔞)],

obtenue par CONTRAPOSITION de l'équivalence des égalités correspondantes :

        (𝔞 = 𝔞+1)  ⇔  (𝔞+1 = 𝔞+2).

  • SENS  (𝔞+1 = 𝔞+2) ⇒ (𝔞 = 𝔞+1) :   𝔞+1 = 𝔞+2 EST successeur(𝔞) = successeur(𝔞+1)
    (car 𝔞+1 = successeur(𝔞) et 𝔞+2 = successeur(𝔞+1)) ; la Proposition 8 donne alors
    Card(𝔞) = Card(𝔞+1) ; or 𝔞+1 = successeur(𝔞) est TOUJOURS un cardinal, donc
    Card(𝔞+1) = 𝔞+1, et 𝔞 cardinal donne Card(𝔞) = 𝔞 ; d'où 𝔞 = 𝔞+1.

  • SENS  (𝔞 = 𝔞+1) ⇒ (𝔞+1 = 𝔞+2) :   par CONGRUENCE du terme successeur(·) :
    𝔞 = 𝔞+1 ⇒ successeur(𝔞) = successeur(𝔞+1), c.-à-d. 𝔞+1 = 𝔞+2.

Le premier conjoint « cardinal » se gère FIDÈLEMENT des deux côtés :
  • Fini(𝔞+1) exige est_cardinal(𝔞+1) : TOUJOURS vrai (𝔞+1 = Card(𝔞⊔{∅}) est de la
    forme Card X ; card_est_un_cardinal) ;
  • Fini(𝔞) exige est_cardinal(𝔞) : c'est l'HYPOTHÈSE de la Proposition (𝔞 cardinal).

LEMMES (tous CERTIFIÉS par le noyau, rien postulé) :
  • _card_idempotent_t(X)            — ⊢ Card(Card X) = Card X  (réexporté du patron
        de fini_deux : Eq(X, Card X) + Prop. 1 sens direct) ;
  • cardinal_de_cardinal(a)          — ⊢ est_cardinal(𝔞) ⇒ (Card(𝔞) = 𝔞) ;
  • successeur_est_un_cardinal(a)    — ⊢ est_cardinal(𝔞+1)  (inconditionnel) ;
  • succ_egal_implique_distinct(a)   — ⊢ est_cardinal(𝔞) ⇒ ((𝔞+1 = 𝔞+2) ⇒ (𝔞 = 𝔞+1)) ;
  • distinct_implique_succ_egal(a)   — ⊢ (𝔞 = 𝔞+1) ⇒ (𝔞+1 = 𝔞+2)  (congruence) ;
  • fini_implique_fini_successeur(a) — ⊢ Fini(𝔞) ⇒ Fini(𝔞+1)   (SENS DIRECT) ;
  • fini_successeur_implique_fini(a) — ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞+1) ⇒ Fini(𝔞))  (RÉCIPR.) ;
  • fini_ssi_fini_successeur(a)      — ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞+1))  (PROP. 1).

Aucun axiome nouveau ; la Proposition 8 qui ferme l'argument est elle-même
inconditionnelle et close (transposition CONSTRUITE).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, Terme, egal, non, et, impl, equiv
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (equipotent_son_cardinal,
                                          cardinal_egal_si_equipotent)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, contraposition,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                                          composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, est_fini
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_fini2 import prop8_successeur_injectif


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ═══════════════════════════════════════════════════════════════════════════════
# IDEMPOTENCE :  ⊢ Card(Card X) = Card X   (un cardinal est son propre cardinal)
# ═══════════════════════════════════════════════════════════════════════════════
def _card_idempotent_t(tX):
    """⊢ Card(Card X) = Card X   pour un TERME X.   (un cardinal est son propre cardinal.)

    Eq(X, Card X) (equipotent_son_cardinal) ; la Proposition 1 sens direct
    (cardinal_egal_si_equipotent à (X, Card X)) donne Card X = Card(Card X) ; symétrie.
    Patron identique à ensembles_fini_deux._card_idempotent_t (re-dérivé localement
    pour ne dépendre que de l'API publique de ensembles_cardinaux_theoremes)."""
    eq_thm = N.generalisation("X", equipotent_son_cardinal("X"))                 # (∀X) Eq(X, Card X)
    ceq = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))                                  # (∀X)(∀Y)(Eq(X,Y)⇒CardX=CardY)
    cX = cardinal(tX)
    eqX = instancie(eq_thm, tX)                                                  # Eq(X, Card X)
    cimp = instancie(instancie(ceq, tX), cX)                                     # Eq(X,CardX) ⇒ CardX=Card(CardX)
    cardX_eq = N.modus_ponens(eqX, cimp)                                         # Card X = Card(Card X)
    return N.modus_ponens(cardX_eq, symetrie(cX, cardinal(cX)))                  # Card(Card X) = Card X


# ═══════════════════════════════════════════════════════════════════════════════
# ⊢ est_cardinal(𝔞) ⇒ (Card(𝔞) = 𝔞)   (un cardinal EST son propre cardinal)
# ═══════════════════════════════════════════════════════════════════════════════
def cardinal_de_cardinal(a="a", x="X"):
    """⊢ est_cardinal(𝔞) ⇒ (Card(𝔞) = 𝔞).   (un cardinal coïncide avec son cardinal.)

    est_cardinal(𝔞) = (∃X)(𝔞 = Card X).  Sous un témoin 𝔞 = Card X :
      • congruence du terme Card(·) : 𝔞 = Card X ⇒ Card(𝔞) = Card(Card X) ;
      • idempotence : Card(Card X) = Card X  (_card_idempotent_t) ;
      • symétrie du témoin : Card X = 𝔞.
    Composition ⇒ Card(𝔞) = 𝔞.  Le témoin X étant lié, on décharge par ∃-élimination
    (X n'est pas libre dans la conclusion Card(𝔞) = 𝔞, 𝔞 étant un paramètre ≠ X)."""
    va = _t(a)
    vX = var(x)
    cX = cardinal(vX)                                          # Card X
    temoin = egal(va, cX)                                      # 𝔞 = Card X
    h = N.assume(temoin)
    # 𝔞 = Card X ⇒ Card(𝔞) = Card(Card X)   (congruence du terme Card(·))
    cong = N.modus_ponens(h, congruence_terme(va, cX, cardinal(var("w"))))   # Card(𝔞) = Card(Card X)
    idem = _card_idempotent_t(vX)                              # Card(Card X) = Card X
    card_a_eq_cX = composer_egalites(cong, idem)              # Card(𝔞) = Card X
    cX_eq_a = N.modus_ponens(h, symetrie(va, cX))             # Card X = 𝔞
    card_a_eq_a = composer_egalites(card_a_eq_cX, cX_eq_a)    # Card(𝔞) = 𝔞   [hyp témoin]
    imp = N.loi_deduction(temoin, card_a_eq_a)               # (𝔞 = Card X) ⇒ (Card(𝔞) = 𝔞)
    return existe_elimination(imp, x)                        # (∃X)(𝔞 = Card X) ⇒ (Card(𝔞) = 𝔞)


# ═══════════════════════════════════════════════════════════════════════════════
# ⊢ est_cardinal(𝔞 + 1)   (le successeur cardinal est TOUJOURS un cardinal)
# ═══════════════════════════════════════════════════════════════════════════════
def successeur_est_un_cardinal(a="a", x="X"):
    """⊢ est_cardinal(𝔞 + 1)  =  ⊢ (∃X)(𝔞+1 = Card X).   (INCONDITIONNEL, E.III.3.1, Déf. 2.)

    𝔞 + 1 = successeur(𝔞) = Card(𝔞 ⊔ {∅}) est, PAR DÉFINITION du successeur fidèle,
    de la forme Card(X) (témoin X := 𝔞 ⊔ {∅}).  Or successeur(𝔞) = cardinal(𝔞⊔{∅})
    littéralement ; card_est_un_cardinal(𝔞⊔{∅}) = (∃X)(Card(𝔞⊔{∅}) = Card X) EST donc
    déjà est_cardinal(successeur(𝔞)) = est_cardinal(𝔞+1)."""
    va = _t(a)
    # successeur(𝔞) = cardinal(somme_disjointe(𝔞, {∅})) (définition fidèle) : le sous-ensemble
    # est Y := 𝔞 ⊔ {∅}.  card_est_un_cardinal(Y) = (∃X)(Card(Y) = Card X) EST donc
    # est_cardinal(Card(Y)) = est_cardinal(successeur(𝔞)) = est_cardinal(𝔞+1).
    sous = somme_disjointe(va, E.singleton(E.VIDE))           # 𝔞 ⊔ {∅}  (= sous-ensemble de successeur(𝔞))
    return card_est_un_cardinal(sous, x)                     # est_cardinal(𝔞+1)


# ═══════════════════════════════════════════════════════════════════════════════
# ÉQUIVALENCE DES CONJOINTS « ≠ successeur » :  (𝔞 = 𝔞+1) ⇔ (𝔞+1 = 𝔞+2)
# ═══════════════════════════════════════════════════════════════════════════════
def distinct_implique_succ_egal(a="a"):
    """⊢ (𝔞 = 𝔞 + 1) ⇒ (𝔞 + 1 = 𝔞 + 2).   (congruence du terme successeur, E.III.4.1.)

    Si 𝔞 = 𝔞+1, alors successeur(𝔞) = successeur(𝔞+1) par CONGRUENCE du terme
    successeur(·) (congruence_terme avec le trou w) ; or successeur(𝔞) = 𝔞+1 et
    successeur(𝔞+1) = 𝔞+2 (définitions), d'où 𝔞+1 = 𝔞+2."""
    va = _t(a)
    succ_a = successeur(va)                                   # 𝔞 + 1
    # le terme successeur(·) avec trou « w » : congruence_terme construit (w|w)succ = succ(w)
    return congruence_terme(va, succ_a, successeur(var("w")))  # (𝔞 = 𝔞+1) ⇒ (succ 𝔞 = succ(𝔞+1)) = (𝔞+1 = 𝔞+2)


def succ_egal_implique_distinct(a="a"):
    """⊢ est_cardinal(𝔞) ⇒ ((𝔞 + 1 = 𝔞 + 2) ⇒ (𝔞 = 𝔞 + 1)).   (PROPOSITION 8 appliquée.)

    𝔞+1 = 𝔞+2 EST successeur(𝔞) = successeur(𝔞+1) (def.) ; la Proposition 8 donne
    Card(𝔞) = Card(𝔞+1) ; sous est_cardinal(𝔞), Card(𝔞) = 𝔞 (cardinal_de_cardinal),
    et inconditionnellement Card(𝔞+1) = 𝔞+1 (cardinal_de_cardinal + successeur cardinal) ;
    réécritures ⇒ 𝔞 = 𝔞+1.  Sous l'hypothèse est_cardinal(𝔞)."""
    va = _t(a)
    succ_a = successeur(va)                                   # 𝔞 + 1
    succ_succ_a = successeur(succ_a)                          # 𝔞 + 2

    # Proposition 8 à (A := 𝔞, B := 𝔞+1) : (succ 𝔞 = succ(𝔞+1)) ⇒ (Card 𝔞 = Card(𝔞+1))
    gen = N.generalisation("A", N.generalisation("B", prop8_successeur_injectif("A", "B")))
    p8 = instancie(instancie(gen, va), succ_a)               # (𝔞+1 = 𝔞+2) ⇒ (Card 𝔞 = Card(𝔞+1))

    # Card(𝔞+1) = 𝔞+1  (INCONDITIONNEL : 𝔞+1 est un cardinal)
    succ_is_card = successeur_est_un_cardinal(a)             # est_cardinal(𝔞+1)
    card_succ_eq = N.modus_ponens(succ_is_card, cardinal_de_cardinal(succ_a))   # Card(𝔞+1) = 𝔞+1

    # Card(𝔞) = 𝔞  SOUS est_cardinal(𝔞)
    h_card_a = N.assume(est_cardinal(va))
    card_a_eq = N.modus_ponens(h_card_a, cardinal_de_cardinal(va))             # Card(𝔞) = 𝔞   [hyp card 𝔞]

    # SOUS (𝔞+1 = 𝔞+2) :  Card(𝔞) = Card(𝔞+1)  ⇒ (réécritures)  𝔞 = 𝔞+1
    h_succ_eq = N.assume(egal(succ_a, succ_succ_a))          # 𝔞+1 = 𝔞+2
    card_eq = N.modus_ponens(h_succ_eq, p8)                  # Card(𝔞) = Card(𝔞+1)  [hyp 𝔞+1=𝔞+2]
    # 𝔞 = Card(𝔞)  (symétrie de Card(𝔞)=𝔞)  puis  = Card(𝔞+1)  puis  = 𝔞+1
    a_eq_card_a = symetrie(cardinal(va), va)                 # (Card 𝔞 = 𝔞) ⇒ (𝔞 = Card 𝔞)
    a_eq_card_a = N.modus_ponens(card_a_eq, a_eq_card_a)     # 𝔞 = Card(𝔞)   [hyp card 𝔞]
    a_eq_card_succ = composer_egalites(a_eq_card_a, card_eq)  # 𝔞 = Card(𝔞+1)
    a_eq_succ = composer_egalites(a_eq_card_succ, card_succ_eq)   # 𝔞 = 𝔞+1   [hyps card 𝔞, 𝔞+1=𝔞+2]

    inner = N.loi_deduction(egal(succ_a, succ_succ_a), a_eq_succ)   # (𝔞+1=𝔞+2) ⇒ (𝔞=𝔞+1)   [hyp card 𝔞]
    return N.loi_deduction(est_cardinal(va), inner)         # est_cardinal(𝔞) ⇒ ((𝔞+1=𝔞+2) ⇒ (𝔞=𝔞+1))


# ═══════════════════════════════════════════════════════════════════════════════
# SENS DIRECT :  ⊢ Fini(𝔞) ⇒ Fini(𝔞 + 1)
# ═══════════════════════════════════════════════════════════════════════════════
def fini_implique_fini_successeur(a="a"):
    """⊢ Fini(𝔞) ⇒ Fini(𝔞 + 1).   (PROPOSITION 1, sens « il faut », E.III.4.1.)

    Sous Fini(𝔞) = (est_cardinal(𝔞) et 𝔞 ≠ 𝔞+1) :
      • 1er conjoint de Fini(𝔞+1) : est_cardinal(𝔞+1) — INCONDITIONNEL ;
      • 2e conjoint : 𝔞+1 ≠ 𝔞+2.  De est_cardinal(𝔞) (1er conjoint de Fini(𝔞)),
        succ_egal_implique_distinct donne (𝔞+1=𝔞+2) ⇒ (𝔞=𝔞+1) ; sa CONTRAPOSÉE
        envoie ¬(𝔞=𝔞+1) (2e conjoint de Fini(𝔞)) sur ¬(𝔞+1=𝔞+2)."""
    va = _t(a)
    succ_a = successeur(va)                                   # 𝔞 + 1
    succ_succ_a = successeur(succ_a)                          # 𝔞 + 2

    h = N.assume(est_fini(va))                                # Fini(𝔞)
    card_a = conjonction_elim_gauche(h)                       # est_cardinal(𝔞)
    ne_a = conjonction_elim_droite(h)                         # ¬(𝔞 = 𝔞+1)

    # 1er conjoint : est_cardinal(𝔞+1)
    succ_is_card = successeur_est_un_cardinal(a)             # est_cardinal(𝔞+1)

    # 2e conjoint : ¬(𝔞+1 = 𝔞+2)  par contraposée de (𝔞+1=𝔞+2)⇒(𝔞=𝔞+1)
    imp = N.modus_ponens(card_a, succ_egal_implique_distinct(a))   # (𝔞+1=𝔞+2) ⇒ (𝔞=𝔞+1)
    contra = contraposition(imp)                             # ¬(𝔞=𝔞+1) ⇒ ¬(𝔞+1=𝔞+2)
    ne_succ = N.modus_ponens(ne_a, contra)                   # ¬(𝔞+1 = 𝔞+2)

    fini_succ = conjonction_intro(succ_is_card, ne_succ)     # Fini(𝔞+1)
    return N.loi_deduction(est_fini(va), fini_succ)          # Fini(𝔞) ⇒ Fini(𝔞+1)


# ═══════════════════════════════════════════════════════════════════════════════
# SENS RÉCIPROQUE :  ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞 + 1) ⇒ Fini(𝔞))
# ═══════════════════════════════════════════════════════════════════════════════
def fini_successeur_implique_fini(a="a"):
    """⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞 + 1) ⇒ Fini(𝔞)).   (PROPOSITION 1, sens « il suffit ».)

    Bourbaki suppose 𝔞 cardinal (« Pour qu'un CARDINAL 𝔞 … ») : c'est l'hypothèse
    est_cardinal(𝔞), indispensable car Fini(𝔞+1) seul ne fournit PAS que 𝔞 est un
    cardinal.  Sous est_cardinal(𝔞) et Fini(𝔞+1) = (est_cardinal(𝔞+1) et 𝔞+1 ≠ 𝔞+2) :
      • 1er conjoint de Fini(𝔞) : est_cardinal(𝔞) — l'HYPOTHÈSE ;
      • 2e conjoint : 𝔞 ≠ 𝔞+1.  distinct_implique_succ_egal donne (𝔞=𝔞+1)⇒(𝔞+1=𝔞+2) ;
        sa CONTRAPOSÉE envoie ¬(𝔞+1=𝔞+2) (2e conjoint de Fini(𝔞+1)) sur ¬(𝔞=𝔞+1)."""
    va = _t(a)
    succ_a = successeur(va)                                   # 𝔞 + 1
    succ_succ_a = successeur(succ_a)                          # 𝔞 + 2

    h_card_a = N.assume(est_cardinal(va))                     # est_cardinal(𝔞)   (hypothèse Bourbaki)
    h_fs = N.assume(est_fini(succ_a))                         # Fini(𝔞+1)
    ne_succ = conjonction_elim_droite(h_fs)                   # ¬(𝔞+1 = 𝔞+2)

    # 2e conjoint de Fini(𝔞) : ¬(𝔞 = 𝔞+1)  par contraposée de (𝔞=𝔞+1)⇒(𝔞+1=𝔞+2)
    contra = contraposition(distinct_implique_succ_egal(a))   # ¬(𝔞+1=𝔞+2) ⇒ ¬(𝔞=𝔞+1)
    ne_a = N.modus_ponens(ne_succ, contra)                    # ¬(𝔞 = 𝔞+1)

    fini_a = conjonction_intro(h_card_a, ne_a)               # Fini(𝔞)  [hyps card 𝔞, Fini(𝔞+1)]
    inner = N.loi_deduction(est_fini(succ_a), fini_a)        # Fini(𝔞+1) ⇒ Fini(𝔞)   [hyp card 𝔞]
    return N.loi_deduction(est_cardinal(va), inner)          # est_cardinal(𝔞) ⇒ (Fini(𝔞+1) ⇒ Fini(𝔞))


# ═══════════════════════════════════════════════════════════════════════════════
# PROPOSITION 1 (COMPLÈTE) :  ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞 + 1))
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §4.1 Prop.1 | E III.31 L.17-18 | PDF p.134
def fini_ssi_fini_successeur(a="a"):
    """⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞 + 1)).   (PROPOSITION 1, E.III.4.1.)

    « Pour qu'un cardinal 𝔞 soit fini, il faut et il suffit que 𝔞 + 1 soit fini. »
    Sous l'hypothèse est_cardinal(𝔞) (le « cardinal 𝔞 » de l'énoncé), on assemble
    l'équivalence à partir des deux sens :
      • il FAUT   :  fini_implique_fini_successeur  (Fini(𝔞) ⇒ Fini(𝔞+1)), INCONDITIONNEL ;
      • il SUFFIT :  fini_successeur_implique_fini   (sous est_cardinal(𝔞), Fini(𝔞+1) ⇒ Fini(𝔞)).
    L'équivalence Fini(𝔞) ⇔ Fini(𝔞+1) EST la conjonction de ces deux implications."""
    va = _t(a)
    fwd = fini_implique_fini_successeur(a)                    # Fini(𝔞) ⇒ Fini(𝔞+1)   (⊢, sans hyp)
    bwd_under = N.modus_ponens(N.assume(est_cardinal(va)),
                               fini_successeur_implique_fini(a))   # Fini(𝔞+1) ⇒ Fini(𝔞)   [hyp card 𝔞]
    equ = conjonction_intro(fwd, bwd_under)                  # Fini(𝔞) ⇔ Fini(𝔞+1)   [hyp card 𝔞]
    return N.loi_deduction(est_cardinal(va), equ)            # est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞+1))


__all__ = ["cardinal_de_cardinal", "successeur_est_un_cardinal",
           "distinct_implique_succ_egal", "succ_egal_implique_distinct",
           "fini_implique_fini_successeur", "fini_successeur_implique_fini",
           "fini_ssi_fini_successeur"]
