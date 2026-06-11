"""§III.6 — PROPOSITIONS DIRECTES sur les ensembles INFINIS / DÉNOMBRABLES.

Ce module SALVAGE, de manière GRADUÉE (anti-faux), les énoncés ATTEIGNABLES de
E.III.6 à partir des DÉFINITIONS de ensembles_infinis.py (est_infini = ¬Fini,
est_denombrable, A4, N opaque) et des grands théorèmes DÉJÀ prouvés du projet
(comparabilité des cardinaux, transport par équipotence, monotonie de ≤).

────────────────────────────────────────────────────────────────────────────────
ÉTAT DES PALIERS (cf. les __all__) :

  ✅ INCONDITIONNEL (rien postulé, theorie_ensembles()=22) :
     • cardinal_egal_succ_implique_infini(a)   — (a = a+1) ⇒ est_infini(a)
            [sens FACILE de la caractérisation de Dedekind : si a = a+1, alors a ne
             peut PAS être fini (Fini(a) = est_cardinal(a) ∧ a≠a+1 exige a≠a+1)] ;
            ⚠️ NB : la réciproque « est_infini(a) ⇒ a=a+1 » est FAUSSE SANS est_cardinal(a)
            (un non-cardinal est ¬Fini trivialement sans être stable par +1) ; c'est
            pourquoi le sens dur ci-dessous porte la garde est_cardinal(a) ;
     • cardinal_infini_implique_egal_succ(a)   — (est_cardinal(a) et est_infini(a)) ⇒ a = a+1
            [sens DUR de Dedekind, sous est_cardinal : a infini ⇒ a stabilise par +1] ;
     • dedekind_cardinal(a)                     — est_cardinal(a) ⇒ ( est_infini(a) ⇔ a = a+1 )
            [CARACTÉRISATION DE DEDEKIND complète pour un cardinal : « infini ⟺ a+1=a »] ;
     • existe_cardinal_infini()                 — (∃a) ¬Fini(a)   [A4 ⇒ un cardinal infini
            existe ; ré-exposition du théorème cardinal_infini_existe (ÉTAPE A de ℕ)].

  ⚠️ CONDITIONNEL (report fini_downward DÉCHARGÉ en antécédent explicite, JAMAIS
     postulé — devient inconditionnel dès que fini_downward_thm l'est, cf.
     ensembles_recurrence_C61) :
     • infini_monotone_cond(a, b)               — fini_downward(a,b) ⇒ ((a≤b et a infini) ⇒ b infini)
            [MONOTONIE de l'infini : un cardinal au-dessus d'un infini est infini.
             CONTRAPOSÉE de fini_downward : ¬Fini(a) ⇒ ¬(a≤b ∧ Fini b)] ;
     • infini_ensemble_monotone_cond(X, Y)      — version ENSEMBLES (via Card, X≤Y ⊂-monotone) ;
     • sous_ensemble_denombrable_cond(...)      — une partie d'un ensemble dénombrable est
            dénombrable (Prop. 1 §III.6.4 ; CONDITIONNEL au transport « A≤B et B dénombrable
            ⇒ A dénombrable », isolé en hyp — l'inclusion A⊂B ⇒ A≤B est INCONDITIONNELLE) ;
     • aleph0_inf_egal_cardinal_infini_enonce(a) — ÉNONCÉ (formule, pas théorème) :
            est_infini(a) ⇒ (ℵ₀ ≤ a).  REPORTÉ : exige « tout entier n vérifie n ≤ a » +
            collectivisation de N (Th. 1) + arithmétique cardinale infinie (sup/limite).

⚠️ INVARIANT : aucun N.axiome n'est ajouté à theorie_ensembles() (=22).  Les seuls
   « givens » sont des HYPOTHÈSES explicites (est_cardinal, fini_downward, a≤b),
   déchargées par loi_deduction.  Anti-tautologie/anti-affaibli strict : chaque
   énoncé inconditionnel a un CONTENU (la caractérisation de Dedekind n'est PAS
   P⇒P : elle relie ¬Fini à l'égalité a=a+1).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, impl, equiv)
from bourbaki.logique import noyau_abrege as N

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal, inf_egal_card
from bourbaki.entiers.ensembles_entiers import est_fini, est_fini_ensemble, successeur
from bourbaki.entiers.ensembles_infinis import (
    est_infini, est_infini_ensemble, est_denombrable, NN, aleph0,
)
from bourbaki.entiers.ensembles_N_collectivise import fini_downward

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  Brique : de « hyp H ⊢ Q » et « ⊢ ¬Q », déduire « ⊢ ¬H »  (ex falso fermé).
# ════════════════════════════════════════════════════════════════════════════
def _refuter(H, thm_Q_sous_H, thm_nQ):
    """{H ⊢ Q}, {⊢ ¬Q}  ⟹  ⊢ ¬H   (H et ¬Q incompatibles ⇒ ¬H).

    Motif standard du projet (cf. inf_strict_irreflexif) : sous H on a Q et ¬Q,
    d'où ¬H par (H⇒¬H)⇒¬H (S1).  thm_Q_sous_H a H dans ses hypothèses ouvertes ;
    thm_nQ est CLOS (ou à hyps disjointes de H)."""
    Q = thm_Q_sous_H.conclusion
    # sous H : ¬H   (de Q et ¬Q : Q ⇒ (¬Q ⇒ ¬H))
    falso = N.modus_ponens(thm_Q_sous_H,
                           N.modus_ponens(thm_nQ, N.s2(non(Q), non(H))))   # ¬H  [sous H]
    return N.modus_ponens(N.loi_deduction(H, falso), N.s1(non(H)))         # ¬H


# ════════════════════════════════════════════════════════════════════════════
#  (1) DEDEKIND, sens FACILE :  (a = a+1) ⇒ est_infini(a)   (INCONDITIONNEL)
#
#  est_infini(a) = ¬Fini(a) = ¬( est_cardinal(a) ∧ a≠a+1 ).  Si a = a+1, alors le
#  2ᵉ conjoint a≠a+1 est FAUX, donc Fini(a) est faux : ¬Fini(a).  Aucune hypothèse —
#  vrai même si a n'est pas un cardinal (la conjonction est de toute façon fausse).
# ════════════════════════════════════════════════════════════════════════════
def cardinal_egal_succ_implique_infini(a="a"):
    """⊢ ( a = a + 1 ) ⇒ est_infini(a).   (DEDEKIND, sens facile ; INCONDITIONNEL.)

    Caractérisation de Dedekind (E.III.6 / le « cardinal stable par successeur »).
    Fini(a) = est_cardinal(a) ∧ (a ≠ a+1) ; sous l'hypothèse a = a+1, le 2ᵉ conjoint
    a ≠ a+1 est réfuté (¬¬(a=a+1) contredirait a≠a+1).  Donc Fini(a) est faux, i.e.
    est_infini(a) = ¬Fini(a).  Vrai pour TOUT terme a (pas besoin de est_cardinal)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dni
    va = _t(a)
    sa = successeur(va)
    fini = est_fini(va)                                   # est_cardinal(a) ∧ a≠a+1
    h_eq = N.assume(egal(va, sa))                         # a = a+1
    # ¬(a≠a+1) = ¬¬(a=a+1)  depuis a=a+1  (introduction de la double négation)
    nn_eq = N.modus_ponens(h_eq, dni(egal(va, sa)))       # ¬¬(a=a+1) = ¬(a≠a+1)  [sous a=a+1]
    # Fini(a) ⊢ a≠a+1 (2ᵉ conjoint) ; contredit ¬(a≠a+1)  →  ¬Fini(a)
    h_fini = N.assume(fini)                               # Fini(a)
    ne = conjonction_elim_droite(h_fini)                  # ¬(a = a+1)   [sous Fini a]
    nfini_sous = _refuter(fini, ne, nn_eq)                # ¬Fini(a)   [sous a=a+1]
    return N.loi_deduction(egal(va, sa), nfini_sous)      # (a=a+1) ⇒ ¬Fini(a) = est_infini(a)


# ════════════════════════════════════════════════════════════════════════════
#  (2) DEDEKIND, sens DUR :  (est_cardinal(a) et est_infini(a)) ⇒ a = a+1
#                                                                   (INCONDITIONNEL)
#
#  est_infini(a) = ¬Fini(a) = ¬( est_cardinal(a) ∧ a≠a+1 ).  Sous est_cardinal(a),
#  si l'on avait a≠a+1, la conjonction donnerait Fini(a), contredisant ¬Fini(a).
#  Donc ¬(a≠a+1) = ¬¬(a=a+1), d'où a=a+1 (dne).  L'hypothèse est_cardinal(a) est
#  INDISPENSABLE (sans elle, ¬Fini(a) ne force pas a=a+1 — un non-cardinal a ¬Fini
#  trivialement sans être stable par +1).
# ════════════════════════════════════════════════════════════════════════════
def cardinal_infini_implique_egal_succ(a="a"):
    """⊢ ( est_cardinal(a) et est_infini(a) ) ⇒ ( a = a + 1 ).   (DEDEKIND, sens dur.)

    « Un cardinal infini est STABLE par successeur » (a + 1 = a) : c'est le contenu
    de la caractérisation de Dedekind dans le sens non trivial.  est_infini(a)=¬Fini(a)
    et Fini(a)=est_cardinal(a)∧(a≠a+1) ; sous est_cardinal(a), supposer a≠a+1 donnerait
    Fini(a) (conjonction), contredisant ¬Fini(a) ; donc ¬(a≠a+1), i.e. a=a+1 (double
    négation).  Hypothèse est_cardinal(a) ESSENTIELLE (cf. docstring du module)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne
    va = _t(a)
    sa = successeur(va)
    ante = et(est_cardinal(va), est_infini(va))
    h = N.assume(ante)
    h_card = conjonction_elim_gauche(h)                   # est_cardinal(a)
    h_inf = conjonction_elim_droite(h)                    # est_infini(a) = ¬Fini(a)
    # supposer a≠a+1 : Fini(a) = est_cardinal(a) ∧ (a≠a+1) ; contredit ¬Fini(a)
    h_ne = N.assume(non(egal(va, sa)))                    # a ≠ a+1
    fini = conjonction_intro(h_card, h_ne)                # Fini(a)   [sous est_card, a≠a+1]
    nn_eq = _refuter(non(egal(va, sa)), fini, h_inf)      # ¬(a≠a+1)  [sous est_card]
    eq = N.modus_ponens(nn_eq, dne(egal(va, sa)))         # a = a+1   [sous est_card]
    return N.loi_deduction(ante, eq)                      # (est_card et infini) ⇒ a=a+1


# ════════════════════════════════════════════════════════════════════════════
#  (3) DEDEKIND complète :  est_cardinal(a) ⇒ ( est_infini(a) ⇔ a = a+1 )
# ════════════════════════════════════════════════════════════════════════════
def dedekind_cardinal(a="a"):
    """⊢ est_cardinal(a) ⇒ ( est_infini(a) ⇔ ( a = a + 1 ) ).   (DEDEKIND ; INCONDITIONNEL.)

    CARACTÉRISATION DE DEDEKIND d'un cardinal infini (E.III.6) : « un cardinal est
    infini si et seulement si il est égal à son successeur » (a + 1 = a).  Conjonction
    des deux sens :
      • (⇒) est_infini(a) ⇒ a=a+1  — sens DUR (cardinal_infini_implique_egal_succ,
        sous est_cardinal(a)) ;
      • (⇐) a=a+1 ⇒ est_infini(a)  — sens FACILE (cardinal_egal_succ_implique_infini,
        INCONDITIONNEL, ré-introduit sous est_cardinal).
    Sous l'hypothèse est_cardinal(a), déchargée (l'équivalence VAUT pour un cardinal)."""
    va = _t(a)
    sa = successeur(va)
    h_card = N.assume(est_cardinal(va))                   # est_cardinal(a)
    # (⇒) : sous est_cardinal(a), de est_infini(a) déduire a=a+1
    hard = cardinal_infini_implique_egal_succ(a)          # (est_card et infini) ⇒ a=a+1
    h_inf = N.assume(est_infini(va))                      # est_infini(a)
    eq = N.modus_ponens(conjonction_intro(h_card, h_inf), hard)   # a = a+1   [est_card, infini]
    sens_avant = N.loi_deduction(est_infini(va), eq)      # est_infini(a) ⇒ a=a+1   [est_card]
    # (⇐) : a=a+1 ⇒ est_infini(a)   (inconditionnel)
    sens_arriere = cardinal_egal_succ_implique_infini(a)  # (a=a+1) ⇒ est_infini(a)
    equ = conjonction_intro(sens_avant, sens_arriere)     # est_infini(a) ⇔ a=a+1   [est_card]
    return N.loi_deduction(est_cardinal(va), equ)         # est_card(a) ⇒ (infini ⇔ a=a+1)


# ════════════════════════════════════════════════════════════════════════════
#  (4) Un cardinal INFINI existe  (A4 ⇒ (∃a)¬Fini(a))   — ré-exposition E.III.6.
# ════════════════════════════════════════════════════════════════════════════
def existe_cardinal_infini(a="a", X="X"):
    """⊢ (∃a) est_infini(a)   (= il existe un cardinal infini, de A4, §III.6.1).

    THÉORÈME (de l'axiome de l'infini A4) : il existe un cardinal infini.  est_infini(a)
    = ¬Fini(a) ; c'est exactement l'ÉTAPE A de la collectivisation de ℕ
    (cardinal_infini_existe, prouvée INCONDITIONNELLEMENT à partir de A4).  Ré-exposé
    ici dans le contexte « ensembles infinis » §III.6.  (Point de départ de toute la
    théorie des cardinaux infinis ; sa pleine exploitation — N≤a, ℵ₀ — exige Th. 1.)"""
    from bourbaki.entiers.ensembles_N_collectivise import cardinal_infini_existe
    return cardinal_infini_existe(a, X)                   # (∃a)¬Fini(a) = (∃a)est_infini(a)


# ════════════════════════════════════════════════════════════════════════════
#  (5) MONOTONIE de l'infini (CONTRAPOSÉE de fini_downward)  — CONDITIONNEL.
#
#  fini_downward(a,b) = (a≤b et Fini b) ⇒ Fini a.  Contraposée : ¬Fini a ⇒ ¬(a≤b ∧
#  Fini b).  Avec a≤b (hyp), on conclut ¬Fini b = b infini.  REPORT : fini_downward
#  dépend de la récurrence C61 (ensembles_recurrence_C61) ; il est DÉCHARGÉ en
#  antécédent, JAMAIS postulé.
# ════════════════════════════════════════════════════════════════════════════
def infini_monotone_cond(a="a", b="b"):
    """⊢ fini_downward(a,b) ⇒ ( ( a ≤ b et est_infini(a) ) ⇒ est_infini(b) ).

    🎯 MONOTONIE de l'infini (E.III.6, voisin de Prop. 3) : un cardinal au-dessus d'un
    cardinal infini est infini.  C'est la CONTRAPOSÉE de fini_downward = (a≤b et Fini b)
    ⇒ Fini a : si b était fini, a (≤ b) le serait, contredisant a infini.  Sous a≤b et
    ¬Fini a, on déduit ¬Fini b = est_infini(b).  ⚠️ CONDITIONNEL : fini_downward(a,b)
    DÉCHARGÉ en antécédent (report C61, ensembles_recurrence_C61) ; jamais postulé.

    Preuve : sous fini_downward(a,b), a≤b, est_infini(a)=¬Fini(a) :
       supposer Fini(b) ; avec a≤b, fini_downward donne Fini(a), contredisant ¬Fini(a) ;
       donc ¬Fini(b) = est_infini(b)."""
    va, vb = _t(a), _t(b)
    fd = fini_downward(va, vb)                            # (a≤b et Fini b) ⇒ Fini a
    h_fd = N.assume(fd)
    ante = et(inf_egal_card(va, vb), est_infini(va))      # a≤b et ¬Fini a
    h = N.assume(ante)
    h_le = conjonction_elim_gauche(h)                     # a ≤ b
    h_inf_a = conjonction_elim_droite(h)                  # ¬Fini(a)
    # supposer Fini(b) : Fini(a) (downward), contredit ¬Fini(a)  →  ¬Fini(b)
    h_fini_b = N.assume(est_fini(vb))                     # Fini(b)
    fini_a = N.modus_ponens(conjonction_intro(h_le, h_fini_b), h_fd)   # Fini(a)  [sous Fini b]
    n_fini_b = _refuter(est_fini(vb), fini_a, h_inf_a)    # ¬Fini(b) = est_infini(b)
    inner = N.loi_deduction(ante, n_fini_b)              # (a≤b et infini a) ⇒ infini b  [fd]
    return N.loi_deduction(fd, inner)                    # fini_downward ⇒ (… ⇒ infini b)


def infini_ensemble_monotone_cond(X="X", Y="Y"):
    """⊢ fini_downward(Card X, Card Y) ⇒ ( ( Card X ≤ Card Y et X infini ) ⇒ Y infini ).

    Version ENSEMBLES de la monotonie de l'infini (E.III.6) : si X est infini et son
    cardinal est ≤ celui de Y, alors Y est infini.  « X infini » = est_infini_ensemble(X)
    = ¬Fini(Card X) = est_infini(Card X) ; idem pour Y.  Simple spécialisation de
    infini_monotone_cond aux termes Card X, Card Y (est_infini_ensemble(E)=est_infini(Card E)
    LITTÉRALEMENT).  ⚠️ CONDITIONNEL : fini_downward(Card X,Card Y) déchargé (report C61).

    NB : on n'introduit PAS l'inclusion X⊂Y ici (le pont X⊂Y ⇒ Card X≤Card Y est dans
    ensembles_finis_props.partie_inf_egal_card) — on prend directement Card X ≤ Card Y,
    qui est l'hypothèse pertinente pour la monotonie cardinale."""
    cX, cY = cardinal(_t(X)), cardinal(_t(Y))
    return infini_monotone_cond(cX, cY)                  # est_infini_ensemble = est_infini∘Card


# ════════════════════════════════════════════════════════════════════════════
#  (6) DÉNOMBRABLE : sous-ensemble d'un dénombrable  (CONDITIONNEL, transport isolé).
#
#  est_denombrable(E) = (∃Y)(Y⊂N et Eq(E,Y)).  « Une partie d'un dénombrable est
#  dénombrable » exige : de A⊂B et B dénombrable, construire une partie de N
#  équipotente à A.  La construction (composer la bijection B≃Y⊂N avec l'injection
#  A↪B, restreindre l'image) est l'objet de la Prop. 1 §III.6.4, qui repose sur le
#  transport « E ≤ dénombrable ⇒ E dénombrable » (cardinal) — REPORTÉ.  On le DÉCHARGE
#  en hypothèse isolée pour fournir l'énoncé CLOS sans rien postuler.
# ════════════════════════════════════════════════════════════════════════════
def _transport_denombrable(A, B):
    """ÉNONCÉ (report) : ( A ≤ B et B dénombrable ) ⇒ A dénombrable   (transport cardinal).

    « Si A s'injecte dans un ensemble dénombrable B, alors A est dénombrable » — la
    moitié « injection » de la Prop. 1 §III.6.4.  Renvoie la FORMULE-cible (pas une
    preuve) ; déchargée en antécédent par sous_ensemble_denombrable_cond.  JAMAIS
    postulée comme théorème (sa preuve = composition d'injections + restriction à une
    partie de N).  A ≤ B est le ≤ entre ENSEMBLES (injection de A dans B)."""
    return impl(et(inf_egal_card(_t(A), _t(B)), est_denombrable(_t(B))),
                est_denombrable(_t(A)))


def sous_ensemble_denombrable_cond(A="A", B="B"):
    """⊢ _transport_denombrable(A,B) ⇒ ( ( A ⊂ B et B dénombrable ) ⇒ A dénombrable ).

    🎯 PROPOSITION 1 §III.6.4 (partie d'un dénombrable), forme CONDITIONNELLE au
    contenu non trivial (PAS P⇒P) : « tout sous-ensemble d'un ensemble dénombrable est
    dénombrable ».  Preuve enchaînant une étape INCONDITIONNELLE et l'unique report :
      1. A ⊂ B ⇒ A ≤ B  (la diagonale Δ_A injecte A dans B — partie_inf_egal_card,
         au niveau ENSEMBLES : A ≤ B = (∃f) injection de A dans B) ;
      2. ( A ≤ B et B dénombrable ) ⇒ A dénombrable  [report H = _transport_denombrable,
         la moitié « injection » de la Prop. 1 §III.6.4 : composer A↪B avec B≃Y⊂N et
         restreindre l'image donne une bijection A≃(partie de N)].
    H est l'UNIQUE maillon reporté (déchargé en antécédent) — jamais postulé.  On dérive
    le_AB EN PREMIER puis on bâtit H à partir de SA conclusion (le ≤ ensembliste exact
    produit par partie_inf_egal_card), garantissant l'identité structurelle pour le MP."""
    from bourbaki.entiers.ensembles_finis_props import partie_inf_egal_card
    from bourbaki.logique.formule import inclus
    vA, vB = _t(A), _t(B)
    # étape 1 : A ⊂ B ⇒ A ≤ B   (ENSEMBLES) ; on capture A≤B = le_concl
    h_incl = N.assume(inclus(vA, vB))                     # A ⊂ B
    le_AB_thm = N.modus_ponens(h_incl, partie_inf_egal_card(A, B))   # A ≤ B   [sous A⊂B]
    le_concl = le_AB_thm.conclusion                       # la formule A ≤ B (forme exacte)
    # report H : ( A ≤ B et B dénombrable ) ⇒ A dénombrable   (bâti sur le_concl)
    H = impl(et(le_concl, est_denombrable(vB)), est_denombrable(vA))
    h_H = N.assume(H)
    ante = et(inclus(vA, vB), est_denombrable(vB))        # A ⊂ B et B dénombrable
    h = N.assume(ante)
    h_incl2 = conjonction_elim_gauche(h)                  # A ⊂ B
    h_den_B = conjonction_elim_droite(h)                  # B dénombrable
    le_AB = N.modus_ponens(h_incl2, partie_inf_egal_card(A, B))   # A ≤ B
    den_A = N.modus_ponens(conjonction_intro(le_AB, h_den_B), h_H)   # A dénombrable
    inner = N.loi_deduction(ante, den_A)                  # (A⊂B et B dén.) ⇒ A dén.   [H]
    return N.loi_deduction(H, inner)                      # H ⇒ (… ⇒ A dénombrable)


# ════════════════════════════════════════════════════════════════════════════
#  (7) ℵ₀ ≤ a  pour un cardinal infini a  — REPORTÉ (Théorème 1).
# ════════════════════════════════════════════════════════════════════════════
def aleph0_inf_egal_cardinal_infini_enonce(a="a"):
    """ÉNONCÉ (formule, NON théorème) : est_infini(a) ⇒ ( ℵ₀ ≤ a ).

    « Pour tout cardinal infini a, on a ℵ₀ ≤ a » (= N s'injecte dans tout infini,
    Théorème 1 / Prop. §III.6.1).  ⚠️ REPORTÉ : exige (i) la COLLECTIVISATION de N
    (Théorème 1, z∈N ⇔ Fini z — cf. ensembles_N_collectivise/ensembles_recurrence_C61,
    sous report fini_downward) ET (ii) « tout entier n vérifie n ≤ a »
    (entier_inf_egal_a, ÉTAPE C de ℕ, sous fini_downward) ; le passage de « tout n ≤ a »
    à « ℵ₀ = Card N ≤ a » requiert de PLUS l'ARITHMÉTIQUE CARDINALE INFINIE (sup/limite),
    absente.  Renvoie la FORMULE-cible ; JAMAIS postulée."""
    va = _t(a)
    return impl(est_infini(va), inf_egal_card(aleph0(), va))


__all__ = [
    # ✅ INCONDITIONNELS — caractérisation de Dedekind + existence
    "cardinal_egal_succ_implique_infini",
    "cardinal_infini_implique_egal_succ",
    "dedekind_cardinal",
    "existe_cardinal_infini",
    # ⚠️ CONDITIONNELS — monotonie de l'infini, partie d'un dénombrable (reports déchargés)
    "infini_monotone_cond",
    "infini_ensemble_monotone_cond",
    "sous_ensemble_denombrable_cond",
    # ⚠️ ÉNONCÉS REPORTÉS (formules-cibles, jamais postulées)
    "aleph0_inf_egal_cardinal_infini_enonce",
]
