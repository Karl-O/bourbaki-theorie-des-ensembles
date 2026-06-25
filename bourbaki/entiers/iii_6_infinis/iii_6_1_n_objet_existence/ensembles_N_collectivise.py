"""§III.6.1 — THÉORÈME 1 : « Fini(x) est collectivisante » (l'ensemble N des entiers
existe).  Module NEUF.

Bourbaki, E.III.6.1, Théorème 1 : « La relation "x est un entier" est collectivisante. »
Autrement dit l'ensemble N := {x | Fini(x)} des entiers naturels EXISTE.

────────────────────────────────────────────────────────────────────────────────
STRUCTURE DE LA PREUVE (recette A→E)

  On travaille avec un cardinal INFINI « a » (terme/variable) : est_cardinal(a) et
  ¬Fini(a).  ÉTAPE A le fournit à partir de l'axiome A4 de l'infini.

  ÉTAPE A — un cardinal INFINI existe :  A4 ⊢ (∃X)¬Fini(Card X) ; comme Card X est un
            cardinal, A4 ⊢ (∃a)( est_cardinal(a) et ¬Fini(a) )       [INCONDITIONNEL]
            (= cardinal_infini_existe).  Le passage X ↦ a=Card X découple le témoin
            de l'ensemble X (évite la collision de noms avec le liant interne de
            est_cardinal).

  ÉTAPE B — Fini DOWNWARD-CLOSED :  (b ≤ c et Fini(c)) ⇒ Fini(b).
            ⚠️ VERROU.  « Un cardinal ≤ un cardinal fini est fini » = la Proposition
            "toute partie d'un ensemble fini est finie" (E.III.4, voisine de Prop. 3),
            qui SANS récurrence (C61 absent) n'est PAS dérivable ici.  REPORTÉ et
            encodé comme HYPOTHÈSE explicite `fini_downward(b,c)` circulant dans C→E.
            Tous les paliers C..E sont CONDITIONNÉS à cette seule hypothèse.

  ÉTAPE C — tout entier n vérifie n ≤ a :  comparabilite(n,a) donne n≤a OU a≤n ;
            si a≤n alors (ÉTAPE B, Fini(n)) ⊢ Fini(a), ce qui CONTREDIT ¬Fini(a)
            (ÉTAPE A) ; donc n≤a (cas + ex falso).        [SOUS l'hypothèse B]

  ÉTAPE D — séparation S8 :  le terme Ncol(a) := { x ∈ [0,a] | Fini(x) } est un
            ensemble (sélection S8 dans l'ensemble EXISTANT [0,a] = intervalle_entiers,
            unicité A1) — exactement le motif de la différence E∖X ou de l'intervalle.
            theorie_ensembles() reste INCHANGÉE = 22 (axiome de Ncol en théorie DÉDIÉE
            theorie_Ncol).  Légitime car [0,a] EXISTE déjà (Remarque III.25).

  ÉTAPE E — N collectivise Fini :  on prouve (∀x)( x ∈ Ncol(a) ⇔ Fini(x) ).
            • ⇐ : Fini(x) ⇒ (x cardinal et 0≤x et x≤a) = x∈[0,a] (D : C+borne 0)
                  donc x∈[0,a] et Fini(x), donc x∈Ncol(a).
            • ⇒ : x∈Ncol(a) ⇒ (x∈[0,a] et Fini(x)) ⇒ Fini(x)  (projection).
            Le TÉMOIN Ncol(a) établit alors coll(x, Fini(x)) = (∃Y)(∀x)(x∈Y ⇔ Fini(x)).
            La collectivisation est ainsi DÉMONTRÉE (équivalence = théorème), JAMAIS
            postulée.

🎯 N_collectivise() ⊢ coll(x, Fini(x))   [SOUS l'hypothèse B universelle].

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  L'unique axiome introduit est
   celui de Ncol (sélection S8 dans [0,a]), dans une théorie DÉDIÉE — JAMAIS la
   collectivisation de Fini elle-même (qui est le THÉORÈME prouvé).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, app, egal, et, ou, non, impl, equiv, appartient, existe, pourtout,
    subst_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, ZERO
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble, est_infini, A4, theorie_infini,
)

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, cas, instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE B (VERROU) — Fini downward-closed, encodée comme HYPOTHÈSE explicite.
# ════════════════════════════════════════════════════════════════════════════
def fini_downward(b, c):
    """Énoncé « Fini est downward-closed pour ≤ » :  (b ≤ c et Fini(c)) ⇒ Fini(b).

    ⚠️ NON PROUVÉ ici (REPORTÉ — Proposition voisine de E.III.4 Prop. 3, exige la
    récurrence C61, absente).  C'est l'HYPOTHÈSE de toute la chaîne C→E.  « Un
    cardinal ≤ un cardinal fini est fini »."""
    return impl(et(inf_egal_card(_t(b), _t(c)), est_fini(_t(c))), est_fini(_t(b)))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE A — un cardinal INFINI existe.
#  On travaille avec le TÉMOIN concret a := Card X, où X est le témoin de A4
#  (binder « X », exigé pour que l'élimination du témoin recolle EXACTEMENT à A4 :
#  le corps de A4, est_infini_ensemble(X)=¬Fini(Card X), est repris littéralement).
#  La SEULE propriété de a utilisée en aval est ¬Fini(a) (= le corps de A4) ; on ne
#  décompose JAMAIS est_infini_ensemble(X), ce qui évite toute collision de noms.
# ════════════════════════════════════════════════════════════════════════════
def cardinal_temoin(X="X"):
    """a := Card X  (le cardinal infini, terme ; X = témoin de A4, binder « X »)."""
    return cardinal(var(X))


def a_infini_sous_temoin(X="X"):
    """⊢ { est_infini_ensemble(X) } ⊢ ¬Fini(Card X).

    ÉTAPE A : sous l'hypothèse « X est infini » (corps de A4), a := Card X vérifie
    ¬Fini(a).  est_infini_ensemble(X) EST littéralement ¬Fini(Card X) (Déf. 1) — c'est
    l'hypothèse elle-même."""
    return N.assume(est_infini_ensemble(var(X)))           # ¬Fini(Card X)


def cardinal_infini_existe(a="a", X="X"):
    """⊢ (∃a)( ¬Fini(a) )   (= il existe un cardinal infini).

    ÉTAPE A — INCONDITIONNEL.  De A4 = (∃X)¬Fini(Card X) (theorie_infini) : sous un
    témoin X, ¬Fini(Card X) (corps de A4) ; on en déduit la forme « propre »
    (¬Fini(a))[a:=Card X] — dont le 1er conjoint de Fini (est_cardinal(Card X)) est
    α-renommé (non capturé), MAIS reste équivalent au conjoint capturé du corps de A4
    (les deux sont VRAIS : Card X est un cardinal).  On témoigne a := Card X dans
    (∃a)¬Fini(a), puis on élimine le témoin X et on applique A4.

    BRIDGE captured⇒uncaptured : Fini_unc(Card X) ⇒ Fini_cap(Card X) (même 2e conjoint
    Card X≠Card X+1, 1er conjoint est_cardinal(Card X) PROUVÉ) ; par contraposée,
    ¬Fini_cap(Card X) ⇒ ¬Fini_unc(Card X)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import composantes_conjonction
    vX = var(X)
    cX = cardinal(vX)                                       # Card X
    va = var(a)
    notfini_a = non(est_fini(va))                          # ¬Fini(a)
    # forme « propre » substituée :  ¬Fini_unc(Card X) = (Card X | a)¬Fini(a)
    target_unc = subst_f(cX, a, notfini_a)                # ¬Fini_unc(Card X)
    fini_unc = target_unc.sous[0]                         # Fini_unc(Card X)
    # corps de A4 = ¬Fini_cap(Card X)
    A4body = est_infini_ensemble(vX)                      # ¬Fini_cap(Card X)
    fini_cap = A4body.sous[0]                             # Fini_cap(Card X)
    c1cap, c2cap = composantes_conjonction(fini_cap)      # est_cardinal_cap(Card X), Card X≠Card X+1
    c1unc, c2unc = composantes_conjonction(fini_unc)      # est_cardinal_unc(Card X), Card X≠Card X+1
    # BRIDGE : Fini_unc ⇒ Fini_cap   (c2cap==c2unc ; c1cap PROUVÉ via card_est_un_cardinal)
    card_cap = card_est_un_cardinal(X, lieur=c1cap.lieur)  # est_cardinal_cap(Card X)  (liant c1cap)
    assert card_cap.conclusion == c1cap, "forme est_cardinal_cap inattendue"
    h_unc = N.assume(fini_unc)                            # Fini_unc(Card X)
    c2_thm = conjonction_elim_droite(h_unc)              # Card X≠Card X+1
    fini_cap_thm = conjonction_intro(card_cap, c2_thm)  # Fini_cap(Card X)   [Fini_unc]
    imp_unc_cap = N.loi_deduction(fini_unc, fini_cap_thm)   # Fini_unc ⇒ Fini_cap
    bridge = contraposition(imp_unc_cap)                  # ¬Fini_cap ⇒ ¬Fini_unc
    # sous le témoin X : A4body=¬Fini_cap ⊢ ¬Fini_unc ⊢ (∃a)¬Fini(a)
    hbody = N.assume(A4body)                              # ¬Fini_cap(Card X)
    notfini_unc = N.modus_ponens(hbody, bridge)          # ¬Fini_unc(Card X) = target_unc
    ex_a = N.modus_ponens(notfini_unc, N.s5(notfini_a, cX, a))   # (∃a)¬Fini(a)  [A4body]
    wit = N.loi_deduction(A4body, ex_a)                  # A4body ⇒ (∃a)¬Fini(a)
    exX = existe_elimination(wit, X)                     # (∃X)A4body ⇒ (∃a)¬Fini(a)
    a4 = N.axiome(theorie_infini(), A4)                  # (∃X)¬Fini(Card X) = A4
    return N.modus_ponens(a4, exX)                       # (∃a)¬Fini(a)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE C — tout entier n vérifie n ≤ a  (par comparabilité + ex falso, sous B)
# ════════════════════════════════════════════════════════════════════════════
def _comparabilite_terme(n, a):
    """⊢ (n ≤ a)  OU  (a ≤ n)   (comparabilité des cardinaux instanciée aux TERMES n, a)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_comparabilite import comparabilite_cardinaux
    th = comparabilite_cardinaux("X", "Y")                   # CLOS, binders X,Y
    th = N.generalisation("X", N.generalisation("Y", th))    # (∀Y∀X)( … )
    th = instancie(th, _t(n))                                # X := n
    th = instancie(th, _t(a))                                # Y := a
    return th                                                # (n≤a) ou (a≤n)


def entier_inf_egal_a(a="a", n="n"):
    """⊢ { ¬Fini(a), fini_downward(a, n), Fini(n) } ⊢  n ≤ a.

    ÉTAPE C : a un cardinal infini (ÉTAPE A).  Par comparabilité, n≤a OU a≤n.
      • si a≤n : fini_downward(a, n) avec Fini(n) ⊢ Fini(a), ce qui CONTREDIT
        ¬Fini(a) — ex falso ⊢ n≤a ;
      • si n≤a : directement.
    Trois hypothèses ouvertes : ¬Fini(a) (A), la downward-closure à (a,n) et Fini(n)."""
    va, vn = _t(a), _t(n)
    le_na = inf_egal_card(vn, va)                            # n ≤ a
    le_an = inf_egal_card(va, vn)                            # a ≤ n

    notfini_a = N.assume(non(est_fini(va)))                  # ¬Fini(a)   [hyp A]
    dwn = N.assume(fini_downward(va, vn))                    # (a≤n et Fini n) ⇒ Fini a   [hyp B]
    hfin_n = N.assume(est_fini(vn))                          # Fini(n)    [hyp]

    comp = _comparabilite_terme(vn, va)                     # (n≤a) ou (a≤n)

    b_left = N.loi_deduction(le_na, N.assume(le_na))        # (n≤a) ⇒ (n≤a)

    h_an = N.assume(le_an)                                   # a≤n
    fini_a = N.modus_ponens(conjonction_intro(h_an, hfin_n), dwn)   # Fini(a)
    absurde = N.modus_ponens(fini_a,
                             N.modus_ponens(notfini_a, N.s2(non(est_fini(va)), le_na)))
    b_right = N.loi_deduction(le_an, absurde)               # (a≤n) ⇒ (n≤a)

    return cas(comp, b_left, b_right)                       # n ≤ a   [hyps A, B, Fini n]


# ════════════════════════════════════════════════════════════════════════════
#  0 ≤ x  pour un cardinal x  (borne inférieure 0, ÉTAPE D auxiliaire)
# ════════════════════════════════════════════════════════════════════════════
def zero_inf_egal_cardinal(x="x", Xw="Xw"):
    """⊢ { est_cardinal(x) } ⊢  0 ≤ x   (= inf_egal_card(ZERO, x)).

    De est_cardinal(x) = (∃X)(x = Card X), on extrait un témoin X ; cardinal_zero_inf_egal(X)
    donne 0 ≤ Card X = ZERO ≤ Card X ; Leibniz réécrit Card X ↦ x (via x = Card X)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_bornes import cardinal_zero_inf_egal
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    vx = _t(x)
    vXw = var(Xw)
    corps = egal(vx, cardinal(vXw))                         # x = Card Xw
    hc = N.assume(corps)
    le0 = cardinal_zero_inf_egal(vXw)                       # 0 ≤ Card Xw
    cardw_eq_x = N.modus_ponens(hc, symetrie(vx, cardinal(vXw)))   # Card Xw = x
    leib = N.s6(cardinal(vXw), vx, "w", inf_egal_card(ZERO, var("w")))
    equ = N.modus_ponens(cardw_eq_x, leib)                 # (0≤Card Xw) ⇔ (0≤x)
    le0_x = N.modus_ponens(le0, equivalence_avant(equ))    # 0 ≤ x   [x=Card Xw]
    wit = N.loi_deduction(corps, le0_x)                    # (x=Card Xw) ⇒ 0≤x
    ex_imp = existe_elimination(wit, Xw)                   # (∃Xw)(x=Card Xw) ⇒ 0≤x
    hcard = N.assume(est_cardinal(vx))                     # (∃X)(x=Card X)  (liant « X »)
    if Xw != "X":
        ren = alpha_existe("X", Xw, egal(vx, cardinal(var("X"))))
        hcard = N.modus_ponens(hcard, equivalence_avant(ren))    # (∃Xw)(x=Card Xw)
    return N.modus_ponens(hcard, ex_imp)                   # 0 ≤ x   [est_cardinal(x)]


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE D — la SÉPARATION Ncol(a) := { x ∈ [0,a] | Fini(x) }  (S8 dans [0,a]).
#  Terme opaque + axiome DÉFINITIONNEL (motif difference / segment_extremite).
#  theorie_ensembles() reste INCHANGÉE = 22.
# ════════════════════════════════════════════════════════════════════════════
def Ncol(a):
    """Ncol(a) := { x ∈ [0,a] | Fini(x) }   (sélection S8 dans l'EXISTANT [0,a])."""
    return app("N_col", _t(a))


def _corps_Ncol(a, x):
    """Corps de Ncol(a) :  x ∈ [0,a]  et  Fini(x)."""
    return et(appartient(_t(x), E.intervalle_entiers(ZERO, _t(a))), est_fini(_t(x)))


def axiome_Ncol(a="a", x="x"):
    """⊢-schéma  (∀a)(∀x)( x ∈ Ncol(a) ⇔ (x ∈ [0,a] et Fini(x)) ).

    Axiome DÉFINITIONNEL de la séparation de Fini DANS l'ensemble EXISTANT [0,a]
    (légitime S8 = sélection dans [0,a], unicité A1) — exactement le motif de la
    différence E∖X = {z∈E | ¬(z∈X)} ou de l'intervalle.  N'altère PAS
    theorie_ensembles() (= 22).  Le test sélecteur est Fini(x) ; le contenant [0,a]
    EXISTE déjà (Remarque III.25)."""
    va, vx = var(a), var(x)
    return pourtout(a, pourtout(x,
        equiv(appartient(vx, Ncol(va)), _corps_Ncol(va, vx))))


def theorie_Ncol(a="a", x="x"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Ncol (E.III.6.1, Théorème 1).

    Schéma identique à theorie_intervalle_entiers / theorie_Inj : l'axiome fait
    référence à l'ordre des cardinaux et à Fini, donc théorie dédiée."""
    return N.Theorie("N-collectivise", [axiome_Ncol(a, x)])


def _inst_Ncol(a, x):
    """⊢ ( x ∈ Ncol(a) ⇔ (x∈[0,a] et Fini(x)) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Ncol(), axiome_Ncol())
    ax = instancie(ax, _t(a))
    ax = instancie(ax, _t(x))
    return ax


def Ncol_membre(a="a", x="x"):
    """⊢ ( x ∈ Ncol(a) ) ⇔ ( x ∈ [0,a] et Fini(x) )."""
    return _inst_Ncol(var(a), var(x))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE D (suite) — Fini(x) ⇒ x ∈ [0,a]   (sous A + B-à-x)
# ════════════════════════════════════════════════════════════════════════════
def _membre_intervalle_0a(a, x):
    """⊢ ( x ∈ [0,a] ) ⇔ ( x cardinal et 0≤x et x≤a )   (axiome d'intervalle, [0,a]).

    Instancie l'axiome d'intervalle (∀a)(∀b)(∀x)(…) directement aux TERMES 0, a, x
    (dans CET ordre — borne inf 0, borne sup a)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        theorie_intervalle_entiers, axiome_intervalle_entiers,
    )
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    ax = instancie(ax, ZERO)                                 # a := 0
    ax = instancie(ax, _t(a))                                # b := a
    ax = instancie(ax, _t(x))                                # x := x
    return ax


def fini_implique_dans_intervalle(a="a", x="x"):
    """⊢ { ¬Fini(a), fini_downward(a,x), Fini(x) } ⊢ x ∈ [0, a].

    ÉTAPE D : sous Fini(x), x est un cardinal (1er conjoint), 0≤x (borne 0,
    zero_inf_egal_cardinal) et x≤a (ÉTAPE C) ; ces trois faits sont exactement le
    corps de x∈[0,a], d'où x∈[0,a] par l'axiome d'intervalle.  On ALIGNE le liant
    interne de est_cardinal(x) sur celui de l'antécédent de l'axiome d'intervalle
    (que l'instanciation b:=a peut α-renommer si a contient des variables liées par
    est_cardinal — ex. a=Card X)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
        composantes_conjonction, antecedent_consequent,
    )
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    va, vx = _t(a), _t(x)
    membre = _membre_intervalle_0a(va, vx)                  # x∈[0,a] ⇔ (card x et 0≤x et x≤a)
    ant, _c = antecedent_consequent(equivalence_arriere(membre).conclusion)
    L, R = composantes_conjonction(ant)                     # L=(card x et 0≤x), R=(x≤a)
    LL, LR = composantes_conjonction(L)                     # LL=card x (liant à matcher), LR=0≤x
    hfin = N.assume(est_fini(vx))                           # Fini(x)
    card_x_std = N.modus_ponens(hfin, fini_implique_cardinal(vx))   # est_cardinal(x)  (liant « X »)
    le0 = _cut(zero_inf_egal_cardinal(vx), est_cardinal(vx), card_x_std)   # 0 ≤ x
    # aligne le 1er conjoint sur LL (liant éventuellement α-renommé)
    card_x = card_x_std
    if card_x.conclusion != LL:
        ren = alpha_existe("X", LL.lieur, egal(vx, cardinal(var("X"))))
        card_x = N.modus_ponens(card_x, equivalence_avant(ren))    # est_cardinal(x) liant LL.lieur
    le_xa = entier_inf_egal_a(va, vx)                       # x ≤ a   [hyps A,B,Fini x]
    corps = conjonction_intro(conjonction_intro(card_x, le0), le_xa)
    return N.modus_ponens(corps, equivalence_arriere(membre))


# ════════════════════════════════════════════════════════════════════════════
#  Alignement-α de Fini(x) sur la forme attendue par un axiome instancié à a=Card X
#  (l'instanciation b:=Card X α-renomme le liant interne « X » de est_cardinal).
# ════════════════════════════════════════════════════════════════════════════
def _fini_aligne(thm_fini, x, cible):
    """De ⊢ est_fini(x) [thm_fini] et une cible α-équivalente `cible` (= Fini(x) avec
    le liant interne de est_cardinal renommé), renvoie ⊢ cible.

    Fini(x) = (est_cardinal(x) et x≠x+1) ; seul le liant interne de est_cardinal(x)
    diffère.  On extrait les deux conjoints, on aligne est_cardinal(x) par renommage-α
    de son existentielle (liant « X » → liant de la cible), et on réassemble."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import composantes_conjonction
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    vx = _t(x)
    if thm_fini.conclusion == cible:
        return thm_fini
    Cc1, Cc2 = composantes_conjonction(cible)             # est_cardinal(x)*, x≠x+1
    card_src = conjonction_elim_gauche(thm_fini)          # est_cardinal(x)  (liant source)
    autre = conjonction_elim_droite(thm_fini)             # x≠x+1
    card_aligne = card_src
    if card_src.conclusion != Cc1:
        src_lieur = card_src.conclusion.lieur             # liant de la source
        # est_cardinal(x) = (∃<lieur>)(x = Card <lieur>) ; renomme source → cible
        ren = alpha_existe(src_lieur, Cc1.lieur,
                           egal(vx, cardinal(var(src_lieur))))
        card_aligne = N.modus_ponens(card_src, equivalence_avant(ren))
    return conjonction_intro(card_aligne, autre)          # cible


def _corps_Ncol_inst(a, x):
    """⊢ ( x∈Ncol(a) ⇔ (x∈[0,a] et Fini(x)) )  +  les deux conjoints attendus (AL, AR).

    Renvoie (ax_ncol, AL, AR) où AL = « x∈[0,a] » et AR = « Fini(x) » DANS LA FORME
    exacte de l'antécédent de l'axiome (AR peut avoir le liant de est_cardinal renommé)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
        composantes_conjonction, antecedent_consequent,
    )
    ax = _inst_Ncol(a, x)
    ant, _c = antecedent_consequent(equivalence_arriere(ax).conclusion)
    AL, AR = composantes_conjonction(ant)
    return ax, AL, AR


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE E — Ncol(a) collectivise Fini :  (∀x)( x∈Ncol(a) ⇔ Fini(x) )
# ════════════════════════════════════════════════════════════════════════════
def Ncol_equivaut_fini(a="a", x="x"):
    """⊢ { ¬Fini(a), (∀x)fini_downward(a,x) } ⊢  (∀x)( x ∈ Ncol(a) ⇔ Fini(x) ).

    ÉTAPE E (cœur) : pour tout x,
      • ⇐ : Fini(x) ⇒ x∈[0,a] (ÉTAPE D) et Fini(x), donc (x∈[0,a] et Fini x),
            donc x∈Ncol(a) (axiome de Ncol) ;
      • ⇒ : x∈Ncol(a) ⇒ (x∈[0,a] et Fini x) ⇒ Fini x (projection droite).
    L'hypothèse downward-closure est prise SOUS forme universelle (∀x)fini_downward
    pour pouvoir l'instancier au x courant — c'est l'unique report (ÉTAPE B)."""
    va, vx = _t(a), _t(x)
    ax_ncol, AL, AR = _corps_Ncol_inst(va, vx)            # ⇔ + conjoints attendus AL, AR

    # ⇐ : Fini(x) ⇒ x∈Ncol(a).  Le corps attendu est (AL et AR) où AR = Fini(x) aligné.
    hfin = N.assume(est_fini(vx))                          # Fini(x)
    dans_interv = fini_implique_dans_intervalle(va, vx)   # x∈[0,a] (= AL)   [hyps A, B-à-x, Fini x]
    fini_AR = _fini_aligne(hfin, vx, AR)                  # Fini(x) dans la forme AR
    corps_ncol = conjonction_intro(dans_interv, fini_AR)  # (AL et AR)
    x_in_ncol = N.modus_ponens(corps_ncol, equivalence_arriere(ax_ncol))  # x∈Ncol(a)
    sens_cg = N.loi_deduction(est_fini(vx), x_in_ncol)    # Fini(x) ⇒ x∈Ncol(a)

    # ⇒ : x∈Ncol(a) ⇒ Fini(x)
    h_in = N.assume(appartient(vx, Ncol(va)))             # x∈Ncol(a)
    corps = N.modus_ponens(h_in, equivalence_avant(ax_ncol))   # (AL et AR)
    fini_AR2 = conjonction_elim_droite(corps)             # AR (= Fini x aligné)
    fini_x = _fini_aligne(fini_AR2, vx, est_fini(vx))     # Fini(x) en forme standard
    sens_gd = N.loi_deduction(appartient(vx, Ncol(va)), fini_x)   # x∈Ncol(a) ⇒ Fini(x)

    equ = conjonction_intro(sens_gd, sens_cg)             # x∈Ncol(a) ⇔ Fini(x)

    # remplace l'hyp ponctuelle fini_downward(a,x) par l'universelle (∀x)fini_downward(a,x)
    dwn_x = fini_downward(va, vx)
    dwn_all = pourtout(x, dwn_x)
    inst = instancie(N.assume(dwn_all), vx)               # fini_downward(a,x)  [hyp ∀]
    equ2 = _cut(equ, dwn_x, inst)                         # ⇔ ; hyps {¬Fini a, (∀x)dwn}
    return N.generalisation(x, equ2)                      # (∀x)(x∈Ncol(a) ⇔ Fini x)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 THÉORÈME 1 — Fini est collectivisante  (sous l'hypothèse B universelle)
# ════════════════════════════════════════════════════════════════════════════
def _coll_fini(x="x"):
    """La formule coll(x, Fini(x)) = (∃Y)(∀x)(x∈Y ⇔ Fini(x))   (liant existentiel « y »)."""
    from bourbaki.logique.i_1_termes_relations.formule import coll
    return coll(x, est_fini(var(x)))


def N_collectivise_sous_cardinal(a="a", x="x", Y="y"):
    """⊢ { ¬Fini(a), (∀x)fini_downward(a, x) } ⊢ coll(x, Fini(x)).

    Sous un cardinal infini a (variable/terme) et l'hypothèse downward-closure :
    Ncol(a) collectivise Fini (Ncol_equivaut_fini), donc il témoigne
    (∃Y)(∀x)(x∈Y ⇔ Fini x) = coll(x, Fini x).  Le binder existentiel Y défaut « y »
    pour matcher coll(x,Fini x) (formule.coll).  Quand a est une variable PROPRE (≠ des
    liants internes de est_cardinal/Fini), aucun α-renommage n'intervient ; l'alignement
    _aligner_pour_tout est un no-op (sécurité si a contient des variables liées)."""
    va, vx = _t(a), var(x)
    equ_all = Ncol_equivaut_fini(va, x)                   # (∀x)(x∈Ncol(a) ⇔ Fini x)  [hyps A,B]
    R = pourtout(x, equiv(appartient(vx, var(Y)), est_fini(vx)))
    s5 = N.s5(R, Ncol(va), Y)                             # (Ncol(a)|Y)R ⇒ (∃Y)R = coll(x,Fini x)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import antecedent_consequent
    ant_s5, _c = antecedent_consequent(s5.conclusion)     # (Ncol(a)|Y)R
    equ_aligne = _aligner_pour_tout(equ_all, ant_s5, x)   # ⊢ ant_s5  (= equ_all aligné α)
    return N.modus_ponens(equ_aligne, s5)                # coll(x, Fini x)   [hyps A, B]


def _aligner_pour_tout(thm_all, cible, x):
    """De ⊢ (∀x)(x∈S ⇔ Fini(x)) [thm_all] et une cible (∀x)(x∈S ⇔ Fini(x)*) α-équivalente
    (Fini ayant son liant interne renommé), renvoie ⊢ cible.

    On instancie thm_all à x, on reconstruit l'équivalence cible à partir des deux sens
    en alignant le membre Fini (via _fini_aligne), puis on re-généralise."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
        antecedent_consequent, conjonction_intro, composantes_conjonction,
    )
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    if thm_all.conclusion == cible:
        return thm_all
    vx = _t(x)
    bndr, corps_cible = _peler_pourtout(cible)            # corps cible : (x∈S ⇔ Fini*)
    inst = instancie(thm_all, vx)                         # x∈S ⇔ Fini   (forme source)
    gd = conjonction_elim_gauche(inst)                    # x∈S ⇒ Fini
    cg = conjonction_elim_droite(inst)                    # Fini ⇒ x∈S
    sS, fini_form = antecedent_consequent(gd.conclusion)  # sS = x∈S, fini_form = Fini (source)
    # corps_cible = (x∈S ⇒ Fini*) et (Fini* ⇒ x∈S) ; on extrait Fini* (cible)
    cible_gd_f, _cible_cg_f = composantes_conjonction(corps_cible)   # formules
    _sS2, fini_cible = antecedent_consequent(cible_gd_f)  # fini_cible = Fini* (cible)
    # sens ⇒ : x∈S ⇒ Fini*
    fini_src_thm = N.modus_ponens(N.assume(sS), gd)       # Fini (source)
    fini_cible_thm = _fini_aligne(fini_src_thm, vx, fini_cible)      # Fini*
    gd2 = N.loi_deduction(sS, fini_cible_thm)            # x∈S ⇒ Fini*
    # sens ⇐ : Fini* ⇒ x∈S
    fini_src2 = _fini_aligne(N.assume(fini_cible), vx, fini_form)    # Fini (source)
    sS_thm = N.modus_ponens(fini_src2, cg)              # x∈S
    cg2 = N.loi_deduction(fini_cible, sS_thm)           # Fini* ⇒ x∈S
    equ2 = conjonction_intro(gd2, cg2)                  # x∈S ⇔ Fini*  (= corps_cible)
    return N.generalisation(bndr, equ2)                 # (∀x)(x∈S ⇔ Fini*) = cible


# @livre Ch.III §6.1 Th.1 | E III.45 L.24-25 | PDF p.148
def N_collectivise(a="a", x="x", Y="y"):
    """🎯 THÉORÈME 1, E.III.6.1 — « Fini(x) est collectivisante ».

    ⊢ { (∀a)(∀x)fini_downward(a, x) } ⊢ coll(x, Fini(x))
      = (∃Y)(∀x)( x ∈ Y ⇔ Fini(x) )   (l'ensemble N des entiers EXISTE).

    SOUS LA SEULE HYPOTHÈSE B (downward-closure de Fini = « un cardinal ≤ un cardinal
    fini est fini », E.III.4, REPORTÉE faute de récurrence C61), prise sous forme
    universelle (∀a)(∀x)fini_downward(a, x).  ÉTAPE A (∃ cardinal infini) est déchargée
    INCONDITIONNELLEMENT par A4 (cardinal_infini_existe) ; C, D, E sont déchargées
    modulo B.  L'unique report est B.

    Assemblage : N_collectivise_sous_cardinal donne coll(x,Fini x) sous ¬Fini(a) et
    (∀x)fini_downward(a, x) [a variable PROPRE] ; la seconde est tirée de B universelle
    instanciée à a.  On décharge ¬Fini(a), puis on élimine le témoin a depuis
    (∃a)¬Fini(a) (= cardinal_infini_existe, A4).  a est PROPRE : non libre dans
    coll(x,Fini x) ni dans l'hypothèse universelle B."""
    va, vx = var(a), var(x)
    # sous-théorème : {¬Fini(a), (∀x)dwn(a,x)} ⊢ coll   (a variable PROPRE)
    sub = N_collectivise_sous_cardinal(a, x, Y)         # hyps : ¬Fini(a), (∀x)dwn(a,x)
    # B universelle (∀a)(∀x)dwn(a,x) → (∀x)dwn(a,x) par instanciation a:=a
    dwn_all_x = pourtout(x, fini_downward(va, vx))       # (∀x)dwn(a,x)
    B_all = pourtout(a, dwn_all_x)                       # (∀a)(∀x)dwn(a,x)
    inst_dwn = instancie(N.assume(B_all), va)            # (∀x)dwn(a,x)   [hyp B]
    sub = _cut(sub, dwn_all_x, inst_dwn)                # coll  [hyps : ¬Fini(a), B]
    # décharge ¬Fini(a) et élimine le témoin a depuis (∃a)¬Fini(a)
    wit = N.loi_deduction(non(est_fini(va)), sub)       # ¬Fini(a) ⇒ coll   [hyp B]
    ex_imp = existe_elimination(wit, a)                 # (∃a)¬Fini(a) ⇒ coll   [hyp B]
    exists_inf = cardinal_infini_existe(a)              # (∃a)¬Fini(a)   (A4, INCONDITIONNEL)
    return N.modus_ponens(exists_inf, ex_imp)           # coll(x, Fini x)   [hyp B]


__all__ = [
    "fini_downward",
    "cardinal_temoin", "a_infini_sous_temoin", "cardinal_infini_existe",
    "entier_inf_egal_a", "zero_inf_egal_cardinal",
    "Ncol", "axiome_Ncol", "theorie_Ncol", "Ncol_membre",
    "fini_implique_dans_intervalle", "Ncol_equivaut_fini",
    "N_collectivise_sous_cardinal", "N_collectivise",
]
