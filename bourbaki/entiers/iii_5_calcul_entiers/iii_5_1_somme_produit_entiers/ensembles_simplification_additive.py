"""§III.5 — SIMPLIFICATION ADDITIVE FINIE (Cor. 3 de la Prop. 3, E.III.37).

🎯 « L'addition par un entier (cardinal fini) est simplifiable / injective » :

    simplification_additive_finie :
        ⊢ est_entier(a) ⇒
            (∀c)(∀c')( ( est_cardinal(c) et est_cardinal(c') et a+c = a+c' ) ⇒ c = c' ).

C'est le résidu honnête qui bloquait l'UNICITÉ de la soustraction des entiers
(`soustraction_unicite`, jusqu'ici sous hypothèse de simplifiabilité) et plusieurs
résultats combinatoires §III.5.

────────────────────────────────────────────────────────────────────────────────
ROUTE — récurrence C61 sur a (`principe_recurrence_preuve`, déjà CLOSE modulo
`predecesseur_fini_universel`, lui-même CLOS par Prop. 2) du prédicat

    P(a) := (∀c)(∀c')( ( est_cardinal(c) et est_cardinal(c') et a+c = a+c' )
                       ⇒ c = c' ).

  • BASE  P(0) :  0+c = Card(∅⊔c)... ; via commutativité a+0=a et 0+c=c (commute +
    a+0=a aux TERMES c) on a 0+c = c et 0+c' = c'.  De 0+c = 0+c' on tire c = c'.
  • PAS  P(a) ⇒ P(a+1) :  (a+1)+c = (a+1)+c'.  Maillon
    `successeur(a)+c = successeur(a+c)` (commute + somme_succ_distribue, sous card c) :
        s(a)+c = c+s(a)            [commute]
               = s(c+a)            [somme_succ_distribue(c,a), card c, card a]
               = s(a+c)            [commute a+c=c+a sous le successeur, Leibniz].
    D'où s(a+c) = s(a+c') ; PROP 8 (successeur injectif) ⇒ Card(a+c) = Card(a+c') ;
    a+c et a+c' sont des Card (cardinal_de_cardinal) ⇒ a+c = a+c' ; l'HYP de
    récurrence P(a) ⇒ c = c'.

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé : C61 déchargé de son unique
   résidu (predecesseur) par sa preuve close ; PROP 8 inconditionnelle ; tous les
   maillons algébriques (commute / somme_succ_distribue / cardinal_de_cardinal) clos.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, pourtout,
)
from bourbaki.logique import noyau_abrege as N

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_entier, successeur, ZERO
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

# ── briques CLOSES réutilisées ────────────────────────────────────────────────
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_succ_distribue
from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_fini2 import (
    prop8_successeur_injectif,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal

# C61 (récurrence sur ℕ) + décharge du résidu prédécesseur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import principe_recurrence
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  Le prédicat d'induction  P(a) := (∀c)(∀c')( (card c et card c' et a+c=a+c') ⇒ c=c' )
# ════════════════════════════════════════════════════════════════════════════
def _P(C="cSA", Cp="cpSA"):
    """P comme fonction Terme → Formule."""
    def P(a):
        va = _t(a)
        vc, vcp = var(C), var(Cp)
        ac = somme_cardinale_binaire(va, vc)
        acp = somme_cardinale_binaire(va, vcp)
        corps = impl(et(et(est_cardinal(vc), est_cardinal(vcp)), egal(ac, acp)),
                     egal(vc, vcp))
        return pourtout(C, pourtout(Cp, corps))
    return P


# ── maillon : Card(a+c) = a+c  (a+c est un cardinal) ──────────────────────────
def _card_somme_eq(va, vc):
    """⊢ Card(a+c) = a+c   (a+c = Card(a⊔c) est un cardinal)."""
    ac = somme_cardinale_binaire(va, vc)                 # = Card(a⊔c)
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
    aXc = somme_disjointe(va, vc)
    is_card = card_est_un_cardinal(aXc, est_cardinal(ac).lieur)   # est_cardinal(a+c), binder aligné
    return N.modus_ponens(is_card, cardinal_de_cardinal(ac))   # Card(a+c) = a+c


# ── maillon : commutativité TERME  a+c = c+a ──────────────────────────────────
def _commute(va, vc):
    """⊢ somme_cardinale_binaire(a, c) = somme_cardinale_binaire(c, a).

    somme_cardinale_binaire(x,y) := Card(x⊔y) ; somme_cardinale_commutative donne
    Card(a⊔c) = Card(c⊔a), ce qui EST a+c = c+a (égalité de termes).

    ⚠️ somme_cardinale_commutative a des liants internes (u,v,z,up du graphe témoin)
    qui CAPTURENT si on lui passe des termes structurés ; on prouve sur des NOMS
    frais, on généralise, puis on instancie aux TERMES (capture-safe)."""
    base = somme_cardinale_commutative("Acom", "Bcom")   # Card(Acom⊔Bcom)=Card(Bcom⊔Acom)
    gen = N.generalisation("Acom", N.generalisation("Bcom", base))
    return instancie(instancie(gen, _t(va)), _t(vc))     # Card(a⊔c) = Card(c⊔a)


def _ssd(vx, vy):
    """⊢ (card x et card y) ⇒ x+(y+1) = (x+y)+1, aux TERMES x,y (capture-safe).

    somme_succ_distribue a des liants internes (graphe d'associativité) qui
    capturent sur des termes structurés ; on prouve sur noms frais, généralise,
    instancie."""
    base = somme_succ_distribue("Assd", "Bssd")
    gen = N.generalisation("Assd", N.generalisation("Bssd", base))
    return instancie(instancie(gen, _t(vx)), _t(vy))


# ── maillon : successeur(a)+c = successeur(a+c)  (sous card a, card c) ─────────
def _succ_somme(va, vc):
    """⊢ ( est_cardinal a et est_cardinal c ) ⇒
         somme_cardinale_binaire(successeur a, c) = successeur(somme_cardinale_binaire(a, c)).

    s(a)+c = c+s(a) [commute] = s(c+a) [somme_succ_distribue(c,a)] = s(a+c) [commute, Leibniz]."""
    sa = successeur(va)
    sa_c = somme_cardinale_binaire(sa, vc)               # s(a)+c
    c_sa = somme_cardinale_binaire(vc, sa)               # c+s(a)
    ca = somme_cardinale_binaire(vc, va)                 # c+a
    ac = somme_cardinale_binaire(va, vc)                 # a+c

    h = N.assume(et(est_cardinal(va), est_cardinal(vc)))
    card_a = conjonction_elim_gauche(h)
    card_c = conjonction_elim_droite(h)

    # (1) s(a)+c = c+s(a)
    eq1 = _commute(sa, vc)                               # s(a)+c = c+s(a)

    # (2) c+s(a) = s(c+a)   via somme_succ_distribue(c, a) sous (card c et card a)
    ssd = _ssd(vc, va)                                  # (card c et card a) ⇒ c+s(a) = s(c+a)
    eq2 = N.modus_ponens(conjonction_intro(card_c, card_a), ssd)   # c+s(a) = s(c+a)

    # (3) s(c+a) = s(a+c)   :  c+a = a+c (commute) ⇒ Leibniz sous successeur(·)
    ca_eq_ac = _commute(vc, va)                          # c+a = a+c
    leib = N.s6(ca, ac, "wsa", egal(successeur(ca), successeur(var("wsa"))))  # (c+a=a+c)⇒(s(c+a)=s(c+a)⇔s(c+a)=s(a+c))
    # plus simple : congruence du terme successeur via s6 sur (successeur w)
    leib2 = N.modus_ponens(ca_eq_ac, N.s6(ca, ac, "wsa2", egal(successeur(var("wsa2")), successeur(ac))))
    # leib2 : (s(c+a)=s(a+c)) ⇔ (s(a+c)=s(a+c)) ; on prend la flèche arrière depuis la réflexivité
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    refl_sac = N.reflexivite(successeur(ac))             # s(a+c)=s(a+c)
    eq3 = N.modus_ponens(refl_sac, equivalence_arriere(leib2))   # s(c+a) = s(a+c)

    chain = composer_egalites(eq1, eq2)                  # s(a)+c = s(c+a)
    final = composer_egalites(chain, eq3)                # s(a)+c = s(a+c)
    return N.loi_deduction(et(est_cardinal(va), est_cardinal(vc)), final)


# ════════════════════════════════════════════════════════════════════════════
#  BASE  P(0)
# ════════════════════════════════════════════════════════════════════════════
def _preuve_P0(C="cSA", Cp="cpSA"):
    """⊢ P(0).   (0+c = c et 0+c' = c' ; de 0+c=0+c' on tire c=c'.)"""
    P = _P(C, Cp)
    vc, vcp = var(C), var(Cp)
    zc = somme_cardinale_binaire(ZERO, vc)               # 0+c
    zcp = somme_cardinale_binaire(ZERO, vcp)             # 0+c'

    h = N.assume(et(et(est_cardinal(vc), est_cardinal(vcp)), egal(zc, zcp)))
    card_c = conjonction_elim_gauche(conjonction_elim_gauche(h))
    card_cp = conjonction_elim_droite(conjonction_elim_gauche(h))
    h_eq = conjonction_elim_droite(h)                    # 0+c = 0+c'

    # 0+c = c   :  0+c = c+0 [commute] = c [somme_cardinale_zero_neutre via a+0=a]
    zc_eq_c = _zero_plus(vc, card_c)                     # 0+c = c
    zcp_eq_cp = _zero_plus(vcp, card_cp)                 # 0+c' = c'

    # c = 0+c = 0+c' = c'
    c_eq_zc = N.modus_ponens(zc_eq_c, symetrie(zc, vc))  # c = 0+c
    c_eq_zcp = composer_egalites(c_eq_zc, h_eq)          # c = 0+c'
    c_eq_cp = composer_egalites(c_eq_zcp, zcp_eq_cp)     # c = c'

    corps = N.loi_deduction(et(et(est_cardinal(vc), est_cardinal(vcp)), egal(zc, zcp)), c_eq_cp)
    res = N.generalisation(C, N.generalisation(Cp, corps))
    assert res.conclusion == P(ZERO), "P(0) mal formé"
    return res


def _zero_plus(vc, card_c):
    """{ est_cardinal c } ⊢ somme_cardinale_binaire(0, c) = c.   (0+c = c.)

    0+c = c+0 [commute] ; c+0 = c [somme_cardinale_zero_neutre symétrisé : a+0=a]."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import (
        somme_cardinale_zero_neutre,
    )
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
    from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
    zc = somme_cardinale_binaire(ZERO, vc)               # 0+c = Card(∅⊔c)
    c0 = somme_cardinale_binaire(vc, ZERO)               # c+0 = Card(c⊔∅)... mais 0=Card∅

    # commute : 0+c = c+0   (Card(0⊔c) = Card(c⊔0)) ; 0 = Card∅ (DÉF ZERO)
    eq_comm = _commute(ZERO, vc)                          # 0+c = c+0

    # c+0 = c  : somme_cardinale_zero_neutre donne Card(∅⊔c)=Card c ; mais ici on veut c+0=c.
    #  somme_zero_neutre_droite(c) : est_cardinal c ⇒ somme_cardinale_binaire(c,0) = c
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_zero_neutre_droite
    szd_base = somme_zero_neutre_droite("Aszn")           # est_cardinal A ⇒ A+0 = A
    szd = instancie(N.generalisation("Aszn", szd_base), vc)  # est_cardinal c ⇒ c+0 = c
    c0_eq_c = N.modus_ponens(card_c, szd)                 # c+0 = c

    return composer_egalites(eq_comm, c0_eq_c)            # 0+c = c


# ════════════════════════════════════════════════════════════════════════════
#  PAS  P(a) ⇒ P(a+1)
# ════════════════════════════════════════════════════════════════════════════
def _preuve_step(C="cSA", Cp="cpSA", a="aSA"):
    """⊢ (∀a)( ( Fini a et P(a) ) ⇒ P(a+1) ).

    Forme EXACTE exigée par principe_recurrence (le « pas »)."""
    P = _P(C, Cp)
    va = var(a)
    vc, vcp = var(C), var(Cp)
    sa = successeur(va)
    ac = somme_cardinale_binaire(va, vc)                 # a+c
    acp = somme_cardinale_binaire(va, vcp)               # a+c'
    sac = somme_cardinale_binaire(sa, vc)                # (a+1)+c
    sacp = somme_cardinale_binaire(sa, vcp)              # (a+1)+c'

    h = N.assume(et(est_fini(va), P(va)))
    fini_a = conjonction_elim_gauche(h)
    Pa = conjonction_elim_droite(h)                      # P(a)
    card_a = conjonction_elim_gauche(fini_a)             # est_cardinal a

    # Q(a+1) : fixe c, c', assume (card c et card c' et (a+1)+c = (a+1)+c')
    h_in = N.assume(et(et(est_cardinal(vc), est_cardinal(vcp)), egal(sac, sacp)))
    card_c = conjonction_elim_gauche(conjonction_elim_gauche(h_in))
    card_cp = conjonction_elim_droite(conjonction_elim_gauche(h_in))
    h_eq = conjonction_elim_droite(h_in)                 # (a+1)+c = (a+1)+c'

    # s(a)+c = s(a+c)   et   s(a)+c' = s(a+c')
    succ_c = N.modus_ponens(conjonction_intro(card_a, card_c), _succ_somme(va, vc))   # s(a)+c = s(a+c)
    succ_cp = N.modus_ponens(conjonction_intro(card_a, card_cp), _succ_somme(va, vcp))  # s(a)+c' = s(a+c')

    # s(a+c) = s(a)+c = s(a)+c' = s(a+c')
    sac_eq_sa_c = N.modus_ponens(succ_c, symetrie(sac, successeur(ac)))   # s(a+c) = s(a)+c
    sac_eq_sacp = composer_egalites(sac_eq_sa_c, h_eq)                    # s(a+c) = s(a)+c'
    sumc_eq = composer_egalites(sac_eq_sacp, succ_cp)                     # s(a+c) = s(a+c')

    # PROP 8 (successeur injectif) instanciée aux TERMES a+c, a+c'
    p8 = prop8_successeur_injectif("A", "B")                              # (succ A=succ B)⇒(Card A=Card B) CLOS
    p8_gen = N.generalisation("A", N.generalisation("B", p8))
    p8_inst = instancie(instancie(p8_gen, ac), acp)                      # (s(a+c)=s(a+c'))⇒(Card(a+c)=Card(a+c'))
    card_eq = N.modus_ponens(sumc_eq, p8_inst)                           # Card(a+c) = Card(a+c')

    # a+c = Card(a+c) = Card(a+c') = a+c'
    card_ac_eq = _card_somme_eq(va, vc)                                  # Card(a+c) = a+c
    card_acp_eq = _card_somme_eq(va, vcp)                                # Card(a+c') = a+c'
    ac_eq_card = N.modus_ponens(card_ac_eq, symetrie(cardinal_terme(ac), ac))  # a+c = Card(a+c)
    ac_eq_cardacp = composer_egalites(ac_eq_card, card_eq)              # a+c = Card(a+c')
    ac_eq_acp = composer_egalites(ac_eq_cardacp, card_acp_eq)          # a+c = a+c'

    # P(a) à (c, c') :  (card c et card c' et a+c=a+c') ⇒ c=c'
    Pa_cc = instancie(instancie(Pa, vc), vcp)                           # (card c et card c' et a+c=a+c')⇒c=c'
    c_eq_cp = N.modus_ponens(conjonction_intro(conjonction_intro(card_c, card_cp), ac_eq_acp), Pa_cc)

    corps_in = N.loi_deduction(et(et(est_cardinal(vc), est_cardinal(vcp)), egal(sac, sacp)), c_eq_cp)
    Pa1 = N.generalisation(C, N.generalisation(Cp, corps_in))           # P(a+1)
    assert Pa1.conclusion == P(sa), "P(a+1) mal formé"

    corps_step = N.loi_deduction(et(est_fini(va), P(va)), Pa1)
    return N.generalisation(a, corps_step)


def cardinal_terme(t):
    return cardinal(t)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 SIMPLIFICATION ADDITIVE FINIE
# ════════════════════════════════════════════════════════════════════════════
def simplification_additive_finie_enonce(a="aSA", C="cSA", Cp="cpSA"):
    """Énoncé :  est_entier(a) ⇒ (∀c)(∀c')( (card c et card c' et a+c=a+c') ⇒ c=c' )."""
    P = _P(C, Cp)
    va = _t(a)
    return impl(est_entier(va), P(va))


def simplification_additive_finie(a="aSA", C="cSA", Cp="cpSA", k="kpredSA"):
    """🎯🎯 ⊢ est_entier(a) ⇒ (∀c)(∀c')( (card c et card c' et a+c=a+c') ⇒ c=c' ).
       (THÉORÈME CLOS, 0 hyp — la simplifiabilité additive des entiers, Cor. 3 §III.5.)

    Récurrence C61 sur a (cf. module) : P(0) (base, 0+c=c) et le pas P(a)⇒P(a+1)
    (PROP 8 successeur injectif + commute + somme_succ_distribue) ; C61
    (principe_recurrence_preuve, résidu predecesseur DÉCHARGÉ par Prop. 2) donne
    (∀a)(Fini a ⇒ P(a)), instancié à a.  theorie=22, 0 hyp."""
    P = _P(C, Cp)
    va = _t(a)

    p0 = _preuve_P0(C, Cp)                                # P(0)
    step = _preuve_step(C, Cp, a)                         # (∀a)((Fini a et P(a)) ⇒ P(a+1))

    # C61 : principe_recurrence(P, a)  déchargé de predecesseur_fini_universel
    princ_imp = principe_recurrence_preuve(P, a, k=k)     # {pfu} ⊢ (P(0) et step) ⇒ (∀a)(Fini a ⇒ P a)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent (forme ?)"
    preuve_pfu = predecesseur_fini_universel_preuve(k=k)  # ⊢ pfu (CLOS)
    princ_imp = _cut(princ_imp, pfu, preuve_pfu)          # (P(0) et step) ⇒ (∀a)(Fini a ⇒ P a)  [0 résidu]

    ante = conjonction_intro(p0, step)                    # P(0) et step
    fini_implique_Pa = N.modus_ponens(ante, princ_imp)    # (∀a)(Fini a ⇒ P(a))

    # instancie à a  :  Fini a ⇒ P(a)  =  est_entier a ⇒ P(a)
    inst = instancie(fini_implique_Pa, va)                # Fini a ⇒ P(a)
    # est_entier(a) == est_fini(a) ; conclusion alignée
    assert inst.conclusion == impl(est_fini(va), P(va))
    res = inst
    assert res.conclusion == simplification_additive_finie_enonce(a, C, Cp), \
        "conclusion ≠ énoncé attendu"
    assert res.est_clos and not res.hypotheses, "simplification_additive_finie : non close !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 UNICITÉ DE LA SOUSTRACTION DES ENTIERS — résidu DÉCHARGÉ
# ════════════════════════════════════════════════════════════════════════════
def soustraction_unicite_close_enonce(a="aSU", c="cSU", cp="cpSU", b="bSU"):
    """Énoncé :  ( est_entier(a) et card c et card c' et a+c=b et a+c'=b ) ⇒ c=c'."""
    va, vc, vcp, vb = _t(a), _t(c), _t(cp), _t(b)
    ac = somme_cardinale_binaire(va, vc)
    acp = somme_cardinale_binaire(va, vcp)
    ante = et(et(et(et(est_entier(va), est_cardinal(vc)), est_cardinal(vcp)),
                 egal(ac, vb)), egal(acp, vb))
    return impl(ante, egal(vc, vcp))


def soustraction_unicite_close(a="aSU", c="cSU", cp="cpSU", b="bSU", k="kpredSU"):
    """🎯 ⊢ ( est_entier(a) et card c et card c' et a+c=b et a+c'=b ) ⇒ c=c'.
       (CLOS, 0 hyp — l'UNICITÉ de la différence des entiers, Cor. 4 §III.5, résidu
       de simplifiabilité DÉCHARGÉ par `simplification_additive_finie`.)

    a+c=b et a+c'=b ⇒ a+c=a+c' (transitivité via b) ; simplification_additive_finie(a)
    instanciée à (c,c') donne (card c et card c' et a+c=a+c') ⇒ c=c' ; MP ⇒ c=c'."""
    va, vc, vcp, vb = _t(a), _t(c), _t(cp), _t(b)
    ac = somme_cardinale_binaire(va, vc)
    acp = somme_cardinale_binaire(va, vcp)

    ante = et(et(et(et(est_entier(va), est_cardinal(vc)), est_cardinal(vcp)),
                 egal(ac, vb)), egal(acp, vb))
    h = N.assume(ante)
    h_ent = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(
                conjonction_elim_gauche(h))))                 # est_entier a
    h_cc = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(
                conjonction_elim_gauche(h))))                 # card c
    h_ccp = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # card c'
    h_ac_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # a+c = b
    h_acp_b = conjonction_elim_droite(h)                          # a+c' = b

    # a+c = a+c'  :  a+c = b = a+c'
    b_eq_acp = N.modus_ponens(h_acp_b, symetrie(acp, vb))         # b = a+c'
    ac_eq_acp = composer_egalites(h_ac_b, b_eq_acp)              # a+c = a+c'

    # simplification_additive_finie(a) : est_entier a ⇒ (∀c)(∀c')(... ⇒ c=c')
    saf = simplification_additive_finie(a="aSAFu", k=k)          # CLOS : est_entier(aSAFu) ⇒ P(aSAFu)
    saf_a = instancie(N.generalisation("aSAFu", saf), va)        # est_entier a ⇒ P(a)
    safa = N.modus_ponens(h_ent, saf_a)                          # (∀c)(∀c')(...⇒c=c')  [ante]
    Pa_cc = instancie(instancie(safa, vc), vcp)                 # (card c et card c' et a+c=a+c') ⇒ c=c'
    c_eq_cp = N.modus_ponens(conjonction_intro(conjonction_intro(h_cc, h_ccp), ac_eq_acp), Pa_cc)

    res = N.loi_deduction(ante, c_eq_cp)
    assert res.conclusion == soustraction_unicite_close_enonce(a, c, cp, b), \
        "soustraction_unicite_close : conclusion ≠ énoncé attendu"
    assert res.est_clos and not res.hypotheses, "soustraction_unicite_close : non close !"
    return res


__all__ = [
    "simplification_additive_finie", "simplification_additive_finie_enonce",
    "soustraction_unicite_close", "soustraction_unicite_close_enonce",
]
