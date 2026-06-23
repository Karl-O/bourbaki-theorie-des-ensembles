"""§III.5 — PRINCIPE DE RÉCURRENCE SUR LES ENSEMBLES FINIS.

🎯 Le keystone de la combinatoire §III.5 : pour prouver une propriété P de TOUT
ensemble FINI, il suffit de prouver P(∅) et le pas « P(X) ⇒ P(X∪{x}) ».

    recurrence_finie(P) :=
        ( P(∅)  et  (∀X)(∀x)( ( est_fini_ensemble(X) et ¬(x∈X) et P(X) )
                              ⇒ P(X∪{x}) ) )
        ⇒ (∀X)( est_fini_ensemble(X) ⇒ P(X) ).

────────────────────────────────────────────────────────────────────────────────
ROUTE — récurrence sur n = Card(X) via C61 (`principe_recurrence_preuve`, récurrence
sur ℕ, déjà CLOSE modulo `predecesseur_fini_universel`, lui-même CLOS par Prop. 2 —
`predecesseur_fini_universel_preuve`) + la chirurgie « retrait+adjonction d'un point »
(`card_egal_succ_card_diff`, `eq_retire_ajoute`).

  On pose  Q(n) := (∀X)( est_fini_ensemble(X) et Card(X) = n ⇒ P(X) ).
  • Q(0)        : Card X = 0 = Card∅ ⇒ X = ∅ (cardinal_egal_zero_ssi_vide) ; P(∅)
                  (hyp) ⇒ P(X) (Leibniz X↦∅).
  • Q(n)⇒Q(n+1) : X fini, Card X = n+1 ≠ 0 ⇒ X non vide ⇒ (∃x0∈X) ; Y := X∖{x0} ;
                  Card X = successeur(Card Y) (card_egal_succ_card_diff) = successeur(n)
                  ⇒ (Prop. 8, successeur injectif) Card Y = n ; Y fini (Card Y = n,
                  Fini n) ; Q(n) ⇒ P(Y) ; x0∉Y ; le pas ⇒ P(Y∪{x0}) ; X = Y∪{x0}
                  ⇒ P(X).
  C61 ⇒ (∀n)(Fini n ⇒ Q(n)).  Pour X fini, n := Card X est Fini (= est_fini_ensemble X)
  et Card X = Card X, d'où Q(Card X) ⇒ P(X).

⚠️ INVARIANT : theorie_ensembles() = 22.  Aucun postulat ; `predecesseur_fini_universel`
  est DÉCHARGÉ par sa preuve close (Prop. 2 §III.5).  recurrence_finie est CLOS (0 hyp).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, est_fini_ensemble, successeur, ZERO,
)

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

# ── briques CLOSES réutilisées ────────────────────────────────────────────────
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    principe_recurrence, _fini_et_P_implique_succ, _fini_implique_P,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve, singleton_inclus,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import card_egal_succ_card_diff
from bourbaki.cardinaux.arithmetique.ensembles_prop8_fini2 import (
    prop8_successeur_injectif,
)
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_prop7 import (
    cardinal_egal_zero_ssi_vide,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import (
    partie_reunion_complement,
)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import commutativite_reunion
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, card_est_un_cardinal,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import card_egal_succ_card_diff as _ces
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _comm_reunion_t(ta, tb):
    """⊢ (A∪B) = (B∪A)  pour des TERMES A, B (commutativité de ∪, version terme)."""
    gen = N.generalisation("ca", N.generalisation("cb", commutativite_reunion("ca", "cb")))
    return instancie(instancie(gen, _t(ta)), _t(tb))


# ════════════════════════════════════════════════════════════════════════════
#  Le pas (énoncé) sur les ENSEMBLES finis.
# ════════════════════════════════════════════════════════════════════════════
def _pas_ensemble(P, X="Xrec", x="xrec"):
    """(∀X)(∀x)( ( est_fini_ensemble(X) et ¬(x∈X) et P(X) ) ⇒ P(X∪{x}) )."""
    vX, vx = var(X), var(x)
    Xux = E.reunion(vX, E.singleton(vx))
    corps = impl(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)),
                 P(Xux))
    return pourtout(X, pourtout(x, corps))


def recurrence_finie_enonce(P, X="Xrec", x="xrec"):
    """Énoncé du principe de récurrence sur les ensembles finis (cf. module)."""
    vX = var(X)
    return impl(et(P(E.VIDE), _pas_ensemble(P, X, x)),
                pourtout(X, impl(est_fini_ensemble(vX), P(vX))))


# ════════════════════════════════════════════════════════════════════════════
#  Q(n) := (∀X)( est_fini_ensemble(X) et Card(X) = n ⇒ P(X) )
# ════════════════════════════════════════════════════════════════════════════
def _Q(P, X="XQ"):
    """Le prédicat d'induction Q comme fonction Terme → Formule :
        Q(n) := (∀X)( est_fini_ensemble(X) et Card(X) = n ⇒ P(X) )."""
    def Q(n):
        vX = var(X)
        return pourtout(X, impl(et(est_fini_ensemble(vX), egal(cardinal(vX), _t(n))),
                                P(vX)))
    return Q


# ════════════════════════════════════════════════════════════════════════════
#  Q(0) — sous l'hypothèse P(∅).
# ════════════════════════════════════════════════════════════════════════════
def _preuve_Q0(P, hP0, X="XQ"):
    """{ P(∅) [hP0] } ⊢ Q(0).

    Pour X fini avec Card X = 0 = Card∅ : cardinal_egal_zero_ssi_vide ⇒ X = ∅ ;
    Leibniz X↦∅ (via ∅ = X) transporte P(∅) en P(X)."""
    Q = _Q(P, X)
    vX = var(X)
    h = N.assume(et(est_fini_ensemble(vX), egal(cardinal(vX), ZERO)))   # Fini-ens X et Card X = 0
    card_eq_0 = conjonction_elim_droite(h)                  # Card X = 0 = Card∅  (ZERO == Card∅)
    # Card X = Card∅ ⇒ X = ∅
    x_eq_vide = N.modus_ponens(card_eq_0,
        equivalence_avant(cardinal_egal_zero_ssi_vide(X)))  # X = ∅
    vide_eq_x = N.modus_ponens(x_eq_vide, symetrie(vX, E.VIDE))   # ∅ = X
    leib = N.s6(E.VIDE, vX, "wq0", P(var("wq0")))           # (∅ = X) ⇒ (P(∅) ⇔ P(X))
    eqv = N.modus_ponens(vide_eq_x, leib)                   # P(∅) ⇔ P(X)
    pX = N.modus_ponens(hP0, equivalence_avant(eqv))        # P(X)   [P(∅)]
    corps = N.loi_deduction(et(est_fini_ensemble(vX), egal(cardinal(vX), ZERO)), pX)
    res = N.generalisation(X, corps)                        # Q(0)
    assert res.conclusion == Q(ZERO), "Q(0) mal formé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  Helpers chirurgicaux pour le pas.
# ════════════════════════════════════════════════════════════════════════════
def _x0_non_dans_diff(X, x0):
    """⊢ ¬( x0 ∈ X∖{x0} ).   (x0 retiré n'est plus dans le complément.)

    z∈X∖{x0} ⇔ (z∈X et ¬(z∈{x0})) (AXIOME_DIFF) ; à z:=x0 : x0∈X∖{x0} ⇒ ¬(x0∈{x0}),
    or x0∈{x0} (singleton_membre + réflexivité x0=x0) ⇒ contradiction."""
    vX, vx0 = _t(X), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vX, sing)
    # axiome diff instancié à (X, {x0}, x0)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    ax = instancie(instancie(instancie(ax, vX), sing), vx0)   # x0∈X∖{x0} ⇔ (x0∈X et ¬(x0∈{x0}))
    h = N.assume(appartient(vx0, D))                          # x0 ∈ X∖{x0}
    corps = N.modus_ponens(h, equivalence_avant(ax))          # x0∈X et ¬(x0∈{x0})
    nx0_in_sing = conjonction_elim_droite(corps)              # ¬(x0∈{x0})
    # x0 ∈ {x0}  :  x0=x0 ⇒ x0∈{x0}  (singleton_membre arrière)
    x0_eq = N.reflexivite(vx0)                               # x0 = x0
    x0_in_sing = N.modus_ponens(x0_eq, equivalence_arriere(singleton_membre(vx0, vx0)))  # x0∈{x0}
    # contradiction : ¬(x0∈{x0}) et x0∈{x0}  ⇒  ¬(x0∈X∖{x0})
    falso = N.modus_ponens(x0_in_sing,
        N.modus_ponens(nx0_in_sing, N.s2(non(appartient(vx0, sing)), non(appartient(vx0, D)))))
    # falso : ¬(x0∈X∖{x0})  sous hyp h (x0∈X∖{x0})  ⇒  (x0∈D)⇒¬(x0∈D)  ⇒  ¬(x0∈D)
    imp = N.loi_deduction(appartient(vx0, D), falso)          # (x0∈D) ⇒ ¬(x0∈D)
    return N.modus_ponens(imp, N.s1(non(appartient(vx0, D))))  # ¬(x0 ∈ X∖{x0})


def _X_egal_diff_union_singleton(X, x0):
    """⊢ ( x0 ∈ X ) ⇒ ( (X∖{x0}) ∪ {x0} = X ).

    {x0}⊂X (singleton_inclus) ⇒ {x0}∪(X∖{x0}) = X (partie_reunion_complement) ;
    commutativité ∪ ⇒ (X∖{x0})∪{x0} = X."""
    vX, vx0 = _t(X), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vX, sing)
    h = N.assume(appartient(vx0, vX))                         # x0 ∈ X
    sub = N.modus_ponens(h, singleton_inclus(vx0, vX))        # {x0} ⊂ X
    prc = partie_reunion_complement(vX, sing)                 # ({x0}⊂X) ⇒ ({x0}∪(X∖{x0}) = X)
    sing_uD_eq_X = N.modus_ponens(sub, prc)                   # {x0}∪(X∖{x0}) = X
    comm = _comm_reunion_t(D, sing)                           # (X∖{x0})∪{x0} = {x0}∪(X∖{x0})
    res = composer_egalites(comm, sing_uD_eq_X)               # (X∖{x0})∪{x0} = X
    return N.loi_deduction(appartient(vx0, vX), res)


# ════════════════════════════════════════════════════════════════════════════
#  Le pas Q(n) ⇒ Q(n+1) — sous l'hypothèse _pas_ensemble(P).
# ════════════════════════════════════════════════════════════════════════════
def _preuve_step(P, hPas, n="nrec", X="XQ", x0="x0rec"):
    """{ _pas_ensemble(P) [hPas] } ⊢ (∀n)( (Fini n et Q(n)) ⇒ Q(n+1) ).

    hPas : preuve de _pas_ensemble(P) (le pas ensembliste, hyp de recurrence_finie).
    Pour n fixé, sous (Fini n et Q(n)), on prouve Q(n+1)."""
    Q = _Q(P, X)
    vn = var(n)
    vX = var(X)
    vx0 = var(x0)
    sing0 = E.singleton(vx0)
    Y = E.difference(vX, sing0)                               # Y = X∖{x0}
    cY = cardinal(Y)
    succ_n = successeur(vn)

    # hyp (Fini n et Q(n))
    h_conj = N.assume(et(est_fini(vn), Q(vn)))
    h_fini_n = conjonction_elim_gauche(h_conj)                # Fini n
    h_Qn = conjonction_elim_droite(h_conj)                    # Q(n)
    card_n = conjonction_elim_gauche(h_fini_n)                # est_cardinal(n)

    # Q(n+1) : fixe X, assume (Fini-ens X et Card X = n+1)
    h_X = N.assume(et(est_fini_ensemble(vX), egal(cardinal(vX), succ_n)))
    fini_ens_X = conjonction_elim_gauche(h_X)                 # est_fini_ensemble X
    cardX_eq = conjonction_elim_droite(h_X)                   # Card X = successeur(n)

    # ── X non vide : Card X = succ(n) ≠ 0 = Card∅ ⇒ ¬(X = ∅) ⇒ (∃z)(z∈X) ──────────
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import successeur_non_nul
    snn = successeur_non_nul(vn)                              # ¬(successeur(n) = 0)
    # Card X = succ n ⇒ ¬(Card X = 0) (Leibniz succ n ↦ Card X)
    cardX_eq_sym = N.modus_ponens(cardX_eq, symetrie(cardinal(vX), succ_n))  # succ n = Card X
    leib_ne = N.s6(succ_n, cardinal(vX), "wne", non(egal(var("wne"), ZERO)))  # (succ n=Card X)⇒(¬(succ n=0)⇔¬(Card X=0))
    eqv_ne = N.modus_ponens(cardX_eq_sym, leib_ne)
    cardX_ne_0 = N.modus_ponens(snn, equivalence_avant(eqv_ne))   # ¬(Card X = 0) = ¬(Card X = Card∅)
    # ¬(Card X = Card∅) ⇒ ¬(X = ∅)  (contraposée de (X=∅)⇒(Card X=Card∅))
    ez = cardinal_egal_zero_ssi_vide(X)                       # (Card X = Card∅) ⇔ (X = ∅)
    X_ne_vide = N.modus_ponens(cardX_ne_0, contraposition(equivalence_arriere(ez)))  # ¬(X=∅)
    ex_z = N.modus_ponens(X_ne_vide, equivalence_avant(non_vide_ssi_element(vX)))  # (∃z)(z∈X)

    # ── per témoin x0 ∈ X : on dérive P(X) ──────────────────────────────────────
    h_x0 = N.assume(appartient(vx0, vX))                      # x0 ∈ X

    # Card X = successeur(Card Y)
    cardX_eq_succY = N.modus_ponens(h_x0, card_egal_succ_card_diff(vX, vx0))  # Card X = succ(Card Y)
    # successeur(n) = successeur(Card Y)
    succn_eq_succY = composer_egalites(
        N.modus_ponens(cardX_eq, symetrie(cardinal(vX), succ_n)),   # succ n = Card X
        cardX_eq_succY)                                        # succ n = succ(Card Y)
    # Prop 8 : Card n = Card(Card Y)  (généralisé puis instancié aux TERMES — capture-safe)
    p8_base = prop8_successeur_injectif("A", "B")             # (succ A=succ B) ⇒ (Card A=Card B)  CLOS (noms)
    p8_gen = N.generalisation("A", N.generalisation("B", p8_base))
    p8 = instancie(instancie(p8_gen, vn), cY)                 # (succ n = succ(Card Y)) ⇒ (Card n = Card(Card Y))
    cardn_eq_ccY = N.modus_ponens(succn_eq_succY, p8)         # Card n = Card(Card Y)
    # Card n = n  (cardinal_de_cardinal, sous est_cardinal(n))
    cardn_eq_n = N.modus_ponens(card_n, cardinal_de_cardinal(vn))   # Card n = n
    # Card(Card Y) = Card Y  (cardinal_de_cardinal, sous est_cardinal(Card Y) = card_est_un_cardinal)
    card_cY = card_est_un_cardinal(Y, est_cardinal(cY).lieur)     # est_cardinal(Card Y)
    ccY_eq_cY = N.modus_ponens(card_cY, cardinal_de_cardinal(cY))  # Card(Card Y) = Card Y
    # n = Card n = Card(Card Y) = Card Y
    n_eq_cardn2 = N.modus_ponens(cardn_eq_n, symetrie(cardinal(vn), vn))  # n = Card n
    chain = composer_egalites(n_eq_cardn2, cardn_eq_ccY)      # n = Card(Card Y)
    n_eq_cY = composer_egalites(chain, ccY_eq_cY)             # n = Card Y
    cY_eq_n = N.modus_ponens(n_eq_cY, symetrie(vn, cY))       # Card Y = n

    # ── Y fini : est_fini_ensemble Y = Fini(Card Y) ; Card Y = n, Fini n ⇒ Fini(Card Y)
    # Leibniz n ↦ Card Y (via n = Card Y)
    leib_fini = N.s6(vn, cY, "wf", est_fini(var("wf")))       # (n = Card Y) ⇒ (Fini n ⇔ Fini(Card Y))
    eqv_fini = N.modus_ponens(n_eq_cY, leib_fini)
    fini_cY = N.modus_ponens(h_fini_n, equivalence_avant(eqv_fini))   # Fini(Card Y) = est_fini_ensemble Y
    fini_ens_Y = fini_cY                                      # est_fini_ensemble Y  (= est_fini(Card Y))

    # ── Q(n) à Y : (est_fini_ensemble Y et Card Y = n) ⇒ P(Y) ───────────────────
    Qn_Y = instancie(h_Qn, Y)                                 # (Fini-ens Y et Card Y = n) ⇒ P(Y)
    P_Y = N.modus_ponens(conjonction_intro(fini_ens_Y, cY_eq_n), Qn_Y)   # P(Y)

    # ── x0 ∉ Y ───────────────────────────────────────────────────────────────────
    x0_notin_Y = _x0_non_dans_diff(vX, vx0)                   # ¬(x0 ∈ Y)

    # ── le pas à (Y, x0) : (Fini-ens Y et ¬(x0∈Y) et P(Y)) ⇒ P(Y∪{x0}) ──────────
    pas_inst = instancie(instancie(hPas, Y), vx0)             # (Fini-ens Y et ¬(x0∈Y) et P(Y)) ⇒ P(Y∪{x0})
    ante_pas = conjonction_intro(conjonction_intro(fini_ens_Y, x0_notin_Y), P_Y)
    P_Yux0 = N.modus_ponens(ante_pas, pas_inst)              # P(Y∪{x0})

    # ── X = Y∪{x0} ⇒ P(X) (Leibniz Y∪{x0} ↦ X) ──────────────────────────────────
    Yux0_eq_X = N.modus_ponens(h_x0, _X_egal_diff_union_singleton(vX, vx0))  # Y∪{x0} = X
    leib_P = N.s6(E.reunion(Y, sing0), vX, "wp", P(var("wp")))   # (Y∪{x0}=X) ⇒ (P(Y∪{x0}) ⇔ P(X))
    eqv_P = N.modus_ponens(Yux0_eq_X, leib_P)
    P_X = N.modus_ponens(P_Yux0, equivalence_avant(eqv_P))   # P(X)   [x0∈X, Fini n, Q(n), ..., hPas, Fini-ens X, Card X=succ n]

    # ── élimine le témoin x0 : (∃z)(z∈X) ⇒ P(X) ─────────────────────────────────
    imp_x0 = N.loi_deduction(appartient(vx0, vX), P_X)       # (x0∈X) ⇒ P(X)
    ex_imp = existe_elimination(imp_x0, x0)                  # (∃x0)(x0∈X) ⇒ P(X)
    # ex_z lie « z » : α-renomme « z » → x0
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    ex_x0 = N.modus_ponens(ex_z, equivalence_avant(alpha_existe("z", x0, appartient(var("z"), vX))))
    P_X_final = N.modus_ponens(ex_x0, ex_imp)               # P(X)   [Fini n, Q(n), hPas, Fini-ens X, Card X=succ n]

    # ── Q(n+1) : décharge (Fini-ens X et Card X = succ n), généralise X ──────────
    corps_Qn1 = N.loi_deduction(et(est_fini_ensemble(vX), egal(cardinal(vX), succ_n)), P_X_final)
    Qn1 = N.generalisation(X, corps_Qn1)                     # Q(n+1)   [Fini n, Q(n), hPas]
    assert Qn1.conclusion == Q(succ_n), "Q(n+1) mal formé"

    # ── (Fini n et Q(n)) ⇒ Q(n+1), généralise n ─────────────────────────────────
    corps_step = N.loi_deduction(et(est_fini(vn), Q(vn)), Qn1)   # (Fini n et Q(n)) ⇒ Q(n+1)  [hPas]
    return N.generalisation(n, corps_step)                  # (∀n)((Fini n et Q(n)) ⇒ Q(n+1))  [hPas]


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PRINCIPE DE RÉCURRENCE SUR LES ENSEMBLES FINIS — recurrence_finie
# ════════════════════════════════════════════════════════════════════════════
def recurrence_finie(P, n="nrec", X="XQ", x0="x0rec", Xe="Xrec", xe="xrec",
                     k="kpred"):
    """🎯🎯 ⊢ recurrence_finie_enonce(P).   (THÉORÈME CLOS, 0 hyp.)

    Le PRINCIPE DE RÉCURRENCE SUR LES ENSEMBLES FINIS :
        ( P(∅) et (∀X)(∀x)( (est_fini_ensemble(X) et ¬(x∈X) et P(X)) ⇒ P(X∪{x}) ) )
        ⇒ (∀X)( est_fini_ensemble(X) ⇒ P(X) ).

    P : fonction Python (Terme → Formule).  Récurrence sur n = Card(X) (cf. module) :
    on assume les deux conjoints de la prémisse (P(∅) et le pas ensembliste), on prouve
    Q(0) et le pas Q(n)⇒Q(n+1) (Q(n) = (∀X)(Fini-ens X et Card X = n ⇒ P(X))), on
    invoque C61 (`principe_recurrence_preuve`, dont l'unique résidu
    `predecesseur_fini_universel` est DÉCHARGÉ par sa preuve close — Prop. 2 §III.5),
    obtenant (∀n)(Fini n ⇒ Q(n)) ; pour X fini, n := Card X est Fini (= est_fini_ensemble X)
    et Card X = Card X ⇒ Q(Card X) ⇒ P(X).  theorie=22, 0 hyp."""
    Q = _Q(P, X)
    vX = var(Xe)

    # ── prémisse : assume (P(∅) et le pas ensembliste) ──────────────────────────
    premisse = et(P(E.VIDE), _pas_ensemble(P, Xe, xe))
    hPrem = N.assume(premisse)
    hP0 = conjonction_elim_gauche(hPrem)                     # P(∅)
    hPas = conjonction_elim_droite(hPrem)                    # le pas ensembliste

    # ── Q(0) et le pas Q(n)⇒Q(n+1) ──────────────────────────────────────────────
    q0 = _preuve_Q0(P, hP0, X)                               # Q(0)   [P(∅)]
    step = _preuve_step(P, hPas, n, X, x0)                   # (∀n)((Fini n et Q(n))⇒Q(n+1))  [pas]

    # ── C61 : principe_recurrence(Q,n) déchargé de predecesseur_fini_universel ──
    princ_imp = principe_recurrence_preuve(Q, n, k=k)        # {pfu} ⊢ (Q(0) et step) ⇒ (∀n)(Fini n ⇒ Q n)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent (forme ?)"
    preuve_pfu = predecesseur_fini_universel_preuve(k=k)     # ⊢ pfu  (CLOS)
    princ_imp = _cut(princ_imp, pfu, preuve_pfu)             # (Q(0) et step) ⇒ (∀n)(Fini n ⇒ Q n)  [0 résidu C61]

    ante = conjonction_intro(q0, step)                       # Q(0) et step   [P(∅), pas]
    fini_implique_Qn = N.modus_ponens(ante, princ_imp)       # (∀n)(Fini n ⇒ Q(n))   [P(∅), pas]

    # ── pour X fini : Q(Card X) ⇒ P(X) ──────────────────────────────────────────
    h_fini_ens_X = N.assume(est_fini_ensemble(vX))           # est_fini_ensemble X = Fini(Card X)
    # instancie (∀n)(Fini n ⇒ Q n) à n := Card X
    inst = instancie(fini_implique_Qn, cardinal(vX))         # Fini(Card X) ⇒ Q(Card X)
    Q_cardX = N.modus_ponens(h_fini_ens_X, inst)             # Q(Card X)
    # Q(Card X) à X : (Fini-ens X et Card X = Card X) ⇒ P(X)
    Q_cardX_X = instancie(Q_cardX, vX)                       # (Fini-ens X et Card X = Card X) ⇒ P(X)
    cardX_eq_cardX = N.reflexivite(cardinal(vX))             # Card X = Card X
    P_X = N.modus_ponens(conjonction_intro(h_fini_ens_X, cardX_eq_cardX), Q_cardX_X)   # P(X)

    corps = N.loi_deduction(est_fini_ensemble(vX), P_X)      # (est_fini_ensemble X) ⇒ P(X)   [P(∅), pas]
    concl = N.generalisation(Xe, corps)                      # (∀X)(est_fini_ensemble X ⇒ P(X))   [P(∅), pas]

    res = N.loi_deduction(premisse, concl)                   # recurrence_finie_enonce(P)
    assert res.conclusion == recurrence_finie_enonce(P, Xe, xe), \
        "conclusion ≠ recurrence_finie_enonce(P)"
    return res


__all__ = ["recurrence_finie_enonce", "recurrence_finie"]
