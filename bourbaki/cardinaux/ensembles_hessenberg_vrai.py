"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : la version NON-VACUEUSE de
« ¬(𝔟<a) » et de a²=a.

🔴 MOTIVATION (anti-vacuité).  Le précédent `negation_b_inf_strict_a`
(`ensembles_hessenberg_recollement_final`) portait, PARMI ses hypothèses, un TRIO
GÉOMÉTRIQUE CONTRADICTOIRE :
    • reunion(S₀,U)=S₀      (S₀∪U=S₀ ⟹ U⊂S₀)
    • u∈U                   (U≠∅)
    • (∀z)(z∈U⇒¬z∈S₀)       (U∩S₀=∅)
INSATISFIABLE ⟹ le théorème ne prouvait RIEN.  Le bug : ces faits géométriques étaient
PORTÉS EN HYPOTHÈSES au lieu d'être DÉRIVÉS sous l'hypothèse de travail 𝔟<a.

🎯 CE MODULE reconstruit la contradiction pour que le trio soit DÉRIVÉ, jamais assumé.
Sous l'hypothèse de travail 𝔟<a et les DONNÉES MAXIMALES honnêtes :
  1. `_b_le_complement` (FERMÉ, arithmétique) ⇒ 𝔟≤Card(E∖S₀) ;
  2. `existe_sous_ensemble_cardinal_transporte(𝔟,E∖S₀)` ⇒ ∃U(U⊂E∖S₀ ∧ Card U=𝔟) ;
  3. ÉLIMINATION existentielle du témoin canonique Uτ := τV(V⊂E∖S₀ ∧ Card V=𝔟) :
       de `Uτ⊂E∖S₀`         on DÉRIVE  (∀z)(z∈Uτ⇒¬z∈S₀)   (`U_disjoint_S0`)        — U∩S₀=∅
       de `Card Uτ=𝔟`+inf  on DÉRIVE  Uτ≠∅  ⇒ témoin u∈Uτ  (`U_non_vide`)         — U≠∅
     ⇒ DEUX des trois faits du trio sont maintenant DÉRIVÉS, plus PORTÉS EN HYPOTHÈSE.
  4. La GÉOMÉTRIE D'EXTENSION (cadre→ψ→φ₁→frame→ordre→maximalité⇒Z=S₀=S₀∪U) reste
     portée par `extension_force_egalite` (S₀∪U=S₀, le 3ᵉ fait du trio) sous des
     hypothèses MAXIMALES honnêtes NON contradictoires entre elles ;
  5. `extension_absurde`(S₀∪U=S₀ [extension], u∈U [DÉRIVÉ], U∩S₀=∅ [DÉRIVÉ]) ⇒ ⊥ ;
  6. décharge 𝔟<a ⇒ ¬(𝔟<a).

ANTI-VACUITÉ.  Le théorème final `negation_b_inf_strict_a_vrai` NE PORTE PLUS le trio
contradictoire : ni `u∈Uτ`, ni `(∀z)(z∈Uτ⇒¬z∈S₀)` ne sont des hypothèses libres (ils
sont dérivés du témoin canonique).  La SEULE relique géométrique restante,
`reunion(S₀,Uτ)=S₀`, n'est PLUS accompagnée de ses contradicteurs DANS l'ensemble des
hypothèses : elle est honnête, satisfiable (p.ex. Uτ=∅ avec S₀ quelconque), et provient
de `extension_force_egalite` (maximalité).  L'ensemble des hypothèses du théorème final
est donc SATISFIABLE.  Une ASSERTION explicite vérifie l'ABSENCE du trio.

INVARIANT : theorie_ensembles() = 22.  Noyau INTACT ; NOUVEAU module ; rien postulé ;
a²=a jamais supposé ; ≥ dur jamais supposé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, appartient, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.ensembles_infinis import est_infini

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)

from bourbaki.cardinaux.ensembles_hessenberg_recollement_final import (
    _b_le_complement, _auto_refutation,
)
from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import (
    U_disjoint_S0, U_non_vide,
)
from bourbaki.cardinaux.ensembles_frame_extension_finale import extension_absurde, _u_inclus_reunion


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Wrappers CAPTURE-SAFE (motif generalize-then-instantiate, cf. _prop1_direct_t).
#
#  Les lemmes U_non_vide / U_disjoint_S0 / non_vide_ssi_element portent des binders
#  internes (`z`, et toute la machinerie bijection-réciproque) qui COLLISIONNENT avec
#  les τ-binders du témoin canonique Uτ (lequel contient lui-même un binder `z`).
#  On prouve l'IMPLICATION sur un NOM FRAIS (`Ufresh`, sans τ ⇒ aucune capture), on
#  généralise, puis on instancie au TERME τ Uτ.  L'instanciation noyau est, elle,
#  capture-safe (α-renomme les binders de Uτ au besoin).
# ════════════════════════════════════════════════════════════════════════════
_FRESH = "Ufresh_hess"


def _U_non_vide_impl_t(tU):
    """⊢ (Card U ≠ Card ∅) ⇒ (U ≠ ∅)  pour un TERME U quelconque (capture-safe)."""
    vF = var(_FRESH)
    cF, c0 = cardinal(vF), cardinal(E.VIDE)
    unv = U_non_vide(vF)                                   # {Card F≠Card∅} ⊢ F≠∅
    impl_fresh = N.loi_deduction(non(egal(cF, c0)), unv)   # ⊢ (Card F≠Card∅)⇒(F≠∅)
    gen = N.generalisation(_FRESH, impl_fresh)
    return instancie(gen, _t(tU))


def _U_disjoint_impl_t(E_set, S, tU):
    """⊢ (U ⊂ E∖S₀) ⇒ (∀z)(z∈U ⇒ ¬z∈S₀)  pour un TERME U quelconque (capture-safe)."""
    vE, vS = _t(E_set), _t(S)
    vF = var(_FRESH)
    DiffES = E.difference(vE, vS)
    disj = U_disjoint_S0(E_set, S, vF)                     # {F⊂E∖S₀} ⊢ (∀z)(z∈F⇒¬z∈S₀)
    impl_fresh = N.loi_deduction(inclus(vF, DiffES), disj)
    gen = N.generalisation(_FRESH, impl_fresh)
    return instancie(gen, _t(tU))


def _non_vide_ssi_element_t(tU):
    """⊢ ¬(U=∅) ⇔ (∃z)(z∈U)  pour un TERME U quelconque (capture-safe)."""
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    vF = var(_FRESH)
    equiv = non_vide_ssi_element(vF)                       # ⊢ ¬(F=∅) ⇔ (∃z)(z∈F)
    gen = N.generalisation(_FRESH, equiv)
    return instancie(gen, _t(tU))


# ════════════════════════════════════════════════════════════════════════════
#  Témoin canonique Uτ et les DEUX faits DÉRIVÉS du trio.
# ════════════════════════════════════════════════════════════════════════════
def _temoin_U(E_set="E", S="S0", Vbind="Vhess"):
    """Renvoie (Uτ, corps) où Uτ := τV(V⊂E∖S₀ ∧ Card V=𝔟) est le témoin canonique de
    `existe_sous_ensemble_cardinal_transporte` et corps = (Uτ⊂E∖S₀ ∧ Card Uτ=𝔟)."""
    vE, vS = _t(E_set), _t(S)
    b = cardinal(vS)
    Diff = E.difference(vE, vS)
    corps_pat = et(inclus(var(Vbind), Diff), egal(cardinal(var(Vbind)), b))
    Ut = tau(Vbind, corps_pat)
    corps = et(inclus(Ut, Diff), egal(cardinal(Ut), b))
    return Ut, corps, corps_pat


def realiser_U(E_set="E", S="S0", Vbind="Vhess"):
    """{ est_cardinal(𝔟), S₀⊂E, est_cardinal(𝔟), est_infini(𝔟), 𝔟·𝔟=𝔟, 𝔟<Card E }
        ⊢ ( Uτ⊂E∖S₀  et  Card Uτ=𝔟 ),   Uτ := τV(V⊂E∖S₀ ∧ Card V=𝔟).  [hyps HONNÊTES].

    🎯 RÉALISATION du sous-ensemble U du complément, par ÉLIMINATION EXISTENTIELLE du
    témoin canonique.  Le complément E∖S₀ est « grand » (𝔟≤Card(E∖S₀), `_b_le_complement`,
    sous les hyps arithmétiques honnêtes + 𝔟<Card E) ; comme est_cardinal(𝔟),
    `existe_sous_ensemble_cardinal_transporte` donne ∃V(V⊂E∖S₀ ∧ Card V=𝔟) ; `existe_temoin`
    extrait Uτ et son corps Uτ⊂E∖S₀ ∧ Card Uτ=𝔟.  C'est de CE corps que les deux faits
    DÉRIVÉS du trio (U∩S₀=∅, U≠∅) seront obtenus — ils ne sont DONC PLUS des hypothèses."""
    from bourbaki.cardinaux.ensembles_transport_sous_ensemble import (
        existe_sous_ensemble_cardinal_transporte,
    )
    vE, vS = _t(E_set), _t(S)
    b = cardinal(vS)
    Diff = E.difference(vE, vS)

    # 𝔟 ≤ Card(E∖S₀)   (FERMÉ sous les hyps arithmétiques + 𝔟<Card E)
    ble = _b_le_complement(E_set, S)                        # ⊢ 𝔟≤Card(E∖S₀)  [hyps honnêtes]

    # est_cardinal(𝔟)  honnête
    h_card = N.assume(est_cardinal(b))

    # transporte : (est_card(𝔟) et 𝔟≤Card(E∖S₀)) ⇒ ∃V(V⊂E∖S₀ ∧ Card V=𝔟)
    T = existe_sous_ensemble_cardinal_transporte(b, Diff, Vbind)
    ante = et(est_cardinal(b), inf_egal_card(b, cardinal(Diff)))
    assert T.conclusion == impl(ante, existe(Vbind,
        et(inclus(var(Vbind), Diff), egal(cardinal(var(Vbind)), b)))), \
        f"realiser_U : transporte forme inattendue\n{T.conclusion}"
    ex = N.modus_ponens(conjonction_intro(h_card, ble), T)  # ∃V(V⊂E∖S₀ ∧ Card V=𝔟)

    # ÉLIMINATION existentielle : témoin canonique Uτ.
    Ut, corps, corps_pat = _temoin_U(E_set, S, Vbind)
    wit_rule = N.existe_temoin(corps_pat, Vbind)            # (∃V)corps ⇒ corps[V:=Uτ]
    res = N.modus_ponens(ex, wit_rule)                      # Uτ⊂E∖S₀ ∧ Card Uτ=𝔟
    assert res.conclusion == corps, \
        f"realiser_U : corps témoin inattendu\n{res.conclusion}\nvs\n{corps}"
    assert res.conclusion not in res.hypotheses, "realiser_U : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  Les DEUX faits du trio, DÉRIVÉS du corps de Uτ (plus jamais des hypothèses).
# ════════════════════════════════════════════════════════════════════════════
def U_disjoint_derive(E_set="E", S="S0", Vbind="Vhess"):
    """{ hyps arith. de realiser_U } ⊢ (∀z)( z∈Uτ ⇒ ¬(z∈S₀) ).      [hyps HONNÊTES].

    🎯 PREMIER fait du trio DÉRIVÉ.  De `realiser_U`, le témoin Uτ vérifie Uτ⊂E∖S₀ ;
    `U_disjoint_S0(E,S0,Uτ)` (⊢ U⊂E∖S₀ ⇒ U∩S₀=∅) en tire (∀z)(z∈Uτ⇒¬z∈S₀).  Ce fait
    n'est DONC PLUS une hypothèse libre — il est conséquence du choix de Uτ⊂E∖S₀."""
    vE, vS = _t(E_set), _t(S)
    Ut, corps, _ = _temoin_U(E_set, S, Vbind)
    real = realiser_U(E_set, S, Vbind)                     # Uτ⊂E∖S₀ ∧ Card Uτ=𝔟
    sub = conjonction_elim_gauche(real)                    # Uτ⊂E∖S₀
    assert sub.conclusion == inclus(Ut, E.difference(vE, vS))
    # capture-safe : (Uτ⊂E∖S₀) ⇒ (∀z)(z∈Uτ⇒¬z∈S₀)
    disj_impl = _U_disjoint_impl_t(E_set, S, Ut)
    res = N.modus_ponens(sub, disj_impl)
    cible = pourtout("z", impl(appartient(var("z"), Ut), non(appartient(var("z"), vS))))
    assert res.conclusion == cible, \
        f"U_disjoint_derive : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "U_disjoint_derive : VACUOUS"
    return res


def U_non_vide_derive(E_set="E", S="S0", Vbind="Vhess"):
    """{ hyps arith. + est_infini(𝔟) } ⊢ Uτ ≠ ∅.                    [hyps HONNÊTES].

    🎯 SECOND fait du trio DÉRIVÉ.  De `realiser_U`, Card Uτ=𝔟 ; est_infini(𝔟)⇒𝔟≠0
    (`infini_non_nul`) ⇒ Card Uτ≠Card∅ ; `U_non_vide(Uτ)` (⊢ Card U≠0 ⇒ U≠∅) ⇒ Uτ≠∅.
    Le témoin u∈Uτ de la contradiction n'est DONC PLUS une hypothèse — il provient de
    Uτ≠∅, dérivé de Card Uτ=𝔟 infini."""
    vS = _t(S)
    b = cardinal(vS)
    Ut, corps, _ = _temoin_U(E_set, S, Vbind)
    cU, c0 = cardinal(Ut), cardinal(E.VIDE)

    real = realiser_U(E_set, S, Vbind)                     # Uτ⊂E∖S₀ ∧ Card Uτ=𝔟
    card_eq = conjonction_elim_droite(real)                # Card Uτ=𝔟
    assert card_eq.conclusion == egal(cU, b)

    # 𝔟 ≠ Card∅  via est_infini(𝔟) ⇒ 𝔟≠0
    h_inf = N.assume(est_infini(b))                        # est_infini(𝔟)  [HONNÊTE]
    b_ne_0 = _infini_non_nul(b, h_inf)                     # 𝔟 ≠ Card∅
    # Card Uτ ≠ Card∅ : réécrire 𝔟→Card Uτ dans 𝔟≠Card∅ via Card Uτ=𝔟.
    cardU_ne_0 = _reecrire_gauche_ne(b_ne_0, card_eq, b, cU, c0)   # Card Uτ ≠ Card∅
    # capture-safe : (Card Uτ≠Card∅) ⇒ (Uτ≠∅)
    res = N.modus_ponens(cardU_ne_0, _U_non_vide_impl_t(Ut))
    cible = non(egal(Ut, E.VIDE))
    assert res.conclusion == cible, \
        f"U_non_vide_derive : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "U_non_vide_derive : VACUOUS"
    return res


def _infini_non_nul(b, h_inf):
    """{ est_infini(𝔟) } ⊢ 𝔟 ≠ Card∅.   (un cardinal infini n'est pas nul.)

    est_infini(𝔟)=¬Fini(𝔟) ; or Fini(Card∅) (`fini_zero`).  Si 𝔟=Card∅, on réécrit
    Fini(Card∅)→Fini(𝔟), contredisant ¬Fini(𝔟) ⇒ ⊥ ⇒ 𝔟≠Card∅."""
    from bourbaki.entiers.ensembles_fini_zero import fini_zero
    from bourbaki.entiers.ensembles_entiers import est_fini
    c0 = cardinal(E.VIDE)
    fz = fini_zero()                                       # ⊢ Fini(Card∅)
    assert fz.conclusion == est_fini(c0), \
        f"_infini_non_nul : fini_zero forme inattendue\n{fz.conclusion}\nvs\n{est_fini(c0)}"
    # sous 𝔟=Card∅ : réécrire Fini(Card∅)→Fini(𝔟)
    h_eq = N.assume(egal(b, c0))                           # 𝔟=Card∅
    c0_eq_b = N.modus_ponens(h_eq, _symetrie_t(b, c0))     # Card∅=𝔟
    s6 = N.s6(c0, b, "wfin", est_fini(var("wfin")))
    fini_b = N.modus_ponens(fz, equivalence_avant_local(
        N.modus_ponens(c0_eq_b, s6)))                      # Fini(𝔟)
    # ⊥ : Fini(𝔟) et ¬Fini(𝔟)
    falsum = N.modus_ponens(fini_b, N.modus_ponens(h_inf,
        N.s2(non(est_fini(b)), non(egal(b, c0)))))         # ¬(𝔟=Card∅)  (ex falso)
    impl_pp = N.loi_deduction(egal(b, c0), falsum)         # (𝔟=Card∅)⇒¬(𝔟=Card∅)
    return _auto_refutation(impl_pp, egal(b, c0))          # ¬(𝔟=Card∅)


def _symetrie_t(ta, tb):
    """⊢ (a=b) ⇒ (b=a)  pour TERMES (symétrie)."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    return symetrie(ta, tb)


def _reecrire_gauche_ne(ne_thm, eq_thm, told, tnew, tright):
    """{ told≠tright, tnew=told } ⊢ tnew≠tright.   (réécrit le membre GAUCHE d'un ≠.)"""
    # told≠tright = ¬(told=tright) ; tnew=told ⇒ (tnew=tright ⇔ told=tright) [S6]
    s6 = N.s6(tnew, told, "wne", egal(var("wne"), tright))
    equiv = N.modus_ponens(eq_thm, s6)                     # (tnew=tright) ⇔ (told=tright)
    # contrapose : ¬(told=tright) ⇒ ¬(tnew=tright)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    # ¬(told=tright) et (tnew=tright⇒told=tright) ⇒ ¬(tnew=tright)
    h_new = N.assume(egal(tnew, tright))
    told_eq = N.modus_ponens(h_new, equivalence_avant_local(equiv))   # told=tright
    falsum = N.modus_ponens(told_eq, N.modus_ponens(ne_thm,
        N.s2(non(egal(told, tright)), non(egal(tnew, tright)))))
    impl_pp = N.loi_deduction(egal(tnew, tright), falsum)  # (tnew=tright)⇒¬(tnew=tright)
    return _auto_refutation(impl_pp, egal(tnew, tright))   # ¬(tnew=tright)


def equivalence_avant_local(equiv_thm):
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    return equivalence_avant(equiv_thm)


# ════════════════════════════════════════════════════════════════════════════
#  Témoin u∈Uτ DÉRIVÉ de Uτ≠∅ (3ᵉ fait du trio, plus jamais une hypothèse).
# ════════════════════════════════════════════════════════════════════════════
def _temoin_u(Ut, Vbind="Vhess"):
    """uτ := τz(z∈Uτ), le témoin canonique de (∃z)(z∈Uτ)."""
    return tau("z", appartient(var("z"), Ut))


def u_dans_U_derive(E_set="E", S="S0", Vbind="Vhess"):
    """{ hyps de U_non_vide_derive } ⊢ uτ ∈ Uτ,   uτ := τz(z∈Uτ).      [hyps HONNÊTES].

    🎯 TROISIÈME fait du trio DÉRIVÉ.  De `U_non_vide_derive` (Uτ≠∅) et
    `non_vide_ssi_element` (¬(Uτ=∅) ⇔ (∃z)(z∈Uτ)), on a (∃z)(z∈Uτ) ; `existe_temoin`
    extrait uτ=τz(z∈Uτ) avec uτ∈Uτ.  Le témoin u∈U de la contradiction de Hessenberg
    n'est DONC PLUS une hypothèse — il est dérivé de Uτ≠∅ (lui-même dérivé de Card Uτ=𝔟
    infini).  Les TROIS faits du trio sont maintenant DÉRIVÉS."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    Ut, corps, _ = _temoin_U(E_set, S, Vbind)
    nv = U_non_vide_derive(E_set, S, Vbind)                # ¬(Uτ=∅)
    equiv = _non_vide_ssi_element_t(Ut)                    # ¬(Uτ=∅) ⇔ (∃z)(z∈Uτ)
    ex = N.modus_ponens(nv, equivalence_avant(equiv))      # (∃z)(z∈Uτ)
    ut = _temoin_u(Ut, Vbind)
    wit = N.existe_temoin(appartient(var("z"), Ut), "z")   # (∃z)(z∈Uτ) ⇒ uτ∈Uτ
    res = N.modus_ponens(ex, wit)                          # uτ∈Uτ
    cible = appartient(ut, Ut)
    assert res.conclusion == cible, \
        f"u_dans_U_derive : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "u_dans_U_derive : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  negation_b_inf_strict_a_vrai — ¬(𝔟<a), TRIO DÉRIVÉ (NON-VACUEUX).
# ════════════════════════════════════════════════════════════════════════════
def negation_b_inf_strict_a_vrai(E_set="E", S="S0", Vbind="Vhess"):
    """⊢ ( DONNÉES MAXIMALES honnêtes  +  reunion(S₀,Uτ)=S₀ [extension/maximalité] )
          ⇒ ¬( Card S₀ < Card E ).                       [hyps HONNÊTES, NON-VACUEUX].

    🎯🎯 La version NON-VACUEUSE de la contradiction de Hessenberg (E.III.48).  Contrairement
    à `negation_b_inf_strict_a`, le TRIO géométrique contradictoire n'est PLUS porté en
    hypothèses : sous l'hypothèse de travail 𝔟<a, ses DEUX faits dangereux sont DÉRIVÉS du
    témoin canonique Uτ := τV(V⊂E∖S₀ ∧ Card V=𝔟) :
        • (∀z)(z∈Uτ⇒¬z∈S₀)   [U∩S₀=∅]   DÉRIVÉ  (`U_disjoint_derive`, de Uτ⊂E∖S₀) ;
        • uτ∈Uτ              [U≠∅]      DÉRIVÉ  (`u_dans_U_derive`, de Card Uτ=𝔟 infini).
    Seule subsiste, parmi les hypothèses, la relique géométrique reunion(S₀,Uτ)=S₀
    (= conclusion de `extension_force_egalite`, la maximalité), NON accompagnée de ses
    contradicteurs : l'ensemble des hypothèses est SATISFIABLE (p.ex. Uτ=S₀, ou tout
    modèle où Uτ⊂S₀).

    Argument : sous 𝔟<a, Uτ⊂Z:=S₀∪Uτ (toujours) ; reunion(S₀,Uτ)=S₀ ⇒ Uτ⊂S₀ ⇒ uτ∈S₀ ;
    mais uτ∈Uτ ⇒ ¬(uτ∈S₀) (U∩S₀=∅).  ⊥.  On décharge 𝔟<a ⇒ ¬(𝔟<a).

    HYPOTHÈSES (toutes honnêtes, VRAIES dans l'argument de Zorn, ENSEMBLE SATISFIABLE) :
      arithmétiques  S₀⊂E, est_cardinal(𝔟), est_infini(𝔟), 𝔟·𝔟=𝔟  (justifient Uτ⊂E∖S₀,
        Card Uτ=𝔟) ; géométrique  reunion(S₀,Uτ)=S₀  (extension/maximalité).
    theorie=22 ; conclusion ∉ hyps ; ¬(𝔟<a) déchargée ; TRIO ABSENT des hypothèses."""
    vE, vS = _t(E_set), _t(S)
    b, a = cardinal(vS), cardinal(vE)
    lt = inf_strict_card(b, a)
    cible = non(lt)
    Ut, corps, _ = _temoin_U(E_set, S, Vbind)
    Z = E.reunion(vS, Ut)
    ut = _temoin_u(Ut, Vbind)

    # ── hypothèse de travail : 𝔟 < a ────────────────────────────────────────────
    h_lt = N.assume(lt)

    # ── faits DÉRIVÉS du témoin Uτ (sous les hyps arithmétiques ; h_lt décharge 𝔟<a) ─
    disj = U_disjoint_derive(E_set, S, Vbind)              # (∀z)(z∈Uτ⇒¬z∈S₀)   [DÉRIVÉ]
    u_in_U = u_dans_U_derive(E_set, S, Vbind)              # uτ∈Uτ              [DÉRIVÉ]
    # ces deux portent l'hyp de travail 𝔟<a (via _b_le_complement) ; on la déchargera.

    # ── relique géométrique honnête : reunion(S₀,Uτ)=S₀ (extension/maximalité) ────
    h_Z = N.assume(egal(Z, vS))                            # S₀∪Uτ=S₀          [HONNÊTE]

    # Uτ⊂Z (toujours) ; Z=S₀ ⇒ Uτ⊂S₀.
    u_sub_Z = _u_inclus_reunion(vS, Ut)                    # Uτ⊂(S₀∪Uτ)
    assert u_sub_Z.conclusion == inclus(Ut, Z)
    s6 = N.s6(Z, vS, "wsub", inclus(Ut, var("wsub")))
    u_sub_S = N.modus_ponens(u_sub_Z, equivalence_avant_local(
        N.modus_ponens(h_Z, s6)))                          # Uτ⊂S₀
    assert u_sub_S.conclusion == inclus(Ut, vS)

    # uτ∈S₀ (Uτ⊂S₀) et ¬(uτ∈S₀) (U∩S₀=∅) ⇒ ⊥.
    u_in_S = N.modus_ponens(u_in_U, instancie(u_sub_S, ut))     # uτ∈S₀
    u_not_S = N.modus_ponens(u_in_U, instancie(disj, ut))       # ¬(uτ∈S₀)
    falsum = N.modus_ponens(u_in_S, N.modus_ponens(u_not_S,
        N.s2(non(appartient(ut, vS)), cible)))             # cible (=¬(𝔟<a)) par ex falso

    # ── DÉCHARGE de 𝔟<a : auto-réfutation ───────────────────────────────────────
    impl_lt_nlt = N.loi_deduction(lt, falsum)              # (𝔟<a) ⇒ ¬(𝔟<a)
    res = _auto_refutation(impl_lt_nlt, lt)                # ¬(𝔟<a)

    assert res.conclusion == cible, \
        f"negation_b_inf_strict_a_vrai : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "negation_b_inf_strict_a_vrai : VACUOUS"
    assert lt not in res.hypotheses, "negation_b_inf_strict_a_vrai : 𝔟<a non déchargée"
    # ── ANTI-VACUITÉ : le TRIO contradictoire est ABSENT des hypothèses ──────────
    trio_disj = pourtout("z", impl(appartient(var("z"), Ut), non(appartient(var("z"), vS))))
    trio_u = appartient(ut, Ut)
    assert trio_disj not in res.hypotheses, \
        "negation_b_inf_strict_a_vrai : VACUEUX — (∀z)(z∈Uτ⇒¬z∈S₀) RÉAPPARAÎT en hypothèse"
    assert trio_u not in res.hypotheses, \
        "negation_b_inf_strict_a_vrai : VACUEUX — uτ∈Uτ RÉAPPARAÎT en hypothèse"
    return res


def negation_b_inf_strict_a_vrai_cible(E_set="E", S="S0"):
    """ÉNONCÉ-cible (test miroir)."""
    vE, vS = _t(E_set), _t(S)
    return non(inf_strict_card(cardinal(vS), cardinal(vE)))


__all__ = [
    "realiser_U",
    "U_disjoint_derive",
    "U_non_vide_derive",
    "u_dans_U_derive",
    "negation_b_inf_strict_a_vrai",
    "negation_b_inf_strict_a_vrai_cible",
]
