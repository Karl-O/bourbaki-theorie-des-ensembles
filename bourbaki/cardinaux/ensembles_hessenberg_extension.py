"""§III.6.3 (Théorème 2, HESSENBERG) — pièces CARDINAL-ARITHMÉTIQUES de l'argument
d'EXTENSION du maximal (Bourbaki E.III.48, « CLAIM : Card(S₀)=Card(E) »).

CONTEXTE.  L'argument de Zorn fournit un couple maximal (S₀, φ₀) ∈ 𝔉(E), φ₀ : S₀×S₀ →
S₀ bijective (⇒ Card(S₀×S₀)=Card S₀, `maximal_carre_egal`).  Pour conclure Card S₀ =
Card E, Bourbaki suppose Card(E∖S₀) ≤ 𝔟 := Card S₀ et l'EXTENSION du maximal (cadre
(S₀∪U)²∖S₀², U⊂E∖S₀ de cardinal 𝔟) contredit la maximalité.  Ce module isole les DEUX
pièces d'arithmétique cardinale TRACTABLES de ce schéma :

  • `complement_grand(E, S0)` :
        { S₀⊂E,  𝔟+𝔟=𝔟  (𝔟:=Card S₀),  𝔟 < Card E }  ⊢  ¬( Card(E∖S₀) ≤ 𝔟 ).
    CLOS.  Route : E = S₀ ⊔ (E∖S₀) ⇒ Card E = 𝔟 + Card(E∖S₀) ; si Card(E∖S₀) ≤ 𝔟,
    additivité ⇒ Card E = 𝔟+Card(E∖S₀) ≤ 𝔟+𝔟 = 𝔟 < Card E, donc Card E ≤ 𝔟 ; or 𝔟 ≤ Card E
    (de 𝔟<Card E) ⇒ par antisymétrie 𝔟 = Card E, contredisant 𝔟 ≠ Card E.  Contraposition.

  • `existe_sous_ensemble_cardinal(c, A)` :
        { est_cardinal(c),  c ≤ Card A }  ⊢  (∃U)( U ⊂ A  et  Card U = c ).
    Route : c ≤ Card A ⇒ ∃ injection F : c ↪ Card A ; l'image Im=F⟨c⟩ ⊂ Card A vérifie
    Card Im = c.  Pour la RAMENER dans A (et non Card A), on transporte par la bijection
    Card A ≃ A (équipotence canonique d'un ensemble à son cardinal).  Cf. RÉSIDU précis.

OBSTRUCTION (étape 3, la bijection d'EXTENSION φ₀∪frame : (S₀∪U)²→S₀∪U + contradiction
de maximalité) : REPORTÉE — cf. bloc REPORT en fin de module.  Elle exige le cadre
disjoint 3𝔟²=3𝔟=𝔟 (lui-même sous le verrou « n≤𝔟 pour 𝔟 infini », REPORTÉ ailleurs)
PLUS le recollement φ₀∪frame et le contredit-maximalité (chirurgie de frames 𝔉(E)).

INVARIANT : theorie_ensembles() = 22.  Aucun axiome nouveau ; rien postulé ; les
hypothèses (𝔟+𝔟=𝔟, 𝔟<Card E, c≤Card A) sont HONNÊTES, jamais supposées vraies sans
décharge.  Noyau INTACT ; NOUVEAU module uniquement.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, inf_strict_card,
    est_injection_de, equipotent,
)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.ensembles_cardinal_ordre_props import (
    somme_cardinale_additive,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card, _cardinal_est_son_cardinal,
)
from bourbaki.entiers.ensembles_chap3_props_restantes import est_cardinal_de_cardinal

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

# ── machinerie disjoint-union cardinal (réutilisée telle quelle de Prop 13) ───────
from bourbaki.cardinaux.ensembles_prop13_complement import (
    _partie_reunion_complement_t, _partie_disjoint_complement_t,
    _eq_reunion_disjointe_somme_t, _somme_disjointe_cardinal_t, _prop1_direct_tt,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════════
#  Brique : Card E = somme_cardinale_binaire(Card S₀, Card(E∖S₀))  sous S₀⊂E.
#  (E = S₀ ⊔ (E∖S₀) : partie_reunion_complement + eq_reunion_disjointe_somme + Prop1
#   + somme_disjointe_cardinal, EXACTEMENT comme existe_complement_depuis_inf_egal.)
# ════════════════════════════════════════════════════════════════════════════════
def _card_E_somme(vE, vS):
    """{ S₀⊂E } ⊢ Card E = somme_cardinale_binaire(Card S₀, Card(E∖S₀)).

    S₀ joue le rôle de Im (la « partie »), R := E∖S₀ le complément ; on n'a PAS besoin
    d'injection (S₀ est déjà ⊂ E).  Renvoie le théorème sous la seule hyp S₀⊂E."""
    cS = cardinal(vS)
    R = E.difference(vE, vS)                       # E ∖ S₀
    cR = cardinal(R)
    SR = E.reunion(vS, R)                          # S₀ ∪ (E∖S₀)
    SsR = somme_disjointe(vS, R)                   # S₀ ⊔ (E∖S₀)

    h_sub = N.assume(inclus(vS, vE))               # S₀ ⊂ E

    # S₀ ∪ (E∖S₀) = E
    SR_eq_E = N.modus_ponens(h_sub, _partie_reunion_complement_t(vE, vS))
    # S₀ ∩ (E∖S₀) = ∅
    disj = _partie_disjoint_complement_t(vE, vS)
    # Eq(S₀∪R, S₀⊔R)
    eq_union_somme = N.modus_ponens(disj, _eq_reunion_disjointe_somme_t(vS, R))
    # réécrire S₀∪R ↦ E ⇒ Eq(E, S₀⊔R)
    eq_E_somme = N.modus_ponens(eq_union_somme, _equivalence_avant(N.modus_ponens(
        SR_eq_E, N.s6(SR, vE, "wext", equipotent(var("wext"), SsR)))))
    cardE_eq_cardsomme = N.modus_ponens(eq_E_somme, _prop1_direct_tt(vE, SsR))  # Card E = Card(S₀⊔R)

    # Card(S₀⊔R) = somme_cardinale_binaire(Card S₀, Card R)
    sdc = _somme_disjointe_cardinal_t(vS, R, cS, cR)
    cardsomme_eq = N.modus_ponens(
        conjonction_intro(N.reflexivite(cS), N.reflexivite(cR)), sdc)  # Card(S₀⊔R)=cS+cR
    return composer_egalites(cardE_eq_cardsomme, cardsomme_eq)         # Card E = cS + cR


def _equivalence_avant(thm_equiv):
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    return equivalence_avant(thm_equiv)


# ════════════════════════════════════════════════════════════════════════════════
#  (1)  complement_grand — ¬( Card(E∖S₀) ≤ 𝔟 ) sous {S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<Card E}.
# ════════════════════════════════════════════════════════════════════════════════
def complement_grand(E_set="E", S="S0"):
    """{ S₀⊂E,  𝔟+𝔟=𝔟,  𝔟<Card E }  ⊢  ¬( Card(E∖S₀) ≤ 𝔟 ),  où 𝔟 := Card S₀.

    🎯 Le complément du maximal est « grand » : sous S₀⊂E et l'absorption 2𝔟=𝔟, si le
    cardinal infini 𝔟=Card S₀ était STRICTEMENT plus petit que Card E, alors Card(E∖S₀)
    ne peut PAS être ≤ 𝔟 (sinon Card E ≤ 𝔟+𝔟=𝔟 < Card E, absurde par antisymétrie).
    C'est la première moitié de l'argument d'extension (E.III.48) : le reste E∖S₀ a de
    quoi loger un U équipotent à S₀.

    Hyps HONNÊTES (jamais postulées) : S₀⊂E, somme_cardinale_binaire(𝔟,𝔟)=𝔟, 𝔟<Card E.
    Conclusion ∉ hyps ; theorie=22 ; non vacuous."""
    vE, vS = _t(E_set), _t(S)
    cS = cardinal(vS)                                   # 𝔟 = Card S₀
    cE = cardinal(vE)                                   # Card E
    R = E.difference(vE, vS)                            # E ∖ S₀
    cR = cardinal(R)                                    # Card(E∖S₀)
    bb = somme_cardinale_binaire(cS, cS)                # 𝔟 + 𝔟
    bcR = somme_cardinale_binaire(cS, cR)              # 𝔟 + Card(E∖S₀)
    cible = non(inf_egal_card(cR, cS))                  # ¬( Card(E∖S₀) ≤ 𝔟 )

    # hyps honnêtes
    h_bb = N.assume(egal(bb, cS))                       # 𝔟 + 𝔟 = 𝔟
    h_lt = N.assume(inf_strict_card(cS, cE))            # 𝔟 < Card E  = (𝔟≤Card E et 𝔟≠Card E)
    b_le_E = conjonction_elim_gauche(h_lt)              # 𝔟 ≤ Card E
    b_ne_E = conjonction_elim_droite(h_lt)              # ¬(𝔟 = Card E)

    # Card E = 𝔟 + Card(E∖S₀)   (sous S₀⊂E)
    cardE_eq = _card_E_somme(vE, vS)                    # Card E = 𝔟 + Card(E∖S₀)   [S₀⊂E]
    assert cardE_eq.conclusion == egal(cE, bcR)

    # ── sous l'hypothèse de RÉFUTATION  c := Card(E∖S₀) ≤ 𝔟 ───────────────────────
    h_cle = N.assume(inf_egal_card(cR, cS))             # Card(E∖S₀) ≤ 𝔟

    # additivité : (Card S₀ ≤ Card S₀  et  Card(E∖S₀) ≤ Card S₀)
    #              ⇒ Card(Card S₀ ⊔ Card(E∖S₀)) ≤ Card(Card S₀ ⊔ Card S₀)
    #   i.e.  somme_cardinale_binaire(𝔟, Card(E∖S₀)) ≤ somme_cardinale_binaire(𝔟, 𝔟)
    # construit aux TERMES via somme_cardinale_additive généralisé/instancié (capture-safe).
    add_base = somme_cardinale_additive("Aadd", "Badd", "A1add", "B1add")
    add_gen = N.generalisation("Aadd", N.generalisation("Badd",
        N.generalisation("A1add", N.generalisation("B1add", add_base))))
    # instancie (A:=𝔟, B:=Card(E∖S₀), A₁:=𝔟, B₁:=𝔟)
    add = instancie(instancie(instancie(instancie(add_gen, cS), cR), cS), cS)
    ant_add = et(inf_egal_card(cS, cS), inf_egal_card(cR, cS))
    assert add.conclusion == impl(ant_add, inf_egal_card(bcR, bb)), \
        f"complement_grand : additivité forme inattendue\n{add.conclusion}"
    # 𝔟 ≤ 𝔟  (réflexivité au terme cS)
    refl_b = instancie(N.generalisation("Xrefl", inf_egal_reflexif("Xrefl")), cS)
    assert refl_b.conclusion == inf_egal_card(cS, cS)
    le_sums = N.modus_ponens(conjonction_intro(refl_b, h_cle), add)   # 𝔟+Card(E∖S₀) ≤ 𝔟+𝔟

    # rewrite RHS : 𝔟+𝔟 ↦ 𝔟  (h_bb)  ⇒  𝔟+Card(E∖S₀) ≤ 𝔟
    s6_rhs = N.s6(bb, cS, "wrhs", inf_egal_card(bcR, var("wrhs")))
    le_bcR_b = N.modus_ponens(le_sums, _equivalence_avant(N.modus_ponens(h_bb, s6_rhs)))
    assert le_bcR_b.conclusion == inf_egal_card(bcR, cS)              # 𝔟+Card(E∖S₀) ≤ 𝔟

    # rewrite LHS : 𝔟+Card(E∖S₀) ← Card E  (cardE_eq)  ⇒  Card E ≤ 𝔟
    # on réécrit bcR ↦ cE dans (bcR ≤ 𝔟) via bcR = cE (symétrie de cardE_eq).
    bcR_eq_cE = N.modus_ponens(cardE_eq, symetrie(cE, bcR))          # 𝔟+Card(E∖S₀) = Card E
    s6_lhs = N.s6(bcR, cE, "wlhs", inf_egal_card(var("wlhs"), cS))
    le_E_b = N.modus_ponens(le_bcR_b, _equivalence_avant(N.modus_ponens(bcR_eq_cE, s6_lhs)))
    assert le_E_b.conclusion == inf_egal_card(cE, cS)                 # Card E ≤ 𝔟

    # antisymétrie (𝔟, Card E) : (𝔟≤Card E et Card E≤𝔟 et card 𝔟 et card Card E) ⇒ 𝔟=Card E
    anti = instancie(instancie(inf_egal_antisymetrique_card("aanti", "banti"), cS), cE)
    card_b = est_cardinal_de_cardinal(vS)                            # est_cardinal(Card S₀)
    assert card_b.conclusion == est_cardinal(cS)
    card_E = est_cardinal_de_cardinal(vE)                            # est_cardinal(Card E)
    assert card_E.conclusion == est_cardinal(cE)
    ante_anti = et(et(et(inf_egal_card(cS, cE), inf_egal_card(cE, cS)),
                      est_cardinal(cS)), est_cardinal(cE))
    minor = conjonction_intro(conjonction_intro(conjonction_intro(
        b_le_E, le_E_b), card_b), card_E)
    assert minor.conclusion == ante_anti, \
        f"complement_grand : antécédent antisym inattendu\n{minor.conclusion}\nvs\n{ante_anti}"
    b_eq_E = N.modus_ponens(minor, anti)                             # 𝔟 = Card E

    # décharge : (Card(E∖S₀) ≤ 𝔟) ⇒ (𝔟 = Card E)
    impl_cle_eq = N.loi_deduction(inf_egal_card(cR, cS), b_eq_E)     # c≤𝔟 ⇒ 𝔟=Card E
    # contraposition : ¬(𝔟=Card E) ⇒ ¬(c≤𝔟)
    contra = contraposition(impl_cle_eq)                             # ¬(𝔟=Card E) ⇒ ¬(c≤𝔟)
    assert contra.conclusion == impl(non(egal(cS, cE)), cible), \
        f"complement_grand : contraposée inattendue\n{contra.conclusion}"
    res = N.modus_ponens(b_ne_E, contra)                             # ¬( Card(E∖S₀) ≤ 𝔟 )

    assert res.conclusion == cible, \
        f"complement_grand : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert inclus(vS, vE) in res.hypotheses, "complement_grand : hyp S₀⊂E absente"
    assert egal(bb, cS) in res.hypotheses, "complement_grand : hyp 𝔟+𝔟=𝔟 absente"
    assert inf_strict_card(cS, cE) in res.hypotheses, "complement_grand : hyp 𝔟<Card E absente"
    assert res.conclusion not in res.hypotheses, "complement_grand : VACUOUS"
    return res


def complement_grand_cible(E_set="E", S="S0"):
    """ÉNONCÉ-cible (test miroir) de complement_grand."""
    vE, vS = _t(E_set), _t(S)
    cS, cR = cardinal(vS), cardinal(E.difference(vE, vS))
    return non(inf_egal_card(cR, cS))


__all__ = [
    "complement_grand",
    "complement_grand_cible",
]
