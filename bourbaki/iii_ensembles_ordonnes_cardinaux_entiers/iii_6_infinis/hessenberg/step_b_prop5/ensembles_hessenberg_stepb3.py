"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : STEP B2-RÉUNION — l'élimination
de Ucadre ABOUTIT : ¬( Card S₀ < Card E ) sous la seule maximal-data.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  B1' (stepb2, via_reunion=True) livre le FALSUM sous 12 hyps dont 9
mentionnent Ucadre.  Le re-câblage RÉUNION ayant dissous le mur somme-disjointe
(cf. TABLE DE DÉCHARGE au journal), CHAQUE hyp-Ucadre est ici DÉCHARGÉE depuis
le seul CORPS du transport { U⊂E∖S₀, Card U=𝔟 } + la maximal-data :

  (1) imgφ₀∩U=∅        ← inter(S₀,U)=∅ (produits_disjoints) + rewrite imgφ₀→S₀ ;
  (2) imgφ₀∪U=Z        ← RÉFLEXIVITÉ S₀∪U=Z + même rewrite ;
  (3) S₀²∪F_r=Z²       ← s0sq_cadre_reunion_egale_carre  [CLOS] ;
  (4) Card F_r=Card U  ← cadre_card_trois_b_reunion (L4) + Card U=𝔟 ;
  (5) dom-disj         ← carre_disjoint_cadre_reunion (L5) + rewrite domφ₀→S₀² ;
  (7) Z⊂E              ← U⊂E∖S₀ + S₀⊂E (par cas sur AXIOME_REUNION) ;
  (8) Z infini         ← z_infini_derive (L-inf) ;
  (9) Card U≠Card∅     ← Card U=𝔟 + est_infini(𝔟) + fini-de-zéro (absurde).
Puis loi de déduction sur le corps, existe_elimination("Ucadre"), et l'AMONT :
𝔟<Card E ⇒ complement_grand ⇒ (comparabilité des cardinaux, CLOSE) ⇒
𝔟 ≤ Card(E∖S₀) ⇒ transport ⇒ (∃U)(corps) ⇒ marqueur ; contraposition ⇒
**¬( 𝔟 < Card E )**.

HYPS FINALES (toutes Ucadre-LIBRES, toutes fournies par unpack_maximal ou
∀∀-closes reportées) : { bij(φ₀,S₀²,S₀), element_maximal, (S₀,φ₀)∈𝔉,
est_infini_ensemble(S₀), S₀⊂E, résidus ∀∀ de fini_downward_thm }.
INVARIANT : theorie_ensembles()=22 ; rien postulé ; lock ABSENT ; noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, contraposition, dni, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, est_bijection_de, inf_egal_card, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_stepb2 import (
    negation_strict_sous_temoins_UF, _marqueur_faux,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    """Décharge dans thm chaque hypothèse == conclusion d'une preuve fournie."""
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _exfalso_vers(neg_thm, pos_thm, cible):
    """De ⊢¬X et ⊢X, déduit ⊢ cible  (S2, motif marqueur)."""
    x = pos_thm.conclusion
    return N.modus_ponens(pos_thm, N.modus_ponens(neg_thm, N.s2(non(x), cible)))


def _Z_inclus_E(vS, vU, vE, corps_incl):
    """{ corps_incl : (∀z)(z∈U ⇒ z∈E∖S₀),  S₀⊂E } ⊢ Z⊂E,  Z=S₀∪U.  (par cas)."""
    Z = E.reunion(vS, vU)
    vz = var("z")
    h_SE = N.assume(inclus(vS, vE))                          # S₀⊂E   [hyp propre]
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION), vS), vU), vz)
    hz = N.assume(appartient(vz, Z))
    disj = N.modus_ponens(hz, equivalence_avant(car))        # z∈S₀ ∨ z∈U
    # branche S₀ : z∈S₀ ⇒ z∈E
    b1 = instancie(h_SE, vz)                                 # z∈S₀ ⇒ z∈E
    # branche U : z∈U ⇒ z∈E∖S₀ ⇒ z∈E  (AXIOME_DIFF, conjoint gauche)
    hU = N.assume(appartient(vz, vU))
    z_diff = N.modus_ponens(hU, instancie(corps_incl, vz))   # z∈E∖S₀
    car_diff = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF), vE), vS), vz)
    z_in_E = conjonction_elim_gauche(
        N.modus_ponens(z_diff, equivalence_avant(car_diff))) # z∈E
    b2 = N.loi_deduction(appartient(vz, vU), z_in_E)         # z∈U ⇒ z∈E
    z_E = cas(disj, b1, b2)                                  # z∈E
    return N.generalisation("z", N.loi_deduction(appartient(vz, Z), z_E))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.38-42 | PDF p.151  (« donc Card(S₀)=Card(E) » : la négation du strict, l'extension ne laissant pas 𝔟<𝔞)
def negation_strict_sous_maximal_reunion(E_set="E", S="S0", phi0="phi0"):
    """⊢ ¬( Card S₀ < Card E ) sous { bij(φ₀,S₀²,S₀), element_maximal, (S₀,φ₀)∈𝔉,
       est_infini_ensemble(S₀), S₀⊂E, résidus ∀∀ fini_downward }.   [Ucadre ÉLIMINÉ].

    STEP B2 ABOUTI (cf. en-tête + journal « ANATOMIE COMPLÈTE DE B2 »)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_produits_disjoints import (
        inter_vide_depuis_disjonction, carre_disjoint_cadre_reunion,
        _flip_disjonction, _disj_forme,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_produit_union_carre import (
        s0sq_cadre_reunion_egale_carre,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_extension_z_infini import (
        z_infini_derive, cadre_card_trois_b_reunion,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
        U_disjoint_S0,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_extension import (
        complement_grand,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_maximal_card import (
        maximal_carre_egal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_descentes_inconditionnelles import (
        deux_b_egal_b_inconditionnel,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
        est_cardinal_de_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.realisation_segment.ensembles_transport_sous_ensemble import (
        existe_sous_ensemble_cardinal_transporte,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_comparabilite import (
        comparabilite_cardinaux,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
        fini_zero,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
        est_infini_ensemble,
    )
    vE, vS, vphi0 = _t(E_set), _t(S), _t(phi0)
    U = "Ucadre"
    vU = var(U)
    b = cardinal(vS)                                         # 𝔟 = Card S₀
    cE = cardinal(vE)
    diff = E.difference(vE, vS)
    Z = E.reunion(vS, vU)
    SxS = E.produit(vS, vS)
    SxU, UxS, UxU = E.produit(vS, vU), E.produit(vU, vS), E.produit(vU, vU)
    F_r = E.reunion(SxU, E.reunion(UxS, UxU))
    marqueur = _marqueur_faux(E_set)

    # ════════ B1' (réunion) : marqueur sous les 12 hyps ════════
    b1 = negation_strict_sous_temoins_UF(E_set, phi0, "psi", S, U, "uwit",
                                         via_reunion=True)

    # ════════ le CORPS du transport, assumé ; ses deux conjoints ════════
    corps = et(inclus(vU, diff), egal(cardinal(vU), b))      # (U⊂E∖S₀) et (Card U=𝔟)
    Hcorps = N.assume(corps)
    Hincl = conjonction_elim_gauche(Hcorps)                  # U ⊂ E∖S₀  (= hyp 6 de B1')
    HcardU = conjonction_elim_droite(Hcorps)                 # Card U = 𝔟

    # maximal-data pelée depuis l'hyp bij(φ₀,S₀²,S₀) de B1'
    bij0 = N.assume(est_bijection_de(vphi0, SxS, vS))
    dom0 = conjonction_elim_droite(conjonction_elim_gauche(bij0))   # dom φ₀ = S₀²
    img0 = conjonction_elim_droite(conjonction_elim_droite(bij0))   # image(φ₀,S₀²)=S₀
    # image(φ₀, dom φ₀) = S₀   (congruence sur le 2e argument puis img0)
    img_dom = composer_egalites(
        N.modus_ponens(dom0, congruence_terme(E.dom(vphi0), SxS,
                                              E.image(vphi0, var("w")))),
        img0)                                                # image(φ₀,domφ₀)=S₀
    IMGt = E.image(vphi0, E.dom(vphi0))

    # disjonction U/S₀ (∀-forme, binder zpd) depuis U⊂E∖S₀
    disjUS = U_disjoint_S0(E_set, S, U, "zpd")               # {U⊂E∖S₀} ⊢ (∀zpd)(∈U⇒¬∈S₀)
    disjUS = _cut(disjUS, Hincl)
    assert disjUS.conclusion == _disj_forme(vU, vS, "zpd")
    flip = _cut(_flip_disjonction(vU, vS, "zpd"), disjUS)    # (∀zpd)(∈S₀⇒¬∈U)

    # trio cardinal : est_cardinal(𝔟) [CLOS], est_infini(𝔟) [hyp propre], 𝔟·𝔟=𝔟 [bij0]
    card_b = est_cardinal_de_cardinal(vS)                    # ⊢ est_cardinal(𝔟)
    h_infS = N.assume(est_infini_ensemble(vS))               # ¬Fini(𝔟)   [hyp propre]
    # 𝔟·𝔟=𝔟 : Card(S₀×S₀)=𝔟·𝔟 (bien-déf capture-safe, réflexivités Card S₀=𝔟)
    #         puis Card(S₀×S₀)=𝔟 (maximal_carre_egal sous bij0) et composition.
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire, produit_cardinal_bien_defini,
    )
    bb = produit_cardinal_binaire(b, b)
    bd_gen = N.generalisation("XX", N.generalisation("YY",
        N.generalisation("AA", N.generalisation("BB",
            produit_cardinal_bien_defini("XX", "YY", "AA", "BB")))))
    bd = instancie(instancie(instancie(instancie(bd_gen, vS), vS), b), b)
    refl_b = N.reflexivite(b)                                # Card S₀ = 𝔟 (même terme)
    card_SxS_eq_bb = N.modus_ponens(
        conjonction_intro(refl_b, refl_b), bd)               # Card(S₀×S₀)=𝔟·𝔟
    mce = _cut(maximal_carre_egal(S, phi0), bij0)            # Card(S₀×S₀)=𝔟  [bij0]
    bb_eq_b = composer_egalites(
        N.modus_ponens(card_SxS_eq_bb, symetrie(cardinal(SxS), bb)), mce)  # 𝔟·𝔟=𝔟

    # ════════ décharges des 9 hyps-Ucadre de B1' ════════
    # (3) s0sq [CLOS]
    d3 = s0sq_cadre_reunion_egale_carre(S, U)
    # (1) inter(imgφ₀dom, U)=∅  ← inter(S₀,U)=∅ + rewrite S₀→imgφ₀dom
    ivSU = _cut(inter_vide_depuis_disjonction(vS, vU, "zpd"), flip)  # inter(S₀,U)=∅
    s6_1 = N.s6(IMGt, vS, "h6r", egal(E.intersection(var("h6r"), vU), E.VIDE))
    d1 = N.modus_ponens(ivSU, equivalence_arriere(N.modus_ponens(img_dom, s6_1)))
    # (2) reunion(imgφ₀dom, U)=Z ← réflexivité + même rewrite
    reflZ = N.reflexivite(Z)                                 # S₀∪U = S₀∪U
    s6_2 = N.s6(IMGt, vS, "h6r", egal(E.reunion(var("h6r"), vU), Z))
    d2 = N.modus_ponens(reflZ, equivalence_arriere(N.modus_ponens(img_dom, s6_2)))
    # (5) (∀u)¬(u∈domφ₀ ∧ u∈F_r) ← L5[u="u"] + rewrite S₀²→domφ₀
    L5 = _cut(carre_disjoint_cadre_reunion(S, U, "u", "zpd"), disjUS)
    s6_5 = N.s6(E.dom(vphi0), SxS, "h6r",
                pourtout("u", non(et(appartient(var("u"), var("h6r")),
                                     appartient(var("u"), F_r)))))
    d5 = N.modus_ponens(L5, equivalence_arriere(
        N.modus_ponens(dom0, s6_5)))
    # (4) Card F_r = Card U ← L4 (Card F_r=𝔟) + 𝔟=Card U
    L4 = _cut(cadre_card_trois_b_reunion(S, U, "zpd", "upd"),
              N.modus_ponens(HcardU, symetrie(cardinal(vU), b)),  # 𝔟=Card U ✗ forme CardS=CardU
              bb_eq_b, card_b, h_infS, disjUS)
    d4 = composer_egalites(L4, N.modus_ponens(HcardU, symetrie(cardinal(vU), b)))
    # (7) Z⊂E ← corps + S₀⊂E [hyp propre]
    d7 = _Z_inclus_E(vS, vU, vE, Hincl)
    # (8) Z infini ← L-inf
    d8 = z_infini_derive(S, U)                               # hyps : infS + ∀∀-résidus
    d8 = _cut(d8, h_infS)
    # (9) Card U ≠ Card ∅ ← Card U=𝔟 + ¬Fini(𝔟) + Fini(Card ∅)
    c_vide = cardinal(E.VIDE)
    h_eq0 = N.assume(egal(cardinal(vU), c_vide))             # Card U=Card∅  [à réfuter]
    b_eq_0 = composer_egalites(
        N.modus_ponens(HcardU, symetrie(cardinal(vU), b)), h_eq0)   # 𝔟=Card∅
    fz = fini_zero()                                         # ⊢ Fini(Card ∅) (forme à vérifier)
    s6_9 = N.s6(b, c_vide, "h6r", est_fini(var("h6r")))
    fini_b = N.modus_ponens(fz, equivalence_arriere(
        N.modus_ponens(b_eq_0, s6_9)))                       # Fini(𝔟)
    fx9 = _exfalso_vers(h_infS, fini_b, marqueur)            # marqueur [h_eq0,…]
    d9 = N.modus_ponens(
        N.modus_ponens(N.reflexivite(vE), dni(egal(vE, vE))),
        contraposition(N.loi_deduction(egal(cardinal(vU), c_vide), fx9)))  # ¬(CardU=Card∅)

    # ════════ toutes les décharges dans B1' ════════
    cur = _cut(b1, d1, d2, d3, d4, d5, Hincl, d7, d8, d9)
    # seule hyp-Ucadre licite restante : le CORPS lui-même (déchargé juste après).
    reste_uc = [h for h in cur.hypotheses
                if "Ucadre" in libres_f(h) and h != corps]
    assert not reste_uc, \
        "B2 : hyps-Ucadre résiduelles après décharges :\n" + "\n".join(map(str, reste_uc))

    # ════════ éliminer Ucadre ════════
    imp_corps = N.loi_deduction(corps, cur)                  # corps ⇒ marqueur
    imp_ex = existe_elimination(imp_corps, U)                # (∃Ucadre corps) ⇒ marqueur

    # ════════ AMONT : 𝔟<Card E ⇒ ∃U(corps) ════════
    h_lt = N.assume(inf_strict_card(b, cE))                  # 𝔟 < Card E   [à réfuter]
    h_SE = N.assume(inclus(vS, vE))                          # S₀⊂E   [hyp propre]
    bb2 = N.modus_ponens(conjonction_intro(conjonction_intro(
        card_b, h_infS), bb_eq_b), _deux_b(b))               # 𝔟+𝔟=𝔟
    cg = _cut(complement_grand(E_set, S), h_SE, bb2, h_lt)   # ¬(Card(E∖S₀) ≤ 𝔟)
    # comparabilité (CLOSE) instanciée (Card(E∖S₀), 𝔟) puis retournement
    comp = comparabilite_cardinaux()                          # inf(X,Y) ∨ inf(Y,X)
    comp = instancie(instancie(
        N.generalisation("X", N.generalisation("Y", comp)), cardinal(diff)), b)
    le_b_diff = cas(comp,
                    N.modus_ponens(cg, N.s2(non(inf_egal_card(cardinal(diff), b)),
                                            inf_egal_card(b, cardinal(diff)))),
                    a_implique_a(inf_egal_card(b, cardinal(diff))))
    # transport : (est_cardinal(𝔟) ∧ 𝔟 ≤ Card(E∖S₀)) ⇒ ∃VE(corps_VE)
    tr = existe_sous_ensemble_cardinal_transporte(b, diff)
    ex_VE = N.modus_ponens(conjonction_intro(card_b, le_b_diff), tr)
    corps_VE = et(inclus(var("VE"), diff), egal(cardinal(var("VE")), b))
    aeq = alpha_existe("VE", U, corps_VE)                    # (∃VE) ⇔ (∃Ucadre)
    ex_U = N.modus_ponens(ex_VE, equivalence_avant(aeq))     # (∃Ucadre)(corps)

    # ════════ falsum sous 𝔟<Card E, puis négation ════════
    fx = N.modus_ponens(ex_U, imp_ex)                        # marqueur
    res = N.modus_ponens(
        N.modus_ponens(N.reflexivite(vE), dni(egal(vE, vE))),
        contraposition(N.loi_deduction(inf_strict_card(b, cE), fx)))

    cible = non(inf_strict_card(b, cE))
    assert res.conclusion == cible, "B2 : conclusion ≠ ¬(𝔟<Card E)"
    for h in res.hypotheses:
        assert "Ucadre" not in libres_f(h), f"B2 : hyp Ucadre résiduelle\n{h}"
    assert res.conclusion not in res.hypotheses, "B2 : VACUOUS"
    return res


def _deux_b(b_terme):
    """⊢ (est_cardinal(𝔟) ∧ est_infini(𝔟) ∧ 𝔟·𝔟=𝔟) ⇒ 𝔟+𝔟=𝔟, instancié au terme 𝔟."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_descentes_inconditionnelles import (
        deux_b_egal_b_inconditionnel,
    )
    base = deux_b_egal_b_inconditionnel("bzi")
    return instancie(N.generalisation("bzi", base), b_terme)


__all__ = ["negation_strict_sous_maximal_reunion"]
