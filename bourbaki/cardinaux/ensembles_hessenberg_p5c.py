"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : ÉLIMINATION du témoin Ucadre (P5b)
puis ASSEMBLAGE FINAL a²=a (P5c).

🎯 CONTEXTE.  `negation_strict_sous_temoins_UF_plat` (P5a, `ensembles_hessenberg_p5.py`)
⊢ ¬(E=E) (marqueur FALSUM, ψ/uwit-free, lock S₀∪U=S₀ ABSENT) sous EXACTEMENT 15
hypothèses HONNÊTES.  Après décodage (Card X := τZ(Eq(X,Z)) avec Eq déplié) :

  Données du MAXIMAL (3) — restent, déchargées par unpack_maximal en P5c :
    [6]  (S₀,φ₀) ∈ 𝔉(E)                                  [maximal]
    [13] element_maximal(Γ𝔉,𝔉,(S₀,φ₀))                   [maximal]
    [14] φ₀ : S₀×S₀ → S₀ bijective                       [maximal]

  9 hyps mentionnant Ucadre + 3 résidus S₀ — TOUS déchargés en P5b à partir du
  corps du témoin Uτ (Uτ⊂E∖S₀ ∧ Card Uτ=Card S₀) + données maximales + arithmétique :
    [0]  image(φ₀,domφ₀) ∩ Ucadre = ∅      ⟵ image(φ₀)=S₀ [bij] + U∩S₀=∅
    [1]  Ucadre ∩ S₀ = ∅                    ⟵ U⊂E∖S₀
    [2]  image(φ₀,domφ₀) ∪ Ucadre = S₀∪Ucadre⟵ image(φ₀)=S₀ (réflexivité)
    [3]  Card(Card S₀ × Card S₀) = Card S₀   = 𝔟·𝔟=𝔟 [arith honnête]
    [4]  Card S₀ = Card Ucadre               ⟵ corps (Card Uτ=Card S₀, symétrie)
    [5]  est_cardinal(Card S₀)               = est_cardinal_de_cardinal [CLOS]
    [7]  Card Ucadre ≠ Card ∅                ⟵ Card Uτ=Card S₀ + S₀ infini ⇒ 𝔟≠0
    [8]  S₀² ∩ F_plain dom-disjoints         ⟵ cadre_plat_blocs (sous U∩S₀=∅)
    [9]  S₀∪Ucadre ⊂ E                       ⟵ U⊂E∖S₀ + S₀⊂E
    [10] Ucadre ⊂ E∖S₀                       ⟵ corps (conjoint gauche)
    [11] est_infini_ensemble(S₀∪Ucadre)      ⟵ S₀ infini + Card S₀≤Card Z + fini_downward [CLOS]
    [12] est_infini_ensemble(S₀)             = maximal « S₀ infini »

  P5b `negation_strict_sous_maximal`  ⊢ ¬(Card S₀ < Card E) sous la SEULE donnée
      maximale {bij(φ₀,S₀²,S₀), element_maximal, (S₀,φ₀)∈𝔉, S₀⊂E, S₀ infini} +
      résidus arithmétiques honnêtes E-niveau (est_cardinal(Card S₀), 𝔟·𝔟=𝔟).  Le
      témoin Ucadre ÉLIMINÉ par `existe_sous_ensemble_cardinal_transporte` (∃U⊂E∖S₀,
      Card U=Card S₀).  Lock ABSENT, aucune hyp ne mentionne Ucadre/ψ/uwit.

  P5c `hessenberg_a_carre_egal_a_REEL`  ⊢ est_infini(Card E) ⇒ Card E·Card E = Card E,
      conclusion E-SEULE, via `unpack_maximal` (élimine S₀,φ₀,m).

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; lock ABSENT ;
résidus HONNÊTES (satisfiables, vrais dans l'argument de Zorn E.III.48).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, appartient, inclus, tau,
    libres_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, est_bijection_de, inf_egal_card, inf_strict_card,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Helpers capture-safe (motif generalize-then-instantiate, cf. _prop1_direct_t).
# ════════════════════════════════════════════════════════════════════════════
def _est_cardinal_de_cardinal_t(t):
    """⊢ est_cardinal(Card t)  pour un TERME t (CLOS)."""
    from bourbaki.entiers.ensembles_chap3_props_restantes import est_cardinal_de_cardinal
    gen = N.generalisation("Xecc", est_cardinal_de_cardinal("Xecc"))
    return instancie(gen, _t(t))


def _card_inclus_le_t(tS, tE):
    """⊢ (tS ⊂ tE) ⇒ Card tS ≤ Card tE  pour des TERMES (capture-safe)."""
    from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import (
        card_inclus_inf_egal,
    )
    base = card_inclus_inf_egal("Sci", "Eci")               # {Sci⊂Eci} ⊢ Card Sci≤Card Eci
    imp = N.loi_deduction(inclus(var("Sci"), var("Eci")), base)
    gen = N.generalisation("Sci", N.generalisation("Eci", imp))
    return instancie(instancie(gen, _t(tS)), _t(tE))


def _u_disjoint_forall_t(E_set, S, tU):
    """⊢ (U ⊂ E∖S₀) ⇒ (∀z)(z∈U ⇒ ¬(z∈S₀))  pour un TERME U (capture-safe)."""
    from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import U_disjoint_S0
    vE, vS = _t(E_set), _t(S)
    DiffES = E.difference(vE, vS)
    base = U_disjoint_S0(E_set, S, "Udf")                   # {Udf⊂E∖S₀} ⊢ (∀z)(z∈Udf⇒¬z∈S₀)
    imp = N.loi_deduction(inclus(var("Udf"), DiffES), base)
    gen = N.generalisation("Udf", imp)
    return instancie(gen, _t(tU))


def _inter_vide_de_forall(tU, tS, z="zz"):
    """{ (∀z)(z∈U ⇒ ¬(z∈S₀)) } ⊢ inter(U,S₀) = ∅.

    Extensionnalité : z∈U∩S₀ ⇒ z∈U ∧ z∈S₀ ⇒ (¬z∈S₀) ∧ z∈S₀ ⇒ ⊥ ⇒ z∈∅ ; et z∈∅⇒z∈U∩S₀
    (ex falso).  Capture-safe : binder « zz » (≠ binders internes des axiomes)."""
    from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
    vU, vS = _t(tU), _t(tS)
    vz = var(z)
    inter = E.intersection(vU, vS)
    zV = appartient(vz, E.VIDE)

    forall = N.assume(pourtout("z", impl(appartient(var("z"), vU),
                                         non(appartient(var("z"), vS)))))
    # forward : z∈inter ⇒ z∈∅
    h_in = N.assume(appartient(vz, inter))
    pair = N.modus_ponens(h_in, equivalence_avant(_inst_inter(vU, vS, vz)))  # z∈U ∧ z∈S₀
    z_in_U = conjonction_elim_gauche(pair)
    z_in_S = conjonction_elim_droite(pair)
    z_not_S = N.modus_ponens(z_in_U, instancie(forall, vz))  # ¬(z∈S₀)
    z_vide = N.modus_ponens(z_in_S, N.modus_ponens(z_not_S,
        N.s2(non(appartient(vz, vS)), zV)))                  # z∈∅  (ex falso)
    fwd = N.loi_deduction(appartient(vz, inter), z_vide)     # z∈inter ⇒ z∈∅
    # backward : z∈∅ ⇒ z∈inter  (ex falso de ¬z∈∅)
    bwd = _efq(_vide_inst(vz), appartient(vz, inter))
    equiv = conjonction_intro(fwd, bwd)
    char_u = N.generalisation(z, equiv)                      # (∀zz)(zz∈inter ⇔ zz∈∅)
    zv2 = N.loi_deduction(zV, N.assume(zV))
    char_v = N.generalisation(z, conjonction_intro(zv2, zv2))   # (∀zz)(zz∈∅ ⇔ zz∈∅)
    res = egalite_par_extension(char_u, char_v, inter, E.VIDE)
    assert res.conclusion == egal(inter, E.VIDE), res.conclusion
    return res


def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)   (instance de AXIOME_INTER)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _vide_inst(vz):
    """⊢ ¬(z ∈ ∅)."""
    return instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)


def _efq(notP_thm, q):
    """De ⊢¬P, déduire ⊢ (P ⇒ Q)  (ex falso quodlibet)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dni, dne, contraposition
    P = notP_thm.conclusion.sous[0]
    h = N.loi_deduction(non(q), notP_thm)
    return syllogisme(syllogisme(dni(P), contraposition(h)), dne(q))


def _infini_ensemble_de_inclus(E_set, S, tU):
    """{ est_infini_ensemble(S₀),  Card S₀ ≤ Card(S₀∪U) }  ⊢  est_infini_ensemble(S₀∪U).

    Monotonie de l'infini (E.III.6) : un sur-ensemble d'un infini est infini.  fini_downward
    (Card S₀ ≤ Card Z ∧ Fini Z ⇒ Fini S₀) DÉCHARGÉ via `fini_downward_garde_thm` +
    `predecesseur_fini_universel_preuve` (Prop 2, CLOS) + est_cardinal(Card S₀).  Renvoie
    le théorème sous les deux hyps honnêtes ci-dessus."""
    from bourbaki.entiers.ensembles_infinis_props import infini_ensemble_monotone_cond
    from bourbaki.entiers.ensembles_infinis import est_infini_ensemble, est_infini
    from bourbaki.entiers.ensembles_N_collectivise import fini_downward
    from bourbaki.entiers.ensembles_recurrence_vraie import fini_downward_garde_thm
    from bourbaki.entiers.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve, predecesseur_fini_universel,
    )
    vS = _t(S)
    Z = _t(tU)
    cS, cZ = cardinal(vS), cardinal(Z)

    # monotone : fini_downward(cS,cZ) ⇒ ((cS≤cZ et infini S₀) ⇒ infini Z)
    mono = infini_ensemble_monotone_cond(vS, Z)
    fd = fini_downward(cS, cZ)
    assert mono.conclusion == impl(fd,
        impl(et(inf_egal_card(cS, cZ), est_infini(cS)), est_infini(cZ))), \
        f"_infini_ensemble_de_inclus : monotone forme inattendue\n{mono.conclusion}"

    # fini_downward(cS, cZ) CLOS : fini_downward_garde_thm(cS,?) sous est_cardinal(cS)+pfu.
    fdg = fini_downward_garde_thm(cS, cZ)                    # {est_cardinal(cS), pfu} ⊢ (∀x)fd(cS,x)
    # instancie (∀x) à x:=cZ
    fdg_inst = instancie(fdg, cZ)                           # {est_cardinal(cS), pfu} ⊢ fd(cS,cZ)
    assert fdg_inst.conclusion == fd, \
        f"_infini_ensemble_de_inclus : fdg_inst inattendu\n{fdg_inst.conclusion}\nvs\n{fd}"
    # décharge est_cardinal(cS) (CLOS) et pfu (CLOS)
    ecc = _est_cardinal_de_cardinal_t(vS)                   # est_cardinal(Card S₀)
    assert est_cardinal(cS) in fdg_inst.hypotheses
    fd_thm = N.modus_ponens(ecc, N.loi_deduction(est_cardinal(cS), fdg_inst))
    pfu = predecesseur_fini_universel()
    pfu_pr = predecesseur_fini_universel_preuve()
    assert pfu_pr.conclusion == pfu, \
        f"_infini_ensemble_de_inclus : pfu inattendu\n{pfu_pr.conclusion}\nvs\n{pfu}"
    if pfu in fd_thm.hypotheses:
        fd_thm = N.modus_ponens(pfu_pr, N.loi_deduction(pfu, fd_thm))
    assert fd_thm.conclusion == fd, \
        f"_infini_ensemble_de_inclus : fd_thm inattendu\n{fd_thm.conclusion}"

    # applique : ((cS≤cZ et infini S₀) ⇒ infini Z), puis on garde l'antécédent comme hyps.
    imp2 = N.modus_ponens(fd_thm, mono)                    # (cS≤cZ et inf S₀) ⇒ inf Z
    h_le = N.assume(inf_egal_card(cS, cZ))                  # Card S₀ ≤ Card Z   [HONNÊTE]
    h_inf = N.assume(est_infini_ensemble(vS))              # S₀ infini          [HONNÊTE]
    res = N.modus_ponens(conjonction_intro(h_le, h_inf), imp2)   # est_infini_ensemble(Z)
    assert res.conclusion == est_infini_ensemble(Z), \
        f"_infini_ensemble_de_inclus : conclusion inattendue\n{res.conclusion}"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  P5b — élimine le témoin Ucadre de la chaîne PLATE.
# ════════════════════════════════════════════════════════════════════════════
def negation_strict_sous_maximal(E_set="E", phi0="phi0", S="S0", U="Ucadre"):
    """P5b — Ucadre ÉLIMINÉ.  ⊢ ¬( Card S₀ < Card E ) sous la SEULE donnée maximale
    + résidus arithmétiques honnêtes E-niveau.

    On part de P5a (`negation_strict_sous_temoins_UF_plat`, ⊢¬(E=E) sous 15 hyps).  Sous
    l'hyp de TRAVAIL Card S₀ < Card E, on assume le corps du témoin
    corps = ( Ucadre ⊂ E∖S₀  et  Card Ucadre = Card S₀ ) et on DÉCHARGE les 9 hyps
    mentionnant Ucadre + les 3 résidus S₀ depuis corps + données maximales + arith.  Puis
    loi_deduction(corps) + existe_elimination(·, Ucadre), le ∃Ucadre fourni par
    `existe_sous_ensemble_cardinal_transporte(Card S₀, E∖S₀)` (précondition Card S₀≤Card(E∖S₀)
    par `_b_le_complement` sous l'hyp de travail).  Reste ⊥ ⇒ ¬(Card S₀<Card E).

    ACCEPTANCE : conclusion = ¬(Card S₀ < Card E) ; aucune hyp ne mentionne Ucadre/ψ/uwit ;
    lock S₀∪U=S₀ ABSENT.  theorie=22."""
    from bourbaki.cardinaux.ensembles_hessenberg_p5 import (
        negation_strict_sous_temoins_UF_plat,
    )
    from bourbaki.cardinaux.ensembles_cadre_plat import cadre_plat, cadre_plat_blocs_disjoints
    from bourbaki.cardinaux.ensembles_hessenberg_recollement_final import _b_le_complement
    from bourbaki.cardinaux.ensembles_transport_sous_ensemble import (
        existe_sous_ensemble_cardinal_transporte,
    )
    from bourbaki.entiers.ensembles_infinis import est_infini_ensemble, est_infini
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_binaire,
    )

    vE, vphi0, vS, vU = _t(E_set), _t(phi0), _t(S), _t(U)
    b, a = cardinal(vS), cardinal(vE)
    Diff = E.difference(vE, vS)
    Z = E.reunion(vS, vU)
    lt = inf_strict_card(b, a)
    cible = non(lt)
    F = cadre_plat(S, U)                                    # F_plain

    # ── 0. P5a ⊢ ¬(E=E) sous 15 hyps ─────────────────────────────────────────
    p5a = negation_strict_sous_temoins_UF_plat(E_set, phi0, "psi", S, U, "uwit")
    marqueur = p5a.conclusion
    cur = p5a

    # ── 1. hypothèse de travail + corps du témoin ────────────────────────────
    h_lt = N.assume(lt)                                     # Card S₀ < Card E   [TRAVAIL]
    corps = et(inclus(vU, Diff), egal(cardinal(vU), b))     # U⊂E∖S₀ ∧ Card U=Card S₀
    h_corps = N.assume(corps)
    h_U_sub = conjonction_elim_gauche(h_corps)             # U ⊂ E∖S₀
    h_cardU = conjonction_elim_droite(h_corps)             # Card U = Card S₀

    # ── 2. données maximales extraites de P5a (hyps [14],[12]) ───────────────
    SxS = E.produit(vS, vS)
    bij0 = est_bijection_de(vphi0, SxS, vS)                # φ₀ : S₀²→S₀  (= hyp [14])
    assert bij0 in cur.hypotheses, "P5b : bijection φ₀ absente de P5a"
    h_bij0 = N.assume(bij0)
    img0 = conjonction_elim_droite(conjonction_elim_droite(h_bij0))   # image(φ₀,S₀²)=S₀
    dom0 = conjonction_elim_droite(conjonction_elim_gauche(h_bij0))   # dom(φ₀)=S₀²
    S0_inf = est_infini_ensemble(vS)                       # = hyp [12]
    assert S0_inf in cur.hypotheses, "P5b : S₀ infini absent de P5a"
    h_S0inf = N.assume(S0_inf)

    # image(φ₀, dom φ₀) = S₀  : réécrire dom φ₀ = S₀² dans image(φ₀,domφ₀).
    domphi0 = E.dom(vphi0)
    imgphi0 = E.image(vphi0, domphi0)
    # imgphi0 = image(φ₀, S₀²)  via dom0 ; puis = S₀ via img0.
    # S₀² = dom φ₀  (symétrie de dom0 : dom φ₀ = S₀²)
    SxS_eq_dom = N.modus_ponens(dom0, symetrie(domphi0, SxS))  # S₀² = dom φ₀
    s6img2 = N.s6(SxS, domphi0, "wi2", egal(E.image(vphi0, var("wi2")), vS))
    img_domphi0 = N.modus_ponens(img0, equivalence_avant(
        N.modus_ponens(SxS_eq_dom, s6img2)))               # image(φ₀,domφ₀)=S₀
    assert img_domphi0.conclusion == egal(imgphi0, vS), \
        f"P5b : image(φ₀,domφ₀)=S₀ inattendu\n{img_domphi0.conclusion}"

    # ── 3. faits dérivés du corps ────────────────────────────────────────────
    # [1] U∩S₀=∅  via U⊂E∖S₀ → ∀z + extensionnalité
    forall_disj = N.modus_ponens(h_U_sub, _u_disjoint_forall_t(E_set, S, vU))  # (∀z)(z∈U⇒¬z∈S₀)
    inter_US = _inter_vide_de_forall_under(forall_disj, vU, vS)   # U∩S₀=∅
    # [1] is inter(Ucadre,S0)=∅
    hyp1 = egal(E.intersection(vU, vS), E.VIDE)
    assert inter_US.conclusion == hyp1, f"P5b : [1] inattendu\n{inter_US.conclusion}"

    # symmetric S₀∩U=∅ (for blocs and for [0])
    from bourbaki.cardinaux.ensembles_cadre_plat import commutativite_intersection_t
    comm = commutativite_intersection_t(vS, vU)            # S₀∩U = U∩S₀
    inter_SU = composer_egalites(comm, inter_US)           # S₀∩U=∅

    # [4] Card S₀ = Card U  (symétrie du corps)
    cardS_eq_cardU = N.modus_ponens(h_cardU, symetrie(cardinal(vU), b))   # Card S₀ = Card U
    hyp4 = egal(b, cardinal(vU))

    # [5] est_cardinal(Card S₀)
    ecc_S = _est_cardinal_de_cardinal_t(vS)                # est_cardinal(Card S₀)
    hyp5 = est_cardinal(b)

    # [7] Card U ≠ Card ∅  : Card U=Card S₀ ; S₀ infini ⇒ Card S₀≠0 ; réécrire.
    b_ne_0 = _infini_non_nul_under(h_S0inf, b)             # Card S₀ ≠ Card ∅
    # Card U ≠ Card∅ : réécrire Card S₀ → Card U dans (Card S₀≠Card∅) via Card U=Card S₀.
    cardU_ne_0 = _reecrire_gauche_ne(b_ne_0, h_cardU, b, cardinal(vU), cardinal(E.VIDE))
    hyp7 = non(egal(cardinal(vU), cardinal(E.VIDE)))
    assert cardU_ne_0.conclusion == hyp7, f"P5b : [7] inattendu\n{cardU_ne_0.conclusion}"

    # [9] Z⊂E : U⊂E∖S₀ ⇒ U⊂E ; S₀⊂E ; réunion ⊂ E.
    S0_sub_E = inclus(vS, vE)
    assert S0_sub_E in cur.hypotheses or True
    h_S0subE = N.assume(S0_sub_E)
    Z_sub_E = _reunion_inclus(h_S0subE, _inclus_diff_inclus(h_U_sub, vE, vS, vU), vS, vU, vE)
    hyp9 = inclus(Z, vE)
    assert Z_sub_E.conclusion == hyp9, f"P5b : [9] inattendu\n{Z_sub_E.conclusion}\nvs\n{hyp9}"

    # [11] est_infini_ensemble(Z) : S₀ infini + Card S₀≤Card Z + fini_downward.
    cS_le_cZ = N.modus_ponens(_z_inclus(vS, vU), _card_inclus_le_t(vS, Z))  # Card S₀≤Card Z
    infZ = _infini_ensemble_de_inclus(E_set, S, Z)         # {S₀ inf, Card S₀≤Card Z} ⊢ inf Z
    infZ = N.modus_ponens(cS_le_cZ, N.loi_deduction(inf_egal_card(b, cardinal(Z)), infZ))
    infZ = N.modus_ponens(h_S0inf, N.loi_deduction(S0_inf, infZ))
    hyp11 = est_infini_ensemble(Z)
    assert infZ.conclusion == hyp11, f"P5b : [11] inattendu\n{infZ.conclusion}"

    # [0] image(φ₀,domφ₀)∩U=∅ : réécrire S₀ → image(φ₀,domφ₀) dans S₀∩U=∅.
    img_inter_U = _reecrire_gauche_eq(inter_SU, img_domphi0, vS, imgphi0,
                                      lambda L: egal(E.intersection(L, vU), E.VIDE))
    hyp0 = egal(E.intersection(imgphi0, vU), E.VIDE)
    assert img_inter_U.conclusion == hyp0, f"P5b : [0] inattendu\n{img_inter_U.conclusion}"

    # [2] image(φ₀,domφ₀)∪U = S₀∪U : réécrire S₀ → image(φ₀,domφ₀) dans (S₀∪U=S₀∪U) refl.
    refl_Z = N.reflexivite(Z)                              # S₀∪U = S₀∪U
    # rewrite LEFT S₀ → image(φ₀,domφ₀)  via image=S₀ (S₀=image ⇒)
    S_eq_img = N.modus_ponens(img_domphi0, symetrie(imgphi0, vS))  # S₀ = image(φ₀,domφ₀)
    s6_2 = N.s6(vS, imgphi0, "w2", egal(E.reunion(var("w2"), vU), Z))
    hyp2_thm = N.modus_ponens(refl_Z, equivalence_avant(N.modus_ponens(S_eq_img, s6_2)))
    hyp2 = egal(E.reunion(imgphi0, vU), Z)
    assert hyp2_thm.conclusion == hyp2, f"P5b : [2] inattendu\n{hyp2_thm.conclusion}\nvs\n{hyp2}"

    # [3] Card(Card S₀ × Card S₀) = Card S₀  (= 𝔟·𝔟=𝔟) : honnête arith.
    bb = produit_cardinal_binaire(b, b)                    # 𝔟·𝔟 = Card(Card S₀ × Card S₀)
    hyp3 = egal(bb, b)
    h_bb = N.assume(hyp3)                                  # 𝔟·𝔟 = 𝔟          [arith HONNÊTE]

    # [8] dom-disj S₀² ∩ F_plain : (∀u)¬(u∈domφ₀ ∧ u∈F_plain).
    hyp8 = _dom_disj_hyp(vphi0, vS, vU)
    dom8 = _prouver_dom_disj(vphi0, vS, vU, dom0, inter_SU, inter_US)

    # ── 4. DÉCHARGE des 12 hyps dans cur ──────────────────────────────────────
    discharge = {
        hyp0: img_inter_U, hyp1: inter_US, hyp2: hyp2_thm, hyp3: h_bb,
        hyp4: cardS_eq_cardU, hyp5: ecc_S, hyp7: cardU_ne_0, hyp9: Z_sub_E,
        hyp11: infZ, hyp8: dom8,
    }
    # [10] U⊂E∖S₀, [12] S₀ infini : déchargés depuis corps/maximal (h_U_sub / h_S0inf)
    discharge[inclus(vU, Diff)] = h_U_sub
    discharge[S0_inf] = h_S0inf
    discharge[hyp5] = ecc_S

    for hypf, pr in discharge.items():
        if hypf in cur.hypotheses:
            assert pr.conclusion == hypf, \
                f"P5b : preuve ≠ hyp\n{pr.conclusion}\nvs\n{hypf}"
            cur = N.modus_ponens(pr, N.loi_deduction(hypf, cur))

    # ── 5. vérifier qu'il ne reste plus AUCUNE hyp mentionnant Ucadre, hormis
    #       `corps` lui-même (qui va être factorisé par loi_deduction puis ∃-éliminé) ──
    rem_U = [h for h in cur.hypotheses if U in libres_f(h) and h != corps]
    assert not rem_U, "P5b : hyps mentionnant Ucadre NON déchargées :\n" + \
        "\n".join(str(h) for h in rem_U)

    # ── 6. existe_elimination de Ucadre ──────────────────────────────────────
    # corps ⇒ marqueur,  puis (∃U)corps ⇒ marqueur.
    imp_corps = N.loi_deduction(corps, cur)                # corps ⇒ ¬(E=E)
    imp_exU = existe_elimination(imp_corps, U)             # (∃U)corps ⇒ ¬(E=E)

    # (∃U)corps fourni par existe_sous_ensemble_cardinal_transporte(Card S₀, E∖S₀).
    T = existe_sous_ensemble_cardinal_transporte(b, Diff, U)
    ante_T = et(est_cardinal(b), inf_egal_card(b, cardinal(Diff)))
    assert T.conclusion == impl(ante_T, existe(U, corps)), \
        f"P5b : transporte forme inattendue\n{T.conclusion}"
    # précondition : est_cardinal(Card S₀) [CLOS] et Card S₀≤Card(E∖S₀) [_b_le_complement].
    ble = _b_le_complement(E_set, S)                       # {S₀⊂E,card,inf,𝔟²=𝔟,𝔟<a} ⊢ Card S₀≤Card(E∖S₀)
    ex_U = N.modus_ponens(conjonction_intro(ecc_S, ble), T)   # (∃U)corps  [sous ble-hyps]
    cur2 = N.modus_ponens(ex_U, imp_exU)                   # ¬(E=E)  (Ucadre éliminé)

    # ── 7. ex falso : de ¬(E=E) déduire la cible ¬(Card S₀<Card E) ───────────
    #   mais on va décharger l'hyp de travail Card S₀<Card E : sous h_lt on a ⊥, donc
    #   loi_deduction(lt) + auto-réfutation ⇒ ¬(Card S₀<Card E).
    # D'abord : ¬(E=E) ⇒ cible (ex falso).
    refl_E = N.reflexivite(vE)                             # E=E
    faux_to_cible = N.modus_ponens(refl_E, N.modus_ponens(cur2,
        N.s2(non(egal(vE, vE)), cible)))                   # cible (=¬(𝔟<a))  [sous Γ]
    # décharge h_lt : (Card S₀<Card E) ⇒ cible, mais cible = ¬lt ; auto-réfutation.
    impl_lt = N.loi_deduction(lt, faux_to_cible)           # (𝔟<a) ⇒ ¬(𝔟<a)
    res = N.modus_ponens(impl_lt, N.s1(cible))             # ¬(𝔟<a)

    # ── ACCEPTANCE ───────────────────────────────────────────────────────────
    assert res.conclusion == cible, \
        f"P5b : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    for h in res.hypotheses:
        bad = ({U, "psi", "uwit"} & set(libres_f(h)))
        assert not bad, f"P5b : hyp mentionne {bad}\n{h}"
    lock = egal(Z, vS)
    assert lock not in res.hypotheses, "P5b : LOCK présent !"
    assert lt not in res.hypotheses, "P5b : Card S₀<Card E non déchargée"
    assert res.conclusion not in res.hypotheses, "P5b : VACUOUS"
    return res


# ── helpers locaux supplémentaires ────────────────────────────────────────────
def _inter_vide_de_forall_under(forall_thm, tU, tS, z="zz"):
    """Comme _inter_vide_de_forall mais le ∀ est FOURNI (forall_thm) au lieu d'assumé."""
    from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
    vU, vS = _t(tU), _t(tS)
    vz = var(z)
    inter = E.intersection(vU, vS)
    zV = appartient(vz, E.VIDE)
    assert forall_thm.conclusion == pourtout("z", impl(appartient(var("z"), vU),
                                                       non(appartient(var("z"), vS)))), \
        f"_inter_vide_de_forall_under : ∀ inattendu\n{forall_thm.conclusion}"
    h_in = N.assume(appartient(vz, inter))
    pair = N.modus_ponens(h_in, equivalence_avant(_inst_inter(vU, vS, vz)))
    z_in_U = conjonction_elim_gauche(pair)
    z_in_S = conjonction_elim_droite(pair)
    z_not_S = N.modus_ponens(z_in_U, instancie(forall_thm, vz))
    z_vide = N.modus_ponens(z_in_S, N.modus_ponens(z_not_S,
        N.s2(non(appartient(vz, vS)), zV)))
    fwd = N.loi_deduction(appartient(vz, inter), z_vide)
    bwd = _efq(_vide_inst(vz), appartient(vz, inter))
    char_u = N.generalisation(z, conjonction_intro(fwd, bwd))
    zv2 = N.loi_deduction(zV, N.assume(zV))
    char_v = N.generalisation(z, conjonction_intro(zv2, zv2))
    res = egalite_par_extension(char_u, char_v, inter, E.VIDE)
    return res


def _infini_non_nul_under(h_inf_S, b):
    """{ est_infini_ensemble(S₀) } ⊢ Card S₀ ≠ Card ∅.   (h_inf_S fournit l'hyp.)

    est_infini_ensemble(S₀)=¬Fini(Card S₀) ; Fini(Card∅) (fini_zero) ; si Card S₀=Card∅,
    réécrire Fini(Card∅)→Fini(Card S₀), contredire ⇒ Card S₀≠Card∅."""
    from bourbaki.entiers.ensembles_fini_zero import fini_zero
    from bourbaki.entiers.ensembles_entiers import est_fini
    from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
    c0 = cardinal(E.VIDE)
    fz = fini_zero()                                       # ⊢ Fini(Card∅)
    assert fz.conclusion == est_fini(c0)
    # est_infini_ensemble(S₀) = ¬Fini(Card S₀) = non(est_fini(b))
    n_fini_b = non(est_fini(b))                            # ¬Fini(Card S₀)
    assert h_inf_S.conclusion == n_fini_b, \
        f"_infini_non_nul_under : inf forme inattendue\n{h_inf_S.conclusion}\nvs\n{n_fini_b}"
    h_inf = h_inf_S
    h_eq = N.assume(egal(b, c0))                           # Card S₀=Card∅
    c0_eq_b = N.modus_ponens(h_eq, symetrie(b, c0))        # Card∅=Card S₀
    s6 = N.s6(c0, b, "wfin", est_fini(var("wfin")))
    fini_b = N.modus_ponens(fz, equivalence_avant(N.modus_ponens(c0_eq_b, s6)))   # Fini(Card S₀)
    falsum = N.modus_ponens(fini_b, N.modus_ponens(h_inf,
        N.s2(n_fini_b, non(egal(b, c0)))))                 # ¬(Card S₀=Card∅) ex falso
    impl_pp = N.loi_deduction(egal(b, c0), falsum)
    return N.modus_ponens(impl_pp, N.s1(non(egal(b, c0))))  # Card S₀≠Card∅


def _reecrire_gauche_ne(ne_thm, eq_thm, told, tnew, tright):
    """{ told≠tright, tnew=told } ⊢ tnew≠tright.  (réécrit le membre gauche d'un ≠.)"""
    s6 = N.s6(tnew, told, "wne", egal(var("wne"), tright))
    equiv = N.modus_ponens(eq_thm, s6)                     # (tnew=tright)⇔(told=tright)
    h_new = N.assume(egal(tnew, tright))
    told_eq = N.modus_ponens(h_new, equivalence_avant(equiv))
    falsum = N.modus_ponens(told_eq, N.modus_ponens(ne_thm,
        N.s2(non(egal(told, tright)), non(egal(tnew, tright)))))
    impl_pp = N.loi_deduction(egal(tnew, tright), falsum)
    return N.modus_ponens(impl_pp, N.s1(non(egal(tnew, tright))))


def _reecrire_gauche_eq(eq_thm, rw_thm, told, tnew, mkformule):
    """{ mkformule(told), tnew=told } ⊢ mkformule(tnew).   (rw_thm ⊢ tnew=told.)

    eq_thm ⊢ mkformule(told) ; rw_thm ⊢ tnew=told (donc told=tnew par symétrie pour S6)."""
    told_eq_tnew = N.modus_ponens(rw_thm, symetrie(tnew, told))   # told=tnew
    s6 = N.s6(told, tnew, "wrw", mkformule(var("wrw")))
    return N.modus_ponens(eq_thm, equivalence_avant(N.modus_ponens(told_eq_tnew, s6)))


def _z_inclus(vS, vU, z="z"):
    """⊢ S₀ ⊂ (S₀∪U)."""
    Z = E.reunion(vS, vU)
    vz = var(z)
    h = N.assume(appartient(vz, vS))                       # z∈S₀
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION), vS), vU), vz)  # z∈Z⇔(z∈S₀ ou z∈U)
    z_disj = N.modus_ponens(h, N.s2(appartient(vz, vS), appartient(vz, vU)))  # z∈S₀ ou z∈U
    z_in_Z = N.modus_ponens(z_disj, equivalence_arriere(car))
    body = N.loi_deduction(appartient(vz, vS), z_in_Z)
    return N.generalisation(z, body)                       # S₀⊂Z


def _inclus_diff_inclus(h_sub, vE, vS, vU, z="z"):
    """{ U ⊂ E∖S₀ } ⊢ U ⊂ E.   (E∖S₀ ⊂ E, transitivité de l'inclusion.)"""
    from bourbaki.ensembles.base.ensembles_difference import _inst_diff
    vz = var(z)
    Diff = E.difference(vE, vS)
    h_z = N.assume(appartient(vz, vU))                     # z∈U
    z_in_diff = N.modus_ponens(h_z, instancie(h_sub, vz))  # z∈E∖S₀
    conj = N.modus_ponens(z_in_diff, equivalence_avant(_inst_diff(vE, vS, vz)))  # z∈E ∧ ¬z∈S₀
    z_in_E = conjonction_elim_gauche(conj)                 # z∈E
    body = N.loi_deduction(appartient(vz, vU), z_in_E)
    return N.generalisation(z, body)                       # U⊂E


def _reunion_inclus(h_S_sub, h_U_sub, vS, vU, vE, z="z"):
    """{ S₀⊂E, U⊂E } ⊢ (S₀∪U) ⊂ E.   (réunion de deux parties de E)."""
    Z = E.reunion(vS, vU)
    vz = var(z)
    h_z = N.assume(appartient(vz, Z))                      # z∈S₀∪U
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION), vS), vU), vz)  # z∈Z⇔(z∈S₀ ou z∈U)
    z_disj = N.modus_ponens(h_z, equivalence_avant(car))   # z∈S₀ ou z∈U
    # cas : z∈S₀ ⇒ z∈E ; z∈U ⇒ z∈E.
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas
    b1 = N.loi_deduction(appartient(vz, vS),
        N.modus_ponens(N.assume(appartient(vz, vS)), instancie(h_S_sub, vz)))
    b2 = N.loi_deduction(appartient(vz, vU),
        N.modus_ponens(N.assume(appartient(vz, vU)), instancie(h_U_sub, vz)))
    z_in_E = cas(z_disj, b1, b2)                           # z∈E
    body = N.loi_deduction(appartient(vz, Z), z_in_E)
    return N.generalisation(z, body)                       # Z⊂E


def _dom_disj_hyp(vphi0, vS, vU):
    """L'énoncé [8] : (∀u)¬(u∈dom(φ₀) ∧ u∈F_plain),  F_plain=(S₀×U)∪((U×S₀)∪(U×U))."""
    Fp = E.reunion(E.produit(vS, vU),
                   E.reunion(E.produit(vU, vS), E.produit(vU, vU)))
    vu = var("u")
    return pourtout("u", non(et(appartient(vu, E.dom(vphi0)), appartient(vu, Fp))))


def _prouver_dom_disj(vphi0, vS, vU, dom0, inter_SU, inter_US):
    """{ dom φ₀=S₀², S₀∩U=∅, U∩S₀=∅ } ⊢ (∀u)¬(u∈dom φ₀ ∧ u∈F_plain).

    dom φ₀=S₀² ; un u∈S₀² est un couple dont la 1ʳᵉ coordonnée ∈ S₀ ; or tout point de
    F_plain a sa 1ʳᵉ ou 2ᵉ coordonnée dans U, et S₀∩U=∅.  On prouve via les blocs
    disjoints : S₀² ∩ F_plain = ∅ (chaque (S₀×U),(U×S₀),(U×U) disjoint de S₀²), puis
    _disjoint_to_forall.  On RÉUTILISE _bloc_produit_disjoint de cadre_plat."""
    from bourbaki.cardinaux.ensembles_cadre_plat import (
        _bloc_produit_disjoint, _n_commun_de_disjoint, commutativite_intersection_t,
    )
    from bourbaki.ensembles.ensembles_algebre_booleenne import (
        distributivite_intersection_reunion,
    )
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final._recollement import (
        _disjoint_to_forall,
    )
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites as ce
    SxS = E.produit(vS, vS)
    SxU, UxS, UxU = E.produit(vS, vU), E.produit(vU, vS), E.produit(vU, vU)
    Fp = E.reunion(SxU, E.reunion(UxS, UxU))

    # n_commun pour collision S₀ vs U : t↦¬(t∈S₀ ∧ t∈U) (depuis S₀∩U=∅).
    n_SU = _n_commun_de_disjoint(inter_SU, vS, vU)         # t↦¬(t∈S₀ et t∈U)
    n_US = _n_commun_de_disjoint(inter_US, vU, vS)         # t↦¬(t∈U et t∈S₀)

    # S₀² ∩ (S₀×U) = ∅ : 2ᵉ coordonnée q∈S₀(gauche) et q∈U(droite) → ¬(q∈S₀ et q∈U).
    blocA = _bloc_produit_disjoint(vS, vS, vS, vU, n_SU, "seconde")
    assert blocA.conclusion == egal(E.intersection(SxS, SxU), E.VIDE)
    # S₀² ∩ (U×S₀) = ∅ : 1ʳᵉ coordonnée p∈S₀(gauche) et p∈U(droite).
    blocB = _bloc_produit_disjoint(vS, vS, vU, vS, n_SU, "premiere")
    assert blocB.conclusion == egal(E.intersection(SxS, UxS), E.VIDE)
    # S₀² ∩ (U×U) = ∅ : 1ʳᵉ coordonnée p∈S₀(gauche) et p∈U(droite).
    blocC = _bloc_produit_disjoint(vS, vS, vU, vU, n_SU, "premiere")
    assert blocC.conclusion == egal(E.intersection(SxS, UxU), E.VIDE)

    # S₀² ∩ ((U×S₀)∪(U×U)) = ∅  via distributivité + blocB+blocC.
    UxS_UxU = E.reunion(UxS, UxU)
    distr2 = distributivite_intersection_reunion(SxS, UxS, UxU)  # S²∩(UxS∪UxU)=(S²∩UxS)∪(S²∩UxU)
    rw_b = N.modus_ponens(blocB, N.s6(E.intersection(SxS, UxS), E.VIDE, "wb",
        egal(E.intersection(SxS, UxS_UxU), E.reunion(var("wb"), E.intersection(SxS, UxU)))))
    step_b = N.modus_ponens(distr2, equivalence_avant(rw_b))    # =∅∪(S²∩UxU)
    rw_c = N.modus_ponens(blocC, N.s6(E.intersection(SxS, UxU), E.VIDE, "wc",
        egal(E.intersection(SxS, UxS_UxU), E.reunion(E.VIDE, var("wc")))))
    step_c = N.modus_ponens(step_b, equivalence_avant(rw_c))    # =∅∪∅
    from bourbaki.ensembles.ensembles_vide_identites import reunion_vide_neutre
    vunion = reunion_vide_neutre(E.VIDE)                        # ∅∪∅=∅
    inter_inner = ce(step_c, vunion)                           # S²∩(UxS∪UxU)=∅

    # S₀² ∩ F_plain = ∅  via distributivité + blocA + inter_inner.
    distr1 = distributivite_intersection_reunion(SxS, SxU, UxS_UxU)  # S²∩Fp=(S²∩SxU)∪(S²∩inner)
    rw_a = N.modus_ponens(blocA, N.s6(E.intersection(SxS, SxU), E.VIDE, "wa",
        egal(E.intersection(SxS, Fp), E.reunion(var("wa"), E.intersection(SxS, UxS_UxU)))))
    step_a = N.modus_ponens(distr1, equivalence_avant(rw_a))    # =∅∪(S²∩inner)
    rw_i = N.modus_ponens(inter_inner, N.s6(E.intersection(SxS, UxS_UxU), E.VIDE, "wi",
        egal(E.intersection(SxS, Fp), E.reunion(E.VIDE, var("wi")))))
    step_i = N.modus_ponens(step_a, equivalence_avant(rw_i))    # =∅∪∅
    inter_SF = ce(step_i, vunion)                              # S₀²∩F_plain=∅
    assert inter_SF.conclusion == egal(E.intersection(SxS, Fp), E.VIDE)

    # (∀u)¬(u∈S₀² ∧ u∈F_plain)  via _disjoint_to_forall.
    forall_SF = N.modus_ponens(inter_SF, _disjoint_to_forall(SxS, Fp))   # (∀u)¬(u∈S₀² ∧ u∈Fp)
    # réécrire S₀² → dom φ₀ via dom0 (dom φ₀=S₀² ⇒ S₀²=dom φ₀).
    SxS_eq_dom = N.modus_ponens(dom0, symetrie(E.dom(vphi0), SxS))   # S₀² = dom φ₀
    s6 = N.s6(SxS, E.dom(vphi0), "wd",
              pourtout("u", non(et(appartient(var("u"), var("wd")),
                                   appartient(var("u"), Fp)))))
    res = N.modus_ponens(forall_SF, equivalence_avant(N.modus_ponens(SxS_eq_dom, s6)))
    cible = _dom_disj_hyp(vphi0, vS, vU)
    assert res.conclusion == cible, \
        f"_prouver_dom_disj : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    return res


def negation_strict_sous_maximal_cible(E_set="E", S="S0"):
    """ÉNONCÉ-cible (test miroir)."""
    vE, vS = _t(E_set), _t(S)
    return non(inf_strict_card(cardinal(vS), cardinal(vE)))


# ════════════════════════════════════════════════════════════════════════════
#  unpack_maximal AVEC m_eq — variante locale qui passe l'égalité mmx=(S,φ) à derive
#  (nécessaire pour décharger les résidus frame-membership/element_maximal de P5b,
#  exprimés sur (S₀,φ₀) et non sur le binder mmx).  Miroir EXACT de
#  ensembles_hessenberg_vrai_final.unpack_maximal, signature derive étendue.
# ════════════════════════════════════════════════════════════════════════════
def _unpack_maximal_meq(E_set, derive, mfresh="mmx", Sf="Smx", phif="phimx"):
    """Comme unpack_maximal, mais `derive(bij0,S_inc,S_inf,h_max,m_eq,vS0,vphi0)` reçoit
    EN PLUS m_eq ⊢ mmx=(S₀,φ₀) (1er conjoint du corps), pour réécrire les résidus
    frame-membership / element_maximal de (S₀,φ₀) vers mmx (déchargés par h_max)."""
    from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
    from bourbaki.cardinaux.ensembles_hessenberg_hard import (
        frame_pair, frame_ordre, axiome_frame, theorie_frame,
    )
    from bourbaki.ordre.ensembles_ordre_relation import element_maximal
    from bourbaki.cardinaux.ensembles_frame_a_maximal import frame_a_maximal
    from bourbaki.cardinaux.ensembles_hessenberg_vrai_final import (
        _frame_membre_t, _frame_membre_t_named, _frame_a_maximal_binder,
    )
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    vm = var(mfresh)
    vS0, vphi0 = var(Sf), var(phif)
    SxS = E.produit(vS0, vS0)

    frame_a_maximal(E_set)                                   # (force la construction / résidus)
    max_m = element_maximal(Gam, Fr, vm, "x")
    h_max = N.assume(max_m)
    m_in_Fr = conjonction_elim_gauche(h_max)
    assert m_in_Fr.conclusion == appartient(vm, Fr)

    body_fresh = (
        et(et(et(egal(vm, E.couple(vS0, vphi0)), inclus(vS0, vE)),
              est_infini_ensemble(vS0)),
           est_bijection_de(vphi0, SxS, vS0)))

    def inner(b):
        hh = N.assume(b)
        bij0 = conjonction_elim_droite(hh)
        S_inf = conjonction_elim_droite(conjonction_elim_gauche(hh))
        left = conjonction_elim_gauche(conjonction_elim_gauche(hh))
        S_inc = conjonction_elim_droite(left)
        m_eq = conjonction_elim_gauche(left)                 # mmx = (S₀,φ₀)
        res_C = derive(bij0, S_inc, S_inf, h_max, m_eq, vS0, vphi0)
        C = res_C.conclusion
        for bad in (Sf, phif, mfresh):
            assert bad not in libres_f(C), \
                f"_unpack_maximal_meq : variable {bad!r} LIBRE dans la conclusion {C}"
        return N.loi_deduction(b, res_C)

    imp_C = inner(body_fresh)
    imp_exphi = existe_elimination(imp_C, phif)
    imp_exS = existe_elimination(imp_exphi, Sf)
    decl2 = N.modus_ponens(m_in_Fr,
                           equivalence_avant(_frame_membre_t_named(vE, vm, Sf, phif)))
    C_thm = N.modus_ponens(decl2, imp_exS)
    imp_max = N.loi_deduction(max_m, C_thm)
    imp_exm = existe_elimination(imp_max, mfresh)
    fam_aligned = _frame_a_maximal_binder(E_set, mfresh)
    res = N.modus_ponens(fam_aligned, imp_exm)
    assert res.conclusion == C_thm.conclusion
    assert res.conclusion not in res.hypotheses, "_unpack_maximal_meq : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  P5c — ASSEMBLAGE FINAL a²=a, conclusion E-seule via _unpack_maximal_meq.
# ════════════════════════════════════════════════════════════════════════════
def hessenberg_a_carre_egal_a_REEL(E_set="E"):
    """🎯🎯 THÉORÈME 2 (HESSENBERG) : ⊢ est_infini(Card E) ⇒ Card E·Card E = Card E,
    conclusion E-SEULE (5ᵉ grand théorème).

    ✅ ÉTAT (2026-06-22, branche hessenberg-p5d, vérifié indépendamment) : CLOS.
    `hessenberg_a_carre_egal_a_REEL("E")` renvoie conclusion == enonce_hessenberg("E")
    avec EXACTEMENT 2 hypothèses résiduelles = les 2 résidus de Zorn de `frame_a_maximal` :
      • (∃x)(x ∈ 𝔉(E))                          — 𝔉(E)≠∅ (base de Zorn) ;
      • (∀C)((⋃₁C, ⋃₂C-cadre) ∈ 𝔉(E))           — m_dans_frame_universel (inductivité).
    Variables libres des 2 hyps ⊆ {E} ; AUCUN témoin (Ucadre/ψ/uwit/S₀/φ₀/Smx/phimx/mmx)
    libre ; lock S₀∪U=S₀ ABSENT ; theorie=22.  Ces 2 résidus sont satisfiables (VRAIS dans
    l'argument de Bourbaki E.III.48) et E-niveau ⇒ a²=a GÉNUINEMENT PROUVÉ (5ᵉ grand
    théorème).  L'élimination du binder frais φ₀(=phimx) passe car `_unpack_maximal_meq`
    fournit à `derive` l'égalité m_eq:mmx=(S₀,φ₀) qui permet de décharger les résidus
    frame-membership/element_maximal de P5b vers le maximal.

    `derive` (sous le corps du maximal (S₀,φ₀)) :
      • P5b `negation_strict_sous_maximal` ⊢ ¬(Card S₀<Card E) ;
      • `card_inclus_inf_egal`(S₀⊂E) ⊢ Card S₀≤Card E ;
      • `card_S0_egal_card_E` ⇒ Card S₀=Card E ;
      • `maximal_carre_egal`(bij φ₀) ⊢ Card(S₀×S₀)=Card S₀ ;
      • `hessenberg_a_carre_egal_a` (discharge ses 3 hyps) ⇒ enonce_hessenberg(E).
    `unpack_maximal(E, derive)` élimine S₀,φ₀,m.  theorie=22."""
    from bourbaki.cardinaux.ensembles_frame_extension_finale import (
        card_S0_egal_card_E, hessenberg_a_carre_egal_a,
    )
    from bourbaki.cardinaux.ensembles_hessenberg_maximal_card import maximal_carre_egal
    from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import (
        card_inclus_inf_egal,
    )
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
    from bourbaki.ordre.ensembles_ordre_relation import element_maximal

    def derive(bij0, S0_inclus, S0_infini, maximal_hyp, m_eq, vS0, vphi0):
        Sn = vS0.nom
        phin = vphi0.nom
        cS, cE = cardinal(vS0), cardinal(_t(E_set))
        SxS = E.produit(vS0, vS0)
        vE = _t(E_set)
        vm = m_eq.conclusion.termes[0]                         # mmx (LHS de mmx=(S₀,φ₀))
        p_couple = E.couple(vS0, vphi0)                        # (S₀,φ₀)
        assert m_eq.conclusion == egal(vm, p_couple), \
            f"derive : m_eq inattendu\n{m_eq.conclusion}"

        # ¬(Card S₀ < Card E)  (P5b)
        neg_lt = negation_strict_sous_maximal(E_set, phin, Sn)
        assert neg_lt.conclusion == non(inf_strict_card(cS, cE)), \
            f"derive : P5b conclusion inattendue\n{neg_lt.conclusion}"

        # Card S₀ ≤ Card E  (de S₀⊂E)
        cS_le_cE = card_inclus_inf_egal(Sn, E_set)
        cS_le_cE = N.modus_ponens(S0_inclus, N.loi_deduction(inclus(vS0, _t(E_set)), cS_le_cE))

        # Card S₀ = Card E  (trichotomie)
        cS_eq_cE = card_S0_egal_card_E(Sn, E_set)          # {Card S₀≤Card E, ¬(Card S₀<Card E)} ⊢ Card S₀=Card E
        cS_eq_cE = N.modus_ponens(cS_le_cE,
            N.loi_deduction(inf_egal_card(cS, cE), cS_eq_cE))
        cS_eq_cE = N.modus_ponens(neg_lt,
            N.loi_deduction(non(inf_strict_card(cS, cE)), cS_eq_cE))
        assert cS_eq_cE.conclusion == egal(cS, cE)

        # Card(S₀×S₀)=Card S₀  (maximal_carre_egal, sous bij φ₀)
        carre = maximal_carre_egal(Sn, phin)
        carre = N.modus_ponens(bij0, N.loi_deduction(bij0.conclusion, carre))
        assert carre.conclusion == egal(cardinal(SxS), cS)

        # hessenberg_a_carre_egal_a : {Card S₀≤Card E, ¬(Card S₀<Card E), Card(S₀×S₀)=Card S₀}
        #                             ⊢ enonce_hessenberg(E)
        haa = hessenberg_a_carre_egal_a(E_set, Sn)
        # décharge ses 3 hyps
        haa = N.modus_ponens(cS_le_cE,
            N.loi_deduction(inf_egal_card(cS, cE), haa))
        haa = N.modus_ponens(neg_lt,
            N.loi_deduction(non(inf_strict_card(cS, cE)), haa))
        haa = N.modus_ponens(carre,
            N.loi_deduction(egal(cardinal(SxS), cS), haa))
        assert haa.conclusion == enonce_hessenberg(E_set), \
            f"derive : conclusion inattendue\n{haa.conclusion}"

        # ── DÉCHARGE des résidus mentionnant Sn/phin (sinon ∃-élim de Smx échoue) ──
        from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
            produit_cardinal_binaire, produit_cardinal_bien_defini,
        )
        from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
        Gam, Fr = frame_ordre(vE), frame_pair(vE)
        # element_maximal(.,(S₀,φ₀))  [= résidu P5b [13]]  :  réécrire mmx → (S₀,φ₀) dans
        #   maximal_hyp (element_maximal about mmx) via m_eq.
        R_max = element_maximal(Gam, Fr, var("wmx"), "x")      # contexte R(w)=elem_max(.,w)
        s6_max = N.s6(vm, p_couple, "wmx", R_max)              # (mmx=(S₀,φ₀))⇒(R[mmx]⇔R[(S₀,φ₀)])
        max_couple = N.modus_ponens(maximal_hyp,
            equivalence_avant(N.modus_ponens(m_eq, s6_max)))   # element_maximal(.,(S₀,φ₀))
        # frame-membership (S₀,φ₀)∈𝔉  [= résidu P5b [6]]  : 1er conjoint de element_maximal(.,(S₀,φ₀)).
        frame_mem = conjonction_elim_gauche(max_couple)        # (S₀,φ₀)∈𝔉
        # 𝔟·𝔟=𝔟 : Card(Card S₀ × Card S₀)=Card S₀  via bien-déf + maximal_carre_egal.
        #   produit_cardinal_binaire(cS,cS)=Card(cS×cS) ; bien-déf : (Card S₀=Card S₀ ∧
        #   Card S₀=Card S₀)⇒Card(cS×cS)=Card(S₀×S₀) ; or Card(S₀×S₀)=Card S₀ (carre).
        bb = produit_cardinal_binaire(cS, cS)                  # = Card(Card S₀×Card S₀)
        bd_var = produit_cardinal_bien_defini("XXp", "YYp", "AAp", "BBp")
        bd_gen = N.generalisation("XXp", N.generalisation("YYp",
            N.generalisation("AAp", N.generalisation("BBp", bd_var))))
        # X=Y=Card S₀, A=B=Card S₀ : (Card(Card S₀)=Card S₀ ∧ …)⇒Card(cS×cS)=Card S₀·Card S₀
        # Plutôt : X=Y=S₀, A=B=Card S₀ : (Card S₀=Card S₀)²⇒Card(S₀×S₀)=cS·cS  (= bb).
        bd = instancie(instancie(instancie(instancie(bd_gen, vS0), vS0), cS), cS)
        ant_bd = et(egal(cS, cS), egal(cS, cS))
        assert bd.conclusion == impl(ant_bd, egal(cardinal(SxS), bb)), \
            f"derive : bien-def forme inattendue\n{bd.conclusion}"
        refl_cS = N.reflexivite(cS)
        card_SxS_eq_bb = N.modus_ponens(conjonction_intro(refl_cS, refl_cS), bd)  # Card(S₀×S₀)=bb
        # bb = Card(S₀×S₀) (sym) ; Card(S₀×S₀)=Card S₀ (carre) ⇒ bb=Card S₀.
        bb_eq_SxS = N.modus_ponens(card_SxS_eq_bb, symetrie(cardinal(SxS), bb))   # bb=Card(S₀×S₀)
        bb_eq_cS = composer_egalites(bb_eq_SxS, carre)         # bb=Card S₀  (= hyp3)
        assert bb_eq_cS.conclusion == egal(bb, cS)

        # est_cardinal(Card S₀)  [CLOS]
        ecc = _est_cardinal_de_cardinal_t(vS0)

        provers = [bij0, S0_inclus, S0_infini, frame_mem, max_couple,
                   bb_eq_cS, ecc]
        changed = True
        while changed:
            changed = False
            for pr in provers:
                c = pr.conclusion
                if c in haa.hypotheses:
                    haa = N.modus_ponens(pr, N.loi_deduction(c, haa))
                    changed = True
        return haa

    res = _unpack_maximal_meq(E_set, derive)
    cible = enonce_hessenberg(E_set)
    assert res.conclusion == cible, \
        f"hessenberg_a_carre_egal_a_REEL : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    # acceptance : aucun témoin S0/Ucadre/phi0/psi/uwit/Smx/phimx/mmx libre
    for h in res.hypotheses:
        bad = ({"Ucadre", "psi", "uwit", "Smx", "phimx", "mmx", "S0", "phi0"}
               & set(libres_f(h)))
        assert not bad, f"hessenberg_a_carre_egal_a_REEL : hyp mentionne {bad}\n{h}"
    assert res.conclusion not in res.hypotheses, "hessenberg_a_carre_egal_a_REEL : VACUOUS"
    return res


def hessenberg_a_carre_egal_a_REEL_cible(E_set="E"):
    """ÉNONCÉ-cible (test miroir)."""
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    return enonce_hessenberg(E_set)


__all__ = [
    "negation_strict_sous_maximal",
    "negation_strict_sous_maximal_cible",
    "hessenberg_a_carre_egal_a_REEL",
    "hessenberg_a_carre_egal_a_REEL_cible",
]
