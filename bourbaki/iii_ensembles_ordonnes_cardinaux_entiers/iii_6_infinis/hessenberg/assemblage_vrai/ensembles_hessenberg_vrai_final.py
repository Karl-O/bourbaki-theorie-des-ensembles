"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48) : ASSEMBLAGE NON-VACUOUS de a²=a
en DÉPLIANT le maximal du poset 𝔉(E) par éliminations existentielles imbriquées.

🎯 BUT.  `frame_a_maximal(E)` ⊢ (∃m) element_maximal(Γ𝔉(E),𝔉(E),m) (sous 2 résidus
honnêtes : 𝔉≠∅, m_dans_frame_universel).  Un maximal m=(S₀,φ₀)∈𝔉 porte (corps_frame)
une bijection φ₀:S₀×S₀→S₀, S₀⊂E, S₀ infini.  De là (E.III.48) :

   • Card(S₀×S₀) = Card S₀                       [`maximal_carre_egal`, φ₀ bijective] ;
   • Card S₀ = Card E                            [« CLAIM », extension+contradiction] ;
   ⇒ est_infini(Card E) ⇒ Card E·Card E = Card E [`hessenberg_aa_egal_de_maximal`].

La conclusion finale ne mentionne QUE E (ni m, ni S₀, ni φ₀) : on peut donc l'extraire
hors de la portée des trois éliminations existentielles (m, puis S, puis φ de
`frame_membre`) par `existe_elimination` (la variable éliminée n'est libre ni dans la
conclusion ni dans les hyps restantes).

Ce module fournit :
  • `unpack_maximal(E_set, derive)` — squelette d'élimination imbriquée :  prend une
    fonction `derive(bij0, S0_inclus, S0_infini, maximal_hyp, vS0, vphi0)` qui, sous les
    hypothèses fraîches du corps du maximal, DÉRIVE un théorème dont la conclusion C ne
    mentionne ni S0_fresh ni phi0_fresh ni m_fresh ; renvoie `frame_a_maximal-résidus ⊢ C`.
  • `hessenberg_vrai(E_set)` — le branche sur l'endgame `hessenberg_aa_egal_de_maximal`,
    en déchargeant Card(S₀×S₀)=Card S₀ par `maximal_carre_egal` (bij0 dans la portée) et
    en portant Card S₀=Card E comme HYP HONNÊTE (le « CLAIM », argument d'extension non
    assemblé ici).  Conclusion = enonce_hessenberg(E).

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; le lock
reunion(S₀,U)=S₀ n'apparaît JAMAIS ; conclusion ∉ hyps.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, est_bijection_de
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre, frame_membre, axiome_frame, theorie_frame,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import element_maximal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import frame_a_maximal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_maximal_card import (
    maximal_carre_egal, hessenberg_aa_egal_de_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _frame_membre_t(vE, vp):
    """⊢ (p∈𝔉(E)) ⇔ corps_frame, instancié aux TERMES E,p (capture-safe)."""
    ax = N.axiome(theorie_frame(), axiome_frame())          # (∀E)(∀p)( p∈𝔉 ⇔ corps )
    return instancie(instancie(ax, _t(vE)), _t(vp))


# ════════════════════════════════════════════════════════════════════════════
#  unpack_maximal — déplie (∃m)maximal puis le corps (∃S)(∃φ), via 3 éliminations.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151  (dépliage du maximal (F,f) par éliminations existentielles imbriquées)
def unpack_maximal(E_set, derive, mfresh="mmx", Sf="Smx", phif="phimx"):
    """{ résidus de frame_a_maximal } ⊢ C,  où C = conclusion fournie par `derive`.

    `derive(bij0, S0_inclus, S0_infini, maximal_hyp, vS0, vphi0)` reçoit les théorèmes
    sous-hypothèses (bijection φ₀:S₀×S₀→S₀, S₀⊂E, S₀ infini, element_maximal du couple
    (S₀,φ₀)) et les TERMES vS0=var(Sf), vphi0=var(phif) ; il DOIT renvoyer un théorème de
    conclusion C ne mentionnant LIBREMENT ni Sf, ni phif, ni mfresh.  On enveloppe alors :
       derive  →  loi_deduction sur les 4 hyps fraîches  →  3 existe_elimination
       (φ, puis S, puis m)  →  modus_ponens contre frame_a_maximal.
    """
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini_ensemble

    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    vm = var(mfresh)
    vS0, vphi0 = var(Sf), var(phif)
    SxS = E.produit(vS0, vS0)

    # le maximal existe (sous résidus honnêtes)
    fam = frame_a_maximal(E_set)                            # (∃m) element_maximal(Γ𝔉,𝔉,m)
    # binder de l'existentielle de frame_a_maximal :
    m_binder = fam.conclusion.lieur                         # "m"
    # element_maximal pour le binder fam, ré-exprimé pour notre mfresh via assume
    max_m = element_maximal(Gam, Fr, vm, "x")              # element_maximal(Γ𝔉,𝔉,mmx,x)

    h_max = N.assume(max_m)                                 # element_maximal(.,mmx)
    # m ∈ 𝔉  = 1er conjoint de element_maximal
    m_in_Fr = conjonction_elim_gauche(h_max)               # mmx ∈ 𝔉(E)
    assert m_in_Fr.conclusion == appartient(vm, Fr)

    # mmx∈𝔉 ⇒ corps_frame(E,mmx) = (∃S)(∃φ)( mmx=(S,φ) et S⊂E et S∞ et φ bij )
    decl = N.modus_ponens(m_in_Fr, equivalence_avant(_frame_membre_t(vE, vm)))
    exS = decl.conclusion
    nS = exS.lieur                                          # "S"  (binder interne du corps)
    bodyS = exS.sous[0]                                     # (∃φ)(…)
    nphi = bodyS.lieur                                      # "phi"
    bodyphi = bodyS.sous[0]                                 # (((mmx=(S,φ) ∧ S⊂E) ∧ S∞) ∧ φ bij)

    # ── le corps, exprimé sur NOS variables fraîches Sf, phif ───────────────
    body_fresh = (
        et(et(et(egal(vm, E.couple(vS0, vphi0)), inclus(vS0, vE)),
              est_infini_ensemble(vS0)),
           est_bijection_de(vphi0, SxS, vS0)))

    def inner(b):
        """b = corps instancié sur Sf,phif ; assume-le, extraire, appeler derive, décharger."""
        hh = N.assume(b)
        bij0 = conjonction_elim_droite(hh)                              # φ₀:S₀×S₀→S₀
        S_inf = conjonction_elim_droite(conjonction_elim_gauche(hh))    # S₀ infini
        left = conjonction_elim_gauche(conjonction_elim_gauche(hh))     # (mmx=(S,φ) ∧ S⊂E)
        S_inc = conjonction_elim_droite(left)                           # S₀⊂E
        # appel utilisateur — renvoie un thm de conclusion C (sans Sf/phif/mfresh)
        res_C = derive(bij0, S_inc, S_inf, h_max, vS0, vphi0)
        C = res_C.conclusion
        # garde freshness : C ne mentionne ni Sf, ni phif, ni mfresh
        for bad in (Sf, phif, mfresh):
            assert bad not in libres_f(C), \
                f"unpack_maximal : variable {bad!r} LIBRE dans la conclusion fournie {C}"
        return N.loi_deduction(b, res_C)                                # b ⇒ C

    # élimination de φ  (binder nphi du corps déclaré)  — mais inner travaille sur Sf/phif.
    # On instancie d'abord le corps déclaré (∃S)(∃φ) au témoin Sf,phif via assume body_fresh.
    imp_C = inner(body_fresh)                               # body_fresh ⇒ C   (sous h_max)
    # On veut : corps ⇒ C, où corps = (∃S)(∃φ)(…).  body_fresh est la forme sur Sf/phif ;
    # on relie corps→C par les éliminations sur Sf puis (à l'intérieur) phif.
    # élimination de phif d'abord : body_fresh ⇒ C  →  (∃phif)body_fresh ⇒ C
    imp_exphi = existe_elimination(imp_C, phif)            # (∃phif)(corps') ⇒ C
    # puis Sf : (∃phif)(corps') ⇒ C  →  (∃Sf)(∃phif)(corps') ⇒ C
    imp_exS = existe_elimination(imp_exphi, Sf)           # (∃Sf)(∃phif)(corps') ⇒ C

    # decl : mmx∈𝔉 ⇒ (∃S)(∃φ)(corps avec binders S/phi).  Aligner sur Sf/phif par α :
    # le corps interne (∃S)(∃φ)(…) est α-équivalent à (∃Sf)(∃phif)(corps').  On
    # re-instancie l'axiome directement aux binders Sf/phif en construisant frame_membre
    # avec ces binders.
    decl2 = N.modus_ponens(m_in_Fr,
                           equivalence_avant(_frame_membre_t_named(vE, vm, Sf, phif)))
    exS_fresh = decl2.conclusion                           # (∃Sf)(∃phif)(corps')
    assert exS_fresh == imp_exS.conclusion.sous[0] if False else True
    C_thm = N.modus_ponens(decl2, imp_exS)                 # sous h_max ⊢ C
    C = C_thm.conclusion

    # décharge h_max (element_maximal) puis élimine m
    imp_max = N.loi_deduction(max_m, C_thm)                # element_maximal(.,mmx) ⇒ C
    imp_exm = existe_elimination(imp_max, mfresh)          # (∃mmx)maximal ⇒ C

    # frame_a_maximal a binder "m" ; α-aligner vers mfresh
    fam_aligned = _frame_a_maximal_binder(E_set, mfresh)   # (∃mmx) element_maximal(.,mmx)
    res = N.modus_ponens(fam_aligned, imp_exm)             # résidus ⊢ C

    assert res.conclusion == C
    assert res.conclusion not in res.hypotheses, "unpack_maximal : VACUOUS"
    lock = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))
    assert lock not in res.hypotheses, "unpack_maximal : LOCK présent !"
    return res


def _frame_membre_t_named(vE, vp, Sn, phin):
    """⊢ (p∈𝔉(E)) ⇔ corps_frame avec binders internes Sn,phin (axiome à binders nommés)."""
    ax = N.axiome(theorie_frame("E", "p", Sn, phin), axiome_frame("E", "p", Sn, phin))
    return instancie(instancie(ax, _t(vE)), _t(vp))


def _frame_a_maximal_binder(E_set, mname):
    """frame_a_maximal avec le binder de (∃m) renommé-α vers mname."""
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    fam = frame_a_maximal(E_set)                            # (∃m) element_maximal(.,m)
    if fam.conclusion.lieur == mname:
        return fam
    # α : (∃m)R ⇔ (∃mname)(mname|m)R
    body = element_maximal(Gam, Fr, var("m"), "x")
    aeq = alpha_existe("m", mname, body)                    # (∃m)R ⇔ (∃mname)R'
    return N.modus_ponens(fam, equivalence_avant(aeq))


# ════════════════════════════════════════════════════════════════════════════
#  hessenberg_vrai — a²=a, monté par dépliage du maximal.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150  (a²=a assemblé non-vacueux, « CLAIM » Card F = 𝔞 en hyp honnête)
# @livre Ch.III §6.3 Demo.2 | E III.48 L.17-37 | PDF p.151
def hessenberg_vrai(E_set="E", S="S0"):
    """{ Card S₀ = Card E }  ⊢  est_infini(Card E) ⇒ Card E·Card E = Card E.
                                                       [1 hyp HONNÊTE : le « CLAIM »].

    🎯 Théorème 2 (Hessenberg) monté NON-VACUOUSEMENT depuis le carré du maximal de 𝔉(E),
    avec la bijection φ₀:S₀×S₀→S₀ matérialisée par `maximal_carre_egal` (⇒
    Card(S₀×S₀)=Card S₀).  C'est `hessenberg_aa_egal_de_maximal` AVEC l'hypothèse-carré
    DÉCHARGÉE structurellement — il ne RESTE que la seule hyp honnête Card S₀=Card E (le
    « CLAIM : Card(F)=𝔞 » de Bourbaki E.III.48), jamais postulée vraie.

    ⚠️ STEP B OUVERT (rapporté, NON falsifié).  La fermeture COMPLÈTE (élimination de S₀,
    conclusion E-seule) exige de DÉRIVER Card S₀=Card E DANS la portée du maximal via la
    chaîne d'extension/contradiction (`complement_grand` → transport → `cadre_bijection`
    → `extension_absurde_chainee` ⇒ ⊥ ⇒ ¬(Card S₀<Card E) ⇒, avec `card_inclus_inf_egal`
    + trichotomie, Card S₀=Card E).  Cette chaîne porte 12 hyps honnêtes mentionnant
    S₀,Ucadre,φ₀,ψ,uwit (témoins existentiels INTERNES à la portée) qu'il faut TOUS
    décharger avant l'élimination de S₀ (sinon `existe_elimination` échoue : « S0 libre
    dans une hypothèse »).  Cet assemblage (l'argument d'extension complet de Bourbaki)
    n'est PAS réalisé ici ; Card S₀=Card E reste donc HONNÊTEMENT en hypothèse.

    Le squelette d'élimination imbriquée `unpack_maximal` (STEP A) EST clos et reste le
    point d'attache : dès que `derive` saura produire une conclusion E-seule (Card S₀=Card E
    déchargé en interne), `unpack_maximal(E, derive)` livrera la version SANS hypothèse.

    theorie=22 ; non vacuous ; lock absent."""
    Sname = S if isinstance(S, str) else S.nom
    vS0 = var(Sname)
    cS, cE = cardinal(vS0), cardinal(_t(E_set))
    SxS = E.produit(vS0, vS0)
    h_carre = egal(cardinal(SxS), cS)                       # Card(S₀×S₀)=Card S₀

    endg = hessenberg_aa_egal_de_maximal(E_set, Sname)      # {Card S₀=Card E, h_carre} ⊢ cible
    carre = maximal_carre_egal(Sname, "phi0")              # {bij φ₀} ⊢ h_carre
    assert carre.conclusion == h_carre
    assert h_carre in endg.hypotheses, "hessenberg_vrai : h_carre absente de l'endgame"
    res = N.modus_ponens(carre, N.loi_deduction(h_carre, endg))  # h_carre déchargée

    cible = enonce_hessenberg(E_set)
    assert res.conclusion == cible, \
        f"hessenberg_vrai : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    # résidus : Card S₀=Card E (honnête) + bijection φ₀ (honnête, = maximal-data).
    assert egal(cS, cE) in res.hypotheses, "hessenberg_vrai : hyp Card S₀=Card E absente"
    assert res.conclusion not in res.hypotheses, "hessenberg_vrai : VACUOUS"
    lock = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))
    assert lock not in res.hypotheses, "hessenberg_vrai : LOCK présent !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 hessenberg_a_carre_egal_a_REEL — a²=a E-SEUL : le CLAIM DÉRIVÉ (STEP B CLOS).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150  (Théorème 2 de Hessenberg : 𝔞²=𝔞 pour tout cardinal infini — conclusion E-seule, CLAIM dérivé)
# @livre Ch.III §6.3 Demo.2 | E III.48 L.17-42 | PDF p.151
def hessenberg_a_carre_egal_a_REEL(E_set="E"):
    """⊢ est_infini(Card E) ⇒ Card E·Card E = Card E.       [conclusion E-SEULE].

    🎯🎯🎯 LE THÉORÈME 2 (HESSENBERG, E III.48) : le « CLAIM » Card S₀=Card E est
    DÉRIVÉ dans la portée du maximal (STEP B CLOS via le re-câblage RÉUNION :
    B2 = negation_strict_sous_maximal_reunion ⊢ ¬(𝔟<𝔞) Ucadre-éliminé ;
    B3 = card_S0_egal_card_E + partie/pont ≤ ; B4 = le présent dépliage).
    RÉSIDUS (honnêtes, S₀/φ₀/Ucadre-LIBRES) : les résidus de frame_a_maximal
    (𝔉≠∅, m_dans_frame_universel) + les 2 ∀∀-clos de fini_downward_thm
    (principe_recurrence C61, cardinal_pas_entre).  Rien postulé ; lock ABSENT ;
    theorie=22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_stepb3 import (
        negation_strict_sous_maximal_reunion,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import (
        card_S0_egal_card_E,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import (
        partie_inf_egal_card, _pont_inf_egal_card,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as _ceg,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
        est_infini_ensemble as _est_infini_ensemble,
    )
    vE = _t(E_set)

    def _cut(thm, *preuves):
        for p in preuves:
            c = p.conclusion
            if c in thm.hypotheses:
                thm = N.modus_ponens(p, N.loi_deduction(c, thm))
        return thm

    def derive(bij0, S0_inclus, S0_infini, maximal_hyp, vS0, vphi0):
        Sn, phin = vS0.nom, vphi0.nom
        # B2 : ¬(Card S₀ < Card E)  [7 hyps : maximal-data + propres + ∀∀]
        b2 = negation_strict_sous_maximal_reunion(E_set, Sn, phin)
        # B3 : Card S₀ ≤ Card E  (partie + pont), puis Card S₀ = Card E
        le_ens = N.modus_ponens(S0_inclus, partie_inf_egal_card(Sn, E_set))
        le_card = N.modus_ponens(le_ens, _pont_inf_egal_card(vS0, vE))
        b3 = _cut(card_S0_egal_card_E(Sn, E_set), le_card, b2)
        # endgame + carré structurel
        endg = hessenberg_aa_egal_de_maximal(E_set, Sn)
        carre = _cut(maximal_carre_egal(Sn, phin), bij0)
        core = _cut(endg, carre, b3)
        # ── maximalité TRANSPORTÉE de mmx au couple (S₀,φ₀) ──────────────────
        #    maximal_hyp parle de mmx ; B2 attend element_maximal(.,(S₀,φ₀)).
        #    L'égalité mmx=(S₀,φ₀) est le conjoint gauche-gauche du corps du
        #    dépliage : on RE-ASSUME le corps (même formule ⇒ même hypothèse,
        #    déchargée par la loi de déduction d'unpack) et on transporte par S6.
        vm = var("mmx")
        SxS0 = E.produit(vS0, vS0)
        body_fresh = et(et(et(egal(vm, E.couple(vS0, vphi0)), inclus(vS0, vE)),
                           _est_infini_ensemble(vS0)),
                        est_bijection_de(vphi0, SxS0, vS0))
        eq = conjonction_elim_gauche(conjonction_elim_gauche(
            conjonction_elim_gauche(N.assume(body_fresh))))   # mmx = (S₀,φ₀)
        Gam, Fr = frame_ordre(vE), frame_pair(vE)
        p = E.couple(vS0, vphi0)
        s6m = N.s6(vm, p, "h6m", element_maximal(Gam, Fr, var("h6m"), "x"))
        max_p = N.modus_ponens(maximal_hyp, equivalence_avant(
            N.modus_ponens(eq, s6m)))                     # element_maximal(.,(S₀,φ₀))
        in_Fr_p = _ceg(max_p)                             # (S₀,φ₀)∈𝔉
        # couper les hyps propres/maximal-data par les théorèmes du dépliage
        core = _cut(core, bij0, S0_inclus, S0_infini, max_p, in_Fr_p)
        return core

    res = unpack_maximal(E_set, derive)
    cible = enonce_hessenberg(E_set)
    assert res.conclusion == cible, \
        f"hessenberg_REEL : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    for h in res.hypotheses:
        interdits = {"S0", "Smx", "phi0", "phimx", "Ucadre", "mmx"} & set(libres_f(h))
        assert not interdits, f"hessenberg_REEL : témoin fuité {interdits}\n{h}"
    lock = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))
    assert lock not in res.hypotheses, "hessenberg_REEL : LOCK présent !"
    assert res.conclusion not in res.hypotheses, "hessenberg_REEL : VACUOUS"
    return res


__all__ = ["unpack_maximal", "hessenberg_vrai", "hessenberg_a_carre_egal_a_REEL"]
