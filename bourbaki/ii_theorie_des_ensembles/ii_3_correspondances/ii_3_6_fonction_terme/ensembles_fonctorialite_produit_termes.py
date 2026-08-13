"""§II.3.6/IV.1.2 — F2-TERMES : (g×g')∘(f×f') = (g∘f)×(g'∘f') en ÉGALITÉ DE TERMES.

────────────────────────────────────────────────────────────────────────────────
LE cas × du critère CST1 (fonctorialité du produit d'applications réel), miroir
de fonctorialite_parties_termes (B3) :

    { est_application(f,A,A'), est_application(f',B,B'),
      est_application(g,A',A''), est_application(g',B',B'') }
      ⊢ produit_app_reelle(g∘f, g'∘f', A, B)
        = composee( produit_app_reelle(g,g',A',B'), produit_app_reelle(f,f',A,B) ).

Assemblage de l'extensionnalité (egalite_graphe_terme, B2 + relais-α) avec les
4 décharges ; briques : composee_est_graphe, composee_fonctionnelle,
dom_composee_borne, graphe_terme_domaine, composition_valeur_t,
produit_app_valeur (points-termes), valeur_dans_codomaine (pont graphe §II.3.4),
composee_valeur_app, projections _proj_t, et le lemme local _pr_dans.
INVARIANT : theorie_ensembles()=22 ; rien postulé ; conventions xg/xk/pw.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.II §2.2 Prop.- | E II.9 L.1-8 | PDF p.60  (les projections d'un élément du produit restent dans les facteurs)
def pr_dans(u, A, B, pw2="pw2", qw2="qw2"):
    """{ u ∈ A×B } ⊢ ( pr₁(u)∈A  et  pr₂(u)∈B ).            [1 hyp, u TERME ok].

    AXIOME_PRODUIT (témoins FRAIS pw2/qw2), injectivité du couple, projections,
    transport S6 — motif dom_composee_borne (sens →)."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        _proj_t,
    )
    vu, vA, vB = _t(u), _t(A), _t(B)
    hu = N.assume(appartient(vu, E.produit(vA, vB)))
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    ex_n = N.modus_ponens(hu, equivalence_avant(
        instancie(instancie(instancie(ax, vA), vB), vu)))    # ∃p∃q(u=(p,q)∧p∈A∧q∈B)
    corps_w = et(et(egal(vu, E.couple(var(pw2), var(qw2))),
                    appartient(var(pw2), vA)), appartient(var(qw2), vB))
    # renommage (p,q)→(pw2,qw2), 2 étages
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import subst_f
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import monotonie_existe
    corps_p_q2 = subst_f(var("p"), pw2, corps_w)
    i1 = monotonie_existe(existe_elimination(
        N.s5(corps_p_q2, var("q"), qw2), "q"), "p")
    i2 = existe_elimination(N.s5(existe(qw2, corps_w), var("p"), pw2), "p")
    ex_w = N.modus_ponens(N.modus_ponens(ex_n, i1), i2)      # ∃pw2∃qw2 corps
    hb = N.assume(corps_w)
    eq_u = conjonction_elim_gauche(conjonction_elim_gauche(hb))     # u=(pw2,qw2)
    p_A = conjonction_elim_droite(conjonction_elim_gauche(hb))
    q_B = conjonction_elim_droite(hb)
    pj1, pj2 = _proj_t(var(pw2), var(qw2))                   # pr₁((pw2,qw2))=pw2 …
    # pr₁(u) = pr₁((pw2,qw2)) = pw2   (congruence sur u=(pw2,qw2) puis pj1)
    c1 = composer_egalites(N.modus_ponens(eq_u, congruence_terme(
        vu, E.couple(var(pw2), var(qw2)), E.pr1(var("w")))), pj1)   # pr₁u=pw2
    c2 = composer_egalites(N.modus_ponens(eq_u, congruence_terme(
        vu, E.couple(var(pw2), var(qw2)), E.pr2(var("w")))), pj2)   # pr₂u=qw2
    pr1_A = N.modus_ponens(p_A, equivalence_arriere(N.modus_ponens(
        c1, N.s6(E.pr1(vu), var(pw2), "h6p", appartient(var("h6p"), vA)))))
    pr2_B = N.modus_ponens(q_B, equivalence_arriere(N.modus_ponens(
        c2, N.s6(E.pr2(vu), var(qw2), "h6p", appartient(var("h6p"), vB)))))
    both = conjonction_intro(pr1_A, pr2_B)
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(corps_w, both), qw2), pw2)
    res = N.modus_ponens(ex_w, imp)
    assert res.conclusion == et(appartient(E.pr1(vu), vA), appartient(E.pr2(vu), vB))
    assert len(res.hypotheses) == 1, "pr_dans : hyps ≠ 1"
    return res


def _cva_t(tg, tf, te, tfp, tgp, point):
    """composee_valeur_app aux TERMES : {est_application(tf,te,tfp),
    est_application(tg,tfp,tgp)} ⊢ (point∈te) ⇒ ((tg∘tf)(point)=tg(tf(point))).

    La brique est NOMS-SEULEMENT : on décharge ses 2 hyps en antécédents,
    on généralise les 6 noms, on instancie aux termes, on ré-assume."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
        composee_valeur_app,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import (
        est_application,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    base = composee_valeur_app("Gcv", "Fcv", "Ecv", "Fpcv", "Gpcv", "ucv")
    hF = est_application(var("Fcv"), var("Ecv"), var("Fpcv"))
    hG = est_application(var("Gcv"), var("Fpcv"), var("Gpcv"))
    imp = N.loi_deduction(hF, N.loi_deduction(hG, base))     # ⊢ hF⇒(hG⇒((u∈E)⇒eq))
    gen = imp
    for nom in ["ucv", "Gpcv", "Fpcv", "Ecv", "Fcv", "Gcv"]:
        gen = N.generalisation(nom, gen)
    inst = gen
    for t in [tg, tf, te, tfp, tgp, point]:
        inst = instancie(inst, _t(t))
    aF = N.assume(est_application(_t(tf), _t(te), _t(tfp)))
    aG = N.assume(est_application(_t(tg), _t(tfp), _t(tgp)))
    return N.modus_ponens(aG, N.modus_ponens(aF, inst))


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (fonctorialité du produit d'applications, ÉGALITÉ DE TERMES — le cas × du critère CST1 réalisé)
def fonctorialite_produit_termes(f="f", g="g", fp="fp", gp="gp",
                                 A="A", Ap="Ap", A2="A2",
                                 B="B", Bp="Bp", B2="B2",
                                 xg="xg", pw="pw"):
    """{ est_application(f,A,A'), est_application(f',B,B'),
        est_application(g,A',A''), est_application(g',B',B'') }
      ⊢ produit_app_reelle(g∘f, g'∘f', A, B) = composee(prod_g, prod_f).  [4 hyps]."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        produit_app_reelle, produit_app_fonctionnel, produit_app_valeur,
        terme_produit_app, _proj_t,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_composee_graphe_support import (
        composee_est_graphe, dom_composee_borne,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
        egalite_graphe_terme, hyp_valeurs,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_fonctions_composee import (
        composee_fonctionnelle,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
        composition_valeur_t, composee_valeur_app,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_domaine,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import (
        est_application,
    )
    vf, vg, vfp, vgp = _t(f), _t(g), _t(fp), _t(gp)
    vA, vAp, vB, vBp = _t(A), _t(Ap), _t(B), _t(Bp)
    AxB, ApxBp = E.produit(vA, vB), E.produit(vAp, vBp)
    gf, gpfp = E.composee(vg, vf), E.composee(vgp, vfp)
    prod_f = produit_app_reelle(f, fp, A, B, xg)
    prod_g = produit_app_reelle(g, gp, Ap, Bp, xg)
    G = E.composee(prod_g, prod_f)
    t_cible = terme_produit_app(gf, gpfp, xg)
    vpw = var(pw)
    p1, p2 = E.pr1(vpw), E.pr2(vpw)

    # hyps propres : les 4 applications
    hf = N.assume(est_application(vf, vA, vAp))
    hfp = N.assume(est_application(vfp, vB, vBp))
    hg = N.assume(est_application(vg, vAp, _t(A2)))
    hgp = N.assume(est_application(vgp, vBp, _t(B2)))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    def _val_codom(happ, func_t, dom_t, codom_t, point_in):
        """De est_application + point∈dom : valeur(func_t, point)∈codom."""
        from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import (
            valeur_dans_codomaine,
        )
        pt = point_in.conclusion.termes[0]
        vc = valeur_dans_codomaine(func_t, dom_t, codom_t, pt)
        return _cut(vc,
                    conjonction_elim_droite(happ),                      # f⊂A×A'
                    conjonction_elim_droite(conjonction_elim_gauche(happ)),  # dom f=A
                    point_in)

    # briques CLOSES
    dom_pf = graphe_terme_domaine(AxB, terme_produit_app(f, fp, xg), xg)
    dom_pg = graphe_terme_domaine(ApxBp, terme_produit_app(g, gp, xg), xg)
    func_pf = produit_app_fonctionnel(f, fp, A, B, xg)
    func_pg = produit_app_fonctionnel(g, gp, Ap, Bp, xg)
    fb = N.modus_ponens(conjonction_intro(func_pf, func_pg),
                        composee_fonctionnelle(prod_g, prod_f))         # CLOS

    # ── sous pw∈A×B : les faits de point ──
    hpw = N.assume(appartient(vpw, AxB))
    prs = pr_dans(vpw, vA, vB)                              # {pw∈A×B} ⊢ pr₁∈A ∧ pr₂∈B
    pr1_A = conjonction_elim_gauche(prs)
    pr2_B = conjonction_elim_droite(prs)
    f_p1_Ap = _val_codom(hf, vf, vA, vAp, pr1_A)            # f(pr₁pw)∈A'
    fp_p2_Bp = _val_codom(hfp, vfp, vB, vBp, pr2_B)         # f'(pr₂pw)∈B'
    Kf = E.couple(E.valeur(vf, p1), E.valeur(vfp, p2))
    # Kf ∈ A'×B'  (AXIOME_PRODUIT ⇐, témoins f(pr₁pw)/f'(pr₂pw))
    axp = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT), vAp), vBp), Kf)
    wit = conjonction_intro(conjonction_intro(
        N.reflexivite(Kf), f_p1_Ap), fp_p2_Bp)
    w1 = N.modus_ponens(wit, N.s5(
        et(et(egal(Kf, E.couple(E.valeur(vf, p1), var("q"))), f_p1_Ap.conclusion),
           appartient(var("q"), vBp)), E.valeur(vfp, p2), "q"))
    w2 = N.modus_ponens(w1, N.s5(
        existe("q", et(et(egal(Kf, E.couple(var("p"), var("q"))),
                          appartient(var("p"), vAp)),
                       appartient(var("q"), vBp))), E.valeur(vf, p1), "p"))
    Kf_in = N.modus_ponens(w2, equivalence_arriere(axp))    # Kf∈A'×B'
    # valeur(prod_f, pw) = Kf, puis ∈ dom prod_g
    e_vf = produit_app_valeur(f, fp, A, B, vpw, xg)         # {pw∈A×B} ⊢ prod_f(pw)=Kf
    vKf = E.valeur(prod_f, vpw)
    vf_in_ApBp = N.modus_ponens(Kf_in, equivalence_avant(N.modus_ponens(
        N.modus_ponens(e_vf, symetrie(vKf, Kf)),
        N.s6(Kf, vKf, "h6p", appartient(var("h6p"), ApxBp)))))
    vf_domg = N.modus_ponens(vf_in_ApBp, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_pg, symetrie(E.dom(prod_g), ApxBp)),
        N.s6(ApxBp, E.dom(prod_g), "h6p",
             appartient(vKf, var("h6p"))))))                # prod_f(pw)∈dom prod_g

    # (c) dom(G)=A×B
    borne_dom = N.generalisation(pw, N.loi_deduction(
        appartient(vpw, AxB), vf_domg))
    fc = _cut(dom_composee_borne(prod_g, prod_f, AxB, wd=pw), dom_pf, borne_dom)

    # (d) hyp_valeurs(G) : G(pw)=T[pw]
    pw_dompf = N.modus_ponens(hpw, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_pf, symetrie(E.dom(prod_f), AxB)),
        N.s6(AxB, E.dom(prod_f), "h6p", appartient(vpw, var("h6p"))))))
    ex_f = N.modus_ponens(pw_dompf, equivalence_avant(
        instancie(instancie(ax_dom, prod_f), vpw)))
    ex_g = N.modus_ponens(vf_domg, equivalence_avant(
        instancie(instancie(ax_dom, prod_g), vKf)))
    cv = _cut(composition_valeur_t(prod_g, prod_f, vpw), ex_f, ex_g, fb)
    #    G(pw)=prod_g(prod_f(pw))
    cv2 = N.modus_ponens(cv, equivalence_avant(N.modus_ponens(
        e_vf, N.s6(vKf, Kf, "h6p",
                   egal(E.valeur(G, vpw), E.valeur(prod_g, var("h6p")))))))
    #    G(pw)=prod_g(Kf)
    e_vg = _cut(produit_app_valeur(g, gp, Ap, Bp, Kf, xg), Kf_in)
    #    prod_g(Kf)=couple(g(pr₁Kf), gp(pr₂Kf))
    pj1, pj2 = _proj_t(E.valeur(vf, p1), E.valeur(vfp, p2))
    d1 = N.modus_ponens(pj1, congruence_terme(
        E.pr1(Kf), E.valeur(vf, p1),
        E.couple(E.valeur(vg, var("w")), E.valeur(vgp, E.pr2(Kf)))))
    d2 = N.modus_ponens(pj2, congruence_terme(
        E.pr2(Kf), E.valeur(vfp, p2),
        E.couple(E.valeur(vg, E.valeur(vf, p1)), E.valeur(vgp, var("w")))))
    e_vg2 = composer_egalites(composer_egalites(e_vg, d1), d2)
    #    prod_g(Kf)=couple(g(f(pr₁pw)), gp(fp(pr₂pw)))
    cv3 = composer_egalites(cv2, e_vg2)
    # cible T[pw] = couple((g∘f)(pr₁pw), (gp∘fp)(pr₂pw)) : composee_valeur_app sym ×2
    eq1 = N.modus_ponens(pr1_A, _cut(_cva_t(vg, vf, vA, vAp, _t(A2), p1), hf, hg))
    eq2 = N.modus_ponens(pr2_B, _cut(_cva_t(vgp, vfp, vB, vBp, _t(B2), p2), hfp, hgp))
    u1 = N.modus_ponens(N.modus_ponens(eq1, symetrie(
        E.valeur(gf, p1), E.valeur(vg, E.valeur(vf, p1)))), congruence_terme(
        E.valeur(vg, E.valeur(vf, p1)), E.valeur(gf, p1),
        E.couple(var("w"), E.valeur(vgp, E.valeur(vfp, p2)))))
    u2 = N.modus_ponens(N.modus_ponens(eq2, symetrie(
        E.valeur(gpfp, p2), E.valeur(vgp, E.valeur(vfp, p2)))), congruence_terme(
        E.valeur(vgp, E.valeur(vfp, p2)), E.valeur(gpfp, p2),
        E.couple(E.valeur(gf, p1), var("w"))))
    cv4 = composer_egalites(composer_egalites(cv3, u1), u2)  # G(pw)=T[pw]
    fd = N.generalisation(pw, N.loi_deduction(appartient(vpw, AxB), cv4))
    assert fd.conclusion == hyp_valeurs(G, AxB, t_cible, xg, pw), \
        "F2-termes : hyp_valeurs dérivée ≠ forme attendue"

    # ══ extensionnalité + décharges ══
    base = egalite_graphe_terme(AxB, t_cible, G, xg, pw)
    res = _cut(base, composee_est_graphe(prod_g, prod_f), fb, fc, fd)

    cible = egal(produit_app_reelle(gf, gpfp, A, B, xg), G)
    assert res.conclusion == cible, "F2-termes : conclusion ≠"
    attendues = frozenset({hf.conclusion, hfp.conclusion,
                           hg.conclusion, hgp.conclusion})
    assert res.hypotheses == attendues, \
        "F2-termes : hyps ≠ les est_application attendues (dédupliquées si a==b)"
    return res


__all__ = ["pr_dans", "fonctorialite_produit_termes"]
