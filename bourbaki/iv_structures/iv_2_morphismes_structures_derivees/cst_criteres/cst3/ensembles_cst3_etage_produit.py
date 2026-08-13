"""§IV.1.2 — CST3, étage × : la réciproque du produit d'applications réelles.

────────────────────────────────────────────────────────────────────────────────
    { Q(f)∖dom, Q(g)∖dom }  (8 hyps)
        ⊢  reciproque(produit_app_reelle(f,g,A,B,xi))
             = produit_app_reelle(f⁻¹, g⁻¹, A', B', xi)

Même route B2 que l'étage 𝔓 (G := P⁻¹) ; les décharges est_un_graphe /
func P⁻¹ / dom(P⁻¹)=A'×B' viennent des briques génériques (cst3_etage_parties)
et de Q(P) (cst2).  hyp_valeurs : valeur(P⁻¹,pw) = (f⁻¹(pr₁pw), g⁻¹(pr₂pw))
par `_recip_val` — au point p'∈A' : témoin-préimage pa (alpha_existe x→pa),
f⁻¹(p')=pa (_valeur_de_couple sur f⁻¹) d'où f⁻¹(p')∈A ET f(f⁻¹(p'))=p'
(congruence + _valeur_de_couple sur f) — puis (T'[pw], pw)∈P et bascule.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_bijective_identites_er10 import (
    _valeur_de_couple,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonctorialite_produit_termes import (
    pr_dans,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
    egalite_graphe_terme,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    terme_produit_app, produit_app_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_etage_produit import (
    produit_app_bijective_q, _proj_forme,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_parties import (
    reciproque_est_graphe, dom_reciproque_graphe,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _recip_val(vf, vA, vAp, Hfunc, Hrec, Himg, p_thm, p_t):
    """{p∈A' (thm), …} ⊢ ( f⁻¹(p)∈A  ∧  f(f⁻¹(p))=p ).       (p TERME sans x/pa.)

    p∈A'=f⟨A⟩ [Himg sym S6] → ∃pa(pa∈A ∧ (pa,p)∈f) [AXIOME_IMAGE + α x→pa] ;
    sous pa : (p,pa)∈f⁻¹ → f⁻¹(p)=pa [_valeur_de_couple f⁻¹, Hrec] → les deux
    conjoints par transport S6 / congruence + _valeur_de_couple f (Hfunc)."""
    rf = E.reciproque(vf)
    fip = E.valeur(rf, p_t)                                # f⁻¹(p)
    in_img = N.modus_ponens(p_thm, equivalence_arriere(N.modus_ponens(
        Himg, N.s6(E.image(vf, vA), vAp, "w", appartient(p_t, var("w"))))))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, vf), vA), p_t)
    body = et(appartient(var("x"), vA), appartient(E.couple(var("x"), p_t), vf))
    ex = N.modus_ponens(N.modus_ponens(in_img, equivalence_avant(car)),
                        equivalence_avant(alpha_existe("x", "pa", body)))
    corps = et(appartient(var("pa"), vA), appartient(E.couple(var("pa"), p_t), vf))
    hb = N.assume(corps)
    pa_A = conjonction_elim_gauche(hb)
    pap_f = conjonction_elim_droite(hb)                    # (pa, p) ∈ f
    ppa_r = N.modus_ponens(pap_f, equivalence_arriere(
        couple_reciproque(vf, p_t, var("pa"))))            # (p, pa) ∈ f⁻¹
    val_r = _cut(N.modus_ponens(ppa_r, _valeur_de_couple(rf, p_t, var("pa"))),
                 Hrec)                                     # f⁻¹(p) = pa
    fip_A = N.modus_ponens(pa_A, equivalence_arriere(N.modus_ponens(
        val_r, N.s6(fip, var("pa"), "w", appartient(var("w"), vA)))))
    cong = N.modus_ponens(val_r, congruence_terme(
        fip, var("pa"), E.valeur(vf, var("w"))))           # f(f⁻¹(p)) = f(pa)
    val_f = _cut(N.modus_ponens(pap_f, _valeur_de_couple(vf, var("pa"), p_t)),
                 Hfunc)                                    # f(pa) = p
    both = conjonction_intro(fip_A, composer_egalites(cong, val_f))
    return N.modus_ponens(ex, existe_elimination(
        N.loi_deduction(corps, both), "pa"))


# @livre Ch.IV §1.2 Crit.CST3 | E IV.2 L.35-37 | PDF p.205  (étage × de CST3 : la réciproque du produit de bijections est le produit des réciproques — hyps honnêtes)
def reciproque_produit_app(f, g, a, b, ap, bp, xi="xg1"):
    """{ Q(f)∖dom, Q(g)∖dom } (8 hyps) ⊢ (f×g)⁻¹ = f⁻¹×g⁻¹ (réelles)."""
    vf, vg = _t(f), _t(g)
    vA, vB, vAp, vBp = _t(a), _t(b), _t(ap), _t(bp)
    AxB, ApxBp = E.produit(vA, vB), E.produit(vAp, vBp)
    T = terme_produit_app(vf, vg, xi)
    Tp = terme_produit_app(E.reciproque(vf), E.reciproque(vg), xi)
    P = E.graphe_terme(AxB, T, xi)
    RP = E.reciproque(P)
    Hf = N.assume(E.est_fonctionnel(vf))
    Hdf = N.assume(egal(E.dom(vf), vA))
    Hrf = N.assume(E.est_fonctionnel(E.reciproque(vf)))
    Hif = N.assume(egal(E.image(vf, vA), vAp))
    Hg = N.assume(E.est_fonctionnel(vg))
    Hdg = N.assume(egal(E.dom(vg), vB))
    Hrg = N.assume(E.est_fonctionnel(E.reciproque(vg)))
    Hig = N.assume(egal(E.image(vg, vB), vBp))

    q = produit_app_bijective_q(vf, vg, vA, vB, vAp, vBp, xi)
    rec_P = conjonction_elim_gauche(conjonction_elim_droite(q))   # func P⁻¹
    img_P = conjonction_elim_droite(conjonction_elim_droite(q))   # P⟨A×B⟩=A'×B'
    g1 = reciproque_est_graphe(P)
    d = composer_egalites(dom_reciproque_graphe(AxB, T, xi), img_P)

    # hyp_valeurs : (∀pw)(pw∈A'×B' ⇒ valeur(P⁻¹,pw) = (f⁻¹(pr₁pw), g⁻¹(pr₂pw)))
    vpw = var("pw")
    p1, p2 = E.pr1(vpw), E.pr2(vpw)
    wt = E.couple(E.valeur(E.reciproque(vf), p1), E.valeur(E.reciproque(vg), p2))
    hpw = N.assume(appartient(vpw, ApxBp))
    prs = _cut(pr_dans(vpw, vAp, vBp), hpw)                # pr₁pw∈A' ∧ pr₂pw∈B'
    rf = _recip_val(vf, vA, vAp, Hf, Hrf, Hif, conjonction_elim_gauche(prs), p1)
    rg = _recip_val(vg, vB, vBp, Hg, Hrg, Hig, conjonction_elim_droite(prs), p2)
    wt_in = N.modus_ponens(conjonction_intro(
        conjonction_elim_gauche(rf), conjonction_elim_gauche(rg)),
        equivalence_arriere(couple_dans_produit_ssi(
            E.valeur(E.reciproque(vf), p1), E.valeur(E.reciproque(vg), p2),
            vA, vB)))                                      # wt ∈ A×B
    # pw = (pr₁pw, pr₂pw) = (f(f⁻¹(pr₁pw)), g(g⁻¹(pr₂pw))) = T[wt]
    pf = _proj_forme(vpw, vAp, vBp, hpw)                   # pw = (pr₁pw, pr₂pw)
    e1 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_droite(rf), symetrie(
            E.valeur(vf, E.valeur(E.reciproque(vf), p1)), p1)),
        congruence_terme(p1, E.valeur(vf, E.valeur(E.reciproque(vf), p1)),
                         E.couple(var("w"), p2)))
    e2 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_droite(rg), symetrie(
            E.valeur(vg, E.valeur(E.reciproque(vg), p2)), p2)),
        congruence_terme(p2, E.valeur(vg, E.valeur(E.reciproque(vg), p2)),
                         E.couple(E.valeur(vf, E.valeur(E.reciproque(vf), p1)),
                                  var("w"))))
    # …puis réduire vers T[wt] LITTÉRAL : T[wt] = (f(pr₁wt), g(pr₂wt)) avec
    # pr₁wt NON réduit — projections aux TERMES (gen-inst) + 2 congruences.
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere, projection_seconde,
    )
    u_t, v_t = E.valeur(E.reciproque(vf), p1), E.valeur(E.reciproque(vg), p2)
    pj1 = instancie(instancie(N.generalisation("ua", N.generalisation(
        "va", projection_premiere("ua", "va"))), u_t), v_t)       # pr₁wt = f⁻¹(pr₁pw)
    pj2 = instancie(instancie(N.generalisation("ua", N.generalisation(
        "va", projection_seconde("ua", "va"))), u_t), v_t)
    e3 = N.modus_ponens(N.modus_ponens(pj1, symetrie(E.pr1(wt), u_t)),
                        congruence_terme(u_t, E.pr1(wt),
                                         E.couple(E.valeur(vf, var("w")),
                                                  E.valeur(vg, v_t))))
    e4 = N.modus_ponens(N.modus_ponens(pj2, symetrie(E.pr2(wt), v_t)),
                        congruence_terme(v_t, E.pr2(wt),
                                         E.couple(E.valeur(vf, E.pr1(wt)),
                                                  E.valeur(vg, var("w")))))
    pw_Twt = composer_egalites(composer_egalites(composer_egalites(
        composer_egalites(pf, e1), e2), e3), e4)           # pw = T[wt]
    mg_wt = instancie(instancie(N.generalisation("uq", N.generalisation(
        "vq", membre_graphe_terme(AxB, T, "uq", "vq", xi, "y"))), wt), vpw)
    wtpw_P = N.modus_ponens(conjonction_intro(wt_in, pw_Twt),
                            equivalence_arriere(mg_wt))    # (wt, pw) ∈ P
    pwwt_R = N.modus_ponens(wtpw_P, equivalence_arriere(
        couple_reciproque(P, vpw, wt)))                    # (pw, wt) ∈ P⁻¹
    val = _cut(N.modus_ponens(pwwt_R, _valeur_de_couple(RP, vpw, wt)), rec_P)
    fd = N.generalisation("pw", N.loi_deduction(appartient(vpw, ApxBp), val))

    base = egalite_graphe_terme(ApxBp, Tp, RP, xi, "pw")
    res = _cut(base, g1, rec_P, d, fd)
    res = N.modus_ponens(res, symetrie(E.graphe_terme(ApxBp, Tp, xi), RP))
    cible = egal(RP, produit_app_reelle(E.reciproque(vf), E.reciproque(vg),
                                        vAp, vBp, xi))
    assert res.conclusion == cible, "reciproque_produit_app : ≠ cible"
    attendu = {Hf.conclusion, Hdf.conclusion, Hrf.conclusion, Hif.conclusion,
               Hg.conclusion, Hdg.conclusion, Hrg.conclusion, Hig.conclusion}
    assert set(res.hypotheses) <= attendu, "reciproque_produit_app : hyps"
    return res


__all__ = ["reciproque_produit_app"]
