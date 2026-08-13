"""§IV.1.2 — CST3, étage 𝔓 : la réciproque de l'extension aux parties.

────────────────────────────────────────────────────────────────────────────────
    { func g, dom g=A, func g⁻¹, g⟨A⟩=A' }
        ⊢  reciproque(ext_parties_reelle(g,A,xi)) = ext_parties_reelle(g⁻¹,A',xi)

Route B2 (egalite_graphe_terme, G := F⁻¹) : les 4 décharges sont
  • est_un_graphe(F⁻¹)  — `reciproque_est_graphe` (GÉNÉRIQUE, CLOS : AXIOME_
    RECIP donne z=(p,q), d'où est_couple(z) par S5 y,x — motif _diag_est_graphe) ;
  • est_fonctionnel(F⁻¹) — conjoint c3 de Q (ext_parties_bijective_q) ;
  • dom(F⁻¹) = 𝔓A'      — `dom_reciproque_graphe` (GÉNÉRIQUE, CLOS :
    dom(F⁻¹) = F⟨A⟩ par double extension) composée avec c4 (F⟨𝔓A⟩=𝔓A') ;
  • hyp_valeurs          — valeur(F⁻¹,pw) = g⁻¹⟨pw⟩ par le témoin-préimage
    (motif c4-bwd de l'étage 𝔓 CST2) + _valeur_de_couple sur F⁻¹.
Les 2 briques génériques resservent TELLES QUELLES à l'étage ×.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe, inclus,
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
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    image_image_reciproque_egal_si_surjective, image_reciproque_inclus_domaine,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_bijective_identites_er10 import (
    _valeur_de_couple,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
    egalite_graphe_terme,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    ext_parties_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst2_briques import (
    ext_parties_bijective_q,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def reciproque_est_graphe(G_t):
    """⊢ est_un_graphe(G⁻¹), G TERME.                              [CLOS, 0 hyp]."""
    vG, vz = _t(G_t), var("z")
    RG = E.reciproque(vG)
    car = instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP), vG), vz)
    h = N.assume(appartient(vz, RG))
    ex = N.modus_ponens(h, equivalence_avant(car))
    corps = et(egal(vz, E.couple(var("p"), var("q"))),
               appartient(E.couple(var("q"), var("p")), vG))
    hb = N.assume(corps)
    j1 = N.modus_ponens(conjonction_elim_gauche(hb),
                        N.s5(egal(vz, E.couple(var("p"), var("y"))), var("q"), "y"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("y", egal(vz, E.couple(var("x"), var("y")))), var("p"), "x"))
    ec = N.modus_ponens(ex, existe_elimination(existe_elimination(
        N.loi_deduction(corps, j2), "q"), "p"))
    res = N.generalisation("z", N.loi_deduction(appartient(vz, RG), ec))
    assert res.conclusion == E.est_un_graphe(RG), "reciproque_est_graphe : ≠ cible"
    assert not res.hypotheses, "reciproque_est_graphe : NON clos"
    return res


def dom_reciproque_graphe(a_t, t, xi):
    """⊢ dom(F⁻¹) = F⟨A⟩,   F = graphe_terme(A,T,xi).             [CLOS, 0 hyp].

    Zq∈dom(F⁻¹) ⇔ ∃y(Zq,y)∈F⁻¹ ⇔[α yb] (yb,Zq)∈F, et yb∈A par membre ⇒
    témoin de Zq∈F⟨A⟩ ; réciproque en re-basculant le couple.  Relais Zq→z."""
    vA = _t(a_t)
    F = E.graphe_terme(vA, t, xi)
    RF = E.reciproque(F)
    Im = E.image(F, vA)
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(dom_ax, RF), var("Zq"))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car_img = instancie(instancie(instancie(ax_img, F), vA), var("Zq"))

    def _membre(nu, nv):
        return membre_graphe_terme(vA, t, nu, nv, xi, "y")

    # → : témoin yb : (Zq,yb)∈F⁻¹ ⇒ (yb,Zq)∈F ⇒ yb∈A ⇒ Zq∈F⟨A⟩
    hz = N.assume(appartient(var("Zq"), E.dom(RF)))
    body_y = appartient(E.couple(var("Zq"), var("y")), RF)
    ex_y = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(car_dom)),
                          equivalence_avant(alpha_existe("y", "yb", body_y)))
    corps_yb = appartient(E.couple(var("Zq"), var("yb")), RF)
    hyb = N.assume(corps_yb)
    ybZ_F = N.modus_ponens(hyb, equivalence_avant(
        couple_reciproque(F, "Zq", "yb")))                 # (yb,Zq)∈F
    yb_A = conjonction_elim_gauche(N.modus_ponens(
        ybZ_F, equivalence_avant(_membre("yb", "Zq"))))    # yb∈A
    body_x = et(appartient(var("x"), vA),
                appartient(E.couple(var("x"), var("Zq")), F))
    ex_x = N.modus_ponens(conjonction_intro(yb_A, ybZ_F),
                          N.s5(body_x, var("yb"), "x"))
    z_Im = N.modus_ponens(ex_x, equivalence_arriere(car_img))
    fwd = N.loi_deduction(appartient(var("Zq"), E.dom(RF)), N.modus_ponens(
        ex_y, existe_elimination(N.loi_deduction(corps_yb, z_Im), "yb")))

    # ← : témoin xb : (xb,Zq)∈F ⇒ (Zq,xb)∈F⁻¹ ⇒ ∃y ⇒ Zq∈dom(F⁻¹)
    hi = N.assume(appartient(var("Zq"), Im))
    ex_xb = N.modus_ponens(N.modus_ponens(hi, equivalence_avant(car_img)),
                           equivalence_avant(alpha_existe("x", "xb", body_x)))
    corps_xb = et(appartient(var("xb"), vA),
                  appartient(E.couple(var("xb"), var("Zq")), F))
    hxb = N.assume(corps_xb)
    Zx_R = N.modus_ponens(conjonction_elim_droite(hxb), equivalence_arriere(
        couple_reciproque(F, "Zq", "xb")))                 # (Zq,xb)∈F⁻¹
    ex_y2 = N.modus_ponens(Zx_R, N.s5(body_y, var("xb"), "y"))
    z_dom = N.modus_ponens(ex_y2, equivalence_arriere(car_dom))
    bwd = N.loi_deduction(appartient(var("Zq"), Im), N.modus_ponens(
        ex_xb, existe_elimination(N.loi_deduction(corps_xb, z_dom), "xb")))

    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), Im)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    res = egalite_par_extension(thm_u, thm_v, E.dom(RF), Im, x="z")
    assert res.conclusion == egal(E.dom(RF), Im), "dom_reciproque : ≠ cible"
    assert not res.hypotheses, "dom_reciproque : NON clos"
    return res


# @livre Ch.IV §1.2 Crit.CST3 | E IV.2 L.35-37 | PDF p.205  (étage 𝔓 de CST3 : la réciproque de l'extension aux parties de g est l'extension aux parties de g⁻¹ — hyps honnêtes Q(g)∖dom)
def reciproque_ext_parties(g, a, ap, xi="xg1"):
    """{ func g, dom g=A, func g⁻¹, g⟨A⟩=A' }
        ⊢ reciproque(ext_parties_reelle(g,A,xi)) = ext_parties_reelle(g⁻¹,A',xi)."""
    vg, vA, vAp = _t(g), _t(a), _t(ap)
    PA, PAp = E.parties(vA), E.parties(vAp)
    T = E.image(vg, var(xi))
    Tp = E.image(E.reciproque(vg), var(xi))
    F = E.graphe_terme(PA, T, xi)
    RF = E.reciproque(F)
    Hfunc = N.assume(E.est_fonctionnel(vg))
    Hdom = N.assume(egal(E.dom(vg), vA))
    Hrec = N.assume(E.est_fonctionnel(E.reciproque(vg)))
    Himg = N.assume(egal(E.image(vg, vA), vAp))

    q = ext_parties_bijective_q(vg, vA, vAp, xi)
    rec_F = conjonction_elim_gauche(conjonction_elim_droite(q))   # func F⁻¹
    img_F = conjonction_elim_droite(conjonction_elim_droite(q))   # F⟨𝔓A⟩=𝔓A'
    g1 = reciproque_est_graphe(F)                                 # est_un_graphe(F⁻¹)
    d = composer_egalites(dom_reciproque_graphe(PA, T, xi), img_F)  # dom(F⁻¹)=𝔓A'

    # hyp_valeurs : (∀pw)(pw∈𝔓A' ⇒ valeur(F⁻¹,pw) = g⁻¹⟨pw⟩)   (motif c4-bwd)
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)
    vpw = var("pw")
    wt = E.image(E.reciproque(vg), vpw)
    hpw = N.assume(appartient(vpw, PAp))
    pw_Ap = N.modus_ponens(hpw, equivalence_avant(
        instancie(instancie(ax_p, vAp), vpw)))             # pw ⊂ A'
    pw_gA = N.modus_ponens(pw_Ap, equivalence_avant(N.modus_ponens(
        N.modus_ponens(Himg, symetrie(E.image(vg, vA), vAp)),
        N.s6(vAp, E.image(vg, vA), "w", inclus(vpw, var("w"))))))    # pw ⊂ g⟨A⟩
    wt_sub = N.modus_ponens(Hdom, image_reciproque_inclus_domaine(vg, vpw, vA))
    wt_PA = N.modus_ponens(wt_sub, equivalence_arriere(
        instancie(instancie(ax_p, vA), wt)))               # wt ∈ 𝔓A
    surj = N.modus_ponens(pw_gA, N.modus_ponens(
        Hfunc, image_image_reciproque_egal_si_surjective(vg, vpw, vA)))
    pw_gwt = N.modus_ponens(surj, symetrie(E.image(vg, wt), vpw))    # pw = g⟨wt⟩
    mg_wt = instancie(instancie(N.generalisation("uq", N.generalisation(
        "vq", membre_graphe_terme(PA, T, "uq", "vq", xi, "y"))), wt), vpw)
    wtpw_F = N.modus_ponens(conjonction_intro(wt_PA, pw_gwt),
                            equivalence_arriere(mg_wt))    # (wt, pw) ∈ F
    pwwt_R = N.modus_ponens(wtpw_F, equivalence_arriere(
        couple_reciproque(F, vpw, wt)))                    # (pw, wt) ∈ F⁻¹
    val = _cut(N.modus_ponens(pwwt_R, _valeur_de_couple(RF, vpw, wt)), rec_F)
    fd = N.generalisation("pw", N.loi_deduction(appartient(vpw, PAp), val))

    base = egalite_graphe_terme(PAp, Tp, RF, xi, "pw")
    res = _cut(base, g1, rec_F, d, fd)
    res = N.modus_ponens(res, symetrie(E.graphe_terme(PAp, Tp, xi), RF))
    cible = egal(RF, ext_parties_reelle(E.reciproque(vg), vAp, xi))
    assert res.conclusion == cible, "reciproque_ext_parties : ≠ cible"
    attendu = {Hfunc.conclusion, Hdom.conclusion, Hrec.conclusion, Himg.conclusion}
    assert set(res.hypotheses) <= attendu, "reciproque_ext_parties : hyps non honnêtes"
    return res


__all__ = ["reciproque_est_graphe", "dom_reciproque_graphe", "reciproque_ext_parties"]
