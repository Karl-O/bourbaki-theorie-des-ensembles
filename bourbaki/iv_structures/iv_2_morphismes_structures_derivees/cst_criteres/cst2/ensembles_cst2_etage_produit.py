"""§IV.1.2 — CST2, étage × : bijectivité du produit d'applications réelles.

────────────────────────────────────────────────────────────────────────────────
Pendant × de l'étage 𝔓 (ensembles_cst2_briques) : P = produit_app_reelle
(f,g,A,B,xi) = graphe_terme(A×B, (f(pr₁xi), g(pr₂xi)), xi) et
    { func f, dom f=A, func f⁻¹, f⟨A⟩=A',
      func g, dom g=B, func g⁻¹, g⟨B⟩=B' }   ⊢   Q(P, A×B, A'×B')
(8 hyps = Q(f)∪Q(g) moins les conjoints dom, coupables par les 2 IH).
Routes : func P⁻¹ par injectivité POINTWISE (couple (p,f(p))∈f depuis dom,
bascule en f⁻¹, univalence de f⁻¹) + décomposition couple ; image par
(f(pr₁x), g(pr₂x)) ∈ A'×B' (→, valeur-dans-image) et par le témoin (pa,qb)
préimage composante par composante (←, α-renommage des ∃ x→pa/qb).
α-discipline : relais uq/vq/zq/Zq comme à l'étage 𝔓.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
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
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couple_caracterisation import (
    couple_egal_projections,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
    projection_premiere, projection_seconde,
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
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme, graphe_terme_fonctionnel,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonctorialite_produit_termes import (
    pr_dans,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    terme_produit_app,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst2_briques import (
    bijection_q,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _couple_dans_graphe(vf, vA, Hdom, p_t):
    """{p∈A, dom f=A} ⊢ (p, f(p)) ∈ f.   (p TERME ; route dom → AXIOME_DOM.)"""
    hp = N.assume(appartient(p_t, vA))
    p_dom = N.modus_ponens(hp, equivalence_arriere(N.modus_ponens(
        Hdom, N.s6(E.dom(vf), vA, "w", appartient(p_t, var("w"))))))
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    ex = N.modus_ponens(p_dom, equivalence_avant(
        instancie(instancie(dom_ax, vf), p_t)))
    return _cut(valeur_dans_graphe(vf, p_t), ex)


def _inj_point(vf, vA, Hdom, Hrec, pA, qA, feq, p_t, q_t):
    """{…} ⊢ p = q   depuis p,q∈A (thms), f(p)=f(q) (thm), func f⁻¹ (Hrec).

    (p,f(p))∈f et (q,f(q))∈f (dom) → bascule f⁻¹ → transport f(q)↦f(p) →
    univalence de f⁻¹ instanciée (f(p), p, q)."""
    fp, fq = E.valeur(vf, p_t), E.valeur(vf, q_t)
    rp = N.modus_ponens(_cut(_couple_dans_graphe(vf, vA, Hdom, p_t), pA),
                        equivalence_arriere(couple_reciproque(vf, fp, p_t)))
    rq = N.modus_ponens(_cut(_couple_dans_graphe(vf, vA, Hdom, q_t), qA),
                        equivalence_arriere(couple_reciproque(vf, fq, q_t)))
    rq_p = N.modus_ponens(rq, equivalence_arriere(N.modus_ponens(
        feq, N.s6(fp, fq, "w",
                  appartient(E.couple(var("w"), q_t), E.reciproque(vf))))))
    univ = instancie(instancie(instancie(Hrec, fp), p_t), q_t)
    return N.modus_ponens(conjonction_intro(rp, rq_p), univ)


def _proj_forme(t, vA, vB, member_thm):
    """{…} ⊢ t = (pr₁t, pr₂t)   depuis t∈A×B (thm).   (motif identite_produit.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    exn = N.modus_ponens(member_thm, equivalence_avant(
        instancie(instancie(instancie(ax, vA), vB), t)))
    corps = et(et(egal(t, E.couple(var("p"), var("q"))),
                  appartient(var("p"), vA)), appartient(var("q"), vB))
    hb = N.assume(corps)
    eqc = conjonction_elim_gauche(conjonction_elim_gauche(hb))
    j1 = N.modus_ponens(eqc, N.s5(egal(t, E.couple(var("p"), var("b"))),
                                  var("q"), "b"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("b", egal(t, E.couple(var("a"), var("b")))), var("p"), "a"))
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(corps, j2), "q"), "p")
    ec = N.modus_ponens(exn, imp)                          # est_couple(t)
    return N.modus_ponens(ec, equivalence_arriere(couple_egal_projections(t)))


def _val_dans_cible(vf, vA, vAp, Hdom, Himg, p_t):
    """{p∈A, dom f=A, f⟨A⟩=A'} ⊢ f(p) ∈ A'.   (p TERME via relais-α « pv ».)

    Au nom pv : (pv,f(pv))∈f + pv∈A → témoin de f(pv)∈f⟨A⟩ [AXIOME_IMAGE] →
    ∈A' [transport Himg] ; antécédent pv∈A, gen, instancié au terme."""
    vpv = var("pv")
    hp = N.assume(appartient(vpv, vA))
    cpl = _cut(_couple_dans_graphe(vf, vA, Hdom, vpv), hp)
    fpv = E.valeur(vf, vpv)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, vf), vA), fpv)
    body = et(appartient(var("x"), vA), appartient(E.couple(var("x"), fpv), vf))
    ex = N.modus_ponens(conjonction_intro(hp, cpl), N.s5(body, vpv, "x"))
    in_img = N.modus_ponens(ex, equivalence_arriere(car))  # f(pv) ∈ f⟨A⟩
    in_Ap = N.modus_ponens(in_img, equivalence_avant(N.modus_ponens(
        Himg, N.s6(E.image(vf, vA), vAp, "w", appartient(fpv, var("w"))))))
    imp = N.generalisation("pv", N.loi_deduction(appartient(vpv, vA), in_Ap))
    return N.modus_ponens(N.assume(appartient(_t(p_t), vA)), instancie(imp, _t(p_t)))


# @livre Ch.IV §1.2 Crit.CST2 | E IV.2 L.33-34 | PDF p.205  (étage × de CST2 : si f et g sont des bijections A→A', B→B', leur produit est une bijection de A×B sur A'×B' — vocabulaire Q, hyps honnêtes)
def produit_app_bijective_q(f, g, a, b, ap, bp, xi="xg1"):
    """{ Q(f)∖dom, Q(g)∖dom } (8 hyps) ⊢ Q(f×g, A×B, A'×B')."""
    vf, vg = _t(f), _t(g)
    vA, vB, vAp, vBp = _t(a), _t(b), _t(ap), _t(bp)
    AxB, ApxBp = E.produit(vA, vB), E.produit(vAp, vBp)
    T = terme_produit_app(vf, vg, xi)
    P = E.graphe_terme(AxB, T, xi)
    Hf = N.assume(E.est_fonctionnel(vf))
    Hdf = N.assume(egal(E.dom(vf), vA))
    Hrf = N.assume(E.est_fonctionnel(E.reciproque(vf)))
    Hif = N.assume(egal(E.image(vf, vA), vAp))
    Hg = N.assume(E.est_fonctionnel(vg))
    Hdg = N.assume(egal(E.dom(vg), vB))
    Hrg = N.assume(E.est_fonctionnel(E.reciproque(vg)))
    Hig = N.assume(egal(E.image(vg, vB), vBp))

    c1 = graphe_terme_fonctionnel(AxB, T, xi, "y")         # func P        [CLOS]
    c2 = graphe_terme_domaine(AxB, T, xi, "y", "z")        # dom P = A×B  [CLOS]

    def _membre(nu, nv):
        return membre_graphe_terme(AxB, T, nu, nv, xi, "y")

    def _Tde(t):                                           # (f(pr₁t), g(pr₂t))
        return E.couple(E.valeur(vf, E.pr1(t)), E.valeur(vg, E.pr2(t)))

    # ── c3 : func P⁻¹ — cœur aux noms uq/vq/zq, re-liage u/v/z ────────────────
    corps3 = et(appartient(E.couple(var("uq"), var("vq")), E.reciproque(P)),
                appartient(E.couple(var("uq"), var("zq")), E.reciproque(P)))
    h3 = N.assume(corps3)
    d1 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_gauche(h3),
        equivalence_avant(couple_reciproque(P, "uq", "vq"))),
        equivalence_avant(_membre("vq", "uq")))            # vq∈A×B ∧ uq=T[vq]
    d2 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_droite(h3),
        equivalence_avant(couple_reciproque(P, "uq", "zq"))),
        equivalence_avant(_membre("zq", "uq")))
    Tv_Tz = composer_egalites(
        N.modus_ponens(conjonction_elim_droite(d1),
                       symetrie(var("uq"), _Tde(var("vq")))),
        conjonction_elim_droite(d2))                       # T[vq] = T[zq]
    comp = N.modus_ponens(Tv_Tz, couple_egal_implique_composantes(
        E.valeur(vf, E.pr1(var("vq"))), E.valeur(vg, E.pr2(var("vq"))),
        E.valeur(vf, E.pr1(var("zq"))), E.valeur(vg, E.pr2(var("zq")))))
    prv = _cut(pr_dans(var("vq"), vA, vB), conjonction_elim_gauche(d1))
    prz = _cut(pr_dans(var("zq"), vA, vB), conjonction_elim_gauche(d2))
    p_eq = _inj_point(vf, vA, Hdf, Hrf,
                      conjonction_elim_gauche(prv), conjonction_elim_gauche(prz),
                      conjonction_elim_gauche(comp),
                      E.pr1(var("vq")), E.pr1(var("zq")))  # pr₁vq = pr₁zq
    q_eq = _inj_point(vg, vB, Hdg, Hrg,
                      conjonction_elim_droite(prv), conjonction_elim_droite(prz),
                      conjonction_elim_droite(comp),
                      E.pr2(var("vq")), E.pr2(var("zq")))  # pr₂vq = pr₂zq
    fv = _proj_forme(var("vq"), vA, vB, conjonction_elim_gauche(d1))
    fz = _proj_forme(var("zq"), vA, vB, conjonction_elim_gauche(d2))
    e1 = N.modus_ponens(p_eq, congruence_terme(
        E.pr1(var("vq")), E.pr1(var("zq")),
        E.couple(var("w"), E.pr2(var("vq")))))
    e2 = N.modus_ponens(q_eq, congruence_terme(
        E.pr2(var("vq")), E.pr2(var("zq")),
        E.couple(E.pr1(var("zq")), var("w"))))
    v_eq_z = composer_egalites(composer_egalites(composer_egalites(
        fv, e1), e2),
        N.modus_ponens(fz, symetrie(var("zq"),
                                    E.couple(E.pr1(var("zq")), E.pr2(var("zq"))))))
    core3 = N.loi_deduction(corps3, v_eq_z)
    gen3 = N.generalisation("uq", N.generalisation("vq", N.generalisation("zq", core3)))
    re3 = instancie(instancie(instancie(gen3, var("u")), var("v")), var("z"))
    c3 = N.generalisation("u", N.generalisation("v", N.generalisation("z", re3)))
    assert c3.conclusion == E.est_fonctionnel(E.reciproque(P)), "c3 : ≠ func P⁻¹"

    # ── c4 : P⟨A×B⟩ = A'×B' — au nom Zq puis relais-α vers z ─────────────────
    Im = E.image(P, AxB)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, P), AxB), var("Zq"))

    # → : xa∈A×B ∧ (xa,Zq)∈P ⇒ Zq = T[xa] ∈ A'×B'  (témoin α-renommé x→xa :
    #     pr_dans/projections interdisent « x »)
    corps4 = et(appartient(var("x"), AxB), appartient(E.couple(var("x"), var("Zq")), P))
    corps4a = et(appartient(var("xa"), AxB), appartient(E.couple(var("xa"), var("Zq")), P))
    hb = N.assume(corps4a)
    mx = N.modus_ponens(conjonction_elim_droite(hb),
                        equivalence_avant(_membre("xa", "Zq")))
    z_eq = conjonction_elim_droite(mx)                     # Zq = T[xa]
    prx = _cut(pr_dans(var("xa"), vA, vB), conjonction_elim_gauche(hb))
    fpx = _cut(_val_dans_cible(vf, vA, vAp, Hdf, Hif, E.pr1(var("xa"))),
               conjonction_elim_gauche(prx))               # f(pr₁xa) ∈ A'
    gpx = _cut(_val_dans_cible(vg, vB, vBp, Hdg, Hig, E.pr2(var("xa"))),
               conjonction_elim_droite(prx))               # g(pr₂xa) ∈ B'
    Tx_in = N.modus_ponens(conjonction_intro(fpx, gpx), equivalence_arriere(
        couple_dans_produit_ssi(E.valeur(vf, E.pr1(var("xa"))),
                                E.valeur(vg, E.pr2(var("xa"))), vAp, vBp)))
    z_in = N.modus_ponens(Tx_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(var("Zq"), _Tde(var("xa")), "w",
                   appartient(var("w"), ApxBp)))))         # Zq ∈ A'×B'
    fwd_imp = existe_elimination(N.loi_deduction(corps4a, z_in), "xa")
    hZi = N.assume(appartient(var("Zq"), Im))
    ex_a = N.modus_ponens(N.modus_ponens(hZi, equivalence_avant(car)),
                          equivalence_avant(alpha_existe("x", "xa", corps4)))
    fwd = N.loi_deduction(appartient(var("Zq"), Im), N.modus_ponens(ex_a, fwd_imp))

    # ← : Zq∈A'×B' ⇒ témoins p,q puis préimages pa,qb ⇒ (pa,qb) témoin de Im
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    hZp = N.assume(appartient(var("Zq"), ApxBp))
    exn = N.modus_ponens(hZp, equivalence_avant(
        instancie(instancie(instancie(ax_prod, vAp), vBp), var("Zq"))))
    corps_pq = et(et(egal(var("Zq"), E.couple(var("p"), var("q"))),
                     appartient(var("p"), vAp)), appartient(var("q"), vBp))
    hpq = N.assume(corps_pq)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hpq))   # Zq=(p,q)
    p_Ap = conjonction_elim_droite(conjonction_elim_gauche(hpq))
    q_Bp = conjonction_elim_droite(hpq)

    def _ex_preimage(vfn, vAn, vApn, Himgn, pt_thm, pt_terme, frais):
        """{pt∈A'} ⊢ (∃frais)(frais∈A ∧ (frais,pt)∈f).   (A'=f⟨A⟩ + α x→frais.)"""
        in_img = N.modus_ponens(pt_thm, equivalence_arriere(N.modus_ponens(
            Himgn, N.s6(E.image(vfn, vAn), vApn, "w",
                        appartient(pt_terme, var("w"))))))     # pt ∈ f⟨A⟩
        car_f = instancie(instancie(instancie(ax_img, vfn), vAn), pt_terme)
        ex0 = N.modus_ponens(in_img, equivalence_avant(car_f))
        body = et(appartient(var("x"), vAn), appartient(E.couple(var("x"), pt_terme), vfn))
        return N.modus_ponens(ex0, equivalence_avant(alpha_existe("x", frais, body)))

    ex_pa = _ex_preimage(vf, vA, vAp, Hif, p_Ap, var("p"), "pa")
    ex_qb = _ex_preimage(vg, vB, vBp, Hig, q_Bp, var("q"), "qb")
    corps_pa = et(appartient(var("pa"), vA), appartient(E.couple(var("pa"), var("p")), vf))
    corps_qb = et(appartient(var("qb"), vB), appartient(E.couple(var("qb"), var("q")), vg))
    hpa, hqb = N.assume(corps_pa), N.assume(corps_qb)
    xw = E.couple(var("pa"), var("qb"))
    xw_in = N.modus_ponens(conjonction_intro(
        conjonction_elim_gauche(hpa), conjonction_elim_gauche(hqb)),
        equivalence_arriere(couple_dans_produit_ssi("pa", "qb", vA, vB)))
    # T[xw] = (f(pr₁xw), g(pr₂xw)) = (f(pa), g(qb)) = (p, q) = Zq
    pr1_eq = projection_premiere("pa", "qb")               # pr₁(pa,qb) = pa
    pr2_eq = projection_seconde("pa", "qb")
    t1 = N.modus_ponens(pr1_eq, congruence_terme(
        E.pr1(xw), var("pa"),
        E.couple(E.valeur(vf, var("w")), E.valeur(vg, E.pr2(xw)))))
    t2 = N.modus_ponens(pr2_eq, congruence_terme(
        E.pr2(xw), var("qb"),
        E.couple(E.valeur(vf, var("pa")), E.valeur(vg, var("w")))))
    f_pa = _cut(N.modus_ponens(conjonction_elim_droite(hpa),
                               _valeur_de_couple(vf, var("pa"), var("p"))), Hf)
    g_qb = _cut(N.modus_ponens(conjonction_elim_droite(hqb),
                               _valeur_de_couple(vg, var("qb"), var("q"))), Hg)
    t3 = N.modus_ponens(f_pa, congruence_terme(
        E.valeur(vf, var("pa")), var("p"),
        E.couple(var("w"), E.valeur(vg, var("qb")))))
    t4 = N.modus_ponens(g_qb, congruence_terme(
        E.valeur(vg, var("qb")), var("q"),
        E.couple(var("p"), var("w"))))
    Txw_Zq = composer_egalites(composer_egalites(composer_egalites(
        composer_egalites(t1, t2), t3), t4),
        N.modus_ponens(z_pq, symetrie(var("Zq"), E.couple(var("p"), var("q")))))
    z_Txw = N.modus_ponens(Txw_Zq, symetrie(_Tde(xw), var("Zq")))   # Zq = T[xw]
    mg_xw = instancie(instancie(N.generalisation(
        "uq", N.generalisation("vq", _membre("uq", "vq"))), xw), var("Zq"))
    xwZ_P = N.modus_ponens(conjonction_intro(xw_in, z_Txw),
                           equivalence_arriere(mg_xw))     # (xw, Zq) ∈ P
    ex_x = N.modus_ponens(conjonction_intro(xw_in, xwZ_P), N.s5(corps4, xw, "x"))
    z_Im = N.modus_ponens(ex_x, equivalence_arriere(car))  # Zq ∈ Im
    # éliminations : qb, pa, puis q, p
    z_Im = N.modus_ponens(ex_qb, existe_elimination(
        N.loi_deduction(corps_qb, z_Im), "qb"))
    z_Im = N.modus_ponens(ex_pa, existe_elimination(
        N.loi_deduction(corps_pa, z_Im), "pa"))
    z_Im = N.modus_ponens(exn, existe_elimination(existe_elimination(
        N.loi_deduction(corps_pq, z_Im), "q"), "p"))
    bwd = N.loi_deduction(appartient(var("Zq"), ApxBp), z_Im)

    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), ApxBp)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    c4 = egalite_par_extension(thm_u, thm_v, Im, ApxBp, x="z")

    res = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))
    assert res.conclusion == bijection_q(P, AxB, ApxBp), "produit : ≠ Q"
    attendu = {Hf.conclusion, Hdf.conclusion, Hrf.conclusion, Hif.conclusion,
               Hg.conclusion, Hdg.conclusion, Hrg.conclusion, Hig.conclusion}
    assert set(res.hypotheses) <= attendu, "produit : hyps non honnêtes"
    return res


__all__ = ["produit_app_bijective_q"]
