"""§II.3.6 — ÉGALITÉ D'UN GRAPHE DE TERME ET D'UN GRAPHE FONCTIONNEL (extensionnalité).

────────────────────────────────────────────────────────────────────────────────
RÔLE (B2 du chantier CST, cf. journal de campagne).  Pour pousser une identité
de fonctorialité À L'INTÉRIEUR d'un graphe_terme (récurrence du générateur CST1),
il faut l'égalité de TERMES :

    egalite_graphe_terme :
      { est_un_graphe(G),  est_fonctionnel(G),  dom(G) = A,
        (∀pw)( pw∈A ⇒ valeur(G, pw) = T[pw] ) }
        ⊢  graphe_terme(A, T) = G.

ROUTE : extensionnalité (A1) au liant canonique « z » — les DEUX membres sont
caractérisés par LA MÊME formule R = corps de la z-forme C54 (axiome déposé,
abrege:977) : côté graphe_terme c'est l'axiome ; côté G c'est le travail
(est_un_graphe → témoins-couple FRAIS xw/yw → (xw,yw)∈G → xw∈dom G=A →
yw=G(xw)=T[xw] [C46 + hyp-valeurs] → R ; réciproque par valeur_dans_graphe).
MOTIFS : re-nommage de témoins par S5-exotique (ev. 109), existe_elimination
(PAS monotonie, ev. 122), noms-puis-termes.  CONVENTION-x : celle du terme T
(x param, défaut « xg » — ev. 119, une seule convention par terme).
INVARIANT : theorie_ensembles()=22 (l'axiome C54 vit dans sa théorie dédiée).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, subst_t, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe, valeur_caracterisation,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def hyp_valeurs(G, a, t, x="xg", pw="pw"):
    """La FORME d'hypothèse « G vaut T partout sur A » :
        (∀pw)( pw∈A ⇒ valeur(G, pw) = T[pw] )."""
    vpw = var(pw)
    Tp = subst_t(vpw, x, t)
    return pourtout(pw, impl(appartient(vpw, _t(a)),
                             egal(E.valeur(_t(G), vpw), Tp)))


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66  (unicité du graphe de x↦T : tout graphe fonctionnel de domaine A aux mêmes valeurs EST le graphe de terme — extensionnalité)
def egalite_graphe_terme(a, t, G, x="xg", pw="pw", xw="xw", yw="yw", xk="xk"):
    """{ est_un_graphe(G), est_fonctionnel(G), dom(G)=A, hyp_valeurs }
        ⊢ graphe_terme(A, T) = G.                          [4 hyps honnêtes].

    ⚠️ t exprimé dans la variable `x` ; xw/yw/pw frais (∉ liants internes ni t)."""
    vA, vG, vz = _t(a), _t(G), var("z")
    vxw, vyw = var(xw), var(yw)
    F = E.graphe_terme(vA, t, x)
    Txw = subst_t(vxw, x, t)

    # ── thm_u : (∀z)(z∈F ⇔ R) = LA z-forme C54 (axiome dédié, binders x/"y"/z) ──
    thm_u = N.axiome(E.theorie_graphe_terme(vA, t, x, "y", "z"),
                     E.axiome_graphe_terme(vA, t, x, "y", "z"))
    R = thm_u.conclusion.sous[0].sous[1] if False else None  # (doc) R lu ci-dessous
    corps_R = et(et(egal(vz, E.couple(var(x), var("y"))), appartient(var(x), vA)),
                 egal(var("y"), t))
    R = existe(x, existe("y", corps_R))
    # relais α : mêmes corps au binder FRAIS xk (xg est LIBRE dans les termes-graphes
    # consommateurs — l'éliminer serait bloqué ; xk ne l'est jamais)
    t_k = subst_t(var(xk), x, t)
    corps_K = et(et(egal(vz, E.couple(var(xk), var("y"))), appartient(var(xk), vA)),
                 egal(var("y"), t_k))
    R_K = existe(xk, existe("y", corps_K))

    # ── hyps propres ──
    h_graphe = N.assume(E.est_un_graphe(vG))
    h_func = N.assume(E.est_fonctionnel(vG))
    h_dom = N.assume(egal(E.dom(vG), vA))
    h_vals = N.assume(hyp_valeurs(vG, vA, t, x, pw))

    # ══ SENS → : z∈G ⇒ R ══
    hz = N.assume(appartient(vz, vG))
    cpl = N.modus_ponens(hz, instancie(h_graphe, vz))        # ∃x∃y(z=(x,y))
    # témoins FRAIS xw/yw (les canoniques x,y sont pris par R)
    i1 = existe_elimination(N.s5(egal(vz, E.couple(var("x"), vyw)), var("y"), yw), "y")
    i1 = monotonie_existe(i1, "x")                           # ∃x∃y ⇒ ∃x∃yw
    i2 = existe_elimination(N.s5(
        existe(yw, egal(vz, E.couple(vxw, vyw))), var("x"), xw), "x")
    ex_w = N.modus_ponens(N.modus_ponens(cpl, i1), i2)       # ∃xw∃yw(z=(xw,yw))

    body_w = egal(vz, E.couple(vxw, vyw))
    hb = N.assume(body_w)
    cpl_in = N.modus_ponens(hz, equivalence_avant(N.modus_ponens(
        hb, N.s6(vz, E.couple(vxw, vyw), "h6q", appartient(var("h6q"), vG)))))
    #   (xw,yw)∈G
    ex_dom = N.modus_ponens(cpl_in, N.s5(
        appartient(E.couple(vxw, var("y")), vG), vyw, "y"))  # ∃y((xw,y)∈G)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    xw_domG = N.modus_ponens(ex_dom, equivalence_arriere(
        instancie(instancie(ax_dom, vG), vxw)))              # xw∈dom G
    xw_A = N.modus_ponens(xw_domG, equivalence_avant(N.modus_ponens(
        h_dom, N.s6(E.dom(vG), vA, "h6q", appartient(vxw, var("h6q"))))))   # xw∈A
    # yw = G(xw)   (C46, y libre généralisé puis instancié à yw)
    vc = valeur_caracterisation(vG, vxw)                     # ((xw,y)∈G) ⇔ (y=G(xw))
    yw_G = N.modus_ponens(cpl_in, equivalence_avant(
        instancie(N.generalisation("y", vc), vyw)))          # yw=G(xw)
    yw_G = N.modus_ponens(ex_dom, N.loi_deduction(
        existe("y", appartient(E.couple(vxw, var("y")), vG)), yw_G))
    yw_G = N.modus_ponens(h_func, N.loi_deduction(E.est_fonctionnel(vG), yw_G))
    # yw = T[xw]
    G_T = N.modus_ponens(xw_A, instancie(h_vals, vxw))       # G(xw)=T[xw]
    yw_T = composer_egalites(yw_G, G_T)                      # yw=T[xw]
    # R : intro ∃"y" (témoin yw) puis ∃x (témoin xw)
    corps_w = conjonction_intro(conjonction_intro(hb, xw_A), yw_T)
    r1 = N.modus_ponens(corps_w, N.s5(
        et(et(egal(vz, E.couple(vxw, var("y"))), appartient(vxw, vA)),
           egal(var("y"), Txw)), vyw, "y"))
    r2 = N.modus_ponens(r1, N.s5(existe("y", corps_K), vxw, xk))    # R_K
    imp_b = N.loi_deduction(body_w, r2)
    imp_b = existe_elimination(existe_elimination(imp_b, yw), xw)
    fwd = N.loi_deduction(appartient(vz, vG), N.modus_ponens(ex_w, imp_b))
    #     z∈G ⇒ R_K

    # ══ SENS ← : R_K ⇒ z∈G  (témoins = les binders xk,"y", ÉLIMINABLES) ══
    vx, vy = var(xk), var("y")
    hbR = N.assume(corps_K)
    eq_z = conjonction_elim_gauche(conjonction_elim_gauche(hbR))    # z=(x,y)
    x_A = conjonction_elim_droite(conjonction_elim_gauche(hbR))     # x∈A
    y_T = conjonction_elim_droite(hbR)                              # y=T[x]
    G_Tx = N.modus_ponens(x_A, instancie(h_vals, vx))               # G(x)=T[x]
    y_G = composer_egalites(y_T, N.modus_ponens(G_Tx, symetrie(
        E.valeur(vG, vx), subst_t(vx, xk, t_k))))                   # y=G(xk)
    x_domG = N.modus_ponens(x_A, equivalence_arriere(N.modus_ponens(
        h_dom, N.s6(E.dom(vG), vA, "h6q", appartient(vx, var("h6q"))))))  # x∈dom G
    ex_y = N.modus_ponens(x_domG, equivalence_avant(
        instancie(instancie(ax_dom, vG), vx)))                      # ∃y((x,y)∈G)
    xGx = N.modus_ponens(ex_y, N.loi_deduction(
        existe("y", appartient(E.couple(vx, var("y")), vG)),
        valeur_dans_graphe(vG, vx)))                                # (x,G(x))∈G
    xy_in = N.modus_ponens(xGx, equivalence_avant(N.modus_ponens(
        N.modus_ponens(y_G, symetrie(vy, E.valeur(vG, vx))),
        N.s6(E.valeur(vG, vx), vy, "h6q",
             appartient(E.couple(vx, var("h6q")), vG)))))           # (x,y)∈G
    z_in = N.modus_ponens(xy_in, equivalence_arriere(N.modus_ponens(
        eq_z, N.s6(vz, E.couple(vx, vy), "h6q", appartient(var("h6q"), vG)))))
    imp_R = N.loi_deduction(corps_K, z_in)
    bwd = existe_elimination(existe_elimination(imp_R, "y"), xk)    # R_K ⇒ z∈G

    # ══ ponts α : R ⇔ R_K (deux s5+élimination, 0 hyp — xk frais) ══
    b1 = existe_elimination(N.s5(existe("y", corps_K), var(x), xk), x)   # R ⇒ R_K
    b2 = existe_elimination(N.s5(existe("y", corps_R), var(xk), x), xk)  # R_K ⇒ R
    pontRK = conjonction_intro(b1, b2)                              # R ⇔ R_K

    # ══ z∈F ⇔ z∈G, puis A1 (R-témoin trivial z∈G) ══
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_transitivite, equivalence_symetrie,
    )
    eqF = instancie(thm_u, vz)                                      # z∈F ⇔ R
    eqG = conjonction_intro(fwd, bwd)                               # z∈G ⇔ R_K
    chain = equivalence_transitivite(
        equivalence_transitivite(eqF, pontRK), equivalence_symetrie(eqG))
    RG = appartient(vz, vG)
    triv = N.loi_deduction(RG, N.assume(RG))
    thm_u2 = N.generalisation("z", chain)                           # ∀z(z∈F ⇔ z∈G)
    thm_v2 = N.generalisation("z", conjonction_intro(triv, triv))   # ∀z(z∈G ⇔ z∈G)
    res = egalite_par_extension(thm_u2, thm_v2, F, vG, x="z")

    assert res.conclusion == egal(F, vG), "egalite_graphe_terme : conclusion ≠ F=G"
    assert len(res.hypotheses) == 4, \
        "egalite_graphe_terme : hyps ≠ 4 (%d)" % len(res.hypotheses)
    assert res.conclusion not in res.hypotheses, "egalite_graphe_terme : VACUOUS"
    return res


# ─────────────────────────────────────────────────────────────────────────────
#  B3 : F1-TERMES — ⟨g∘f⟩^𝔓 = ⟨g⟩^𝔓 ∘ ⟨f⟩^𝔓 en ÉGALITÉ DE TERMES (CST1, cas 𝔓).
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (fonctorialité de l'extension aux parties, ÉGALITÉ DE TERMES — le cas 𝔓 du critère CST1 réalisé)
def fonctorialite_parties_termes(f="f", g="g", A="A", B="B", xg="xg", pw="pw"):
    """{ (∀pw)( pw∈𝔓(A) ⇒ image(f,pw)∈𝔓(B) ) } ⊢
        ext_parties_reelle(g∘f, A)  =  composee( ext_parties_reelle(g,B),
                                                 ext_parties_reelle(f,A) ).
                                                            [1 hyp ∀-close].

    L'extensionnalité (egalite_graphe_terme, B2) appliquée à G := la composée
    des extensions réelles, avec ses 4 hypothèses DÉCHARGÉES : est_un_graphe ←
    composee_est_graphe [CLOS] ; fonctionnel ← composee_fonctionnelle +
    T1-fonctionnels [CLOS] ; dom=𝔓A ← dom_composee_borne + graphe_terme_domaine
    [CLOS] + la borne ; valeurs ← composition_valeur_t + T1-valeurs +
    image_composee.  SEULE la borne-image reste (∀-close, honnête)."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        ext_parties_reelle, ext_parties_fonctionnel, ext_parties_valeur,
        terme_ext_parties,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_composee_graphe_support import (
        composee_est_graphe, dom_composee_borne,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_fonctions_composee import (
        composee_fonctionnelle,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
        composition_valeur_t,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_domaine,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import (
        image_composee,
    )

    def _cut(thm, *preuves):
        for p in preuves:
            c = p.conclusion
            if c in thm.hypotheses:
                thm = N.modus_ponens(p, N.loi_deduction(c, thm))
        return thm

    vf, vg = _t(f), _t(g)
    PA, PB = E.parties(_t(A)), E.parties(_t(B))
    gf = E.composee(vg, vf)
    ext_f = ext_parties_reelle(f, A, xg)
    ext_g = ext_parties_reelle(g, B, xg)
    G = E.composee(ext_g, ext_f)
    t_gf = terme_ext_parties(gf, xg)                     # image(g∘f, xg)
    vpw = var(pw)

    h_borne = N.assume(pourtout(pw, impl(
        appartient(vpw, PA), appartient(E.image(vf, vpw), PB))))

    # briques CLOSES
    dom_f = graphe_terme_domaine(PA, terme_ext_parties(f, xg), xg)   # dom ext_f = 𝔓A
    dom_g = graphe_terme_domaine(PB, terme_ext_parties(g, xg), xg)   # dom ext_g = 𝔓B
    func_f = ext_parties_fonctionnel(f, A, xg)
    func_g = ext_parties_fonctionnel(g, B, xg)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    # (b) est_fonctionnel(G)
    fb = N.modus_ponens(conjonction_intro(func_f, func_g),
                        composee_fonctionnelle(ext_g, ext_f))        # CLOS

    # aides : appartenances-domaines au point pw (sous pw∈𝔓A)
    hpw = N.assume(appartient(vpw, PA))
    pw_domf = N.modus_ponens(hpw, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_f, symetrie(E.dom(ext_f), PA)),
        N.s6(PA, E.dom(ext_f), "h6b", appartient(vpw, var("h6b"))))))    # pw∈dom ext_f
    imfpw = E.image(vf, vpw)
    e_valf = ext_parties_valeur(f, A, vpw, xg)           # {pw∈𝔓A} ⊢ ext_f(pw)=image(f,pw)
    born_pw = N.modus_ponens(hpw, instancie(h_borne, vpw))           # image(f,pw)∈𝔓B
    vfp_PB = N.modus_ponens(born_pw, equivalence_avant(N.modus_ponens(
        N.modus_ponens(e_valf, symetrie(E.valeur(ext_f, vpw), imfpw)),
        N.s6(imfpw, E.valeur(ext_f, vpw), "h6b",
             appartient(var("h6b"), PB)))))              # ext_f(pw)∈𝔓B
    vfp_domg = N.modus_ponens(vfp_PB, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_g, symetrie(E.dom(ext_g), PB)),
        N.s6(PB, E.dom(ext_g), "h6b",
             appartient(E.valeur(ext_f, vpw), var("h6b"))))))        # ext_f(pw)∈dom ext_g

    # (c) dom(G)=𝔓A  — dom_composee_borne, sa 2e hyp ∀-close DÉRIVÉE (binder pwd)
    vfd_domg = N.generalisation(pw, N.loi_deduction(appartient(vpw, PA), vfp_domg))
    fc = _cut(dom_composee_borne(ext_g, ext_f, PA, wd=pw), dom_f, vfd_domg)

    # (d) hyp_valeurs(G) : (∀pw)(pw∈𝔓A ⇒ G(pw)=image(g∘f,pw))
    ex_f = N.modus_ponens(pw_domf, equivalence_avant(
        instancie(instancie(ax_dom, ext_f), vpw)))       # (∃y)((pw,y)∈ext_f)
    ex_g = N.modus_ponens(vfp_domg, equivalence_avant(
        instancie(instancie(ax_dom, ext_g), E.valeur(ext_f, vpw))))  # (∃y)(ext_f(pw),y)∈ext_g
    cv = _cut(composition_valeur_t(ext_g, ext_f, vpw), ex_f, ex_g, fb)
    #    G(pw) = ext_g(ext_f(pw))
    s6v = N.s6(E.valeur(ext_f, vpw), imfpw, "h6b",
               egal(E.valeur(G, vpw), E.valeur(ext_g, var("h6b"))))
    cv2 = N.modus_ponens(cv, equivalence_avant(N.modus_ponens(e_valf, s6v)))
    #    G(pw) = ext_g(image(f,pw))
    e_valg = ext_parties_valeur(g, B, imfpw, xg)         # {image(f,pw)∈𝔓B} ⊢ = image(g,·)
    e_valg = _cut(e_valg, born_pw)
    cv3 = composer_egalites(cv2, e_valg)                 # G(pw)=image(g,image(f,pw))
    ic = N.modus_ponens(image_composee(vg, vf, vpw),
                        symetrie(E.image(gf, vpw), E.image(vg, imfpw)))
    cv4 = composer_egalites(cv3, ic)                     # G(pw)=image(g∘f,pw)
    fd = N.generalisation(pw, N.loi_deduction(appartient(vpw, PA), cv4))
    assert fd.conclusion == hyp_valeurs(G, PA, t_gf, xg, pw), \
        "F1-termes : hyp_valeurs dérivée ≠ forme attendue"

    # ══ extensionnalité + décharges ══
    base = egalite_graphe_terme(PA, t_gf, G, xg, pw)
    res = _cut(base, composee_est_graphe(ext_g, ext_f), fb, fc, fd)

    cible = egal(ext_parties_reelle(gf, A, xg), G)
    assert res.conclusion == cible, "F1-termes : conclusion ≠ ⟨g∘f⟩=⟨g⟩∘⟨f⟩"
    assert len(res.hypotheses) == 1, \
        "F1-termes : hyps ≠ 1 (%d)" % len(res.hypotheses)
    return res


__all__ = ["hyp_valeurs", "egalite_graphe_terme", "fonctorialite_parties_termes"]
