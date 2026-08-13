"""§IV.1.5 — Réversion d'isomorphisme RÉELLE : la sœur qui consomme tout CST.

────────────────────────────────────────────────────────────────────────────────
`reciproque_isomorphisme_reel(s, fs, bases, bases_p, U, V)` :
  { Q(f_i)…, bornes CST1, U∈S(E), ⟨f⟩^S(U)=V }   ⊢
  est_bijection_de((⟨f⟩^S)⁻¹, S(E'), S(E))  ∧  (⟨f⟩^S)⁻¹(V) = U
— l'isomorphisme réciproque au niveau échelon, SANS hypothèse CST : la
bijectivité inverse vient de `bijection_reciproque` (briques base dérivées),
la clause (4) inverse de cst3_prouve (congruence) + valeur_reciproque_identite.
Briques base (GÉNÉRIQUES, tout G aux 4 conjoints Q) :
  • dom_reciproque_de_dom : {dom G=X} ⊢ dom(G⁻¹) = G⟨X⟩ ;
  • image_reciproque_pleine : {dom G=X, G⟨X⟩=Y} ⊢ G⁻¹⟨Y⟩ = X ;
  • injective_reciproque : {func G, func G⁻¹, G⟨X⟩=Y} ⊢ injective_dans(G⁻¹,Y)
    (via _recip_val : u = G(G⁻¹(u))) ;
  • bijection_reciproque : l'assemblage est_bijection_de(G⁻¹, Y, X).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

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
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_genere import (
    cst2_prouve, _q_conjoints,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_genere import (
    cst3_prouve,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_produit import (
    _recip_val,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_corollaire import (
    valeur_reciproque_identite,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def dom_reciproque_de_dom(g, x):
    """{dom G=X} ⊢ dom(G⁻¹) = G⟨X⟩.   (générique, tout G ; extension liant z.)"""
    vG, vX = _t(g), _t(x)
    RG = E.reciproque(vG)
    Im = E.image(vG, vX)
    Hdom = N.assume(egal(E.dom(vG), vX))
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(dom_ax, RG), var("Zq"))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car_img = instancie(instancie(instancie(ax_img, vG), vX), var("Zq"))
    body_y = appartient(E.couple(var("Zq"), var("y")), RG)
    body_x = et(appartient(var("x"), vX),
                appartient(E.couple(var("x"), var("Zq")), vG))

    hz = N.assume(appartient(var("Zq"), E.dom(RG)))
    ex_y = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(car_dom)),
                          equivalence_avant(alpha_existe("y", "yb", body_y)))
    corps_yb = appartient(E.couple(var("Zq"), var("yb")), RG)
    hyb = N.assume(corps_yb)
    ybZ = N.modus_ponens(hyb, equivalence_avant(
        couple_reciproque(vG, "Zq", "yb")))                # (yb,Zq)∈G
    yb_X = N.modus_ponens(_cut(couple_dans_dom(vG, var("yb"), var("Zq")), ybZ),
                          equivalence_avant(N.modus_ponens(
                              Hdom, N.s6(E.dom(vG), vX, "w",
                                         appartient(var("yb"), var("w"))))))
    ex_x = N.modus_ponens(conjonction_intro(yb_X, ybZ),
                          N.s5(body_x, var("yb"), "x"))
    z_Im = N.modus_ponens(ex_x, equivalence_arriere(car_img))
    fwd = N.loi_deduction(appartient(var("Zq"), E.dom(RG)), N.modus_ponens(
        ex_y, existe_elimination(N.loi_deduction(corps_yb, z_Im), "yb")))

    hi = N.assume(appartient(var("Zq"), Im))
    ex_xb = N.modus_ponens(N.modus_ponens(hi, equivalence_avant(car_img)),
                           equivalence_avant(alpha_existe("x", "xb", body_x)))
    corps_xb = et(appartient(var("xb"), vX),
                  appartient(E.couple(var("xb"), var("Zq")), vG))
    hxb = N.assume(corps_xb)
    Zx = N.modus_ponens(conjonction_elim_droite(hxb), equivalence_arriere(
        couple_reciproque(vG, "Zq", "xb")))
    ex_y2 = N.modus_ponens(Zx, N.s5(body_y, var("xb"), "y"))
    z_dom = N.modus_ponens(ex_y2, equivalence_arriere(car_dom))
    bwd = N.loi_deduction(appartient(var("Zq"), Im), N.modus_ponens(
        ex_xb, existe_elimination(N.loi_deduction(corps_xb, z_dom), "xb")))

    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), Im)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    res = egalite_par_extension(thm_u, thm_v, E.dom(RG), Im, x="z")
    assert res.conclusion == egal(E.dom(RG), Im), "dom_reciproque_de_dom : ≠"
    return res


def image_reciproque_pleine(g, x, y):
    """{dom G=X, G⟨X⟩=Y} ⊢ G⁻¹⟨Y⟩ = X.   (générique ; extension liant z.)"""
    vG, vX, vY = _t(g), _t(x), _t(y)
    RG = E.reciproque(vG)
    Im = E.image(RG, vY)
    Hdom = N.assume(egal(E.dom(vG), vX))
    Himg = N.assume(egal(E.image(vG, vX), vY))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, RG), vY), var("Zq"))
    body_x = et(appartient(var("x"), vY),
                appartient(E.couple(var("x"), var("Zq")), RG))
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    hz = N.assume(appartient(var("Zq"), Im))
    ex_xb = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(car)),
                           equivalence_avant(alpha_existe("x", "xb", body_x)))
    corps_xb = et(appartient(var("xb"), vY),
                  appartient(E.couple(var("xb"), var("Zq")), RG))
    hxb = N.assume(corps_xb)
    Zx_G = N.modus_ponens(conjonction_elim_droite(hxb), equivalence_avant(
        couple_reciproque(vG, "xb", "Zq")))                # (Zq,xb)∈G
    z_X = N.modus_ponens(_cut(couple_dans_dom(vG, var("Zq"), var("xb")), Zx_G),
                         equivalence_avant(N.modus_ponens(
                             Hdom, N.s6(E.dom(vG), vX, "w",
                                        appartient(var("Zq"), var("w"))))))
    fwd = N.loi_deduction(appartient(var("Zq"), Im), N.modus_ponens(
        ex_xb, existe_elimination(N.loi_deduction(corps_xb, z_X), "xb")))

    hzx = N.assume(appartient(var("Zq"), vX))
    z_dom = N.modus_ponens(hzx, equivalence_arriere(N.modus_ponens(
        Hdom, N.s6(E.dom(vG), vX, "w", appartient(var("Zq"), var("w"))))))
    ex_v = N.modus_ponens(z_dom, equivalence_avant(
        instancie(instancie(dom_ax, vG), var("Zq"))))
    cpl = _cut(valeur_dans_graphe(vG, var("Zq")), ex_v)    # (Zq, G(Zq))∈G
    GZ = E.valeur(vG, var("Zq"))
    car_gz = instancie(instancie(instancie(ax_img, vG), vX), GZ)
    body_w = et(appartient(var("x"), vX), appartient(E.couple(var("x"), GZ), vG))
    gz_im = N.modus_ponens(N.modus_ponens(conjonction_intro(hzx, cpl),
                                          N.s5(body_w, var("Zq"), "x")),
                           equivalence_arriere(car_gz))    # G(Zq)∈G⟨X⟩
    gz_Y = N.modus_ponens(gz_im, equivalence_avant(N.modus_ponens(
        Himg, N.s6(E.image(vG, vX), vY, "w", appartient(GZ, var("w"))))))
    gzZ_R = N.modus_ponens(cpl, equivalence_arriere(
        couple_reciproque(vG, GZ, var("Zq"))))             # (G(Zq), Zq)∈G⁻¹
    ex2 = N.modus_ponens(conjonction_intro(gz_Y, gzZ_R), N.s5(body_x, GZ, "x"))
    bwd = N.loi_deduction(appartient(var("Zq"), vX),
                          N.modus_ponens(ex2, equivalence_arriere(car)))

    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), vX)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    res = egalite_par_extension(thm_u, thm_v, Im, vX, x="z")
    assert res.conclusion == egal(Im, vX), "image_reciproque_pleine : ≠"
    return res


def injective_reciproque(g, x, y):
    """{func G, func G⁻¹, dom G=X, G⟨X⟩=Y} ⊢ injective_dans(G⁻¹, Y).

    u = G(G⁻¹(u)) (_recip_val) des deux côtés + congruence — relais ub/wb."""
    vG, vX, vY = _t(g), _t(x), _t(y)
    RG = E.reciproque(vG)
    Hf = N.assume(E.est_fonctionnel(vG))
    Hr = N.assume(E.est_fonctionnel(RG))
    Hi = N.assume(egal(E.image(vG, vX), vY))
    corps = et(et(appartient(var("ub"), vY), appartient(var("wb"), vY)),
               egal(E.valeur(RG, var("ub")), E.valeur(RG, var("wb"))))
    h = N.assume(corps)
    rv_u = _recip_val(vG, vX, vY, Hf, Hr, Hi,
                      conjonction_elim_gauche(conjonction_elim_gauche(h)),
                      var("ub"))
    rv_w = _recip_val(vG, vX, vY, Hf, Hr, Hi,
                      conjonction_elim_droite(conjonction_elim_gauche(h)),
                      var("wb"))
    u_eq = N.modus_ponens(conjonction_elim_droite(rv_u), symetrie(
        E.valeur(vG, E.valeur(RG, var("ub"))), var("ub")))  # ub = G(G⁻¹(ub))
    cong = N.modus_ponens(conjonction_elim_droite(h), congruence_terme(
        E.valeur(RG, var("ub")), E.valeur(RG, var("wb")),
        E.valeur(vG, var("w"))))
    res_c = composer_egalites(composer_egalites(u_eq, cong),
                              conjonction_elim_droite(rv_w))   # ub = wb
    core = N.loi_deduction(corps, res_c)
    gen = N.generalisation("ub", N.generalisation("wb", core))
    re = instancie(instancie(gen, var("u")), var("up"))
    res = N.generalisation("u", N.generalisation("up", re))
    assert res.conclusion == E.injective_dans(RG, vY), "injective_reciproque : ≠"
    return res


def bijection_reciproque(g, x, y):
    """{func G, dom G=X, func G⁻¹, G⟨X⟩=Y} ⊢ est_bijection_de(G⁻¹, Y, X)."""
    vG, vX, vY = _t(g), _t(x), _t(y)
    RG = E.reciproque(vG)
    Hr = N.assume(E.est_fonctionnel(RG))
    Himg = N.assume(egal(E.image(vG, vX), vY))
    d = composer_egalites(dom_reciproque_de_dom(vG, vX), Himg)   # dom G⁻¹=Y
    res = conjonction_intro(
        conjonction_intro(Hr, d),
        conjonction_intro(injective_reciproque(vG, vX, vY),
                          image_reciproque_pleine(vG, vX, vY)))
    assert res.conclusion == est_bijection_de(RG, vY, vX), "bijection_recip : ≠"
    return res


# @livre Ch.IV §1.5 Prop.- | E IV.6 L.13-18 | PDF p.209  (la réciproque d'un isomorphisme est un isomorphisme — VERSION RÉELLE au niveau échelon, toutes hypothèses CST déchargées par les générateurs)
def reciproque_isomorphisme_reel(s: Schema, fs: Sequence, bases: Sequence,
                                 bases_p: Sequence, u: str = "U", v: str = "V",
                                 xg: str = "xg"):
    """(thm, hyps) ⊢ est_bijection_de((⟨f⟩^S)⁻¹, S(E'), S(E)) ∧ (⟨f⟩^S)⁻¹(V)=U.

    hyps = Q(f_i) + bornes CST1 + { U∈S(E), ⟨f⟩^S(U)=V }.  La clause (4)
    inverse passe par CST3 (congruence (⟨f⟩^S)⁻¹ ↦ ⟨f⁻¹⟩^S) puis
    valeur_reciproque_identite."""
    fs_t = [_t(x) for x in fs]
    fsp = [E.reciproque(f) for f in fs_t]
    A = construction_echelon(s, [_t(b) for b in bases])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    SE, SEp, vU, vV = A[-1], Ap[-1], _t(u), _t(v)
    Gf = extension_canonique_reelle(s, fs_t, bases, xg)[-1]
    Gg = extension_canonique_reelle(s, fsp, bases_p, xg)[-1]
    RGf = E.reciproque(Gf)

    q2, hq2 = cst2_prouve(s, fs, bases, bases_p, xg)
    bij = _cut(bijection_reciproque(Gf, SE, SEp), *_q_conjoints(q2))
    c3, h3 = cst3_prouve(s, fs, bases, bases_p, xg)        # (⟨f⟩^S)⁻¹ = ⟨f⁻¹⟩^S
    vri, hv = valeur_reciproque_identite(s, fs, bases, bases_p, u, xg)
    hV = N.assume(egal(E.valeur(Gf, vU), vV))              # ⟨f⟩^S(U)=V
    #   (⟨f⟩^S)⁻¹(V) = ⟨f⁻¹⟩^S(V) = ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U
    e1 = N.modus_ponens(c3, congruence_terme(RGf, Gg, E.valeur(var("w"), vV)))
    e2 = N.modus_ponens(N.modus_ponens(hV, symetrie(E.valeur(Gf, vU), vV)),
                        congruence_terme(vV, E.valeur(Gf, vU),
                                         E.valeur(Gg, var("w"))))
    val = composer_egalites(composer_egalites(e1, e2), vri)
    res = conjonction_intro(bij, val)
    hyps = sorted(set(hq2) | set(h3) | set(hv) | {hV.conclusion}, key=str)
    cible = et(est_bijection_de(RGf, SEp, SE), egal(E.valeur(RGf, vV), vU))
    assert res.conclusion == cible, "reciproque_isomorphisme_reel : ≠ cible"
    assert set(res.hypotheses) <= set(hyps), "reciproque_isomorphisme_reel : hyps"
    return res, hyps


__all__ = ["dom_reciproque_de_dom", "image_reciproque_pleine",
           "injective_reciproque", "bijection_reciproque",
           "reciproque_isomorphisme_reel"]
