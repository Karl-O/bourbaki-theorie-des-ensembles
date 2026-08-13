"""§IV.1.2 — Corollaire CST3 : ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Δ_{S(E)}  (le capstone).

────────────────────────────────────────────────────────────────────────────────
Assemblage des trois générateurs :
  ⟨f⁻¹⟩^S ∘ ⟨f⟩^S  =  ⟨f⁻¹∘f⟩^S      [CST1, gs := f⁻¹, sym]
                   =  ⟨Δ_E⟩^S          [congruence-famille : f_i⁻¹∘f_i = Δ_{E_i}
                                        par `composee_reciproque_diagonale`,
                                        trou = extension du terme-famille w]
                   =  Δ_{S(E)}          [CST1-identité, CLOS]
Brique base : {dom f=A, func f⁻¹} ⊢ f⁻¹∘f = Δ_A — extension liant z :
→ AXIOME_COMPOSEE (α p/r/y → pc/rc/yb), univalence de f⁻¹ force pc=rc, d'où
  le témoin diagonal ; ← témoin interne f(d0) (motif _couple_dans_graphe).
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
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle, cst1_termes_prouve,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_identite import (
    cst1_identite_prouve,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst2_briques import (
    bijection_q,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_etage_produit import (
    _couple_dans_graphe,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.II §3.7 Prop.- | E II.18 L.1-6 | PDF p.69  (f injective : la composée f⁻¹∘f est l'application identique de A — forme graphe, diagonale)
def composee_reciproque_diagonale(f, a):
    """{ dom f=A, func f⁻¹ } ⊢ composee(f⁻¹, f) = Δ_A.       [2 hyps ⊆ Q(f)]."""
    vf, vA = _t(f), _t(a)
    rf = E.reciproque(vf)
    C = E.composee(rf, vf)
    DA = E.diagonale(vA)
    Hdom = N.assume(egal(E.dom(vf), vA))
    Hrec = N.assume(E.est_fonctionnel(rf))
    ax_c = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    car_c = instancie(instancie(instancie(ax_c, rf), vf), var("Zq"))
    ax_d = N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE)
    car_d = instancie(instancie(ax_d, vA), var("Zq"))

    def body_pr(pt, rt):
        return et(egal(var("Zq"), E.couple(pt, rt)),
                  existe("y", et(appartient(E.couple(pt, var("y")), vf),
                                 appartient(E.couple(var("y"), rt), rf))))

    # → : Zq∈f⁻¹∘f ⇒ (α pc/rc/yb) pc=rc [univalence f⁻¹], pc∈A ⇒ Zq∈Δ_A
    hz = N.assume(appartient(var("Zq"), C))
    ex_p = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(car_c)),
                          equivalence_avant(alpha_existe(
                              "p", "pc", existe("r", body_pr(var("p"), var("r"))))))
    corps_pc = existe("r", body_pr(var("pc"), var("r")))
    hpc = N.assume(corps_pc)
    ex_r = N.modus_ponens(hpc, equivalence_avant(alpha_existe(
        "r", "rc", body_pr(var("pc"), var("r")))))
    corps_rc = body_pr(var("pc"), var("rc"))
    hrc = N.assume(corps_rc)
    z_eq = conjonction_elim_gauche(hrc)                    # Zq=(pc,rc)
    body_y = et(appartient(E.couple(var("pc"), var("y")), vf),
                appartient(E.couple(var("y"), var("rc")), rf))
    ex_y = N.modus_ponens(conjonction_elim_droite(hrc),
                          equivalence_avant(alpha_existe("y", "yb", body_y)))
    corps_yb = et(appartient(E.couple(var("pc"), var("yb")), vf),
                  appartient(E.couple(var("yb"), var("rc")), rf))
    hyb = N.assume(corps_yb)
    yb_pc = N.modus_ponens(conjonction_elim_gauche(hyb), equivalence_arriere(
        couple_reciproque(vf, "yb", "pc")))                # (yb,pc)∈f⁻¹
    univ = instancie(instancie(instancie(Hrec, var("yb")), var("pc")), var("rc"))
    pc_rc = N.modus_ponens(conjonction_intro(
        yb_pc, conjonction_elim_droite(hyb)), univ)        # pc=rc
    pc_dom = couple_dans_dom(vf, var("pc"), var("yb"))
    pc_A = N.modus_ponens(_cut(pc_dom, conjonction_elim_gauche(hyb)),
                          equivalence_avant(N.modus_ponens(
                              Hdom, N.s6(E.dom(vf), vA, "w",
                                         appartient(var("pc"), var("w"))))))
    cc = N.modus_ponens(N.modus_ponens(pc_rc, symetrie(var("pc"), var("rc"))),
                        congruence_terme(var("rc"), var("pc"),
                                         E.couple(var("pc"), var("w"))))
    z_dd = composer_egalites(z_eq, cc)                     # Zq=(pc,pc)
    body_d = et(appartient(var("d0"), vA),
                egal(var("Zq"), E.couple(var("d0"), var("d0"))))
    ex_d = N.modus_ponens(conjonction_intro(pc_A, z_dd),
                          N.s5(body_d, var("pc"), "d0"))
    z_DA = N.modus_ponens(ex_d, equivalence_arriere(car_d))
    z_DA = N.modus_ponens(ex_y, existe_elimination(
        N.loi_deduction(corps_yb, z_DA), "yb"))
    z_DA = N.modus_ponens(ex_r, existe_elimination(
        N.loi_deduction(corps_rc, z_DA), "rc"))
    z_DA = N.modus_ponens(ex_p, existe_elimination(
        N.loi_deduction(corps_pc, z_DA), "pc"))
    fwd = N.loi_deduction(appartient(var("Zq"), C), z_DA)

    # ← : Zq∈Δ_A ⇒ témoin d0 : (d0,f(d0))∈f, (f(d0),d0)∈f⁻¹ ⇒ Zq∈f⁻¹∘f
    hz2 = N.assume(appartient(var("Zq"), DA))
    ex_d2 = N.modus_ponens(hz2, equivalence_avant(car_d))
    hd = N.assume(body_d)
    d_A = conjonction_elim_gauche(hd)
    cpl = _cut(_couple_dans_graphe(vf, vA, Hdom, var("d0")), d_A)
    fd0 = E.valeur(vf, var("d0"))
    cpl_r = N.modus_ponens(cpl, equivalence_arriere(
        couple_reciproque(vf, fd0, var("d0"))))            # (f(d0),d0)∈f⁻¹
    ex_y2 = N.modus_ponens(conjonction_intro(cpl, cpl_r), N.s5(
        et(appartient(E.couple(var("d0"), var("y")), vf),
           appartient(E.couple(var("y"), var("d0")), rf)), fd0, "y"))
    inner = conjonction_intro(conjonction_elim_droite(hd), ex_y2)
    ex_r2 = N.modus_ponens(inner, N.s5(body_pr(var("d0"), var("r")), var("d0"), "r"))
    ex_p2 = N.modus_ponens(ex_r2, N.s5(
        existe("r", body_pr(var("p"), var("r"))), var("d0"), "p"))
    z_C = N.modus_ponens(ex_p2, equivalence_arriere(car_c))
    bwd = N.loi_deduction(appartient(var("Zq"), DA), N.modus_ponens(
        ex_d2, existe_elimination(N.loi_deduction(body_d, z_C), "d0")))

    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), DA)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    res = egalite_par_extension(thm_u, thm_v, C, DA, x="z")
    assert res.conclusion == egal(C, DA), "composee_reciproque_diagonale : ≠ cible"
    assert set(res.hypotheses) <= {Hdom.conclusion, Hrec.conclusion}, \
        "composee_reciproque_diagonale : hyps"
    return res


# @livre Ch.IV §1.2 Crit.CST3 | E IV.2 L.35-37 | PDF p.205  (corollaire : l'extension des réciproques compose avec l'extension en l'identité de l'échelon — CST1 + congruence-famille + CST1-identité)
def cst3_corollaire_identite(s: Schema, fs: Sequence, bases: Sequence,
                             bases_p: Sequence, xg: str = "xg"):
    """(thm, hyps) : thm ⊢ ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Δ_{S(E)}.

    hyps = les n Q(f_i) + les hyps honnêtes de CST1 (bornes-image /
    est_application des étages, sur les familles f et f⁻¹)."""
    fs_t = [_t(x) for x in fs]
    fsp = [E.reciproque(f) for f in fs_t]
    A = construction_echelon(s, [_t(b) for b in bases])
    comps0 = [E.composee(E.reciproque(f), f) for f in fs_t]
    C_ext = extension_canonique_reelle(s, comps0, bases, xg)[-1]
    Gf = extension_canonique_reelle(s, fs_t, bases, xg)[-1]
    Gg = extension_canonique_reelle(s, fsp, bases_p, xg)[-1]
    c1, h1 = cst1_termes_prouve(s, fs_t, fsp, bases, bases_p, bases, xg)
    #   ⟨f⁻¹∘f⟩^S = ⟨f⁻¹⟩^S ∘ ⟨f⟩^S  → symétrie
    hyps = list(h1)
    eq = N.modus_ponens(c1, symetrie(C_ext, E.composee(Gg, Gf)))

    # congruence-famille : remplacer composee(f_i⁻¹,f_i) par Δ_{E_i}, un i à la fois
    comps = comps0
    diags = [E.diagonale(_t(b)) for b in bases]
    for i in range(len(fs_t)):
        famille_trou = diags[:i] + [var("w")] + comps[i + 1:]
        trou = extension_canonique_reelle(s, famille_trou, bases, xg)[-1]
        base_eq = composee_reciproque_diagonale(fs_t[i], _t(bases[i]))
        q = bijection_q(fs_t[i], _t(bases[i]), _t(bases_p[i]))
        hq = N.assume(q)
        base_eq = _cut(base_eq,
                       conjonction_elim_droite(conjonction_elim_gauche(hq)),
                       conjonction_elim_gauche(conjonction_elim_droite(hq)))
        hyps.append(q)
        cong = N.modus_ponens(base_eq, congruence_terme(
            comps[i], diags[i], trou))
        eq = composer_egalites(eq, cong)
    #   … = ⟨Δ⟩^S = Δ_{S(E)}
    eq = composer_egalites(eq, cst1_identite_prouve(s, bases, xg))
    cible = egal(E.composee(Gg, Gf), E.diagonale(A[-1]))
    assert eq.conclusion == cible, "cst3_corollaire : ≠ ⟨f⁻¹⟩∘⟨f⟩=Δ_{S(E)}"
    assert set(eq.hypotheses) <= set(hyps), "cst3_corollaire : hyps"
    return eq, sorted(set(hyps), key=str)


# @livre Ch.IV §1.5 Prop.- | E IV.6 L.13-18 | PDF p.209  (la 3e hypothèse de reciproque_isomorphisme_espece, DÉCHARGÉE au niveau valeur : ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U)
def valeur_reciproque_identite(s: Schema, fs: Sequence, bases: Sequence,
                               bases_p: Sequence, u: str = "U",
                               xg: str = "xg"):
    """(thm, hyps) : thm ⊢ ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U.

    hyps = celles du capstone + { U ∈ S(E) }.  Chaîne : composition_valeur_t
    (3 hyps déchargées : U∈dom⟨f⟩ par Q-dom, ⟨f⟩(U)∈dom⟨f⁻¹⟩ par Q-image +
    graphe_terme_domaine CLOS, func(∘) par transport du capstone sur func(Δ)),
    puis congruence-capstone, puis Δ_{S(E)}(U)=U (_dval_t).
    ⚠️ schéma NON TRIVIAL exigé (dernier couple ≠ (0,b) : dom⟨f⁻¹⟩ via C54)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
        composition_valeur_t,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_domaine,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
        diagonale_fonctionnelle, diagonale_valeur,
    )
    from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_genere import (
        cst2_prouve, _q_conjoints,
    )
    a_top, b_top = s.couples[-1]
    assert a_top != 0, "valeur_reciproque_identite : schéma trivial (0,b)"
    fs_t = [_t(x) for x in fs]
    fsp = [E.reciproque(f) for f in fs_t]
    A = construction_echelon(s, [_t(b) for b in bases])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    SE, SEp, vU = A[-1], Ap[-1], _t(u)
    Gf = extension_canonique_reelle(s, fs_t, bases, xg)[-1]
    Gg = extension_canonique_reelle(s, fsp, bases_p, xg)[-1]
    cap, hyps = cst3_corollaire_identite(s, fs, bases, bases_p, xg)
    q2, hq2 = cst2_prouve(s, fs, bases, bases_p, xg)
    hyps = sorted(set(hyps) | set(hq2), key=str)
    _, dom_f, _, img_f = _q_conjoints(q2)                  # dom Gf=S(E), Gf⟨S(E)⟩=S(E')
    hU = N.assume(appartient(vU, SE))
    hyps = hyps + [hU.conclusion]
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    def _ex_dom(G_t, pt, dom_eq, dom_set):
        pt_dom = N.modus_ponens(N.modus_ponens(dom_eq, symetrie(
            E.dom(G_t), dom_set)), N.s6(dom_set, E.dom(G_t), "w",
                                        appartient(pt, var("w"))))
        return N.modus_ponens(N.modus_ponens(_ptin(pt, dom_set),
                                             equivalence_avant(pt_dom)),
                              equivalence_avant(
                                  instancie(instancie(dom_ax, G_t), pt)))

    _seen = {}

    def _ptin(pt, dom_set):
        return _seen[(str(pt), str(dom_set))]

    # hyp 1 : (∃y)(U,y)∈Gf
    _seen[(str(vU), str(SE))] = hU
    ex1 = _ex_dom(Gf, vU, dom_f, SE)
    # Gf(U) ∈ S(E') : témoin U dans l'image + c4
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
        valeur_dans_graphe,
    )
    GfU = E.valeur(Gf, vU)
    cplU = _cut(valeur_dans_graphe(Gf, vU), ex1)           # (U, Gf(U)) ∈ Gf
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, Gf), SE), GfU)
    body = et(appartient(var("x"), SE), appartient(E.couple(var("x"), GfU), Gf))
    exw = N.modus_ponens(conjonction_intro(hU, cplU), N.s5(body, vU, "x"))
    in_img = N.modus_ponens(exw, equivalence_arriere(car))
    GfU_SEp = N.modus_ponens(in_img, equivalence_avant(N.modus_ponens(
        img_f, N.s6(E.image(Gf, SE), SEp, "w", appartient(GfU, var("w"))))))
    # hyp 2 : (∃y)(Gf(U),y)∈Gg — dom Gg = S(E') par C54 (top non trivial)
    xi_top = f"{xg}{len(s.couples)}"
    if b_top == 0:
        Tg = E.image(extension_canonique_reelle(s, fsp, bases_p, xg)[a_top - 1],
                     var(xi_top))
        dom_g = graphe_terme_domaine(E.parties(Ap[a_top - 1]), Tg, xi_top,
                                     "y", "z")
    else:
        Gga = extension_canonique_reelle(s, fsp, bases_p, xg)
        Tg = E.couple(E.valeur(Gga[a_top - 1], E.pr1(var(xi_top))),
                      E.valeur(Gga[b_top - 1], E.pr2(var(xi_top))))
        dom_g = graphe_terme_domaine(E.produit(Ap[a_top - 1], Ap[b_top - 1]),
                                     Tg, xi_top, "y", "z")
    _seen[(str(GfU), str(SEp))] = GfU_SEp
    ex2 = _ex_dom(Gg, GfU, dom_g, SEp)
    # hyp 3 : func(Gg∘Gf) — transport du capstone sur func(Δ_{S(E)})
    func_D = instancie(N.generalisation("Xdf", diagonale_fonctionnelle("Xdf")), SE)
    func_C = N.modus_ponens(func_D, equivalence_arriere(N.modus_ponens(
        cap, N.s6(E.composee(Gg, Gf), E.diagonale(SE), "w",
                  E.est_fonctionnel(var("w"))))))
    cv = _cut(composition_valeur_t(Gg, Gf, vU), ex1, ex2, func_C)
    #   Gg(Gf(U)) = (Gg∘Gf)(U) = Δ(U) = U
    eq1 = N.modus_ponens(cv, symetrie(E.valeur(E.composee(Gg, Gf), vU),
                                      E.valeur(Gg, GfU)))
    eq2 = N.modus_ponens(cap, congruence_terme(
        E.composee(Gg, Gf), E.diagonale(SE), E.valeur(var("w"), vU)))
    dv = diagonale_valeur("Xdv", "udv")
    imp = N.loi_deduction(appartient(var("udv"), var("Xdv")), dv)
    gen = N.generalisation("Xdv", N.generalisation("udv", imp))
    eq3 = N.modus_ponens(hU, instancie(instancie(gen, SE), vU))
    res = composer_egalites(composer_egalites(eq1, eq2), eq3)
    assert res.conclusion == egal(E.valeur(Gg, GfU), vU),         "valeur_reciproque_identite : ≠ ⟨f⁻¹⟩(⟨f⟩(U))=U"
    assert set(res.hypotheses) <= set(hyps), "valeur_reciproque_identite : hyps"
    return res, hyps


__all__ = ["composee_reciproque_diagonale", "cst3_corollaire_identite",
           "valeur_reciproque_identite"]
