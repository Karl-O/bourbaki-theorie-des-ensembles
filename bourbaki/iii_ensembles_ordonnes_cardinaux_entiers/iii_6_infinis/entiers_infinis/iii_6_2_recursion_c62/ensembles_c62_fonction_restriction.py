"""§III.6.2 — C62, LE PONT RESTRICTION (cœur) :  f|seg(x) = p|seg(x)  pour un essai p.

La forme FIDÈLE de C62 (E III.46) fait lire à la règle la RESTRICTION f⁽ⁿ⁾=f|[0,n[.
Pour y arriver il faut le théorème substantiel : LA FONCTION GLOBALE RESTREINTE AU
SEGMENT D'UN ESSAI COÏNCIDE (au niveau GRAPHE) AVEC LA RESTRICTION DE CET ESSAI.

  • `essai_inclus_fonction`        { p∈𝔇_tot } ⊢ p ⊂ f                  [1 hyp]
  • `restriction_essai_incluse`    { p∈𝔇_tot } ⊢ p|A ⊂ f|A  (A terme)   [1 hyp]
  • `restriction_fonction_incluse` { p∈𝔇_tot, est_essai(p,x) } ⊢
        f|seg(x) ⊂ p|seg(x)                                            [2 hyps]
      — le sens DUR : un couple (a,b)∈f vient d'un AUTRE essai q ; mais b=valeur(q,a)
        =T(a)=valeur(p,a) (valeurs épinglées sur la règle) et a∈seg(x)⊂dom p, donc
        (a,b)∈p.  C'est la COHÉRENCE des essais, au niveau graphe.
  • 🎯 `restriction_egale_essai_seg` { p∈𝔇_tot, est_essai(p,x) } ⊢
        f|seg(x) = p|seg(x)                       [2 hyps ; antisymétrie de ⊂].

INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import _inst_restriction

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    est_essai, dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    _inst_union_famille, _membre_dans_union,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_final import couple_donne_valeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, fonction_globale, membres_fonctionnels_tot, valeur_membre_egale_regle_tot,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, antecedent_dans_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ── corps EXACT de AXIOME_RESTRICTION (binders internes « p », « q ») ─────────
def _corps_restr(F, A, z):
    """((z=(p,q) et p∈A) et (p,q)∈F)   — le corps sous (∃p)(∃q) de z∈F|A."""
    vp, vq = var("p"), var("q")
    cpq = E.couple(vp, vq)
    return et(et(egal(_t(z), cpq), appartient(vp, _t(A))), appartient(cpq, _t(F)))


def _rebuild_restr(F, A, z, thm_corps):
    """De ⊢ corps(z ; a:=p, b:=q) [thm_corps, aux VARIABLES p,q] déduit ⊢ z∈F|A."""
    corps_q = _corps_restr(F, A, z)                              # corps aux vars p,q
    ex_q = N.modus_ponens(thm_corps, N.s5(corps_q, var("q"), "q"))
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", corps_q), var("p"), "p"))
    return N.modus_ponens(ex_pq, equivalence_arriere(_inst_restriction(_t(F), _t(A), _t(z))))


# ════════════════════════════════════════════════════════════════════════════
#  p ⊂ f  — tout essai est inclus dans la fonction globale.
# ════════════════════════════════════════════════════════════════════════════
def essai_inclus_fonction(vh, e="Enat", G="Gle", V="Uval", p="pess"):
    """{ p∈𝔇_tot } ⊢ p ⊂ f,   f = ⋃𝔇_tot                              [1 hyp]."""
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    vp, vz = var(p), var("z")

    h_pD = N.assume(appartient(vp, Dt))                          # p∈𝔇   [HONNÊTE]
    h_w = N.assume(appartient(vz, vp))                           # z∈p
    in_f = _membre_dans_union(Dt, vp, vz, h_pD, h_w)             # z∈⋃𝔇
    res = N.generalisation("z", N.loi_deduction(appartient(vz, vp), in_f))

    assert res.conclusion == inclus(vp, f), "essai_inclus_fonction : ≠ p⊂f"
    assert len(res.hypotheses) == 1, "essai_inclus_fonction : hyps ≠ 1"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  p|A ⊂ f|A  — monotonie de la restriction dans le graphe (sens FACILE).
# ════════════════════════════════════════════════════════════════════════════
def restriction_essai_incluse(vh, A, e="Enat", G="Gle", V="Uval", p="pess"):
    """{ p∈𝔇_tot } ⊢ p|A ⊂ f|A   (A : Terme)                          [1 hyp]."""
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    vp, vz = var(p), var("z")
    A = _t(A)

    h_z = N.assume(appartient(vz, E.restriction(vp, A)))         # z∈p|A
    dec = N.modus_ponens(h_z, equivalence_avant(_inst_restriction(vp, A, vz)))
    # dec = (∃p)(∃q)((z=(p,q) et p∈A) et (p,q)∈p_essai) — binders internes p,q
    corps = _corps_restr(vp, A, vz)
    h_c = N.assume(corps)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_c))   # z=(p,q)
    aA = conjonction_elim_droite(conjonction_elim_gauche(h_c))     # p∈A
    ab_in = conjonction_elim_droite(h_c)                           # (p,q)∈p_essai
    h_pD = N.assume(appartient(vp, Dt))                            # p_essai∈𝔇   [HONNÊTE]
    ab_f = _membre_dans_union(Dt, vp, E.couple(var("p"), var("q")), h_pD, ab_in)
    wit = conjonction_intro(conjonction_intro(z_eq, aA), ab_f)     # corps côté f
    z_fA = _rebuild_restr(f, A, vz, wit)                           # z∈f|A

    # élimine les témoins q puis p (non libres dans z∈f|A ni dans p_essai∈𝔇)
    z_fA = N.loi_deduction(corps, z_fA)
    imp_q = existe_elimination(z_fA, "q")                          # (∃q)corps ⇒ z∈f|A
    imp_pq = existe_elimination(imp_q, "p")                        # (∃p)(∃q)corps ⇒ z∈f|A
    z_fA = N.modus_ponens(dec, imp_pq)

    res = N.generalisation("z", N.loi_deduction(appartient(vz, E.restriction(vp, A)), z_fA))
    assert res.conclusion == inclus(E.restriction(vp, A), E.restriction(f, A)), \
        "restriction_essai_incluse : ≠ p|A ⊂ f|A"
    assert len(res.hypotheses) == 1, "restriction_essai_incluse : hyps ≠ 1"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  f|seg(x) ⊂ p|seg(x)  — le sens DUR (cohérence des essais au niveau graphe).
# ════════════════════════════════════════════════════════════════════════════
def restriction_fonction_incluse(vh, e="Enat", G="Gle", V="Uval",
                                 x="zfgl", p="pess"):
    """{ p∈𝔇_tot, est_essai(p,x) } ⊢ f|seg(x) ⊂ p|seg(x)              [2 hyps].

    (a,b)∈f avec a∈seg(x) : (a,b) vient d'un essai q∈𝔇_tot ; a∈dom q donc
    b=valeur(q,a)=T(a) (valeurs épinglées) ; a∈seg(x)⊂dom p donc valeur(p,a)=T(a)
    et (a,valeur(p,a))∈p ; b=valeur(p,a) ⇒ (a,b)∈p.  Rebuild z∈p|seg(x)."""
    R = _graphe_R(G)
    ve, vx, vp = _t(e), var(x), var(p)
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, vx)
    de = dom_essai(G, ve, vx)
    vz = var("z")
    va, vb = var("p"), var("q")                # les témoins de AXIOME_RESTRICTION
    cab = E.couple(va, vb)

    h_pD = N.assume(appartient(vp, Dt))                          # p∈𝔇          [HONNÊTE]
    h_ess = N.assume(est_essai(vp, vh, G, ve, vx))               # est_essai(p,x) [HONNÊTE]
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(h_ess))   # dom p = seg∪{x}

    # func p et func q (∀-CLOS instancié)
    mf = membres_fonctionnels_tot(vh, e, G, V)                   # (∀pmf)(pmf∈𝔇⇒func)  CLOS

    h_z = N.assume(appartient(vz, E.restriction(f, seg)))        # z∈f|seg(x)
    dec = N.modus_ponens(h_z, equivalence_avant(_inst_restriction(f, seg, vz)))
    corps = _corps_restr(f, seg, vz)
    h_c = N.assume(corps)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_c))   # z=(a,b)
    a_seg = conjonction_elim_droite(conjonction_elim_gauche(h_c))  # a∈seg(x)
    ab_f = conjonction_elim_droite(h_c)                            # (a,b)∈f

    # ── (a,b) vient d'un essai q∈𝔇 : b = T(a) ────────────────────────────────
    dec_u = N.modus_ponens(ab_f, equivalence_avant(_inst_union_famille(Dt, cab)))
    vqu = var("punion")
    corps_u = et(appartient(vqu, Dt), appartient(cab, vqu))
    h_u = N.assume(corps_u)
    quD = conjonction_elim_gauche(h_u)                           # q∈𝔇
    ab_q = conjonction_elim_droite(h_u)                          # (a,b)∈q
    func_q = N.modus_ponens(quD, instancie(mf, vqu))             # func q
    b_val_q = couple_donne_valeur(vqu, va, vb)                   # {func q,(a,b)∈q} ⊢ b=val(q,a)
    b_val_q = N.modus_ponens(func_q, N.loi_deduction(E.est_fonctionnel(vqu), b_val_q))
    b_val_q = N.modus_ponens(ab_q, N.loi_deduction(appartient(cab, vqu), b_val_q))
    a_dom_q = N.modus_ponens(ab_q, antecedent_dans_domaine(va, vb, vqu))   # a∈dom q
    vmr_q = valeur_membre_egale_regle_tot(vh, e, G, V, "punion", "p")      # val(q,a)=T(a)
    vmr_q = N.modus_ponens(quD, N.loi_deduction(appartient(vqu, Dt), vmr_q))
    vmr_q = N.modus_ponens(a_dom_q, N.loi_deduction(appartient(va, E.dom(vqu)), vmr_q))
    b_Ta = composer_egalites(b_val_q, vmr_q)                     # b = T(a)

    # ── a∈dom p et (a, val(p,a))∈p ; val(p,a)=T(a) ───────────────────────────
    a_de = N.modus_ponens(N.modus_ponens(a_seg, N.s2(appartient(va, seg),
                                                     appartient(va, E.singleton(vx)))),
                          equivalence_arriere(membre_reunion_graphes(
                              seg, E.singleton(vx), va)))        # a∈seg∪{x}
    eq2 = N.modus_ponens(dom_eq, symetrie(E.dom(vp), de))        # seg∪{x} = dom p
    eqF = N.modus_ponens(eq2, N.s6(de, E.dom(vp), "wdm", appartient(va, var("wdm"))))
    a_dom_p = N.modus_ponens(a_de, equivalence_avant(eqF))       # a∈dom p
    # (∃y)((a,y)∈p) puis témoin y : y=val(p,a), val(p,a)=T(a), b=T(a) ⇒ y=b ⇒ (a,b)∈p
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vp), va)                   # a∈dom p ⇔ (∃y)((a,y)∈p)
    ex_y = N.modus_ponens(a_dom_p, equivalence_avant(car))
    vy = var("y")
    cay = E.couple(va, vy)
    h_y = N.assume(appartient(cay, vp))
    func_p = N.modus_ponens(h_pD, instancie(mf, vp))             # func p
    y_val_p = couple_donne_valeur(vp, va, vy)
    y_val_p = N.modus_ponens(func_p, N.loi_deduction(E.est_fonctionnel(vp), y_val_p))
    y_val_p = N.modus_ponens(h_y, N.loi_deduction(appartient(cay, vp), y_val_p))  # y=val(p,a)
    vmr_p = valeur_membre_egale_regle_tot(vh, e, G, V, p, "p")   # val(p,a)=T(a)
    vmr_p = N.modus_ponens(h_pD, N.loi_deduction(appartient(vp, Dt), vmr_p))
    vmr_p = N.modus_ponens(a_dom_p, N.loi_deduction(appartient(va, E.dom(vp)), vmr_p))
    y_Ta = composer_egalites(y_val_p, vmr_p)                     # y = T(a)
    y_b = composer_egalites(y_Ta, N.modus_ponens(b_Ta, symetrie(vb, vh(va))))   # y=b
    eqYB = N.modus_ponens(y_b, N.s6(vy, vb, "wrc", appartient(E.couple(va, var("wrc")), vp)))
    ab_p = N.modus_ponens(h_y, equivalence_avant(eqYB))          # (a,b)∈p
    ab_p = N.modus_ponens(ex_y, existe_elimination(
        N.loi_deduction(appartient(cay, vp), ab_p), "y"))

    # ── rebuild z∈p|seg(x), puis éliminations punion, q, p ────────────────────
    wit = conjonction_intro(conjonction_intro(z_eq, a_seg), ab_p)
    z_pA = _rebuild_restr(vp, seg, vz, wit)                      # z∈p|seg(x)
    z_pA = N.modus_ponens(dec_u, existe_elimination(
        N.loi_deduction(corps_u, z_pA), "punion"))
    imp_q = existe_elimination(N.loi_deduction(corps, z_pA), "q")
    imp_pq = existe_elimination(imp_q, "p")
    z_pA = N.modus_ponens(dec, imp_pq)

    res = N.generalisation("z", N.loi_deduction(appartient(vz, E.restriction(f, seg)), z_pA))
    assert res.conclusion == inclus(E.restriction(f, seg), E.restriction(vp, seg)), \
        "restriction_fonction_incluse : ≠ f|seg ⊂ p|seg"
    assert len(res.hypotheses) == 2, "restriction_fonction_incluse : hyps ≠ 2"
    assert res.conclusion not in res.hypotheses, "restriction_fonction_incluse : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 f|seg(x) = p|seg(x)  — LE PONT RESTRICTION (antisymétrie de ⊂).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Demo.C62 | E III.46 L.14-20 | PDF p.149  (la solution globale coïncide avec chaque essai sur son segment — le recollement du livre, niveau graphe)
def restriction_egale_essai_seg(vh, e="Enat", G="Gle", V="Uval",
                                x="zfgl", p="pess"):
    """🎯 { p∈𝔇_tot, est_essai(p,x) } ⊢ f|seg(x) = p|seg(x)            [2 hyps].

    L'égalité de GRAPHES : la fonction globale restreinte au segment d'un essai EST
    la restriction de cet essai.  Double inclusion + antisymétrie de ⊂ (A1)."""
    R = _graphe_R(G)
    ve, vx, vp = _t(e), var(x), var(p)
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, vx)

    sub = restriction_fonction_incluse(vh, e, G, V, x, p)        # f|seg ⊂ p|seg  [2 hyps]
    sup = restriction_essai_incluse(vh, seg, e, G, V, p)         # p|seg ⊂ f|seg  [1 hyp]
    res = N.modus_ponens(conjonction_intro(sub, sup),
                         inclusion_antisymetrique(E.restriction(f, seg),
                                                  E.restriction(vp, seg)))

    assert res.conclusion == egal(E.restriction(f, seg), E.restriction(vp, seg)), \
        "restriction_egale_essai_seg : ≠ f|seg=p|seg"
    assert len(res.hypotheses) == 2, "restriction_egale_essai_seg : hyps ≠ 2"
    return res


__all__ = [
    "essai_inclus_fonction", "restriction_essai_incluse",
    "restriction_fonction_incluse", "restriction_egale_essai_seg",
]
