"""§II.5.5 — ADJONCTION D'INDICE, briques restriction / réunion / prolongement.

Infrastructure de la bijection Φ : F ↦ (F|I, F(j)) (cf. ensembles_produit_adjonction) :
  • restriction_dans_produit    {t ∈ ∏_{I∪{j}}} ⊢ t|I ∈ ∏_I ;
  • restriction_est_graphe      ⊢ est_un_graphe(f|X)                        [CLOS] ;
  • valeur_reunion_gauche       {func(G∪H), t∈dom G} ⊢ (G∪H)(t) = G(t) ;
  • valeur_reunion_point        {func(G∪{(j,x)})} ⊢ (G∪{(j,x)})(j) = x ;
  • prolongement_un_point_dans_produit   (l'ANTÉCÉDENT de la surjectivité)
        {G ∈ ∏_I, x ∈ u_j, ¬(j∈I)} ⊢ G∪{(j,x)} ∈ ∏_{I∪{j}}.
Briques closes réutilisées : restriction_valeur / restriction_dom_sous_inclusion /
_restriction_fonctionnelle_terme (cantor_bernstein), membre_reunion_graphes /
reunion_graphes_fonctionnelle / dom_reunion_graphes (recollement),
singleton_couple_fonctionnel / dom_singleton_couple (c60).  Hypothèses honnêtes
LISTÉES dans chaque docstring ; rien postulé ; theorie_ensembles() = 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient, existe, inclus, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe, valeur_caracterisation)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import (
    _inst_restriction)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur, _restriction_fonctionnelle_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, reunion_graphes_fonctionnelle, dom_reunion_graphes)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    singleton_couple_fonctionnel, dom_singleton_couple)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    _t, _dech, indices_adjoints, produit_total, i_dans_union, inclusion_I_union,
    _car_union, _inst_fam, _corps_membre, _leibniz_membre, _leibniz_membre_arriere)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    conjoint_de_tete, corps_membre, graphe_du_point)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    graphe_apres_adjonction)


# ── La restriction d'un point du produit total tombe dans ∏_I ─────────────────
def restriction_dans_produit(tt, u="uq", i="Iq", j="jq"):
    """{t ∈ ∏_{I∪{j}}} ⊢ t|I ∈ ∏_I.   (t : nom ou terme ; hypothèse honnête t∈∏.)

    func(t|I) par restriction d'un fonctionnel ; dom(t|I)=I par I⊂I∪{j}=dom t ;
    valeurs : (t|I)(i)=t(i)∈u_i pour i∈I (restriction_valeur + membership)."""
    vt, vI = _t(tt), _t(i)
    A, prodI = produit_total(u, i, j), E.produit_famille(_t(u), vI)
    h = N.assume(appartient(vt, A))
    _incl_t, func_t, domeq_t, vals_t = _corps_membre(h, u, indices_adjoints(i, j), vt)
    # (a) fonctionnalité ; (b) domaine : I ⊂ I∪{j} = dom t ⇒ dom(t|I) = I
    func_res = N.modus_ponens(func_t, _restriction_fonctionnelle_terme(vt, vI))
    leib = N.modus_ponens(domeq_t, N.s6(E.dom(vt), indices_adjoints(i, j), "w",
                                        inclus(vI, var("w"))))
    incl_dom = N.modus_ponens(inclusion_I_union(i, j), equivalence_arriere(leib))
    dom_res = N.modus_ponens(incl_dom, restriction_dom_sous_inclusion(vt, vI))
    # (c) valeurs : (∀i)(i∈I ⇒ (t|I)(i) ∈ u_i)
    vi = var("i")
    hi = N.assume(appartient(vi, vI))
    i_un = _dech(i_dans_union(i, j, vi), hi)                    # i ∈ I∪{j}
    i_dom = _leibniz_membre_arriere(i_un, domeq_t, vi)          # i ∈ dom t
    t_i_in = N.modus_ponens(i_un, instancie(vals_t, vi))        # t(i) ∈ u_i
    rv = _dech(restriction_valeur(vt, vI, vi), func_t, hi, i_dom)   # (t|I)(i) = t(i)
    fam_i = E.valeur_famille(_t(u), vi)
    leib_v = N.modus_ponens(rv, N.s6(E.valeur(E.restriction(vt, vI), vi),
                                     E.valeur(vt, vi), "w", appartient(var("w"), fam_i)))
    res_i = N.modus_ponens(t_i_in, equivalence_arriere(leib_v))  # (t|I)(i) ∈ u_i
    vals_res = N.generalisation("i", N.loi_deduction(appartient(vi, vI), res_i))
    # (d) conjoint de TÊTE (Déf. 1, rétabli le 26 juil. 2026) : t|I ⊂ I × ⋃_{ι∈I} u_ι.
    #     est_un_graphe(t|I) est CLOS (restriction_est_graphe) ; le pivot fait le reste.
    tete = conjoint_de_tete(restriction_est_graphe(vt, vI), func_res, dom_res, vals_res,
                            E.restriction(vt, vI), _t(u), vI)
    # assemblage → t|I ∈ ∏_I
    corps = corps_membre(tete, func_res, dom_res, vals_res)
    res = N.modus_ponens(corps, equivalence_arriere(_inst_fam(u, vI, E.restriction(vt, vI))))
    assert res.conclusion == appartient(E.restriction(vt, vI), prodI), "restriction_dans_produit : forme"
    assert res.hypotheses == frozenset({appartient(vt, A)}), "restriction_dans_produit : hyps"
    return res


# ── est_un_graphe d'une restriction (dérivé de AXIOME_RESTRICTION ; CLOS) ─────
def restriction_est_graphe(f, x):
    """⊢ est_un_graphe(f|X)   (tout élément de f|X est un couple ; f, x termes ; CLOS).

    z∈f|X ⇔ (∃p)(∃q)(z=(p,q) et …) ⇒ (∃x)(∃y)(z=(x,y))  (témoins p,q re-liés x,y)."""
    vf, vX, vz = _t(f), _t(x), var("z")
    vp, vq = var("p"), var("q")
    inst = _inst_restriction(vf, vX, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)),
              appartient(E.couple(vp, vq), vf))
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))       # z=(p,q)
    inner = egal(vz, E.couple(var("x"), var("y")))                    # z=(x,y)
    ex_y = N.modus_ponens(z_pq, N.s5(subst_f(vp, "x", inner), vq, "y"))   # (∃y)(z=(p,y))
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("y", inner), vp, "x"))       # (∃x)(∃y)(z=(x,y))
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex_xy), "q"), "p")                      # (∃p)(∃q)body ⇒ couple
    hz = N.assume(appartient(vz, E.restriction(vf, vX)))
    couple_z = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(inst)), imp)
    res = N.generalisation("z", N.loi_deduction(appartient(vz, E.restriction(vf, vX)), couple_z))
    assert res.conclusion == E.est_un_graphe(E.restriction(vf, vX)), "restriction_est_graphe : forme"
    assert res.est_clos, "restriction_est_graphe : non clos"
    return res


# ── Valeurs d'une réunion de graphes fonctionnelle ────────────────────────────
def valeur_reunion_gauche(g, h, tt):
    """{est_fonctionnel(G∪H), t∈dom G} ⊢ (G∪H)(t) = G(t).   (g, h, t : termes.)

    (t,G(t))∈G ⊂ G∪H ; C46 sur le fonctionnel G∪H identifie la valeur."""
    vg, vh, vt = _t(g), _t(h), _t(tt)
    GuH, Gt = E.reunion(vg, vh), E.valeur(_t(g), _t(tt))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    h_dom = N.assume(appartient(vt, E.dom(vg)))
    exG = N.modus_ponens(h_dom, equivalence_avant(instancie(instancie(ax_dom, vg), vt)))
    in_G = _dech(valeur_dans_graphe(vg, vt), exG)               # (t, G(t)) ∈ G
    cpl = E.couple(vt, Gt)
    disj = N.modus_ponens(in_G, N.s2(appartient(cpl, vg), appartient(cpl, vh)))
    in_u = N.modus_ponens(disj, equivalence_arriere(membre_reunion_graphes(vg, vh, cpl)))
    ex_u = N.modus_ponens(in_u, N.s5(appartient(E.couple(vt, var("y")), GuH), Gt, "y"))
    vc_Gt = instancie(N.generalisation("y", valeur_caracterisation(GuH, vt)), Gt)
    eq = N.modus_ponens(in_u, equivalence_avant(vc_Gt))         # G(t) = (G∪H)(t)
    res = _dech(N.modus_ponens(eq, symetrie(Gt, E.valeur(GuH, vt))), ex_u)
    assert res.conclusion == egal(E.valeur(GuH, vt), Gt), "valeur_reunion_gauche : forme"
    assert res.hypotheses == frozenset({E.est_fonctionnel(GuH), appartient(vt, E.dom(vg))}), \
        "valeur_reunion_gauche : hyps"
    return res


def valeur_reunion_point(g, j, x):
    """{est_fonctionnel(G∪{(j,x)})} ⊢ (G∪{(j,x)})(j) = x.   (g, j, x : termes.)"""
    vg, vj, vx = _t(g), _t(j), _t(x)
    cpl = E.couple(vj, vx)
    S = E.singleton(cpl)
    GuS = E.reunion(vg, S)
    in_S = N.modus_ponens(N.reflexivite(cpl), equivalence_arriere(singleton_membre(cpl, cpl)))
    inSf, inGf = appartient(cpl, S), appartient(cpl, vg)
    disj = N.modus_ponens(N.modus_ponens(in_S, N.s2(inSf, inGf)), N.s3(inSf, inGf))
    in_u = N.modus_ponens(disj, equivalence_arriere(membre_reunion_graphes(vg, S, cpl)))
    ex_u = N.modus_ponens(in_u, N.s5(appartient(E.couple(vj, var("y")), GuS), vx, "y"))
    vc_x = instancie(N.generalisation("y", valeur_caracterisation(GuS, vj)), vx)
    eq = N.modus_ponens(in_u, equivalence_avant(vc_x))          # x = (G∪S)(j)
    res = _dech(N.modus_ponens(eq, symetrie(vx, E.valeur(GuS, vj))), ex_u)
    assert res.conclusion == egal(E.valeur(GuS, vj), vx), "valeur_reunion_point : forme"
    assert res.hypotheses == frozenset({E.est_fonctionnel(GuS)}), "valeur_reunion_point : hyps"
    return res


# ── Le prolongement-singleton G∪{(j,x)} est un point de ∏_{I∪{j}} ─────────────
#   (cas à UN indice adjoint de la construction de la démonstration de Prop. 6 —
#    graphe G ∪ ⋃_{ι∈I−J}{(ι,T_ι)} — avec témoin explicite x au lieu du τ-terme T_ι.)
# @livre Ch.II §5.4 Prop.6 | E II.34 L.5-12 | PDF p.85
def prolongement_un_point_dans_produit(gg, xx, u="uq", i="Iq", j="jq"):
    """{G ∈ ∏_I, x ∈ u_j, ¬(j∈I)} ⊢ G∪{(j,x)} ∈ ∏_{I∪{j}}.   (gg, xx : termes.)

    Hypothèses honnêtes : G point du produit partiel, x dans le facteur adjoint,
    j∉I (disjonction des domaines I ⊥ {j}).  gg, xx SANS « u », « i » libres
    (liants de la disjonction / du ∀-valeurs)."""
    vG, vx, vI, vj = _t(gg), _t(xx), _t(i), _t(j)
    prodI, union = E.produit_famille(_t(u), vI), indices_adjoints(i, j)
    S = E.singleton(E.couple(vj, vx))
    t0 = E.reunion(vG, S)
    h_G = N.assume(appartient(vG, prodI))
    h_x = N.assume(appartient(vx, E.valeur_famille(_t(u), vj)))
    h_j = N.assume(non(appartient(vj, vI)))
    incl_G, func_G, domeq_G, vals_G = _corps_membre(h_G, u, vI, vG)
    func_S = singleton_couple_fonctionnel(vj, vx)               # CLOS
    dom_S = dom_singleton_couple(vj, vx)                        # dom S = {j}, CLOS
    # (a) domaines disjoints : (∀u)¬(u∈dom G et u∈dom S)   [u∈I et u=j ⇒ j∈I, absurde]
    vu = var("u")
    conj_f = et(appartient(vu, E.dom(vG)), appartient(vu, E.dom(S)))
    hd = N.assume(conj_f)
    u_I = _leibniz_membre(conjonction_elim_gauche(hd), domeq_G, vu)      # u∈I
    u_sj = _leibniz_membre(conjonction_elim_droite(hd), dom_S, vu)       # u∈{j}
    u_j = N.modus_ponens(u_sj, equivalence_avant(singleton_membre(vu, vj)))   # u=j
    j_I = N.modus_ponens(u_I, equivalence_avant(N.modus_ponens(
        u_j, N.s6(vu, vj, "w", appartient(var("w"), vI)))))              # j∈I
    absurd = N.modus_ponens(j_I, N.modus_ponens(
        h_j, N.s2(non(appartient(vj, vI)), non(conj_f))))
    imp = N.loi_deduction(conj_f, absurd)
    _, notP = antecedent_consequent(imp.conclusion)
    disj = N.generalisation("u", N.modus_ponens(imp, N.s1(notP)))
    # (b) fonctionnalité du recollement (pivot, 3 prémisses déchargées)
    func_t0 = _dech(reunion_graphes_fonctionnelle(vG, S), func_G, func_S, disj)
    # (c) domaine : dom(G∪S) = dom G ∪ dom S = I ∪ {j}
    c1 = N.modus_ponens(domeq_G, congruence_terme(E.dom(vG), vI,
                                                  E.reunion(var("w"), E.dom(S))))
    c2 = N.modus_ponens(dom_S, congruence_terme(E.dom(S), E.singleton(vj),
                                                E.reunion(vI, var("w"))))
    dom_t0 = composer_egalites(dom_reunion_graphes(vG, S), composer_egalites(c1, c2))
    # (d) valeurs : (∀i)(i∈I∪{j} ⇒ (G∪S)(i) ∈ u_i)   — par cas i∈I / i∈{j}
    vi = var("i")
    hi = N.assume(appartient(vi, union))
    disj_i = N.modus_ponens(hi, equivalence_avant(_car_union(i, j, vi)))
    fam = lambda t: E.valeur_famille(_t(u), t)
    #   cas gauche : i∈I ⇒ (G∪S)(i) = G(i) ∈ u_i
    hiI = N.assume(appartient(vi, vI))
    i_domG = _leibniz_membre_arriere(hiI, domeq_G, vi)          # i ∈ dom G
    vrg = _dech(valeur_reunion_gauche(vG, S, vi), func_t0, i_domG)
    G_i_in = N.modus_ponens(hiI, instancie(vals_G, vi))         # G(i) ∈ u_i
    leib = N.modus_ponens(vrg, N.s6(E.valeur(t0, vi), E.valeur(vG, vi), "w",
                                    appartient(var("w"), fam(vi))))
    brA = N.loi_deduction(appartient(vi, vI),
                          N.modus_ponens(G_i_in, equivalence_arriere(leib)))
    #   cas droit : i∈{j} ⇒ i=j ⇒ (G∪S)(i) = x ∈ u_i
    hiJ = N.assume(appartient(vi, E.singleton(vj)))
    i_eq_j = N.modus_ponens(hiJ, equivalence_avant(singleton_membre(vi, vj)))
    vrp = _dech(valeur_reunion_point(vG, vj, vx), func_t0)
    leib_x = N.modus_ponens(vrp, N.s6(E.valeur(t0, vj), vx, "w",
                                      appartient(var("w"), fam(vj))))
    t0j_in = N.modus_ponens(h_x, equivalence_arriere(leib_x))   # (G∪S)(j) ∈ u_j
    transport = N.modus_ponens(N.modus_ponens(i_eq_j, symetrie(vi, vj)),
        N.s6(vj, vi, "w", appartient(E.valeur(t0, var("w")), fam(var("w")))))
    brB = N.loi_deduction(appartient(vi, E.singleton(vj)),
                          N.modus_ponens(t0j_in, equivalence_avant(transport)))
    vals_t0 = N.generalisation("i", N.loi_deduction(appartient(vi, union),
                                                    cas(disj_i, brA, brB)))
    # (e) conjoint de TÊTE : G∪{(j,x)} ⊂ (I∪{j}) × ⋃_{ι∈I∪{j}} u_ι.  « G est un
    #     graphe » se LIT maintenant du conjoint de tête de G∈∏_I (ce n'est plus
    #     une hypothèse honnête), et l'adjonction d'un couple le préserve (B3).
    graphe_G = graphe_du_point(incl_G, vG, vI, _t(u))
    graphe_t0 = _dech(graphe_apres_adjonction(vG, vj, vx), graphe_G)
    tete = conjoint_de_tete(graphe_t0, func_t0, dom_t0, vals_t0, t0, _t(u), union)
    # assemblage → G∪{(j,x)} ∈ ∏_{I∪{j}}
    corps = corps_membre(tete, func_t0, dom_t0, vals_t0)
    res = N.modus_ponens(corps, equivalence_arriere(_inst_fam(u, union, t0)))
    assert res.conclusion == appartient(t0, produit_total(u, i, j)), "prolongement : forme"
    assert res.hypotheses == frozenset({h_G.conclusion, h_x.conclusion, h_j.conclusion}), \
        "prolongement : hyps"
    return res


__all__ = ["restriction_dans_produit", "restriction_est_graphe",
           "valeur_reunion_gauche", "valeur_reunion_point",
           "prolongement_un_point_dans_produit"]
