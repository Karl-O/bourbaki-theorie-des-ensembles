# -*- coding: utf-8 -*-
"""§III.6.2 — R8' (étape 2) : L'ÉVALUATION EN 0 DE L'ITÉRATION VRAIE.

🎯 CIBLE (une hypothèse honnête — être solution) :

    valeur_zero_iteration(S, a) :
        { est_solution_rec(g, T_{S,a}, G_≤, ℕ) }  ⊢  valeur(g, 0) = a

L'équation de la solution en 0 lit g|seg(0) ; le segment de 0 est VIDE
(segment_zero_NN_est_vide, le plus petit élément), la restriction au vide est
vide, et la règle au vide vaut a (t_iter_en_vide) :
    g(0) = T(g|seg 0) = T(g|∅) = T(∅) = a.
Le g est HYPOTHÉTIQUE (les consommateurs K6-K7 élimineront le témoin du
(∃g) de iteration_N_vrai).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  S OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import (
    restriction_vide_est_vide,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, zero_dans_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_segment_zero_NN import (
    segment_zero_NN, segment_zero_NN_est_vide,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie, t_iter_en_vide,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


# @livre Ch.III §6.2 Crit.C63 | E III.46 L.21-24 | PDF p.149  (la première équation
#   de l'itération : f(0) = a — le cas u=∅ de la règle, en n=0)
def valeur_zero_iteration(S, a, g="gcap", V="Vitv", yname="yitv"):
    """🎯 R8'-étape 2 : { est_solution_rec(g, T_{S,a}, G_≤, ℕ) }
       ⊢ valeur(g, 0) = a                                      [1 hyp honnête]."""
    va = _t(a)
    vg = _t(g)
    T = regle_iteration_vraie(S, a, yname)
    GNN = G_ordre_NN()
    NN = ensemble_NN()
    seg0 = segment_zero_NN()                                # seg(≤_G, ℕ, 0)

    h_sol = N.assume(est_solution_rec(vg, T, GNN, NN))      # sol(g)     [HONNÊTE]
    dom_g = conjonction_elim_droite(conjonction_elim_gauche(h_sol))   # dom g = ℕ
    eq_g = conjonction_elim_droite(h_sol)                   # l'équation (lieur zesr)

    # 0 ∈ dom g   (0∈ℕ CLOS + Leibniz dom g = ℕ, sens ⇐)
    z_dom = N.modus_ponens(zero_dans_NN(), equivalence_arriere(N.modus_ponens(
        dom_g, N.s6(E.dom(vg), NN, "wite", appartient(ZERO, var("wite"))))))
    # g(0) = T(g|seg 0)   (l'équation instanciée en 0)
    eq_0 = N.modus_ponens(z_dom, instancie(eq_g, ZERO))

    # g|seg(0) = g|∅ = ∅   (le segment de 0 est vide, la restriction au vide aussi)
    r_seg0_vide = N.modus_ponens(segment_zero_NN_est_vide(), congruence_terme(
        seg0, E.VIDE, E.restriction(vg, var("wite")), "wite"))   # g|seg0 = g|∅
    r_vide = composer_egalites(r_seg0_vide, restriction_vide_est_vide(vg))  # = ∅
    # T(g|seg 0) = T(∅)   (congruence à travers la règle opaque, trou frais)
    T_eq = N.modus_ponens(r_vide, congruence_terme(
        E.restriction(vg, seg0), E.VIDE, T(var("witr")), "witr"))
    # chaîne : g(0) = T(g|seg 0) = T(∅) = a
    res = composer_egalites(composer_egalites(eq_0, T_eq), t_iter_en_vide(S, a, yname))

    assert res.conclusion == egal(E.valeur(vg, ZERO), va), "valeur_zero_iteration : forme"
    assert list(res.hypotheses) == [est_solution_rec(vg, T, GNN, NN)], \
        "valeur_zero_iteration : hyps ≠ {sol(g)}"
    return res


# @livre Ch.III §6.2 Crit.C63 | E III.46 L.21-24 | PDF p.149  (la seconde équation
#   de l'itération : f(succ n) = S(f(n)) — le cas u≠∅, le max du segment vaut n)
def valeur_succ_iteration(S, a, n="nitv", g="gcap", V="Vitv", yname="yitv"):
    """🎯 R8'-étape 3 : { est_solution_rec(g, T_{S,a}, G_≤, ℕ),  n∈ℕ }
       ⊢ valeur(g, succ n) = S(valeur(g, n))                   [2 hyps honnêtes].

    u := g|seg(succ n) est NON VIDE ((n, g(n)) y habite — h4 : n∈seg(succ n)) ;
    t_fac_en_non_vide évalue T(u) = S(u(M(dom u))) ; la chaîne de réécritures
    dom u = seg(succ n) = [0,n] et M([0,n]) = n (max_intervalle) puis
    u(n) = g(n) (restriction_valeur) conclut."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe, non
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        successeur, est_entier,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import terme_plus_grand
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
        restriction_dom_sous_inclusion, restriction_valeur, _couple_restriction,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import (
        t_fac_en_non_vide,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_pont_segment_iii5 import (
        segment_succ_est_intervalle,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import (
        intervalle_zero, max_intervalle_vaut_n_entier,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
        appartenance_NN_instanciee,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (
        h1_succ_dans_NN, h4_n_dans_seg,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_dans_graphe
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_equation_globale import (
        seg_inclus_E,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus

    vg, vn = _t(g), _t(n)
    T = regle_iteration_vraie(S, a, yname)
    GNN = G_ordre_NN()
    NN = ensemble_NN()
    sn = successeur(vn)
    segsucc = E.segment_extremite(GNN, NN, sn)              # == segment_succ_NN(n)
    u = E.restriction(vg, segsucc)
    gn = E.valeur(vg, vn)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    h_sol = N.assume(est_solution_rec(vg, T, GNN, NN))      # sol(g)     [HONNÊTE]
    h_nN = N.assume(appartient(vn, NN))                     # n∈ℕ        [HONNÊTE]
    func_g = conjonction_elim_gauche(conjonction_elim_gauche(h_sol))
    dom_g = conjonction_elim_droite(conjonction_elim_gauche(h_sol))
    eq_g = conjonction_elim_droite(h_sol)
    fini_n = N.modus_ponens(h_nN, equivalence_avant(
        appartenance_NN_instanciee(vn, "x", "y")))          # Fini n

    # succ n ∈ ℕ ⊂ dom g, l'équation instanciée
    sn_NN = N.modus_ponens(fini_n, instancie(h1_succ_dans_NN(), vn))
    sn_dom = N.modus_ponens(sn_NN, equivalence_arriere(N.modus_ponens(
        dom_g, N.s6(E.dom(vg), NN, "wite", appartient(sn, var("wite"))))))
    eq_sn = N.modus_ponens(sn_dom, instancie(eq_g, sn))     # g(succ n)=T(u)

    # (n, g(n)) ∈ u  — donc u ≠ ∅
    n_dom = N.modus_ponens(h_nN, equivalence_arriere(N.modus_ponens(
        dom_g, N.s6(E.dom(vg), NN, "wite", appartient(vn, var("wite"))))))
    ex_y = N.modus_ponens(n_dom, equivalence_avant(
        instancie(instancie(ax_dom, vg), vn)))
    in_g = _cut(ex_y, existe("y", appartient(E.couple(vn, var("y")), vg)),
                _cut(func_g, E.est_fonctionnel(vg), valeur_dans_graphe(vg, vn)))
    n_seg = N.modus_ponens(fini_n, instancie(h4_n_dans_seg(), vn))   # n∈seg(succ n)
    in_u = N.modus_ponens(conjonction_intro(n_seg, in_g), equivalence_arriere(
        _couple_restriction(vg, segsucc, vn, gn)))          # (n,g(n))∈u
    cpl = E.couple(vn, gn)
    h_uv = N.assume(egal(u, E.VIDE))
    in_vide = N.modus_ponens(in_u, equivalence_avant(N.modus_ponens(
        h_uv, N.s6(u, E.VIDE, "witn", appartient(cpl, var("witn"))))))
    neg_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), cpl)
    cible_neg = non(egal(u, E.VIDE))
    inner = N.modus_ponens(in_vide, N.modus_ponens(neg_vide,
        N.s2(non(appartient(cpl, E.VIDE)), cible_neg)))
    nonvide = N.modus_ponens(N.loi_deduction(egal(u, E.VIDE), inner),
                             N.s1(cible_neg))               # ¬(u=∅)

    # T(u) = S(u(M(dom u))), puis la chaîne de réécritures du max
    tval = t_fac_en_non_vide(T, u, nonvide)
    M_tpl = lambda hole: S(E.valeur(u, terme_plus_grand(inf_egal_card, hole, "m", "x")))
    #   dom u = seg(succ n)   (seg⊂ℕ=dom g, restriction pleine du domaine)
    sub = N.modus_ponens(seg_inclus_E(GNN, NN, sn), equivalence_avant(
        N.modus_ponens(N.modus_ponens(dom_g, symetrie(E.dom(vg), NN)),
                       N.s6(NN, E.dom(vg), "wite", inclus(segsucc, var("wite"))))))
    du = N.modus_ponens(sub, restriction_dom_sous_inclusion(vg, segsucc))
    c1 = N.modus_ponens(du, congruence_terme(E.dom(u), segsucc,
                                             M_tpl(var("witm")), "witm"))
    #   seg(succ n) = [0,n]   (le pont, sous n∈ℕ)
    pont = _cut(h_nN, appartient(vn, NN), segment_succ_est_intervalle(vn))
    c2 = N.modus_ponens(pont, congruence_terme(segsucc, intervalle_zero(vn),
                                               M_tpl(var("witm")), "witm"))
    #   M([0,n]) = n   (max_intervalle, sous est_entier n == Fini n)
    maxi = _cut(fini_n, est_entier(vn), max_intervalle_vaut_n_entier(n))
    c3 = N.modus_ponens(maxi, congruence_terme(
        terme_plus_grand(inf_egal_card, intervalle_zero(vn), "m", "x"), vn,
        S(E.valeur(u, var("witp"))), "witp"))
    #   u(n) = g(n)   (restriction_valeur, coupures)
    rv = restriction_valeur(vg, segsucc, vn)
    rv = _cut(n_seg, appartient(vn, segsucc), rv)
    rv = _cut(n_dom, appartient(vn, E.dom(vg)), rv)
    rv = _cut(func_g, E.est_fonctionnel(vg), rv)
    c4 = N.modus_ponens(rv, congruence_terme(E.valeur(u, vn), gn,
                                             S(var("wits")), "wits"))
    res = composer_egalites(composer_egalites(composer_egalites(
        composer_egalites(composer_egalites(eq_sn, tval), c1), c2), c3), c4)

    assert res.conclusion == egal(E.valeur(vg, sn), S(gn)), "valeur_succ : forme"
    assert len(res.hypotheses) == 2, "valeur_succ : hyps ≠ 2"
    return res


__all__ = ["valeur_zero_iteration", "valeur_succ_iteration"]
