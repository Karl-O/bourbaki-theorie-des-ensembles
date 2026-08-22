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
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
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


__all__ = ["valeur_zero_iteration"]
