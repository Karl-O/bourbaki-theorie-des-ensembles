# -*- coding: utf-8 -*-
"""§III.6.2 — R8' (final) : 🎯🎯🎯 LE CRITÈRE C63 VÉRITABLE (l'itération du livre).

    iteration_complete(S, a) :
        { regle_dans_V(T_{S,a}, V) }
        ⊢ (∃g)( g(0)=a  ∧  (∀n)( n∈ℕ ⇒ g(succ n) = S(g(n)) ) )

C'EST LE C63 DE BOURBAKI (E III.46) : « il existe une suite (g(n)) telle que
g(0)=a et g(n+1)=S(g(n)) » — obtenu ici DEPUIS le critère C60-VRAI (la règle
lit la restriction) et non depuis la tabulation : le témoin du (∃) de
iteration_N_vrai vérifie les deux équations (valeur_zero/valeur_succ), on les
conjoint sous le corps, S5 réintroduit l'existentiel, l'élimination du témoin
referme.  UNE hypothèse honnête : la règle bornée (la donnée « S à valeurs
dans V » de Bourbaki).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  S OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie, iteration_N_vrai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_eval import (
    valeur_zero_iteration, valeur_succ_iteration,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def corps_c63(S, a, g="gcap", n="nitv"):
    """Le corps du C63 : g(0)=a ∧ (∀n)(n∈ℕ ⇒ g(succ n)=S(g(n)))."""
    va, vg, vn = _t(a), _t(g), var(n)
    NN = ensemble_NN()
    return et(egal(E.valeur(vg, ZERO), va),
              pourtout(n, impl(appartient(vn, NN),
                               egal(E.valeur(vg, successeur(vn)),
                                    S(E.valeur(vg, vn))))))


# @livre Ch.III §6.2 Crit.C63 | E III.46 L.21-24 | PDF p.149  (LE critère d'itération :
#   « il existe une suite avec g(0)=a et g(n+1)=S(g(n)) » — ici depuis C60-VRAI)
def iteration_complete(S, a, V="Vitv", yname="yitv"):
    """🎯🎯🎯 LE C63 VÉRITABLE :
       { regle_dans_V(T_{S,a}, V) }
       ⊢ (∃gcap)( gcap(0)=a ∧ (∀nitv)(nitv∈ℕ ⇒ gcap(succ nitv)=S(gcap(nitv))) )."""
    T = regle_iteration_vraie(S, a, yname)
    GNN = G_ordre_NN()
    NN = ensemble_NN()
    corps_sol = est_solution_rec(var("gcap"), T, GNN, NN)

    # sous le corps-témoin : les deux équations, conjointes
    z = valeur_zero_iteration(S, a, g="gcap", V=V, yname=yname)      # {sol}
    vs = valeur_succ_iteration(S, a, n="nitv", g="gcap", V=V, yname=yname)
    gen = N.generalisation("nitv", N.loi_deduction(
        appartient(var("nitv"), NN), vs))                            # {sol}
    conj = conjonction_intro(z, gen)                                 # {sol}
    # S5 au témoin gcap lui-même, puis élimination du témoin
    cible = corps_c63(S, a)
    ex_c63 = N.modus_ponens(conj, N.s5(cible, var("gcap"), "gcap"))  # {sol}
    imp_ex = existe_elimination(N.loi_deduction(corps_sol, ex_c63), "gcap")
    res = N.modus_ponens(iteration_N_vrai(S, a, V, yname), imp_ex)

    assert res.conclusion == existe("gcap", cible), "iteration_complete : forme"
    assert list(res.hypotheses) == [regle_dans_V(T, V)], \
        "iteration_complete : hyps ≠ {règle bornée}"
    return res


def corps_c63_fort(S, a, g="gcap", n="nitv"):
    """Le corps RENFORCÉ : func g ∧ dom g=ℕ ∧ corps_c63 — le témoin devient
    utilisable comme graphe d'application (équipotence, Lemme 1 §III.6.3)."""
    vg = _t(g)
    return et(et(E.est_fonctionnel(vg), egal(E.dom(vg), ensemble_NN())),
              corps_c63(S, a, g, n))


def iteration_complete_forte(S, a, V="Vitv", yname="yitv"):
    """🎯 C63 FORT : { regle_dans_V(T_{S,a}, V) }
       ⊢ (∃g)( est_fonctionnel(g) ∧ dom g=ℕ ∧ g(0)=a ∧ (∀n∈ℕ)(g(succ n)=S(g(n))) ).

    Même squelette que iteration_complete, mais l'∃ GARDE la fonctionnalité et
    le domaine du témoin (extraits de est_solution_rec avant l'élimination) —
    ce que la version faible jetait."""
    T = regle_iteration_vraie(S, a, yname)
    GNN = G_ordre_NN()
    NN = ensemble_NN()
    corps_sol = est_solution_rec(var("gcap"), T, GNN, NN)

    h_sol = N.assume(corps_sol)                             # {sol}
    func = conjonction_elim_gauche(conjonction_elim_gauche(h_sol))
    dom = conjonction_elim_droite(conjonction_elim_gauche(h_sol))
    z = valeur_zero_iteration(S, a, g="gcap", V=V, yname=yname)      # {sol}
    vs = valeur_succ_iteration(S, a, n="nitv", g="gcap", V=V, yname=yname)
    gen = N.generalisation("nitv", N.loi_deduction(
        appartient(var("nitv"), NN), vs))                            # {sol}
    conj = conjonction_intro(conjonction_intro(func, dom),
                             conjonction_intro(z, gen))              # {sol}
    cible = corps_c63_fort(S, a)
    ex = N.modus_ponens(conj, N.s5(cible, var("gcap"), "gcap"))      # {sol}
    imp_ex = existe_elimination(N.loi_deduction(corps_sol, ex), "gcap")
    res = N.modus_ponens(iteration_N_vrai(S, a, V, yname), imp_ex)

    assert res.conclusion == existe("gcap", cible), \
        "iteration_complete_forte : forme"
    assert list(res.hypotheses) == [regle_dans_V(T, V)], \
        "iteration_complete_forte : hyps ≠ {règle bornée}"
    return res


__all__ = ["corps_c63", "iteration_complete",
           "corps_c63_fort", "iteration_complete_forte"]
