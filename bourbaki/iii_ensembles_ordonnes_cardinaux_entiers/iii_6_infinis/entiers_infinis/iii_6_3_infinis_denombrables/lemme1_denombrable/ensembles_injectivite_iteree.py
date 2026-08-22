# -*- coding: utf-8 -*-
"""§III.6.3 — K6d (briques 1-2) : L'ITÉRÉE ÉVITE x0 ET SE SIMPLIFIE.

🎯 CIBLES (g := le témoin gcap, hypothétique ; Γ = les hyps du chantier) :

    x0_hors_image(u, x0, e) := (∀t)( t∈E ⇒ ¬(u(t)=x0) )     [la donnée Dedekind]

    g_succ_evite_x0 :  Γ ∪ {hors}  ⊢ (∀n)( n∈ℕ ⇒ ¬(g(succ n)=x0) )
    succ_simplification : Γ ∪ {inj} ⊢
        (∀m)(∀n)( (m∈ℕ ∧ n∈ℕ ∧ g(succ m)=g(succ n)) ⇒ g(m)=g(n) )

L'argument du livre : x0 n'est jamais ré-atteint (u le rate), et
l'injectivité de u fait « remonter » toute collision d'un cran.  La brique 3
(l'injectivité complète, C61 double avec case-split par le prédécesseur)
assemblera ces deux-là.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, non, appartient, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_valeurs_iteration import (
    valeurs_dans_E, equation_declampee,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def x0_hors_image(u, x0, e, t="thi"):
    """La donnée Dedekind : (∀t)( t∈E ⇒ ¬(u(t)=x0) ) — x0 n'est pas atteint."""
    vu, vx0, ve, vt = _t(u), _t(x0), _t(e), var(t)
    return pourtout(t, impl(appartient(vt, ve),
                            non(egal(E.valeur(vu, vt), vx0))))


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def g_succ_evite_x0(u, x0, e, g="gcap", n="nitv"):
    """{corps, x0∈E, u⊂E×E, dom u=E, hors} ⊢ (∀n∈ℕ)(¬(g(succ n)=x0))  [5 hyps].

    g(succ n)=u(g(n)) avec g(n)∈E, et u(g(n))≠x0 (la donnée) ; toute égalité
    g(succ n)=x0 forcerait u(g(n))=x0 — ex falso encodé-∨ puis S1."""
    vu, vx0, ve, vg, vn = _t(u), _t(x0), _t(e), _t(g), var(n)
    NN = ensemble_NN()
    h_hors = N.assume(x0_hors_image(u, x0, e))              # la donnée [HONNÊTE]
    eqd = equation_declampee(u, x0, e, g)                   # {4 hyps du chantier}
    vals = valeurs_dans_E(u, x0, e, g)

    h_n = N.assume(appartient(vn, NN))
    eq_n = N.modus_ponens(h_n, instancie(eqd, vn))          # g(succ n)=u(g(n))
    gn_in = N.modus_ponens(h_n, instancie(vals, vn))        # g(n)∈E
    ne = N.modus_ponens(gn_in, instancie(h_hors, E.valeur(vg, vn)))
    #   ¬(u(g(n))=x0) ; supposer g(succ n)=x0 donne u(g(n))=x0 : absurde
    gs = E.valeur(vg, successeur(vn))
    h_abs = N.assume(egal(gs, vx0))
    u_eq = composer_egalites(N.modus_ponens(eq_n, symetrie(gs, E.valeur(vu, E.valeur(vg, vn)))),
                             h_abs)                         # u(g(n))=x0
    cible = non(egal(gs, vx0))
    inner = N.modus_ponens(u_eq, N.modus_ponens(ne,
        N.s2(non(egal(E.valeur(vu, E.valeur(vg, vn)), vx0)), cible)))
    res_n = N.modus_ponens(N.loi_deduction(egal(gs, vx0), inner), N.s1(cible))
    res = N.generalisation(n, N.loi_deduction(appartient(vn, NN), res_n))
    assert res.conclusion == pourtout(n, impl(appartient(vn, NN),
                                              non(egal(gs, vx0)))), \
        "g_succ_evite_x0 : forme"
    assert len(res.hypotheses) == 5, "g_succ_evite_x0 : hyps ≠ 5"
    return res


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def succ_simplification(u, x0, e, g="gcap", m="mitv", n="nitv"):
    """{corps, x0∈E, u⊂E×E, dom u=E, injective_dans(u,E)} ⊢
       (∀m)(∀n)( (m∈ℕ ∧ n∈ℕ ∧ g(succ m)=g(succ n)) ⇒ g(m)=g(n) )   [5 hyps].

    Les deux équations déclampées transportent la collision sur u, que
    l'injectivité gardée simplifie (les deux valeurs sont dans E)."""
    vu, vx0, ve, vg, vm, vn = _t(u), _t(x0), _t(e), _t(g), var(m), var(n)
    NN = ensemble_NN()
    h_inj = N.assume(E.injective_dans(vu, ve))              # u injective [HONNÊTE]
    eqd = equation_declampee(u, x0, e, g)
    vals = valeurs_dans_E(u, x0, e, g)
    gm, gn = E.valeur(vg, vm), E.valeur(vg, vn)

    ant = et(et(appartient(vm, NN), appartient(vn, NN)),
             egal(E.valeur(vg, successeur(vm)), E.valeur(vg, successeur(vn))))
    h_ant = N.assume(ant)
    m_NN = conjonction_elim_gauche(conjonction_elim_gauche(h_ant))
    n_NN = conjonction_elim_droite(conjonction_elim_gauche(h_ant))
    coll = conjonction_elim_droite(h_ant)                   # g(succ m)=g(succ n)
    eq_m = N.modus_ponens(m_NN, instancie(eqd, vm))         # g(succ m)=u(g(m))
    eq_n = N.modus_ponens(n_NN, instancie(eqd, vn))         # g(succ n)=u(g(n))
    gm_in = N.modus_ponens(m_NN, instancie(vals, vm))
    gn_in = N.modus_ponens(n_NN, instancie(vals, vn))
    # u(g(m)) = g(succ m) = g(succ n) = u(g(n))
    u_coll = composer_egalites(composer_egalites(
        N.modus_ponens(eq_m, symetrie(E.valeur(vg, successeur(vm)),
                                      E.valeur(vu, gm))), coll), eq_n)
    inj_inst = instancie(instancie(h_inj, gm), gn)
    res_mn = N.modus_ponens(conjonction_intro(
        conjonction_intro(gm_in, gn_in), u_coll), inj_inst)  # g(m)=g(n)
    res = N.generalisation(m, N.generalisation(n,
        N.loi_deduction(ant, res_mn)))
    assert res.conclusion == pourtout(m, pourtout(n, impl(ant, egal(gm, gn)))), \
        "succ_simplification : forme"
    assert len(res.hypotheses) == 5, "succ_simplification : hyps ≠ 5"
    return res


__all__ = ["x0_hors_image", "g_succ_evite_x0", "succ_simplification"]
