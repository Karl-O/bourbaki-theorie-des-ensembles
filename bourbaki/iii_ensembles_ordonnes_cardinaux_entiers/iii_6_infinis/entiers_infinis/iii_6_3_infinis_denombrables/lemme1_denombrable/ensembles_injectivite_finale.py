# -*- coding: utf-8 -*-
"""§III.6.3 — K6d (brique 3) : L'INJECTIVITÉ COMPLÈTE DE L'ITÉRÉE.

🎯 CIBLE (g := le témoin gcap, hypothétique ; Γ = les 4 hyps du chantier) :

    injectivite_iteree :  Γ ∪ {hors, inj}  ⊢
        (∀n)( n∈ℕ ⇒ (∀m)( m∈ℕ ⇒ ( g(m)=g(n) ⇒ m=n ) ) )        [6 hyps]

Récurrence C61 sur P(n) := (∀m∈ℕ)( g(m)=g(n) ⇒ m=n ), le patron W3
(deux_valuation_unique) : chaque cas fait un tiers exclu sur m=0, le cas
m≠0 produit le prédécesseur (pfu CLOS), le témoin kpred s'élimine.
  • BASE : g(m)=g(0)=x0 ; si m=succ k alors g(succ k)=x0 contredit
    g_succ_evite_x0 (brique 1) — donc m=0.
  • PAS : g(m)=g(succ n) ; m=0 forcerait g(succ n)=x0 (absurde, brique 1) ;
    m=succ k donne g(succ k)=g(succ n), la brique 2 simplifie en
    g(k)=g(n), l'hypothèse de récurrence conclut k=n, donc m=succ n.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, non, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, tiers_exclu, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
    _ex_falso,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur, est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    fini_successeur_implique_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_valeurs_iteration import (
    _contexte, _cut,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_iteree import (
    g_succ_evite_x0, succ_simplification,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _corps_pred(vm, vkp):
    """Le corps du prédécesseur (== predecesseur_fini, lieur kpred ouvert)."""
    return et(et(egal(vm, successeur(vkp)), est_cardinal(vkp)),
              inf_strict_card(vkp, vm))


def _fini_k(b_eq, card_k, fini_m, vm, vkp):
    """{m=succ k, est_cardinal k, Fini m} ⊢ Fini k  (Leibniz + Prop. 1)."""
    leib = N.s6(vm, successeur(vkp), "wfi", est_fini(var("wfi")))
    fini_succk = N.modus_ponens(fini_m,
                                equivalence_avant(N.modus_ponens(b_eq, leib)))
    fsif = instancie(N.generalisation("afsk",
        fini_successeur_implique_fini("afsk")), vkp)
    return N.modus_ponens(fini_succk, N.modus_ponens(card_k, fsif))


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def injectivite_iteree(u, x0, e, g="gcap", m="mitv", n="nitv",
                       zname="zcl", yname="ycl"):
    """🎯 K6d : {corps, x0∈E, u⊂E×E, dom u=E, hors, injective_dans(u,E)} ⊢
       (∀n)( n∈ℕ ⇒ (∀m)( m∈ℕ ⇒ ( g(m)=g(n) ⇒ m=n ) ) )   [6 hyps].

    C61 sur P(n) := (∀m∈ℕ)(g(m)=g(n) ⇒ m=n), patron W3 : tiers exclu m=0,
    prédécesseur pfu (CLOS), témoin kpred éliminé dans chaque branche."""
    vu, vx0, ve, vg, S_c, h_x0, h_incl, h_dom, eq0, eq_succ = _contexte(
        u, x0, e, g, zname, yname)
    vm, vn, vkp = var(m), var(n), var("kpred")
    NN = ensemble_NN()
    gv = lambda t: E.valeur(vg, t)
    P = lambda t: pourtout(m, impl(appartient(vm, NN),
                                   impl(egal(gv(vm), gv(t)), egal(vm, t))))
    evite = g_succ_evite_x0(u, x0, e, g)                    # brique 1 [+hors]
    ss = succ_simplification(u, x0, e, g, m, n)             # brique 2 [+inj]
    pont_m = appartenance_NN_instanciee(vm, "x", "y")
    cong_g = congruence_terme(vm, successeur(vkp), gv(var("wij")), "wij")

    # ── BASE : P(0) ───────────────────────────────────────────────────────
    h_m = N.assume(appartient(vm, NN))
    h_eq = N.assume(egal(gv(vm), gv(ZERO)))
    gm_x0 = composer_egalites(h_eq, eq0)                    # g(m)=x0
    #   cas A : m=0 — direct
    brA = N.loi_deduction(egal(vm, ZERO), N.assume(egal(vm, ZERO)))
    #   cas B : m≠0 — prédécesseur, g(succ k)=x0 contredit la brique 1
    hb = N.assume(non(egal(vm, ZERO)))
    fini_m = N.modus_ponens(h_m, equivalence_avant(pont_m))
    pred = N.modus_ponens(conjonction_intro(fini_m, hb),
                          instancie(predecesseur_fini_universel_preuve(), vm))
    hK = N.assume(_corps_pred(vm, vkp))
    b_eq, card_k = conjonction_elim_gauche(conjonction_elim_gauche(hK)), \
        conjonction_elim_droite(conjonction_elim_gauche(hK))
    k_NN = N.modus_ponens(_fini_k(b_eq, card_k, fini_m, vm, vkp),
        equivalence_arriere(appartenance_NN_instanciee(vkp, "x", "y")))
    gs_x0 = composer_egalites(N.modus_ponens(
        N.modus_ponens(b_eq, cong_g),                       # g(m)=g(succ k)
        symetrie(gv(vm), gv(successeur(vkp)))), gm_x0)      # g(succ k)=x0
    absurd = _ex_falso(gs_x0, N.modus_ponens(k_NN, instancie(evite, vkp)),
                       egal(vm, ZERO))
    exk = existe_elimination(N.loi_deduction(_corps_pred(vm, vkp), absurd),
                             "kpred")
    brB = N.loi_deduction(non(egal(vm, ZERO)), N.modus_ponens(pred, exk))
    conc0 = cas(tiers_exclu(egal(vm, ZERO)), brA, brB)      # m=0
    p0 = N.generalisation(m, N.loi_deduction(appartient(vm, NN),
        N.loi_deduction(egal(gv(vm), gv(ZERO)), conc0)))
    assert p0.conclusion == P(ZERO), "injectivite : P[0] mal formé"

    # ── PAS : (Fini n ∧ P(n)) ⇒ P(succ n) ────────────────────────────────
    h2 = N.assume(et(est_fini(vn), P(vn)))
    fn, Pn = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)
    n_NN = N.modus_ponens(fn, equivalence_arriere(
        appartenance_NN_instanciee(vn, "x", "y")))
    h_m1 = N.assume(appartient(vm, NN))
    h_eq1 = N.assume(egal(gv(vm), gv(successeur(vn))))
    cible1 = egal(vm, successeur(vn))
    #   cas A : m=0 — g(succ n)=g(m)=g(0)=x0 contredit la brique 1 en n
    ha1 = N.assume(egal(vm, ZERO))
    gm_g0 = N.modus_ponens(ha1, congruence_terme(vm, ZERO, gv(var("wij")),
                                                 "wij"))    # g(m)=g(0)
    gsn_x0 = composer_egalites(composer_egalites(N.modus_ponens(
        h_eq1, symetrie(gv(vm), gv(successeur(vn)))), gm_g0), eq0)
    absurd1 = _ex_falso(gsn_x0, N.modus_ponens(n_NN, instancie(evite, vn)),
                        cible1)
    brA1 = N.loi_deduction(egal(vm, ZERO), absurd1)
    #   cas B : m=succ k — brique 2 puis l'hypothèse de récurrence
    hb1 = N.assume(non(egal(vm, ZERO)))
    fini_m1 = N.modus_ponens(h_m1, equivalence_avant(pont_m))
    pred1 = N.modus_ponens(conjonction_intro(fini_m1, hb1),
                           instancie(predecesseur_fini_universel_preuve(), vm))
    hK1 = N.assume(_corps_pred(vm, vkp))
    b_eq1 = conjonction_elim_gauche(conjonction_elim_gauche(hK1))
    card_k1 = conjonction_elim_droite(conjonction_elim_gauche(hK1))
    k_NN1 = N.modus_ponens(_fini_k(b_eq1, card_k1, fini_m1, vm, vkp),
        equivalence_arriere(appartenance_NN_instanciee(vkp, "x", "y")))
    coll = composer_egalites(N.modus_ponens(
        N.modus_ponens(b_eq1, cong_g),                      # g(m)=g(succ k)
        symetrie(gv(vm), gv(successeur(vkp)))), h_eq1)      # g(succ k)=g(succ n)
    gk_gn = N.modus_ponens(conjonction_intro(
        conjonction_intro(k_NN1, n_NN), coll),
        instancie(instancie(ss, vkp), vn))                  # g(k)=g(n)
    k_eq_n = N.modus_ponens(gk_gn, N.modus_ponens(k_NN1, instancie(Pn, vkp)))
    m_eq = composer_egalites(b_eq1, N.modus_ponens(k_eq_n,
        congruence_terme(vkp, vn, successeur(var("wij")), "wij")))  # m=succ n
    exk1 = existe_elimination(N.loi_deduction(_corps_pred(vm, vkp), m_eq),
                              "kpred")
    brB1 = N.loi_deduction(non(egal(vm, ZERO)), N.modus_ponens(pred1, exk1))
    conc1 = cas(tiers_exclu(egal(vm, ZERO)), brA1, brB1)    # m=succ n
    p_succ = N.generalisation(m, N.loi_deduction(appartient(vm, NN),
        N.loi_deduction(egal(gv(vm), gv(successeur(vn))), conc1)))
    assert p_succ.conclusion == P(successeur(vn)), "injectivite : P[succ] mal formé"
    pas = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)),
                                              p_succ))

    # ── assemblage C61 + conversion de la garde Fini → n∈ℕ ────────────────
    pr = _cut(predecesseur_fini_universel_preuve(), predecesseur_fini_universel(),
              principe_recurrence_preuve(P, n))
    concl = N.modus_ponens(conjonction_intro(p0, pas), pr)  # ∀n(Fini n ⇒ P(n))
    h_n = N.assume(appartient(vn, NN))
    fini2 = N.modus_ponens(h_n, equivalence_avant(
        appartenance_NN_instanciee(vn, "x", "y")))
    pn = N.modus_ponens(fini2, instancie(concl, vn))
    res = N.generalisation(n, N.loi_deduction(appartient(vn, NN), pn))
    assert res.conclusion == pourtout(n, impl(appartient(vn, NN), P(vn))), \
        "injectivite_iteree : forme"
    assert len(res.hypotheses) == 6, "injectivite_iteree : hyps ≠ 6"
    return res


__all__ = ["injectivite_iteree"]
