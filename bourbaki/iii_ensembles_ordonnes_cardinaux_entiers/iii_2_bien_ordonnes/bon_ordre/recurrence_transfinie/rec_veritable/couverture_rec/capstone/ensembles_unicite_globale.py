# -*- coding: utf-8 -*-
"""§III.2.2 — R7' (étape 4) : L'UNICITÉ GLOBALE DE LA SOLUTION.

🎯 CIBLES :

    est_solution_rec(g) := func g  ∧  dom g = E  ∧  (∀z∈dom g)(g(z)=vh(g|seg z))

    unicite_globale :
        { bo, est_solution_rec(g), est_solution_rec(h), graphe g, graphe h }
            ⊢  g = h

Deux solutions globales de la VRAIE équation coïncident : induction C59 sur le
prédicat ponctuel P(t) := g(t)=h(t) — l'hérédité passe par l'égalité des
restrictions g|seg = h|seg (extensionnalité sous l'HR) et la congruence C44 à
travers la règle opaque ; puis l'extensionnalité globale (doms = E) conclut.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout, inclus,
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
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    graphe_egal_par_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur, _restriction_fonctionnelle_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    restriction_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
    heredite_couverture, couverture_transfinie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
    equation_sur_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_equation_globale import (
    seg_inclus_E,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def est_solution_rec(g, vh, G, e):
    """« g est LA solution globale » : func g ∧ dom g=E ∧ équation-restriction."""
    vg = _t(g)
    return et(et(E.est_fonctionnel(vg), egal(E.dom(vg), _t(e))),
              equation_sur_seg(vg, vh, _t(G), _t(e)))


def unicite_globale(vh, g="gcap", h="hcap", G="Gsr", e="Esr"):
    """🎯 R7'-étape 4 : {bo, sol(g), sol(h), graphe g, graphe h} ⊢ g = h."""
    vg, vgh, vG, ve = _t(g), _t(h), _t(G), _t(e)
    h_sg = N.assume(est_solution_rec(vg, vh, vG, ve))       # sol(g)     [HONNÊTE]
    h_sh = N.assume(est_solution_rec(vgh, vh, vG, ve))      # sol(h)     [HONNÊTE]
    h_gg = N.assume(E.est_un_graphe(vg))                    # graphe g   [HONNÊTE]
    h_gh = N.assume(E.est_un_graphe(vgh))                   # graphe h   [HONNÊTE]
    func_g = conjonction_elim_gauche(conjonction_elim_gauche(h_sg))
    dom_g = conjonction_elim_droite(conjonction_elim_gauche(h_sg))
    eq_g = conjonction_elim_droite(h_sg)
    func_h = conjonction_elim_gauche(conjonction_elim_gauche(h_sh))
    dom_h = conjonction_elim_droite(conjonction_elim_gauche(h_sh))
    eq_h = conjonction_elim_droite(h_sh)

    P = lambda t: egal(E.valeur(vg, t), E.valeur(vgh, t))   # le couvert ponctuel

    # ── HÉRÉDITÉ : x0tf∈E, HR sur seg(x0tf) ⇒ g(x0tf)=h(x0tf) ────────────────
    vx0 = var("x0tf")
    segx0 = E.segment_extremite(vG, ve, vx0)
    rG_, rH_ = E.restriction(vg, segx0), E.restriction(vgh, segx0)
    h_xE = N.assume(appartient(vx0, ve))
    hr = pourtout("ytf", impl(appartient(var("ytf"), segx0), P(var("ytf"))))
    h_hr = N.assume(hr)
    sie = seg_inclus_E(G, e, "x0tf")                        # CLOS : seg⊂E
    sub_g = N.modus_ponens(sie, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_g, symetrie(E.dom(vg), ve)),
        N.s6(ve, E.dom(vg), "wug", inclus(segx0, var("wug"))))))
    sub_h = N.modus_ponens(sie, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_h, symetrie(E.dom(vgh), ve)),
        N.s6(ve, E.dom(vgh), "wug", inclus(segx0, var("wug"))))))
    d_g = N.modus_ponens(sub_g, restriction_dom_sous_inclusion(vg, segx0))
    d_h = N.modus_ponens(sub_h, restriction_dom_sous_inclusion(vgh, segx0))
    dom_eq = composer_egalites(d_g, N.modus_ponens(d_h, symetrie(E.dom(rH_), segx0)))
    f_g = N.modus_ponens(func_g, _restriction_fonctionnelle_terme(vg, segx0))
    f_h = N.modus_ponens(func_h, _restriction_fonctionnelle_terme(vgh, segx0))
    gr_g = restriction_est_graphe(vg, segx0)
    gr_h = restriction_est_graphe(vgh, segx0)
    vt = var("x")
    h_t = N.assume(appartient(vt, E.dom(rG_)))
    t_seg = N.modus_ponens(h_t, equivalence_avant(N.modus_ponens(
        d_g, N.s6(E.dom(rG_), segx0, "wug", appartient(vt, var("wug"))))))
    t_domg = N.modus_ponens(t_seg, instancie(sub_g, vt))
    t_domh = N.modus_ponens(t_seg, instancie(sub_h, vt))
    rv_g = restriction_valeur(vg, segx0, vt)
    rv_g = _cut(t_seg, appartient(vt, segx0), rv_g)
    rv_g = _cut(t_domg, appartient(vt, E.dom(vg)), rv_g)
    rv_g = _cut(func_g, E.est_fonctionnel(vg), rv_g)        # (g|seg)(t)=g(t)
    ght = N.modus_ponens(t_seg, instancie(h_hr, vt))        # g(t)=h(t)  [HR]
    rv_h = restriction_valeur(vgh, segx0, vt)
    rv_h = _cut(t_seg, appartient(vt, segx0), rv_h)
    rv_h = _cut(t_domh, appartient(vt, E.dom(vgh)), rv_h)
    rv_h = _cut(func_h, E.est_fonctionnel(vgh), rv_h)       # (h|seg)(t)=h(t)
    chaine_t = composer_egalites(composer_egalites(rv_g, ght),
        N.modus_ponens(rv_h, symetrie(E.valeur(rH_, vt), E.valeur(vgh, vt))))
    val = N.generalisation("x", N.loi_deduction(appartient(vt, E.dom(rG_)), chaine_t))
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(f_g, f_h), gr_g), gr_h), dom_eq), val)
    cong = N.modus_ponens(N.modus_ponens(prem, graphe_egal_par_valeurs(rG_, rH_)),
        congruence_terme(rG_, rH_, vh(var("wrec")), "wrec"))  # vh(g|s)=vh(h|s)
    x_domg = N.modus_ponens(h_xE, equivalence_arriere(N.modus_ponens(
        dom_g, N.s6(E.dom(vg), ve, "wug", appartient(vx0, var("wug"))))))
    x_domh = N.modus_ponens(h_xE, equivalence_arriere(N.modus_ponens(
        dom_h, N.s6(E.dom(vgh), ve, "wug", appartient(vx0, var("wug"))))))
    eqg_x = N.modus_ponens(x_domg, instancie(eq_g, vx0))    # g(x0)=vh(g|seg x0)
    eqh_x = N.modus_ponens(x_domh, instancie(eq_h, vx0))
    chaine_x = composer_egalites(composer_egalites(eqg_x, cong),
        N.modus_ponens(eqh_x, symetrie(E.valeur(vgh, vx0), vh(rH_))))  # g(x0)=h(x0)
    her = N.generalisation("x0tf", N.loi_deduction(appartient(vx0, ve),
                           N.loi_deduction(hr, chaine_x)))
    assert her.conclusion == heredite_couverture(P, G, ve, "x0tf", "ytf"), \
        "unicite_globale : hérédité ≠ heredite_couverture"

    # ── C59 : (∀t∈E)( g(t)=h(t) ), puis l'extensionnalité globale ────────────
    cov = _cut(her, heredite_couverture(P, G, ve, "x0tf", "ytf"),
               couverture_transfinie(P, e, G))
    h_t2 = N.assume(appartient(vt, E.dom(vg)))
    t_E = N.modus_ponens(h_t2, equivalence_avant(N.modus_ponens(
        dom_g, N.s6(E.dom(vg), ve, "wug", appartient(vt, var("wug"))))))
    ght2 = N.modus_ponens(t_E, instancie(cov, vt))
    val2 = N.generalisation("x", N.loi_deduction(appartient(vt, E.dom(vg)), ght2))
    dom_gh = composer_egalites(dom_g, N.modus_ponens(dom_h, symetrie(E.dom(vgh), ve)))
    prem2 = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(func_g, func_h), h_gg), h_gh), dom_gh), val2)
    res = N.modus_ponens(prem2, graphe_egal_par_valeurs(vg, vgh))

    assert res.conclusion == egal(vg, vgh), "unicite_globale : ≠ g=h"
    assert len(res.hypotheses) == 5, "unicite_globale : hyps ≠ 5"
    assert res.conclusion not in res.hypotheses, "unicite_globale : VACUOUS"
    return res


__all__ = ["est_solution_rec", "unicite_globale"]
