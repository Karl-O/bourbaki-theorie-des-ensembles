# -*- coding: utf-8 -*-
"""§III.6.3 — K6c : LES VALEURS DE L'ITÉRÉE VIVENT DANS E (le déclampage).

🎯 CIBLES (g := le témoin gcap de l'itération Dedekind, HYPOTHÉTIQUE) :

    valeurs_dans_E :
        { corps_c63(S_c, x0),  x0∈E,  u⊂E×E,  dom u=E }
            ⊢ (∀n)( n∈ℕ ⇒ valeur(g, n)∈E )

    equation_declampee :
        { mêmes }  ⊢ (∀n)( n∈ℕ ⇒ valeur(g, succ n) = valeur(u, valeur(g, n)) )

Récurrence C61 sur P(n) := g(n)∈E : base g(0)=x0∈E ; pas g(succ n) =
clamp(u(g(n))) = u(g(n)) ∈ E (valeur_dans_codomaine sous l'HR, clamp_eval).
Le DÉCLAMPAGE en découle : l'équation de l'itérée est CELLE DU LIVRE,
g(n+1)=u(g(n)) — le clamp était un échafaudage, invisible sur ℕ.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
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
    symetrie, composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur, est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import (
    valeur_dans_codomaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    regle_clampee, clamp_eval,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _contexte(u, x0, e, g, zname, yname):
    """Les hypothèses honnêtes partagées et les extraits du corps-témoin."""
    vu, vx0, ve, vg = _t(u), _t(x0), _t(e), _t(g)
    T, S_c = regle_clampee(u, x0, e, zname, yname)
    h_corps = N.assume(corps_c63(S_c, vx0, g=g))            # le témoin   [HONNÊTE]
    h_x0 = N.assume(appartient(vx0, ve))                    # x0∈E        [HONNÊTE]
    h_incl = N.assume(inclus(vu, E.produit(ve, ve)))        # u⊂E×E       [HONNÊTE]
    h_dom = N.assume(egal(E.dom(vu), ve))                   # dom u=E     [HONNÊTE]
    eq0 = conjonction_elim_gauche(h_corps)                  # g(0)=x0
    eq_succ = conjonction_elim_droite(h_corps)              # (∀nitv)(…)
    return vu, vx0, ve, vg, S_c, h_x0, h_incl, h_dom, eq0, eq_succ


def _u_val_dans_E(vu, ve, t, h_incl, h_dom, preuve_t_in):
    """De t∈E (preuve), conclure u(t)∈E (valeur_dans_codomaine, coupures)."""
    vdc = valeur_dans_codomaine(vu, ve, ve, t)
    vdc = _cut(h_incl, inclus(vu, E.produit(ve, ve)), vdc)
    vdc = _cut(h_dom, egal(E.dom(vu), ve), vdc)
    return _cut(preuve_t_in, appartient(t, ve), vdc)        # u(t)∈E


# @livre Ch.III §6.2 Ex.1 | E III.47 L.7-12 | PDF p.150  (« on a f(n)∈E ; f est
#   par suite une application de ℕ dans E » — la moitié « valeurs dans E »)
def valeurs_dans_E(u, x0, e, g="gcap", zname="zcl", yname="ycl", n="nitv"):
    """🎯 K6c : {corps, x0∈E, u⊂E×E, dom u=E} ⊢ (∀n)(n∈ℕ ⇒ g(n)∈E)  [4 hyps]."""
    vu, vx0, ve, vg, S_c, h_x0, h_incl, h_dom, eq0, eq_succ = _contexte(
        u, x0, e, g, zname, yname)
    vn = var(n)
    NN = ensemble_NN()
    P = lambda t: appartient(E.valeur(vg, t), ve)

    # base : g(0)=x0 ∈ E  (Leibniz arrière)
    base = N.modus_ponens(h_x0, equivalence_arriere(N.modus_ponens(
        eq0, N.s6(E.valeur(vg, ZERO), vx0, "wvi", appartient(var("wvi"), ve)))))
    # pas : (Fini n ∧ g(n)∈E) ⇒ g(succ n)∈E
    h_pas = N.assume(et(est_fini(vn), P(vn)))
    fini_n = conjonction_elim_gauche(h_pas)
    hr = conjonction_elim_droite(h_pas)                     # g(n)∈E
    n_NN = N.modus_ponens(fini_n, equivalence_arriere(
        appartenance_NN_instanciee(vn, "x", "y")))          # n∈ℕ
    eqn = N.modus_ponens(n_NN, instancie(eq_succ, vn))      # g(succ n)=S_c(g(n))
    u_in = _u_val_dans_E(vu, ve, E.valeur(vg, vn), h_incl, h_dom, hr)
    cl = _cut(u_in, appartient(E.valeur(vu, E.valeur(vg, vn)), ve),
              clamp_eval(E.valeur(vu, E.valeur(vg, vn)), ve, vx0, zname))
    eq_dec = composer_egalites(eqn, cl)                     # g(succ n)=u(g(n))
    pas_ccl = N.modus_ponens(u_in, equivalence_arriere(N.modus_ponens(
        eq_dec, N.s6(E.valeur(vg, successeur(vn)),
                     E.valeur(vu, E.valeur(vg, vn)), "wvi",
                     appartient(var("wvi"), ve)))))         # g(succ n)∈E
    pas = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)), pas_ccl))

    pr = _cut(predecesseur_fini_universel_preuve(), predecesseur_fini_universel(),
              principe_recurrence_preuve(P, n))
    concl = N.modus_ponens(conjonction_intro(base, pas), pr)  # ∀n(Fini n ⇒ P(n))
    # convertir la garde Fini → n∈ℕ
    h_n = N.assume(appartient(vn, NN))
    fini2 = N.modus_ponens(h_n, equivalence_avant(
        appartenance_NN_instanciee(vn, "x", "y")))
    pn = N.modus_ponens(fini2, instancie(concl, vn))
    res = N.generalisation(n, N.loi_deduction(appartient(vn, NN), pn))
    assert res.conclusion == pourtout(n, impl(appartient(vn, NN), P(vn))), \
        "valeurs_dans_E : forme"
    assert len(res.hypotheses) == 4, "valeurs_dans_E : hyps ≠ 4"
    return res


# @livre Ch.III §6.2 Ex.1 | E III.47 L.7-12 | PDF p.150  (« f(0) = a et
#   f(n+1) = g(f(n)) pour tout entier n » — l'équation de l'exemple, déclampée)
def equation_declampee(u, x0, e, g="gcap", zname="zcl", yname="ycl", n="nitv"):
    """🎯 K6c : {corps, x0∈E, u⊂E×E, dom u=E}
       ⊢ (∀n)( n∈ℕ ⇒ valeur(g, succ n) = valeur(u, valeur(g, n)) )   [4 hyps].

    L'ÉQUATION DU LIVRE : g(n+1) = u(g(n)) — le clamp déclampé sous g(n)∈E."""
    vu, vx0, ve, vg, S_c, h_x0, h_incl, h_dom, eq0, eq_succ = _contexte(
        u, x0, e, g, zname, yname)
    vn = var(n)
    NN = ensemble_NN()
    vals = valeurs_dans_E(u, x0, e, g, zname, yname, n)     # mêmes 4 hyps

    h_n = N.assume(appartient(vn, NN))
    eqn = N.modus_ponens(h_n, instancie(eq_succ, vn))       # g(succ n)=S_c(g(n))
    gn_in = N.modus_ponens(h_n, instancie(vals, vn))        # g(n)∈E
    u_in = _u_val_dans_E(vu, ve, E.valeur(vg, vn), h_incl, h_dom, gn_in)
    cl = _cut(u_in, appartient(E.valeur(vu, E.valeur(vg, vn)), ve),
              clamp_eval(E.valeur(vu, E.valeur(vg, vn)), ve, vx0, zname))
    res_n = composer_egalites(eqn, cl)                      # g(succ n)=u(g(n))
    res = N.generalisation(n, N.loi_deduction(appartient(vn, NN), res_n))
    assert res.conclusion == pourtout(n, impl(
        appartient(vn, NN),
        egal(E.valeur(vg, successeur(vn)), E.valeur(vu, E.valeur(vg, vn))))), \
        "equation_declampee : forme"
    assert len(res.hypotheses) == 4, "equation_declampee : hyps ≠ 4"
    return res


__all__ = ["valeurs_dans_E", "equation_declampee"]
