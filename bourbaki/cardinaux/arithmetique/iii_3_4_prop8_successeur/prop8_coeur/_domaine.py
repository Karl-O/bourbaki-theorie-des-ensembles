"""CŒUR Prop. 8 — conjoint DOMAINE : dom g = A×{0}   (g = h|(A×{0})).

dom g = A×{0} sous la seule hypothèse A×{0} ⊂ dom h (vraie au CAS 1 car
dom h = A⊔{∅} ⊃ A×{0}).  Caractérisation membre :

    u ∈ dom g  ⇔  (∃v)((u,v)∈g)              [AXIOME_DOM]
              ⇔  (∃v)(u∈A×{0} et (u,v)∈h)    [membre_g_ssi_t]
              ⇔  u ∈ A×{0}                    [⇒ projection ; ⇐ témoin via A×{0}⊂dom h]

puis égalité par extension.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient, existe, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.prop8_coeur._g import (
    A0_terme, G_RESTR, membre_g_ssi_t, _H)


def g_domaine(a="A", h=_H):
    """{A×{0} ⊂ dom h} ⊢ dom g = A×{0}.   (g = h|(A×{0}) ; conjoint domaine.)

    Le domaine de la restriction à A×{0} est A×{0} tout entier, car A×{0} est
    inclus dans le domaine de h."""
    vh = var(h)
    A0 = A0_terme(a)
    g = G_RESTR(a, h)
    vu, vv = var("u"), var("v")

    # u∈dom g ⇔ (∃v)((u,v)∈g)   (AXIOME_DOM, liant interne « y » → renommé « v »)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car0 = instancie(instancie(ax_dom, g), vu)        # u∈dom g ⇔ (∃y)((u,y)∈g)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    ren = alpha_existe("y", "v", appartient(E.couple(vu, var("y")), g))
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_transitivite
    dom_car = equivalence_transitivite(dom_car0, ren)     # u∈dom g ⇔ (∃v)((u,v)∈g)

    # ── ⇒ : (∃v)((u,v)∈g) ⇒ u∈A×{0} ───────────────────────────────────────────
    body = appartient(E.couple(vu, vv), g)
    hb = N.assume(body)                                   # (u,v)∈g
    u_inA0 = conjonction_elim_gauche(N.modus_ponens(hb,
        equivalence_avant(membre_g_ssi_t(a, vu, vv, h))))  # u∈A×{0}
    fwd_inner = existe_elimination(N.loi_deduction(body, u_inA0), "v")  # (∃v)(u,v)∈g ⇒ u∈A×{0}
    fwd = syllogisme(equivalence_avant(dom_car), fwd_inner)   # u∈dom g ⇒ u∈A×{0}

    # ── ⇐ : u∈A×{0} ⇒ (∃v)((u,v)∈g)  (témoin v:=h(u), via A×{0}⊂dom h) ──────────
    hsub = N.assume(inclus(A0, E.dom(vh)))                # A×{0} ⊂ dom h
    hu = N.assume(appartient(vu, A0))                     # u∈A×{0}
    u_in_domh = N.modus_ponens(hu, instancie(hsub, vu))  # u∈dom h
    ax_domh = instancie(instancie(ax_dom, vh), vu)        # u∈dom h ⇔ (∃y)((u,y)∈h)
    exy_h = N.modus_ponens(u_in_domh, equivalence_avant(ax_domh))   # (∃y)((u,y)∈h)
    hu_in_h = N.modus_ponens(exy_h, N.existe_temoin(
        appartient(E.couple(vu, var("y")), vh), "y"))     # (u,h(u))∈h
    hp = E.valeur(vh, vu)                                  # h(u)
    # (u,h(u))∈g  via membre_g_ssi_t ⇐
    hu_in_g = N.modus_ponens(conjonction_intro(hu, hu_in_h),
                             equivalence_arriere(membre_g_ssi_t(a, vu, hp, h)))  # (u,h(u))∈g
    ex_v = N.modus_ponens(hu_in_g, N.s5(appartient(E.couple(vu, vv), g), hp, "v"))  # (∃v)((u,v)∈g)
    bwd_inner = N.loi_deduction(appartient(vu, A0), ex_v)    # u∈A×{0} ⇒ (∃v)(u,v)∈g
    bwd = syllogisme(bwd_inner, equivalence_arriere(dom_car))   # u∈A×{0} ⇒ u∈dom g

    equiv_u = conjonction_intro(fwd, bwd)                 # u∈dom g ⇔ u∈A×{0}
    char_dom = N.generalisation("u", equiv_u)             # (∀u)(u∈dom g ⇔ u∈A×{0})
    self_A0 = N.generalisation("u", conjonction_intro(
        a_implique_a(appartient(vu, A0)), a_implique_a(appartient(vu, A0))))   # (∀u)(u∈A×{0} ⇔ u∈A×{0})
    return egalite_par_extension(char_dom, self_A0, E.dom(g), A0, "z")


__all__ = ["g_domaine"]
