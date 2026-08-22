# -*- coding: utf-8 -*-
"""§III.2.2 — R4'a : LA RESTRICTION D'UN ESSAI RÉCURSIF DESCEND.

🎯 CIBLES :

    dom_essai_monotone :
        { bo, y∈dom_essai(x) }  ⊢  dom_essai(y) ⊂ dom_essai(x)

    restriction_essai_rec :
        { bo, est_essai_rec(p, vh, G, E, x), y∈dom_essai(x) }
            ⊢  est_essai_rec( p | dom_essai(y),  vh, G, E, y )

C'est la brique de COHÉRENCE de la famille des essais (R5') : deux essais
récursifs en des points différents y ≤ y' se comparent en RESTREIGNANT le plus
grand au dom_essai du plus petit — la restriction reste un essai récursif
(l'équation passe par la composition des restrictions R4'b : (p|D)|seg z =
p|seg z dès que seg z ⊂ D), et R2'-unicité conclut la coïncidence.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    alpha_pour_tout,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur, _restriction_fonctionnelle_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_inclus_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_composition_restrictions import (
    composition_restrictions,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def dom_essai_monotone(G="Gsr", e="Esr", x="xsr", y="ysr", u="udm"):
    """{ bo, y∈dom_essai(x) } ⊢ dom_essai(y) ⊂ dom_essai(x)   [2 hyps honnêtes].

    u∈seg(y)∪{y} : le cas seg(y) passe par la brique (ii) (seg(y)⊂dom_essai(x)
    sous y∈dom_essai(x)), le cas u=y est l'hypothèse réécrite (Leibniz)."""
    vG, ve, vx, vy, vu = _t(G), _t(e), _t(x), _t(y), var(u)
    domx = dom_essai(vG, ve, vx)
    domy = dom_essai(vG, ve, vy)
    segy = E.segment_extremite(vG, ve, vy)
    singy = E.singleton(vy)

    h_yd = N.assume(appartient(vy, domx))                   # y∈dom_essai(x)
    segy_sub = N.modus_ponens(h_yd, seg_inclus_dom_essai(G, e, x, y))  # {bo}

    h_u = N.assume(appartient(vu, domy))
    disj = N.modus_ponens(h_u, equivalence_avant(_instance_reunion(segy, singy, vu)))
    # cas A : u∈seg(y) ⊂ dom_essai(x)
    h_us = N.assume(appartient(vu, segy))
    impA = N.loi_deduction(appartient(vu, segy),
                           N.modus_ponens(h_us, instancie(segy_sub, vu)))
    # cas B : u=y ∈ dom_essai(x)
    h_ub = N.assume(appartient(vu, singy))
    u_eq_y = N.modus_ponens(h_ub, equivalence_avant(singleton_membre(vu, vy)))
    u_domx = N.modus_ponens(h_yd, equivalence_arriere(N.modus_ponens(
        u_eq_y, N.s6(vu, vy, "wdm", appartient(var("wdm"), domx)))))
    impB = N.loi_deduction(appartient(vu, singy), u_domx)

    gen = N.generalisation(u, N.loi_deduction(appartient(vu, domy),
                                              cas(disj, impA, impB)))
    return N.modus_ponens(gen, equivalence_avant(alpha_pour_tout(
        u, "z", impl(appartient(vu, domy), appartient(vu, domx)))))


def restriction_essai_rec(vh, p="pes", G="Gsr", e="Esr", x="xsr", y="ysr"):
    """🎯 R4'a : {bo, est_essai_rec(p,x), y∈dom_essai(x)}
       ⊢ est_essai_rec(p|dom_essai(y), vh, G, E, y)          [3 hyps honnêtes]."""
    vp, vG, ve, vx, vy = _t(p), _t(G), _t(e), _t(x), _t(y)
    domx = dom_essai(vG, ve, vx)
    domy = dom_essai(vG, ve, vy)
    pD = E.restriction(vp, domy)                            # p|dom_essai(y)

    h_ep = N.assume(est_essai_rec(vp, vh, vG, ve, vx))      # essai p    [HONNÊTE]
    h_yd = N.assume(appartient(vy, domx))                   # y∈dom_essai(x)
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(h_ep))
    dom_p = conjonction_elim_droite(conjonction_elim_gauche(h_ep))
    eq_p = conjonction_elim_droite(h_ep)

    # dom_essai(y) ⊂ dom p  (monotonie + Leibniz dom_essai(x) = dom p)
    mono = dom_essai_monotone(G, e, x, y)                   # {bo, y∈domx}
    sym_dp = N.modus_ponens(dom_p, symetrie(E.dom(vp), domx))
    sub_domp = N.modus_ponens(mono, equivalence_avant(N.modus_ponens(
        sym_dp, N.s6(domx, E.dom(vp), "wdm", inclus(domy, var("wdm"))))))

    # ── conjoints 1 et 2 : fonctionnalité et domaine ─────────────────────────
    c1 = N.modus_ponens(func_p, _restriction_fonctionnelle_terme(vp, domy))
    c2 = N.modus_ponens(sub_domp, restriction_dom_sous_inclusion(vp, domy))

    # ── conjoint 3 : l'équation sur dom(p|D) = dom_essai(y) ──────────────────
    vz = var("zesr")
    segz = E.segment_extremite(vG, ve, vz)
    h_z = N.assume(appartient(vz, E.dom(pD)))
    z_D = N.modus_ponens(h_z, equivalence_avant(N.modus_ponens(
        c2, N.s6(E.dom(pD), domy, "wdm", appartient(vz, var("wdm"))))))  # z∈domy
    z_domp = N.modus_ponens(z_D, instancie(sub_domp, vz))               # z∈dom p
    # (p|D)(z) = p(z)   (brique (iii), coupures)
    rv = restriction_valeur(vp, domy, vz)
    rv = _cut(z_D, appartient(vz, domy), rv)
    rv = _cut(z_domp, appartient(vz, E.dom(vp)), rv)
    rv = _cut(func_p, E.est_fonctionnel(vp), rv)
    # p(z) = vh(p|seg z)   (l'équation de p)
    eq_z = N.modus_ponens(z_domp, instancie(eq_p, vz))
    # vh(p|seg z) = vh((p|D)|seg z)   (R4'b sous seg z ⊂ domy, congruence C44)
    segz_sub = N.modus_ponens(z_D, seg_inclus_dom_essai(G, e, y, "zesr"))
    compo = _cut(segz_sub, inclus(segz, domy),
                 composition_restrictions(vp, domy, segz))   # (p|D)|segz = p|segz
    cong = N.modus_ponens(compo, congruence_terme(
        E.restriction(pD, segz), E.restriction(vp, segz), vh(var("wrec")), "wrec"))
    cong_sym = N.modus_ponens(cong, symetrie(
        vh(E.restriction(pD, segz)), vh(E.restriction(vp, segz))))
    chaine = composer_egalites(composer_egalites(rv, eq_z), cong_sym)
    eq_conj = N.generalisation("zesr",
        N.loi_deduction(appartient(vz, E.dom(pD)), chaine))

    res = conjonction_intro(conjonction_intro(c1, c2), eq_conj)
    cible = est_essai_rec(pD, vh, vG, ve, vy)
    assert res.conclusion == cible, "restriction_essai_rec : ≠ est_essai_rec(p|D, y)"
    assert len(res.hypotheses) == 3, "restriction_essai_rec : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "restriction_essai_rec : VACUOUS"
    return res


__all__ = ["dom_essai_monotone", "restriction_essai_rec"]
