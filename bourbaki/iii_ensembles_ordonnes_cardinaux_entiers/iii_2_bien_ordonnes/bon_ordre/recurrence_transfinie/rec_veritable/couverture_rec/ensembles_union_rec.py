# -*- coding: utf-8 -*-
"""§III.2.2 — R5'c (U1) : LA FAMILLE DES ESSAIS RÉCURSIFS EST COMPATIBLE.

🎯 CIBLE (une hypothèse honnête — le bon ordre) :

    compatibilite_Dfam_rec :
        { bo }  ⊢  famille_compatible( Dfam_rec(G,E,x,V) )

Deux membres p, q de la famille avec (a,b)∈p et (a,c)∈q donnent b=c : les
témoins y, y' (p essai-en-y, q essai-en-y') s'extraient de l'axiome S8, les
valeurs b=p(a) et c=q(a) par C46 (valeur_caracterisation), et la COÏNCIDENCE
R5'a (descente bilatérale, sans wlog) conclut p(a)=q(a).  Le a∈E requis vient
de a∈dom_essai(y)⊂E (dom_essai_inclus_E sous y∈E, y∈E par l'axiome-segment).

Avec cette compatibilité, TOUTE la machinerie c60_coeur s'applique à ⋃Dfam_rec :
union_famille_fonctionnelle (fonctionnalité) et valeur_union_famille (transfert
de valeur) — le recollement R5' n'a plus qu'à régler domaine et équation.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    famille_compatible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_unicite_essai_rec import (
    dom_essai_inclus_E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    coincidence_essais_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec, membre_Dfam_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _valeur_depuis_couple(vg, va, vval, ab_dans_g, func_g):
    """De (a,b)∈g et func g, conclure b = valeur(g,a)  (C46 + coupures)."""
    vc = valeur_caracterisation(vg, va)
    vc_b = instancie(N.generalisation("y", vc), vval)       # ((a,b)∈g) ⇔ (b=g(a))
    ex_y = N.modus_ponens(ab_dans_g, N.s5(
        appartient(E.couple(va, var("y")), vg), vval, "y"))
    res = N.modus_ponens(ab_dans_g, equivalence_avant(vc_b))
    res = _cut(ex_y, existe("y", appartient(E.couple(va, var("y")), vg)), res)
    return _cut(func_g, E.est_fonctionnel(vg), res)         # b = g(a)


def _e_du_temoin(G, e, x, vy, y_seg):
    """De y∈seg(G,E,x), extraire y∈E (conjoint gauche-gauche de l'axiome-segment)."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    ax_seg = instancie(N.axiome(E.theorie_segment_extremite(),
                                E.axiome_segment_extremite()), vG)
    corps = N.modus_ponens(y_seg, equivalence_avant(
        instancie(instancie(instancie(ax_seg, ve), vx), vy)))
    return conjonction_elim_gauche(conjonction_elim_gauche(corps))   # y∈E


def compatibilite_Dfam_rec(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """🎯 R5'c-U1 : { bo } ⊢ famille_compatible( Dfam_rec(G,E,x,V) )  [1 hyp].

    Voir la docstring de module.  Témoins de l'axiome S8 aux liants yDr (pour p)
    et zDr (pour q) — distincts (leçon kpred2)."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    D = Dfam_rec(vG, ve, vx, V)
    vp, vq, va, vb, vc = var("pcf"), var("qcf"), var("acf"), var("bcf"), var("ccf")
    vy, vz = var("yDr"), var("zDr")

    ant = et(et(appartient(vp, D), appartient(vq, D)),
             et(appartient(E.couple(va, vb), vp), appartient(E.couple(va, vc), vq)))
    h_ant = N.assume(ant)
    p_D = conjonction_elim_gauche(conjonction_elim_gauche(h_ant))
    q_D = conjonction_elim_droite(conjonction_elim_gauche(h_ant))
    ab_p = conjonction_elim_gauche(conjonction_elim_droite(h_ant))
    ac_q = conjonction_elim_droite(conjonction_elim_droite(h_ant))

    # témoins S8 : p essai-en-yDr, q essai-en-zDr (liants distincts)
    sel_p = conjonction_elim_droite(N.modus_ponens(p_D, equivalence_avant(
        membre_Dfam_rec(vh, G, e, vx, vp, V, y="yDr"))))    # (∃yDr)(yDr∈seg ∧ essai)
    sel_q = conjonction_elim_droite(N.modus_ponens(q_D, equivalence_avant(
        membre_Dfam_rec(vh, G, e, vx, vq, V, y="zDr"))))    # (∃zDr)(…)

    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import est_essai_rec
    corps_y = et(appartient(vy, E.segment_extremite(vG, ve, vx)),
                 est_essai_rec(vp, vh, vG, ve, vy))
    corps_z = et(appartient(vz, E.segment_extremite(vG, ve, vx)),
                 est_essai_rec(vq, vh, vG, ve, vz))
    h_wy = N.assume(corps_y)
    h_wz = N.assume(corps_z)
    y_seg, essai_p = conjonction_elim_gauche(h_wy), conjonction_elim_droite(h_wy)
    z_seg, essai_q = conjonction_elim_gauche(h_wz), conjonction_elim_droite(h_wz)
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(essai_p))
    dom_p = conjonction_elim_droite(conjonction_elim_gauche(essai_p))
    func_q = conjonction_elim_gauche(conjonction_elim_gauche(essai_q))
    dom_q = conjonction_elim_droite(conjonction_elim_gauche(essai_q))

    # b = p(a), c = q(a)  (C46) ; a∈dom p/q par couple_dans_dom (coupé)
    a_dom_p = _cut(ab_p, appartient(E.couple(va, vb), vp),
                   couple_dans_dom(vp, va, vb))
    a_dom_q = _cut(ac_q, appartient(E.couple(va, vc), vq),
                   couple_dans_dom(vq, va, vc))
    b_eq = _valeur_depuis_couple(vp, va, vb, ab_p, func_p)  # b = p(a)
    c_eq = _valeur_depuis_couple(vq, va, vc, ac_q, func_q)  # c = q(a)

    # a∈dom_essai(yDr), a∈dom_essai(zDr)  (Leibniz depuis dom p/q)
    a_dey = N.modus_ponens(a_dom_p, equivalence_avant(N.modus_ponens(
        dom_p, N.s6(E.dom(vp), dom_essai(vG, ve, vy), "wfc",
                    appartient(va, var("wfc"))))))
    a_dez = N.modus_ponens(a_dom_q, equivalence_avant(N.modus_ponens(
        dom_q, N.s6(E.dom(vq), dom_essai(vG, ve, vz), "wfc",
                    appartient(va, var("wfc"))))))
    # a∈E  (dom_essai(yDr)⊂E sous yDr∈E, extrait de l'axiome-segment)
    y_E = _e_du_temoin(G, e, x, vy, y_seg)
    incl_E = _cut(y_E, appartient(vy, ve), dom_essai_inclus_E(G, e, "yDr"))
    a_E = N.modus_ponens(a_dey, instancie(incl_E, va))

    # coïncidence R5'a aux témoins, six coupures
    co = coincidence_essais_rec(vh, "pcf", "qcf", G, e, y="yDr", yp="zDr", a="acf")
    co = _cut(essai_p, est_essai_rec(vp, vh, vG, ve, vy), co)
    co = _cut(essai_q, est_essai_rec(vq, vh, vG, ve, vz), co)
    co = _cut(a_dey, appartient(va, dom_essai(vG, ve, vy)), co)
    co = _cut(a_dez, appartient(va, dom_essai(vG, ve, vz)), co)
    co = _cut(a_E, appartient(va, ve), co)                  # {bo, …} p(a)=q(a)

    # b = p(a) = q(a) = c
    b_eq_c = composer_egalites(composer_egalites(b_eq, co),
        N.modus_ponens(c_eq, symetrie(vc, E.valeur(vq, va))))

    # élimination des témoins (zDr puis yDr), décharge, ∀-clôture (ordre p,q,a,b,c)
    r1 = N.modus_ponens(sel_q, existe_elimination(
        N.loi_deduction(corps_z, b_eq_c), "zDr"))
    r2 = N.modus_ponens(sel_p, existe_elimination(
        N.loi_deduction(corps_y, r1), "yDr"))
    imp = N.loi_deduction(ant, r2)
    res = N.generalisation("pcf", N.generalisation("qcf", N.generalisation(
        "acf", N.generalisation("bcf", N.generalisation("ccf", imp)))))

    cible = famille_compatible(D)
    assert res.conclusion == cible, "compatibilite_Dfam_rec : ≠ famille_compatible"
    assert len(res.hypotheses) == 1, "compatibilite_Dfam_rec : hyps ≠ 1 (bo)"
    return res


__all__ = ["compatibilite_Dfam_rec"]
