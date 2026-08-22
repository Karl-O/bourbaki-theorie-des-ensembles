# -*- coding: utf-8 -*-
"""§III.2.2 — R7' (étape 1) : LA FAMILLE GLOBALE ET SA COMPATIBILITÉ.

🎯 DÉFINITION (S8, patron Dfam_rec avec E au lieu de seg(x)) :

    Dglob_rec(G,E,V) := { p ∈ 𝔓(E×V) | (∃y)( y∈E ∧ est_essai_rec(p,y) ) }

La famille de TOUS les essais récursifs de E.  Sa réunion f := ⋃Dglob_rec est
LA solution globale du critère C60-vrai : dom f = E (par la couverture totale
R6'), l'équation partout, et l'unicité par C59 (étapes 2-5).

🎯 CIBLE (une hypothèse honnête) :

    compatibilite_Dglob :  { bo }  ⊢  famille_compatible( Dglob_rec(G,E,V) )

Copie de la version segmentée (compatibilite_Dfam_rec), SIMPLIFIÉE : le témoin
y∈E est directement le garant de a∈E (dom_essai(y)⊂E).

LÉGALITÉ S8 : sélecteur jamais auto-référent, contenant existant, théorie
DÉDIÉE — theorie_ensembles() reste à 22.  Le terme PORTE G (leçon seg_ext) ;
vh capturée (limite documentée, discipline Dfam_real).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    famille_compatible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_unicite_essai_rec import (
    dom_essai_inclus_E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    coincidence_essais_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_union_rec import (
    _valeur_depuis_couple,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def Dglob_rec(G, e, V="Vval"):
    """Le TERME de la famille GLOBALE { p∈𝔓(E×V) | (∃y∈E) est_essai_rec(p,y) }."""
    return E.app("rec_Dglob", _t(G), _t(e), _t(V))


def _corps_Dglob_rec(vh, G, e, p, V="Vval", y="yDg"):
    """Le corps en p :  p∈𝔓(E×V)  ∧  (∃y)( y∈E ∧ est_essai_rec(p,y) )."""
    vp, vy = _t(p), var(y)
    amb = appartient(vp, ambiant(e, V))
    sel = existe(y, et(appartient(vy, _t(e)),
                       est_essai_rec(vp, vh, _t(G), _t(e), vy)))
    return et(amb, sel)


def axiome_Dglob_rec(vh, G="Gsr", e="Esr", V="Vval", p="pDg", y="yDg"):
    """Schéma définitionnel S8 :
    (∀p)( p∈Dglob_rec(G,E,V) ⇔ ( p∈𝔓(E×V) ∧ (∃y∈E)( est_essai_rec(p,y) ) ) )."""
    vp = var(p)
    return pourtout(p, equiv(appartient(vp, Dglob_rec(G, e, V)),
                             _corps_Dglob_rec(vh, G, e, vp, V, y)))


def theorie_Dglob_rec(vh, G="Gsr", e="Esr", V="Vval", p="pDg", y="yDg"):
    """Théorie DÉDIÉE de la famille globale (S8, R7') — jamais dans les 22."""
    return N.Theorie("Dglob-rec-R7", [axiome_Dglob_rec(vh, G, e, V, p, y)])


def membre_Dglob_rec(vh, G="Gsr", e="Esr", p="pDg", V="Vval", y="yDg"):
    """⊢ ( p∈Dglob_rec ) ⇔ ( p∈𝔓(E×V) ∧ (∃y∈E)( est_essai_rec(p,y) ) )."""
    ax = N.axiome(theorie_Dglob_rec(vh, G, e, V, p="pDg", y=y),
                  axiome_Dglob_rec(vh, G, e, V, p="pDg", y=y))
    return instancie(ax, _t(p))


def compatibilite_Dglob(vh, G="Gsr", e="Esr", V="Vval"):
    """🎯 { bo } ⊢ famille_compatible( Dglob_rec(G,E,V) )       [1 hyp honnête].

    Témoins yDg/zDg (liants distincts) ; a∈E vient du témoin y∈E lui-même
    (dom_essai(y)⊂E) ; la coïncidence R5'a conclut."""
    vG, ve = _t(G), _t(e)
    D = Dglob_rec(vG, ve, V)
    vp, vq, va, vb, vc = var("pcf"), var("qcf"), var("acf"), var("bcf"), var("ccf")
    vy, vz = var("yDg"), var("zDg")

    ant = et(et(appartient(vp, D), appartient(vq, D)),
             et(appartient(E.couple(va, vb), vp), appartient(E.couple(va, vc), vq)))
    h_ant = N.assume(ant)
    p_D = conjonction_elim_gauche(conjonction_elim_gauche(h_ant))
    q_D = conjonction_elim_droite(conjonction_elim_gauche(h_ant))
    ab_p = conjonction_elim_gauche(conjonction_elim_droite(h_ant))
    ac_q = conjonction_elim_droite(conjonction_elim_droite(h_ant))

    sel_p = conjonction_elim_droite(N.modus_ponens(p_D, equivalence_avant(
        membre_Dglob_rec(vh, G, e, vp, V, y="yDg"))))
    sel_q = conjonction_elim_droite(N.modus_ponens(q_D, equivalence_avant(
        membre_Dglob_rec(vh, G, e, vq, V, y="zDg"))))

    corps_y = et(appartient(vy, ve), est_essai_rec(vp, vh, vG, ve, vy))
    corps_z = et(appartient(vz, ve), est_essai_rec(vq, vh, vG, ve, vz))
    h_wy = N.assume(corps_y)
    h_wz = N.assume(corps_z)
    y_E, essai_p = conjonction_elim_gauche(h_wy), conjonction_elim_droite(h_wy)
    z_E, essai_q = conjonction_elim_gauche(h_wz), conjonction_elim_droite(h_wz)
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(essai_p))
    dom_p = conjonction_elim_droite(conjonction_elim_gauche(essai_p))
    func_q = conjonction_elim_gauche(conjonction_elim_gauche(essai_q))
    dom_q = conjonction_elim_droite(conjonction_elim_gauche(essai_q))

    a_dom_p = _cut(ab_p, appartient(E.couple(va, vb), vp),
                   couple_dans_dom(vp, va, vb))
    a_dom_q = _cut(ac_q, appartient(E.couple(va, vc), vq),
                   couple_dans_dom(vq, va, vc))
    b_eq = _valeur_depuis_couple(vp, va, vb, ab_p, func_p)  # b = p(a)
    c_eq = _valeur_depuis_couple(vq, va, vc, ac_q, func_q)  # c = q(a)

    a_dey = N.modus_ponens(a_dom_p, equivalence_avant(N.modus_ponens(
        dom_p, N.s6(E.dom(vp), dom_essai(vG, ve, vy), "wfc",
                    appartient(va, var("wfc"))))))
    a_dez = N.modus_ponens(a_dom_q, equivalence_avant(N.modus_ponens(
        dom_q, N.s6(E.dom(vq), dom_essai(vG, ve, vz), "wfc",
                    appartient(va, var("wfc"))))))
    incl_E = _cut(y_E, appartient(vy, ve), dom_essai_inclus_E(G, e, "yDg"))
    a_E = N.modus_ponens(a_dey, instancie(incl_E, va))

    co = coincidence_essais_rec(vh, "pcf", "qcf", G, e, y="yDg", yp="zDg", a="acf")
    co = _cut(essai_p, est_essai_rec(vp, vh, vG, ve, vy), co)
    co = _cut(essai_q, est_essai_rec(vq, vh, vG, ve, vz), co)
    co = _cut(a_dey, appartient(va, dom_essai(vG, ve, vy)), co)
    co = _cut(a_dez, appartient(va, dom_essai(vG, ve, vz)), co)
    co = _cut(a_E, appartient(va, ve), co)                  # p(a)=q(a)

    b_eq_c = composer_egalites(composer_egalites(b_eq, co),
        N.modus_ponens(c_eq, symetrie(vc, E.valeur(vq, va))))

    r1 = N.modus_ponens(sel_q, existe_elimination(
        N.loi_deduction(corps_z, b_eq_c), "zDg"))
    r2 = N.modus_ponens(sel_p, existe_elimination(
        N.loi_deduction(corps_y, r1), "yDg"))
    imp = N.loi_deduction(ant, r2)
    res = N.generalisation("pcf", N.generalisation("qcf", N.generalisation(
        "acf", N.generalisation("bcf", N.generalisation("ccf", imp)))))

    assert res.conclusion == famille_compatible(D), "compatibilite_Dglob : forme"
    assert len(res.hypotheses) == 1, "compatibilite_Dglob : hyps ≠ 1 (bo)"
    return res


__all__ = ["Dglob_rec", "axiome_Dglob_rec", "theorie_Dglob_rec",
           "membre_Dglob_rec", "compatibilite_Dglob"]
