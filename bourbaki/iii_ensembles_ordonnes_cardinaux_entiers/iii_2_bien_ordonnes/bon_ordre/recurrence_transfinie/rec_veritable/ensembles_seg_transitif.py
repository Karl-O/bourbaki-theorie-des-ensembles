# -*- coding: utf-8 -*-
"""§III.2.2 — R2'a, brique (ii) : SEG-TRANSITIVITÉ (le segment d'un point du
domaine d'essai reste dans le domaine d'essai).

🎯 CIBLES (chacune UNE hypothèse honnête : le bon ordre) :

    seg_transitif_strict :
        { est_bien_ordonne(R,E) } ⊢ (z∈seg(G,E,x) ∧ u∈seg(G,E,z)) ⇒ u∈seg(G,E,x)

    seg_inclus_dom_essai :
        { est_bien_ordonne(R,E) } ⊢ z∈dom_essai(G,E,x) ⇒ seg(G,E,z) ⊂ dom_essai(G,E,x)

C'est la brique de DOMAINE du lemme d'unicité R2' (deux essais récursifs en x
coïncident) : l'équation de récursion en z lit p|seg(z), et pour comparer les
restrictions il faut seg(z) ⊂ dom(p) = dom_essai(x).  Bourbaki l'utilise
tacitement dans la démonstration de C60 (« l'ensemble des t∈E tels que t<z » est
contenu dans le segment fermé) — la transitivité et l'antisymétrie proviennent
du bon ordre.

STRATÉGIE (patron extrait de `couverture_segment_realise`, c60_clauses) :
  u∈seg(z) donne (u∈E ∧ (u,z)∈G ∧ u≠z) [axiome-segment CLOS] ;
  • z∈seg(x) : (z,x)∈G, donc (u,x)∈G (TRANSITIVITÉ) ; u≠x sinon (x,z)∈G et
    (z,x)∈G forcent x=z (ANTISYMÉTRIE), contredisant z≠x → u∈seg(x) ;
  • z=x (z∈{x}) : seg(z)=seg(x) par réécriture S6.
  Enfin seg(x) ⊂ seg(x)∪{x} = dom_essai(x)  (S2 + axiome-réunion).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  Tout dérivé, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, non, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
    cas, antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    alpha_pour_tout,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _composantes_ordre(h_bo):
    """Extrait (transitivité, antisymétrie) d'une hypothèse est_bien_ordonne.

    bo = et( est_relation_ordre_dans, plus-petit-élément )
    est_relation_ordre_dans = et( est_relation_ordre, réflexivité-dans-E )
    est_relation_ordre = et( et(transitif, antisymétrique), réflexivité-implicite )."""
    ord_dans = conjonction_elim_gauche(h_bo)
    rel_ordre = conjonction_elim_gauche(ord_dans)
    trans_antisym = conjonction_elim_gauche(rel_ordre)
    return (conjonction_elim_gauche(trans_antisym),
            conjonction_elim_droite(trans_antisym))


def _ax_seg(vG):
    """Instance en G de l'axiome CLOS du segment : (∀E)(∀x)(∀y)(y∈seg(G,E,x) ⇔ …)."""
    th = E.theorie_segment_extremite()
    return instancie(N.axiome(th, E.axiome_segment_extremite()), vG)


# @livre Ch.III §2.2 Demo.60 | E III.18 L.34-39 | PDF p.121  (démonstration de C60 :
#   les segments des points d'un segment restent dans le segment — transitivité tacite)
def seg_transitif_strict(G="Gsr", e="Esr", x="xsr", z="zsr", u="usr"):
    """{ est_bien_ordonne(R,E) } ⊢ (z∈seg(G,E,x) ∧ u∈seg(G,E,z)) ⇒ u∈seg(G,E,x).

    Transitivité STRICTE du segment d'extrémité (u<z et z<x donnent u<x) :
    (u,x)∈G par transitivité de l'ordre ; u≠x par antisymétrie (u=x forcerait
    x=z via (x,z)∈G ∧ (z,x)∈G, contredisant z≠x).  UNE hypothèse honnête."""
    vG, ve, vx, vz, vu = _t(G), _t(e), _t(x), _t(z), _t(u)
    R = _graphe_R(vG)
    segx = E.segment_extremite(vG, ve, vx)
    segz = E.segment_extremite(vG, ve, vz)

    h_bo = N.assume(E.est_bien_ordonne(R, ve))                  # bon ordre [HONNÊTE]
    trans, antisym = _composantes_ordre(h_bo)

    conj = et(appartient(vz, segx), appartient(vu, segz))
    h_conj = N.assume(conj)
    z_in_segx = conjonction_elim_gauche(h_conj)                 # z∈seg(x)
    u_in_segz = conjonction_elim_droite(h_conj)                 # u∈seg(z)

    ax_seg = _ax_seg(vG)
    # z∈seg(x) ⇔ ((z∈E ∧ (z,x)∈G) ∧ z≠x)
    z_body = N.modus_ponens(z_in_segx, equivalence_avant(
        instancie(instancie(instancie(ax_seg, ve), vx), vz)))
    z_le_x = conjonction_elim_droite(conjonction_elim_gauche(z_body))   # (z,x)∈G
    z_ne_x = conjonction_elim_droite(z_body)                            # z≠x
    # u∈seg(z) ⇔ ((u∈E ∧ (u,z)∈G) ∧ u≠z)
    u_body = N.modus_ponens(u_in_segz, equivalence_avant(
        instancie(instancie(instancie(ax_seg, ve), vz), vu)))
    u_in_E = conjonction_elim_gauche(conjonction_elim_gauche(u_body))   # u∈E
    u_le_z = conjonction_elim_droite(conjonction_elim_gauche(u_body))   # (u,z)∈G

    # transitivité : ((u,z)∈G ∧ (z,x)∈G) ⇒ (u,x)∈G
    trans_inst = instancie(instancie(instancie(trans, vu), vz), vx)
    u_le_x = N.modus_ponens(conjonction_intro(u_le_z, z_le_x), trans_inst)

    # u≠x par antisymétrie : sous u=x, (x,z)∈G [réécriture S6 de (u,z)∈G] et
    # (z,x)∈G donnent x=z puis z=x, contredisant z≠x.
    h_u_eq_x = N.assume(egal(vu, vx))
    x_le_z = N.modus_ponens(u_le_z, equivalence_avant(
        N.modus_ponens(h_u_eq_x, N.s6(vu, vx, "wux",
            appartient(E.couple(var("wux"), vz), vG)))))                # (x,z)∈G
    antisym_inst = instancie(instancie(antisym, vx), vz)
    x_eq_z = N.modus_ponens(conjonction_intro(x_le_z, z_le_x), antisym_inst)
    z_eq_x = N.modus_ponens(x_eq_z, symetrie(vx, vz))                   # z=x
    cible_neg = non(egal(vu, vx))
    # ¬(z=x) ⇒ (¬(z=x) ∨ ¬(u=x)) == (z=x) ⇒ ¬(u=x)  [∨ encode l'implication]
    inner = N.modus_ponens(z_eq_x, N.modus_ponens(z_ne_x,
        N.s2(non(egal(vz, vx)), cible_neg)))                            # ¬(u=x) [sous u=x]
    imp_neg = N.loi_deduction(egal(vu, vx), inner)                      # (u=x)⇒¬(u=x)
    _, notP = antecedent_consequent(imp_neg.conclusion)
    u_ne_x = N.modus_ponens(imp_neg, N.s1(notP))                        # ¬(u=x)

    # u∈seg(x) ⇐ ((u∈E ∧ (u,x)∈G) ∧ u≠x)
    u_in_segx = N.modus_ponens(
        conjonction_intro(conjonction_intro(u_in_E, u_le_x), u_ne_x),
        equivalence_arriere(instancie(instancie(instancie(ax_seg, ve), vx), vu)))
    return N.loi_deduction(conj, u_in_segx)


# @livre Ch.III §2.2 Demo.60 | E III.18 L.34-39 | PDF p.121  (démonstration de C60 :
#   le domaine d'un essai contient le segment de chacun de ses points)
def seg_inclus_dom_essai(G="Gsr", e="Esr", x="xsr", z="zsr", u="usr"):
    """{ est_bien_ordonne(R,E) } ⊢ z∈dom_essai(G,E,x) ⇒ seg(G,E,z) ⊂ dom_essai(G,E,x).

    dom_essai(x) = seg(x)∪{x} : z y appartient par z∈seg(x) ou z=x.
      • z∈seg(x) : u∈seg(z) ⇒ u∈seg(x)   [seg_transitif_strict] ;
      • z=x      : seg(z) = seg(x)        [réécriture S6].
    Dans les deux cas u∈seg(x) ⊂ dom_essai(x)  (S2 + axiome-réunion).
    Brique (ii) de R2'a : elle donne seg(z) ⊂ dom(p) pour tout essai récursif p
    en x et tout z de son domaine — la restriction p|seg(z) est alors pleine."""
    vG, ve, vx, vz, vu = _t(G), _t(e), _t(x), _t(z), _t(u)
    R = _graphe_R(vG)
    segx = E.segment_extremite(vG, ve, vx)
    segz = E.segment_extremite(vG, ve, vz)
    singx = E.singleton(vx)
    domx = dom_essai(vG, ve, vx)

    h_zd = N.assume(appartient(vz, domx))                       # z∈dom_essai(x)
    disj = N.modus_ponens(h_zd, equivalence_avant(
        _instance_reunion(segx, singx, vz)))                    # z∈seg(x) ∨ z∈{x}

    h_useg = N.assume(appartient(vu, segz))                     # u∈seg(z)

    def _dans_domx(u_in_segx):
        """u∈seg(x) ⊢ u∈seg(x)∪{x} = dom_essai(x)."""
        u_disj = N.modus_ponens(u_in_segx,
            N.s2(appartient(vu, segx), appartient(vu, singx)))
        return N.modus_ponens(u_disj, equivalence_arriere(
            _instance_reunion(segx, singx, vu)))

    # CAS A : z∈seg(x) — la transitivité stricte conclut.
    h_zsegx = N.assume(appartient(vz, segx))
    u_in_segx_A = N.modus_ponens(
        conjonction_intro(h_zsegx, h_useg),
        seg_transitif_strict(G, e, x, z, u))
    impA = N.loi_deduction(appartient(vz, segx), _dans_domx(u_in_segx_A))

    # CAS B : z∈{x} — z=x, seg(z) se réécrit seg(x).
    h_zsx = N.assume(appartient(vz, singx))
    z_eq_x = N.modus_ponens(h_zsx, equivalence_avant(singleton_membre(vz, vx)))
    u_in_segx_B = N.modus_ponens(h_useg, equivalence_avant(
        N.modus_ponens(z_eq_x, N.s6(vz, vx, "wsr",
            appartient(vu, E.segment_extremite(vG, ve, var("wsr")))))))
    impB = N.loi_deduction(appartient(vz, singx), _dans_domx(u_in_segx_B))

    u_in_domx = cas(disj, impA, impB)                           # u∈dom_essai(x)
    imp_u = N.loi_deduction(appartient(vu, segz), u_in_domx)
    gen = N.generalisation(u, imp_u)                            # (∀u)(u∈seg(z)⇒u∈dom(x))
    incl = N.modus_ponens(gen, equivalence_avant(alpha_pour_tout(
        u, "z", impl(appartient(vu, segz), appartient(vu, domx)))))  # seg(z) ⊂ dom(x)
    return N.loi_deduction(appartient(vz, domx), incl)


__all__ = ["seg_transitif_strict", "seg_inclus_dom_essai"]
