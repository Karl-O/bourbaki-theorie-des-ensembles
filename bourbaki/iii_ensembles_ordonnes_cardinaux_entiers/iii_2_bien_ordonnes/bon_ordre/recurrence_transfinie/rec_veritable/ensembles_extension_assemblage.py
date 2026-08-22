# -*- coding: utf-8 -*-
"""§III.2.2 — R3' : L'EXTENSION D'UN PAS DE L'ESSAI RÉCURSIF (l'assemblage).

🎯 CIBLE (cinq hypothèses honnêtes) :

    { est_bien_ordonne(R,E),  est_fonctionnel(p),  dom p = seg(G,E,x),
      est_un_graphe(p),  (∀z)(z∈dom p ⇒ p(z) = vh(p|seg z)) }
        ⊢  est_essai_rec( p ∪ {(x, vh(p))},  vh, G, E, x )

Un « essai-sur-seg » p (fonction sur le segment OUVERT de x vérifiant
l'équation-restriction) se PROLONGE d'un pas en un essai récursif en x :
la valeur au nouveau point est vh(p) — la règle appliquée à p ENTIER, qui est
bien p'|seg(x) (la restriction efface le nouveau point, et p|seg(x)=p|dom p=p).
C'est le prolongement d'un pas de Bourbaki (E III.19) pour la VRAIE récursion.

LES TROIS CONJOINTS de est_essai_rec(p') :
  1. func p'            — extension_un_pas_fonctionnelle (C60, réutilisé) ;
  2. dom p' = seg∪{x}   — dom_reunion_graphes + dom_singleton_couple + Leibniz ;
  3. l'équation sur dom p', par cas :
     • z∈seg(x) : p'(z) = p(z) [valeur_reunion_gauche] = vh(p|seg z) [éq de p]
       = vh(p'|seg z) [brique 1 : x∉seg z, sinon seg_transitif_strict donnerait
       x∈seg x contre x_hors_seg ; puis congruence C44] ;
     • z=x : p'(x) = vh(p) [valeur_reunion_point] et p'|seg x = p|seg x = p
       [brique 1 + x_hors_seg, restriction_pleine + Leibniz] — congruence,
       puis réécriture z→x.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, non, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai, extension_un_pas_fonctionnelle, dom_singleton_couple,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    dom_reunion_graphes,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    valeur_reunion_gauche, valeur_reunion_point,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec, restriction_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_transitif_strict,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_essai import (
    restriction_reunion_singleton_hors, x_hors_seg, restriction_pleine,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def equation_sur_seg(p, vh, G, e, z="zesr"):
    """L'équation-restriction d'un essai-sur-seg : (∀z)(z∈dom p ⇒ p(z)=vh(p|seg z))."""
    vp, vz = _t(p), var(z)
    return pourtout(z, impl(appartient(vz, E.dom(vp)),
        egal(E.valeur(vp, vz), vh(restriction_seg(vp, _t(G), _t(e), vz)))))


# @livre Ch.III §2.2 Demo.60 | E III.19 L.1-5 | PDF p.122  (fin de la démonstration
#   de C60 : le prolongement d'un pas — ici pour la VRAIE équation-restriction)
def extension_essai_rec(vh, p="pes", G="Gsr", e="Esr", x="xsr"):
    """🎯 R3' : {bo, func p, dom p=seg(x), graphe p, éq-seg}
       ⊢ est_essai_rec(p ∪ {(x, vh(p))}, vh, G, E, x)       [5 hyps honnêtes]."""
    vp, vG, ve, vx = _t(p), _t(G), _t(e), _t(x)
    segx = E.segment_extremite(vG, ve, vx)
    v = vh(vp)                                              # la valeur au point x
    S = E.singleton(E.couple(vx, v))
    pp = E.reunion(vp, S)                                   # p'
    domx = dom_essai(vG, ve, vx)                            # seg(x) ∪ {x}

    h_fp = N.assume(E.est_fonctionnel(vp))                  # func p     [HONNÊTE]
    h_dp = N.assume(egal(E.dom(vp), segx))                  # dom p=seg  [HONNÊTE]
    h_gp = N.assume(E.est_un_graphe(vp))                    # graphe p   [HONNÊTE]
    h_eq = N.assume(equation_sur_seg(vp, vh, vG, ve))       # éq-seg     [HONNÊTE]

    # ── conjoint 1 : func p' ─────────────────────────────────────────────────
    c1 = extension_un_pas_fonctionnelle(p, G, e, x, v)      # {func p, dom p=seg}

    # ── conjoint 2 : dom p' = seg ∪ {x}  (Leibniz ×2 sur dom p∪dom S) ────────
    d1 = dom_reunion_graphes(vp, S)                         # dom(p∪S)=dom p∪dom S
    d1b = N.modus_ponens(d1, equivalence_avant(N.modus_ponens(h_dp,
        N.s6(E.dom(vp), segx, "wda",
             egal(E.dom(pp), E.reunion(var("wda"), E.dom(S)))))))
    c2 = N.modus_ponens(d1b, equivalence_avant(N.modus_ponens(
        dom_singleton_couple(vx, v),
        N.s6(E.dom(S), E.singleton(vx), "wda",
             egal(E.dom(pp), E.reunion(segx, var("wda")))))))   # dom p' = domx

    # ── conjoint 3 : l'équation sur dom p' ───────────────────────────────────
    vz = var("zesr")
    segz = E.segment_extremite(vG, ve, vz)
    h_z = N.assume(appartient(vz, E.dom(pp)))
    disj = N.modus_ponens(
        N.modus_ponens(h_z, equivalence_avant(N.modus_ponens(c2,
            N.s6(E.dom(pp), domx, "wda", appartient(vz, var("wda")))))),
        equivalence_avant(_instance_reunion(segx, E.singleton(vx), vz)))

    # CAS A : z∈seg(x)
    h_zs = N.assume(appartient(vz, segx))
    z_domp = N.modus_ponens(h_zs, equivalence_arriere(N.modus_ponens(h_dp,
        N.s6(E.dom(vp), segx, "wda", appartient(vz, var("wda"))))))    # z∈dom p
    vrg = _cut(z_domp, appartient(vz, E.dom(vp)),
               _cut(c1, E.est_fonctionnel(pp), valeur_reunion_gauche(vp, S, vz)))
    eq_z = N.modus_ponens(z_domp, instancie(h_eq, vz))      # p(z)=vh(p|seg z)
    # ¬(x∈seg z) : sinon la transitivité stricte donnerait x∈seg x (absurde)
    h_xin = N.assume(appartient(vx, segz))
    x_in_segx = N.modus_ponens(conjonction_intro(h_zs, h_xin),
                               seg_transitif_strict(G, e, x, "zesr", x))  # {bo}
    cible_neg = non(appartient(vx, segz))
    inner = N.modus_ponens(x_in_segx, N.modus_ponens(x_hors_seg(G, e, x),
        N.s2(non(appartient(vx, segx)), cible_neg)))
    x_notin = N.modus_ponens(N.loi_deduction(appartient(vx, segz), inner),
                             N.s1(cible_neg))               # ¬(x∈seg z)
    b1 = _cut(x_notin, cible_neg,
              restriction_reunion_singleton_hors(p, x, v, segz))  # p'|segz=p|segz
    cong = N.modus_ponens(b1, congruence_terme(
        E.restriction(pp, segz), E.restriction(vp, segz), vh(var("wrec")), "wrec"))
    cong_sym = N.modus_ponens(cong, symetrie(
        vh(E.restriction(pp, segz)), vh(E.restriction(vp, segz))))
    chainA = composer_egalites(composer_egalites(vrg, eq_z), cong_sym)
    impA = N.loi_deduction(appartient(vz, segx), chainA)    # p'(z)=vh(p'|seg z)

    # CAS B : z∈{x}
    h_zx = N.assume(appartient(vz, E.singleton(vx)))
    z_eq_x = N.modus_ponens(h_zx, equivalence_avant(singleton_membre(vz, vx)))
    vrp = _cut(c1, E.est_fonctionnel(pp), valeur_reunion_point(vp, vx, v))
    b1x = _cut(x_hors_seg(G, e, x), non(appartient(vx, segx)),
               restriction_reunion_singleton_hors(p, x, v, segx))  # p'|segx=p|segx
    p_segx_p = N.modus_ponens(restriction_pleine(p), equivalence_avant(
        N.modus_ponens(h_dp, N.s6(E.dom(vp), segx, "wda",
                               egal(E.restriction(vp, var("wda")), vp)))))  # p|segx=p
    congB = N.modus_ponens(composer_egalites(b1x, p_segx_p), congruence_terme(
        E.restriction(pp, segx), vp, vh(var("wrec")), "wrec"))  # vh(p'|segx)=vh(p)
    chainB_x = composer_egalites(vrp, N.modus_ponens(congB,
        symetrie(vh(E.restriction(pp, segx)), v)))          # p'(x)=vh(p'|seg x)
    chainB = N.modus_ponens(chainB_x, equivalence_arriere(N.modus_ponens(z_eq_x,
        N.s6(vz, vx, "wzb", egal(E.valeur(pp, var("wzb")),
            vh(E.restriction(pp, E.segment_extremite(vG, ve, var("wzb")))))))))
    impB = N.loi_deduction(appartient(vz, E.singleton(vx)), chainB)

    eq_conj = N.generalisation("zesr",
        N.loi_deduction(appartient(vz, E.dom(pp)), cas(disj, impA, impB)))

    res = conjonction_intro(conjonction_intro(c1, c2), eq_conj)
    cible = est_essai_rec(pp, vh, vG, ve, vx)
    assert res.conclusion == cible, "extension_essai_rec : ≠ est_essai_rec(p')"
    assert len(res.hypotheses) == 5, "extension_essai_rec : hyps ≠ 5"
    assert res.conclusion not in res.hypotheses, "extension_essai_rec : VACUOUS"
    return res


__all__ = ["equation_sur_seg", "extension_essai_rec"]
