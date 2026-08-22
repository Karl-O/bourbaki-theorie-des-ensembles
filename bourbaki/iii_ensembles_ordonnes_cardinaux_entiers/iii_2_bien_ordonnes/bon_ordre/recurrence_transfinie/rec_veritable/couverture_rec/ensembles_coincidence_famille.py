# -*- coding: utf-8 -*-
"""§III.2.2 — R5'a : COÏNCIDENCE DES ESSAIS RÉCURSIFS (descente bilatérale).

🎯 CIBLES :

    point_dans_dom_essai :  ⊢  x ∈ dom_essai(G,E,x)                 [CLOS]

    coincidence_essais_rec :
        { bo,  est_essai_rec(p, vh, G, E, y),  est_essai_rec(q, vh, G, E, y'),
          a∈dom_essai(y),  a∈dom_essai(y'),  a∈E }
            ⊢  valeur(p, a) = valeur(q, a)

SANS wlog ni trichotomie : les DEUX essais descendent au point commun a
(restriction_essai_rec, R4'a) — p|dom_essai(a) et q|dom_essai(a) sont des
essais récursifs EN a, donc ÉGAUX (unicite_essai_rec, R2', appliqué aux
TERMES-restrictions ; leurs conjoints graphe sont CLOS par
restriction_est_graphe).  Les valeurs en a se transportent par
restriction_valeur (a ∈ dom_essai(a), point_dans_dom_essai).

C'est la clause de COHÉRENCE (P2) de la famille des essais (R5'b) : la
tabulation C60 l'avait gratuite (valeurs épinglées vh(z)) ; la vraie récursion
l'obtient par l'unicité.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_valeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    restriction_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_unicite_essai_rec import (
    unicite_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_restriction_essai import (
    restriction_essai_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def point_dans_dom_essai(G="Gsr", e="Esr", x="xsr"):
    """⊢ x ∈ dom_essai(G,E,x)                                    [CLOS, 0 hyp].

    x∈{x} (réflexivité + singleton), puis x∈seg∨x∈{x} (S2+S3 commute) et
    l'axiome-réunion referme."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    segx = E.segment_extremite(vG, ve, vx)
    singx = E.singleton(vx)
    in_sing = N.modus_ponens(N.reflexivite(vx),
                             equivalence_arriere(singleton_membre(vx, vx)))
    disj = N.modus_ponens(
        N.modus_ponens(in_sing, N.s2(appartient(vx, singx), appartient(vx, segx))),
        N.s3(appartient(vx, singx), appartient(vx, segx)))
    res = N.modus_ponens(disj, equivalence_arriere(_instance_reunion(segx, singx, vx)))
    assert res.est_clos, "point_dans_dom_essai : non clos"
    return res


def coincidence_essais_rec(vh, p="pre", q="qre", G="Gsr", e="Esr",
                           y="ysr", yp="ypr", a="acf"):
    """🎯 R5'a : {bo, essai p en y, essai q en y', a∈dom_essai(y),
       a∈dom_essai(y'), a∈E} ⊢ valeur(p,a) = valeur(q,a)     [6 hyps honnêtes]."""
    vp, vq, vG, ve, vy, vyp, va = _t(p), _t(q), _t(G), _t(e), _t(y), _t(yp), _t(a)
    domA = dom_essai(vG, ve, va)
    P = E.restriction(vp, domA)
    Q = E.restriction(vq, domA)

    h_ep = N.assume(est_essai_rec(vp, vh, vG, ve, vy))      # essai p en y
    h_eq = N.assume(est_essai_rec(vq, vh, vG, ve, vyp))     # essai q en y'
    h_ay = N.assume(appartient(va, dom_essai(vG, ve, vy)))
    h_ayp = N.assume(appartient(va, dom_essai(vG, ve, vyp)))

    # descentes : P et Q sont des essais récursifs EN a  (R4'a)
    pa = restriction_essai_rec(vh, p, G, e, y, a)           # {bo, essai p, a∈de(y)}
    qa = restriction_essai_rec(vh, q, G, e, yp, a)

    # unicité R2' appliquée aux TERMES P, Q au point a
    uni = unicite_essai_rec(vh, P, Q, G, e, a)
    uni = _cut(pa, est_essai_rec(P, vh, vG, ve, va), uni)
    uni = _cut(qa, est_essai_rec(Q, vh, vG, ve, va), uni)
    uni = _cut(restriction_est_graphe(vp, domA), E.est_un_graphe(P), uni)
    uni = _cut(restriction_est_graphe(vq, domA), E.est_un_graphe(Q), uni)   # P=Q

    # valeurs : p(a) = P(a) = Q(a) = q(a)
    a_in_domA = point_dans_dom_essai(G, e, a)               # a∈dom_essai(a) CLOS
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(h_ep))
    dom_p = conjonction_elim_droite(conjonction_elim_gauche(h_ep))
    a_dom_p = N.modus_ponens(h_ay, equivalence_arriere(N.modus_ponens(
        dom_p, N.s6(E.dom(vp), dom_essai(vG, ve, vy), "wcf",
                    appartient(va, var("wcf"))))))
    rv_p = restriction_valeur(vp, domA, va)
    rv_p = _cut(a_in_domA, appartient(va, domA), rv_p)
    rv_p = _cut(a_dom_p, appartient(va, E.dom(vp)), rv_p)
    rv_p = _cut(func_p, E.est_fonctionnel(vp), rv_p)        # P(a)=p(a)
    func_q = conjonction_elim_gauche(conjonction_elim_gauche(h_eq))
    dom_q = conjonction_elim_droite(conjonction_elim_gauche(h_eq))
    a_dom_q = N.modus_ponens(h_ayp, equivalence_arriere(N.modus_ponens(
        dom_q, N.s6(E.dom(vq), dom_essai(vG, ve, vyp), "wcf",
                    appartient(va, var("wcf"))))))
    rv_q = restriction_valeur(vq, domA, va)
    rv_q = _cut(a_in_domA, appartient(va, domA), rv_q)
    rv_q = _cut(a_dom_q, appartient(va, E.dom(vq)), rv_q)
    rv_q = _cut(func_q, E.est_fonctionnel(vq), rv_q)        # Q(a)=q(a)

    p_eq_P = N.modus_ponens(rv_p, symetrie(E.valeur(P, va), E.valeur(vp, va)))
    PQ_val = N.modus_ponens(uni, congruence_terme(
        P, Q, E.valeur(var("wcf"), va), "wcf"))             # P(a)=Q(a)
    res = composer_egalites(composer_egalites(p_eq_P, PQ_val), rv_q)

    assert res.conclusion == egal(E.valeur(vp, va), E.valeur(vq, va)), \
        "coincidence_essais_rec : forme"
    assert len(res.hypotheses) == 6, "coincidence_essais_rec : hyps ≠ 6"
    return res


__all__ = ["point_dans_dom_essai", "coincidence_essais_rec"]
