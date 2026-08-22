# -*- coding: utf-8 -*-
"""§III.2.2 — R2'a, brique (iv) : ÉGALITÉ DES RESTRICTIONS AU SEGMENT.

🎯 CIBLE (sept hypothèses honnêtes) :

    { est_bien_ordonne(R,E),  est_fonctionnel(p),  est_fonctionnel(q),
      dom p = dom_essai(x),  dom q = dom_essai(x),  z ∈ dom_essai(x),
      (∀u)(u∈seg(z) ⇒ p(u)=q(u)) }
        ⊢  p|seg(z) = q|seg(z)

C'est la brique CENTRALE du lemme d'unicité R2' : quand deux essais récursifs
en x prennent les mêmes valeurs sous z (l'hypothèse de récurrence transfinie),
leurs restrictions au segment ouvert en z sont LE MÊME graphe — la règle vh,
appliquée à ce graphe commun, donnera alors p(z) = vh(p|seg z) = vh(q|seg z)
= q(z) (R2'b, congruence).

ASSEMBLAGE (extensionnalité fonctionnelle graphe_egal_par_valeurs, 6 prémisses) :
  • fonctionnels : _restriction_fonctionnelle_terme sur p et q ;
  • graphes      : restriction_est_graphe (CLOS) ;
  • domaines     : seg(z) ⊂ dom_essai(x) [brique (ii)] réécrit en seg(z) ⊂ dom p,
                   puis restriction_dom_sous_inclusion [brique (i)] :
                   dom(p|seg z) = seg(z) = dom(q|seg z) ;
  • valeurs      : (p|seg z)(u) = p(u) [brique (iii)] = q(u) [HR] = (q|seg z)(u).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  Tout dérivé, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_inclus_dom_essai,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def hypothese_recurrence(p, q, G, e, z, u="ure"):
    """La forme de l'HR transfinie : (∀u)(u∈seg(G,E,z) ⇒ valeur(p,u)=valeur(q,u))."""
    vu = var(u)
    segz = E.segment_extremite(_t(G), _t(e), _t(z))
    return pourtout(u, impl(appartient(vu, segz),
                            egal(E.valeur(_t(p), vu), E.valeur(_t(q), vu))))


def _seg_sous_dom(sub_domx, h_dom, graphe, segz, domx):
    """De seg(z) ⊂ dom_essai(x) et dom g = dom_essai(x), déduire seg(z) ⊂ dom g."""
    dom_g = E.dom(graphe)
    # dom_essai(x) = dom g  (symétrie de l'hypothèse), puis Leibniz sur le trou.
    sym = N.modus_ponens(h_dom, symetrie(dom_g, domx))
    return N.modus_ponens(sub_domx, equivalence_avant(
        N.modus_ponens(sym, N.s6(domx, dom_g, "wre",
                                 inclus(segz, var("wre"))))))


def restrictions_egales(p="pre", q="qre", G="Gsr", e="Esr", x="xsr", z="zsr",
                        u="ure"):
    """{bo, func p, func q, dom p=dom_essai(x), dom q=dom_essai(x), z∈dom_essai(x),
       (∀u)(u∈seg z ⇒ p(u)=q(u))}  ⊢  p|seg(z) = q|seg(z)      [7 hyps honnêtes].

    Brique (iv) de R2'a — voir la docstring de module pour l'assemblage."""
    vp, vq, vG, ve, vx, vz = _t(p), _t(q), _t(G), _t(e), _t(x), _t(z)
    segz = E.segment_extremite(vG, ve, vz)
    domx = dom_essai(vG, ve, vx)
    psz = E.restriction(vp, segz)
    qsz = E.restriction(vq, segz)

    h_fp = N.assume(E.est_fonctionnel(vp))                  # func p      [HONNÊTE]
    h_fq = N.assume(E.est_fonctionnel(vq))                  # func q      [HONNÊTE]
    h_dp = N.assume(egal(E.dom(vp), domx))                  # dom p = dom_essai(x)
    h_dq = N.assume(egal(E.dom(vq), domx))                  # dom q = dom_essai(x)
    h_zd = N.assume(appartient(vz, domx))                   # z∈dom_essai(x)
    hr = N.assume(hypothese_recurrence(vp, vq, vG, ve, vz, u))   # l'HR

    # ── seg(z) ⊂ dom p  et  seg(z) ⊂ dom q  (brique (ii) + réécriture S6) ────
    sub_domx = N.modus_ponens(h_zd, seg_inclus_dom_essai(G, e, x, z))  # {bo} segz⊂domx
    sub_domp = _seg_sous_dom(sub_domx, h_dp, vp, segz, domx)   # segz ⊂ dom p
    sub_domq = _seg_sous_dom(sub_domx, h_dq, vq, segz, domx)   # segz ⊂ dom q

    # ── domaines : dom(p|seg z) = seg(z) = dom(q|seg z)  (brique (i)) ────────
    dpe = N.modus_ponens(sub_domp, restriction_dom_sous_inclusion(vp, segz))
    dqe = N.modus_ponens(sub_domq, restriction_dom_sous_inclusion(vq, segz))
    dom_eq = composer_egalites(dpe, N.modus_ponens(dqe, symetrie(E.dom(qsz), segz)))

    # ── fonctionnels et graphes ──────────────────────────────────────────────
    f_p = N.modus_ponens(h_fp, _restriction_fonctionnelle_terme(vp, segz))
    f_q = N.modus_ponens(h_fq, _restriction_fonctionnelle_terme(vq, segz))
    g_p = restriction_est_graphe(vp, segz)                  # CLOS
    g_q = restriction_est_graphe(vq, segz)                  # CLOS

    # ── valeurs : (∀x)(x∈dom(p|seg z) ⇒ (p|seg z)(x)=(q|seg z)(x)) ──────────
    # lieur « x » imposé par egalite_valeurs (extensionnalité) ; sans capture ici.
    vX0 = var("x")
    h_u = N.assume(appartient(vX0, E.dom(psz)))             # x∈dom(p|seg z)
    u_segz = N.modus_ponens(h_u, equivalence_avant(
        N.modus_ponens(dpe, N.s6(E.dom(psz), segz, "wre",
                                 appartient(vX0, var("wre"))))))       # x∈seg z
    u_domp = N.modus_ponens(u_segz, instancie(sub_domp, vX0))          # x∈dom p
    u_domq = N.modus_ponens(u_segz, instancie(sub_domq, vX0))          # x∈dom q
    # brique (iii) : (p|seg z)(x)=p(x), coupures des appartenances prouvées
    rv_p = restriction_valeur(vp, segz, vX0)
    rv_p = N.modus_ponens(u_segz, N.loi_deduction(appartient(vX0, segz), rv_p))
    rv_p = N.modus_ponens(u_domp, N.loi_deduction(appartient(vX0, E.dom(vp)), rv_p))
    rv_q = restriction_valeur(vq, segz, vX0)
    rv_q = N.modus_ponens(u_segz, N.loi_deduction(appartient(vX0, segz), rv_q))
    rv_q = N.modus_ponens(u_domq, N.loi_deduction(appartient(vX0, E.dom(vq)), rv_q))
    # HR en x : p(x)=q(x)
    pq = N.modus_ponens(u_segz, instancie(hr, vX0))
    # (p|seg z)(x) = p(x) = q(x) = (q|seg z)(x)
    chaine = composer_egalites(composer_egalites(rv_p, pq),
        N.modus_ponens(rv_q, symetrie(E.valeur(qsz, vX0), E.valeur(vq, vX0))))
    val_eq = N.generalisation("x", N.loi_deduction(appartient(vX0, E.dom(psz)), chaine))

    # ── extensionnalité : les 6 prémisses gauche-associées, puis MP ──────────
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(f_p, f_q), g_p), g_q), dom_eq), val_eq)
    return N.modus_ponens(prem, graphe_egal_par_valeurs(psz, qsz))


__all__ = ["hypothese_recurrence", "restrictions_egales"]
