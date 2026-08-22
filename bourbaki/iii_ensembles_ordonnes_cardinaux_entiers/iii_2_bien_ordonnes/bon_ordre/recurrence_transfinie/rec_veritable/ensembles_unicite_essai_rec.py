# -*- coding: utf-8 -*-
"""§III.2.2 — R2'b : UNICITÉ AU POINT de l'essai récursif (le pas d'induction).

🎯 CIBLE (cinq hypothèses honnêtes) :

    { est_bien_ordonne(R,E),
      est_essai_rec(p, vh, G, E, x),  est_essai_rec(q, vh, G, E, x),
      z ∈ dom_essai(G,E,x),
      (∀u)(u∈seg(z) ⇒ p(u)=q(u)) }          [l'HR transfinie]
        ⊢  valeur(p,z) = valeur(q,z)

C'est le CŒUR du lemme d'unicité R2' (deux essais récursifs en x coïncident),
et la vraie récursion s'y voit : les équations d'essai donnent
p(z) = vh(p|seg z) et q(z) = vh(q|seg z) — la règle vh LIT LA RESTRICTION.
Sous l'HR, p|seg z = q|seg z (restrictions_egales, R2'a), et la CONGRUENCE
(C44) transporte l'égalité à travers la règle OPAQUE vh :
    p(z) = vh(p|seg z) = vh(q|seg z) = q(z).
Bourbaki (E III.18, démonstration de C60) : « deux applications ... coïncident
sur le segment, donc leurs valeurs coïncident » — l'unicité tacite du
recollement.

L'induction C59 (couverture_transfinie) déchargera l'HR au tick suivant :
heredite_couverture fournit EXACTEMENT (∀y)(y∈seg(x) ⇒ couvert[y]) ⇒ couvert[x],
la forme de l'HR ci-dessus (interface hypothese_recurrence, R2'a).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec, restriction_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_restrictions_egales import (
    hypothese_recurrence, restrictions_egales,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _equation_en(h_essai, graphe, domx, vz, h_zd):
    """De est_essai_rec(g) assumé et z∈dom_essai(x), extraire (func g, dom g=domx,
    g(z)=vh(g|seg z)) — l'équation d'essai DÉPLIÉE au point z."""
    func_g = conjonction_elim_gauche(conjonction_elim_gauche(h_essai))
    dom_g = conjonction_elim_droite(conjonction_elim_gauche(h_essai))
    eq_g = conjonction_elim_droite(h_essai)                 # (∀z)(z∈dom g ⇒ …)
    # z∈dom g  (réécriture S6 : dom_essai(x) = dom g depuis dom g = dom_essai(x))
    sym = N.modus_ponens(dom_g, symetrie(E.dom(graphe), domx))
    z_dom = N.modus_ponens(h_zd, equivalence_avant(
        N.modus_ponens(sym, N.s6(domx, E.dom(graphe), "wre",
                                 appartient(vz, var("wre"))))))
    eq_z = N.modus_ponens(z_dom, instancie(eq_g, vz))       # g(z) = vh(g|seg z)
    return func_g, dom_g, eq_z


def unicite_au_point(vh, p="pre", q="qre", G="Gsr", e="Esr", x="xsr", z="zsr",
                     u="ure"):
    """{bo, est_essai_rec(p,x), est_essai_rec(q,x), z∈dom_essai(x), HR}
       ⊢ valeur(p,z) = valeur(q,z)                          [5 hyps honnêtes].

    Le pas d'induction du lemme d'unicité R2' — voir la docstring de module."""
    vp, vq, vG, ve, vx, vz = _t(p), _t(q), _t(G), _t(e), _t(x), _t(z)
    domx = dom_essai(vG, ve, vx)
    psz = restriction_seg(vp, vG, ve, vz)                   # p|seg z
    qsz = restriction_seg(vq, vG, ve, vz)                   # q|seg z

    h_ep = N.assume(est_essai_rec(vp, vh, vG, ve, vx))      # essai p    [HONNÊTE]
    h_eq = N.assume(est_essai_rec(vq, vh, vG, ve, vx))      # essai q    [HONNÊTE]
    h_zd = N.assume(appartient(vz, domx))                   # z∈dom_essai(x)

    func_p, dom_p, p_eq = _equation_en(h_ep, vp, domx, vz, h_zd)  # p(z)=vh(p|seg z)
    func_q, dom_q, q_eq = _equation_en(h_eq, vq, domx, vz, h_zd)  # q(z)=vh(q|seg z)

    # ── R2'a : p|seg z = q|seg z, en coupant les 4 conjoints dérivés de l'essai ──
    restr = restrictions_egales(p, q, G, e, x, z, u)
    restr = _cut(func_p, E.est_fonctionnel(vp), restr)
    restr = _cut(func_q, E.est_fonctionnel(vq), restr)
    restr = _cut(dom_p, egal(E.dom(vp), domx), restr)
    restr = _cut(dom_q, egal(E.dom(vq), domx), restr)       # {bo, essais, z∈domx, HR}

    # ── congruence C44 à travers la règle OPAQUE : vh(p|seg z) = vh(q|seg z) ─────
    vh_eq = N.modus_ponens(restr, congruence_terme(psz, qsz, vh(var("wrec")), "wrec"))

    # ── p(z) = vh(p|seg z) = vh(q|seg z) = q(z) ──────────────────────────────────
    gauche_ = composer_egalites(p_eq, vh_eq)                # p(z) = vh(q|seg z)
    retour = N.modus_ponens(q_eq, symetrie(E.valeur(vq, vz), vh(qsz)))
    return composer_egalites(gauche_, retour)               # p(z) = q(z)


__all__ = ["unicite_au_point"]
