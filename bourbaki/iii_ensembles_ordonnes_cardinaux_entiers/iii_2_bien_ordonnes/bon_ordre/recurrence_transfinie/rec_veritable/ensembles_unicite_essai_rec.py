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
    Terme, var, egal, impl, appartient, pourtout,
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
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    graphe_egal_par_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
    heredite_couverture, couverture_transfinie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_inclus_dom_essai,
)
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


def couvert_unicite(p, q, G, e, x):
    """Le prédicat d'induction : couvert[t] := (t∈dom_essai(x) ⇒ p(t)=q(t)).

    GARDÉ par le domaine : hors de dom_essai(x) les valeurs sont du bruit-τ,
    l'égalité n'y est ni vraie ni utile — la garde rend l'hérédité prouvable."""
    vp, vq = _t(p), _t(q)
    domx = dom_essai(_t(G), _t(e), _t(x))
    return lambda t: impl(appartient(t, domx),
                          egal(E.valeur(vp, t), E.valeur(vq, t)))


def heredite_unicite(vh, p="pre", q="qre", G="Gsr", e="Esr", x="xsr"):
    """{bo, est_essai_rec(p,x), est_essai_rec(q,x)}
       ⊢ heredite_couverture(couvert_unicite, G, E)        [3 hyps honnêtes].

    L'HÉRÉDITÉ du prédicat gardé, aux liants x0tf/ytf imposés par le squelette
    C59 (couverture_transfinie).  Sous x0tf∈dom_essai(x) : seg(x0tf) ⊂
    dom_essai(x) [brique (ii)], donc l'HR gardée (∀ytf∈seg)(garde⇒égalité) se
    DÉGARDE en l'HR nue (∀ure∈seg)(p=q), et unicite_au_point conclut.
    Le conjoint x0tf∈E est un AFFAIBLISSEMENT (loi_deduction sur non-hypothèse)."""
    vp, vq, vG, ve = _t(p), _t(q), _t(G), _t(e)
    domx = dom_essai(vG, ve, _t(x))
    couvert = couvert_unicite(p, q, G, e, x)
    vy = var("x0tf")                                        # le point d'hérédité
    seg_y = E.segment_extremite(vG, ve, vy)
    hr_gardee = pourtout("ytf", impl(appartient(var("ytf"), seg_y),
                                     couvert(var("ytf"))))
    h_hrg = N.assume(hr_gardee)                             # l'HR GARDÉE (C59)
    h_yd = N.assume(appartient(vy, domx))                   # x0tf∈dom_essai(x)

    sub = N.modus_ponens(h_yd, seg_inclus_dom_essai(G, e, x, "x0tf"))  # {bo} seg⊂domx
    # l'HR NUE (∀ure)(ure∈seg(x0tf) ⇒ p(ure)=q(ure))  [dégardage point par point]
    vu = var("ure")
    h_us = N.assume(appartient(vu, seg_y))
    u_domx = N.modus_ponens(h_us, instancie(sub, vu))       # ure∈dom_essai(x)
    pq_u = N.modus_ponens(u_domx, N.modus_ponens(h_us, instancie(h_hrg, vu)))
    hr_nue = N.generalisation("ure", N.loi_deduction(appartient(vu, seg_y), pq_u))

    # le pas : unicite_au_point en z := x0tf, HR coupée par l'HR nue dérivée
    up = unicite_au_point(vh, p, q, G, e, x, z="x0tf", u="ure")
    up = _cut(hr_nue, hypothese_recurrence(vp, vq, vG, ve, vy), up)
    couv_y = N.loi_deduction(appartient(vy, domx), up)      # couvert[x0tf]
    imp_hr = N.loi_deduction(hr_gardee, couv_y)             # HR-gardée ⇒ couvert
    imp_E = N.loi_deduction(appartient(vy, ve), imp_hr)     # affaiblissement x0tf∈E
    her = N.generalisation("x0tf", imp_E)

    cible = heredite_couverture(couvert, G, ve, "x0tf", "ytf")
    assert her.conclusion == cible, "heredite_unicite : ≠ heredite_couverture"
    return her


def couverture_unicite(vh, p="pre", q="qre", G="Gsr", e="Esr", x="xsr"):
    """{bo, est_essai_rec(p,x), est_essai_rec(q,x)}
       ⊢ (∀x0tf)( x0tf∈E ⇒ (x0tf∈dom_essai(x) ⇒ p(x0tf)=q(x0tf)) )   [3 hyps].

    LA COUVERTURE TOTALE de l'unicité : le squelette C59 (couverture_transfinie)
    appliqué au prédicat gardé, son hypothèse d'hérédité DÉCHARGÉE par
    heredite_unicite.  Deux essais récursifs en x coïncident en tout point de E
    de leur domaine commun — l'extensionnalité (p=q) s'assemble en R2'-final."""
    ve = _t(e)
    couvert = couvert_unicite(p, q, G, e, x)
    her = heredite_unicite(vh, p, q, G, e, x)               # {bo, essais} ⊢ hérédité
    cov = couverture_transfinie(couvert, e, G)              # {bo, hérédité} ⊢ ∀
    return _cut(her, heredite_couverture(couvert, G, ve, "x0tf", "ytf"), cov)


def dom_essai_inclus_E(G="Gsr", e="Esr", x="xsr", u="ude"):
    """{ x∈E } ⊢ dom_essai(G,E,x) ⊂ E.

    dom_essai(x) = seg(x)∪{x} : u∈seg(x) donne u∈E par l'axiome-segment
    (conjoint gauche-gauche) ; u∈{x} donne u=x puis u∈E par Leibniz depuis
    l'hypothèse x∈E.  UNE hypothèse honnête."""
    vG, ve, vx, vu = _t(G), _t(e), _t(x), var(u)
    segx = E.segment_extremite(vG, ve, vx)
    singx = E.singleton(vx)
    domx = dom_essai(vG, ve, vx)

    h_xE = N.assume(appartient(vx, ve))                     # x∈E        [HONNÊTE]
    h_u = N.assume(appartient(vu, domx))
    disj = N.modus_ponens(h_u, equivalence_avant(
        _instance_reunion(segx, singx, vu)))                # u∈seg(x) ∨ u∈{x}

    # CAS A : u∈seg(x) ⇒ u∈E  (axiome-segment)
    h_us = N.assume(appartient(vu, segx))
    ax_seg = instancie(N.axiome(E.theorie_segment_extremite(),
                                E.axiome_segment_extremite()), vG)
    body = N.modus_ponens(h_us, equivalence_avant(
        instancie(instancie(instancie(ax_seg, ve), vx), vu)))
    impA = N.loi_deduction(appartient(vu, segx),
        conjonction_elim_gauche(conjonction_elim_gauche(body)))

    # CAS B : u∈{x} ⇒ u=x ⇒ u∈E  (Leibniz depuis x∈E)
    h_usx = N.assume(appartient(vu, singx))
    u_eq_x = N.modus_ponens(h_usx, equivalence_avant(singleton_membre(vu, vx)))
    u_E_B = N.modus_ponens(h_xE, equivalence_arriere(
        N.modus_ponens(u_eq_x, N.s6(vu, vx, "wue", appartient(var("wue"), ve)))))
    impB = N.loi_deduction(appartient(vu, singx), u_E_B)

    imp_u = N.loi_deduction(appartient(vu, domx), cas(disj, impA, impB))
    gen = N.generalisation(u, imp_u)
    return N.modus_ponens(gen, equivalence_avant(alpha_pour_tout(
        u, "z", impl(appartient(vu, domx), appartient(vu, ve)))))  # domx ⊂ E


# @livre Ch.III §2.2 Demo.60 | E III.18 L.34-39 | PDF p.121  (démonstration de C60 :
#   l'unicité tacite du recollement — deux essais récursifs au même point coïncident)
def unicite_essai_rec(vh, p="pre", q="qre", G="Gsr", e="Esr", x="xsr"):
    """🎯 LE LEMME R2' :
    { est_bien_ordonne(R,E),  est_essai_rec(p,vh,G,E,x),  est_essai_rec(q,vh,G,E,x),
      x∈E,  est_un_graphe(p),  est_un_graphe(q) }  ⊢  p = q     [6 hyps honnêtes].

    Deux essais RÉCURSIFS au même point sont LE MÊME graphe.  couverture_unicite
    (l'induction C59) donne l'égalité des valeurs sur E∩dom_essai(x) ;
    dom p = dom_essai(x) ⊂ E (sous x∈E) la transporte sur TOUT dom p ;
    graphe_egal_par_valeurs conclut.  Les hypothèses est_un_graphe viendront des
    essais bien-formés (R6') — ici honnêtes, jamais postulées."""
    vp, vq, vG, ve, vx = _t(p), _t(q), _t(G), _t(e), _t(x)
    domx = dom_essai(vG, ve, vx)

    h_ep = N.assume(est_essai_rec(vp, vh, vG, ve, vx))      # essai p    [HONNÊTE]
    h_eq = N.assume(est_essai_rec(vq, vh, vG, ve, vx))      # essai q    [HONNÊTE]
    h_gp = N.assume(E.est_un_graphe(vp))                    # p graphe   [HONNÊTE]
    h_gq = N.assume(E.est_un_graphe(vq))                    # q graphe   [HONNÊTE]
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(h_ep))
    dom_p = conjonction_elim_droite(conjonction_elim_gauche(h_ep))
    func_q = conjonction_elim_gauche(conjonction_elim_gauche(h_eq))
    dom_q = conjonction_elim_droite(conjonction_elim_gauche(h_eq))

    cov = couverture_unicite(vh, p, q, G, e, x)             # {bo, essais}
    incl_E = dom_essai_inclus_E(G, e, x)                    # {x∈E} domx ⊂ E

    # egalite_valeurs (lieur « x » imposé par l'extensionnalité — sans capture)
    vt = var("x")
    h_t = N.assume(appartient(vt, E.dom(vp)))
    t_domx = N.modus_ponens(h_t, equivalence_avant(
        N.modus_ponens(dom_p, N.s6(E.dom(vp), domx, "wre",
                                   appartient(vt, var("wre"))))))      # t∈domx
    t_E = N.modus_ponens(t_domx, instancie(incl_E, vt))                # t∈E
    pq_t = N.modus_ponens(t_domx, N.modus_ponens(t_E, instancie(cov, vt)))
    val_eq = N.generalisation("x", N.loi_deduction(appartient(vt, E.dom(vp)), pq_t))

    # dom p = dom_essai(x) = dom q, puis les 6 prémisses gauche-associées
    dom_eq = composer_egalites(dom_p, N.modus_ponens(dom_q, symetrie(E.dom(vq), domx)))
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(func_p, func_q), h_gp), h_gq), dom_eq), val_eq)
    res = N.modus_ponens(prem, graphe_egal_par_valeurs(vp, vq))        # p = q

    assert res.conclusion == egal(vp, vq), "unicite_essai_rec : conclusion ≠ p=q"
    assert len(res.hypotheses) == 6, "unicite_essai_rec : hyps ≠ 6"
    assert res.conclusion not in res.hypotheses, "unicite_essai_rec : VACUOUS"
    return res


__all__ = ["unicite_au_point", "couvert_unicite", "heredite_unicite",
           "couverture_unicite", "dom_essai_inclus_E", "unicite_essai_rec"]
