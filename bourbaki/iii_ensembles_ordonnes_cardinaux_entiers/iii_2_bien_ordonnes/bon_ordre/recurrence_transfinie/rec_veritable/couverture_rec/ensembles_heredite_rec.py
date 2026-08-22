# -*- coding: utf-8 -*-
"""§III.2.2 — R5'-final (briques AMBIANTES) : tout vit dans 𝔓(E×V).

🎯 CIBLES :

    membre_ambiant_graphe :  { p∈𝔓(E×V) }        ⊢  est_un_graphe(p)
    union_rec_ambiante    :  ⊢  ⋃Dfam_rec(x) ∈ 𝔓(E×V)                 [CLOS]
    extension_ambiante    :  { p∈𝔓(E×V), x∈E, v∈V }  ⊢  p∪{(x,v)} ∈ 𝔓(E×V)
    regle_dans_V          :  la FORME (∀pgv)( vh(pgv)∈V )   [hypothèse honnête]

Le prédicat de couverture est AMBIANT (couvert_essai_rec_amb exige le témoin
dans 𝔓(E×V)) : ces briques fournissent (i) le conjoint est_un_graphe des
essais (extension R3', unicité R2'), (ii) l'ambiance de la réunion (héritée
des membres), (iii) l'ambiance de l'essai étendu — sous l'hypothèse honnête
que la règle vh prend ses valeurs dans V (la donnée de C60 : T à valeurs dans
un ensemble V, Bourbaki E III.18).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    _inst_parties,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    inclus_produit_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    membre_reunion_graphes,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, _inst_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
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


def regle_dans_V(vh, V="Vval", p="pgv"):
    """La FORME d'hypothèse « la règle prend ses valeurs dans V » :
    (∀pgv)( vh(pgv) ∈ V ).  Nom pgv FRAIS (vh peut lier ses propres noms)."""
    return pourtout(p, appartient(vh(var(p)), _t(V)))


def membre_ambiant_graphe(e="Esr", V="Vval", p="pha"):
    """{ p∈𝔓(E×V) } ⊢ est_un_graphe(p)                       [1 hyp honnête]."""
    ve, vV, vp = _t(e), _t(V), _t(p)
    prod = E.produit(ve, vV)
    h = N.assume(appartient(vp, ambiant(e, V)))
    incl = N.modus_ponens(h, equivalence_avant(_inst_parties(prod, vp)))
    return _cut(incl, inclus(vp, prod), inclus_produit_est_graphe(vp, ve, vV))


def union_rec_incluse(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """⊢ ⋃Dfam_rec(x) ⊂ E×V                                   [CLOS, 0 hyp].

    Chaque w de la réunion vient d'un membre punion ∈ 𝔓(E×V) (axiome S8),
    donc w ∈ E×V (A3 + inclusion instanciée)."""
    vG, ve, vx, vV = _t(G), _t(e), _t(x), _t(V)
    D = Dfam_rec(vG, ve, vx, V)
    U = union_famille(D)
    prod = E.produit(ve, vV)
    vw, vpun = var("wha"), var("punion")

    h_w = N.assume(appartient(vw, U))
    ex = N.modus_ponens(h_w, equivalence_avant(_inst_union_famille(D, vw)))
    corps = et(appartient(vpun, D), appartient(vw, vpun))
    h_c = N.assume(corps)
    pun_amb = conjonction_elim_gauche(N.modus_ponens(
        conjonction_elim_gauche(h_c),
        equivalence_avant(membre_Dfam_rec(vh, G, e, vx, vpun, V, y="yDr"))))
    pun_incl = N.modus_ponens(pun_amb, equivalence_avant(_inst_parties(prod, vpun)))
    w_prod = N.modus_ponens(conjonction_elim_droite(h_c), instancie(pun_incl, vw))
    r = N.modus_ponens(ex, existe_elimination(
        N.loi_deduction(corps, w_prod), "punion"))
    sub = N.loi_deduction(appartient(vw, U), r)
    res = N.modus_ponens(N.generalisation("wha", sub), equivalence_avant(
        alpha_pour_tout("wha", "z", impl(appartient(vw, U), appartient(vw, prod)))))
    assert res.est_clos, "union_rec_incluse : non clos"
    return res


def union_rec_ambiante(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """⊢ ⋃Dfam_rec(x) ∈ 𝔓(E×V)                                [CLOS, 0 hyp]."""
    vG, ve, vx, vV = _t(G), _t(e), _t(x), _t(V)
    U = union_famille(Dfam_rec(vG, ve, vx, V))
    prod = E.produit(ve, vV)
    res = N.modus_ponens(union_rec_incluse(vh, G, e, x, V),
                         equivalence_arriere(_inst_parties(prod, U)))
    assert res.est_clos, "union_rec_ambiante : non clos"
    return res


def extension_ambiante(p="pha", x="xsr", v="vha", e="Esr", V="Vval"):
    """{ p∈𝔓(E×V), x∈E, v∈V } ⊢ p∪{(x,v)} ∈ 𝔓(E×V)           [3 hyps honnêtes].

    p ⊂ E×V (A3) ; (x,v) ∈ E×V (AXIOME_PRODUIT, sens ⇐, témoins x/v re-liés
    aux liants p/q de l'axiome) ; la réunion des deux reste ⊂ E×V (cas)."""
    vp, vx, vv, ve, vV = _t(p), _t(x), _t(v), _t(e), _t(V)
    prod = E.produit(ve, vV)
    cpl = E.couple(vx, vv)
    S = E.singleton(cpl)
    pS = E.reunion(vp, S)
    vu = var("uha")

    h_amb = N.assume(appartient(vp, ambiant(e, V)))         # p∈𝔓(E×V)
    h_xE = N.assume(appartient(vx, ve))                     # x∈E
    h_vV = N.assume(appartient(vv, vV))                     # v∈V
    p_incl = N.modus_ponens(h_amb, equivalence_avant(_inst_parties(prod, vp)))

    # (x,v) ∈ E×V  (corps-produit aux témoins x,v, S5 ×2 vers les liants p/q)
    corps_xv = et(et(egal(cpl, cpl), appartient(vx, ve)), appartient(vv, vV))
    corps_prouve = conjonction_intro(
        conjonction_intro(N.reflexivite(cpl), h_xE), h_vV)
    R_q = et(et(egal(cpl, E.couple(vx, var("q"))), appartient(vx, ve)),
             appartient(var("q"), vV))
    ex_q = N.modus_ponens(corps_prouve, N.s5(R_q, vv, "q"))
    R_pq = et(et(egal(cpl, E.couple(var("p"), var("q"))),
                 appartient(var("p"), ve)), appartient(var("q"), vV))
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", R_pq), vx, "p"))
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    cpl_prod = N.modus_ponens(ex_pq, equivalence_arriere(
        instancie(instancie(instancie(ax_prod, ve), vV), cpl)))     # (x,v)∈E×V

    # u∈p∪S ⇒ u∈E×V  (cas), puis A3 referme
    h_u = N.assume(appartient(vu, pS))
    disj = N.modus_ponens(h_u, equivalence_avant(membre_reunion_graphes(vp, S, vu)))
    impA = N.loi_deduction(appartient(vu, vp),
        N.modus_ponens(N.assume(appartient(vu, vp)), instancie(p_incl, vu)))
    h_us = N.assume(appartient(vu, S))
    u_eq = N.modus_ponens(h_us, equivalence_avant(singleton_membre(vu, cpl)))
    impB = N.loi_deduction(appartient(vu, S),
        N.modus_ponens(cpl_prod, equivalence_arriere(N.modus_ponens(
            u_eq, N.s6(vu, cpl, "wha", appartient(var("wha"), prod))))))
    u_prod = cas(disj, impA, impB)
    sub = N.loi_deduction(appartient(vu, pS), u_prod)
    incl_pS = N.modus_ponens(N.generalisation("uha", sub), equivalence_avant(
        alpha_pour_tout("uha", "z", impl(appartient(vu, pS),
                                         appartient(vu, prod)))))
    res = N.modus_ponens(incl_pS, equivalence_arriere(_inst_parties(prod, pS)))
    assert len(res.hypotheses) == 3, "extension_ambiante : hyps ≠ 3"
    return res


# @livre Ch.III §2.2 Demo.60 | E III.19 L.1-5 | PDF p.122  (fin de la démonstration
#   de C60 : recollement des essais + prolongement d'un pas = l'hérédité)
def heredite_rec(vh, G="Gsr", e="Esr", V="Vval"):
    """🎯 R5'-FINAL : { bo, regle_dans_V(vh,V) }
       ⊢ heredite_couverture( couvert_essai_rec_amb, G, E )   [2 hyps honnêtes].

    L'HÉRÉDITÉ COMPLÈTE : pour x0tf∈E dont tout le segment est couvert (HR C59
    au lieur ytf, α-pontée vers l'antécédent yaa des U-lemmes), le recollement
    U := ⋃Dfam_rec(x0tf) est un essai-sur-seg (U1 fonctionnalité, U-dom, U4
    équation, ambiance→graphe) ; l'extension R3' donne l'essai récursif
    p' := U∪{(x0tf, vh(U))} EN x0tf, ambiant (extension_ambiante sous
    vh(U)∈V, la règle bornée) — le témoin S5 de couvert[x0tf]."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
        heredite_couverture,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
        famille_compatible, union_famille_fonctionnelle,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
        equation_sur_seg, extension_essai_rec,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
        est_essai_rec,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
        couvert_essai_rec_amb, antecedent_couverture_rec, dom_union_rec,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_union_rec import (
        compatibilite_Dfam_rec,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_equation_union import (
        equation_union_rec,
    )
    vG, ve, vV = _t(G), _t(e), _t(V)
    couvert = couvert_essai_rec_amb(vh, G, e, V)
    vx0 = var("x0tf")
    segx0 = E.segment_extremite(vG, ve, vx0)
    D = Dfam_rec(vG, ve, vx0, V)
    U = union_famille(D)
    pprime = E.reunion(U, E.singleton(E.couple(vx0, vh(U))))

    h_xE = N.assume(appartient(vx0, ve))                    # x0tf∈E
    hr_ytf = pourtout("ytf", impl(appartient(var("ytf"), segx0),
                                  couvert(var("ytf"))))
    h_hrg = N.assume(hr_ytf)                                # l'HR C59 (lieur ytf)
    h_regle = N.assume(regle_dans_V(vh, V))                 # vh à valeurs dans V

    # pont α ytf→yaa : l'antécédent au lieur des U-lemmes
    ant_formule = antecedent_couverture_rec(vh, G, e, "x0tf", V)
    ant_yaa = N.modus_ponens(h_hrg, equivalence_avant(alpha_pour_tout(
        "ytf", "yaa", impl(appartient(var("ytf"), segx0), couvert(var("ytf"))))))

    # U est un essai-sur-seg : les 4 conjoints d'extension_essai_rec
    compat = compatibilite_Dfam_rec(vh, G, e, "x0tf", V)    # {bo}
    func_U = _cut(compat, famille_compatible(D), union_famille_fonctionnelle(D))
    du = _cut(ant_yaa, ant_formule, dom_union_rec(vh, G, e, "x0tf", V))
    g_U = _cut(union_rec_ambiante(vh, G, e, "x0tf", V),
               appartient(U, ambiant(e, V)), membre_ambiant_graphe(e, V, U))
    equ = _cut(ant_yaa, ant_formule, equation_union_rec(vh, G, e, "x0tf", V))

    ext = extension_essai_rec(vh, U, G, e, "x0tf")          # 5 hyps
    ext = _cut(func_U, E.est_fonctionnel(U), ext)
    ext = _cut(du, egal(E.dom(U), segx0), ext)
    ext = _cut(g_U, E.est_un_graphe(U), ext)
    ext = _cut(equ, equation_sur_seg(U, vh, vG, ve), ext)   # est_essai_rec(p', x0tf)

    # p' ∈ 𝔓(E×V)  (vh(U)∈V par la règle bornée instanciée au terme U)
    amb_p = extension_ambiante(U, "x0tf", vh(U), e, V)
    amb_p = _cut(union_rec_ambiante(vh, G, e, "x0tf", V),
                 appartient(U, ambiant(e, V)), amb_p)
    amb_p = _cut(instancie(h_regle, U), appartient(vh(U), vV), amb_p)

    # couvert[x0tf] : témoin S5 = p'
    corps_paa = et(appartient(var("paa"), ambiant(e, V)),
                   est_essai_rec(var("paa"), vh, vG, ve, vx0))
    cov_x0 = N.modus_ponens(conjonction_intro(amb_p, ext),
                            N.s5(corps_paa, pprime, "paa"))

    her = N.generalisation("x0tf", N.loi_deduction(appartient(vx0, ve),
                           N.loi_deduction(hr_ytf, cov_x0)))
    cible = heredite_couverture(couvert, G, ve, "x0tf", "ytf")
    assert her.conclusion == cible, "heredite_rec : ≠ heredite_couverture"
    assert len(her.hypotheses) == 2, "heredite_rec : hyps ≠ 2 (bo, règle)"
    return her


# @livre Ch.III §2.2 Crit.C60 | E III.18 L.24-33 | PDF p.121  (C60, moitié existence :
#   tout point de E porte un essai récursif — la couverture totale)
def couverture_totale_rec(vh, G="Gsr", e="Esr", V="Vval"):
    """🎯🎯 R6' — LA COUVERTURE TOTALE DE LA VRAIE RÉCURSION :
       { bo, regle_dans_V(vh,V) }
       ⊢ (∀x)( x∈E ⇒ (∃p)( p∈𝔓(E×V) ∧ est_essai_rec(p, vh, G, E, x) ) ).

    Le squelette C59 (couverture_transfinie) sur le prédicat ambiant, son
    hypothèse d'hérédité DÉCHARGÉE par heredite_rec : TOUT point d'un ensemble
    bien ordonné porte un essai de la VRAIE récursion (l'équation lit la
    restriction).  Deux hypothèses honnêtes : le bon ordre, la règle bornée."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
        heredite_couverture, couverture_transfinie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
        couvert_essai_rec_amb,
    )
    ve = _t(e)
    couvert = couvert_essai_rec_amb(vh, G, e, V)
    her = heredite_rec(vh, G, e, V)                         # {bo, règle}
    cov = couverture_transfinie(couvert, e, G)              # {bo, hérédité}
    res = _cut(her, heredite_couverture(couvert, G, ve, "x0tf", "ytf"), cov)
    assert len(res.hypotheses) == 2, "couverture_totale_rec : hyps ≠ 2"
    return res


__all__ = ["regle_dans_V", "membre_ambiant_graphe", "union_rec_incluse",
           "union_rec_ambiante", "extension_ambiante", "heredite_rec",
           "couverture_totale_rec"]
