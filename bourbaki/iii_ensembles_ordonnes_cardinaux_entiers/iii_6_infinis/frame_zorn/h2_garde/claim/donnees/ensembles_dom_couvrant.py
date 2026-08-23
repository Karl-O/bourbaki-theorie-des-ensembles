# -*- coding: utf-8 -*-
"""§III.6.3 — DONNÉE 1/11 : tout point de US×US est dans le domaine d'un membre.

    dom_couvrant : { chaine(Γ𝔉,𝔉,C) }
        ⊢ (∀a)( a ∈ US×US ⇒ (∃p)( p ∈ 𝔇(C) et (∃w)( (a,w) ∈ p ) ) )

La plus composite des onze : un point de US×US a DEUX composantes, chacune
fournissant son membre de la chaîne, qu'il faut COMPARER pour les loger dans un
seul — dont la base contient alors les deux, et dont le carré de cette base EST
le domaine de la bijection.

⚠️ On emploie ici le conjoint pr₁ de l'ordre du frame (les BASES s'emboîtent),
là où `_inclusion_membres` extrait le conjoint pr₂ (les GRAPHES s'emboîtent).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, existe, impl, pourtout, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_monotone import (
    _membre_produit,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import (
    frame_ordre_membre_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
    dom_pr2_egale_carre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_surj_union import (
    _membre_famille_t,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
def dom_couvrant(E_set="E", C="Cch", a="abdm", p="pdm", w="wdm"):
    """🎯 { chaine } ⊢ (∀a)( a ∈ US×US ⇒ (∃p)(p∈𝔇 et (∃w)((a,w)∈p)) ). [1/11]."""
    vE, vC, va = _t(E_set), _t(C), var(a)
    D, US, Fr, Gam = (famille_de_chaine(vC), union_premiere(vC),
                      frame_pair(vE), frame_ordre(vE))
    h_ch = N.assume(chaine(Gam, Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)
    comparables = conjonction_elim_droite(conjonction_elim_droite(h_ch))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    prod = _membre_produit(US, US, va)
    ex1 = N.modus_ponens(N.assume(appartient(va, E.produit(US, US))),
                         equivalence_avant(prod))
    n1, corps1 = ex1.conclusion.lieur, ex1.conclusion.sous[0]
    n2, corps2 = corps1.lieur, corps1.sous[0]
    vc1, vc2 = var(n1), var(n2)

    h2 = N.assume(corps2)
    eq_a = conjonction_elim_gauche(conjonction_elim_gauche(h2))
    c1_us = conjonction_elim_droite(conjonction_elim_gauche(h2))
    c2_us = conjonction_elim_droite(h2)

    exu1 = N.modus_ponens(c1_us, equivalence_avant(membre_union_premiere(C, n1)))
    nu1, cu1 = exu1.conclusion.lieur, exu1.conclusion.sous[0]
    exu2a = N.modus_ponens(c2_us, equivalence_avant(membre_union_premiere(C, n2)))
    nu2 = nu1 + "b"
    exu2 = N.modus_ponens(exu2a, equivalence_avant(
        alpha_existe(nu1, nu2, exu2a.conclusion.sous[0])))
    cu2 = exu2.conclusion.sous[0]
    vu1, vu2 = var(nu1), var(nu2)

    hu1, hu2 = N.assume(cu1), N.assume(cu2)
    u1_C, c1_pr1 = conjonction_elim_gauche(hu1), conjonction_elim_droite(hu1)
    u2_C, c2_pr1 = conjonction_elim_gauche(hu2), conjonction_elim_droite(hu2)
    disj = N.modus_ponens(conjonction_intro(u1_C, u2_C),
                          instancie(instancie(comparables, vu1), vu2))

    corps_but = et(appartient(var(p), D),
                   existe(w, appartient(E.couple(va, var(w)), var(p))))

    def _cote(vmaj, autre, maj_C, comp_autre, thm_autre, thm_maj, maj_est_u2):
        dans_Gam = N.assume(appartient(E.couple(autre, vmaj), Gam))
        corps_o = N.modus_ponens(dans_Gam, equivalence_avant(
            frame_ordre_membre_t(vE, autre, vmaj)))
        incl = conjonction_elim_droite(conjonction_elim_gauche(corps_o))
        pr1m = E.pr1(vmaj)
        carre = E.produit(pr1m, pr1m)
        porte = N.modus_ponens(thm_autre, instancie(incl, comp_autre))
        d1, d2 = (porte, thm_maj) if maj_est_u2 else (thm_maj, porte)

        prodm = _membre_produit(pr1m, pr1m, va)
        cible = antecedent_consequent(equivalence_arriere(prodm).conclusion)[0]
        m1, b1 = cible.lieur, cible.sous[0]
        m2, b2 = b1.lieur, b1.sous[0]
        mineure = conjonction_intro(conjonction_intro(eq_a, d1), d2)
        a_carre = N.modus_ponens(N.modus_ponens(
            N.modus_ponens(mineure, N.s5(b2, vc2, m2)), N.s5(b1, vc1, m1)),
            equivalence_arriere(prodm))

        pr2m = E.pr2(vmaj)
        maj_Fr = N.modus_ponens(maj_C, instancie(C_inc, vmaj))
        dom_eq = N.modus_ponens(maj_Fr, N.loi_deduction(
            appartient(vmaj, Fr), dom_pr2_egale_carre(E_set, vmaj)))
        a_dom = N.modus_ponens(a_carre, equivalence_avant(N.modus_ponens(
            N.modus_ponens(dom_eq, symetrie(E.dom(pr2m), carre)),
            N.s6(carre, E.dom(pr2m), "wdk", appartient(va, var("wdk"))))))

        car = instancie(instancie(ax_dom, pr2m), va)
        ex_y = N.modus_ponens(a_dom, equivalence_avant(car))
        ny = ex_y.conclusion.lieur
        ex_w = N.modus_ponens(ex_y, equivalence_avant(
            alpha_existe(ny, w, ex_y.conclusion.sous[0])))

        equiv_m = _membre_famille_t(C, pr2m)
        ante = antecedent_consequent(equivalence_arriere(equiv_m).conclusion)[0]
        nq, corps_q = ante.lieur, ante.sous[0]
        pr2m_D = N.modus_ponens(N.modus_ponens(
            conjonction_intro(maj_C, N.reflexivite(pr2m)), N.s5(corps_q, vmaj, nq)),
            equivalence_arriere(equiv_m))

        but = N.modus_ponens(conjonction_intro(pr2m_D, ex_w),
                             N.s5(corps_but, pr2m, p))
        return N.loi_deduction(dans_Gam.conclusion, but)

    gauche = _cote(vu2, vu1, u2_C, vc1, c1_pr1, c2_pr1, True)
    droite = _cote(vu1, vu2, u1_C, vc2, c2_pr1, c1_pr1, False)
    but = cas(disj, gauche, droite)

    sortie = N.modus_ponens(exu2, existe_elimination(
        N.loi_deduction(cu2, but), nu2))
    sortie = N.modus_ponens(exu1, existe_elimination(
        N.loi_deduction(cu1, sortie), nu1))
    sortie = N.modus_ponens(N.assume(corps1), existe_elimination(
        N.loi_deduction(corps2, sortie), n2))
    sortie = N.modus_ponens(ex1, existe_elimination(
        N.loi_deduction(corps1, sortie), n1))
    res = N.generalisation(a, N.loi_deduction(
        appartient(va, E.produit(US, US)), sortie))

    assert res.conclusion == pourtout(a, impl(
        appartient(va, E.produit(US, US)), existe(p, corps_but))), \
        "dom_couvrant : forme"
    assert len(res.hypotheses) == 1, "dom_couvrant : hyps ≠ 1"
    return res


__all__ = ["dom_couvrant"]
