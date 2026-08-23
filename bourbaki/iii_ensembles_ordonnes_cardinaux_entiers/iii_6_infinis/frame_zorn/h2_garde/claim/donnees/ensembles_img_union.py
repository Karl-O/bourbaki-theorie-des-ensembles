# -*- coding: utf-8 -*-
"""§III.6.3 — DONNÉE 10/11 : les valeurs du graphe recollé tiennent dans US.

🎯 CIBLE :

    img_union_inclus_us : { chaine(Γ𝔉,𝔉,C) } ⊢ image(⋃𝔇(C), US×US) ⊂ US(C)

Jumelle de la donnée (9) : même descente en trois existentielles emboîtées —
un antécédent x, le membre p qui contient (x,w), le u de la chaîne dont p est
la seconde projection — mais l'axiome de l'IMAGE au départ, et
`valeur_dans_pr1` à l'arrivée : les valeurs d'un membre restent dans sa base,
laquelle est incluse dans US.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, inclus,
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
    symetrie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, _inst_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, membre_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
    pr1_inclus_union, valeur_dans_pr1,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (le graphe recollé prend ses valeurs dans la réunion des bases)
def img_union_inclus_us(E_set="E", C="Cch", w="wiu"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ image( ⋃𝔇(C), US×US ) ⊂ US(C).   [donnée 10/11].

    Une valeur w du graphe recollé provient d'un membre p = pr₂(u) ; par
    `valeur_dans_pr1` elle tombe dans pr₁(u), et `pr1_inclus_union` place
    celui-ci dans US.

    ⚠️ Le liant demandé à `pr1_inclus_union` est « z », celui qu'attend
    l'instanciation — c'est le piège qui avait coûté l'unique essai raté de la
    donnée (9) (LEÇON 18)."""
    vE, vC, vw = _t(E_set), _t(C), var(w)
    D = famille_de_chaine(vC)
    U, US, Fr = union_famille(D), union_premiere(vC), frame_pair(vE)
    Prod = E.produit(US, US)
    h_ch = N.assume(chaine(frame_ordre(vE), Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car_w = instancie(instancie(instancie(ax_img, U), Prod), vw)
    ex_x = N.modus_ponens(N.assume(appartient(vw, E.image(U, Prod))),
                          equivalence_avant(car_w))
    nx, corps_x = ex_x.conclusion.lieur, ex_x.conclusion.sous[0]
    vx = var(nx)

    xw = E.couple(vx, vw)
    ex_p = N.modus_ponens(conjonction_elim_droite(N.assume(corps_x)),
                          equivalence_avant(_inst_union_famille(D, xw)))
    npp, corps_p = ex_p.conclusion.lieur, ex_p.conclusion.sous[0]
    vpp = var(npp)

    h_p = N.assume(corps_p)
    xw_in_p = conjonction_elim_droite(h_p)
    ex_u = N.modus_ponens(conjonction_elim_gauche(h_p),
                          equivalence_avant(membre_famille(C, npp)))
    nu, corps_u = ex_u.conclusion.lieur, ex_u.conclusion.sous[0]
    vu = var(nu)

    h_u = N.assume(corps_u)
    u_in_C, p_eq = conjonction_elim_gauche(h_u), conjonction_elim_droite(h_u)

    #  (x,w) ∈ p  et  p = pr₂u  ⟹  (x,w) ∈ pr₂u
    xw_in_pr2 = N.modus_ponens(xw_in_p, equivalence_avant(N.modus_ponens(
        p_eq, N.s6(vpp, E.pr2(vu), "wiz", appartient(xw, var("wiz"))))))

    #  les valeurs d'un membre restent dans sa base
    u_in_Fr = N.modus_ponens(u_in_C, instancie(C_inc, vu))
    val = N.modus_ponens(u_in_Fr, N.loi_deduction(
        appartient(vu, Fr), valeur_dans_pr1(E_set, vu)))
    w_pr1 = N.modus_ponens(xw_in_pr2, instancie(instancie(val, vx), vw))

    #  pr₁u ⊂ US, instanciée en w
    incl = N.modus_ponens(u_in_C, N.loi_deduction(
        appartient(vu, vC), pr1_inclus_union(C, vu, x="z")))
    but = N.modus_ponens(w_pr1, instancie(incl, vw))

    sortie = N.modus_ponens(ex_u, existe_elimination(
        N.loi_deduction(corps_u, but), nu))
    sortie = N.modus_ponens(ex_p, existe_elimination(
        N.loi_deduction(corps_p, sortie), npp))
    sortie = N.modus_ponens(ex_x, existe_elimination(
        N.loi_deduction(corps_x, sortie), nx))
    res = N.generalisation(w, N.loi_deduction(
        appartient(vw, E.image(U, Prod)), sortie))

    assert res.conclusion == inclus(E.image(U, Prod), US, w), \
        "img_union_inclus_us : forme"
    assert len(res.hypotheses) == 1, "img_union_inclus_us : hyps ≠ 1"
    return res


__all__ = ["img_union_inclus_us"]
