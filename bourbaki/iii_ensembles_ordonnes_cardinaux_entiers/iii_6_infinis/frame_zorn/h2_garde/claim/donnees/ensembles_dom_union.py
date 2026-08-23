# -*- coding: utf-8 -*-
"""§III.6.3 — DONNÉE 9/11 : le domaine du graphe recollé tient dans US×US.

🎯 CIBLE :

    dom_union_inclus_carre : { chaine(Γ𝔉,𝔉,C) } ⊢ dom(⋃𝔇(C)) ⊂ US(C)×US(C)

Séparé de `ensembles_union_premiere` (qui porte les BRIQUES) pour tenir la
limite de 300 lignes : ici l'ASSEMBLAGE, là les pièces.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, equivalence_arriere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
    pr1_inclus_union, dom_pr2_egale_carre,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (le graphe recollé est défini sur le carré de la réunion)
def dom_union_inclus_carre(E_set="E", C="Cch", z="zdu"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ dom( ⋃𝔇(C) ) ⊂ US(C) × US(C).   [donnée 9/11].

    Trois descentes existentielles emboîtées — un y, puis le membre p qui
    contient (z,y), puis le u de la chaîne dont p est la seconde projection —
    et deux remontées : le domaine de p est un CARRÉ (`dom_pr2_egale_carre`),
    que `produit_monotone_carre` fait croître jusqu'à US×US via
    `pr1_inclus_union`.

    ⚠️ Le point qui coûte un essai si on ne l'anticipe pas : de « (z,y) ∈ p »
    il faut REVENIR à « z ∈ dom(p) » par l'axiome du domaine en sens ARRIÈRE
    (S5 au témoin y) avant de pouvoir invoquer l'égalité du domaine."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
        antecedent_consequent,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite, instancie,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        existe_elimination,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        composer_egalites, congruence_terme,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import chaine
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
        union_famille, _inst_union_famille,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_monotone import (
        produit_monotone_carre,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
        frame_pair, frame_ordre,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
        famille_de_chaine, membre_famille,
    )
    vE, vC, vz = _t(E_set), _t(C), var(z)
    D = famille_de_chaine(vC)
    U, US, Fr = union_famille(D), union_premiere(vC), frame_pair(vE)
    h_ch = N.assume(chaine(frame_ordre(vE), Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    car_z = instancie(instancie(ax_dom, U), vz)
    ex_y = N.modus_ponens(N.assume(appartient(vz, E.dom(U))),
                          equivalence_avant(car_z))
    ny, corps_y = ex_y.conclusion.lieur, ex_y.conclusion.sous[0]
    vy = var(ny)

    ex_p = N.modus_ponens(N.assume(corps_y),
                          equivalence_avant(_inst_union_famille(D, E.couple(vz, vy))))
    npp, corps_p = ex_p.conclusion.lieur, ex_p.conclusion.sous[0]
    vpp = var(npp)

    h_p = N.assume(corps_p)
    zy_in_p = conjonction_elim_droite(h_p)
    ex_u = N.modus_ponens(conjonction_elim_gauche(h_p),
                          equivalence_avant(membre_famille(C, npp)))
    nu, corps_u = ex_u.conclusion.lieur, ex_u.conclusion.sous[0]
    vu = var(nu)

    h_u = N.assume(corps_u)
    u_in_C, p_eq = conjonction_elim_gauche(h_u), conjonction_elim_droite(h_u)

    #  retour de « (z,y) ∈ p » vers « z ∈ dom p »  (sens ARRIÈRE)
    car_p = instancie(instancie(ax_dom, vpp), vz)
    corps_loc = antecedent_consequent(equivalence_avant(car_p).conclusion)[1]
    z_in_dom = N.modus_ponens(
        N.modus_ponens(zy_in_p, N.s5(corps_loc.sous[0], vy, corps_loc.lieur)),
        equivalence_arriere(car_p))

    #  dom p = dom(pr₂u) = pr₁u × pr₁u
    u_in_Fr = N.modus_ponens(u_in_C, instancie(C_inc, vu))
    dom_eq = N.modus_ponens(u_in_Fr, N.loi_deduction(
        appartient(vu, Fr), dom_pr2_egale_carre(E_set, vu)))
    carre = E.produit(E.pr1(vu), E.pr1(vu))
    total = composer_egalites(N.modus_ponens(p_eq, congruence_terme(
        vpp, E.pr2(vu), E.dom(var("wdz")), "wdz")), dom_eq)
    z_in_carre = N.modus_ponens(z_in_dom, equivalence_avant(N.modus_ponens(
        total, N.s6(E.dom(vpp), carre, "wdz", appartient(vz, var("wdz"))))))

    #  pr₁u ⊂ US, donc le carré croît jusqu'à US×US
    #  ⚠️ LEÇON 18 : `produit_monotone_carre` attend une inclusion de liant « z »
    #  (le défaut de `inclus`) ; on demande donc ce liant à `pr1_inclus_union`,
    #  au lieu de son « xup » habituel — sinon les formules ne coïncident pas.
    incl = N.modus_ponens(u_in_C, N.loi_deduction(
        appartient(vu, vC), pr1_inclus_union(C, vu, x="z")))
    mono = N.modus_ponens(incl, N.loi_deduction(
        inclus(E.pr1(vu), US), produit_monotone_carre(E.pr1(vu), US)))
    but = N.modus_ponens(z_in_carre, instancie(mono, vz))

    sortie = N.modus_ponens(ex_u, existe_elimination(
        N.loi_deduction(corps_u, but), nu))
    sortie = N.modus_ponens(ex_p, existe_elimination(
        N.loi_deduction(corps_p, sortie), npp))
    sortie = N.modus_ponens(ex_y, existe_elimination(
        N.loi_deduction(corps_y, sortie), ny))
    res = N.generalisation(z, N.loi_deduction(appartient(vz, E.dom(U)), sortie))

    assert res.conclusion == inclus(E.dom(U), E.produit(US, US), z),         "dom_union_inclus_carre : forme"
    assert len(res.hypotheses) == 1, "dom_union_inclus_carre : hyps ≠ 1"
    return res


__all__ = ["dom_union_inclus_carre"]
