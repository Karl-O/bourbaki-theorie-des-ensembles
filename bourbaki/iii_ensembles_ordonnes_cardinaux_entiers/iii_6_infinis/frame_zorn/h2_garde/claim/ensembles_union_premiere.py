# -*- coding: utf-8 -*-
"""§III.6.3 — LE PONT ENTRE UN MEMBRE DE LA CHAÎNE ET ⋃S(C).

🎯 CIBLE :

    pr1_inclus_union : { u ∈ C } ⊢ pr₁(u) ⊂ ⋃S(C)

C'est la brique commune aux QUATRE dernières données du recollement — les
seules qui mêlent la famille 𝔇 et la réunion US (RECHERCHE R-13).  Les sept
premières ne parlaient que de 𝔇 ; celles-ci exigent de relier chaque membre
de la chaîne à la réunion de leurs premières projections.

L'énoncé est immédiat une fois `membre_union_premiere` en main — x ∈ ⋃S(C)
équivaut à l'existence d'un p ∈ C dont la première projection contient x — mais
il faut l'employer dans le sens ARRIÈRE (introduire l'existentielle par S5 au
témoin u), là où `us_inclus_E` l'employait dans le sens avant.

⚠️ `membre_union_premiere` attend des NOMS (elle applique `var()` elle-même) :
c'est ce piège qui avait fait classer `us_inclus_E` en chantier des jours
durant (LEÇON 17).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_union_premiere,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (chaque X de la chaîne est contenu dans la réunion ⋃X)
def pr1_inclus_union(C="Cch", u="umem", x="xup"):
    """🎯 { u ∈ C } ⊢ pr₁(u) ⊂ ⋃S(C).

    Point à point : si x ∈ pr₁(u) et que u ∈ C, alors u TÉMOIGNE de
    l'existentielle qui caractérise ⋃S(C) — d'où x ∈ ⋃S(C).

    Sens ARRIÈRE de `membre_union_premiere` : c'est S5 qui introduit
    l'existentielle au témoin u, et non une élimination."""
    vC, vu, vx = _t(C), _t(u), var(x)
    US = union_premiere(vC)

    mem = membre_union_premiere(C, x)          # (x∈⋃S) ⇔ (∃p)(p∈C et x∈pr₁p)
    #  le corps et le liant RÉELS de l'existentielle — jamais reconstruits
    ex_reel = antecedent_consequent(equivalence_avant(mem).conclusion)[1]
    np, corps = ex_reel.lieur, ex_reel.sous[0]

    temoin = conjonction_intro(N.assume(appartient(vu, vC)),
                               N.assume(appartient(vx, E.pr1(vu))))
    ex_intro = N.modus_ponens(temoin, N.s5(corps, vu, np))
    dans_US = N.modus_ponens(ex_intro, equivalence_arriere(mem))
    res = N.generalisation(x, N.loi_deduction(
        appartient(vx, E.pr1(vu)), dans_US))

    assert res.conclusion == inclus(E.pr1(vu), US, x), "pr1_inclus_union : forme"
    assert list(res.hypotheses) == [appartient(vu, vC)], "pr1_inclus_union : hyps"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (la bijection d'un membre est définie sur le carré de sa première projection)
def dom_pr2_egale_carre(E_set="E", p="pmemb"):
    """🎯 { p ∈ 𝔉(E) } ⊢ dom( pr₂(p) ) = pr₁(p) × pr₁(p).

    Le corps du frame donne `est_bijection_de(φ, S×S, S)`, dont le SECOND
    conjoint du premier conjoint est « dom φ = S×S ».  Deux transports de
    Leibniz suffisent ensuite : φ → pr₂(p) et S → pr₁(p).

    C'est la pièce qui manquait à la donnée (9) du recollement : elle situe le
    domaine de chaque membre dans un carré, seule forme que
    `produit_monotone_carre` sait faire croître."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere, projection_seconde,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        existe_elimination,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
        frame_pair,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import (
        _frame_membre_t,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    vE, vp = _t(E_set), _t(p)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)
    decl = N.modus_ponens(N.assume(appartient(vp, frame_pair(vE))),
                          equivalence_avant(_frame_membre_t(vE, vp)))
    exS = decl.conclusion
    nS, bodyS = exS.lieur, exS.sous[0]
    nphi, bodyphi = bodyS.lieur, bodyS.sous[0]

    def inner(b):
        hh = N.assume(b)
        vS, vphi = var(nS), var(nphi)
        bij = conjonction_elim_droite(hh)
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))                    # p = (S,φ)
        dom_eq = conjonction_elim_droite(conjonction_elim_gauche(bij))
        #  pr₂(p) = φ  et  pr₁(p) = S
        eq_pr2 = composer_egalites(N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr2(var("wdp")), "wdp")),
            projection_seconde(nS, nphi))
        eq_pr1 = composer_egalites(N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr1(var("wdp")), "wdp")),
            projection_premiere(nS, nphi))
        #  dom(pr₂p) = dom(φ) = S×S = pr₁p × pr₁p
        gauche = composer_egalites(N.modus_ponens(eq_pr2, congruence_terme(
            pr2p, vphi, E.dom(var("wdp")), "wdp")), dom_eq)
        droite = N.modus_ponens(N.modus_ponens(eq_pr1, symetrie(pr1p, vS)),
                                congruence_terme(vS, pr1p,
                                                 E.produit(var("wdp"), var("wdp")),
                                                 "wdp"))
        return N.loi_deduction(b, composer_egalites(gauche, droite))

    imp_phi = existe_elimination(inner(bodyphi), nphi)
    body = N.modus_ponens(N.assume(bodyS), imp_phi)
    imp_S = existe_elimination(N.loi_deduction(bodyS, body), nS)
    res = N.modus_ponens(decl, imp_S)
    assert res.conclusion == egal(E.dom(pr2p), E.produit(pr1p, pr1p)),         "dom_pr2_egale_carre : forme"
    assert list(res.hypotheses) == [appartient(vp, frame_pair(vE))],         "dom_pr2_egale_carre : hyps"
    return res


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


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151  (les valeurs d'un membre sont dans sa base)
def valeur_dans_pr1(E_set="E", p="pmemb", x="xvp", w="wvp"):
    """🎯 { p ∈ 𝔉(E) } ⊢ (∀x)(∀w)( (x,w) ∈ pr₂(p) ⇒ w ∈ pr₁(p) ).

    Les valeurs de la bijection d'un membre restent dans sa base.  Le corps du
    frame donne `est_surjective(φ,S×S,S)`, c'est-à-dire `image(φ,S×S) = S` ;
    tout antécédent est dans `dom φ = S×S`, donc toute valeur est dans l'image,
    donc dans S.  Pièce de la donnée (10), jumelle de `dom_pr2_egale_carre`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal, pourtout, impl
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie)
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import _frame_membre_t
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere, projection_seconde)
    vE, vp, vx, vw = _t(E_set), _t(p), var(x), var(w)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)
    decl = N.modus_ponens(N.assume(appartient(vp, frame_pair(vE))),
                          equivalence_avant(_frame_membre_t(vE, vp)))
    nS, bodyS = decl.conclusion.lieur, decl.conclusion.sous[0]
    nphi, bodyphi = bodyS.lieur, bodyS.sous[0]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)

    def inner(b):
        hh = N.assume(b)
        vS, vphi = var(nS), var(nphi)
        SxS = E.produit(vS, vS)
        bij = conjonction_elim_droite(hh)
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hh)))
        dom_eq = conjonction_elim_droite(conjonction_elim_gauche(bij))
        surj = conjonction_elim_droite(conjonction_elim_droite(bij))   # image(φ,S×S)=S
        h_c = N.assume(appartient(E.couple(vx, vw), vphi))
        #  x ∈ dom φ = S×S
        car = instancie(instancie(ax_dom, vphi), vx)
        loc = antecedent_consequent(equivalence_avant(car).conclusion)[1]
        x_dom = N.modus_ponens(N.modus_ponens(h_c, N.s5(loc.sous[0], vw, loc.lieur)),
                               equivalence_arriere(car))
        x_SxS = N.modus_ponens(x_dom, equivalence_avant(N.modus_ponens(
            dom_eq, N.s6(E.dom(vphi), SxS, "wvz", appartient(vx, var("wvz"))))))
        #  w ∈ image(φ, S×S) = S
        cim = instancie(instancie(instancie(ax_img, vphi), SxS), vw)
        lim = antecedent_consequent(equivalence_avant(cim).conclusion)[1]
        w_img = N.modus_ponens(N.modus_ponens(conjonction_intro(x_SxS, h_c),
                                              N.s5(lim.sous[0], vx, lim.lieur)),
                               equivalence_arriere(cim))
        w_S = N.modus_ponens(w_img, equivalence_avant(N.modus_ponens(
            surj, N.s6(E.image(vphi, SxS), vS, "wvz", appartient(vw, var("wvz"))))))
        #  transport φ → pr₂p et S → pr₁p
        eq2 = composer_egalites(N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr2(var("wvy")), "wvy")), projection_seconde(nS, nphi))
        eq1 = composer_egalites(N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr1(var("wvy")), "wvy")), projection_premiere(nS, nphi))
        w_pr1 = N.modus_ponens(w_S, equivalence_avant(N.modus_ponens(
            N.modus_ponens(eq1, symetrie(pr1p, vS)),
            N.s6(vS, pr1p, "wvy", appartient(vw, var("wvy"))))))
        sous_c = N.loi_deduction(appartient(E.couple(vx, vw), vphi), w_pr1)
        pont = N.modus_ponens(N.modus_ponens(eq2, symetrie(pr2p, vphi)),
                              N.s6(vphi, pr2p, "wvy", impl(
                                  appartient(E.couple(vx, vw), var("wvy")),
                                  appartient(vw, pr1p))))
        return N.loi_deduction(b, N.modus_ponens(sous_c, equivalence_avant(pont)))

    imp_phi = existe_elimination(inner(bodyphi), nphi)
    body = N.modus_ponens(N.assume(bodyS), imp_phi)
    res = N.modus_ponens(decl, existe_elimination(N.loi_deduction(bodyS, body), nS))
    res = N.generalisation(x, N.generalisation(w, res))
    assert res.conclusion == pourtout(x, pourtout(w, impl(
        appartient(E.couple(vx, vw), pr2p), appartient(vw, pr1p)))),         "valeur_dans_pr1 : forme"
    assert len(res.hypotheses) == 1, "valeur_dans_pr1 : hyps ≠ 1"
    return res


__all__ = ["pr1_inclus_union", "dom_pr2_egale_carre",
           "dom_union_inclus_carre", "valeur_dans_pr1"]
