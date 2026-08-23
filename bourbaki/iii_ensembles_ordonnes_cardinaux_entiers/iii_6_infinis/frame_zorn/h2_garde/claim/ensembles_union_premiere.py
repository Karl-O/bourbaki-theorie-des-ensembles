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


__all__ = ["pr1_inclus_union", "dom_pr2_egale_carre"]
