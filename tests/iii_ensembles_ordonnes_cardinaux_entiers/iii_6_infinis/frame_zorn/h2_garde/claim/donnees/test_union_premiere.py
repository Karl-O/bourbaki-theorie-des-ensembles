# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_union_premiere.py — le pont membre → ⋃S(C)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
    pr1_inclus_union,
)


def test_pr1_inclus_union():
    """🎯 { u ∈ C } ⊢ pr₁(u) ⊂ ⋃S(C).

    Brique commune aux quatre dernières données du recollement — les seules
    qui mêlent la famille 𝔇 et la réunion US.  Emploie `membre_union_premiere`
    dans le sens ARRIÈRE : S5 introduit l'existentielle au témoin u."""
    vC, vu = var("Cch"), var("umem")
    t = pr1_inclus_union()
    assert t.conclusion == inclus(E.pr1(vu), union_premiere(vC), "xup")
    assert list(t.hypotheses) == [appartient(vu, vC)]
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_dom_pr2_egale_carre():
    """🎯 { p ∈ 𝔉(E) } ⊢ dom( pr₂(p) ) = pr₁(p) × pr₁(p).

    Situe le domaine de chaque membre dans un CARRÉ — seule forme que
    `produit_monotone_carre` sait faire croître, donc la pièce qui manquait
    à la donnée (9)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
        dom_pr2_egale_carre,
    )
    vp = var("pmemb")
    t = dom_pr2_egale_carre()
    assert t.conclusion == egal(E.dom(E.pr2(vp)), E.produit(E.pr1(vp), E.pr1(vp)))
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_dom_union_inclus_carre():
    """🎯 { chaîne } ⊢ dom(⋃𝔇(C)) ⊂ US×US   (donnée 9/11)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
        union_famille,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
        famille_de_chaine,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_dom_union import (
        dom_union_inclus_carre,
    )
    vC = var("Cch")
    U, US = union_famille(famille_de_chaine(vC)), union_premiere(vC)
    t = dom_union_inclus_carre()
    assert t.conclusion == inclus(E.dom(U), E.produit(US, US), "zdu")
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_dans_pr1():
    """🎯 { p ∈ 𝔉(E) } ⊢ (∀x)(∀w)( (x,w) ∈ pr₂(p) ⇒ w ∈ pr₁(p) ).

    Les valeurs de la bijection d'un membre restent dans sa base : pièce de la
    donnée (10), jumelle de `dom_pr2_egale_carre` côté image."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient, pourtout, impl,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
        valeur_dans_pr1,
    )
    vp, vx, vw = var("pmemb"), var("xvp"), var("wvp")
    t = valeur_dans_pr1()
    assert t.conclusion == pourtout("xvp", pourtout("wvp", impl(
        appartient(E.couple(vx, vw), E.pr2(vp)), appartient(vw, E.pr1(vp)))))
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_atteinte():
    """🎯 { p ∈ 𝔉(E) } ⊢ (∀w)( w ∈ pr₁(p) ⇒ (∃a)( (a,w) ∈ pr₂(p) ) ).

    Réciproque de `valeur_dans_pr1` : toute la base d'un membre est ATTEINTE,
    c'est la surjectivité lue dans l'autre sens.  Pièce de la donnée (7)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient, pourtout, impl, existe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
        valeur_atteinte,
    )
    vp, vw = var("pmemb"), var("wva")
    t = valeur_atteinte()
    assert t.conclusion == pourtout("wva", impl(
        appartient(vw, E.pr1(vp)),
        existe("ava", appartient(E.couple(var("ava"), vw), E.pr2(vp)))))
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
