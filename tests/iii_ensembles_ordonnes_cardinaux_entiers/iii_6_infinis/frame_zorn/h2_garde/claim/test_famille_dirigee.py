# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_famille_dirigee.py — données 4 et 2 du recollement."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    famille_dirigee, injectif_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_famille_dirigee import (
    famille_dirigee_de_chaine, union_dirigee_injective,
)


def test_famille_dirigee_de_chaine():
    """🎯 { chaîne } ⊢ famille_dirigee( 𝔇(C) )   (donnée 4/11).

    La direction traduit, au niveau des graphes, que C est une chaîne : deux
    membres sont pr₂(u) et pr₂(v) pour u,v comparables dans Γ𝔉, qui ordonne
    par extension — le plus grand sert de majorant."""
    D = famille_de_chaine(var("Cch"))
    t = famille_dirigee_de_chaine()
    assert t.conclusion == famille_dirigee(D, "pdir", "qdir", "rdir")
    assert len(t.hypotheses) == 1, "hyps : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"


def test_union_dirigee_injective():
    """🎯 { chaîne } ⊢ injectif_graphe( ⋃𝔇(C) )   (donnée 2/11).

    Tombe des données (4) et (5) par `union_famille_injective`, déjà dans le
    dépôt : c'est le rendement du travail de cartographie (R-13)."""
    D = famille_de_chaine(var("Cch"))
    t = union_dirigee_injective()
    assert t.conclusion == injectif_graphe(union_famille(D))
    assert len(t.hypotheses) == 1, "hyps : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_famille_compatible_de_chaine():
    """🎯 { chaîne } ⊢ famille_compatible( 𝔇(C) )   (donnée 3/11).

    Deux membres emboîtés : les deux couples atterrissent dans le plus grand,
    qui est une FONCTION — d'où b=c.  L'asymétrie de construction (c'est le
    couple du PETIT qu'on transporte) est traitée branche par branche."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
        famille_compatible,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_famille_dirigee import (
        famille_compatible_de_chaine,
    )
    D = famille_de_chaine(var("Cch"))
    t = famille_compatible_de_chaine()
    assert t.conclusion == famille_compatible(D, "pcf", "qcf", "acf", "bcf", "ccf")
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"


def test_union_compatible_fonctionnelle():
    """🎯 { chaîne } ⊢ est_fonctionnel( ⋃𝔇(C) )   (donnée 6/11)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_famille_dirigee import (
        union_compatible_fonctionnelle,
    )
    D = famille_de_chaine(var("Cch"))
    t = union_compatible_fonctionnelle()
    assert t.conclusion == E.est_fonctionnel(union_famille(D))
    assert len(t.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22
