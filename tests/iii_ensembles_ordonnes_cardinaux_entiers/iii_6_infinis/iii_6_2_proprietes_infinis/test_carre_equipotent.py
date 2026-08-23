# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_carre_equipotent.py.

Le pont du Théorème 2 : du niveau CARDINAL (Card A · Card A = Card A) au
niveau ENSEMBLE (Eq(A×A, A)), qui est la forme réclamée par le Corollaire 1.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_a_puissance_n_er import (
    hyp_carre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_carre_equipotent import (
    carre_du_produit, carre_equipotent_sous_hessenberg,
)


def test_carre_du_produit_est_clos():
    """⊢ Card(A×A) = Card A · Card A, sans aucune hypothèse.   [~1 s]"""
    vA = var("A")
    cA = cardinal(vA)
    t = carre_du_produit("A")
    assert t.conclusion == egal(cardinal(E.produit(vA, vA)),
                                produit_cardinal_binaire(cA, cA))
    assert not t.hypotheses, "doit être CLOS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_carre_equipotent_donne_exactement_hyp_carre():
    """🎯 Le pont conclut l'hypothèse EXACTE du Corollaire 1.   [~2 s]

    C'est le point du module : `hyp_carre` annonçait une décharge « via
    hessenberg_0hyp », fonction jamais écrite.  L'égalité de formules ci-dessous
    est ce qui rend la décharge possible — une ressemblance ne suffirait pas."""
    vA = var("A")
    t = carre_equipotent_sous_hessenberg("A")
    assert t.conclusion == hyp_carre("A"), \
        "la conclusion doit être IDENTIQUE à hyp_carre, pas seulement semblable"
    assert set(t.hypotheses) == {enonce_hessenberg("A"), est_infini(cardinal(vA))}, \
        "seuls le Théorème 2 et son antécédent doivent rester"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
