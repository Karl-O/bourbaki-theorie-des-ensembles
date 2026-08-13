# -*- coding: utf-8 -*-
"""Tests — témoin cofinal canonique (chaînon de la Prop. 3).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
    temoin_cofinal,
)


def test_temoin_cofinal():
    """🎯 {J cofinale, α∈I} ⊢ β(α)∈J et α≤β(α) — SANS axiome du choix, 2 hyps."""
    th = temoin_cofinal()
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_temoin_majorant_commun():
    """👑 Le témoin CANONIQUE du majorant commun — pendant de `temoin_cofinal`
    pour la FILTRANCE : un majorant de DEUX indices au lieu d'un.

    C'est le δ que Bourbaki appelle « une valeur commune ν ≥ λ et ν ≥ μ »
    (E III.55, démonstration de la Prop. 3), et que `prolongement_bien_defini`
    laissait en variable LIBRE.  Construction par τ, donc toujours sans axiome
    du choix."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, appartient,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
        nu_majorant_commun, temoin_majorant_commun, _R_gleq,
    )
    R = _R_gleq()
    th = temoin_majorant_commun()
    nu = nu_majorant_commun(var("J"), var("ai"), var("bi"))
    assert th.conclusion == et(et(appartient(nu, var("J")), R(var("ai"), nu)),
                               R(var("bi"), nu))
    assert len(th.hypotheses) == 3
    # les deux appartenances sont bien celles des DEUX indices
    assert appartient(var("ai"), var("J")) in th.hypotheses
    assert appartient(var("bi"), var("J")) in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
