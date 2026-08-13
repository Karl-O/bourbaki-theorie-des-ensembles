# -*- coding: utf-8 -*-
"""Tests — bonne définition du prolongement cofinal (Prop. 3).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
    prolongement_bien_defini,
)


def test_prolongement_bien_defini():
    """👑 f_αβ(x_β) = f_αγ(x_γ) : le prolongement ne dépend pas du majorant choisi."""
    th = prolongement_bien_defini()
    assert len(th.hypotheses) == 13
    assert len(E.theorie_ensembles().axiomes) == 22


def test_porter_aux_termes():
    """🔧 L'outil de portage noms→termes : porte la bonne définition aux témoins.

    Vérifie qu'il découvre seul les hypothèses portant les noms, les décharge,
    substitue, et les ré-assume — sans perdre ni inventer d'hypothèse."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
        porter_aux_termes,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
        beta_cofinal,
    )
    base = prolongement_bien_defini()
    porte = porter_aux_termes(base, {"b": beta_cofinal(var("J"), var("a")),
                                     "g": beta_cofinal(var("J"), var("ap"))})
    assert len(porte.hypotheses) == len(base.hypotheses)
    assert porte.conclusion != base.conclusion


def test_prolongement_coherent():
    """👑 x̃ satisfait la relation (1) : le prolongement est DANS lim←_I — 18 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
        prolongement_coherent,
    )
    assert len(prolongement_coherent().hypotheses) == 18


def test_prolongement_restitue():
    """👑 x̃_α = x_α sur J : l'antécédent construit se projette sur x — 2 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
        prolongement_restitue,
    )
    th = prolongement_restitue()
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prolongement_coherent_universel():
    """👑 x̃ vérifie la relation (1) pour TOUT couple α≤α' — 4 hyps de contexte."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
        prolongement_coherent_universel,
    )
    th = prolongement_coherent_universel()
    assert len(th.hypotheses) == 4
    assert all("a" not in libres_f(h) and "ap" not in libres_f(h)
               for h in th.hypotheses)
