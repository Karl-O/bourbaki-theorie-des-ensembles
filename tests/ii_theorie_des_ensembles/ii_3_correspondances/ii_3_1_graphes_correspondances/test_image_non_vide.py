# -*- coding: utf-8 -*-
"""Tests E.R.8 item 5b — X≠∅ ⇔ f⟨X⟩≠∅ (1 hypothèse honnête X ⊂ dom f)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_image_non_vide import (
    image_non_vide, image_non_vide_enonce)


def test_clos_une_hypothese():
    th = image_non_vide()
    assert th.conclusion == image_non_vide_enonce()
    assert th.hypotheses == frozenset({inclus(var("X"), E.dom(var("f")))})


def test_autres_lettres():
    th = image_non_vide("A", "g")
    assert th.conclusion == image_non_vide_enonce("A", "g")
    assert len(th.hypotheses) == 1
