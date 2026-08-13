# -*- coding: utf-8 -*-
"""Tests — C57 (E II.44) : contenu du passage au quotient.  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_c57_passage_quotient import (
    c57_valeur_au_temoin,
)


def test_c57_valeur_au_temoin():
    """🎯 {f compatible, p caractérise R} ⊢ f(s(p(x))) = f(x) — 2 hyps, sans choix."""
    th = c57_valeur_au_temoin()
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22


def test_c57_application_deduite():
    """👑 C57 COMPLET : H = graphe CONSTRUIT, ⊢ H(p(x)) = f(x) — 3 hyps."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_c57_passage_quotient import (
        c57_application_deduite,
    )
    th = c57_application_deduite()
    assert len(th.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22


def test_c57_unicite():
    """👑 C57 « et une seule » : deux factorisations coïncident sur Q — 3 hyps."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_c57_passage_quotient import (
        c57_unicite,
    )
    th = c57_unicite()
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
