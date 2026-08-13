"""Test — PROP 10 CLOSE : a^(b·c)=(a^b)^c (Card(𝓕(B×C;A))=Card(𝓕(C;𝓕(B;A)))).

⚠️ LENT (~15 min : construit inf_egal_curry + inf_egal_uncurry, τ imbriqués 2 niveaux).
"""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop10_currying.ensembles_prop10_final_close import prop10_close
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop10_currying.ensembles_prop10_currying import cible_prop10
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def test_prop10_close_inconditionnel():
    th = prop10_close()
    assert th.est_clos                       # INCONDITIONNEL (0 hypothèse)
    assert len(list(th.hypotheses)) == 0
    # conclusion == cible Bourbaki a^(b·c)=(a^b)^c
    assert th.conclusion == cible_prop10(var("A"), var("B"), var("C"))
    assert th.conclusion.tag == "="
    # theorie intangible
    assert len(E.theorie_ensembles().axiomes) == 22
