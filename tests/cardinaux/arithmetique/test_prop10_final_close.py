"""Test — PROP 10 CLOSE : a^(b·c)=(a^b)^c (Card(𝓕(B×C;A))=Card(𝓕(C;𝓕(B;A)))).

⚠️ LENT (~15 min : construit inf_egal_curry + inf_egal_uncurry, τ imbriqués 2 niveaux).
"""
from bourbaki.cardinaux.arithmetique.ensembles_prop10_final_close import prop10_close
from bourbaki.cardinaux.arithmetique.ensembles_prop10_currying import cible_prop10
from bourbaki.logique.formule import var
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E


def test_prop10_close_inconditionnel():
    th = prop10_close()
    assert th.est_clos                       # INCONDITIONNEL (0 hypothèse)
    assert len(list(th.hypotheses)) == 0
    # conclusion == cible Bourbaki a^(b·c)=(a^b)^c
    assert th.conclusion == cible_prop10(var("A"), var("B"), var("C"))
    assert th.conclusion.tag == "="
    # theorie intangible
    assert len(E.theorie_ensembles().axiomes) == 22
