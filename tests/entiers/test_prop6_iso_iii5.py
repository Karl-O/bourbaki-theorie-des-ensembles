"""Tests §III.5 Prop 6 (E III.38) — iso existence, route Bourbaki Th3 + Prop1.

Vérifie la VÉRITÉ HONNÊTE de l'assemblage :
  • conclusion == cible (sont_isomorphes_ordre_canon(E,F,R,Rp)) ;
  • EXACTEMENT 4 hypothèses HONNÊTES survivantes (bo,bo,Card=,résidu) ;
  • NON vacueux (conclusion ∉ hypothèses) ;
  • theorie=22 (noyau intact).
"""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage import ensembles_prop6_iso_iii5 as P
from bourbaki.ensembles import ensembles_abrege as E


def test_prop6_iso_existe_conclusion_est_cible():
    th = P.prop6_iso_existe()
    assert th.conclusion == P.prop6_iso_existe_cible()


def test_prop6_iso_existe_hypotheses_exactes():
    th = P.prop6_iso_existe()
    exp = set(P.prop6_iso_existe_hypotheses())
    assert set(th.hypotheses) == exp
    assert len(exp) == 4


def test_prop6_iso_existe_non_vacueux():
    th = P.prop6_iso_existe()
    # la conclusion n'est AUCUNE hypothèse : séquent NON vacueux.
    assert th.conclusion not in set(th.hypotheses)


def test_theorie_intacte_22():
    P.prop6_iso_existe()
    assert len(E.theorie_ensembles().axiomes) == 22
