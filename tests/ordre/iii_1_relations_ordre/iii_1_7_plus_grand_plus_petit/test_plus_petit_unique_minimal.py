"""Tests — §III.1.7 (Remarque) : le plus petit élément est l'unique élément minimal.

Vérifie pour `plus_petit_est_unique_minimal` :
  • conclusion == cible  (egal(m,a), via == puis alpha_egal) ;
  • hypothèses == exactement { plus_petit_element(G,E,a), element_minimal(G,E,m) }
    (jamais la conclusion en hypothèse, aucune antisymétrie parasite) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, alpha_egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    plus_petit_element, element_minimal,
)
from bourbaki.ordre.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_plus_petit_unique_minimal import (
    plus_petit_est_unique_minimal, cible,
)

G, E_set, a, m = var("G"), var("E"), var("a"), var("m")


def _thm():
    return plus_petit_est_unique_minimal(G, E_set, a, m)


def test_conclusion_egale_cible():
    thm = _thm()
    but = cible(G, E_set, a, m)
    assert thm.conclusion == but
    assert alpha_egal(thm.conclusion, but)


def test_hypotheses_exactes():
    thm = _thm()
    attendu = {plus_petit_element(G, E_set, a), element_minimal(G, E_set, m)}
    assert thm.hypotheses == attendu
    # honnêteté de l'énoncé : la conclusion n'est jamais glissée en hypothèse
    assert cible(G, E_set, a, m) not in thm.hypotheses
    assert not thm.est_clos  # deux hypothèses non déchargées


def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
