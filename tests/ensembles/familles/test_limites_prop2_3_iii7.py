"""Tests — §III.7.2 Proposition 2 (injectivité de la limite d'applications).

Les théorèmes sont CONDITIONNELS (hypothèses HONNÊTES portées dans le séquent :
injectivité-famille des u_α, appartenance des projections, y,z∈lim←, u(y)=u(z),
y,z∈∏ + graphes).  On vérifie : ils se construisent (noyau accepte chaque pas), la
conclusion est la bonne, la conclusion n'est PAS une hypothèse (anti-tautologie), et
theorie_ensembles() reste à 22.
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_limites_prop2_3_iii7 as P


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_lim_u_coordonnee_construit():
    th = P.lim_u_coordonnee()
    assert th.conclusion is not None


def test_lim_u_coordonnee_egale_construit():
    th = P.lim_u_coordonnee_egale()
    assert th.conclusion is not None


def test_lim_u_projection_egale_construit():
    th = P.lim_u_projection_egale()
    assert th.conclusion is not None


def test_prop2_injectivite_conclusion_y_egal_z():
    th = P.prop2_injectivite()
    # conclusion = (y = z)  avec y='yy', z='zz'
    assert th.conclusion == egal(var("yy"), var("zz"))
    # anti-tautologie : la conclusion n'est pas une hypothèse
    assert th.conclusion not in th.hypotheses
    # hypothèses HONNÊTES (non vides, mais finies et explicites)
    assert len(th.hypotheses) == 9


def test_theorie_toujours_22_apres():
    P.prop2_injectivite()
    assert len(E.theorie_ensembles().axiomes) == 22
