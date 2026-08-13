"""Tests §III.7.2 — UNICITÉ du cône de la limite projective (Prop. 1, « et une seule »).

Vérifie que cone_unicite conclut EXACTEMENT u=u' sous les hypothèses HONNÊTES
(u,u'∈𝓕(F;lim←) ; mêmes coordonnées f_α(u(y))=f_α(u'(y)) ; images des graphes),
non vacuous (u=u' ∉ hypothèses).  Vérifie aussi que le lemme PLAIN
coords_donnent_projections est CLOS.  theorie_ensembles() reste à 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_cone_unicite as CU


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_coords_donnent_projections_close():
    # lemme PLAIN (z,z' variables simples) : mêmes coordonnées ⇒ mêmes projections
    lemme = CU.coords_donnent_projections("E", "f", _leq(), "I", "zp1", "zp2", "a")
    assert lemme.est_clos
    assert len(lemme.hypotheses) == 0


def test_cone_unicite_conclusion_exacte():
    th = CU.cone_unicite("E", "f", "u", "up")
    assert th.conclusion == egal(var("u"), var("up"))


def test_cone_unicite_hypotheses_honnetes():
    """EXACTEMENT 3 hypothèses honnêtes — la prémisse « images graphes » a sauté.

    Elle était la 4ᵉ ; comme u(y), u'(y) sont établis dans lim← au cours de la
    preuve, leur caractère de graphe s'en déduit (`point_limite_est_graphe`,
    §7.1) au lieu d'être supposé."""
    leq = _leq()
    th = CU.cone_unicite("E", "f", "u", "up")
    H = th.hypotheses
    LIM = L.lim_proj(var("E"), var("f"))
    h_coord = CU.cone_coordonnees_egales("E", "f", "u", "up", leq, "I", "F", "a", "yy")
    h_u = appartient(var("u"), E.applications(var("F"), LIM))
    h_up = appartient(var("up"), E.applications(var("F"), LIM))
    assert set(H) == {h_coord, h_u, h_up}
    # la prémisse historique n'est plus consommée
    assert CU.cone_images_graphes("u", "up", "F", "yy") not in H


def test_cone_unicite_non_vacuous():
    th = CU.cone_unicite("E", "f", "u", "up")
    # la conclusion u=u' ne figure PAS dans les hypothèses
    assert egal(var("u"), var("up")) not in th.hypotheses
