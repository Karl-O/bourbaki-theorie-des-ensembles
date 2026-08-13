# -*- coding: utf-8 -*-
"""Tests — « tout point de lim← est un graphe » (§III.7.1).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_lim_graphe import (
    point_limite_est_graphe, limite_points_graphes,
)


def test_point_limite_est_graphe():
    """🎯 Le lemme n'AJOUTE aucune hypothèse : il consomme « p ∈ lim← » seule.

    C'est là tout son intérêt — chez le consommateur, l'appartenance à la limite
    est déjà présente, donc la condition de graphe devient gratuite."""
    th = point_limite_est_graphe()
    assert th.conclusion == E.est_un_graphe(var("p"))
    assert th.hypotheses == frozenset(
        {appartient(var("p"), L.lim_proj(var("E"), var("f")))})
    assert len(E.theorie_ensembles().axiomes) == 22


def test_point_limite_est_graphe_sur_terme_quelconque():
    """Le lemme s'applique à un point NOMMÉ arbitrairement (ici « xx »)."""
    vx = var("xx")
    h = N.assume(appartient(vx, L.lim_proj(var("E"), var("f"))))
    th = point_limite_est_graphe(terme=vx, preuve_in_lim=h)
    assert th.conclusion == E.est_un_graphe(vx)
    assert th.hypotheses == h.hypotheses


def test_limite_points_graphes_close():
    """👑 Forme universelle CLOSE : (∀p)(p ∈ lim← ⇒ est_un_graphe p), 0 hypothèse.

    Aucune hypothèse : le fait est un théorème du dépôt, pas une supposition —
    conséquence de la réparation de l'axiome du produit (`produit_graphe`)."""
    th = limite_points_graphes()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


def test_liant_capture_detectee():
    """⚠️ Un point nommé « z » est CAPTURÉ — et le lemme le DÉTECTE.

    `est_un_graphe(g)` abrège (∀z)(z∈g ⇒ z est un couple) : elle lie « z ».
    Sur un point nommé « z », l'énoncé construit dirait (∀z)(z∈z ⇒ …), qui n'est
    pas ce qu'on veut ; l'assertion de conclusion du lemme le refuse.  Ce test
    fige à la fois le piège et le garde-fou — le nom « p » n'est pas cosmétique."""
    import pytest
    with pytest.raises(AssertionError):
        point_limite_est_graphe(terme=var("z"))
