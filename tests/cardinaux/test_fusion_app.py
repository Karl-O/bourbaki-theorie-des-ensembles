"""Tests — §III.2 coincidence_point_app : consommation de coincidence_univ_app (CLOSE)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_fusion_app import (
    coincidence_point_app, coincidence_point_app_cible,
)


def test_theorie_intangible():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_coincidence_point_app_conclusion():
    """φ_petit(p)=φ_grand(p) DÉRIVÉE (pas postulée) via coincidence_univ_app CLOSE."""
    t = coincidence_point_app()
    assert t.conclusion == coincidence_point_app_cible()
    assert not t.est_clos                       # conditionnel à la prémisse-applications
    assert t.conclusion not in set(t.hypotheses)  # NON vacueux
    assert len(E.theorie_ensembles().axiomes) == 22


def test_coincidence_point_app_hyps_applications():
    """Les hypothèses sont la prémisse-applications (14, BON ORDRE AMBIANT VRAI) + p∈S_petit
    = 15, toutes honnêtes.  Les bons ordres sur SEGMENTS PROPRES (bo(R,Sp), bo(R,Sg),
    bo(R',Tp), bo(R',image)) ont disparu, re-basés sur bo(R,E)+bo(R',F) ambiants VRAIS
    (inclus(Sp,E) fournie par est_segment) → prémisse DISCHARGEABLE dans la fusion."""
    t = coincidence_point_app()
    assert len(t.hypotheses) == 15
