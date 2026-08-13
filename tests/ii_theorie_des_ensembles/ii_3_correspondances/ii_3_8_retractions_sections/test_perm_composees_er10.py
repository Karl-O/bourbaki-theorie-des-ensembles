# -*- coding: utf-8 -*-
"""Test E.R.10-11 item 12 (n°79) — g∘f perm E, f∘g perm F ⇒ f,g bijectives."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_perm_composees_er10 import (
    perm_composees_bijectives, enonce_perm_composees_bijectives)


def test_perm_composees_bijectives():
    """⊢ (g∘f perm E et f∘g perm F) ⇒ (f et g bijectives) — CLOS, 0 hyp."""
    r = perm_composees_bijectives()
    assert r.conclusion == enonce_perm_composees_bijectives()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    perm_composees_bijectives()
    assert len(E.theorie_ensembles().axiomes) == 22
