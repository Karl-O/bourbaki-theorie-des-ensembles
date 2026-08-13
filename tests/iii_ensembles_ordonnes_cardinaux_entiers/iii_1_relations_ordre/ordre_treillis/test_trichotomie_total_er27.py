# -*- coding: utf-8 -*-
"""Test Résumé E.R.27 item 4 — trichotomie exclusive d'un ordre total."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_trichotomie_total_er27 import (
    trichotomie_totale, enonce_trichotomie_totale)


def test_trichotomie_totale():
    """⊢ totalement_ordonne(G,E) ⇒ (∀u,v∈E)(trichotomie exclusive) — CLOS, 0 hyp."""
    r = trichotomie_totale()
    assert r.conclusion == enonce_trichotomie_totale()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    trichotomie_totale()
    assert len(E.theorie_ensembles().axiomes) == 22
