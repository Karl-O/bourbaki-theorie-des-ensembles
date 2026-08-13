#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test du catalogue algébrique : chaque lemme se RE-CERTIFIE au noyau (clos + cible + 22 ax.)."""
import sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lemmes_algebre as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_tous_les_lemmes_algebre_se_recertifient():
    assert M.IDS, "catalogue vide"
    for k in M.IDS:
        t = getattr(M, "lemme_alg_%d" % k)()
        assert type(t).__name__ == "Theoreme" and t.est_clos
        assert repr(t.conclusion) == M._CIBLES[k]
    assert len(theorie_ensembles().axiomes) == 22
