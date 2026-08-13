#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test du catalogue de lemmes auto-decouverts : chaque lemme se RE-CERTIFIE au noyau."""
import sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lemmes_decouverts as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_tous_les_lemmes_se_recertifient():
    assert M.IDS, "catalogue vide"
    for k in M.IDS:
        t = getattr(M, "lemme_%d" % k)()
        assert type(t).__name__ == "Theoreme"
        assert t.est_clos                              # clos = 0 hypothese
        assert repr(t.conclusion) == M._CIBLES[k]      # bien le theoreme attendu
    assert len(theorie_ensembles().axiomes) == 22      # frontiere intacte
