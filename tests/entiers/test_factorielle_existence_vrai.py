"""Tests — déverrouillage du PIVOT de gluing factorielle + site résiduel exact.

(ensembles_factorielle_existence_vrai)  Aucun théorème factorielle n'est asserté ;
on vérifie (1) que le pivot PARAMÉTRÉ construit sur le graphe τ-lourd factoriel avec
des témoins FRAIS, (2) que la theorie reste 22, (3) que le site résiduel est bien
l'appel à témoins par défaut dans le gluing C60 déposé.
"""
import bourbaki.ensembles.ensembles_abrege as E
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence_vrai import (
    pivot_factorielle_frais_ok, site_residuel_exact,
)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pivot_frais_deverrouille():
    r = pivot_factorielle_frais_ok()
    # F bake bien les binders cardinaux interdits du gluing
    assert {"u", "up", "v", "y", "z"} <= set(r["binders_F"])
    # build par défaut : capture attendue ; build frais : OK et non vacuous
    assert "capture" in r["defaut"]
    assert r["frais_ok"] is True
    assert r["frais_concl_tag"] == "non"      # est_fonctionnel = ¬(...)-formé en tête
    assert r["frais_nb_hyps"] == 3
    assert r["non_vacuous"] is True


def test_site_residuel_exact():
    r = site_residuel_exact()
    assert "capture" in r["statut"]
    # site résiduel = appel pivot à témoins PAR DÉFAUT dans le gluing C60 déposé
    assert r["site_pivot_defaut"][0] == "ensembles_c60_existence_close.py"
    assert r["site_pivot_defaut"][2] == "extension_un_pas_fonctionnelle"


def test_theorie_toujours_22_apres():
    pivot_factorielle_frais_ok()
    assert len(E.theorie_ensembles().axiomes) == 22
