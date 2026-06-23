"""Tests — EXISTENCE factorielle : statut HONNÊTE (rule OK, essais bloqués par τ-capture).

On vérifie les FAITS honnêtes (rien postulé) :
  • `regle_factorielle()` est un TERME bien formé (callable Terme→Terme), index-aware ;
  • `factorielle_essais_existe()` est BLOQUÉ par τ-capture du gluing déposé (O3) — il
    LÈVE l'erreur de capture du noyau (preuve que l'obstruction est réelle) ;
  • theorie_ensembles() = 22 (noyau intact).
"""
import pytest

from bourbaki.logique.formule import var, Terme
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
    regle_factorielle, factorielle_essais_existe,
)


def test_theorie_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_regle_factorielle_est_terme():
    """La règle factorielle index-aware est un terme bien formé (callable Terme→Terme)."""
    T = regle_factorielle()
    out = T(var("u0"))
    assert isinstance(out, Terme)
    # terme τ (la règle T{u} = τy(...))
    assert out.tag == "tau"


def test_essais_bloques_par_tau_capture():
    """OBSTRUCTION O3 : la règle factorielle (a=1 τ-terme + sortie lisant u) est REJETÉE
    par τ-capture dans le gluing déposé — l'appel lève l'erreur de capture du noyau.

    C'est la PREUVE honnête que l'existence des essais factoriels n'est PAS atteignable
    via le C62/gluing déposé sans modifier le noyau.  Rien n'est postulé."""
    with pytest.raises(ValueError, match="mineure"):
        factorielle_essais_existe()
