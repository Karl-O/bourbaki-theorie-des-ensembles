"""Primalité effective — et la garde de fidélité qui la rend honnête.

Le test central n'est pas « le théorème est clos » : c'est que sa conclusion est
ÉGALE à `goldbach.est_premier(N(p))` reconstruit depuis le module d'énoncé.  Sans
cette comparaison, rien n'empêcherait de démontrer une variante commode.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    UN,
)
from outils_ia.arithmetique.machine_num import NUM
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures.primalite import est_premier_num, obstruction, pont_un


def test_le_piege_de_fidelite_est_reel():
    """🔴 N(1) et le « 1 » de est_premier sont deux TERMES DIFFÉRENTS.

    C'est ce qui rend le pont nécessaire.  Si cette assertion tombait un jour,
    ce serait que quelqu'un a aligné l'ÉNONCÉ sur la preuve — la faute inverse,
    et la pire : elle rend le théorème vrai et sans valeur."""
    assert NUM(1) == UN
    assert NUM(1) != GB.un(), (
        "N(1) et goldbach.un() sont devenus le même terme : `goldbach.est_premier` "
        "a-t-il été réécrit pour coller aux numéraux ?")
    pont = pont_un()
    assert pont.est_clos and not pont.hypotheses


def test_primalite_de_sept():
    """Le premier cas où l'arithmétique porte vraiment (5 non-divisibilités)."""
    th = est_premier_num(7)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == GB.est_premier(NUM(7)), (
        "la conclusion n'est pas l'énoncé produit par goldbach.py")
    assert len(E.theorie_ensembles().axiomes) == 22


def test_primalite_de_plusieurs_premiers():
    """La machine n'est pas taillée pour 7."""
    for p in (2, 3, 5, 11, 13):
        th = est_premier_num(p)
        assert th.est_clos and th.conclusion == GB.est_premier(NUM(p))


def test_les_composes_sont_refuses():
    """Une machine qui prouverait la primalité de 9 ne vaudrait rien."""
    assert obstruction(7) == [] and obstruction(9) == [3]
    assert obstruction(15) == [3, 5]
    for p in (4, 9, 15, 25):
        with pytest.raises(ValueError, match="OBSTRUCTION"):
            est_premier_num(p)


def test_sur_un_compose_c_est_l_arithmetique_qui_bloque():
    """🔴 LE CONTRÔLE QUI COMPTE — gardes désactivées À TOUS LES ÉTAGES.

    Première version de ce contrôle : FAUSSE.  `garde` n'était pas propagé
    jusqu'à `non_divise`, et l'échec venait donc encore d'une garde Python.
    Ici l'échec doit être une AssertionError de `ne_num` : il faudrait
    ¬( N(9) = N(9) ).  Et p = 7 doit continuer de clore, sinon la désactivation
    aurait simplement tout cassé."""
    for p in (4, 9, 15):
        with pytest.raises(AssertionError):
            est_premier_num(p, garde=False)
    assert est_premier_num(7, garde=False).est_clos
