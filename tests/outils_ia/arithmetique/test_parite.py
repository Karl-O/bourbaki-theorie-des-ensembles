"""Réfutation de parité — ⊢ ¬(∃m)( N(i) = m+m ) pour i impair.

Le quantificateur porte sur des ensembles QUELCONQUES (aucune garde de finitude
sur m) : c'est bien « N(i) n'est pas pair » au sens de `goldbach()`, pas une
version affaiblie.  Trois gardes : clôture et conformité, anti-vacuité (la
parité est PROUVABLE quand elle a lieu), et non-universalité (sur un i PAIR la
recette meurt dans l'ARITHMÉTIQUE, pas dans un assert cosmétique).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from outils_ia.arithmetique.calcul_num import somme_num
from outils_ia.arithmetique.machine_num import NUM
from outils_ia.arithmetique.parite import K_PAIR, corps_pair, est_pair, non_pair

mp = N.modus_ponens


def test_les_impairs_ne_sont_pas_pairs():
    """⊢ ¬( pair(N(i)) ) pour i = 3, 5, 7 — clos, conforme à la formule de goldbach()."""
    for i in (3, 5, 7):
        th = non_pair(i)
        assert th.est_clos and not th.hypotheses
        assert th.conclusion == non(est_pair(NUM(i)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_anti_vacuite_la_parite_est_prouvable():
    """⊢ pair( N(6) ) — témoin N(3).  Sans ce contrôle, les négations pourraient
    nier un prédicat vide."""
    s33 = somme_cardinale_binaire(NUM(3), NUM(3))
    eq = mp(somme_num(3, 3), symetrie(s33, NUM(6)))       # N(6) = N(3)+N(3)
    th = mp(eq, N.s5(corps_pair(NUM(6), K_PAIR), NUM(3), K_PAIR))
    assert th.est_clos and th.conclusion == est_pair(NUM(6))


def test_non_universalite_un_pair_est_refuse():
    """🔴 LE CONTRÔLE QUI COMPTE.  La garde refuse i pair ; garde DÉSACTIVÉE, la
    machine doit mourir dans l'ARITHMÉTIQUE (il faudrait ¬( N(6) = N(6) )) — et
    un impair doit continuer de clore, sinon la désactivation a tout cassé."""
    with pytest.raises(AssertionError, match="IMPAIR attendu"):
        non_pair(6)                        # la garde Python, qui NE prouve rien
    with pytest.raises(AssertionError):
        non_pair(6, garde=False)           # l'arithmétique elle-même
    assert non_pair(5, garde=False).est_clos
