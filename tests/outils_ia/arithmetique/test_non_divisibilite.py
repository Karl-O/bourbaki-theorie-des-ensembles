"""Non-divisibilité effective — le premier calcul arithmétique réel du corpus.

Ces tests protègent trois choses, et la troisième est la plus importante :
  · que les théorèmes restent CLOS et conformes à la cible du dépôt ;
  · que le prédicat n'est pas vide (anti-vacuité) ;
  · qu'une recette qui réussirait PARTOUT serait détectée (non-universalité), et
    que le refus vient du NOYAU, pas d'une garde Python.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)
from outils_ia.arithmetique.machine_num import NUM, ne_num, le_num
from outils_ia.arithmetique.calcul_num import somme_num, produit_num
from outils_ia.arithmetique.non_divisibilite import non_divise, divise_positif, obstruction


def _numeral_a_la_main(k):
    """successeur^k(Card ∅), rebâti sans le cache : on ne croit pas le producteur."""
    t = ZERO
    for _ in range(k):
        t = successeur(t)
    return t


def test_le_calcul_porte_vraiment():
    """⊢ N(m)+N(n) = N(m+n) et ⊢ N(m)·N(n) = N(m·n) — la brique arithmétique."""
    assert somme_num(3, 4).conclusion.termes[1] == _numeral_a_la_main(7)
    assert produit_num(2, 3).conclusion.termes[1] == _numeral_a_la_main(6)
    assert produit_num(3, 0).est_clos and le_num(2, 5).est_clos
    assert ne_num(2, 5).conclusion == non(egal(NUM(2), NUM(5)))


def test_les_cinq_de_sept():
    """Le cas qui a motivé le module : 2, 3, 4, 5, 6 ne divisent pas 7.

    Pour p = 2 la primalité ne demandait aucune arithmétique (l'énumération
    donnait {0,1,2}, dont {1,2} autorisés).  Ici chaque cas est un vrai calcul."""
    for i in (2, 3, 4, 5, 6):
        th = non_divise(i, 7)
        assert th.est_clos and not th.hypotheses
        assert th.conclusion == non(divise_propre(_numeral_a_la_main(i),
                                                  _numeral_a_la_main(7), q="qdiv"))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_la_recette_n_est_pas_taillee_pour_sept():
    """Elle vaut pour des couples que rien ne relie à 7."""
    for (i, p) in ((2, 5), (4, 6), (0, 3), (5, 8), (9, 11)):
        assert non_divise(i, p).est_clos


def test_existe_temoin_verifie_le_geste_et_son_garde_fou():
    """La tactique née de la convergence WL+AST (ev.283) — et son refus.

    Le geste : ⊢ (T|x)corps ⟹ ⊢ (∃x)corps.  Le garde-fou : une matrice qui ne
    redonne PAS la conclusion au témoin est refusée AVANT le noyau — c'est lui
    qui attrape les matrices mal formées (piège S5 de la campagne)."""
    from outils_ia.arithmetique.machine_num import existe_temoin_verifie
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        existe, var,
    )
    corps = egal(var("ztv"), NUM(2))
    th = existe_temoin_verifie(N.reflexivite(NUM(2)), corps, NUM(2), "ztv")
    assert th.est_clos and th.conclusion == existe("ztv", corps)

    with pytest.raises(AssertionError, match="matrice mal formée"):
        existe_temoin_verifie(N.reflexivite(NUM(2)), egal(var("ztv"), NUM(3)),
                              NUM(2), "ztv")


def test_anti_vacuite_la_divisibilite_est_prouvable():
    """Sans ce contrôle, les négations pourraient nier un prédicat vide."""
    for (i, p) in ((1, 7), (7, 7), (3, 9)):
        th = divise_positif(i, p)
        assert th.est_clos and th.conclusion == divise_propre(NUM(i), NUM(p), q="qdiv")


def test_non_universalite_la_garde_dit_ou_ca_coince():
    """Sur i | p la recette doit refuser, et nommer la branche infermable."""
    assert obstruction(2, 6) == 3 and obstruction(7, 7) == 1
    assert obstruction(2, 7) is None
    for (i, p) in ((2, 6), (3, 6), (1, 7), (7, 7)):
        with pytest.raises(ValueError, match="OBSTRUCTION"):
            non_divise(i, p)


def test_le_vrai_verrou_est_dans_le_noyau_pas_dans_la_garde():
    """🔴 LE CONTRÔLE QUI COMPTE — une garde Python ne prouve rien.

    Garde désactivée, la machine doit mourir sur l'ARITHMÉTIQUE : la branche
    j = p/i exigerait ¬( N(p) = N(p) ), que `ne_num` refuse de fabriquer.  Et
    l'on vérifie dans la foulée qu'un cas VRAI continue de clore, donc que la
    désactivation n'a rien cassé."""
    with pytest.raises(AssertionError):
        non_divise(1, 7, garde=False)
    assert non_divise(2, 7, garde=False).est_clos

    # Et pourquoi le noyau ne peut pas céder : ⊢ N(7) = N(7) est clos, donc
    # supposer le contraire laisse une hypothèse jamais déchargeable.
    assert N.reflexivite(NUM(7)).est_clos
    with pytest.raises(AssertionError):
        ne_num(7, 7)
