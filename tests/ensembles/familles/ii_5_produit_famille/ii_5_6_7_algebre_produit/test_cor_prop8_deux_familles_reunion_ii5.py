"""§II.5 — COROLLAIRE de la PROPOSITION 8, seconde formule (2), E II.36 :
    ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ )  =  ⋃_{(ι,κ)∈I×K} ( X_ι ∩ Y_κ ).

ÉGALITÉ PLEINE (deux sens), SANS choix NI tiers exclu (cas L={1,2}).  Le test APPELLE le
théorème et vérifie : conclusion == cible reconstruite INDÉPENDAMMENT avec les constructeurs
E.* BRUTS (intersection binaire ∩, réunions de familles ⋃, produit cartésien I×K, famille Z),
clôture (0 hyp), et theorie_ensembles() == 22 axiomes."""
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import (
    ensembles_cor_prop8_deux_familles_reunion_ii5 as M)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, egal


def _cible_independante():
    """( ⋃_{ι∈I}X_ι )∩( ⋃_{κ∈K}Y_κ ) = ⋃_{(ι,κ)∈I×K}( X_ι∩Y_κ ) reconstruite à la main
    avec les MÊMES constructeurs E.* que la fonction (Z = famille externe sur I×K)."""
    vXX, vYY, vZ, vI, vK = var("XX"), var("YY"), var("Z"), var("I"), var("K")
    gauche = E.intersection(E.reunion_famille(vXX, vI), E.reunion_famille(vYY, vK))
    droite = E.reunion_famille(vZ, E.produit(vI, vK))
    return egal(gauche, droite)


def test_cor_distributivite_reunion_deux_familles_close():
    th = M.cor_distributivite_reunion_inter_deux_familles()
    # clôture : 0 hypothèse pendante
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    # conclusion == cible (construction indépendante avec E.*)
    assert th.conclusion == _cible_independante()
    assert th.conclusion == M._cible()
    # invariant : théorie des ensembles inchangée (22 axiomes)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cible_est_une_egalite():
    """La cible est bien une égalité gauche = droite (forme close, deux sens fusionnés)."""
    th = M.cor_distributivite_reunion_inter_deux_familles()
    c = th.conclusion
    assert c.tag == "="
    g, d = c.termes
    assert g == M._membre_gauche()
    assert d == M._membre_droit()


def test_theorie_locale_close_et_hors_22():
    """La théorie locale `theorie_cor_distrib_2` porte l'axiome-schéma C54 de Z et n'entre
    PAS dans theorie_ensembles() ; N.axiome(theorie_locale, AX_Z) reste légitime."""
    th_loc = M.theorie_cor_distrib_2()
    # un seul axiome-schéma (déf. de Z par son terme sur les couples)
    assert len(th_loc.axiomes) == 1
    # theorie_ensembles() inchangée
    assert len(E.theorie_ensembles().axiomes) == 22
