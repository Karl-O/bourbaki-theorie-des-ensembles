"""Tests §II.5.3 — injectivité de l'application diagonale x↦x̃.

Vérifie : la conclusion EXACTE (== cible reconstruite), la clôture (est_clos), et
l'invariant theorie_ensembles() == 22 (aucun axiome neuf : preuve set/fonction-
théorique via le pivot graphe_terme_valeur).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique import ensembles_extension_canonique as X
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_diagonale import ensembles_diagonale_injective as D


def test_cible_diagonale_injective_forme():
    """La cible est ( α∈I et x∈E et y∈E et x̃=ỹ ) ⇒ x=y (hypothèse conjonctive à gauche)."""
    vE, vI = var("E"), var("I")
    vx, vy, valpha = var("x"), var("yy"), var("alpha")
    xt = X.famille_constante(vI, vx, "iota")
    yt = X.famille_constante(vI, vy, "iota")
    hyp = et(et(et(appartient(valpha, vI), appartient(vx, vE)),
                appartient(vy, vE)),
             egal(xt, yt))
    cible = impl(hyp, egal(vx, vy))
    assert D.cible_diagonale_injective("E", "I", "x", "yy", "alpha", "iota") == cible


def test_diagonale_injective_conclusion_et_close():
    """⊢ ( α∈I et x∈E et y∈E et x̃=ỹ ) ⇒ x=y : conclusion == cible et théorème clos."""
    thm = D.diagonale_injective("E", "I", "x", "yy", "alpha", "iota")
    cible = D.cible_diagonale_injective("E", "I", "x", "yy", "alpha", "iota")
    assert thm.conclusion == cible
    assert thm.est_clos


def test_theorie_ensembles_inchangee_22():
    """Preuve set/fonction-théorique : aucun axiome neuf, theorie_ensembles() reste à 22."""
    assert len(E.theorie_ensembles().axiomes) == 22
