"""Tests §II.2 — CARACTÉRISATION DU COUPLE (Bourbaki E II.7, §2.1, n°1).

On APPELLE le théorème (impératif), on vérifie : CLÔTURE (0 hypothèse non
déchargée), conclusion == cible construite avec les MÊMES constructeurs/liants
(équivalence ⇔, conjonctions et, est_couple = (∃a)(∃b)(z=(a,b)), pr₁/pr₂), et que
theorie_ensembles() reste à 22 axiomes (aucun axiome ajouté — équivalence pure).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, existe, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_2_couples_produit.ensembles_couple_caracterisation as M


def test_caracterisation_close_et_cible_litterale():
    t = M.caracterisation_couple()
    assert t.est_clos and not t.hypotheses           # 0 hypothèse → équivalence pure
    # cible reconstruite À LA MAIN (mêmes constructeurs/liants que l'énoncé Bourbaki)
    x, y, z = var("x"), var("y"), var("z")
    est_couple = existe("a", existe("b", egal(z, E.couple(var("a"), var("b")))))
    droite = et(et(est_couple, egal(x, E.pr1(z))), egal(y, E.pr2(z)))
    attendu = equiv(egal(z, E.couple(x, y)), droite)
    assert t.conclusion == attendu
    assert t.conclusion == M.caracterisation_couple_cible()


def test_caracterisation_est_une_equivalence():
    """La conclusion est un ⇔ (et(impl, impl)) entre z=(x,y) et la conjonction."""
    t = M.caracterisation_couple()
    c = t.conclusion
    # ⇔ se développe en et( (G⇒D), (D⇒G) ) — on vérifie via la cible
    assert c == M.caracterisation_couple_cible()
    gauche = egal(var("z"), E.couple(var("x"), var("y")))
    # le membre gauche de l'équivalence est bien z = (x, y)
    assert M.caracterisation_couple_cible().sous == equiv(gauche, _droite()).sous


def test_membre_droit_est_couple_inline_avec_existe():
    """« z est un couple » est exprimé INLINE = (∃a)(∃b)(z=(a,b)), pas un prédicat."""
    z = var("z")
    ec = M.est_couple(z)
    attendu = existe("a", existe("b", egal(z, E.couple(var("a"), var("b")))))
    assert ec == attendu


def test_caracterisation_parametrable():
    # noms ≠ a, b, c, w (témoins/trous internes)
    t = M.caracterisation_couple(x="u", y="v", z="t")
    assert t.est_clos
    assert t.conclusion == M.caracterisation_couple_cible(x="u", y="v", z="t")


def test_theorie_inchangee_22():
    M.caracterisation_couple()
    assert len(E.theorie_ensembles().axiomes) == 22


def _droite():
    x, y, z = var("x"), var("y"), var("z")
    est_couple = existe("a", existe("b", egal(z, E.couple(var("a"), var("b")))))
    return et(et(est_couple, egal(x, E.pr1(z))), egal(y, E.pr2(z)))
