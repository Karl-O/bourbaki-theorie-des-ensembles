"""Tests §II.1 — identités de la différence (A∩(B∖C), (A∖B)∖C).

Honnêteté LCF : CLOS (0 hyp), conclusion == égalité fidèle, membres distincts, theorie = 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference_identites as M

A, B, C = var("A"), var("B"), var("C")
I, D, U = E.intersection, E.difference, E.reunion


def _check(t, lhs, rhs):
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == egal(lhs, rhs)
    assert lhs != rhs


def test_intersection_difference_associe():
    _check(M.intersection_difference_associe(), I(A, D(B, C)), D(I(A, B), C))


def test_difference_reunion():
    _check(M.difference_reunion(), D(D(A, B), C), D(A, U(B, C)))


# ── Lois du complément ∁X = E∖X (Résumé E.R.4, §1, item 14) ──────────────────
# Cibles = énoncés NUS de Bourbaki via M.cibles() ; lois GARDÉES : hyp == {X⊂E}.
_GARDEES = {"complement_involution", "reunion_complement_plein",
            "inter_ambiant_neutre", "reunion_ambiant_absorbe"}
_INCONDITIONNELLES = {"difference_vide", "inter_complement_vide"}


def _audit(nom):
    """Appelle la loi `nom` et vérifie conclusion==cible, hyps attendues, frontière."""
    cibles = M.cibles()
    t = getattr(M, nom)()
    assert t.conclusion == cibles[nom]              # fidélité : conclusion == énoncé Bourbaki
    assert t.conclusion not in t.hypotheses         # frontière LCF
    if nom in _GARDEES:
        assert set(t.hypotheses) == {cibles["hyp"]}  # hyp honnête X⊂E, non déchargée
        assert not t.est_clos
    else:
        assert not t.hypotheses and t.est_clos       # inconditionnelle close


def test_difference_vide():
    _audit("difference_vide")                        # E∖∅ = E   (item a, E=∁∅ ; clos)


def test_inter_complement_vide():
    _audit("inter_complement_vide")                  # X∩(E∖X) = ∅   (item (3) droite ; clos)


def test_inter_ambiant_neutre():
    _audit("inter_ambiant_neutre")                   # X∩E = X   (item (4) ; X⊂E)


def test_reunion_ambiant_absorbe():
    _audit("reunion_ambiant_absorbe")                # X∪E = E   (item (5) ; X⊂E)


def test_reunion_complement_plein():
    _audit("reunion_complement_plein")               # X∪(E∖X) = E   (item (3) gauche ; X⊂E)


def test_complement_involution():
    _audit("complement_involution")                  # E∖(E∖X) = X   (item (1), ∁∁X=X ; X⊂E)


def test_cibles_couvrent_toutes_les_lois():
    """Toutes les nouvelles lois ont une cible d'audit, et inversement."""
    noms = _GARDEES | _INCONDITIONNELLES
    assert noms <= set(M.cibles())                   # chaque loi a sa cible
    assert noms <= set(M.__all__)                    # chaque loi est exportée


def test_theorie_inchangee_22():
    for f in M.__all__:
        getattr(M, f)()
    assert len(E.theorie_ensembles().axiomes) == 22
