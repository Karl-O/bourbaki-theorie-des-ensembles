"""Tests §II.3.6 — Définition d'une fonction par un terme (Critère C54).

Vérifie la conclusion EXACTE (== cible) et la clôture (est_clos) de chaque
théorème certifié par le noyau abrégé.
"""
from formule import var, equiv, et, impl, appartient, egal, subst_t, alpha_egal
import ensembles_abrege as E
import ensembles_fonction_terme as FT


# Quelques termes-tests T(x) variés.
_X = var("x")
_TERMES = {
    "singleton": E.singleton(_X),       # T = {x}
    "identite":  _X,                    # T = x
    "constante": var("c"),              # T = c   (x ne figure pas dans T)
    "couple":    E.couple(_X, var("b")),# T = (x, b)
}


def _cible_membre(T, u="u", v="v", x="x", y="y"):
    vA, vu, vv = var("A"), var(u), var(v)
    F = E.graphe_terme(vA, T, x)
    Tu = subst_t(vu, x, T)
    lhs = appartient(E.couple(vu, vv), F)
    rhs = et(appartient(vu, vA), egal(vv, Tu))
    return equiv(lhs, rhs)


def test_membre_graphe_terme_conclusion_exacte():
    for T in _TERMES.values():
        thm = FT.membre_graphe_terme("A", T, "u", "v", "x", "y")
        assert thm.est_clos
        assert thm.conclusion == _cible_membre(T)


def test_graphe_terme_fonctionnel_conclusion_exacte():
    for T in _TERMES.values():
        thm = FT.graphe_terme_fonctionnel("A", T, "x", "y")
        F = E.graphe_terme(var("A"), T, "x")
        assert thm.est_clos
        # cœur de C54 : « ce graphe est fonctionnel »
        assert thm.conclusion == E.est_fonctionnel(F)


def test_axiome_graphe_terme_bien_forme():
    # L'axiome de caractérisation est utilisable par le noyau (constante introductrice).
    import noyau_abrege as N
    T = E.singleton(_X)
    th = E.theorie_graphe_terme(var("A"), T)
    ax = N.axiome(th, E.axiome_graphe_terme(var("A"), T))
    assert ax.est_clos
    assert ax.conclusion == E.axiome_graphe_terme(var("A"), T)
