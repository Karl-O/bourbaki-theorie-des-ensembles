"""Tests §II.3.6 — Projections de la fonction x↦T (Critère C54).

Vérifie la conclusion EXACTE (== cible) et les hypothèses de chaque théorème
certifié par le noyau abrégé.
"""
from bourbaki.logique.formule import var, et, impl, appartient, pourtout, subst_t, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.fonctions import ensembles_projections_terme as P


_X = var("x")
_TERMES = {
    "singleton": E.singleton(_X),        # T = {x}
    "identite":  _X,                     # T = x
    "constante": var("c"),               # T = c
    "couple":    E.couple(_X, var("b")), # T = (x, b)
}


# ── pr₁F = A ──────────────────────────────────────────────────────────────────
def test_projection_premiere_conclusion_exacte():
    for T in _TERMES.values():
        thm = P.projection_premiere("A", T, "x", "y", "z")
        F = E.graphe_terme(var("A"), T, "x")
        assert thm.est_clos
        assert thm.conclusion == E.egal(E.dom(F), var("A"))


# ── image(F,A) ⊂ C  sous l'hypothèse (∀u)(u∈A ⇒ T[u]∈C) ──────────────────────
def _hypothese(T, c="C", x="x"):
    Tu = subst_t(var("u"), x, T)
    return pourtout("u", impl(appartient(var("u"), var("A")), appartient(Tu, var(c))))


def test_image_terme_incluse_conclusion_et_hypotheses():
    for T in _TERMES.values():
        thm = P.image_terme_incluse("A", T, "C", "x", "y")
        F = E.graphe_terme(var("A"), T, "x")
        assert thm.conclusion == inclus(E.image(F, var("A")), var("C"))
        # hypothèse unique = « C contient toutes les valeurs T[u] (u∈A) »
        assert thm.hypotheses == frozenset({_hypothese(T)})


def test_img_terme_incluse_conclusion_et_hypotheses():
    for T in _TERMES.values():
        thm = P.img_terme_incluse("A", T, "C", "x", "y")
        F = E.graphe_terme(var("A"), T, "x")
        assert thm.conclusion == inclus(E.img(F), var("C"))
        assert thm.hypotheses == frozenset({_hypothese(T)})
