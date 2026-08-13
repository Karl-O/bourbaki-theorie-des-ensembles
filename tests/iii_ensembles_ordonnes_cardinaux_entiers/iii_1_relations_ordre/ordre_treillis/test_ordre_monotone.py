"""Tests de ensembles_ordre_monotone.py — applications monotones / treillis.

Pour chaque DÉFINITION : on vérifie la forme attendue (construction fidèle).
Pour chaque LEMME : on vérifie la conclusion EXACTE et le statut clos / hypothèses.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, ou, impl, non, appartient, existe, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_monotone as M
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, borne_superieure, borne_inferieure,
)


def _couple_dans(t, u, G):
    return appartient(E.couple(t, u), G)


def _val(f, x):
    return E.valeur(f, x, b="j")


def _strict(t, u, G):
    return et(_couple_dans(t, u, G), non(egal(t, u)))


G, Gp, f = var("G"), var("Gp"), var("f")
Es, Ep = var("E"), var("Ep")
x, y = var("x"), var("y")


# ── Définition 1 — croissante / décroissante / monotone ───────────────────────
def test_est_croissante_forme():
    cible = pourtout("x", pourtout("y", impl(
        et(et(appartient(x, Es), appartient(y, Es)), _couple_dans(x, y, G)),
        _couple_dans(_val(f, x), _val(f, y), Gp))))
    assert M.est_croissante(G, Gp, f, Es, Ep) == cible


def test_est_decroissante_forme():
    cible = pourtout("x", pourtout("y", impl(
        et(et(appartient(x, Es), appartient(y, Es)), _couple_dans(x, y, G)),
        _couple_dans(_val(f, y), _val(f, x), Gp))))
    assert M.est_decroissante(G, Gp, f, Es, Ep) == cible


def test_est_monotone_forme():
    cible = ou(M.est_croissante(G, Gp, f, Es, Ep),
               M.est_decroissante(G, Gp, f, Es, Ep))
    assert M.est_monotone(G, Gp, f, Es, Ep) == cible


# ── Définition 2 — strictement croissante / décroissante / monotone ───────────
def test_est_strictement_croissante_forme():
    cible = pourtout("x", pourtout("y", impl(
        et(et(appartient(x, Es), appartient(y, Es)), _strict(x, y, G)),
        _strict(_val(f, x), _val(f, y), Gp))))
    assert M.est_strictement_croissante(G, Gp, f, Es, Ep) == cible


def test_est_strictement_decroissante_forme():
    cible = pourtout("x", pourtout("y", impl(
        et(et(appartient(x, Es), appartient(y, Es)), _strict(x, y, G)),
        _strict(_val(f, y), _val(f, x), Gp))))
    assert M.est_strictement_decroissante(G, Gp, f, Es, Ep) == cible


def test_est_strictement_monotone_forme():
    cible = ou(M.est_strictement_croissante(G, Gp, f, Es, Ep),
               M.est_strictement_decroissante(G, Gp, f, Es, Ep))
    assert M.est_strictement_monotone(G, Gp, f, Es, Ep) == cible


# ── Définition 8 — ensemble réticulé (treillis) ───────────────────────────────
def test_admet_borne_sup_inf_forme():
    P = E.paire(x, y)
    s, i = var("s"), var("i")
    cible = existe("s", existe("i",
        et(borne_superieure(G, P, s, Es, "u", "mbs"),
           borne_inferieure(G, P, i, Es, "u", "mbi"))))
    assert M.admet_borne_sup_inf(G, x, y, Es) == cible


def test_est_reticule_forme():
    toute_paire = pourtout("x", pourtout("y",
        impl(et(appartient(x, Es), appartient(y, Es)),
             M.admet_borne_sup_inf(G, x, y, Es))))
    cible = et(est_ordre(G, Es), toute_paire)
    assert M.est_reticule(G, Es) == cible


# ── Lemmes directs : croissante / décroissante ⇒ monotone ─────────────────────
def test_croissante_implique_monotone():
    t = M.croissante_implique_monotone()
    assert t.est_clos
    cible = impl(M.est_croissante(G, Gp, f), M.est_monotone(G, Gp, f))
    assert t.conclusion == cible


def test_decroissante_implique_monotone():
    t = M.decroissante_implique_monotone()
    assert t.est_clos
    cible = impl(M.est_decroissante(G, Gp, f), M.est_monotone(G, Gp, f))
    assert t.conclusion == cible


# ── Lemme : strictement croissante ⇒ croissante (sous ordre but + f:E→E') ─────
def test_strictement_croissante_implique_croissante():
    t = M.strictement_croissante_implique_croissante()
    assert t.conclusion == M.est_croissante(G, Gp, f)
    assert t.hypotheses == {
        est_ordre(Gp, Ep),
        M._f_dans_but(f, Es, Ep),
        M.est_strictement_croissante(G, Gp, f),
    }


def test_strictement_decroissante_implique_decroissante():
    t = M.strictement_decroissante_implique_decroissante()
    assert t.conclusion == M.est_decroissante(G, Gp, f)
    assert t.hypotheses == {
        est_ordre(Gp, Ep),
        M._f_dans_but(f, Es, Ep),
        M.est_strictement_decroissante(G, Gp, f),
    }
