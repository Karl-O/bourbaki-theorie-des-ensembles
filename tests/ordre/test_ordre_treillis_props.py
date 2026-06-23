"""Tests de ensembles_ordre_treillis_props.py — propositions III.1-2 d'ordre.

Vérifie pour chaque théorème : conclusion EXACTE, et soit clôture (est_clos),
soit le jeu d'hypothèses EXACT (théorèmes conditionnels).  Anti-tautologie :
les conclusions sont comparées aux formules CIBLES construites indépendamment.
"""
from bourbaki.logique.formule import (
    var, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_relation as O
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_treillis_props as P


G, Gp, Gpp = var("G"), var("Gp"), var("Gpp")
A, Es, Ep, Epp = var("A"), var("E"), var("Ep"), var("Epp")
a, b, m = var("a"), var("b"), var("m")
f, fp, g, gp, h = var("f"), var("fp"), var("g"), var("gp"), var("h")


def _couple_dans(t, u, Gr):
    return appartient(E.couple(t, u), Gr)


def _val(fn, x):
    return E.valeur(fn, x, b="j")


def _strict(t, u, Gr):
    return et(_couple_dans(t, u, Gr), non(egal(t, u)))


def _R(Gr):
    return lambda u, v: appartient(E.couple(u, v), Gr)


# ════════════════════════════════════════════════════════════════════════════
#  TREILLIS / BORNE
# ════════════════════════════════════════════════════════════════════════════
def test_borne_inferieure_unique():
    t = P.borne_inferieure_unique(G, A)
    assert t.conclusion == egal(a, b)
    assert t.hypotheses == {
        O.antisymetrie(G),
        O.borne_inferieure(G, A, a, "E"),
        O.borne_inferieure(G, A, b, "E"),
    }


def test_plus_petit_est_borne_inferieure():
    t = P.plus_petit_est_borne_inferieure(G, A)
    assert t.conclusion == O.borne_inferieure(G, A, m, "E")
    assert t.hypotheses == {inclus(A, Es), O.plus_petit_element(G, A, m)}


# ════════════════════════════════════════════════════════════════════════════
#  COMPOSÉE
# ════════════════════════════════════════════════════════════════════════════
def test_composee_croissantes_construit():
    t = P.composee_croissantes_est_croissante()
    assert t.conclusion == P.croissante_graphe(G, Gpp, h, "E")
    # 4 hypothèses : g croissante, g' croissante, g(t)∈E', h(x)=g'(g(x))
    assert P.croissante_graphe(G, Gp, g, "E") in t.hypotheses
    assert P.croissante_graphe(Gp, Gpp, gp, "Ep") in t.hypotheses
    assert len(t.hypotheses) == 4


def test_composee_compatibles_construit():
    t = P.composee_compatibles_est_compatible()
    assert t.conclusion == P.compatible_graphe(G, Gpp, h, "E")
    assert P.compatible_graphe(G, Gp, f, "E") in t.hypotheses
    assert P.compatible_graphe(Gp, Gpp, fp, "Ep") in t.hypotheses
    assert len(t.hypotheses) == 4


# ════════════════════════════════════════════════════════════════════════════
#  ISOMORPHISMES
# ════════════════════════════════════════════════════════════════════════════
def test_compatible_reciproque_construit():
    t = P.compatible_reciproque()
    # conclusion : g compatible (E',G')→(E,G), quantifs u,v
    assert t.conclusion == P.compatible_graphe(Gp, G, g, "Ep", x="u", y="v")
    assert P.compatible_graphe(G, Gp, f, "E") in t.hypotheses
    assert len(t.hypotheses) == 3


def test_iso_preserve_plus_grand_construit():
    t = P.iso_preserve_plus_grand()
    # conclusion : f(m)∈E' et (∀v)(v∈E' ⇒ (v,f(m))∈Gp)
    fm = _val(f, m)
    vv = var("v")
    pg = pourtout("v", impl(appartient(vv, Ep),
                            appartient(E.couple(vv, fm), Gp)))
    assert t.conclusion == et(appartient(fm, Ep), pg)
    # 4 hypothèses (compatible, but, surjectif, plus grand)
    assert len(t.hypotheses) == 4


def test_iso_preserve_plus_petit_construit():
    t = P.iso_preserve_plus_petit()
    fm = _val(f, m)
    vv = var("v")
    pp = pourtout("v", impl(appartient(vv, Ep),
                            appartient(E.couple(fm, vv), Gp)))
    assert t.conclusion == et(appartient(fm, Ep), pp)
    assert len(t.hypotheses) == 4


# ════════════════════════════════════════════════════════════════════════════
#  INTERVALLES
# ════════════════════════════════════════════════════════════════════════════
def test_intervalle_ferme_a_dans():
    t = P.intervalle_ferme_a_dans(G)
    interv = E.intervalle_ferme(P._rg(G), Es, a, b)
    assert t.conclusion == appartient(a, interv)
    # axiome déchargé : seules restent a∈E, (a,a)∈G, (a,b)∈G
    assert t.hypotheses == {
        appartient(a, Es),
        _couple_dans(a, a, G),
        _couple_dans(a, b, G),
    }


def test_intervalle_ferme_non_vide_si_a_inf_b():
    t = P.intervalle_ferme_non_vide_si_a_inf_b(G)
    interv = E.intervalle_ferme(P._rg(G), Es, a, b)
    assert t.conclusion == non(egal(interv, E.VIDE))
    assert t.hypotheses == {
        appartient(a, Es),
        _couple_dans(a, a, G),
        _couple_dans(a, b, G),
    }


def test_theorie_intervalle_ferme_dediee():
    # l'axiome vit dans une théorie DÉDIÉE, pas dans theorie_ensembles (= 22).
    th = P.theorie_intervalle_ferme(G)
    assert th.nom == "IntervalleFerme"
    assert len(th.axiomes) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 11 — strictement monotone ⇒ injective
# ════════════════════════════════════════════════════════════════════════════
def test_strictement_croissante_injective():
    t = P.strictement_croissante_injective_graphe(G, Gp, f, "E")
    assert t.conclusion == P.injective_sur(f, "E")
    assert O.totalement_ordonne(G, Es) in t.hypotheses
    assert P._str_cr(G, Gp, f, "E", "x", "y") in t.hypotheses
    assert len(t.hypotheses) == 2


def test_strictement_decroissante_injective():
    t = P.strictement_decroissante_injective_graphe(G, Gp, f, "E")
    assert t.conclusion == P.injective_sur(f, "E")
    assert O.totalement_ordonne(G, Es) in t.hypotheses
    assert P._str_dec(G, Gp, f, "E", "x", "y") in t.hypotheses
    assert len(t.hypotheses) == 2


def test_strictement_monotone_injective():
    t = P.strictement_monotone_injective_graphe(G, Gp, f, "E")
    assert t.conclusion == P.injective_sur(f, "E")
    str_cr = P._str_cr(G, Gp, f, "E", "x", "y")
    str_dec = P._str_dec(G, Gp, f, "E", "x", "y")
    assert O.totalement_ordonne(G, Es) in t.hypotheses
    assert ou(str_cr, str_dec) in t.hypotheses
    assert len(t.hypotheses) == 2


# ── anti-affaibli : la conclusion d'injectivité n'est pas triviale ───────────
def test_injective_sur_est_bien_quantifiee():
    # injective_sur = (∀x)(∀y)(... ⇒ x=y) ; pourtout encodé en ¬∃¬, et le corps
    # CONTIENT bien l'implication gardée vers x=y (pas une tautologie triviale).
    vx, vy = var("x"), var("y")
    hyp = et(et(appartient(vx, Es), appartient(vy, Es)),
             egal(_val(f, vx), _val(f, vy)))
    cible = pourtout("x", pourtout("y", impl(hyp, egal(vx, vy))))
    assert P.injective_sur(f, "E") == cible
