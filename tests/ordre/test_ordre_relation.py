"""Tests de ensembles_ordre_relation.py — relation d'ordre comme graphe G.

Chaque test vérifie la conclusion EXACTE produite par le noyau abrégé ET que le
théorème est CLOS (aucune hypothèse résiduelle).
"""
from bourbaki.logique.formule import var, egal, et, ou, impl, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_relation as O


def _couple_dans(t, u, G):
    return appartient(E.couple(t, u), G)


G, A, Es = var("G"), var("A"), var("E")
a, b, m = var("a"), var("b"), var("m")


# ── Définitions bien formées ──────────────────────────────────────────────────
def test_definitions_construisent():
    G, Es = var("G"), var("E")
    assert O.reflexivite_sur(G, Es) is not None
    assert O.antisymetrie(G) is not None
    assert O.transitivite_rel(G) is not None
    assert O.est_ordre(G, Es) is not None
    # est_ordre = (refl et antisym) et trans
    cible = et(et(O.reflexivite_sur(G, Es), O.antisymetrie(G)), O.transitivite_rel(G))
    assert O.est_ordre(G, Es) == cible


# ── Diagonale Δ_E : ordre de l'égalité sur E (E.III.3.1) ──────────────────────
def test_diagonale_reflexive_sur():
    t = O.diagonale_reflexive_sur("E")
    assert t.est_clos
    assert t.conclusion == O.reflexivite_sur(E.diagonale(var("E")), var("E"))


def test_diagonale_antisymetrique():
    t = O.diagonale_antisymetrique("E")
    assert t.est_clos
    assert t.conclusion == O.antisymetrie(E.diagonale(var("E")))


def test_diagonale_transitive():
    t = O.diagonale_transitive("E")
    assert t.est_clos
    assert t.conclusion == O.transitivite_rel(E.diagonale(var("E")))


def test_diagonale_est_ordre():
    t = O.diagonale_est_ordre("E")
    assert t.est_clos
    assert t.conclusion == O.est_ordre(E.diagonale(var("E")), var("E"))


# ── Inclusion ⊂ : ordre (E.III.1.1, Exemple 1) ───────────────────────────────
def test_inclusion_reflexive_sur():
    t = O.inclusion_reflexive_sur("x")
    assert t.est_clos
    assert t.conclusion == inclus(var("x"), var("x"))


def test_inclusion_transitive_rel():
    t = O.inclusion_transitive_rel("a", "b", "c")
    assert t.est_clos
    cible = impl(et(inclus(var("a"), var("b")), inclus(var("b"), var("c"))),
                 inclus(var("a"), var("c")))
    assert t.conclusion == cible


def test_inclusion_antisymetrique():
    t = O.inclusion_antisymetrique("a", "b")
    assert t.est_clos
    cible = impl(et(inclus(var("a"), var("b")), inclus(var("b"), var("a"))),
                 egal(var("a"), var("b")))
    assert t.conclusion == cible


# ── Définitions ordre : majorant/minorant, plus grand/petit, maximal, borne ───
def test_definitions_ordre_construisent():
    assert O.totalement_ordonne(G, Es) is not None
    assert O.majorant(G, A, m, Es) is not None
    assert O.minorant(G, A, m, Es) is not None
    assert O.plus_grand_element(G, A, m) is not None
    assert O.plus_petit_element(G, A, m) is not None
    assert O.element_maximal(G, A, m) is not None
    assert O.element_minimal(G, A, m) is not None
    assert O.borne_superieure(G, A, m, Es) is not None
    assert O.borne_inferieure(G, A, m, Es) is not None
    # totalement_ordonne = est_ordre(G,E) et (comparabilité) — premier conjoint
    from bourbaki.logique.formule import var as _v, pourtout, impl as _impl, et as _et
    vx, vy = _v("x"), _v("y")
    comparables = pourtout("x", pourtout("y",
        _impl(_et(appartient(vx, Es), appartient(vy, Es)),
              ou(_couple_dans(vx, vy, G), _couple_dans(vy, vx, G)))))
    assert O.totalement_ordonne(G, Es) == _et(O.est_ordre(G, Es), comparables)


# ── Unicité du plus grand / plus petit élément (antisymétrie) ─────────────────
def test_plus_grand_element_unique():
    t = O.plus_grand_element_unique("G", "A")
    assert t.conclusion == egal(a, b)
    assert t.hypotheses == {O.antisymetrie(G),
                            O.plus_grand_element(G, A, a),
                            O.plus_grand_element(G, A, b)}


def test_plus_petit_element_unique():
    t = O.plus_petit_element_unique("G", "A")
    assert t.conclusion == egal(a, b)
    assert t.hypotheses == {O.antisymetrie(G),
                            O.plus_petit_element(G, A, a),
                            O.plus_petit_element(G, A, b)}


# ── Le plus grand / petit élément est maximal / minimal ───────────────────────
def test_plus_grand_est_maximal():
    t = O.plus_grand_est_maximal("G", "A")
    assert t.conclusion == O.element_maximal(G, A, m)
    assert t.hypotheses == {O.antisymetrie(G), O.plus_grand_element(G, A, m)}


def test_plus_petit_est_minimal():
    t = O.plus_petit_est_minimal("G", "A")
    assert t.conclusion == O.element_minimal(G, A, m)
    assert t.hypotheses == {O.antisymetrie(G), O.plus_petit_element(G, A, m)}


# ── Le plus grand / petit élément est un majorant / minorant ──────────────────
def test_plus_grand_est_majorant():
    t = O.plus_grand_est_majorant("G", "A")
    assert t.conclusion == O.majorant(G, A, m, Es)
    assert t.hypotheses == {inclus(A, Es), O.plus_grand_element(G, A, m)}


def test_plus_petit_est_minorant():
    t = O.plus_petit_est_minorant("G", "A")
    assert t.conclusion == O.minorant(G, A, m, Es)
    assert t.hypotheses == {inclus(A, Es), O.plus_petit_element(G, A, m)}


# ── Plus grand élément = borne supérieure ; unicité de la borne sup ───────────
def test_plus_grand_est_borne_superieure():
    t = O.plus_grand_est_borne_superieure("G", "A")
    assert t.conclusion == O.borne_superieure(G, A, m, Es)
    assert t.hypotheses == {inclus(A, Es), O.plus_grand_element(G, A, m)}


def test_borne_superieure_unique():
    t = O.borne_superieure_unique("G", "A")
    assert t.conclusion == egal(a, b)
    assert t.hypotheses == {O.antisymetrie(G),
                            O.borne_superieure(G, A, a, Es),
                            O.borne_superieure(G, A, b, Es)}


# ── Ordre induit sur une partie ; ordre total restreint ───────────────────────
def test_ordre_induit_sur_partie():
    t = O.ordre_induit_sur_partie("G")
    assert t.conclusion == O.est_ordre(G, A)
    assert t.hypotheses == {O.est_ordre(G, Es), inclus(A, Es)}


def test_totalement_ordonne_partie():
    t = O.totalement_ordonne_partie("G")
    assert t.conclusion == O.totalement_ordonne(G, A)
    assert t.hypotheses == {O.totalement_ordonne(G, Es), inclus(A, Es)}


# ── Dans un ordre TOTAL, maximal ⇒ plus grand élément ─────────────────────────
def test_maximal_est_plus_grand_si_total():
    t = O.maximal_est_plus_grand_si_total("G")
    assert t.conclusion == O.plus_grand_element(G, A, m)
    assert t.hypotheses == {O.totalement_ordonne(G, Es), inclus(A, Es),
                            O.element_maximal(G, A, m)}
