"""Tests du PONT-α DÉRIVÉ alpha_bridge (renommage de liants ∃/∀ + congruence).

Tous CLOS, 0 hyp, conclusion == cible (forme par défaut), theorie=22, NOYAU INTACT.
Couvre : renommage ∃ simple, ∀∃ imbriqué, ∀∀ (forme injective_dans), et les deux cas
DURS qui cassaient l'ancien alpha_existe — liant interne « @0 » et liant interne
coïncidant avec le NOM cible (« u »/« up »), c.-à-d. la forme exacte du verrou ℵ₀."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, tau, existe, pourtout, appartient, egal, et, impl, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge, bridge_equiv


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_existe_simple():
    """⊢ A⇒A avec A=(∃x)(x∈y) ; ponté vers (∃w)(w∈y)⇒(∃w)(w∈y)."""
    A = existe("x", appartient(var("x"), var("y")))
    thm = a_implique_a(A)
    cible = impl(existe("w", appartient(var("w"), var("y"))),
                 existe("w", appartient(var("w"), var("y"))))
    assert alpha_egal(thm.conclusion, cible)
    b = alpha_bridge(thm, cible)
    assert b.est_clos and not b.hypotheses
    assert b.conclusion == cible


def test_pour_tout_existe_imbrique():
    """∀∃ imbriqué : renommage simultané des deux liants."""
    B = pourtout("a", existe("b", appartient(var("b"), var("a"))))
    thm = a_implique_a(B)
    inner = pourtout("p", existe("q", appartient(var("q"), var("p"))))
    cible = impl(inner, inner)
    b = alpha_bridge(thm, cible)
    assert b.est_clos and b.conclusion == cible


def test_pour_tout_pour_tout_forme_injective():
    """∀∀ — forme de injective_dans (liants m0,m0p → u,up)."""
    body = lambda u, v: impl(et(appartient(var(u), var("A")), appartient(var(v), var("A"))),
                             appartient(var(u), var(v)))
    F = pourtout("m0", pourtout("m0p", body("m0", "m0p")))
    cible_int = pourtout("u", pourtout("up", body("u", "up")))
    cible = impl(cible_int, cible_int)
    b = alpha_bridge(a_implique_a(F), cible)
    assert b.est_clos and b.conclusion == cible


def test_liant_interne_arobase():
    """CAS DUR 1 — un liant τ INTERNE est nommé « @0 » : _fraiche naïf le choisirait
    comme nom frais et re-déclencherait le capture-évitement.  alpha_bridge l'évite."""
    T = lambda v: appartient(v, tau("@0", appartient(var("@0"), var("B"))))
    body = lambda u, w: impl(et(appartient(var(u), var("A")), T(var(w))), egal(var(u), var(w)))
    F = pourtout("m0", pourtout("m0p", body("m0", "m0p")))
    G = pourtout("u", pourtout("up", body("u", "up")))
    b = alpha_bridge(a_implique_a(F), impl(G, G))
    assert b.est_clos and b.conclusion == impl(G, G)


def test_liant_interne_collision_nom_cible():
    """CAS DUR 2 — le NOM cible « u »/« up » coïncide avec des liants τ INTERNES (forme
    EXACTE du verrou ℵ₀ : NN/successeur lient u,up).  L'ancien alpha_existe cassait sur
    le rond-trip ; alpha_bridge (S5+témoin, sans rond-trip du nom colisionnant) tient."""
    T2 = lambda v: appartient(v, tau("u", appartient(var("u"),
                              tau("up", appartient(var("up"), var("B"))))))
    body2 = lambda u, w: impl(et(appartient(var(u), var("A")), T2(var(w))), egal(var(u), var(w)))
    F2 = pourtout("m0", pourtout("m0p", body2("m0", "m0p")))
    G2 = pourtout("u", pourtout("up", body2("u", "up")))
    assert alpha_egal(F2, G2)
    b = alpha_bridge(a_implique_a(F2), impl(G2, G2))
    assert b.est_clos and b.conclusion == impl(G2, G2)


def test_identite_court_circuit():
    """F == G : alpha_bridge renvoie le théorème tel quel (rien à faire)."""
    A = existe("x", appartient(var("x"), var("y")))
    thm = a_implique_a(A)
    b = alpha_bridge(thm, thm.conclusion)
    assert b is thm or b.conclusion == thm.conclusion


def test_refuse_non_alpha_equivalent():
    """alpha_bridge REFUSE deux formules NON α-équivalentes (jamais de fausse preuve)."""
    A = existe("x", appartient(var("x"), var("y")))
    thm = a_implique_a(A)
    faux = impl(existe("x", appartient(var("x"), var("z"))),   # y ≠ z : pas α-équivalent
                existe("x", appartient(var("x"), var("z"))))
    with pytest.raises(ValueError):
        alpha_bridge(thm, faux)


def test_preserve_hypotheses():
    """alpha_bridge préserve les hypothèses du théorème source."""
    A = existe("x", appartient(var("x"), var("y")))
    thm = N.assume(A)                                   # {A} ⊢ A
    cible = existe("w", appartient(var("w"), var("y")))
    b = alpha_bridge(thm, cible)
    assert b.conclusion == cible
    assert b.hypotheses == frozenset({A})               # hyp inchangée


def test_theorie_22_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
