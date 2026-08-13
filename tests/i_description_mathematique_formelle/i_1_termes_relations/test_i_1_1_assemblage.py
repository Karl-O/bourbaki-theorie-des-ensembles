# -*- coding: utf-8 -*-
"""Tests §I.1 — assemblages : invariants, τ_x, substitution (simple et simultanée)."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, est_lettre, lettres, concat, tau_x, substitution_b_x_a,
    lettre_hors_de, substitution_simultanee)


def test_est_lettre():
    assert est_lettre("a") and est_lettre("Z") and est_lettre("x'")
    assert not est_lettre("OU") and not est_lettre("") and not est_lettre("ab")


def test_invariants_liens():
    with pytest.raises(ValueError):
        Assemblage(("TAU", "CARRE"), ((2, 1),))          # u >= v
    with pytest.raises(ValueError):
        Assemblage(("TAU", "a"), ((1, 2),))              # lien vers une lettre
    with pytest.raises(ValueError):
        Assemblage(("TAU", "CARRE", "CARRE"), ((1, 2), (1, 2)))  # dupliqué


def test_concat_decale_les_liens():
    t = tau_x(Assemblage(("=", "x", "x")), "x")          # τ lie deux ▢
    ab = concat(Assemblage(("NON",)), t)
    assert ab.signes == ("NON", "TAU", "=", "CARRE", "CARRE")
    assert ab.liens == ((2, 4), (2, 5))


def test_substitution_remplace_et_reindexe():
    a = Assemblage(("=", "x", "y"))
    b = tau_x(Assemblage(("=", "z", "z")), "z")
    r = substitution_b_x_a(b, "x", a)
    assert r.signes == ("=", "TAU", "=", "CARRE", "CARRE", "y")
    assert r.liens == ((2, 4), (2, 5))
    assert lettres(r) == {"y"}


def test_lettre_hors_de():
    a = Assemblage(("=", "x", "x'"))
    f = lettre_hors_de((a,), exclues={"y"})
    assert est_lettre(f) and f not in lettres(a) and f != "y"


def test_substitution_simultanee_echange():
    # A{y, x} avec x→y, y→x : ÉCHANGE des deux lettres — le cas où x figure
    # dans C et y dans B, impossible par deux substitutions successives.
    a = Assemblage(("=", "x", "y"))
    r = substitution_simultanee(Assemblage(("y",)), "x", Assemblage(("x",)), "y", a)
    assert r.signes == ("=", "y", "x")
    # le séquentiel naïf (C|y)(B|x)A donnerait ("=", "x", "x") : faux.
    naif = substitution_b_x_a(Assemblage(("x",)), "y",
                              substitution_b_x_a(Assemblage(("y",)), "x", a))
    assert naif.signes == ("=", "x", "x") and naif != r


def test_substitution_simultanee_cas_disjoint():
    # Quand B et C ne contiennent ni x ni y, simultané == successif.
    a = Assemblage(("=", "x", "y"))
    b, c = Assemblage(("u",)), Assemblage(("v",))
    r = substitution_simultanee(b, "x", c, "y", a)
    assert r == substitution_b_x_a(c, "y", substitution_b_x_a(b, "x", a))
    assert r.signes == ("=", "u", "v")


def test_substitution_simultanee_exige_lettres_distinctes():
    a = Assemblage(("=", "x", "y"))
    with pytest.raises(ValueError):
        substitution_simultanee(Assemblage(("u",)), "x", Assemblage(("v",)), "x", a)
