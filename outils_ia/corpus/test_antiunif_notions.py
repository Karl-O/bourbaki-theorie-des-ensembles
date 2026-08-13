#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests de l'anti-unificateur de notions (JALON 1) — AST pur, aucun exec-noyau (rapide).

Verrouille la brique nouvelle : DÉTECTION de slots par anti-unification, α-normalisation des
locales, et dédup des slots aux valeurs identiques. Ne touche pas la frontière de confiance.
"""
import ast
import sys
import textwrap
from pathlib import Path

_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from antiunif_notions import _canon, _antiunify_block, _dedup     # noqa: E402


def _block(src):
    return ast.parse(textwrap.dedent(src)).body


def test_divergence_feuille_donne_un_slot():
    """Deux blocs identiques SAUF un littéral ('x' vs 'y') → exactement 1 slot = ce littéral."""
    a = _block("x = f(var('x'))\ny = g(x)")
    b = _block("x = f(var('y'))\ny = g(x)")
    tmpl, slots = _antiunify_block([_canon(a), _canon(b)])
    uniq, _ = _dedup(slots)
    assert len(uniq) == 1
    assert set(uniq[0]) == {"'x'", "'y'"}
    # squelette partagé : le template contient le slot marqueur
    src = ast.unparse(ast.fix_missing_locations(ast.Module(body=tmpl, type_ignores=[])))
    assert "SLOT0" in src and "g(_v0)" in src            # locale α-normalisée en _v0


def test_blocs_identiques_zero_slot():
    """Après α-normalisation, deux blocs structurellement identiques → 0 slot."""
    a = _block("h1 = N.assume(p)\nr = N.modus_ponens(h1, q)")
    b = _block("hyp = N.assume(p)\nres = N.modus_ponens(hyp, q)")
    tmpl, slots = _antiunify_block([_canon(a), _canon(b)])
    uniq, _ = _dedup(slots)
    assert uniq == []                                    # noms de dataflow neutralisés


def test_dedup_fusionne_slots_identiques():
    """Deux positions divergentes de MÊMES valeurs par instance → 1 seul paramètre."""
    a = _block("x = h(var('x'), var('x'))")
    b = _block("x = h(var('y'), var('y'))")
    _, slots = _antiunify_block([_canon(a), _canon(b)])
    assert len(slots) == 2                               # deux positions brutes
    uniq, mapping = _dedup(slots)
    assert len(uniq) == 1                                # fusionnées (même argument réutilisé)
    assert mapping[0] == mapping[1] == 0


def test_projection_pr1_pr2_est_un_slot():
    """Le cas prédit (pas 16-suite) : pr1 vs pr2 = la divergence détectée comme slot."""
    a = _block("t = E.pr1(couple(a, b))")
    b = _block("t = E.pr2(couple(a, b))")
    _, slots = _antiunify_block([_canon(a), _canon(b)])
    uniq, _ = _dedup(slots)
    assert len(uniq) == 1
    assert set(uniq[0]) == {"E.pr1", "E.pr2"}


def test_divergence_d_operateur_refuse_proprement():
    """somme (`+`) vs produit (`*`) : la divergence tombe à une position d'OPÉRATEUR —
    un slot-Name y fabriquerait un AST invalide (KeyError 'Name' dans unparse, mesuré
    au tour #8). L'anti-unification doit refuser (None, None), pas produire un template
    cassé."""
    a = _block("x = f(m + n)")
    b = _block("x = f(m * n)")
    tmpl, slots = _antiunify_block([_canon(a), _canon(b)])
    assert tmpl is None and slots is None
