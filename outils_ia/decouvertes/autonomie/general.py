# -*- coding: utf-8 -*-
"""DESCENTES GÉNÉRALES de l'organe de besoin — la machine sur les énoncés ∀ (ev.325).

Deux règles par-dessus `decouvertes.besoin.besoins` :
  · sous ∀ (¬∃x¬φ) : viser la matrice à variable LIBRE ; refermer par
    `generalisation` (le noyau REFUSE si la variable reste libre dans une
    hypothèse — c'est le garde-fou, pas nous) ;
  · sous ⇒ (ou(¬a, b)) : supposer a (assume), l'éclater en conjoints par
    élimination, viser b SOUS hypothèses, décharger par `loi_deduction`.

Premier verdict réel (8 août 2026, marathon 11h) : sur `goldbach()` — TOUT n,
aucun sous-cas — la machine est descendue sous ∀ngb, a supposé l'antécédent
général, et a nommé son manque pour ∃p∃q(premiers ∧ ngb=p+q) à ngb LIBRE :
« ngb ≤ N6 » via l'unique route (la borne). La borne ne peut structurellement
pas donner tout n — DIT PAR LA MACHINE ; une route non-bornée (théorie des
nombres générale) est désormais jugée nécessaire par l'algo.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_CORPUS = _V9 / "outils_ia" / "corpus"
if str(_CORPUS) not in sys.path:
    sys.path.insert(0, str(_CORPUS))


def besoins_generaux(but, impls, faits, profondeur=3, trace=None,
                     proposeurs=None):
    """Descentes ∀ et ⇒, feuilles = organe de besoin. → (th|None, manques).

    ⚠️ `proposeurs` (10 août, ev.400) : les proposeurs de témoins NE
    FRANCHISSAIENT PAS cette couche — un but universel ou implicatif les
    perdait avant d'atteindre l'organe, si bien qu'aucun ∃ enfoui sous un ∀
    n'était attaquable. Défaut mesuré en sondant GG24. On les propage
    maintenant aux QUATRE points de passage ; par défaut (None) le
    comportement est inchangé."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_droite, conjonction_elim_gauche,
    )
    from outils_ia.decouvertes.besoin import besoins
    from conj_existe import _est_et

    # VOIE DIRECTE D'ABORD (PB9-ter, ev.338) : un but en forme d'implication
    # descendait TOUJOURS au lieu d'être confronté au pool — or un théorème du
    # pool peut conclure exactement en cette implication. Les descentes ne sont
    # que le REPLI.
    th_direct, _m_direct = besoins(but, impls, faits, profondeur, None,
                                   proposeurs=proposeurs)
    if th_direct is not None:
        if trace:
            trace({"type": "fermé-direct"})
        return th_direct, []

    if (hasattr(but, "tag") and but.tag == "non" and but.sous[0].tag == "exists"
            and but.sous[0].sous[0].tag == "non"):          # ∀x φ = ¬∃x¬φ
        x = but.sous[0].lieur
        matrice = but.sous[0].sous[0].sous[0]
        if trace:
            trace({"type": "descente-∀", "var": x})
        th_m, manques = besoins_generaux(matrice, impls, faits, profondeur,
                                         trace, proposeurs)
        if th_m is not None:
            try:
                th = N.generalisation(x, th_m)
                if th.conclusion == but:
                    return th, []
            except Exception as e:
                if trace:
                    trace({"type": "refus-généralisation", "err": str(e)[:80]})
        return None, manques + _m_direct

    if hasattr(but, "tag") and but.tag == "ou" and but.sous[0].tag == "non":
        a, b = but.sous[0].sous[0], but.sous[1]             # a ⇒ b = ¬a ∨ b
        if trace:
            trace({"type": "descente-⇒"})
        faits2 = dict(faits)
        pile = [N.assume(a)]
        while pile:                                         # a et ses conjoints
            t = pile.pop()
            faits2.setdefault(t.conclusion, ("hyp", t))
            if _est_et(t.conclusion):
                pile.append(conjonction_elim_gauche(t))
                pile.append(conjonction_elim_droite(t))
        th_b, manques = besoins_generaux(b, impls, faits2, profondeur, trace,
                                         proposeurs)
        if th_b is not None:
            th = N.loi_deduction(a, th_b)
            if th.conclusion == but:
                return th, []
        return None, manques + _m_direct

    return besoins(but, impls, faits, profondeur, trace,
                   proposeurs=proposeurs)


__all__ = ["besoins_generaux"]
