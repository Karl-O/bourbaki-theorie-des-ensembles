# -*- coding: utf-8 -*-
"""IMPRIMEUR formule→code par MATCHING INVERSE — brique de l'auto-promotion.

Validé 7/7 aller-retours exacts sur les cibles réelles des deux fournées de
lemmes machine (prototype PR1, ev.314, 8 août 2026). Pour chaque constructeur
ENREGISTRÉ, une sonde B(variables fraîches) est matchée (conj_base._match)
contre le sous-arbre : si ça matche, on émet « B(<slots imprimés>) » et on
descend. Les connecteurs sont reconnus structurellement, ABRÉVIATIONS d'abord
(impl avant ou ; et = ¬(¬a∨¬b) ; ∀ = ¬∃¬). Les définitionnels (est_fini…)
s'impriment par leur NOM — jamais dépliés en soupe de τ.

Usage : `code_de(f)` → source Python ; `enregistre(nom, builder, arite)` pour
étendre le registre. `NonImprimable` = hors registre (verdict honnête).
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_CORPUS = _V9 / "outils_ia" / "corpus"
if str(_CORPUS) not in sys.path:
    sys.path.insert(0, str(_CORPUS))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var,
)
from conj_base import _match, _est_terme                              # noqa: E402


class NonImprimable(Exception):
    """Sous-arbre hors registre : l'imprimeur refuse plutôt que d'inventer."""


_SONDE_V = [var("_pr%d" % k) for k in range(4)]
REGISTRE = []          # (nom_code, sonde, noms_slots) — ordre d'ajout = priorité


def enregistre(nom_code, builder, arite):
    """Ajoute un constructeur au registre (sonde à `arite` variables fraîches)."""
    vs = _SONDE_V[:arite]
    REGISTRE.append((nom_code, builder(*vs), [v.nom for v in vs]))


def _slots(pat, cible, noms):
    s = {}
    if _match(pat, cible, s, set(noms)):
        return [s.get(n, var(n)) for n in noms]
    return None


def code_de(f):
    """Émet une expression Python (registre + connecteurs) qui ré-évalue en f."""
    for nom_code, sonde, noms in REGISTRE:
        if type(sonde) is type(f):
            sl = _slots(sonde, f, noms)
            if sl is not None:
                return "%s(%s)" % (nom_code, ", ".join(code_de(x) for x in sl))
    if _est_terme(f):
        if f.tag == "var":
            return "var(%r)" % f.nom
        raise NonImprimable("terme %s:%s hors registre" % (f.tag, f.nom))
    if f.tag == "ou" and f.sous[0].tag == "non":            # impl(a,b) = ¬a ∨ b
        return "impl(%s, %s)" % (code_de(f.sous[0].sous[0]), code_de(f.sous[1]))
    if (f.tag == "non" and f.sous[0].tag == "ou"
            and f.sous[0].sous[0].tag == "non" and f.sous[0].sous[1].tag == "non"):
        return "et(%s, %s)" % (code_de(f.sous[0].sous[0].sous[0]),
                               code_de(f.sous[0].sous[1].sous[0]))
    if (f.tag == "non" and f.sous[0].tag == "exists"
            and f.sous[0].sous[0].tag == "non"):            # ∀x F = ¬∃x ¬F
        return "pourtout(%r, %s)" % (f.sous[0].lieur,
                                     code_de(f.sous[0].sous[0].sous[0]))
    if f.tag == "exists":
        return "existe(%r, %s)" % (f.lieur, code_de(f.sous[0]))
    if f.tag == "non":
        return "non(%s)" % code_de(f.sous[0])
    if f.tag == "ou":
        return "ou(%s, %s)" % (code_de(f.sous[0]), code_de(f.sous[1]))
    if f.tag == "=":
        return "egal(%s, %s)" % (code_de(f.termes[0]), code_de(f.termes[1]))
    if f.tag == "in":
        return "appartient(%s, %s)" % (code_de(f.termes[0]), code_de(f.termes[1]))
    raise NonImprimable("formule %s hors registre" % f.tag)


def _registre_arithmetique():
    """Registre par défaut de l'îlot (appelé une fois, imports paresseux)."""
    if REGISTRE:
        return
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_cardinal, inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, successeur,
    )
    enregistre("est_fini", est_fini, 1)
    enregistre("est_cardinal", est_cardinal, 1)
    enregistre("inf_egal_card", inf_egal_card, 2)
    enregistre("successeur", successeur, 1)
    enregistre("SC", somme_cardinale_binaire, 2)


__all__ = ["code_de", "enregistre", "NonImprimable", "REGISTRE",
           "_registre_arithmetique"]
