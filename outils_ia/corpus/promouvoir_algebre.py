#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Promeut les meilleures découvertes ALGÉBRIQUES (=, ⊂, ⇔) en LEMMES NOMMÉS certifiés.

Pendant de `promouvoir_decouvertes.py` (implications) pour les 3 régimes algébriques du moteur :
prend les découvertes de tour 1 dont les DEUX sources sont des théorèmes du corpus (ou un pont
S6 sur une égalité du corpus), les trie par intérêt, et émet `outils_ia/decouvertes/
lemmes_algebre.py` : un lemme NOMMÉ par découverte, preuve RE-DÉRIVÉE au noyau à l'appel
(σ recalculé par matching ; pour les ponts, les deux sens d1/d2 sont essayés et la conclusion
attendue tranche). AUCUN Theoreme forgé ; frontière 22 axiomes intacte. Émet aussi le test.

PLACEMENT : `outils_ia/decouvertes/` (hors arbre bourbaki/ — vrais mais pas des résultats du livre).
USAGE : python outils_ia/corpus/promouvoir_algebre.py [package…] [--top K]
"""
from __future__ import annotations

import importlib
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from export_corpus import _decouvrir                            # noqa: E402
from conjecturer import (_fmt, _interet, PACKAGES,               # noqa: E402
                         egalites_de, chainer_egalites,
                         equivalences_de, chainer_equivalences,
                         pool_inclusions, chainer_inclusions)


def _preuve_plein(packages):
    """{conclusion: (nom_PLEIN 'module.func', thm)} — noms importables pour la re-dérivation."""
    preuve = {}
    for modname in _decouvrir(packages):
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for name in getattr(mod, "__all__", []):
            if name.endswith("_cible"):
                continue
            fn = getattr(mod, name, None)
            if not callable(fn):
                continue
            try:
                thm = fn()
            except Exception:
                continue
            if type(thm).__name__ == "Theoreme" and getattr(thm, "est_clos", False):
                preuve.setdefault(thm.conclusion, (f"{modname}.{name}", thm))
    return preuve


def _score(d):
    """Intérêt avec module = avant-dernier segment du nom plein (gère le préfixe pont:)."""
    mode, s1, s2, thm = d

    def court(s):
        s = s.split("pont:", 1)[-1]
        seg = s.split(".")
        return ".".join(seg[-2:]) if len(seg) >= 2 else s
    return _interet(mode, court(s1), court(s2), thm)


def _spec(nom):
    """Nom de source → spec de re-dérivation : ('p', égalité) si pont S6, sinon ('c', théorème)."""
    if nom.startswith("pont:"):
        return ("p", nom[5:])
    return ("c", nom)


_ENTETE = '''#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CATALOGUE de LEMMES ALGÉBRIQUES auto-découverts — AUTO-GÉNÉRÉ par promouvoir_algebre.py.

Chaque lemme est une découverte des régimes =, ⊂ ou ⇔ (chaînage de deux théorèmes du corpus,
éventuellement via le pont S6 égalité→inclusions), re-DÉRIVÉE au noyau à l'appel. Aucun
Theoreme forgé ; frontière 22 axiomes. Vrais mais HORS table des matières de Bourbaki.
Ne pas éditer à la main.
"""
from __future__ import annotations
import importlib, sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(_V9 / "outils_ia" / "corpus"))
from conjecturer import (_comme_egal, _comme_equiv, _comme_inclus, _match, _instancier,
                         egal_vers_inclusions, _composer_inclusions)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, libres_f


def _theoreme(mf):
    mod, func = mf.rsplit(".", 1)
    return getattr(importlib.import_module(mod), func)()


def _sources(spec):
    kind, mf = spec
    if kind == "c":
        return [_theoreme(mf)]
    return list(egal_vers_inclusions(_theoreme(mf)))       # pont S6 : les 2 sens


def _sigma(T2, milieu, detecteur):
    s = {}
    _match(detecteur(T2.conclusion)[0], milieu, s, libres_f(T2.conclusion))
    return _instancier(T2, {v: t for v, t in s.items() if t != var(v)})


def _egal(m1, m2, attendu):
    T1 = _theoreme(m1)
    _, b = _comme_egal(T1.conclusion)
    t = composer_egalites(T1, _sigma(_theoreme(m2), b, _comme_egal))
    assert t.est_clos and repr(t.conclusion) == attendu
    return t


def _incl(s1, s2, attendu):
    for T1 in _sources(s1):
        r1 = _comme_inclus(T1.conclusion)
        if not r1:
            continue
        for T2x in _sources(s2):
            try:
                T2 = _sigma(T2x, r1[1], _comme_inclus)
                r2 = _comme_inclus(T2.conclusion)
                tac, _ = _composer_inclusions(T1, T2, r1[0], r1[1], r2[1])
            except Exception:
                continue
            if tac.est_clos and repr(tac.conclusion) == attendu:
                return tac
    raise AssertionError("re-dérivation inclusion échouée")


def _equiv(m1, m2, attendu):
    T1 = _theoreme(m1)
    A, B = _comme_equiv(T1.conclusion)
    T2 = _sigma(_theoreme(m2), B, _comme_equiv)
    Cp = _comme_equiv(T2.conclusion)[1]
    fwd = N.loi_deduction(A, N.modus_ponens(
        N.modus_ponens(N.assume(A), equivalence_avant(T1)), equivalence_avant(T2)))
    bwd = N.loi_deduction(Cp, N.modus_ponens(
        N.modus_ponens(N.assume(Cp), equivalence_arriere(T2)), equivalence_arriere(T1)))
    t = conjonction_intro(fwd, bwd)
    assert t.est_clos and repr(t.conclusion) == attendu
    return t
'''

_TEST = '''#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test du catalogue algébrique : chaque lemme se RE-CERTIFIE au noyau (clos + cible + 22 ax.)."""
import sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lemmes_algebre as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_tous_les_lemmes_algebre_se_recertifient():
    assert M.IDS, "catalogue vide"
    for k in M.IDS:
        t = getattr(M, "lemme_alg_%d" % k)()
        assert type(t).__name__ == "Theoreme" and t.est_clos
        assert repr(t.conclusion) == M._CIBLES[k]
    assert len(theorie_ensembles().axiomes) == 22
'''


def main(argv):
    rest = argv[1:]
    top = 10
    if "--top" in rest:
        i = rest.index("--top")
        top = int(rest[i + 1])
        rest = rest[:i] + rest[i + 2:]
    packages = [a for a in rest if not a.startswith("--")] or PACKAGES

    print("# promotion des découvertes ALGÉBRIQUES en lemmes nommés", file=sys.stderr)
    preuve = _preuve_plein(packages)
    d_eg = chainer_egalites(egalites_de(preuve), preuve)
    d_eqv = chainer_equivalences(equivalences_de(preuve), preuve)
    incls, _, _ = pool_inclusions(preuve)
    d_in = chainer_inclusions(incls, preuve)
    print(f"# tour-1 corpus : {len(d_eg)} égalités, {len(d_eqv)} équivalences, {len(d_in)} inclusions")

    sel = []
    for regime, ds, helper in (("egal", d_eg, "_egal"), ("equiv", d_eqv, "_equiv"),
                               ("incl", d_in, "_incl")):
        for d in sorted(ds, key=_score, reverse=True)[:top]:
            sel.append((regime, helper, d))

    corps, cibles, ids = [], [], []
    for k, (regime, helper, (mode, s1, s2, thm)) in enumerate(sel):
        stmt = _fmt(thm.conclusion)
        if len(stmt) > 180:
            stmt = stmt[:177] + "..."
        if helper == "_incl":
            args = f"{_spec(s1)!r}, {_spec(s2)!r}"
        else:
            args = f"{s1!r}, {s2!r}"
        corps.append(f'''

def lemme_alg_{k}():
    """[{regime}] {stmt}

    Auto-découvert : {s1.split('.')[-1]} ∘ {s2.split('.')[-1]}. Re-dérivé au noyau (clos, 22 ax.)."""
    return {helper}({args}, _CIBLES[{k}])
''')
        cibles.append(f"    {k}: {repr(repr(thm.conclusion))},")
        ids.append(k)

    dest = _V9 / "outils_ia" / "decouvertes"
    dest.mkdir(parents=True, exist_ok=True)
    fin = ["", "", "IDS = " + repr(ids), "", "_CIBLES = {"] + cibles + ["}", ""]
    (dest / "lemmes_algebre.py").write_text(_ENTETE + "".join(corps) + "\n".join(fin),
                                            encoding="utf-8")
    (dest / "test_lemmes_algebre.py").write_text(_TEST, encoding="utf-8")
    n = {r: sum(1 for (rr, _, _) in sel if rr == r) for r in ("egal", "equiv", "incl")}
    print(f"# écrit {len(sel)} lemmes ({n['egal']} =, {n['equiv']} ⇔, {n['incl']} ⊂) "
          f"→ outils_ia/decouvertes/lemmes_algebre.py (+ test)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
