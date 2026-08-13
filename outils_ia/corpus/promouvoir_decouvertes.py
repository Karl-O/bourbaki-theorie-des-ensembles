#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Promeut les meilleures DÉCOUVERTES du conjectureur en LEMMES NOMMÉS certifiés (catalogue).

Prend les découvertes par transitivité (les plus nombreuses/propres), les trie par INTÉRÊT, et émet
`outils_ia/decouvertes/lemmes_decouverts.py` : un lemme NOMMÉ par découverte, dont la preuve est
RE-DÉRIVÉE au noyau à l'appel (import des deux théorèmes-sources + `assume`/`modus_ponens`/
`loi_deduction`, σ recalculé par matching). AUCUN `Theoreme` forgé : tout est re-certifié à l'exécution,
frontière 22 axiomes intacte. Émet aussi un test qui rappelle chaque lemme et vérifie (clos + conclusion
attendue + `theorie==22`).

PLACEMENT : `outils_ia/decouvertes/` (hors arbre `bourbaki/` calqué sur la table des matières — ces
lemmes sont VRAIS et certifiés mais ne sont PAS des résultats de Bourbaki ; on respecte la fidélité).

Outillage seulement ; le noyau reste seul juge.
USAGE : python outils_ia/corpus/promouvoir_decouvertes.py [package…] [--top K]
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
from conjecturer import (_comme_impl, _match, _instancier, _interet,  # noqa: E402
                         _cle_canon, _fmt, PACKAGES)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl, libres_f, var  # noqa: E402

_DEST = _V9 / "outils_ia" / "decouvertes"


def _corpus_plein(packages):
    """(implications clos avec nom PLEIN, ensemble des clés canoniques connues)."""
    impls, connus = [], set()
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
            if type(thm).__name__ != "Theoreme" or not getattr(thm, "est_clos", False):
                continue
            connus.add(_cle_canon(thm.conclusion))
            ab = _comme_impl(thm.conclusion)
            if ab and ab[0] != ab[1]:
                impls.append((modname, name, thm, ab[0], ab[1]))
    return impls, connus


def _decouvrir_transit(impls, connus):
    """Découvertes par transitivité relâchée, avec provenance PLEINE (modules+noms). Dédup canonique."""
    trouves, vus = [], set()
    for (m1, n1, T1, A, B) in impls:
        for (m2, n2, T2, Bp, C) in impls:
            if (m2, n2) == (m1, n1):
                continue
            s = {}
            if not _match(Bp, B, s, libres_f(T2.conclusion)):
                continue
            sig = {v: t for v, t in s.items() if t != var(v)}
            try:
                T2p = _instancier(T2, sig) if sig else T2
                ab = _comme_impl(T2p.conclusion)
                if ab is None or ab[0] != B:
                    continue
                Cp = ab[1]
                if A == Cp:
                    continue
                cible = impl(A, Cp)
                cle = _cle_canon(cible)
                if cle in connus or cle in vus:
                    continue
                tAC = N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2p))
            except Exception:
                continue
            if tAC.est_clos and tAC.conclusion == cible:
                vus.add(cle)
                trouves.append((m1, n1, m2, n2, tAC))
    return trouves


_TMPL = '''

def lemme_%(k)d():
    """%(stmt)s

    Auto-decouvert (transitivite) : %(n1)s o %(n2)s. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module(%(m1)r), %(n1)r)()
    T2 = getattr(importlib.import_module(%(m2)r), %(n2)r)()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))
'''


def _emettre(sel):
    entete = [
        "#!/usr/bin/env python3", "# -*- coding: utf-8 -*-",
        '"""CATALOGUE de LEMMES auto-decouverts — AUTO-GENERE par promouvoir_decouvertes.py.',
        "",
        "Chaque lemme est une DECOUVERTE du conjectureur (chainage de deux theoremes du corpus par",
        "transitivite), promue en fonction NOMMEE dont la preuve est RE-DERIVEE au noyau a l'appel",
        "(aucun Theoreme force ; frontiere 22 axiomes intacte). VRAIS et certifies, mais HORS de la",
        "table des matieres de Bourbaki (ce ne sont pas des resultats du livre). Ne pas editer a la main.",
        '"""',
        "from __future__ import annotations", "import importlib, sys",
        "from pathlib import Path",
        "_V9 = Path(__file__).resolve().parents[2]",
        "sys.path.insert(0, str(_V9))",
        'sys.path.insert(0, str(_V9 / "outils_ia" / "corpus"))',
        "from conjecturer import _comme_impl, _match",
        "from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N",
        "from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie",
        "from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, libres_f",
        "",
    ]
    corps, cibles, ids = [], [], []
    for k, (m1, n1, m2, n2, thm) in enumerate(sel):
        stmt = _fmt(thm.conclusion).replace("%", "pct")
        if len(stmt) > 200:
            stmt = stmt[:197] + "..."
        corps.append(_TMPL % {"k": k, "stmt": stmt, "m1": m1, "n1": n1, "m2": m2, "n2": n2})
        cibles.append(f"    {k}: {repr(repr(thm.conclusion))},")
        ids.append(k)
    fin = ["", "", "IDS = " + repr(ids), "", "_CIBLES = {"] + cibles + ["}", ""]
    return "\n".join(entete) + "".join(corps) + "\n".join(fin) + "\n"


_TEST = '''#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test du catalogue de lemmes auto-decouverts : chaque lemme se RE-CERTIFIE au noyau."""
import sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lemmes_decouverts as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_tous_les_lemmes_se_recertifient():
    assert M.IDS, "catalogue vide"
    for k in M.IDS:
        t = getattr(M, "lemme_%d" % k)()
        assert type(t).__name__ == "Theoreme"
        assert t.est_clos                              # clos = 0 hypothese
        assert repr(t.conclusion) == M._CIBLES[k]      # bien le theoreme attendu
    assert len(theorie_ensembles().axiomes) == 22      # frontiere intacte
'''


def main(argv):
    rest = argv[1:]
    top = 20
    if "--top" in rest:
        i = rest.index("--top")
        top = int(rest[i + 1])
        rest = rest[:i] + rest[i + 2:]
    packages = [a for a in rest if not a.startswith("--")] or PACKAGES

    print("# promotion des decouvertes en lemmes nommes certifies", file=sys.stderr)
    impls, connus = _corpus_plein(packages)
    trouves = _decouvrir_transit(impls, connus)
    print(f"# {len(impls)} implications ; {len(trouves)} decouvertes distinctes par transitivite")

    def score(d):
        m1, n1, m2, n2, thm = d
        return _interet("transit.", f"{m1.split('.')[-1]}.{n1}", f"{m2.split('.')[-1]}.{n2}", thm)
    sel = sorted(trouves, key=score, reverse=True)[:top]

    _DEST.mkdir(parents=True, exist_ok=True)
    (_DEST / "__init__.py").write_text("", encoding="utf-8")
    (_DEST / "lemmes_decouverts.py").write_text(_emettre(sel), encoding="utf-8")
    (_DEST / "test_lemmes_decouverts.py").write_text(_TEST, encoding="utf-8")
    print(f"# ecrit {len(sel)} lemmes -> outils_ia/decouvertes/lemmes_decouverts.py (+ test)")
    print("# top 3 promus :")
    for k, (m1, n1, m2, n2, thm) in enumerate(sel[:3]):
        st = _fmt(thm.conclusion)
        print(f"#   lemme_{k} : {st[:96] + '...' if len(st) > 96 else st}   [{n1} o {n2}]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
