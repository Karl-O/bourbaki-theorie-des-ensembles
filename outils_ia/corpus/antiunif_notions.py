#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Anti-unificateur de motifs de preuve → DÉTECTE les slots d'une notion (JALON 1).

Organe SLEEP-abstraction du volant wake-sleep (design multi-agent 2026-07-01). C'est le
DUAL EXACT du remplisseur-de-slots du TreeNN : le TreeNN *remplit* les slots d'un motif ;
ici on les *DÉTECTE*. Entrée = une MACRO récurrente (n-gramme (fn,arité) miné par
`proto_library_learning`, ≥2 preuves) avec ses INSTANCES concrètes (les blocs de L pas).
Sortie = l'anti-unification (least-general generalization) : un TEMPLATE où les positions
qui CONCORDENT sur toutes les instances sont fixées et où les positions qui DIVERGENT
deviennent des SLOTS = les paramètres de la notion candidate, plus les valeurs par instance.

POURQUOI c'est la brique manquante (mesuré pas 16-suite) : les macros ne sont PAS copiables
verbatim (~0 %) car leurs instances diffèrent au niveau des feuilles-termes (littéraux
'x'/'y', objets pr1z/pr2z). L'anti-unification transforme cette divergence en PARAMÈTRES
nommés → un motif non-copiable devient un TEMPLATE réutilisable. Étape préalable à la
promotion en tactique dérivée + gate MDL (kernel-safe, frontière 22 axiomes intacte).

Deux précautions rendent l'alignement fidèle :
  1. α-NORMALISATION des variables LOCALES au bloc (cibles d'affectation) → `_v0, _v1, …`
     par ordre d'apparition, sinon les noms de dataflow (hsec, comp…) diverges parasitent
     tout. Les noms LUS mais assignés HORS du bloc restent tels quels = candidats-slots.
  2. anti-unification STRUCTURELLE générique (via ast.iter_fields) : même type + mêmes
     champs primitifs + mêmes longueurs d'enfants → on récurse ; sinon → un slot absorbe
     la divergence (au bon grain : un sous-terme, pas tout le pas, quand la structure tient).

Outillage seulement (outils_ia/) : analyse AST PURE, aucun exec-noyau ; ne fabrique aucun
Theoreme ; ne touche pas la frontière de confiance.
USAGE : python outils_ia/corpus/antiunif_notions.py [package1 package2 ...] [--top K]
"""
from __future__ import annotations

import ast
import copy
import importlib
import inspect
import re
import sys
import textwrap
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from export_corpus import _decouvrir                       # noqa: E402
from repair_learned import _fn_principale, _n_args         # noqa: E402

PACKAGES = ["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"]      # rapides (PAS cardinaux/entiers)
NS = (2, 3, 4)                                              # longueurs de macro
_SLOT_RE = re.compile(r"^SLOT\d+$")


# ---------------------------------------------------------------- extraction du corpus
def _preuves_corps(modname):
    """(pid, module_court, suite (fn,arité), liste de stmts) par fonction-théorème."""
    try:
        mod = importlib.import_module(modname)
    except Exception:
        return []
    court = modname.split(".")[-1]
    out = []
    for name in getattr(mod, "__all__", []):
        if name.endswith("_cible"):
            continue
        fn = getattr(mod, name, None)
        if not callable(fn):
            continue
        try:
            fdef = ast.parse(textwrap.dedent(inspect.getsource(fn))).body[0]
        except Exception:
            continue
        if not isinstance(fdef, ast.FunctionDef):
            continue
        body = fdef.body
        start = 1 if (body and isinstance(body[0], ast.Expr)
                      and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
        stmts = body[start:]
        sigs = [(_fn_principale(s), _n_args(s)) for s in stmts]
        if len(sigs) >= 2:
            out.append((f"{court}.{name}", court, sigs, stmts))
    return out


def _indexer(preuves):
    """n-gramme (fn,arité) → liste d'instances (pid, module, bloc de L stmts)."""
    idx = defaultdict(list)
    for pid, mod, sigs, stmts in preuves:
        for n in NS:
            for i in range(len(sigs) - n + 1):
                ng = tuple(sigs[i:i + n])
                idx[ng].append((pid, mod, stmts[i:i + n]))
    return idx


# ---------------------------------------------------------------- α-normalisation locale
def _noms_assignes(stmts):
    """Noms assignés DANS le bloc (dataflow local), par ordre de 1ʳᵉ apparition-cible."""
    order, seen = [], set()
    for s in stmts:
        for node in ast.walk(s):
            if isinstance(node, ast.Assign):
                for tgt in node.targets:
                    for nm in ast.walk(tgt):
                        if isinstance(nm, ast.Name) and nm.id not in seen:
                            seen.add(nm.id)
                            order.append(nm.id)
    return order


class _Rename(ast.NodeTransformer):
    def __init__(self, m):
        self.m = m

    def visit_Name(self, node):
        if node.id in self.m:
            return ast.copy_location(ast.Name(id=self.m[node.id], ctx=node.ctx), node)
        return node


def _canon(stmts):
    """Copie du bloc avec les locales renommées `_v{k}` (alignement inter-instances)."""
    m = {nm: f"_v{k}" for k, nm in enumerate(_noms_assignes(stmts))}
    return [_Rename(m).visit(copy.deepcopy(s)) for s in stmts]


# ---------------------------------------------------------------- anti-unification
class _NonSlotable(Exception):
    """Divergence à une position NON-EXPRESSION (opérateur, contexte) : un slot est
    un `Name`, l'y mettre fabrique un AST invalide (KeyError 'Name' dans unparse,
    mesuré au tour #8 sur somme_num `+` vs produit_num `*`). On refuse proprement."""


_NON_SLOTABLE = (ast.operator, ast.boolop, ast.unaryop, ast.cmpop, ast.expr_context)


def _slot(nodes, slots):
    if any(isinstance(n, _NON_SLOTABLE) for n in nodes):
        raise _NonSlotable
    vals = [ast.unparse(n) if isinstance(n, ast.AST) else repr(n) for n in nodes]
    slots.append(vals)
    return ast.Name(id=f"SLOT{len(slots) - 1}", ctx=ast.Load())


def _au(nodes, slots):
    """Anti-unifie une colonne de nœuds parallèles ; renvoie le template (slots ← divergences)."""
    first = nodes[0]
    if not isinstance(first, ast.AST):
        return first if all(n == first for n in nodes) else _slot(nodes, slots)
    if not all(isinstance(n, ast.AST) and type(n) is type(first) for n in nodes):
        return _slot(nodes, slots)
    for f, v0 in ast.iter_fields(first):
        vals = [getattr(n, f, None) for n in nodes]
        if isinstance(v0, ast.AST):
            if not all(isinstance(v, ast.AST) for v in vals):
                return _slot(nodes, slots)
        elif isinstance(v0, list):
            if not all(isinstance(v, list) and len(v) == len(v0) for v in vals):
                return _slot(nodes, slots)
        else:
            if not all(v == v0 for v in vals):
                return _slot(nodes, slots)
    kids = {}
    for f, v0 in ast.iter_fields(first):
        vals = [getattr(n, f, None) for n in nodes]
        if isinstance(v0, ast.AST):
            kids[f] = _au(vals, slots)
        elif isinstance(v0, list):
            kids[f] = [_au([v[j] for v in vals], slots) for j in range(len(v0))]
        else:
            kids[f] = v0
    return ast.copy_location(type(first)(**kids), first)


def _antiunify_block(instances):
    """Anti-unifie L pas × N instances → (template stmts, slots bruts).

    → (None, None) si une divergence tombe à une position non-slotable
    (opérateur : le motif somme/produit n'est PAS une notion, c'est deux lois)."""
    slots, tmpl = [], []
    try:
        for k in range(len(instances[0])):
            node = _au([inst[k] for inst in instances], slots)
            if not isinstance(node, ast.stmt):
                node = ast.Expr(value=node)
            tmpl.append(node)
    except _NonSlotable:
        return None, None
    return tmpl, slots


def _dedup(slots):
    """Fusionne les slots aux valeurs identiques (même argument réutilisé) → (uniques, map)."""
    uniq, order, mapping = {}, [], {}
    for old, vals in enumerate(slots):
        key = tuple(vals)
        if key not in uniq:
            uniq[key] = len(order)
            order.append(vals)
        mapping[old] = uniq[key]
    return order, mapping


def _renum(tmpl, mapping):
    class _R(ast.NodeTransformer):
        def visit_Name(self, node):
            m = _SLOT_RE.match(node.id)
            if m:
                return ast.copy_location(
                    ast.Name(id=f"SLOT{mapping[int(node.id[4:])]}", ctx=node.ctx), node)
            return node
    return [_R().visit(s) for s in tmpl]


def _sizes(tmpl):
    total = nslot = 0
    for s in tmpl:
        for node in ast.walk(s):
            total += 1
            if isinstance(node, ast.Name) and _SLOT_RE.match(node.id):
                nslot += 1
    return total, nslot


def _fmt_sig(ng):
    return " → ".join(f"{fn}/{a}" for fn, a in ng)


# ---------------------------------------------------------------- pilote
def analyser(macros):
    """Anti-unifie chaque macro (1 instance/preuve distincte) ; renvoie toutes les fiches."""
    fiches = []
    for ng, par_preuve, npr, nmod in macros:
        instances = [_canon(b) for (_, b) in par_preuve.values()]
        tmpl, slots = _antiunify_block(instances)
        if tmpl is None:                # divergence non-slotable → pas une notion
            continue
        uniq, mapping = _dedup(slots)
        tmpl = _renum(tmpl, mapping)
        total, nslot = _sizes(tmpl)
        fiches.append({"ng": ng, "npr": npr, "nmod": nmod, "tmpl": tmpl, "uniq": uniq,
                       "ratio": nslot / max(total, 1), "total": total,
                       "nslot": len(uniq), "gain": len(ng) * npr})
    return fiches


def _imprimer(f):
    print(f"■ macro L={len(f['ng'])} [{f['npr']} preuves / {f['nmod']} mod, gain≈{f['gain']}] "
          f"{_fmt_sig(f['ng'])}")
    print(f"  ratio-slots {f['ratio']:.2f} ({f['nslot']} paramètre(s) / {f['total']} nœuds)")
    tmpl_src = ast.unparse(ast.fix_missing_locations(
        ast.Module(body=f["tmpl"], type_ignores=[])))
    print("  TEMPLATE :")
    for ligne in tmpl_src.splitlines():
        print(f"      {ligne}")
    for j, vals in enumerate(f["uniq"]):
        apercu = " | ".join(dict.fromkeys(vals))
        if len(apercu) > 150:
            apercu = apercu[:147] + "…"
        print(f"      SLOT{j} = {apercu}")
    print()


def main(argv):
    rest = argv[1:]
    limite = 8
    if "--top" in rest:
        i = rest.index("--top")
        limite = int(rest[i + 1])
        rest = rest[:i] + rest[i + 2:]
    packages = [a for a in rest if not a.startswith("--")] or PACKAGES
    modules = _decouvrir(packages)
    print(f"# anti-unif : {len(modules)} modules sous {packages}", file=sys.stderr)

    preuves = []
    for m in modules:
        preuves.extend(_preuves_corps(m))
    idx = _indexer(preuves)

    macros = []
    for ng, insts in idx.items():
        par_preuve = {}
        for pid, mod, block in insts:
            par_preuve.setdefault(pid, (mod, block))       # 1 instance / preuve distincte
        if len(par_preuve) >= 2:
            nmod = len({mod for mod, _ in par_preuve.values()})
            macros.append((ng, par_preuve, len(par_preuve), nmod))
    print(f"# {len(preuves)} preuves | {len(macros)} macros inter-preuves (≥2 preuves distinctes)")

    fiches = analyser(macros)
    histo = defaultdict(int)
    for f in fiches:
        histo[f["nslot"]] += 1
    print("# histogramme #paramètres : " + ", ".join(
        f"{k}→{histo[k]}" for k in sorted(histo)))

    verbatim = sorted((f for f in fiches if f["nslot"] == 0),
                      key=lambda f: (-f["gain"], -f["nmod"]))
    param = sorted((f for f in fiches if 1 <= f["nslot"] <= 6),
                   key=lambda f: (f["ratio"], -f["gain"], -f["nmod"]))

    print(f"\n=== A. SOUS-ROUTINES VERBATIM (0 paramètre) — plus fort gain MDL, promotion la plus sûre ===\n")
    for f in verbatim[:limite]:
        _imprimer(f)
    print(f"=== B. NOTIONS PARAMÉTRÉES (1–6 paramètres) — la vraie invention (une famille nommée) ===\n")
    for f in param[:limite]:
        _imprimer(f)
    print("# = paramètres détectés d'une notion candidate → promotion en tactique dérivée + gate MDL (étape suivante).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
