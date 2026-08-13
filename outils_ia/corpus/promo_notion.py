#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Promotion d'un motif anti-unifié en TACTIQUE dérivée + GATE noyau (MDL) — JALON 1 (suite).

Ferme la boucle SLEEP-abstraction : `antiunif_notions` DÉTECTE les slots d'une macro ; ici on
la PROMEUT en tactique nommée et on la VALIDE par compression kernel-safe. Pour une macro
récurrente (≥2 preuves), l'organe :

  1. calcule les PARAMÈTRES de la notion = entrées libres du bloc (variables proof-locales lues
     mais non assignées dedans → `p0,p1,…`) ∪ slots (globales divergentes → `SLOT0,…`) ;
     les locales assignées dans le bloc → `_v0,…` (internes), rendues en sortie ;
  2. ÉMET une tactique dérivée `notion_…(p…, SLOT…)` = le template anti-unifié + un `return`
     du tuple des `_v` ; c'est un LEMME/bloc réutilisable, PAS un axiome → frontière 22 intacte ;
  3. GATE = pour CHAQUE preuve-source, on réécrit le bloc de L pas en UN appel à la tactique, on
     RE-EXÉCUTE au noyau (`_statut`) et on exige `OK` (conclusion == cible) ; on mesure le gain
     MDL (pas économisés − coût de la tactique). On ne garde la notion QUE si TOUTES les preuves
     re-passent (zéro théorème faux) ET si le corpus rétrécit strictement.

DRY-RUN (préflight) : on ne MUTE PAS `bourbaki/` — on reconstruit la preuve réécrite en mémoire
et on la re-vérifie. C'est le préflight de l'outil transactionnel : prouver le gain + zéro casse
AVANT toute écriture. La mutation réelle du dépôt (avec rollback) est l'étape suivante.

Outillage seulement (outils_ia/) ; le noyau reste seul juge ; aucun Theoreme forgé.
USAGE : python outils_ia/corpus/promo_notion.py [package…] [--essais N] [--montre K]
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

from repair_learned import _fn_principale, _n_args, _assignes            # noqa: E402
from antiunif_notions import _Rename, _antiunify_block, _dedup, _renum, NS  # noqa: E402
from proto_mutation_verify import _rebuild, _cible_de, _instances_de     # noqa: E402
from gen_paires_corruption import _statut, _statut_parametre            # noqa: E402

PACKAGES = ["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"]
_SLOT_RE = re.compile(r"^SLOT\d+$")
_VLOC_RE = re.compile(r"^_v\d+$")
_IDENT = re.compile(r"[^0-9a-zA-Z_]")


# ---------------------------------------------------------------- extraction (avec positions)
def _theoremes(modname):
    try:
        mod = importlib.import_module(modname)
    except Exception:
        return []
    out = []
    for name in getattr(mod, "__all__", []):
        if name.endswith("_cible") or name.endswith("_instances"):
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
        if len(stmts) < 2:
            continue
        sigs = [(_fn_principale(s), _n_args(s)) for s in stmts]
        params = ({a.arg for a in fdef.args.args} | {a.arg for a in fdef.args.kwonlyargs}
                  | {a.arg for a in fdef.args.posonlyargs})
        assigned = set().union(*(_assignes(s) for s in stmts)) if stmts else set()
        out.append({"mod": mod, "name": name, "fdef": fdef, "start": start,
                    "stmts": stmts, "sigs": sigs, "params": params,
                    "locaux": params | assigned, "cible": _cible_de(mod, name),
                    "instances": _instances_de(mod, name)})
    return out


def _assignes_ord(block):
    order, seen = [], set()
    for s in block:
        for node in ast.walk(s):
            if isinstance(node, ast.Assign):
                for tgt in node.targets:
                    for nm in ast.walk(tgt):
                        if isinstance(nm, ast.Name) and nm.id not in seen:
                            seen.add(nm.id)
                            order.append(nm.id)
    return order


def _entrees_ord(block, locaux, assignes_bloc):
    """Variables LUES dans le bloc, proof-locales, non assignées dans le bloc (= entrées)."""
    order, seen = [], set()
    for s in block:
        for node in ast.walk(s):
            if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                    and node.id in locaux and node.id not in assignes_bloc
                    and node.id not in seen):
                seen.add(node.id)
                order.append(node.id)
    return order


# ---------------------------------------------------------------- construction de la tactique
def _canon_promo(block, assignes, entrees):
    m = {nm: f"_v{k}" for k, nm in enumerate(assignes)}
    m.update({nm: f"p{k}" for k, nm in enumerate(entrees)})
    return [_Rename(m).visit(copy.deepcopy(s)) for s in block]


def _construire(instances, nom):
    """instances = [(th, i, L, assignes, entrees, block)]. → (tactic_src, n_entrees, slots_raw, mapping, uniq, n_v) ou None."""
    ref_a, ref_e = instances[0][3], instances[0][4]
    if any(len(x[3]) != len(ref_a) or len(x[4]) != len(ref_e) for x in instances):
        return None
    canon = [_canon_promo(b, a, e) for (_, _, _, a, e, b) in instances]
    tmpl, slots_raw = _antiunify_block(canon)
    if tmpl is None:                    # divergence non-slotable (opérateur) → pas une notion
        return None
    # Validation des slots (autopsie GP9, tour #11) : un slot doit être une
    # EXPRESSION évaluable AU SITE D'APPEL. Refusés : (a) les non-expressions
    # (imports paresseux capturés) ; (b) les slots référençant un `_v{k}` =
    # résultat INTERNE du bloc — l'argument dépendrait de ce que la notion
    # doit elle-même calculer (« cannot access local variable », ~30 candidates).
    for vals in slots_raw:
        for val in vals:
            try:
                arbre = ast.parse(val, mode="eval")
            except SyntaxError:
                return None
            if any(isinstance(n, ast.Name) and _VLOC_RE.match(n.id)
                   for n in ast.walk(arbre)):
                return None
    uniq, mapping = _dedup(slots_raw)
    tmpl = _renum(tmpl, mapping)
    n_v = len(ref_a)
    ret = ast.Return(value=ast.Tuple(
        elts=[ast.Name(id=f"_v{k}", ctx=ast.Load()) for k in range(n_v)], ctx=ast.Load()))
    args = ([ast.arg(arg=f"p{k}") for k in range(len(ref_e))]
            + [ast.arg(arg=f"SLOT{j}") for j in range(len(uniq))])
    fn = ast.FunctionDef(name=nom, args=ast.arguments(
        posonlyargs=[], args=args, vararg=None, kwonlyargs=[], kw_defaults=[],
        kwarg=None, defaults=[]), body=tmpl + [ret], decorator_list=[], returns=None)
    src = ast.unparse(ast.fix_missing_locations(ast.Module(body=[fn], type_ignores=[])))
    return src, len(ref_e), slots_raw, mapping, uniq, n_v


def _slot_exprs(slots_raw, mapping, uniq, t):
    """Valeurs (AST) des slots uniques pour l'instance t, dans l'ordre unique."""
    rep = {}
    for old, new in mapping.items():
        rep.setdefault(new, old)
    out = []
    for u in range(len(uniq)):
        val = slots_raw[rep[u]][t]
        out.append(ast.parse(val, mode="eval").body)
    return out


def _gate(instances, nom, tactic_src, n_ent, slots_raw, mapping, uniq):
    """Réécrit chaque preuve (bloc→appel), re-vérifie au noyau. → (tous_ok, details)."""
    details = []
    for t, (th, i, L, assignes, entrees, block) in enumerate(instances):
        cible_names = _assignes_ord(block)                 # orig, ordre = _v0.._v{n-1}
        # Les slots ont été capturés APRÈS canonicalisation (p{k}/_v{k}) ; au site
        # d'appel ces noms n'existent pas (NameError p1, mesuré GP7 tour #9) —
        # on les renomme vers les noms RÉELS de l'instance (inverse de _canon_promo).
        inv = {f"p{k}": e for k, e in enumerate(entrees)}
        inv.update({f"_v{k}": a for k, a in enumerate(assignes)})
        slot_asts = [_Rename(inv).visit(x)
                     for x in _slot_exprs(slots_raw, mapping, uniq, t)]
        call = ast.Call(func=ast.Name(id=nom, ctx=ast.Load()),
                        args=[ast.Name(id=e, ctx=ast.Load()) for e in entrees]
                        + slot_asts, keywords=[])
        if cible_names:
            appel = ast.Assign(
                targets=[ast.Tuple(elts=[ast.Name(id=nm, ctx=ast.Store())
                                         for nm in cible_names], ctx=ast.Store())],
                value=call)
        else:                       # bloc sans affectation (asserts seuls) :
            appel = ast.Expr(value=call)   # `() = f()` serait un SyntaxError (tour #9)
        new_stmts = th["stmts"][:i] + [appel] + th["stmts"][i + L:]
        new_body = th["fdef"].body[:th["start"]] + new_stmts
        proof_src = _rebuild(th["fdef"], new_body)
        combined = tactic_src + "\n\n" + proof_src
        try:
            if th["cible"] is not None:
                statut = _statut(th["mod"], th["name"], combined, th["cible"])
            else:                       # prouveur paramétré : instances canoniques
                statut = _statut_parametre(th["mod"], th["name"], combined,
                                           th["instances"])
        except Exception:
            statut = "ERROR"
        details.append((th["name"], statut))
    return all(s == "OK" for _, s in details), details


# ---------------------------------------------------------------- pilote
def _nom(ng, idx):
    base = next((fn for fn, _ in ng if fn not in ("var", "_t")), ng[0][0])
    return f"notion_{_IDENT.sub('_', base)}_{len(ng)}p_{idx}"


def _candidats(ths):
    idx = defaultdict(dict)
    for th in ths:
        for n in NS:
            for i in range(len(th["sigs"]) - n + 1):
                ng = tuple(th["sigs"][i:i + n])
                idx[ng].setdefault(th["name"], (th, i, n))       # 1 instance / preuve
    cands = []
    for ng, par in idx.items():
        if len(par) < 2:
            continue
        # Une instance non gatable (cible None — prouveur paramétré — ou bloc
        # contenant un Return) ÉCARTE l'instance, pas la candidate : sur un
        # corpus majoritairement paramétré (îlot Goldbach : 36/43), le
        # tout-ou-rien stérilisait chaque motif (mesuré le 7 août, tour #3 à 0).
        # La notion reste certifiée sur le sous-ensemble gatable (≥2 instances).
        insts = []
        for (th, i, L) in par.values():
            block = th["stmts"][i:i + L]
            gatable = th["cible"] is not None or th["instances"]
            if not gatable or any(isinstance(x, ast.Return) for s in block
                                  for x in ast.walk(s)):
                continue
            a = _assignes_ord(block)
            e = _entrees_ord(block, th["locaux"], set(a))
            insts.append((th, i, L, a, e, block))
        if len(insts) >= 2:
            cands.append((ng, insts))
    cands.sort(key=lambda c: -(len(c[0]) * len(c[1])))          # gain potentiel
    return cands


def _scan(packages):
    """Découvre les modules sous `packages` et renvoie leurs théorèmes gatables."""
    import pkgutil
    modules = []
    for pkg in packages:
        try:
            p = importlib.import_module(pkg)
            for info in pkgutil.walk_packages(p.__path__, pkg + "."):
                if not info.ispkg and "__pycache__" not in info.name:
                    modules.append(info.name)
        except Exception:
            pass
    ths = []
    for m in sorted(set(modules)):
        ths.extend(_theoremes(m))
    return ths


def promouvoir(ths, essais):
    """Scanne les candidates, promeut celles qui passent le gate noyau + gain MDL.

    Renvoie (acceptes, funnel, n_cands). Chaque accepté porte `insts_meta` =
    [(modname, theoreme, i, L)] = l'empreinte de la notion sur le corpus (pour le volant)."""
    cands = _candidats(ths)
    acceptes = []
    funnel = {"none": 0, "gate_fail": 0, "gain_nul": 0, "ok": 0}
    # `essais` borne les passages au GATE (coûteux : exec + re-preuve noyau) ;
    # un refus de construction est GRATUIT et ne consomme plus le budget
    # (8 août 2026 : avant, 346 none sur 553 mangeaient les essais des viables).
    essais_gate = 0
    for k, (ng, insts) in enumerate(cands):
        if essais_gate >= essais:
            break
        nom = _nom(ng, k)
        built = _construire(insts, nom)
        if built is None:
            funnel["none"] += 1
            continue
        essais_gate += 1
        tactic_src, n_ent, slots_raw, mapping, uniq, n_v = built
        try:
            tous_ok, details = _gate(insts, nom, tactic_src, n_ent, slots_raw, mapping, uniq)
        except Exception:
            funnel["gate_fail"] += 1
            continue
        gain = sum(L - 1 for (_, _, L, _, _, _) in insts) - (insts[0][2] + 2)
        if not tous_ok:
            funnel["gate_fail"] += 1
        elif gain <= 0:
            funnel["gain_nul"] += 1
        if tous_ok and gain > 0:
            funnel["ok"] += 1
            acceptes.append({"ng": ng, "nom": nom, "npr": len(insts), "gain": gain,
                             "n_ent": n_ent, "n_slot": len(uniq), "src": tactic_src,
                             "details": details,
                             "insts_meta": [(th["mod"].__name__, th["name"], i, L)
                                            for (th, i, L, _, _, _) in insts]})
    acceptes.sort(key=lambda a: -a["gain"])
    return acceptes, funnel, len(cands)


def main(argv):
    rest = argv[1:]

    def opt(flag, dv):
        if flag in rest:
            return int(rest[rest.index(flag) + 1])
        return dv
    essais, montre = opt("--essais", 60), opt("--montre", 8)
    packages = [a for a in rest if not a.startswith("--")
                and not a.isdigit()] or PACKAGES

    ths = _scan(packages)
    print(f"# promo_notion : {len(ths)} théorèmes gatables sous {packages}", file=sys.stderr)
    acceptes, funnel, n_cands = promouvoir(ths, essais)
    print(f"# {n_cands} macros candidates (≥2 preuves, cible connue, sans return)")
    print(f"# funnel sur {min(essais, n_cands)} essais : {funnel['none']} désalignées, "
          f"{funnel['gate_fail']} gate-fail, {funnel['gain_nul']} gain≤0, {funnel['ok']} PROMUES")
    print(f"\n# {len(acceptes)} notion(s) PROMUE(S) — gate noyau OK (0 théorème faux) + gain MDL > 0\n")
    for a in acceptes[:montre]:
        preuves = ", ".join(n for n, _ in a["details"])
        print(f"■ {a['nom']}  [{a['npr']} preuves, {a['n_ent']} entrée(s)+{a['n_slot']} slot(s), "
              f"gain MDL≈{a['gain']} pas]")
        print(f"  re-prouve identiquement (noyau OK) : {preuves}")
        for ligne in a["src"].splitlines():
            print(f"      {ligne}")
        print()
    tot = sum(a["gain"] for a in acceptes)
    print(f"# GAIN MDL total des notions promues : ≈{tot} pas économisés, corpus strictement "
          f"plus court, zéro théorème faux (noyau juge).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
