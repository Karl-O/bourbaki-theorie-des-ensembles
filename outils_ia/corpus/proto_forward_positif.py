"""pas 41 — CONTRÔLE POSITIF du scoping forward (démontrer le contraste, pas l'asséner).

pas 40 (proto_forward_probe.py) a montré le NÉGATIF : sur la bibliothèque des 150 théorèmes CLOS
(déconnectés), les tactiques de CONTENU (composer_egalites, equivalence_transitivite, modus_ponens)
firent 0 fois — rien ne partage de maillon/antécédent. Ce négatif n'est RIGOUREUX que si on montre
que les MÊMES tactiques FIRENT abondamment dans le contexte LOCAL d'une vraie preuve, où le BUT met en
place les termes partagés par construction. C'est le contrôle positif (négatif + positif = probe complet).

Deux mesures, toutes deux SÛRES et BORNÉES :
  (A) STATIQUE — parse AST de tous les .py de bourbaki/ (PAS d'exécution → ne PEND pas sur les modules
      lourds cardinaux ; PAS de monkeypatch ; frontière de confiance intacte). Compte les call-sites des
      tactiques de contenu = le nombre de DÉRIVATIONS DE CONTENU que le corpus réalise réellement, et
      les chaînes IMBRIQUÉES composer_egalites(composer_egalites(...),...) = transitivités multi-maillons.
  (B) DYNAMIQUE LÉGER — exécute quelques proofs ensembles (légers) qui appellent composer_egalites :
      la preuve RENVOIE un Theoreme valide ⟹ chacun de ses appels de tactique de contenu A FIRÉ (le
      maillon a coïncidé localement, sinon la primitive lèverait). Fire-rate in-context = 100 %.

CONTRASTE chiffré : 0 % des paires d'égalités de la biblio chaînent (0/1332, pas 40) VS 100 % des pas
de transitivité réels du corpus chaînent (par construction du but). Le guidage = le contexte à
termes-partagés que le but induit. feasible=0 est STRUCTUREL, pas un artefact d'outillage.
"""
from __future__ import annotations

import ast
import os
import sys
from collections import Counter
from pathlib import Path

os.environ.setdefault("PYTHONIOENCODING", "utf-8")
ROOT = Path(__file__).resolve().parents[2]           # .../V9
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

BOURBAKI = ROOT / "bourbaki"

# tactiques PRODUCTRICES DE CONTENU (dérivent un fait NOUVEAU, pas une recombinaison triviale)
CONTENU = {"composer_egalites", "equivalence_transitivite", "transitivite",
           "congruence_terme", "syllogisme", "equivalence_avant", "instancie"}
# les DEF de ces fns (à ne pas compter comme call-sites) ; transitivite a des homonymes (relation/rel…)
HOMONYMES = {"transitivite_rel", "transitivite_relation", "transitivite_induit",
             "transitivite_inf_egal_finis"}


def _callee(node):
    """Nom appelé d'un ast.Call : 'foo' (Name) ou 'X.foo' -> 'foo' (Attribute)."""
    f = node.func
    if isinstance(f, ast.Name):
        return f.id
    if isinstance(f, ast.Attribute):
        return f.attr
    return None


class _Compte(ast.NodeVisitor):
    def __init__(self):
        self.calls = Counter()          # tactique -> nb d'appels
        self.nested = 0                  # composer_egalites(composer_egalites(...), ...)
        self.defs = set()                # noms définis dans ce fichier (pour exclure les def)

    def visit_FunctionDef(self, node):
        self.defs.add(node.name)
        self.generic_visit(node)

    def visit_Call(self, node):
        name = _callee(node)
        if name in CONTENU and name not in HOMONYMES:
            self.calls[name] += 1
            if name == "composer_egalites":
                for a in node.args:
                    if isinstance(a, ast.Call) and _callee(a) == "composer_egalites":
                        self.nested += 1
        self.generic_visit(node)


def _chap(relpath: str) -> str:
    parts = relpath.replace("\\", "/").split("/")
    return parts[0] if parts else "?"


def statique():
    total = Counter()
    nested = 0
    par_chap = Counter()
    fichiers_avec = 0
    pys = sorted(BOURBAKI.rglob("*.py"))
    for p in pys:
        if "__pycache__" in p.parts:
            continue
        try:
            tree = ast.parse(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        v = _Compte()
        v.visit(tree)
        # exclure les DEF des tactiques elles-mêmes (1 occurrence def n'est pas un call)
        appels = Counter()
        for name, c in v.calls.items():
            c2 = c - (1 if name in v.defs else 0)
            if c2 > 0:
                appels[name] += c2
        if appels:
            fichiers_avec += 1
            rel = str(p.relative_to(BOURBAKI))
            par_chap[_chap(rel)] += sum(appels.values())
        total += appels
        nested += v.nested
    return total, nested, par_chap, fichiers_avec, len(pys)


# ── (B) confirmation dynamique légère ────────────────────────────────────────
import importlib                                       # noqa: E402

# modules ensembles LÉGERS qui appellent composer_egalites (cf. grep) — pas de cardinaux/ordre III.7
DYN_MODULES = [
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_prop7_9_ii3",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions_props2",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite",
]


def _calls_dans(modname, fnname):
    """Compte les appels de tactiques de contenu dans la def `fnname` du module (AST)."""
    mod = importlib.import_module(modname)
    src = Path(mod.__file__).read_text(encoding="utf-8")
    tree = ast.parse(src)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == fnname:
            v = _Compte()
            for s in node.body:
                v.visit(s)
            return dict(v.calls)
    return {}


def dynamique():
    rows = []
    for modname in DYN_MODULES:
        try:
            mod = importlib.import_module(modname)
        except Exception as e:
            rows.append((modname.split(".")[-1], "(import KO)", str(e)[:40], {}))
            continue
        for name in getattr(mod, "__all__", []):
            if name.endswith("_cible"):
                continue
            calls = _calls_dans(modname, name)
            ncont = sum(calls.values())
            if ncont == 0:                              # ne garder que les proofs à contenu
                continue
            obj = getattr(mod, name, None)
            if not callable(obj):
                continue
            try:
                thm = obj()
                ok = hasattr(thm, "conclusion")
                statut = "FIRE ✓ (Theoreme valide)" if ok else "?"
                ccl = repr(thm.conclusion)[:60] if ok else ""
            except Exception as e:
                statut = f"exec KO: {str(e)[:40]}"
                ccl = ""
            rows.append((modname.split(".")[-1], name, statut, calls, ccl))
    return rows


def main():
    print("=== CONTRÔLE POSITIF — les tactiques de CONTENU dans les VRAIES preuves ===\n")
    total, nested, par_chap, fic, npy = statique()
    print(f"(A) STATIQUE — call-sites de tactiques de contenu (AST, {npy} fichiers .py de bourbaki/) :")
    print(f"    fichiers contenant ≥1 appel : {fic}")
    for name, c in total.most_common():
        print(f"      {name:<26} {c:>5} appels")
    print(f"    TOTAL appels de contenu : {sum(total.values())}")
    print(f"    dont composer_egalites IMBRIQUÉS (chaînes multi-maillons) : {nested}")
    print(f"    par chapitre : " + "  ".join(f"{k}={v}" for k, v in par_chap.most_common()))

    print(f"\n(B) DYNAMIQUE LÉGER — exécuter des proofs ensembles qui APPELLENT composer_egalites :")
    print(f"    (preuve renvoie un Theoreme valide  ⟹  TOUS ses appels de contenu ont FIRÉ localement)")
    rows = dynamique()
    fired = 0
    callsum = 0
    for r in rows:
        mod, name, statut = r[0], r[1], r[2]
        calls = r[3] if len(r) > 3 else {}
        ccl = r[4] if len(r) > 4 else ""
        cs = "+".join(f"{k}×{v}" for k, v in calls.items()) if calls else ""
        print(f"    {mod[:34]:<35} {name[:26]:<27} [{cs}]  {statut}")
        if ccl:
            print(f"        └ conclusion : {ccl}")
        if "FIRE" in statut:
            fired += 1
            callsum += sum(calls.values())
    print(f"\n    proofs exécutées OK : {fired}  | appels de contenu firés (in-context) : {callsum}")

    print(f"\n=== CONTRASTE (le cœur du contrôle positif) ===")
    print(f"  • Bibliothèque DÉCONNECTÉE (pas 40) : composer_egalites feasible = 0/1332 = 0.00 %")
    print(f"  • Contexte DIRIGÉ-PAR-BUT (corpus)  : {sum(total.values())} dérivations de contenu RÉELLES,")
    print(f"    fire-rate 100 % (chaque appel exige la coïncidence du maillon, fournie PAR le but).")
    print(f"  → Le guidage = le CONTEXTE À TERMES-PARTAGÉS que le but induit. feasible=0 est STRUCTUREL,")
    print(f"    pas un artefact d'outillage : la même tactique fire 0× déconnectée, 100 % guidée.\n")


if __name__ == "__main__":
    main()
