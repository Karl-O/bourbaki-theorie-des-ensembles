#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""FAIT ou PARTIEL — croiser les marqueurs ``@livre`` avec le VERDICT DU NOYAU.

LE MANQUE QUE CET OUTIL COMBLE. Le dépôt sait dire, 2187 fois, « cette notion
du livre est formalisée et marquée ». Il ne sait PAS dire « cette notion est
DÉMONTRÉE ». Or c'est la question du projet, mot pour mot :

    « démontré dans le livre » doit coïncider avec « vérifié par la machine ».

Sans ce croisement, le taux de couverture mesure la **diligence de
l'annotation**, pas la vérité mathématique — et les deux peuvent diverger sans
que rien ne le signale. `gen_livre_manifestes.py` compte les notions marquées,
`gen_trous_livre.py` trouve les lignes du livre non couvertes ; ni l'un ni
l'autre n'ouvre un `Theoreme` pour regarder s'il reste des hypothèses dedans.

════════════════════════════════════════════════════════════════════════════
DEUX SOURCES, ET C'EST LEUR DÉSACCORD QUI INTÉRESSE
════════════════════════════════════════════════════════════════════════════

(1) CE QUE LE DÉPÔT DÉCLARE — la docstring de la notion. Le vocabulaire est
    déjà là, mesuré sur l'arbre : « [CLOS] » 140 fois, « [CLOS, N hyp] » 75
    fois, « CLOS, hyps HONNÊTES » 9 fois, « REPORTÉ » une trentaine. ⚠️ Dans ce
    dépôt **CLOS ne veut donc pas dire « 0 hypothèse »** : « CLOS, 2 hyp »
    annonce une preuve close MODULO deux hypothèses. C'est exactement la
    distinction FAIT / PARTIEL de CLAUDE.md, et elle est déjà écrite.

(2) CE QUE LE NOYAU DIT — on importe le module, on appelle la fonction, on
    regarde `len(th.hypotheses)`. Zéro hypothèse = FAIT. C'est un oracle
    EXACT : le noyau ne se trompe jamais sur ce point.

Le produit utile n'est aucune des deux colonnes prise seule, c'est leur
CROISEMENT :

    · déclaré CLOS, noyau d'accord (0 hyp)   → FAIT, confirmé ;
    · déclaré CLOS, noyau trouve des hyps    → **DÉCLARATION TROP FORTE** ;
    · déclaré REPORTÉ, noyau rend 0 hyp      → **REPORT PÉRIMÉ** — le résultat
      est acquis et on risque de le refaire (4 trouvés en 24 h début août) ;
    · muet, noyau rend 0 hyp                 → acquis non déclaré.

Les deux cas en gras sont ceux qu'aucun outil du dépôt ne voit aujourd'hui.

════════════════════════════════════════════════════════════════════════════
POURQUOI L'ÉVALUATION EST OPTIONNELLE
════════════════════════════════════════════════════════════════════════════

La passe (1) est de l'AST : instantanée, toujours lancée. La passe (2) importe
et EXÉCUTE — c'est cher (les imports `cardinaux` pèsent des minutes) et ça ne
peut pas tourner à chaque commit. Elle est donc explicite (`--noyau`), bornée
par chapitre (`--chap III`), et son résultat est mis en cache JSON pour être
rejouable sans tout refaire.

⚠️ CE QUE CET OUTIL NE DÉMONTRE PAS. Il ne juge que la CLÔTURE, pas la
FIDÉLITÉ : un théorème à 0 hypothèse dont l'énoncé ne serait pas celui de
Bourbaki reste faux au sens du projet. Le noyau garantit la soundness, jamais
la fidélité — celle-là se lit dans le PDF, à la page que le `@livre` indique.

Usage :
    python outils_ia/audit/statut_notions.py                  # déclaratif seul
    python outils_ia/audit/statut_notions.py --noyau --chap I # + verdict noyau
    python outils_ia/audit/statut_notions.py --noyau --md rapport.md
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from outils_ia.audit.gen_trous_livre import collecter  # noqa: E402

#: « CLOS, 2 hyp », « CLOS (1 hyp) », « CLOS, hyps HONNÊTES », et surtout
#: « CLOS-SOUS-L'HYPOTHÈSE-HONNÊTE {…} » / « CLOS-SOUS-LES-HYPOTHÈSES-… ».
#: ⚠️ La racine « hypoth » est OBLIGATOIRE ici : une première version testait
#: `hyps?\b`, qui ne matche PAS « HYPOTHÈSE » (pas de frontière de mot après
#: « HYP »). Elle classait donc CLOS trois théorèmes dont la docstring écrit
#: noir sur blanc `hypotheses == {inclus(X,E)}` — l'outil accusait de fausse
#: déclaration les docstrings les plus honnêtes du dépôt. Construire le
#: classificateur sur une liste de fréquences TRONQUÉE au lieu du texte en
#: situ, c'est encore travailler au mauvais niveau.
#: Les TROIS formes sont nécessaires, et l'oubli de l'une se voit dans les
#: chiffres : ne garder que « hypoth » a fait REMONTER Ch.III de 115 à 122
#: CLOS — les « CLOS, hyps HONNÊTES » retombaient en CLOS sec.
_RE_CLOS_HYP = re.compile(
    r"CLOS[^.\n]{0,60}?(?:(\d+)\s*hyp|hypoth|hyps?\b)", re.I)
_RE_CLOS = re.compile(r"\bCLOS\b", re.I)
_RE_REPORTE = re.compile(r"\bREPORT[ÉE]E?S?\b", re.I)

#: cache du verdict noyau, pour ne pas repayer les imports lourds
CACHE = Path(__file__).with_name("_statut_noyau.json")


def declaration(docstring: str | None) -> tuple[str, int | None]:
    """→ (déclaration, nb d'hypothèses annoncé) lue dans la docstring.

    L'ordre des tests compte : « CLOS, 2 hyp » doit être lu comme PARTIEL, pas
    comme CLOS. On teste donc la forme la plus spécifique d'abord."""
    if not docstring:
        return "MUET", None
    m = _RE_CLOS_HYP.search(docstring)
    if m:
        return "CLOS_MODULO", int(m.group(1)) if m.group(1) else None
    if _RE_REPORTE.search(docstring):
        return "REPORTE", None
    if _RE_CLOS.search(docstring):
        return "CLOS", 0
    return "MUET", None


def docstrings_du_fichier(fichier: Path) -> dict[str, str]:
    """→ {nom de fonction: docstring} pour un module, sans l'importer."""
    try:
        arbre = ast.parse(fichier.read_text(encoding="utf-8"))
    except Exception:                                       # noqa: BLE001
        return {}
    out = {}
    for n in ast.walk(arbre):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[n.name] = ast.get_docstring(n) or ""
    return out


def passe_declarative(racine: Path) -> list[dict]:
    """Passe (1) : ce que le dépôt DÉCLARE. AST seul, aucun import."""
    marqueurs = collecter(racine)
    par_fichier: dict[Path, dict[str, str]] = {}
    lignes = []
    for m in marqueurs:
        if not m.notion or m.notion == "?":
            continue                       # marqueur sans def annoncée
        if m.fichier not in par_fichier:
            par_fichier[m.fichier] = docstrings_du_fichier(m.fichier)
        decl, nhyp = declaration(par_fichier[m.fichier].get(m.notion))
        lignes.append({
            "chap": m.chap, "type": m.type, "num": m.num, "repere": m.repere,
            "notion": m.notion, "fichier": str(m.fichier).replace("\\", "/"),
            "declaration": decl, "hyp_declarees": nhyp,
        })
    return lignes


def _module_de(chemin: str) -> str:
    return chemin[:-3].replace("/", ".")


#: types @livre qui PROMETTENT une démonstration — la question FAIT/PARTIEL
#: n'a de sens que pour eux ; Def/Rem/Ex construisent, elles n'ont rien à
#: décharger. Mélanger les deux populations, c'est diluer le seul taux qui
#: réponde à la question du projet (mesuré : 354 « NON_EVALUABLE » dont une
#: grande part était simplement… des définitions qui construisent très bien).
TYPES_DEMONTRABLES = frozenset({"Prop", "Th", "Cor", "Crit", "Lem", "Demo",
                                "Sch", "Ax"})


def est_demontrable(type_livre: str) -> bool:
    return type_livre in TYPES_DEMONTRABLES


def _classer_retour(th) -> tuple[str, int | None, str]:
    hyps = getattr(th, "hypotheses", None)
    if hyps is None:
        #   la notion CONSTRUIT un objet (Terme, formule, booléen…) : c'est le
        #   comportement attendu d'une DÉFINITION, pas un échec.
        return "CONSTRUIT", None, type(th).__name__
    return ("FAIT" if len(hyps) == 0 else "PARTIEL"), len(hyps), ""


def verdict_noyau(chemin: str, notion: str) -> tuple[str, int | None, str]:
    """Passe (2) : ce que le NOYAU dit. Importe, appelle, compte les hypothèses.

    Rend (état, nb d'hypothèses, détail). Un échec n'est jamais silencieux :
    il devient l'état NON_EVALUABLE avec sa cause, parce qu'une notion qu'on
    ne sait pas évaluer n'est PAS une notion démontrée.

    REPLI « arguments génériques » : la convention du dépôt est que les
    paramètres des constructeurs de théorèmes sont des NOMS (chaînes),
    convertis par `var()`/`_t()` à l'intérieur. Une fonction sans valeurs par
    défaut s'appelle donc en passant à chaque paramètre… son propre nom : le
    théorème obtenu est l'instance générique, qui est exactement la notion.
    Si la fonction attend de vrais objets (couche assemblage, prédicats), le
    repli échoue et l'état NON_EVALUABLE reste — jamais de faux verdict."""
    import importlib
    import inspect

    try:
        mod = importlib.import_module(_module_de(chemin))
    except Exception as e:                                  # noqa: BLE001
        return "NON_EVALUABLE", None, "import: %s" % type(e).__name__
    fn = getattr(mod, notion, None)
    if fn is None:
        return "NON_EVALUABLE", None, "absente du module"
    if not callable(fn):
        return "NON_EVALUABLE", None, "non appelable"
    try:
        return _classer_retour(fn())
    except TypeError:
        pass                                   # → repli arguments génériques
    except Exception as e:                                  # noqa: BLE001
        return "NON_EVALUABLE", None, "appel: %s" % type(e).__name__
    try:
        sig = inspect.signature(fn)
        args = [p.name for p in sig.parameters.values()
                if p.default is inspect.Parameter.empty
                and p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)]
        etat, n, detail = _classer_retour(fn(*args))
        return etat, n, (detail + " args génériques").strip()
    except Exception as e:                                  # noqa: BLE001
        return "NON_EVALUABLE", None, "appel: %s" % type(e).__name__


def croisement(decl: str, etat: str) -> str:
    """Le produit utile : où la déclaration et le noyau se contredisent."""
    if etat in ("NON_EVALUABLE", "PAS_UN_THEOREME", "CONSTRUIT"):
        return "NON_TRANCHE"
    if etat == "FAIT":
        if decl == "REPORTE":
            return "REPORT_PERIME"          # acquis, et déclaré ouvert
        if decl == "MUET":
            return "ACQUIS_NON_DECLARE"
        return "ACCORD"
    if decl == "CLOS":                      # noyau : hypothèses restantes
        return "DECLARATION_TROP_FORTE"
    return "ACCORD"


#: on ré-écrit le cache tous les N verdicts : une passe complète dure ~1 h et
#: n'écrire qu'à la fin, c'est tout perdre au moindre timeout — mesuré.
_CADENCE_CACHE = 25


def _ecrire_cache(cache: dict) -> None:
    CACHE.write_text(json.dumps(cache, ensure_ascii=False, indent=1),
                     encoding="utf-8")


def evaluer(lignes: list[dict], chap: str | None, limite: int | None) -> None:
    """Enrichit `lignes` sur place avec le verdict noyau, avec cache.

    Le cache est INCRÉMENTAL : une passe interrompue garde tout ce qu'elle a
    tranché, et la suivante reprend où elle s'est arrêtée."""
    cache = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() else {}
    if getattr(evaluer, "rejuge", False):
        avant = len(cache)
        cache = {k: v for k, v in cache.items()
                 if v["etat"] not in ("NON_EVALUABLE", "PAS_UN_THEOREME")}
        print(" rejuge : %d entrées invalidées" % (avant - len(cache)),
              flush=True)
    faits = 0
    for L in lignes:
        if chap and L["chap"] != chap:
            continue
        if limite is not None and faits >= limite:
            break
        cle = "%s::%s" % (L["fichier"], L["notion"])
        if cle not in cache:
            etat, n, detail = verdict_noyau(L["fichier"], L["notion"])
            cache[cle] = {"etat": etat, "hyp": n, "detail": detail}
            faits += 1
            if faits % _CADENCE_CACHE == 0:
                _ecrire_cache(cache)
        L.update(cache[cle])
        L["croisement"] = croisement(L["declaration"], L["etat"])
    _ecrire_cache(cache)


def rapport(lignes: list[dict], avec_noyau: bool) -> str:
    o = ["=" * 78,
         " STATUT DES NOTIONS — ce que le dépôt DÉCLARE, ce que le NOYAU dit",
         "=" * 78,
         " notions marquées @livre et rattachées à une def : %d" % len(lignes),
         "-" * 78, " (1) DÉCLARÉ — lu dans les docstrings, par chapitre", ""]
    par_chap = defaultdict(Counter)
    for L in lignes:
        par_chap[L["chap"]][L["declaration"]] += 1
    cles = ["CLOS", "CLOS_MODULO", "REPORTE", "MUET"]
    o.append("  chap |" + "".join("%14s" % c for c in cles) + "     total")
    for ch in sorted(par_chap, key=lambda c: ["I", "II", "III", "IV", "R"].index(c)
                     if c in ["I", "II", "III", "IV", "R"] else 9):
        c = par_chap[ch]
        o.append("  %-4s |" % ch + "".join("%14d" % c[k] for k in cles)
                 + "%10d" % sum(c.values()))
    tot = Counter()
    for c in par_chap.values():
        tot.update(c)
    o.append("  %-4s |" % "TOUS" + "".join("%14d" % tot[k] for k in cles)
             + "%10d" % sum(tot.values()))

    if not avec_noyau:
        o += ["-" * 78,
              " (2) NOYAU : non évalué (--noyau pour l'exécuter, c'est cher).",
              " ⚠️ La colonne DÉCLARÉ n'est qu'une DÉCLARATION. Seul le noyau",
              "    tranche, et c'est leur désaccord qui vaut.", "=" * 78]
        return "\n".join(o)

    evalues = [L for L in lignes if "etat" in L]
    o += ["-" * 78, " (2) NOYAU — %d notions évaluées" % len(evalues), ""]
    et = Counter(L["etat"] for L in evalues)
    for k in ("FAIT", "PARTIEL", "CONSTRUIT", "NON_EVALUABLE",
              "PAS_UN_THEOREME"):
        if et[k]:
            o.append("   %-18s %5d" % (k, et[k]))
    #   LE CHIFFRE DE TÊTE : sur les seuls types qui PROMETTENT une preuve.
    #   Une Def qui construit n'est ni FAIT ni PARTIEL — l'y mélanger dilue
    #   la seule réponse chiffrée à « démontré == vérifié ? ».
    dem = [L for L in evalues if est_demontrable(L["type"])]
    etd = Counter(L["etat"] for L in dem)
    o += ["", "   TYPES DÉMONTRABLES (Prop/Th/Cor/Crit/Lem/Demo/Sch/Ax) : %d"
          % len(dem)]
    for k in ("FAIT", "PARTIEL", "CONSTRUIT", "NON_EVALUABLE",
              "PAS_UN_THEOREME"):
        if etd[k]:
            o.append("     %-18s %5d" % (k, etd[k]))
    tranchees = etd["FAIT"] + etd["PARTIEL"]
    if tranchees:
        o.append("   → taux FAIT sur les DÉMONTRABLES tranchées : %.1f %% (%d/%d)"
                 % (100.0 * etd["FAIT"] / tranchees, etd["FAIT"], tranchees))
    o += ["-" * 78, " (3) CROISEMENT — ce qu'aucun autre outil ne voit", ""]
    cr = Counter(L["croisement"] for L in evalues)
    for k in ("ACCORD", "REPORT_PERIME", "DECLARATION_TROP_FORTE",
              "ACQUIS_NON_DECLARE", "NON_TRANCHE"):
        o.append("   %-24s %5d" % (k, cr[k]))
    for k in ("REPORT_PERIME", "DECLARATION_TROP_FORTE"):
        cas = [L for L in evalues if L["croisement"] == k]
        if cas:
            o.append("")
            o.append("   ── %s ──" % k)
            for L in cas[:20]:
                o.append("     %-38s %s (%s hyp) %s"
                         % (L["notion"][:38], L["etat"], L["hyp"],
                            L["fichier"].split("/")[-1]))
    o.append("=" * 78)
    return "\n".join(o)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("racine", nargs="?", default="bourbaki")
    ap.add_argument("--noyau", action="store_true",
                    help="évalue réellement (importe et appelle) — coûteux")
    ap.add_argument("--chap", help="borne l'évaluation à un chapitre (I..IV, R)")
    ap.add_argument("--limite", type=int,
                    help="borne le nombre de NOUVELLES évaluations")
    ap.add_argument("--md", help="écrit aussi un rapport Markdown")
    ap.add_argument("--rejuge", action="store_true",
                    help="rejuge les NON_EVALUABLE/PAS_UN_THEOREME du cache "
                         "(après une amélioration du repli d'appel)")
    a = ap.parse_args(argv)

    lignes = passe_declarative(Path(a.racine))
    if a.noyau:
        evaluer.rejuge = a.rejuge
        evaluer(lignes, a.chap, a.limite)
    txt = rapport(lignes, a.noyau)
    print(txt, flush=True)
    if a.md:
        Path(a.md).write_text("```\n" + txt + "\n```\n", encoding="utf-8")
    return 0 if lignes else 1


__all__ = ["TYPES_DEMONTRABLES", "est_demontrable",
           "declaration", "docstrings_du_fichier", "passe_declarative",
           "verdict_noyau", "croisement", "evaluer", "rapport"]


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(64 * 1024 * 1024)
    code = []
    t = threading.Thread(target=lambda: code.append(main(sys.argv[1:])))
    t.start()
    t.join()
    sys.exit(code[0] if code else 1)
