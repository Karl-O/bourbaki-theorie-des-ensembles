#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""VERIFIE — « est-ce que ça va ? » en UNE commande, et un seul verdict.

LE MANQUE QUE CET OUTIL COMBLE. Répondre à cette question demandait jusqu'ici
QUATRE commandes tapées de mémoire, chacune avec sa sortie à lire à l'œil.
Tant que c'est le cas, un humain est structurellement obligé de tout relire :
il n'existe aucune barrière à laquelle déléguer sa confiance. Ce script EST
cette barrière.

⚠️ RÈGLE CARDINALE : NE JAMAIS ANNONCER VERT CE QUI N'A PAS TOURNÉ.
La suite de tests dure 2 h 20 ; elle n'est donc lancée que sur `--tests`.
Sans ce drapeau, la ligne correspondante dit NON LANCÉ — jamais OK. Un
vérificateur qui tait ce qu'il ignore est pire que pas de vérificateur : il
fabrique une confiance sans objet. Trois notifications « exit 0 » de ce
projet se sont avérées être des timeouts ; c'est la même erreur, et elle est
interdite ici par construction.

CE QU'IL VÉRIFIE, et pourquoi chaque ligne mérite d'y être :
  · AXIOMES     theorie_ensembles() == 22 — l'invariant de la théorie. S'il
                bouge, un axiome a été ajouté quelque part : tout le reste
                devient suspect.
  · SYNTAXE     0 SyntaxError sur bourbaki/. ⚠️ compileall rend 1 même quand
                tout compile (FileNotFoundError sur le .pyc temporaire) : on
                COMPTE les vraies SyntaxError, on ne lit pas le code retour.
  · MARQUEURS   nombre de @livre et de trous intra-page (gen_trous_livre).
                Le compte de trous est un indicateur de DIRECTION, pas un
                seuil : il monte quand on formalise sans annoter.
  · MANIFESTES  notions, marqueurs non conformes, parties complètes
                (gen_livre_manifestes). « 0 non conforme » est un vrai
                garde-fou de format.
  · REPORTS     entrées REPORTES suspectes (audit_reports) — un acquis
                déclaré ouvert qu'on risquerait de refaire.
  · TESTS       sur --tests seulement : la suite, en parallèle xdist.

Usage :
    python outils_ia/audit/verifie.py                    # ~1 min, sans les tests
    python outils_ia/audit/verifie.py --tests            # + la suite (long)
    python outils_ia/audit/verifie.py --tests --rapide   # + la suite « not slow »
"""
from __future__ import annotations

import argparse
import io
import re
import subprocess
import sys
import time
from contextlib import redirect_stdout
from pathlib import Path

RACINE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RACINE))

#: l'invariant de la théorie des ensembles de Bourbaki, tel que le dépôt l'exige
AXIOMES_ATTENDUS = 22


class Ligne:
    """Un constat du rapport. `etat` vaut OK, ALERTE, ECHEC ou NON_LANCE."""

    __slots__ = ("nom", "etat", "detail")

    def __init__(self, nom, etat, detail=""):
        self.nom, self.etat, self.detail = nom, etat, detail

    @property
    def bloquant(self):
        return self.etat == "ECHEC"


def verifie_axiomes():
    """L'invariant : theorie_ensembles() doit valoir exactement 22 axiomes."""
    try:
        from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes \
            .ensembles_abrege import theorie_ensembles
        n = len(theorie_ensembles().axiomes)
    except Exception as e:                                  # noqa: BLE001
        return Ligne("axiomes", "ECHEC", "import/appel : %s" % type(e).__name__)
    if n != AXIOMES_ATTENDUS:
        return Ligne("axiomes", "ECHEC", "%d au lieu de %d" % (n, AXIOMES_ATTENDUS))
    return Ligne("axiomes", "OK", "%d" % n)


def verifie_syntaxe():
    """0 SyntaxError sur bourbaki/ — on COMPTE, on ne lit pas le code retour."""
    r = subprocess.run([sys.executable, "-m", "compileall", "-q", "bourbaki"],
                       cwd=str(RACINE), capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    n = len(re.findall(r"SyntaxError", (r.stdout or "") + (r.stderr or "")))
    if n:
        return Ligne("syntaxe", "ECHEC", "%d SyntaxError" % n)
    return Ligne("syntaxe", "OK", "0 SyntaxError")


def verifie_marqueurs():
    """Marqueurs @livre et trous intra-page — indicateur de direction."""
    try:
        from outils_ia.audit.gen_trous_livre import collecter, trouver_trous
        ms = collecter(RACINE / "bourbaki")
        trous = trouver_trous(ms)
    except Exception as e:                                  # noqa: BLE001
        return Ligne("marqueurs", "ECHEC", type(e).__name__)
    return Ligne("marqueurs", "OK",
                 "%d marqueurs, %d trous intra-page" % (len(ms), len(trous)))


def verifie_manifestes():
    """Notions et marqueurs NON CONFORMES au format @livre (vrai garde-fou)."""
    try:
        from outils_ia.audit import gen_livre_manifestes as glm
        tampon = io.StringIO()
        with redirect_stdout(tampon):
            glm.main(["bourbaki"])
        sortie = tampon.getvalue()
    except Exception as e:                                  # noqa: BLE001
        return Ligne("manifestes", "ECHEC", type(e).__name__)
    m = re.search(r"(\d+) notions, (\d+) fichiers? . caler, (\d+) marqueurs? non conformes?",
                  sortie)
    if not m:
        return Ligne("manifestes", "ALERTE", "sortie non reconnue")
    notions, caler, nc = (int(x) for x in m.groups())
    complets = len(re.findall(r"complet sur l", sortie))
    return Ligne("manifestes", "ECHEC" if nc else "OK",
                 "%d notions, %d non conformes, %d a caler, %d parties completes"
                 % (notions, nc, caler, complets))


def verifie_reports():
    """Entrées REPORTES suspectes : un acquis déclaré ouvert qu'on refera."""
    try:
        from outils_ia.audit import audit_reports as ar
        tampon = io.StringIO()
        with redirect_stdout(tampon):
            ar.main([])
        sortie = tampon.getvalue()
    except Exception as e:                                  # noqa: BLE001
        return Ligne("reports", "ECHEC", type(e).__name__)
    m = re.search(r"(\d+) reports examin.s . (\d+) SUSPECT", sortie)
    if not m:
        return Ligne("reports", "ALERTE", "sortie non reconnue")
    tot, susp = int(m.group(1)), int(m.group(2))
    return Ligne("reports", "ALERTE" if susp else "OK",
                 "%d suivis, %d suspects" % (tot, susp))


def verifie_tests(lance, rapide):
    """La suite. NON LANCÉ tant qu'on ne la demande pas — jamais « OK »."""
    if not lance:
        return Ligne("tests", "NON_LANCE", "relancer avec --tests")
    sortie = RACINE / "_verifie_pytest.txt"
    cmd = [sys.executable, "-m", "pytest", "tests/", "-q",
           "-n", "12", "--dist", "loadfile"]
    if rapide:
        cmd += ["-m", "not slow"]
    t0 = time.time()
    with open(sortie, "w", encoding="utf-8") as f:
        code = subprocess.run(cmd, cwd=str(RACINE), stdout=f,
                              stderr=subprocess.STDOUT).returncode
    txt = sortie.read_text(encoding="utf-8", errors="replace")
    duree = "%d min" % round((time.time() - t0) / 60)
    if code != 0:
        rate = re.search(r"(\d+) failed", txt)
        return Ligne("tests", "ECHEC", "code %d%s, %s, voir %s"
                     % (code, (", %s failed" % rate.group(1)) if rate else "",
                        duree, sortie.name))
    m = re.search(r"(\d+) passed", txt)
    return Ligne("tests", "OK", "%s passed, %s%s"
                 % (m.group(1) if m else "?", duree,
                    " (not slow)" if rapide else ""))


def rapport(lignes):
    SYM = {"OK": "  OK  ", "ALERTE": "ALERTE", "ECHEC": "ECHEC ", "NON_LANCE": "  --  "}
    o = ["=" * 74, " VERIFICATION DU DEPOT - un seul verdict", "=" * 74]
    for L in lignes:
        o.append("  [%s]  %-11s %s" % (SYM.get(L.etat, "?"), L.nom, L.detail))
    o.append("-" * 74)
    ech = [L.nom for L in lignes if L.bloquant]
    nl = [L.nom for L in lignes if L.etat == "NON_LANCE"]
    if ech:
        o.append(" VERDICT : ECHEC sur %s" % ", ".join(ech))
    elif nl:
        o.append(" VERDICT : rien de casse, mais %s NON LANCE - ce n'est PAS vert."
                 % ", ".join(nl))
    else:
        o.append(" VERDICT : VERT - tout ce qui est verifiable a ete verifie.")
    o.append("=" * 74)
    return "\n".join(o)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--tests", action="store_true", help="lance aussi la suite (long)")
    ap.add_argument("--rapide", action="store_true", help="avec --tests : exclut les slow")
    a = ap.parse_args(argv)
    lignes = [verifie_axiomes(), verifie_syntaxe(), verifie_marqueurs(),
              verifie_manifestes(), verifie_reports(),
              verifie_tests(a.tests, a.rapide)]
    print(rapport(lignes), flush=True)
    return 1 if any(L.bloquant for L in lignes) else 0


__all__ = ["AXIOMES_ATTENDUS", "Ligne", "verifie_axiomes", "verifie_syntaxe",
           "verifie_marqueurs", "verifie_manifestes", "verifie_reports",
           "verifie_tests", "rapport"]


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(64 * 1024 * 1024)
    code = []
    t = threading.Thread(target=lambda: code.append(main(sys.argv[1:])))
    t.start()
    t.join()
    sys.exit(code[0] if code else 1)
