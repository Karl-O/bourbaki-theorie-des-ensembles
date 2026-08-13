#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Volant wake-sleep — driver d'UN tour + mesure du COMPOUNDING (JALON 2).

Assemble les organes en une boucle et MESURE ce qui distingue « s'auto-améliorer » de « accumuler » :
une notion promue devient un primitif 1-pas, donc à budget-noyau FIXE (CAP, cf. proto_synth_capcurve)
des preuves auparavant hors-budget passent SOUS le CAP. Un tour :

  WAKE   = le corpus de preuves closes (déjà formalisé) — la sortie du solveur.
  SLEEP-ABSTRACTION = `promo_notion.promouvoir` : mine → anti-unifie → promeut en tactique dérivée,
                      GATE noyau (0 théorème faux), garde ssi corpus strictement plus court.
  MESURE = (1) portée-CAP AVANT/APRÈS substitution des notions (le compounding : combien de preuves
               passent sous chaque CAP quand chaque bloc-notion compte pour 1 pas) ;
           (2) COMPOUNDING D'ORDRE 2 : re-miner le corpus COMPRESSÉ (les notions substituées) et
               compter les macros récurrentes qui CONTIENNENT une notion promue = une notion qui en
               permet une autre (le geste DreamCoder qui découvre en profondeur croissante) ;
           (3) persiste la BIBLIOTHÈQUE apprise `notions_apprises.py` (l'actif qui grossit) + journal.

Tout est statique/AST + gate noyau (borné) : rapide, kernel-safe, frontière 22 axiomes intacte.
Outillage seulement (outils_ia/) ; ne MUTE PAS `bourbaki/` (dry-run, préflight).
USAGE : python outils_ia/corpus/flywheel.py [package…] [--essais N]
"""
from __future__ import annotations

import datetime
import json
import sys
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from promo_notion import _scan, promouvoir, PACKAGES          # noqa: E402

CAPS = [4, 6, 8, 10, 15, 20]
NS = (2, 3, 4)
_BIBLIO = _ICI / "notions_apprises.py"
_JOURNAL = _ICI / "flywheel_journal.jsonl"


def _compress(sigs, blocks):
    """Remplace les blocs-notion (non-chevauchants, greedy) par un pas-primitif. → (stream, gagné)."""
    chosen, last = [], -1
    for (i, L, nom) in sorted(blocks):
        if i > last:
            chosen.append((i, L, nom))
            last = i + L - 1
    out, j, ci = [], 0, 0
    while j < len(sigs):
        if ci < len(chosen) and chosen[ci][0] == j:
            out.append((chosen[ci][2], -1))                   # pas-primitif (arité -1 = notion)
            j += chosen[ci][1]
            ci += 1
        else:
            out.append(sigs[j])
            j += 1
    return out, sum(L - 1 for (_, L, _) in chosen)


def _miner_ordre2(streams):
    """n-grammes ≥2 preuves contenant ≥1 pas-notion (arité -1) = macros de 2ᵉ ordre."""
    ng_preuves = defaultdict(set)
    for pid, s in streams.items():
        for n in NS:
            for i in range(len(s) - n + 1):
                ng = tuple(s[i:i + n])
                if any(a == -1 for _, a in ng):
                    ng_preuves[ng].add(pid)
    return {ng: len(pr) for ng, pr in ng_preuves.items() if len(pr) >= 2}


def _ecrire_biblio(acceptes, meta):
    # Un tour VIDE ne réécrit pas la bibliothèque : le 7 août 2026, un tour à 0
    # notion (îlot non gatable) a effacé les 2 notions du tour #1 — récupérées
    # depuis l'index git. Tant que la fusion par paquet n'existe pas, on ne
    # remplace le fichier que si le tour apporte quelque chose.
    if not acceptes:
        print("# biblio inchangée (tour vide) —", _BIBLIO.name, file=sys.stderr)
        return
    lignes = ['#!/usr/bin/env python3', '# -*- coding: utf-8 -*-',
              '"""BIBLIOTHÈQUE de notions APPRISES — auto-générée par flywheel.py (JALON 2).',
              '',
              'Chaque tactique dérivée ci-dessous a été INVENTÉE par anti-unification d\'un motif',
              'récurrent, NOMMÉE, et CERTIFIÉE par le noyau (gate MDL : re-prouve ≥2 théorèmes',
              'identiquement, corpus strictement plus court, zéro théorème faux). Injectée dans le',
              'namespace du module-preuve à l\'usage (comme le fait le gate). Ne PAS éditer à la main.',
              f'Tour généré le {meta["date"]} — {len(acceptes)} notions, gain MDL total ≈{meta["gain"]} pas.',
              '"""', '', '']
    for a in acceptes:
        preuves = ", ".join(n for n, _ in a["details"])
        lignes.append(f"# notion réutilisée dans {a['npr']} preuves (noyau OK) : {preuves}")
        lignes.append(a["src"])
        lignes.append("")
    _BIBLIO.write_text("\n".join(lignes), encoding="utf-8")


def executer(packages, essais):
    """Un tour d'abstraction : WAKE → SLEEP-abstraction → compounding → biblio. Renvoie (rec, acceptes).

    Imprime les sections (1)(2) et écrit la bibliothèque ; NE journalise PAS (le caller décide :
    `flywheel.main` pour un tour d'abstraction seul, `tour.main` pour le tour complet + découverte)."""
    print("# VOLANT wake-sleep — un tour", file=sys.stderr)
    ths = _scan(packages)
    par_preuve = {(t["mod"].__name__, t["name"]): t for t in ths}
    print(f"# WAKE : {len(ths)} preuves closes (corpus courant)")

    acceptes, funnel, n_cands = promouvoir(ths, essais)
    gain_total = sum(a["gain"] for a in acceptes)
    print(f"# SLEEP-abstraction : {n_cands} candidates → funnel {funnel} → "
          f"{len(acceptes)} notions promues (gate noyau OK), gain MDL ≈{gain_total} pas")

    # empreinte des notions par preuve
    blocs = defaultdict(list)
    for a in acceptes:
        for (mn, nm, i, L) in a["insts_meta"]:
            blocs[(mn, nm)].append((i, L, a["nom"]))

    # (1) portée-CAP AVANT / APRÈS  + streams compressés pour l'ordre 2
    lo, lc = [], []
    streams, touchees = {}, []
    for key, th in par_preuve.items():
        sigs = th["sigs"]
        orig = len(sigs)
        if key in blocs:
            stream, gagne = _compress(sigs, blocs[key])
            comp = orig - gagne
            if gagne > 0:
                touchees.append((key[1], orig, comp))
        else:
            stream, comp = sigs, orig
        streams[key] = stream
        lo.append(orig)
        lc.append(comp)

    print(f"\n# (1) COMPOUNDING — portée sous budget CAP (nb de preuves de longueur ≤ CAP) :")
    print(f"#  {'CAP':>4} | {'AVANT':>6} | {'APRÈS':>6} | gain")
    tot = len(lo)
    for cap in CAPS:
        b = sum(1 for x in lo if x <= cap)
        a2 = sum(1 for x in lc if x <= cap)
        print(f"#  {cap:>4} | {b:>6} | {a2:>6} | +{a2 - b}")
    print(f"#  (sur {tot} preuves ; {len(touchees)} raccourcies par une notion)")
    for nm, o, c in sorted(touchees, key=lambda t: t[1] - t[2], reverse=True)[:6]:
        franchit = [cap for cap in CAPS if c <= cap < o]
        note = f"  ⇒ franchit CAP {franchit}" if franchit else ""
        print(f"#     {nm}: {o} → {c} pas{note}")

    # (2) COMPOUNDING d'ORDRE 2
    o2 = _miner_ordre2(streams)
    print(f"\n# (2) COMPOUNDING d'ordre 2 : {len(o2)} macro(s) récurrente(s) UTILISANT une notion promue")
    for ng, npr in sorted(o2.items(), key=lambda kv: -kv[1])[:5]:
        libell = " → ".join((fn if a == -1 else f"{fn}/{a}") for fn, a in ng)
        print(f"#     [{npr} preuves] {libell}")
    if not o2:
        print("#     (aucune ce tour — attendu sur petit corpus ; apparaît quand la biblio grossit)")

    # (3) persiste la bibliothèque apprise
    date = datetime.date.today().isoformat()
    _ecrire_biblio(acceptes, {"date": date, "gain": gain_total})
    rec = {"date": date, "packages": packages, "n_preuves": len(ths),
           "n_candidates": n_cands, "funnel": funnel, "n_promues": len(acceptes),
           "gain_mdl": gain_total, "ordre2": len(o2),
           "cap_gain": {cap: sum(1 for x in lc if x <= cap) - sum(1 for x in lo if x <= cap)
                        for cap in CAPS}}
    print(f"\n# (3) bibliothèque apprise → {_BIBLIO.name} ({len(acceptes)} notions)")
    return rec, acceptes


def _journaliser(journal, rec):
    """Ajoute rec au journal JSONL avec un numéro de tour ; renvoie le n° de tour."""
    tours = journal.read_text(encoding="utf-8").count("\n") if journal.exists() else 0
    rec = {"tour": tours + 1, **rec}
    with journal.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
    return rec["tour"]


def main(argv):
    rest = argv[1:]
    essais = int(rest[rest.index("--essais") + 1]) if "--essais" in rest else 155
    packages = [a for a in rest if not a.startswith("--") and not a.isdigit()] or PACKAGES
    rec, _ = executer(packages, essais)
    tour = _journaliser(_JOURNAL, rec)
    print(f"# tour #{tour} journalisé → {_JOURNAL.name}")
    print("# = un tour de volant : invente → nomme → certifie → compresse → mesure la portée gagnée.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
