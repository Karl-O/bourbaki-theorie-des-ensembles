#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ANALOGIE — deux preuves de même SQUELETTE, à vocabulaire de domaine différent.

LE MANQUE QUE CET ORGANE COMBLE. Le système travaille toujours dans un seul
sujet. Or les grandes inventions mathématiques viennent du TRANSPORT d'une
structure d'un domaine vers un autre — et rien ici ne savait dire « ceci
ressemble à cela ».

⚠️ CE QU'ON MESURE VRAIMENT, ET IL FAUT LE DIRE. Le noyau ne conserve PAS le
DAG des dérivations : `Theoreme.justification` est une CHAÎNE (« S2 », « MP »,
« axiome[…] »), pas un pointeur vers les parents. Le vrai graphe de preuve
n'est donc pas disponible, et l'obtenir exigerait d'instrumenter le noyau —
exclu. Ce module travaille sur les APPELS entre constructeurs de théorèmes,
extraits par analyse AST. C'est une APPROXIMATION, annoncée comme telle.

════════════════════════════════════════════════════════════════════════════
LA CONCEPTION, ET POURQUOI CELLE-CI — mesuré le 13 août
════════════════════════════════════════════════════════════════════════════

La version du 12 août cherchait des arbres d'appels ISOMORPHES, tous noms
effacés, dépliés sur 3 niveaux. Elle ratait sa cible de validation, et le
plan écrit alors — « il faut une distance d'édition sur les arbres » — était
un mauvais diagnostic. La mesure l'a montré, sur la cible
`symetrie_du_crible` ≈ `symetrie_additive`, deux preuves qui SONT la même :

    profondeur 1  →  85 appels contre 80        (5 d'écart)
    profondeur 3  →  293 nœuds contre 189     (104 d'écart)

**Ce n'est pas l'égalité qui était trop stricte, c'est le DÉPLIAGE qui
détruisait la ressemblance.** En dépliant, on ne compare plus deux preuves :
on compare l'implémentation des lemmes qu'elles appellent. Une analogie se
lit au niveau des pas enchaînés, pas dans les entrailles des pas.

Second constat, décisif : ces deux preuves partagent **26 noms d'appels**
(`_mp`, `_cg`, `s5`, `s6`, `assume`, `generalisation`…) et ne diffèrent que
sur 7 contre 6. Effacer TOUS les noms jetait donc le signal le plus fort.
C'est la structure même d'une analogie mathématique :

    même SQUELETTE d'inférence (vocabulaire de liaison, partagé)
    autre VOCABULAIRE de domaine (rare, propre au sujet)

D'où le critère retenu, et il se décide sans rien savoir du sujet : un nom
appelé depuis ≥ `SEUIL_LIAISON` modules distincts est de la LIAISON et garde
son identité ; un nom rare est du DOMAINE et s'efface en `?`. La distance est
alors l'édition sur multiensembles, normalisée dans [0,1].

RANG DE LA CIBLE, quatre conceptions comparées sur les 582 paires retenues :

    noms tous effacés (l'ancienne, à prof. 1)   rang 42   — morte
    tous les noms gardés                        rang  4   d = 0,127
    liaison gardée / domaine effacé  ← RETENUE  rang  4   d = 0,091
    idem + vocabulaires disjoints exigés        ABSENTE   — voir plus bas

La conception retenue creuse une FALAISE : rangs 1 à 4 sous 0,10, puis saut
à 0,22. `SEUIL_ANALOGIE` est posé au milieu de ce vide, pas au doigt mouillé.

LES SEUILS SONT-ILS UN RÉGLAGE FIN ? Non — balayés, ils donnent un plateau :
la cible reste au rang 2 à 4 pour `SEUIL_LIAISON` de 2 à 8 ET `APPELS_MINI`
de 10 à 40, et la paire emboîtée (ci-dessous) au rang 1 partout. La valeur
exacte ne porte donc rien. ⚠️ `SEUIL_LIAISON = 5` classerait MIEUX la cible
(rang 2, d = 0,030) : on ne le prend pas. Régler un seuil sur l'exemple qui
sert à valider, c'est se mentir — 3 (« vu dans au moins trois modules ») est
le seul choix qui s'explique sans regarder la réponse.

⚠️ POURQUOI ON N'EXIGE PAS DES VOCABULAIRES DISJOINTS. C'était tentant — une
analogie, c'est deux sujets différents. Mesuré : la cible DISPARAÎT. Les deux
preuves partagent des noms rares (`cible_partenaire`, `fic_t`, …). Une
abstraction réussie garde une partie du vocabulaire de sa version concrète ;
exiger la disjonction, c'est interdire précisément le cas qu'on cherche.

CE QUE ÇA NE DÉMONTRE PAS. Une forme commune est une PISTE. Rien ici ne dit
que les deux preuves se transportent l'une en l'autre — seul le noyau
pourrait le juger, et il faudrait l'écrire. Aucun `Theoreme` ne sort d'ici.

Outillage pur : analyse AST, aucun exec-noyau, aucun `Theoreme` fabriqué.
"""
from __future__ import annotations

import ast
import sys
from collections import Counter
from pathlib import Path

#: un nom appelé depuis ce nombre de modules distincts est de la LIAISON
SEUIL_LIAISON = 3
#: plancher : sous ce nombre d'appels, ce n'est pas une preuve à comparer
APPELS_MINI = 20
#: au-delà, ce n'est plus une analogie — posé dans la falaise mesurée
SEUIL_ANALOGIE = 0.15

RACINES = ["recherche", "outils_ia/decouvertes"]


def graphe_appels(racines=RACINES):
    """→ {qualname: [noms appelés]} pour tous les `.py` sous `racines`.

    Le qualname est `module.fonction`. Les appels sont notés par leur nom
    simple : on ne résout pas les imports, et c'est assumé — deux fonctions
    homonymes dans deux modules seront confondues, ce qui va dans le sens de
    l'analogie plutôt que contre elle."""
    graphe = {}
    for racine in racines:
        for f in Path(racine).rglob("*.py"):
            if "__pycache__" in str(f):
                continue
            try:
                arbre = ast.parse(f.read_text(encoding="utf-8"))
            except Exception:                          # noqa: BLE001
                continue
            mod = f.stem
            if mod.startswith("test_"):
                continue          # un test n'est pas une preuve : ses jumeaux
                                  # structurels sont un artefact d'écriture
            for n in ast.walk(arbre):
                if not isinstance(n, ast.FunctionDef):
                    continue
                if n.name.startswith("test_"):
                    continue
                appels = []
                for c in ast.walk(n):
                    if isinstance(c, ast.Call):
                        cible = _nom_appele(c.func)
                        if cible:
                            appels.append(cible)
                graphe["%s.%s" % (mod, n.name)] = appels
    return graphe


def _nom_appele(f):
    if isinstance(f, ast.Name):
        return f.id
    if isinstance(f, ast.Attribute):
        return f.attr
    return None


def vocabulaire_de_liaison(graphe, seuil=SEUIL_LIAISON):
    """→ l'ensemble des noms de LIAISON, décidé par la seule fréquence.

    Un nom appelé depuis `seuil` modules distincts ou plus appartient au
    squelette d'inférence commun (`_mp`, `_cg`, `s5`, `var`, …) ; les autres
    sont du vocabulaire de domaine. Aucune liste blanche n'est écrite à la
    main : le corpus décide seul, et le critère survit à son extension."""
    modules = {}
    for qn, appels in graphe.items():
        mod = qn.split(".")[0]
        for a in set(appels):
            modules.setdefault(a, set()).add(mod)
    return {a for a, m in modules.items() if len(m) >= seuil}


def forme(qn, graphe, liaison):
    """La FORME d'une preuve : ses appels, domaine effacé, liaison gardée.

    C'est le cœur de l'organe, et tout tient dans la ligne ci-dessous : on
    garde ce qui est commun à tous les sujets, on efface ce qui est propre à
    un sujet. Deux preuves de même forme enchaînent les mêmes pas sur des
    objets différents."""
    return Counter(a if a in liaison else "?" for a in graphe.get(qn, []))


def taille(f):
    return sum(f.values())


def distance(f1, f2):
    """Édition sur multiensembles, normalisée dans [0,1] — 0 = même forme.

    |différence symétrique| rapporté au total : un écart de 5 appels sur 165
    vaut 0,03, le même écart sur 40 vaut 0,12. C'est voulu — deux petites
    preuves doivent se ressembler DE PLUS PRÈS pour mériter le rapprochement."""
    tot = taille(f1) + taille(f2)
    if not tot:
        return 1.0
    return sum(((f1 - f2) + (f2 - f1)).values()) / tot


def vocabulaires_opposes(qn1, qn2, graphe, liaison):
    """→ (propres à qn1, propres à qn2) — le vocabulaire de domaine de chacun.

    C'est la charge utile pour un lecteur humain : la distance dit QUE deux
    preuves se ressemblent, ceci dit SUR QUOI elles diffèrent — donc ce que
    le transport devrait traduire."""
    d1 = {a for a in graphe.get(qn1, []) if a not in liaison}
    d2 = {a for a in graphe.get(qn2, []) if a not in liaison}
    return sorted(d1 - d2), sorted(d2 - d1)


def paires_analogues(graphe, mini=APPELS_MINI, seuil=SEUIL_ANALOGIE,
                     liaison=None):
    """→ [(distance, qn1, qn2)] triées, les paires sous `seuil`.

    On écarte deux familles de faux positifs : les fonctions trop petites
    (sous `mini` appels, tout se ressemble) et les paires intra-module (du
    copier-coller n'est pas une analogie entre sujets)."""
    liaison = vocabulaire_de_liaison(graphe) if liaison is None else liaison
    formes = {}
    for qn in graphe:
        f = forme(qn, graphe, liaison)
        if taille(f) >= mini:
            formes[qn] = f
    noms = sorted(formes)
    out = []
    for i in range(len(noms)):
        for j in range(i + 1, len(noms)):
            a, b = noms[i], noms[j]
            if a.split(".")[0] == b.split(".")[0]:
                continue                  # même module : copier-coller
            if a.split(".")[-1] == b.split(".")[-1]:
                continue                  # même nom : pas une analogie
            d = distance(formes[a], formes[b])
            if d <= seuil:
                out.append((d, a, b))
    out.sort(key=lambda x: (x[0], x[1], x[2]))
    return out


def main():
    g = graphe_appels()
    liaison = vocabulaire_de_liaison(g)
    print("=" * 78, flush=True)
    print(" ANALOGIE — même squelette d'inférence, autre vocabulaire de domaine",
          flush=True)
    print("=" * 78, flush=True)
    print(" corpus  : %d fonctions dans %s" % (len(g), ", ".join(RACINES)),
          flush=True)
    print(" liaison : %d noms vus dans ≥ %d modules ; le reste est du domaine"
          % (len(liaison), SEUIL_LIAISON), flush=True)
    print(" ⚠️ graphe d'APPELS (AST), pas le DAG des dérivations : le noyau ne",
          "\n    conserve pas ses parents. Approximation assumée.", flush=True)
    print("-" * 78, flush=True)
    paires = paires_analogues(g, liaison=liaison)
    if not paires:
        print(" aucune paire sous %.2f — ce qui est une information, pas un échec"
              % SEUIL_ANALOGIE, flush=True)
    for (d, a, b) in paires:
        print(" d=%.4f  %-44s ≈ %s" % (d, a, b), flush=True)
        va, vb = vocabulaires_opposes(a, b, g, liaison)
        print("          %-44s | %s" % (", ".join(va[:5]) or "—",
                                        ", ".join(vb[:5]) or "—"), flush=True)
    print("-" * 78, flush=True)
    print(" RAPPEL : une forme commune est une PISTE, pas un théorème. Rien",
          "\n ici ne démontre que les deux preuves se transportent l'une en",
          "\n l'autre — seul le noyau pourrait le juger, et il faudrait l'écrire.",
          flush=True)
    return 0


__all__ = ["SEUIL_LIAISON", "APPELS_MINI", "SEUIL_ANALOGIE", "RACINES",
           "graphe_appels", "vocabulaire_de_liaison", "forme", "taille",
           "distance", "vocabulaires_opposes", "paires_analogues"]


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(64 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
