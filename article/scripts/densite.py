# -*- coding: utf-8 -*-
"""DENSITÉ — mesurer les « gros pavés » d'un article avant de les charcuter.

LE MANQUE QUE CET OUTIL COMBLE. Le 20 août 2026, le retour sur A3 était « trop
de gros pavés, ça donne pas envie de lire ». L'explication évidente — les
paragraphes sont trop longs — était FAUSSE : mesuré, A3 avait une médiane de
544 caractères contre 652 pour A1, dont personne ne se plaignait. La cause
était la mise en page (ligne de ~90 caractères, `\\parskip` nul), pas le texte.

Diagnostiquer à l'œil aurait conduit à réécrire de la prose correcte. D'où cet
outil : **mesurer avant de toucher**.

CE QU'IL REND, et comment le lire :
  · médiane — l'indicateur qui compte ; au-dessus de ~700 caractères, il y a un
    vrai problème de texte ;
  · maximum et les douze plus gros — la file de travail, s'il y en a une ;
  · répartition par seuil — combien de pavés, et à quel point.

⚠️ CE QU'IL NE VOIT PAS. La longueur de ligne, l'interligne et l'espacement
inter-paragraphes — c'est-à-dire, très souvent, la vraie cause. Cet outil dit
si le TEXTE est en cause ; si sa médiane est basse et que la page paraît
quand même compacte, regarder le préambule (cf. `docs/articles/STYLE_ARTICLES.md`
§2). Un outil qui laisserait croire qu'il mesure la lisibilité serait pire
qu'aucun outil.

Usage :
    python article/scripts/densite.py article/goldbach/main_fr.tex
    python article/scripts/densite.py article/*.tex          # comparaison
"""
from __future__ import annotations

import io
import re
import sys

BS = chr(92)

#: en-têtes d'environnements et de commandes qui ne sont pas de la prose
IGNORES = ("begin", "end", "[", "section", "subsection", "node", "draw",
           "bibliographystyle", "bibliography", "includegraphics", "caption",
           "label", "centering", "toprule", "midrule", "bottomrule")

#: en dessous, ce n'est pas un paragraphe mais une ligne de tableau ou un titre
PLANCHER = 80


def paragraphes(chemin):
    """Rend [(longueur en caractères visibles, début du texte)] du CORPS."""
    src = io.open(chemin, encoding="utf-8").read()
    corps = src.split(BS + "maketitle", 1)[-1]
    out = []
    for bloc in corps.split("\n\n"):
        lignes = [l for l in bloc.split("\n") if not l.strip().startswith("%")]
        txt = "\n".join(lignes).strip()
        if not txt or any(txt.startswith(BS + m) for m in IGNORES):
            continue
        nu = re.sub(BS + "[a-zA-Z]+", "", txt)
        nu = re.sub("[" + BS + "{}$&]", "", nu)
        if len(nu) > PLANCHER:
            out.append((len(nu), " ".join(txt.split())[:62]))
    return out


def rapport(chemin):
    par = sorted(paragraphes(chemin), reverse=True)
    if not par:
        print("%s : aucun paragraphe de corps trouvé" % chemin)
        return
    n = [p[0] for p in par]
    med = sorted(n)[len(n) // 2]
    print("=" * 74)
    print(" %s" % chemin)
    print("=" * 74)
    print("  %d paragraphes  |  moyenne %d  |  MEDIANE %d  |  max %d"
          % (len(par), sum(n) // len(n), med, n[0]))
    for s in (500, 800, 1100, 1400):
        print("     >= %4d car. : %2d" % (s, sum(1 for x in n if x >= s)))
    verdict = ("le TEXTE est dense" if med >= 700 else
               "le texte va — si la page paraît compacte, voir le PREAMBULE "
               "(STYLE_ARTICLES.md §2)")
    print("  -> %s" % verdict)
    print("  les 12 plus gros :")
    for longueur, debut in par[:12]:
        print("    %4d  %s..." % (longueur, debut))
    print("")


def main(argv):
    if not argv:
        print(__doc__.splitlines()[0])
        print("usage : python article/scripts/densite.py <fichier.tex> [...]")
        return 1
    for chemin in argv:
        rapport(chemin)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
