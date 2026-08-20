# Théorie des ensembles de Bourbaki, vérifiée par un noyau LCF

Ce dépôt formalise la *Théorie des ensembles* de N. Bourbaki dans un noyau de preuve
écrit en Python, en style LCF. Sa particularité n'est pas d'en formaliser le **contenu**
— d'autres l'ont fait, au-dessus de la logique d'un assistant existant — mais d'habiter
le **formalisme propre** de Bourbaki : l'opérateur `τ`, les assemblages et leurs liens,
et les critères que Bourbaki *démontre sur les démonstrations* au lieu de les poser comme
règles.

L'objectif est que « démontré dans le livre » et « vérifié par la machine » coïncident.

---

## Les deux articles

| | sujet | PDF |
|---|---|---|
| **A1** | L'échec comme théorème : objets d'erreur certifiés, audit de fidélité, dernier kilomètre instrumenté | [`article/main.pdf`](article/main.pdf) · [FR](article/main_fr.pdf) |
| **A3** | Cartographier l'ouvert : réductions certifiées de la conjecture de Goldbach, et une mesure de ce qu'elles ne contiennent pas | [`article/goldbach/main.pdf`](article/goldbach/main.pdf) · [FR](article/goldbach/main_fr.pdf) |

Le tag **`preprint-v1`** épingle l'état exact sur lequel toutes les mesures des deux
articles ont été prises. Si vous voulez rejouer ce qu'ils rapportent, c'est ce tag qu'il
faut, pas `main` :

```bash
git checkout preprint-v1
```

---

## Vérifier en une commande

```bash
python outils_ia/audit/verifie.py
```

Un seul verdict : invariant des 22 axiomes, erreurs de syntaxe, marqueurs `@livre`,
manifestes, reports. **Il n'annonce jamais vert ce qui n'a pas tourné** — sans
`--tests`, la ligne des tests dit `NON LANCÉ`, et le verdict le refuse explicitement.
Trois notifications « exit 0 » de ce projet se sont avérées être des délais dépassés ;
la règle est née de là.

La suite complète (`--tests`, ~2 h) : **4 221 tests verts** au tag, en 2 h 03 avec
`pytest-xdist -n 12 --dist loadfile`.

---

## Où regarder

| dossier | contenu |
|---|---|
| `bourbaki/` | **767 modules**, l'arborescence calque la table des matières du livre — un dossier vide est un trou de couverture |
| `bourbaki/…/i_2_theoremes/noyau/` | le **noyau de confiance** : `Theoreme` opaque, `assume`, S1–S7, `axiome`, modus ponens, déduction, généralisation |
| `bourbaki/…/i_1_termes_relations/i_1_1_assemblage.py` | couche 0 : assemblages `(signes, liens)`, `τ`, substitution |
| `recherche/` | ce que le projet démontre **au-delà** du livre — Goldbach n'est pas dans Bourbaki, ses réductions vivent ici |
| `outils_ia/` | recherche de preuve, audit, mesure de couverture |
| `tests/` | **616 fichiers**, l'arbre calque `bourbaki/` à l'identique |
| `docs/` | journal, anomalies, cartes de couverture, plan éditorial |
| `article/` | les préprints, leurs sources et leurs figures |

**La frontière de confiance.** Un `Theoreme` ne se crée que par les primitives du noyau.
Pas de constructeur dérobé, pas de `monkeypatch`, pas d'objet fabriqué à la main. Tout le
reste du dépôt est du code ordinaire qui *appelle* le noyau — et qui ne peut donc pas
mentir sur ce qu'il a démontré.

---

## Rejouer l'arc Goldbach

```bash
python recherche/goldbach/capstone.py
```

18 maillons rejoués et **jugés par le noyau**, ~7 min 30. La sortie sépare deux colonnes
que rien n'oblige à distinguer et que tout invite à confondre : « clos » (le noyau
accepte la preuve) et « axiomes ad hoc » (de quelle théorie dédiée elle dépend). Onze
maillons sont libres, sept reposent sur les deux axiomes du crible. **Un théorème tiré
par la règle d'axiome a zéro hypothèse** — la clôture ne dit donc rien des axiomes
ajoutés, et les confondre serait la seule tricherie réellement possible ici.

Le résultat central de A3 se rejoue par `tests/recherche/additif/` : la même dérivation,
exécutée sur un prédicat opaque, sur la primalité, et sur un prédicat trivial. Les trois
ferment.

---

## Ce qui n'est pas fait

Ce dépôt n'est **pas** le livre formalisé. Il en est une part, et le dire précisément
importe plus que le chiffre :

- sur les notions d'un type qui *promet une preuve* (proposition, théorème, corollaire,
  critère, lemme), **413 sont closes sur 815 tranchées — 50,7 %** ; le reste est démontré
  sous hypothèses honnêtement déclarées, ou pas encore ;
- des résultats majeurs restent **ouverts** : Hessenberg, le bon ordre des cardinaux, le
  théorème de Cantor, la division euclidienne, les limites projectives et inductives ;
- les marqueurs `@livre` ancrent chaque notion au livre. **La page est fiable ;
  l'intervalle de lignes ne l'est pas uniformément** — au moins deux conventions
  coexistent, et 12,2 % des intervalles ne peuvent pas être des lignes imprimées. Mesure
  et conséquences dans [`docs/journal/ANOMALIES.md`](docs/journal/ANOMALIES.md).

Le noyau garantit la *correction* — aucun faux théorème. Il ne garantit **pas** la
*fidélité* : qu'un énoncé formalisé soit bien celui du livre. Cette seconde garantie est
un problème d'ingénierie à part entière, elle a ses propres outils dans `outils_ia/audit/`,
et c'est le sujet de A1.

---

## Environnement

Python 3.13, `pytest` 9.0.3, `pytest-xdist`. Lancer depuis la racine, avec
`PYTHONIOENCODING=utf-8`. Certains imports de la théorie des cardinaux sont lourds : un
test de théorème profond peut prendre plusieurs minutes.

## Licence et contact

Karl Olivet — `karl.olivet@gmail.com`. Chercheur indépendant.
