# Théorie des ensembles de Bourbaki — formalisation vérifiée par noyau (V9)

## Objectif (le nord)
**Retranscrire INTÉGRALEMENT le livre *Théorie des ensembles* de N. Bourbaki dans le code**,
chaque résultat nommé (définition, axiome, critère C/CS/CF, proposition, théorème, corollaire)
devenant un objet `Theoreme` **certifié par le noyau LCF**. « Démontré dans le livre » doit
coïncider avec « vérifié par la machine ». Un résultat n'est *FAIT* que s'il est clos
(0 hypothèse non déchargée) et que son énoncé == celui de Bourbaki ; sinon il est *PARTIEL*.

## Frontière de confiance (ne JAMAIS la franchir)
- Un `Theoreme` ne se crée qu'avec les **primitives du noyau** (`bourbaki/logique/noyau*.py`,
  exposées via `N.*` : `assume, modus_ponens, loi_deduction, generalisation, existe_temoin,
  s1..s7, axiome, instancie`). **Jamais** de `_CLE`, de `Theoreme(...)` fabriqué à la main,
  de monkeypatch.
- Invariant : `theorie_ensembles()` doit valoir **22 axiomes**. N'en ajouter aucun à la légère.

## Conventions de structure
1. **Un fichier = une responsabilité, ≤ 300 lignes.**
2. **≤ 10 entrées par dossier** (fichiers + sous-dossiers **confondus**). Dès qu'un dossier
   atteint 10, on l'**éclate en sous-dossiers nommés d'après la section du livre**.
3. **L'arborescence calque la table des matières du livre** (chapitre → section → sous-section
   → thème). Conséquence voulue : un **trou de couverture devient visible structurellement**
   (dossier vide ou absent = résultat du livre pas encore formalisé).
4. **`tests/` calque `bourbaki/` à l'identique** (même arbre, mêmes noms).
5. **Tests verts avant d'avancer.**

## Table des matières de référence (cible de l'arbre)
- **Chap. I** Logique : I.1 termes/relations · I.2 critères déductifs C · I.3 quantifiés · I.4 égalitaires
- **Chap. II** Ensembles : II.1 collectivisantes/axiomes · II.2 couples/produit · II.3 correspondances/fonctions ·
  II.4 réunion/intersection de familles · II.5 produit d'une famille · II.6 relations d'équivalence
- **Chap. III** Ordre & cardinaux : III.1 relations d'ordre · III.2 bon ordre · III.3 équipotence/cardinaux ·
  III.4 entiers/finis · III.5 calcul sur les entiers · III.6 ensembles infinis · III.7 limites proj./induct.
- **Chap. IV** Structures : IV.1 structures/isomorphismes · IV.2 morphismes/structures dérivées · IV.3 applications universelles

## Suivi de couverture
La couverture réelle est suivie hors de `outils_ia/couverture.py` (périmé). Audit du 2026-06-23 :
~85 % des définitions, mais propositions ~38 %, théorèmes nommés ~26 % réellement clos
(beaucoup de PARTIEL : cas binaire seul, « modulo résidus honnêtes », niveau valeurs, terme opaque).
Gros chantiers ouverts : Hessenberg a²=a (III.6), bon ordre des cardinaux (III.3), Cantor 2^a>a,
division euclidienne (III.5), limites (III.7), CST1/CST2 (IV).

## Documents de référence (la SPEC — le code doit y correspondre)
Trois sources, sous `../V6/` (depuis `V9/`) :
1. **Le livre** — `../V6/1) Theorie Des Ensembles.pdf` (scan Bourbaki, source ultime).
2. **Transcription** — `../V6/V7/` : **154 `Texte.tex`** calqués sur la table des matières (énoncés +
   preuves du livre, annotés `% §`) → `../V6/V7/main.pdf`.
3. **Rapport ingénieur** — `../V6/V8/` : un `rapport.tex` par sous-section (énoncé Bourbaki verbatim +
   implémentation Python + choix algorithmiques + figures) → `../V6/V8/main.pdf`. **C'est le MODÈLE de
   style** du rapport V9 ci-dessous.

**FIDÉLITÉ MAXIMALE (exigée par l'utilisateur, 2026-06-24) — toute notion calée sur le PDF.**
Pour CHAQUE notion (définition, axiome, critère, proposition, théorème, corollaire), **lire
DIRECTEMENT la page du PDF du livre** (`pages:` via Read) en plus du `Texte.tex` (V7) et du
`rapport.tex` (V8), et faire **coïncider exactement** l'énoncé formalisé avec le texte de Bourbaki.
Le noyau garantit la *soundness* (aucun faux théorème) mais PAS la *fidélité* (énoncé == Bourbaki) :
celle-ci repose sur cette relecture. Auditer aussi les notions **déjà formalisées** (surtout les
définitions) contre le PDF. En cas de conflit : le **PDF prime pour la fidélité**, le **noyau tranche
pour la soundness** (cf. la preuve LaTeX du Th2 qui diffère du PDF) ; consigner tout écart dans
`ANOMALIES.md`.

**Calibrage §→page PDF** (établi le 2026-06-24) : voir `outils_ia/pdf_index.md` (mapping
section Bourbaki → page physique du PDF de 349 pages).

## Livrable : rapport V9 (LaTeX façon livre Bourbaki)
Maintenir dans **`V9/rapport/`** un document LaTeX multi-parties expliquant TOUT le projet, agencé comme
le livre (Chapitre → Section → Sous-section), dans le **même style que `V6/V8/main.tex`** : pour chaque
résultat, énoncé Bourbaki + ce qui est formalisé + comment c'est mis en place (architecture noyau LCF) +
statut (FAIT/PARTIEL). `main.tex` + un fragment `rapport.tex` par sous-section, compilé en PDF
(`latexmk -pdf` si dispo). Tenu à jour au fil de la formalisation.
**Figures/courbes bienvenues** quand elles aident à expliquer (matplotlib → PNG, intégrées via
`\includegraphics`, comme dans V8) : métriques de recherche de preuve (nœuds, MP vérifiés), diagrammes
d'architecture (couches du noyau, frontière de confiance), courbes de couverture par chapitre, schémas de
preuve. Scripts de génération versionnés à côté des PNG (reproductibles).

## Barre de qualité : niveau ingénieur pro (le plus important)
- Avant d'écrire, **lire des modules clos exemplaires** (Zorn/Zermelo dans `ordre/`, C61 dans `entiers/`)
  et **calquer leur style** : docstring claire (énoncé + stratégie + invariants), nommage explicite,
  une responsabilité par fichier, ≤300 lignes, un test par résultat.
- S'inspirer des conventions de **bibliothèques de preuves professionnelles** (mathlib4, Isabelle/HOL & ZF,
  Metamath `set.mm`) pour la modularité, le nommage, la doc — **s'en inspirer, ne pas copier** (système
  différent : noyau LCF maison en Python).
- Cohérence avant tout : un nouveau fichier doit être **indiscernable en qualité** des meilleurs existants.

## Performance / optimisation (projet énorme → la vitesse compte)
Optimiser le code **agressivement là où c'est mesuré**, **sans JAMAIS sacrifier la correction**
(soundness du noyau, tests verts, `theorie==22`). Règles :
- **Mesurer d'abord** : profiler les chemins lents (ex. le test Hessenberg ~16 min) avant d'optimiser ;
  comparer avant/après (benchmark chiffré, jamais d'optimisation « au pif »).
- **Leviers** : mémoïsation des fonctions pures (substitution, forme canonique d'assemblage, prédicats de
  lecture) ; assemblages immuables/hashables (`__slots__`, interning) → égalité/hash O(1) ; ne pas
  reconstruire deux fois le même théorème (cache `conclusion`+`hypotheses`) ; imports paresseux, **zéro
  construction de théorème au niveau module** ; sortir les invariants des boucles.
- **Infra de test** : `pytest-xdist` (parallélisme), marqueur `slow`, fixtures cachées.
- **Garde-fou absolu** : toute optimisation du noyau préserve la frontière de confiance ; la suite
  **complète** doit rester verte après ; **jamais affaiblir une vérification du noyau** pour gagner de la
  vitesse. Tracer les gains dans le rapport V9 (courbes avant/après).

## Environnement (Windows)
- Le `.venv` est **CASSÉ** (Python 3.11 du Windows Store désinstallé). Utiliser le **`python` global**
  (3.13, pytest 9.0.3). Lancer pytest **depuis `V9/`**. Toujours `PYTHONIOENCODING=utf-8`.
- ⚠️ Les imports `cardinaux` sont lourds : un test de théorème profond (Hessenberg) prend **10–18 min**.
  Ne **jamais** piper pytest dans `| tail` (masque le code de sortie).
