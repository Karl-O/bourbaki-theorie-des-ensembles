# Index PDF du livre — mapping § Bourbaki → page physique (calibré 2026-06-24)

PDF : `../V6/1) Theorie Des Ensembles.pdf` — **349 pages, SCAN pur** (aucune couche texte).
Édition Hermann, « Nouveau tirage 1970 ».

## Rendre une page en image (pour la lire)
`pdftoppm` est fourni par MiKTeX. Depuis V9/ :
```
PP='/c/Users/KARL/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdftoppm'
PDF='../V6/1) Theorie Des Ensembles.pdf'
"$PP" -png -f <PREMIERE> -l <DERNIERE> -r 150 "$PDF" outils_ia/pdf_pages/p
# -> outils_ia/pdf_pages/p-<NN>.png  (puis Read l'image)
```
(Le dossier `outils_ia/pdf_pages/` est gitignored.)

## Ancres de pagination
- **Chapitres (texte principal)** : pagination par chapitre `E <chap>.<page>`.
  Ancre connue : **E I.50 = page physique 50** (chap. I, exercices/appendice).
  → pour le chap. I, page physique ≈ page imprimée. Offsets II/III/IV : à calibrer
  au besoin (rendre une page, lire l'en-tête `E II.x` / `E III.x` / `E IV.x`).
- **Résumé des résultats** (récap concis de TOUTES les notions, chap. II-IV) :
  pagination `E.R.<page>`, **page physique = E.R.page + 303** (E.R.3 = phys 306 ✓).

## RÉSUMÉ DES RÉSULTATS — la référence de fidélité (énoncés sans preuves)
Table (depuis la TOC du Résumé, page phys 349) — section → E.R.page → page physique :

| Résumé § | Titre | E.R. | phys |
|---|---|---|---|
| §1 | Éléments et parties d'un ensemble | E.R.1 | 304 |
| §2 | Fonctions | E.R.5 | 308 |
| §3 | Produit de plusieurs ensembles | E.R.11 | 314 |
| §4 | Réunion, intersection, produit d'une famille | E.R.16 | 319 |
| §5 | Relations d'équivalence ; ensemble quotient | E.R.22 | 325 |
| §6 | Ensembles ordonnés | E.R.25 | 328 |
| §7 | Puissances. Ensembles dénombrables | E.R.32 | 335 |
| §8 | Échelles d'ensembles et structures | E.R.34 | 337 |
| — | Index des notations | E.R.38 | 341 |
| — | Index terminologique | E.R.40 | 343 |
| — | (TOC du Résumé) | — | 349 |

Le Résumé NUMÉROTE chaque notion (1, 2, 3, …) et donne défs + énoncés. Il couvre
la théorie des ensembles (chap. II-IV) ; il PRÉSUPPOSE la logique (chap. I), qu'il
ne récapitule pas — pour les critères C1-C61 et la logique, utiliser le texte
principal (`E I.x`).

## Correspondance Résumé § ↔ chapitres du livre / arbre du code
- Résumé §1 (Éléments/parties) ↔ II.1 (relations collectivisantes, ⊂, ∅, 𝔓)
- Résumé §2 (Fonctions) ↔ II.3 (correspondances, fonctions, rétractions/sections)
- Résumé §3 (Produit de plusieurs ensembles) ↔ II.2 (couples, produit)
- Résumé §4 (Réunion/intersection/produit d'une famille) ↔ II.4 + II.5
- Résumé §5 (Relations d'équivalence) ↔ II.6
- Résumé §6 (Ensembles ordonnés) ↔ III.1 + III.2
- Résumé §7 (Puissances/dénombrables) ↔ III.3-III.6 (cardinaux, entiers, infinis)
- Résumé §8 (Échelles/structures) ↔ IV
