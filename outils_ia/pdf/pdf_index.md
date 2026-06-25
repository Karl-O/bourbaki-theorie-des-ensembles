# Index PDF du livre — § Bourbaki → page physique (calibré 2026-06-24)

PDF : `../V6/1) Theorie Des Ensembles.pdf` — **349 pages, SCAN pur** (aucune couche texte).
Édition Hermann « Nouveau tirage 1970 ». Pagination PAR CHAPITRE : `E I.x`, `E II.x`,
`E III.x`, `E IV.x` ; puis « Résumé des résultats » `E.R.x`.

## Rendre une page en image (pour la LIRE)
`pdftoppm` fourni par MiKTeX. Depuis V9/ :
```
PP='/c/Users/KARL/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdftoppm'
PDF='../V6/1) Theorie Des Ensembles.pdf'
"$PP" -png -f <PREM> -l <DERN> -r 150 "$PDF" outils_ia/pdf/pdf_pages/p   # -> p-<NN>.png, puis Read
```
(`outils_ia/pdf/pdf_pages/` est gitignored.)

## Décalages page-imprimée → page-physique (à confirmer en lisant l'en-tête ± 1-2)
| Chapitre | formule | ancre vérifiée |
|---|---|---|
| **Ch I** (logique) | phys = `E I.p` | E I.50 = phys 50 |
| **Ch II** (ensembles) | phys = `E II.p` + 51 | E II.1 ≈ phys 52 |
| **Ch III** (ordre/cardinaux) | phys = `E III.p` + 103 | E III.6 = phys 109, E III.7 = phys 110 (en-têtes vérifiés 2026-06-24) |
| **Ch IV** (structures) | phys = `E IV.p` + 202 | E IV.101 = phys 303 |
| **Résumé** (E.R.) | phys = `E.R.p` + 303 | E.R.3 = phys 306 |

⚠ **Le texte principal a les ÉNONCÉS + les DÉMONSTRATIONS + est COMPLET.** Le Résumé des
résultats (phys 304-346) ne donne que des énoncés condensés, OMET le chapitre I, et n'est PAS
exhaustif → s'en servir seulement comme repère rapide, JAMAIS comme liste de référence.

## TABLE DES MATIÈRES PRINCIPALE (depuis le PDF, pages phys 300-303)

### CHAPITRE II — Théorie des ensembles (E II.1 ; phys ≈ E II.p+51)
- §1 Relations collectivisantes (E II.1) : 1.théorie ens. E II.1 · 2.inclusion E II.2 ·
  3.axiome extensionalité E II.3 · 4.rel. collectivisantes E II.3 · 5.axiome paire E II.4 ·
  6.schéma sélection-réunion E II.4 · 7.complémentaire, ∅ E II.6
- §2 Couples (E II.7) : 1.déf couples E II.7 · 2.produit deux ens. E II.8
- §3 Correspondances (E II.9) : 1.graphes E II.9 · 2.corr. réciproque E II.11 · 3.composée E II.11 ·
  4.fonctions E II.13 · 5.restrictions/prolongements E II.15 · 6.fonction par un terme E II.15 ·
  7.composée fonctions/fonction réciproque E II.16 · 8.rétractions et sections E II.18 ·
  9.fonctions de deux arguments E II.21
- §4 Réunion/intersection d'une famille (E II.22) : 1.déf E II.22 · 2.propriétés E II.24 ·
  3.images E II.25 · 4.complémentaire E II.26 · 5.réunion/inter de deux ens. E II.26 ·
  6.recouvrements E II.27 · 7.partitions E II.29 · 8.somme d'une famille E II.29
- §5 Produit d'une famille (E II.30) : 1.axiome 𝔓(E) E II.30 · 2.ens. applications E II.31 ·
  3.déf produit E II.32 · 4.produits partiels E II.33 · 5.associativité E II.35 ·
  6.distributivité E II.35 · 7.extension aux produits E II.38
- §6 Relations d'équivalence (E II.39) : 1.déf E II.39 · 2.classes/quotient E II.41 ·
  3.compatibles E II.42 · 4.parties saturées E II.43 · 5.applications compatibles E II.44 ·
  6.image réciproque/relation induite E II.45 · 7.quotients E II.45 · 8.produits E II.46 ·
  9.classes d'objets équiv. E II.47
- Exercices §1-6 : E II.49-51

### CHAPITRE III — Ensembles ordonnés, cardinaux, entiers (E III.1 ; phys ≈ E III.p+102)
- §1 Relations d'ordre (E III.1) : 1.déf ordre E III.1 · 2.préordre E III.2 · 3.notations E III.4 ·
  4.sous-ens./produit ordonnés E III.5 · 5.applications croissantes E III.7 ·
  6.max/min E III.8 · 7.plus grand/petit élément E III.8 · 8.majorants/minorants E III.9 ·
  9.borne sup/inf E III.10 · 10.filtrants E III.12 · 11.réticulés E III.13 ·
  12.totalement ordonnés E III.13 · 13.intervalles E III.14
- §2 Ensembles bien ordonnés (E III.15) : 1.segments E III.15 · 2.récurrence transfinie E III.17 ·
  3.Zermelo E III.19 · 4.inductifs E III.20 · 5.isomorphismes E III.21 · 6.lexicographiques E III.22
- §3 Équipotents, Cardinaux (E III.23) : 1.cardinal E III.23 · 2.ordre cardinaux E III.24 ·
  3.opérations E III.25 · 4.cardinaux 0 et 1 E III.27 · 5.exponentiation E III.28 ·
  6.ordre+opérations E III.29
- §4 Entiers naturels, ensembles finis (E III.30) : 1.déf entiers E III.30 · 2.inégalités E III.31 ·
  3.récurrence E III.32 · 4.parties finies E III.34 · 5.caractère fini E III.34
- §5 Calcul sur les entiers (E III.35) : 1.opérations E III.35 · 2.inégalités strictes E III.36 ·
  3.intervalles d'entiers E III.37 · 4.suites finies E III.38 · 5.fonctions caractéristiques E III.38 ·
  6.division euclidienne E III.39 · 7.base b E III.40 · 8.analyse combinatoire E III.41
- §6 Ensembles infinis (E III.45) : 1.ℕ E III.45 · 2.applications par récurrence E III.46 ·
  3.cardinaux infinis E III.47 · 4.dénombrables E III.49 · 5.suites stationnaires E III.50
- §7 Limites projectives/inductives (E III.51) : 1.proj. E III.51 · 2.systèmes proj. E III.52 ·
  3.double proj. E III.56 · 4.conditions non-vide E III.57 · 5.inductives E III.60 ·
  6.systèmes ind. E III.62 · 7.double ind. E III.66
- Exercices §1-7 : E III.69-94 · Note historique : E III.97

### CHAPITRE IV — Structures (E IV.1 ; phys ≈ E IV.p+202)
- §1 Structures et isomorphismes (E IV.1) : 1.échelons E IV.1 · 2.extensions canoniques E IV.2 ·
  3.relations transportables E IV.3 · 4.espèces de structure E IV.4 · 5.isomorphismes/transport E IV.6 ·
  6.déduction E IV.7 · 7.espèces équivalentes E IV.9
- §2 Morphismes et structures dérivées (E IV.11) : 1.morphismes E IV.11 · 2.plus fines E IV.12 ·
  3.initiales E IV.14 · 4.ex. initiales E IV.15 · 5.finales E IV.19 · 6.ex. finales E IV.21
- §3 Applications universelles (E IV.22) : 1.ens./applications universels E IV.22 ·
  2.existence E IV.23 · 3.exemples E IV.25
- Note historique I-IV E IV.33 · Bibliographie E IV.77 · Index notations E IV.80 · Index terminologique E IV.83

### CHAPITRE I — Description de la mathématique formelle (E I.1 ; phys = E I.p)
(Détail à lire depuis les pages TOC phys 298-299 quand on traitera la logique : §1 termes/relations,
§2 théorèmes/axiomes S1-S8, §3 théories logiques C1-C..., §4 quantifiés, §5 égalitaires, Appendice.)

## RÉSUMÉ DES RÉSULTATS (secondaire — énoncés condensés, sans preuves, INCOMPLET)
TOC à phys 349 : §1 Éléments/parties E.R.1 (phys 304) · §2 Fonctions E.R.5 (308) ·
§3 Produit E.R.11 (314) · §4 Réunion/famille E.R.16 (319) · §5 Équivalence E.R.22 (325) ·
§6 Ordonnés E.R.25 (328) · §7 Puissances/dénombrables E.R.32 (335) · §8 Structures E.R.34 (337) ·
Index notations E.R.38 (341) · Index terminologique E.R.40 (343).
