# Théorie des ensembles de Bourbaki — formalisation vérifiée par noyau (V9)

## Objectif (le nord)
**Retranscrire INTÉGRALEMENT le livre *Théorie des ensembles* de N. Bourbaki dans le code**,
chaque résultat nommé (définition, axiome, critère C/CS/CF, proposition, théorème, corollaire)
devenant un objet `Theoreme` **certifié par le noyau LCF**. « Démontré dans le livre » doit
coïncider avec « vérifié par la machine ». Un résultat n'est *FAIT* que s'il est clos
(0 hypothèse non déchargée) et que son énoncé == celui de Bourbaki ; sinon il est *PARTIEL*.

## Frontière de confiance (ne JAMAIS la franchir)
- Un `Theoreme` ne se crée qu'avec les **primitives du noyau**
  (`bourbaki/i_description_mathematique_formelle/i_2_theoremes/noyau/noyau*.py`,
  exposées via `N.*` : `assume, modus_ponens, loi_deduction, generalisation, existe_temoin,
  s1..s7, axiome, instancie`). **Jamais** de `_CLE`, de `Theoreme(...)` fabriqué à la main,
  de monkeypatch.
- Invariant : `theorie_ensembles()` doit valoir **22 axiomes**. N'en ajouter aucun à la légère.

## Conventions de structure
1. **Un fichier = une responsabilité, ≤ 300 lignes** (la limite vise la complexité du *code* ;
   les lignes de commentaire de traçabilité `@livre` n'entrent pas dans ce compte).
2. **≤ 10 entrées par dossier** (fichiers + sous-dossiers **confondus**). Dès qu'un dossier
   atteint 10, on l'**éclate en sous-dossiers nommés d'après la section du livre**.
3. **L'arborescence calque la table des matières du livre** (chapitre → section → sous-section
   → thème). Conséquence voulue : un **trou de couverture devient visible structurellement**
   (dossier vide ou absent = résultat du livre pas encore formalisé).
4. **`tests/` calque `bourbaki/` à l'identique** (même arbre, mêmes noms).
5. **Tests verts avant d'avancer.**

## Arborescence effective (depuis le 2026-07-02 : un paquet = un chapitre du livre)
- `bourbaki/i_description_mathematique_formelle/` — Chap. I (couches assemblages + formules + noyau
  réunies) : `i_1_termes_relations` (assemblage.py couche 0 + formule/lecture/notation/criteres_CS/CF),
  `i_2_theoremes` (demonstration.py couche 0 + `noyau/` + `criteres/` + `tactiques/` + `verification/`),
  `i_3_theories_logiques`, `i_4_theories_quantifiees` (ex `logique/i_3_quantifies`),
  `i_5_theories_egalitaires` (ex `logique/i_4_egalitaires`). `assemblage.py` = façade de ré-exports.
- `bourbaki/ii_theorie_des_ensembles/` — Chap. II : sections ii_1_relations_collectivisantes
  (contient `ensembles_abrege.py`), ii_2_couples, ii_3_correspondances (9 sous-sections),
  ii_4_reunion_intersection_famille, ii_5_produit_famille, ii_6_relations_equivalence.
- `bourbaki/iii_ensembles_ordonnes_cardinaux_entiers/` — Chap. III : iii_1_relations_ordre,
  iii_2_bien_ordonnes, iii_3_equipotence_cardinaux, iii_3_3_operations_cardinaux (ex `arithmetique`,
  au top pour cause MAX_PATH), iii_4_entiers_finis, iii_5_calcul_entiers, iii_6_infinis, iii_7_limites.
- `bourbaki/iv_structures/` — Chap. IV : iv_1, iv_2, iv_3_applications_universelles.
⚠️ MAX_PATH Windows actif (LongPathsEnabled=0) : les chemins profonds du III frôlent 260 —
tout renommage doit raccourcir ou rester neutre.

## Table des matières de référence (cible de l'arbre)
- **Chap. I** Logique : I.1 termes/relations · I.2 critères déductifs C · I.3 quantifiés · I.4 égalitaires
- **Chap. II** Ensembles : II.1 collectivisantes/axiomes · II.2 couples/produit · II.3 correspondances/fonctions ·
  II.4 réunion/intersection de familles · II.5 produit d'une famille · II.6 relations d'équivalence
- **Chap. III** Ordre & cardinaux : III.1 relations d'ordre · III.2 bon ordre · III.3 équipotence/cardinaux ·
  III.4 entiers/finis · III.5 calcul sur les entiers · III.6 ensembles infinis · III.7 limites proj./induct.
- **Chap. IV** Structures : IV.1 structures/isomorphismes · IV.2 morphismes/structures dérivées · IV.3 applications universelles

## Suivi de couverture  (mis à jour le 2026-08-19 — VÉRIFIÉ en code)

**LA PREMIÈRE COMMANDE À LANCER, avant et après chaque session :**
```
python outils_ia/audit/verifie.py
```
Six constats, **un seul verdict**, code de retour 0/1 : axiomes 22 · 0 SyntaxError ·
marqueurs et trous · manifestes (notions, non conformes, parties complètes) ·
reports suspects · tests. ⚠️ Sa règle cardinale : **il n'annonce JAMAIS vert ce
qui n'a pas tourné** — sans `--tests` il dit « NON LANCÉ », pas « OK ». Trois
notifications « exit 0 » de ce projet se sont avérées être des timeouts ; on ne
lit un verdict qu'à la dernière ligne du fichier de sortie.

**État au 2026-08-19** : **2230 notions** aux manifestes, 1983 marqueurs `@livre`,
**179 trous** intra-page, 51 reports dont 6 suspects, 0 marqueur non conforme, les
cinq parties « complet sur l'intervalle » (E I 14-46, E II 1-48, E III 2-66 + 87,
E IV 1-26, E R 3-32).

**LE TAUX QUI RÉPOND À LA QUESTION DU PROJET — 50,7 %.**
`python outils_ia/audit/statut_notions.py --noyau` croise chaque `@livre` avec le
VERDICT DU NOYAU (nombre d'hypothèses non déchargées). Sur les 1142 notions de type
démontrable (Prop/Th/Cor/Crit/Lem/Demo/Sch/Ax), 815 sont tranchées : **413 FAIT**
(0 hypothèse) contre 402 PARTIEL. C'est la première réponse chiffrée à
« démontré dans le livre » == « vérifié par la machine ». Il signale aussi 23
REPORTS PÉRIMÉS et 92 déclarations trop fortes — à vérifier une par une, il
signale, il ne juge pas la nuance d'une docstring.

`outils_ia/audit/couverture.py` est PÉRIMÉ : ne pas s'y fier. Les outils qui font foi :
- `gen_livre_manifestes.py` — couverture **page par page**. ⚠️ « couvert » = chaque
  page a ses notions marquées `@livre`, **pas** que tout est démontré. Ce détecteur
  est SATURÉ (5/5 parties complètes) : il ne peut plus rien trouver.
- `gen_trous_livre.py` — granularité **ligne**, le seul qui voie encore quelque
  chose. Ses 211 trous ont été triés le 18 août par lecture du PDF : **41 % n'en
  étaient pas** (démonstrations non annotées). Reste 93 vrais manques.
- `audit_reports.py` — croise `REPORTES` et `@livre`, signale les reports PÉRIMÉS.
  **Lancer AVANT d'attaquer un report et TESTER EN CODE (import + appel)** : 4
  périmés trouvés en 24 h début août — on risque de réécrire un acquis.

**LA FILE DE TRAVAIL EST `docs/couverture/CIBLES_VERIFIEES_2026-08-19.md`**, pas le
tri. Sur les 38 cibles « HAUTE » du tri, **20 avaient déjà une `def`** dans le
dépôt : les attaquer telles quelles, c'était réécrire vingt notions existantes.
17 sont vraiment ABSENTES. ⚠️ Une `def` au bon nom ne prouve ni que son énoncé est
celui de Bourbaki, ni qu'elle est close — lire la fonction ET la page.

**LES TESTS, ET CE QU'ILS COÛTENT VRAIMENT** (mesuré le 18 août) :
- suite complète : `pytest tests/ -q -n 12 --dist loadfile` → **4210 passed en
  2 h 20**. C'est un contrôle à lancer AVANT d'annoncer un résultat, pas à chaque
  commit.
- porte « not slow » : **1 h 18**. Utile, mais pas un garde-fou de commit.
- ⚠️ **Il n'existe PAS de porte de 5 minutes, et ce n'est pas faute d'avoir
  essayé.** Sous `--dist loadfile` un fichier ne se découpe pas : le plus lourd
  impose 54 min ; même test par test, le plus lent en fait 40 à lui seul. Et le
  coût est DIFFUS — après retrait des 21 fichiers les plus lourds il reste 1 h 18.
- **La porte de commit est donc** : `verifie.py` sans les tests (≈1 min) **plus les
  tests des fichiers touchés**. Pour un lot qui touche `tests/`,
  `pytest --collect-only` attrape les imports cassés en quelques secondes.

⚠️ **CE QU'AUCUN TEST N'ATTRAPERA.** Le noyau garantit la SOUNDNESS, jamais la
FIDÉLITÉ. Un marqueur qui ment sur le livre laisse la suite verte, les 22 axiomes
en place et les manifestes conformes — c'est arrivé le 18 août (trois `Demo.-`
posés sur des clôtures d'énoncé de C39/C40/C42, où Bourbaki n'imprime AUCUNE
démonstration, corrigé en 452f071). Seule l'ouverture de la page le révèle.

Gros chantiers : **FAITS** — Hessenberg a²=a (III.6), division euclidienne (III.5),
trichotomie/bon ordre des cardinaux (III.3), Cantor, **CST1 + CST1-identité + CST2 +
CST3 + capstone ⟨f⁻¹⟩^S∘⟨f⟩^S=Δ (IV.1.2)**, réversion/composition d'isomorphismes
réelles (IV.1.5), **Prop. 6 §III.7.6 intégrale** (1° existence + unicité, 2°, 3°),
**C57 II.6.5** (existence + unicité, sans axiome du choix), Prop. 1 §III.7.2,
**décomposition canonique II.6.5** (`ensembles_pont_theta` :
b_construite_injective 1 hyp, b_construite_surjective 2 hyps — vérifié en code),
**Prop. 3 §III.7.2 — LES DEUX SENS, prouvés ET quantifiés**, sans axiome du choix
(injectivité universelle 2 hyps, surjectivité universelle 4 hyps), plus
**l'application canonique g CONSTRUITE** (`prop1_proj/ensembles_g_construite` :
func + dom CLOS, et la formule (3) DÉMONTRÉE — l'axiome `axiome_canonique_g`
est donc superflu).
**OUVERTS** : 2ᵉ assertion de la Prop. 2 §III.7.2 (u⁻¹(x')=lim← M_α — exige le
pont d'encodage famille-de-parties), Prop. 5 et Théorème 1 §III.7.4 (énoncés
posés, preuves reportées), et la MIGRATION des consommateurs du terme opaque
`application_canonique_g` vers `graphe_g` — mécanique, mais **prérequis** pour
écrire `est_bijection_de(g, …)` : ne pas conjoindre des énoncés portant sur deux
termes différents (garde consignée dans `ensembles_g_construite.REPORTES`).

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
`docs/journal/ANOMALIES.md`.

**Calibrage §→page PDF** (établi le 2026-06-24) : voir `outils_ia/pdf/pdf_index.md` (mapping
section Bourbaki → page physique du PDF de 349 pages).

## Traçabilité livre — marqueur `@livre` (page + lignes de CHAQUE notion)
**But (exigé par l'utilisateur, 2026-06-25).** Chaque notion formalisée (définition, axiome,
critère, proposition, théorème, **démonstration**, corollaire) porte **une ligne machine-lisible**
qui la cale exactement sur le livre : repère Bourbaki + **intervalle de lignes** + page physique du
PDF. Méthode en deux passes : (1) lire le livre et écrire en **notant la position** de chaque
notion ; (2) repasser, et en **triant tout par (chapitre, page, ligne)**, faire apparaître les
**trous** — un intervalle de lignes non couvert = une notion oubliée. *La citation EST le détecteur
de trous.*

**Format exact** (commentaire Python, juste au-dessus de la `def` de la notion) :
```
# @livre Ch.<C> §<s>.<ss> <Type>.<num> | <repère Bourbaki> L.<l1>-<l2> | PDF p.<phys>
```
- `<C>` = `I`..`IV` (ou `R` pour le Résumé) ; `<s>.<ss>` = section.sous-section (ex. `1.2`).
- `<Type>` ∈ {`Def`,`Ax`,`Crit`,`Prop`,`Th`,`Cor`,`Lem`,`Sch`,`Rem`,`Ex`,`Demo`,`Meta`} ; `<num>` = n° Bourbaki (sinon `-`).
  `Meta` = métathéorème (résultat démontré SUR le formalisme, ex. signes initiaux E I.19) :
  prose + preuve en commentaire, JAMAIS un `Theoreme` du noyau. Les blocs de PROSE du livre
  (remarques intuitives, exemples non formalisables) reçoivent aussi leur `@livre` (`Rem`/`Ex`)
  avec une note « prose, rien à formaliser » — ainsi CHAQUE ligne du livre est comptabilisée.
- `<repère Bourbaki>` = repère imprimé du livre, ex. `E III.2` (E = pagination interne du livre).
- `L.<l1>-<l2>` = lignes sur CETTE page (une démo placée ailleurs a son **propre** `@livre`).
- `PDF p.<phys>` = page physique du scan. Offsets : Ch I `+0`, II `+51`, III `+103`, IV `+203`, Résumé `+303`.
  (Ancres vérifiées en-tête : E III.7=p.110, E III.66=p.169 ; E IV.1=p.204, E IV.2=p.205, E IV.3=p.206. Ces offsets sont des **ancres** : toujours confirmer l'en-tête imprimé de la page rendue, car la pagination peut dériver d'1 page dans une queue d'exercices.)
- Exemple : `# @livre Ch.III §1.2 Prop.1 | E III.2 L.3-14 | PDF p.109`

**Règle.** Toute notion écrite ou auditée **à partir de maintenant** reçoit son `@livre`. Le
retrofit de l'existant se fait **section par section** (passe 1 : poser les `@livre` depuis le PDF ;
passe 2 : trier + lister les trous). L'outil `outils_ia/audit/gen_trous_livre.py` collationne les
`@livre` (tri chapitre/page/ligne, signale les intervalles non couverts ; option `--md`).

**Manifestes par dossier — `LIVRE.md` (exigé par l'utilisateur, 2026-07-04).**
`python outils_ia/audit/gen_livre_manifestes.py` écrit dans **chaque dossier** de `bourbaki/` un
`LIVRE.md` généré (NE PAS éditer à la main) : notions du dossier triées par **page imprimée du
livre** (le repère `E III.10` en haut de page — PAS la page du PDF) + lignes, fichiers **à caler**
(sans `@livre` ; `__init__.py`/`outil_*.py` exclus), cumul des sous-dossiers, et bilan remonté
récursivement jusqu'à `bourbaki/LIVRE.md` qui liste par chapitre les **pages du livre manquantes**
— le verdict « rien d'oublié » se lit à la racine. Régénérer après chaque pose de `@livre`.
Les `LIVRE.md` **ne comptent pas** dans la règle « ≤10 entrées par dossier » (fichiers générés).

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
