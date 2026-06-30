# Corpus de preuves → dataset generate-and-verify (pivot méta-algo)

Premier pas du **pivot méta-algo** (cf. `docs/couverture/STATUT_REEL_2026-06-30.md`) : la
formalisation Bourbaki étant quasi-complète, le corpus devient le **carburant** d'un
générateur *generate-and-verify* (l'IA propose une preuve/théorie, le **noyau LCF la
certifie**). Le substrat est mûr : ≈616 modules, ≈939 traces `@livre`, le « pourquoi »
et les erreurs documentés.

## Ce que produit `export_corpus.py`

Un fichier **JSONL**, un objet par théorème, forme **(BUT ⟶ PREUVE)** :

| champ | sens |
|---|---|
| `name`, `module` | identité de la fonction-théorème |
| `livre` | marqueur `@livre` (Ch/§/page PDF) — **ancre vers le livre** |
| `clos`, `n_hyp` | statut : clos (0 hyp.) ou conditionnel honnête |
| `justification` | dernière règle noyau appliquée (ex. `MP(C1)`, `S6`, `loi_deduction`) |
| `conclusion_ast` | **AST canonique** de la formule-but (repr fidèle, ré-parsable) = le BUT |
| `hypotheses_ast` | AST de chaque hypothèse honnête |
| `proof_src` | **source de la fonction = le PROGRAMME-preuve** (la trajectoire) = la CIBLE |
| `verified` | `True` si `conclusion == cible` re-vérifié via le companion `*_cible` |

Le **vérificateur** est gratuit et exact : ré-exécuter `proof_src` et vérifier
`conclusion == conclusion_ast`. C'est la récompense dense, jamais bruitée, du générateur.

## Usage
```
python outils_ia/corpus/export_corpus.py [module1 module2 ...] > sortie.jsonl
```
Sans argument : liste « fast » par défaut (évite les imports cardinaux 13-18 min).
`corpus_sample.jsonl` = échantillon de démonstration (22 théorèmes, 8 modules fast).
Le corpus complet est **régénérable** (ne pas le committer en entier — volumineux).

## Trajectoire pas-à-pas — la « marche sur le DAG » (pas 2, FAIT)

`Theoreme` ne stocke que `(hypotheses, conclusion, justification)` — **pas ses
prémisses**. Pour obtenir le DAG fin, `trace_preuve.py` **observe le noyau** : il
enveloppe temporairement les primitives `N.*` (observateur pur, soundness intacte — il
appelle la vraie primitive et la consigne, sans pouvoir forger de `Theoreme`) et
enregistre chaque pas `{i, rule, inputs:[indices], concl, clos}` = la trajectoire
primitive-par-primitive.

```
python outils_ia/corpus/trace_preuve.py <module> <fonction>   # affiche le DAG
```
`export_corpus.py` intègre un **résumé** par théorème : `trace_len` (nb de pas primitifs
= profondeur DAG) et `rule_hist` (histogramme des règles). Échantillon 8 modules :
**205 861 pas primitifs**, médiane ≈5 557 pas/théorème (ex. `couple_diagonale` = 6 707 pas) ;
règles dominantes `modus_ponens`, `assume`, `loi_deduction`, `s3`. La trajectoire COMPLÈTE
(avec AST par pas) est volumineuse → régénérée à la demande, pas committée.

C'est la donnée idéale pour diffusion discrète / GFlowNet : **forward** = effacer des pas,
**reverse** = les reconstruire, **kernel** = filtre de validité à chaque pas. Voir mémoire
`meta-algo-diffusion-marche`.

## Export large + exemples négatifs (pas 3, FAIT)

- **Export large** : `export_corpus.py --discover [packages]` auto-découvre tous les
  modules sous des packages (défaut : `logique`, `ensembles`, `ordre`, `structures` —
  PAS cardinaux/entiers, lents). `--no-trace` pour la vitesse (pas de trajectoire).
  Les fonctions-théorème à ARGUMENTS sont appelées via des témoins génériques (`_appel`).
  Mesure : `logique`+`ensembles` ⇒ **282 théorèmes** (97 modules, 0 erreur d'import).
  Le corpus complet (`corpus_full.jsonl`) est **gitignoré** (régénérable, gros).
- **Exemples négatifs** : `export_erreurs.py` parse `DECISIONS.md`/`ANOMALIES.md` en JSONL
  de **marches mortes étiquetées** (`tautologie-rejetee`, `verrou-tau`, `choix-bloque`,
  `fidelite`, `lecon`…). Échantillon `erreurs_sample.jsonl`. Données pour PÉNALISER ces
  patterns côté générateur (le « pourquoi » des erreurs, documenté, devient de la donnée).

## Proto generate-and-verify (pas 5, FAIT) — `proto_mutation_verify.py`

Premier bout-à-bout du générateur. On CORROMPT une preuve valide d'un cran (supprimer
un pas / échanger deux pas = le *forward process* de la diffusion) et le NOYAU tranche :
`ERROR` (le code casse) · `WRONG` (s'exécute mais ≠ cible — rejeté) · `OK` (encore correct
= pas redondant). Mesure (module `diagonale_couple`, 6 théorèmes) : **152 mutants 1-pas,
85 % rejetés** par noyau+cible. Chaque rejet = une **paire (corrompu → valide)** pour
entraîner le *reverse process* (débruitage = réparer la preuve) ; chaque `OK` = slack local.
Soundness intacte : un mutant ne fabrique jamais un faux théorème (juste un vrai différent,
recalé par la cible). `python outils_ia/corpus/proto_mutation_verify.py [module] [noms...]`.

## Dataset de paires (corrompu → valide) — forward process (pas 6, FAIT)

`gen_paires_corruption.py` engendre des TRAJECTOIRES de corruption progressive (x0 valide
→ x1 → … → xK, k corruptions 1-pas), le noyau étiquetant chaque état. JSONL par état :
`{valide_src (x0), parent_src (x_{k-1}), corrompu_src (xk), n_corruptions, statut: OK|WRONG|ERROR}`.
→ donnée du *reverse process* : **(corrompu → parent)** = un pas de débruitage (cadre diffusion),
**(corrompu → valide)** = débruitage complet ; `statut` = récompense dense du noyau. Mesure
(`diagonale_couple`) : la validité CHUTE avec la profondeur (K=1 : 5 % valides → K≥2 : ~0 %),
97 % rejetés — exactement le *noising schedule* de la diffusion. Échantillon
`paires_corruption_sample.jsonl` ; graine fixe (reproductible).

## Reverse process : repaireur 1-pas (pas 7, FAIT) — `proto_repair.py`

Le pas de DÉBRUITAGE atomique : une preuve corrompue par suppression d'un pas → chercher
dans la bibliothèque quel candidat, ré-inséré, fait re-accepter le noyau. Mesure
(`diagonale_couple`) : 79 corruptions, **1193 essais filtrés**, **100 % récupérées** par
recherche+noyau (l'oracle passe toujours ; tout le reste rejeté) ; 0 réparation alternative
(pool local minimal → preuves « tendues »). = la brique du *reverse process*, encore en
brute-force (pas appris).

## Proof-of-concept COMPLET (pas 1→7)

Les DEUX directions de la diffusion sont démontrées, **noyau = oracle exact partout** :
forward (corrompre + filtre, 85 % rejeté) · dataset de paires (corrompu→valide, validité
chute avec K) · reverse (réparer = chercher + filtre, 100 % récupérable). Le mécanisme
generate-and-verify FONCTIONNE end-to-end.

## Repaireur APPRIS (pas 8-9, FAIT) — `repair_learned.py` — « ça apprend à marcher »

Premier composant APPRIS du reverse process : un classifieur sklearn (LogisticRegression)
qui, vu le CONTEXTE d'un trou (tactiques voisines + position + **signal data-flow** : le
candidat fournit-il la variable manquante ?), prédit quel candidat répare. On range les
candidats par P(repair) et on n'appelle le noyau que sur les mieux classés.

Mesure (5 modules, 2547 candidat-insertions, 12 théorèmes, **GroupKFold = test sur preuves
JAMAIS vues**), features enrichies (data-flow + n_args/uses_N/n_assignes/pos) :
- **LogReg accuracy CV 0.998** | **RandomForest 0.999** (robuste, pas un artefact d'un modèle) ;
- rang moyen de la 1ʳᵉ vraie réparation : **1.00** (modèle classe le bon repair EN TÊTE à
  chaque fois) vs **8.82** (brute-force) → **89 % d'appels-noyau en moins** ;
- **importance des features (RandomForest)** : `fournit_manquante` (data-flow) = **0.69**,
  écrasant tout le reste → on a QUANTIFIÉ ce que le modèle apprend.

Le signal décisif est donc la **structure data-flow** de la preuve (le pas supprimé
définissait une variable lue plus loin ; le candidat qui la re-fournit est la réparation).
Le NOYAU reste l'oracle exact qui valide. → la politique apprise **bat la force brute,
généralise, et est robuste cross-modèle**. C'est l'embryon du générateur ; reste à l'enrichir
(politique séquentielle, niveau-tactique, bibliothèque inter-preuves, GFlowNet/diffusion ; torch dispo).

## Politique SÉQUENTIELLE (pas 12-13-15, FAIT) — `proto_sequential.py` : la marche guidée multi-pas

On supprime K pas et on RECONSTRUIT en chaînant la repair-policy apprise + filtre noyau final
= generate(politique)+verify(noyau), testé sur preuves **TENUES À L'ÉCART**. Trois stratégies :
- **INDÉPENDANT** — top-1 du modèle par trou, sans interaction ;
- **ITÉRATIF** (pas 13) — greedy + recompute : remplir le trou de plus haute confiance d'abord,
  RECALCULER les features (les manquantes diminuent), recommencer ;
- **BEAM** B=4 (pas 15) — garder les **B reconstructions partielles** les plus probables (somme de
  log-probas) ; à chaque pas, étendre chaque beam par les B meilleurs candidats de chaque trou et
  ne conserver que les B meilleurs états. Le NOYAU ne juge QU'À LA FIN, sur les ≤B beams complets.

| K (pas supprimés) | indépendant | itératif (pas 13) | **beam B=4 (pas 15)** |
|---|---|---|---|
| 1 | 100 % | 100 % | **100 %** |
| 2 | 45 % | 83 % | **100 %** |
| 3 | 8 %  | 29 % | **100 %** |
| 4 | 0 %  | 62 % | **100 %** |
| 5 | 0 %  | 25 % | **75 %** |

(K≤3 : 24 essais = 3 preuves × 8 ; K=4-5 : 8 essais — seule `composee_monotone` a ≥4 pas.)
L'itératif relève déjà K≥2 ; le **BEAM tient 100 % jusqu'à K=4** et ne fléchit qu'à **K=5 (75 %)**,
là où l'indépendant est à 0 % dès K=4. Garder B trajectoires lève l'ambiguïté d'assignation
multi-trous bien au-delà du greedy ; le noyau ne juge qu'à la fin (≤B appels) =
generate(politique) + verify(noyau). Frontière visible (pas de saturation triviale) à K=5.

## Bibliothèque INTER-preuves (pas 14, FAIT) — `proto_inter_preuves.py` : vocabulaire PARTAGÉ

Jusqu'ici la « bibliothèque » candidate = les pas de la preuve COURANTE seulement → on
**recombine UNE preuve**, on ne génère pas. Ici on construit un **pool PARTAGÉ** (tous les pas
de TOUTES les preuves du module) et son **vocabulaire de TEMPLATES** = les couples
*(tactique, arité)* distincts. On teste alors si un trou (suppression 1-pas) se comble par une
brique venue d'AILLEURS, sous deux régimes — le NOYAU validant (OK == cible) :
- **VERBATIM** — ré-insérer le pas étranger tel quel ;
- **TEMPLATE-TRANSPLANT** — *régénérer* le pas depuis un template + **recherche de binding
  local** (renommer la sortie vers la variable manquante = data-flow, re-lier les lectures aux
  variables locales disponibles ; on ne re-lie que les variables proof-locales, les tactiques/`N`
  restent intactes ; bornes : ≤2 lectures re-liées, budget dur d'essais/trou car la
  ré-exécution-noyau par variante coûte 1–70 ms selon la preuve).

Mesure sur **97 trous** = `projection` + `identite` (multi-preuves symétriques, 36) **et**
`diagonale_couple` (5 preuves HÉTÉROGÈNES : projections, composées, réciproque ; 61 — la 6ᵉ,
`couple_diagonale` = 6707 pas primitifs, exclue car ~20–30 ms/essai-noyau × milliers d'essais) :

| régime | comblés / 97 | lecture |
|---|---|---|
| local (oracle, sanity) | 97 (100 %) | la preuve est réparable par sa propre brique |
| **VERBATIM** (pas étranger tel quel) | **1 (1 %)** | un pas littéral ne transfère quasi JAMAIS : les variables diffèrent |
| **TEMPLATE-TRANSPLANT** | **33 (34 %)** | le pas se **régénère** depuis le vocabulaire de templates + binding |
| dont **tactique ÉTRANGÈRE** (signature absente de la preuve) | **0 (0 %)** | jamais besoin d'une tactique que la preuve n'emploie pas déjà |

**Ce que ça établit (résultat net, pas seulement positif).**
1. Le vocabulaire partagé opère au niveau **(tactique + binding)**, pas du statement littéral :
   régénérer ≠ recaler verbatim (**1 % → 34 %**). C'est le 1er pas concret vers *générer* un pas
   hors des statements de la preuve courante (le noyau validant), pas permuter une preuve.
2. **L'import d'une tactique genuinement étrangère = 0 %**, et ce **même sur le module hétérogène**
   (les templates étrangers sont essayés EN PREMIER et échouent tous ; seuls des *self-templates*
   re-bindés régénèrent le pas). Conclusion : dans ce corpus, le **multiset de tactiques de chaque
   preuve se suffit** — le gain d'une bibliothèque inter-preuves vient du **re-binding de tactiques
   COMMUNES** (partager un *prior* de binding entre preuves), pas de l'import de tactiques neuves.

**Conséquence design** : le levier inter-preuves prometteur n'est pas l'import 1-pas d'une tactique
absente (rendement nul ici) mais (i) un **prior de binding** partagé qui réduit la recherche, et
(ii) le **library-learning** = abstraire des **macros multi-pas récurrentes** entre preuves (≠ un
seul pas). `python outils_ia/corpus/proto_inter_preuves.py [module…]`.

## Library-learning : macros multi-pas (pas 16, FAIT) — `proto_library_learning.py`

Le pas 14 a tranché : un pas ISOLÉ d'une autre preuve ne transfère pas (verbatim ~0 %, import de
tactique étrangère 0 %). Le levier, c'est le **bloc MULTI-pas récurrent**. Une *macro* = une
sous-séquence contiguë de signatures *(tactique, arité)* qui réapparaît dans plusieurs preuves
(elle porte son propre flot-de-données interne → vrai morceau de vocabulaire partagé). Analyse
**AST pure** (aucun exec-noyau → 4 s sur tout le corpus logique+ensembles) :

- **Corpus** : 97 modules → **458 preuves** (≥2 pas), **4121 pas de tactique**.
- **Macros inter-preuves** (n-gramme dans ≥2 preuves, n=2..4) : **1223**, dont **840 INTER-modules**
  (≥2 modules distincts) = partage réel, pas répétition intra-fichier.
- **Compression** : **82 % des pas** sont absorbés par une macro ; une preuve = *pas-libres +
  appels-macro* → longueur **0.45×** l'originale. Une **petite** bibliothèque suffit déjà :
  top-10 macros couvrent **26 %** des pas, top-25 **39 %**, top-50 **48 %**.
- **Top macros** = motifs Bourbaki reconnaissables : `assume → modus_ponens` (100 preuves / 51 mod),
  `modus_ponens → modus_ponens`, `modus_ponens → loi_deduction`, `conjonction_elim_gauche →
  conjonction_elim_droite` (scinder une conjonction), `loi_deduction → generalisation` (décharger
  puis généraliser), `generalisation → egalite_par_extension`…

**Ce que ça établit** : contrairement au 1-pas (transfert nul, pas 14), le vocabulaire **multi-pas**
est massivement PARTAGÉ (840 macros inter-modules couvrant 82 % des pas). C'est la cible naturelle
du générateur : émettre des MACROS (blocs), pas des primitives isolées — trajectoires courtes,
vocabulaire riche (cf. l'insight niveau-tactique de STATS.md). `python
outils_ia/corpus/proto_library_learning.py [package…]`.

## Valider une macro par le NOYAU (pas 16-suite, FAIT) — `proto_macro_noyau.py`

Test décisif : un bloc multi-pas se RÉGÉNÈRE-t-il depuis une AUTRE preuve, le noyau certifiant ?
Protocole : preuve TEST P contenant une macro → supprimer son bloc de L pas ; preuve DONNEUSE Q≠P
contenant la même macro → transplanter SON bloc concret dans le trou de P, re-bindé (m sorties → m
variables manquantes via data-flow, internes → noms frais, entrées → variables locales par binding),
noyau validant le P reconstruit.

**Résultat : 1 / 103 blocs régénérés (≈ 0 %)** — copier le bloc concret d'une autre preuve + renommer
les variables Python ne reproduit **quasi jamais** la cible. **Et la cause est prouvée** (en
inspectant deux instances de la macro `c45_avant/4 → egal/2`) :

| | bloc concret |
|---|---|
| `pr1_caracterisation` | `fwd = c45_avant(R, 'x', 'u', 'v')` ; `eq = egal(var('x'), pr1z)` |
| `pr2_caracterisation` | `fwd = c45_avant(R, 'y', 'u', 'v')` ; `eq = egal(var('y'), pr2z)` |

Les instances diffèrent au **niveau TERME** : des **littéraux** (`'x'` vs `'y'` = noms de variables
liées encodés en chaînes) et des **objets propres à la preuve** (`pr1z` vs `pr2z`) — que le renommage
de variables Python ne substitue PAS. Le bloc copié calcule donc le résultat de l'autre preuve → rejeté.

**Conclusion (capitale pour le design).** Le 1-pas (pas 14) ET le bloc multi-pas (pas 16-suite)
échouent au transfert par copie+renommage, **pour la même raison** : une macro est un **TEMPLATE
PARAMÉTRÉ sur ses arguments-termes**, pas un fragment copiable. Le vocabulaire partagé (1223 macros,
pas 16) est un **squelette structurel abstrait** ; l'employer exige de **SYNTHÉTISER les
arguments-termes** (le noyau validant), ce que la **récupération/copie ne peut pas faire** → ça
**confirme le besoin d'un générateur APPRIS** (et explique pourquoi). `python
outils_ia/corpus/proto_macro_noyau.py [module…]`.

## Substituer les arguments-termes (pas 17, FAIT) — `proto_macro_termes.py`

Test DIRECT de l'hypothèse « macro = template paramétré » : on étend le transplant de bloc pour
substituer AUSSI les **littéraux-chaînes** du bloc donneur (les `'x'`/`'y'` nommant les variables
liées) vers les chaînes locales de P, pas seulement les variables Python. Mesure côte-à-côte sur les
mêmes 103 blocs (donneuse ≠ P), noyau validant :

| | variables seules (pas 16-suite) | **+ substitution des termes** |
|---|---|---|
| `projection` (pr1/pr2 symétriques) | 0 % | **15 %** |
| `identite` | 0 % | 0 % |
| `diagonale` (5 preuves) | 1 % | 1 % |
| **TOTAL** | **0 % (1/103)** | **5 % (6/103)** |

**Le lift est réel mais localisé** : la substitution atomique rescape les cas SYMÉTRIQUES (projection
`'x'↔'y'`) mais pas le reste. Cause (deux macros inspectées) : les arguments d'une macro sont des
**SOUS-TERMES STRUCTURÉS** (arbres d'expression), pas des atomes —
- identite : `…E.composee(vG, E.diagonale(vA))…` vs `…E.composee(E.diagonale(vB), vG)…` (la forme du
  sous-terme change : ordre composée/diagonale) ;
- diagonale : `egal(cple, E.couple(vu, vu))` vs `egal(var('u'), vz)` (sous-termes entièrement
  différents ; `vu` variable vs `var('u')` appel).

**Conclusion (la plus précise jusqu'ici).** Une macro est un template paramétré par des **termes
STRUCTURÉS** ; l'instancier = **synthétiser des arbres d'expression** (le noyau validant), ce que ni
le renommage de variables ni la substitution d'atomes ne peuvent faire (plafond 5–15 %). Cela ne
**confirme** pas seulement le besoin d'un générateur APPRIS : ça en **spécifie le TYPE DE SORTIE** —
des termes structurés. `python outils_ia/corpus/proto_macro_termes.py [module…]`.

## Synthèse de termes (pas 18, FAIT) — `proto_synth_termes.py` : la 1re vraie GÉNÉRATION

Conséquence directe de pas 17 : pour un bloc-macro supprimé, on garde le SQUELETTE (les appels-
tactiques = la macro) mais au lieu de COPIER les termes du donneur, on **SYNTHÉTISE** les slots-
termes depuis le vocabulaire LOCAL de P — atomes (variables locales + `var('<noms liés>')`),
constructeurs (`E.composee/2`, `E.diagonale/1`, `E.couple/2`) appliqués à profondeur ≤2 — et le
NOYAU filtre. C'est la 1re fois qu'on **construit du contenu neuf**, pas qu'on recombine l'existant.

**Démonstration end-to-end** (projection, budget suffisant) : **2/18 blocs synthétisables régénérés
par SYNTHÈSE (11 %)** — au-dessus du plafond 5 % de la copie (pas 17) et du 1 % variables-seules. Le
noyau a accepté un bloc dont le terme a été **fabriqué**, pas copié (vérif directe) :

| | bloc |
|---|---|
| donneur (pr2) | `eq = egal(var('y'), pr2z)` ; `h_eq = N.assume(eq)` |
| **SYNTHÉTISÉ** (accepté noyau, pr1) | `eq = egal(var('x'), pr1z)` ; `h_eq = N.assume(eq)` |

→ le synthétiseur a **construit** `egal(var('x'), pr1z)` à partir du vocabulaire de P (le nom lié
`'x'`, la variable `pr1z`), il n'a PAS recopié le `var('y'), pr2z` du donneur.

**Le mur, mesuré.** Les slots PROFONDS (ex. identite `E.composee(vG, E.diagonale(vA))`, depth-2)
ne sont pas atteints par l'énumération brute : le terme-oracle EST générable mais il **arrive au rang
561 sur 7265 candidats** — l'énumération est exponentielle. Avec un budget tractable → ~0 % ; il faut
**ranger** les candidats. C'est la motivation MESURÉE du prior appris (exactement comme la repair-
policy rangeait les tactiques : rang 1.00 vs 8.82). `python outils_ia/corpus/proto_synth_termes.py
[module…]` (défaut = projection ; modules profonds = gros budget + pas 19).

## Prior appris sur la synthèse (pas 19, FAIT) — `proto_synth_prior.py` : ranger les termes

Le pas 18 a mesuré le mur (terme-oracle au rang ~561). Ici on APPREND à ranger les candidats. Pour
chaque slot-terme, on génère le pool (synth_termes) et on entraîne un classifieur à prédire « ce
candidat est-il le terme attendu ? » depuis des features de CONTEXTE (tactique appelante + position
d'argument ; profondeur/forme/taille du terme ; data-flow : leaves ∈ variables manquantes/disponibles
/sorties du bloc). **Astuce clé : l'oracle de label est GRATUIT** (égalité au terme réel de P au même
slot) → AUCUN appel-noyau pour l'entraînement. **GroupKFold par PREUVE** (test sur preuves jamais vues).

Mesure (projection + identite + diagonale, **47 slots in-grammaire**, 117 500 candidat-features) :

| | rang du bon terme | appels-noyau |
|---|---|---|
| énumération brute | **396** (médiane 41) | référence |
| **prior LogReg** | **140** | **−65 %** |
| prior RandomForest | 271 | −32 % |

Le prior **coupe 65 % des appels-noyau** à la synthèse en apprenant à préférer les termes **petits et
data-flow-pertinents** (`nnodes` 0.26, `natoms` 0.13, `df_disp` 0.09 = features-clés). **Honnêteté** :
le ranking de termes STRUCTURÉS est plus dur que celui des tactiques (pas 8, rang 1.00) — features
shallow plafonnent à ~rang 140, pas ~1 ; résoudre l'**arrangement exact** des variables (ex.
`composee(vG,diag(vA))` vs `composee(vA,diag(vG))`, mêmes compteurs) demande des modèles STRUCTURÉS
(embeddings d'AST, torch). `python outils_ia/corpus/proto_synth_prior.py [module…]`.

## Synthèse guidée end-to-end (pas 20, FAIT) — `proto_synth_guide.py`

On BRANCHE le prior (pas 19) dans la synthèse : on range le pool de candidats par P(correct) AVANT
le filtre noyau, à BUDGET FIXE (CAP=200 essais-noyau/bloc), et on mesure la régénération de bloc —
BRUTE vs PRIOR — sur identite (depth-2) TENU À L'ÉCART (prior entraîné sur projection+diagonale).

**Résultat NÉGATIF à DOUBLE CAUSE, mesuré :**
- **couverture grammaire** : seulement **6/10 slots** sont dans la grammaire de termes ; les 4 autres
  exigent des constructeurs non couverts (`conjonction_intro`, lemmes-helpers) → insynthétisables ;
- **plafond de ranking** : pour les slots in-grammaire, le bon terme est au rang brut **798**, et le
  prior shallow le remonte seulement à **557** (−30 %) — toujours ≫ CAP=200 ;
- **régénération end-to-end** (2 blocs FULLY in-grammaire) : **BRUTE 0 % → PRIOR 0 %**.

Le prior AIDE (rang −30 %) mais ne FRANCHIT pas le budget pour le depth-2 ; et la grammaire est trop
étroite. Conclusion : les deux verrous restants sont (1) une **grammaire de termes plus large** et
(2) un **modèle de ranking STRUCTURÉ** (les features shallow ne pincent pas l'arrangement exact).
`python outils_ia/corpus/proto_synth_guide.py`.

## Modèle STRUCTURÉ torch (pas 21, FAIT) — `proto_synth_torch.py` : le ranking neuronal

Le shallow (pas 19-20) plafonne car il agrège (il ne voit pas l'ARRANGEMENT : quelle variable à
quelle position). Ici un petit **TreeNN** encode l'AST RÉCURSIVEMENT : chaque feuille porte ses
features data-flow (∈ manquantes/disponibles/sorties), chaque constructeur (`composee/diagonale/
couple/var`) COMPOSE ses enfants avec des poids propres → l'embedding connaît la STRUCTURE. Un MLP
score (terme ⊕ contexte-slot). Entraînement **ranking listwise** par slot (softmax, cible = terme
réel de P = oracle GRATUIT), **GroupKFold par PREUVE**. Petit modèle CPU, ~80 s.

Rang du bon terme (47 slots in-grammaire tenus à l'écart, ~1500 candidats/slot) :

| ranker | **médiane** | top-5 | moyenne |
|---|---|---|---|
| brut (énumération) | 41 | 0 % | 396 |
| shallow (LogReg, pas 19) | 20 | 38 % | 123 |
| **neuronal (TreeNN, pas 21)** | **1** | **60 %** | 433 (instable) |

**Le TreeNN met le bon terme en TÊTE pour la moitié des slots** (médiane 1) et dans le **top-5 pour
60 %** — là où le shallow plafonnait (38 %) et le brut échouait (0 %). L'**encodage de la structure
capture l'arrangement** des variables que les features superficielles ne voyaient pas. Implication
end-to-end : à **budget 5 essais-noyau**, on régénérerait **60 %** des slots depth-2 (vs ~0 % brut,
cf. pas 20). `python outils_ia/corpus/proto_synth_torch.py [module…]`.

**Stabilisation tentée (pas 22)** : on a ajouté **dropout + L2 + ENSEMBLE de graines** et tenté
d'**élargir les modules** — la médiane (1) et le top-5 (~60 %) restent robustes, mais la **MOYENNE ne
baisse pas** (~360-430). Diagnostic : (1) les outliers sont **SYSTÉMATIQUES** (une preuve tenue à
l'écart dont la structure des termes n'apparaît dans aucune preuve d'entraînement → tous ses slots
ratés), PAS du bruit de graine que l'ensemble pourrait moyenner ; (2) élargir à
correspondances/image/reciproque **n'ajoute AUCUN slot in-grammaire** (leurs termes utilisent
d'autres constructeurs). **Le goulot de DONNÉES est le goulot de GRAMMAIRE** : seuls 3 modules
produisent des termes `composee/diagonale/couple/var`. → le vrai levier est d'**enrichir la grammaire**.

## Grammaire enrichie : littéraux de noms (pas 23, FAIT) — la couverture double

Diagnostic pas 22 = le goulot est la grammaire. **Inspection des 243 slots** des 3 modules : seuls
**47 (19 %) in-grammaire** ; le plus gros manque = **49 slots `const` profondeur 0** = des LITTÉRAUX
nus de noms de variables liées (`'y'`, `'w'`…) que les primitives `s5/s6/symetrie/existe_temoin`
prennent en argument. La grammaire générait `var('y')` mais **jamais le `'y'` nu**.

Correctif (1 ligne) : émettre les `str_atoms` aussi en **`ast.Constant` nus** (pas seulement dans
`var(·)`). Coût pool ≈ nul (quelques feuilles) ; zéro changement au TreeNN (`_leaf_vec` gère déjà
`Constant`). Résultat — couverture **19 % → 39 %** (47 → **96/243** slots) ; le corpus de ranking
**DOUBLE** (47 → 97 slots). Re-run `proto_synth_torch` sur le corpus élargi :

| ranker | médiane | top-5 | moyenne |
|---|---|---|---|
| brut | 24 | 0 % | 214 |
| shallow (LogReg) | 1 | 70 % | **27** |
| **neuronal (TreeNN)** | **1** | **80 %** | 185 |

**Le top-5 du TreeNN monte 60 % → 80 %**, médiane 1 tenue : plus de données = meilleure couverture,
**hypothèse pas 22 CONFIRMÉE**. MAIS finding nouveau : sur ce corpus la **moyenne du shallow (27) bat
celle du TreeNN (185)**. Cause MESURÉE : `_leaf_vec` encode tout `Constant` à l'identique
(`[0,1,0,0,0,1]`) → le TreeNN ne distingue PAS `'y'` de `'x'`, il les ÉGALISE, et le bon littéral peut
tomber loin dans l'égalité ; le shallow gagne via ses features explicites. C'est le levier de pas 24.

## Grammaire enrichie : formules et/2 (pas 24, FAIT) — couverture 47 %

**Probe d'abord (économise un tick)** : pour les 49 slots-littéraux, la chaîne (`'x'`,`'y'`…) n'est
**JAMAIS** dans le data-flow (0/49) et ne concourt qu'à ~3 candidats → le bon littéral est
**UNDERDETERMINÉ** par les features de feuille (shallow comme TreeNN ne peuvent qu'appliquer un prior
position/cf). Donc on **n'ajoute PAS** de feature data-flow sur `Constant` (idée RÉFUTÉE par la mesure) ;
on vise la famille suivante **structurellement déterminée** : `et/2` (20 slots, `et(P, Gxz)` où P, Gxz
sont de vraies variables-formule présentes dans le data-flow).

Grammaire : **couche FORMULES `et/2` sur atomes-Name**, construite à PART avec un **QUOTA réservé**
(≤ 20 % du budget), **non réinjectée** dans la couche objets (sinon `composee(et(…))` explose). TreeNN :
poids de constructeur `et` dédié. Couverture **39 % → 47 %** (96 → **116/243** slots ; les 20 et-slots
entrent). Re-run `proto_synth_torch` (113 slots rangés) :

| ranker | médiane | top-5 | moyenne |
|---|---|---|---|
| brut | 26 | 0 % | 359 |
| shallow (LogReg) | 7 | 44 % | 121 |
| **neuronal (TreeNN)** | **1** | **67 %** | 151 |

Bilan : la **moyenne du TreeNN baisse** (185 → 151, objectif pas 22 atteint) et la **médiane 1** tient ;
le top-5 passe 80 % → 67 % car les et-slots sont une famille **PLUS DURE** (choisir la bonne paire
`(P,Gxz)` parmi ~150 et-termes, vs 3 littéraux) — mais le TreeNN y reste le **meilleur** (médiane 1,
top-5 67 % vs shallow 44 % vs brut 0 %). Les outliers restants (mean 151 ≳ shallow 121) = mêmes échecs
SYSTÉMATIQUES de généralisation (**9 preuves seulement**) → le prochain levier est plus de DONNÉES.

## Plus de données via plus de constructeurs (pas 25, FAIT) — la moyenne s'effondre

Objectif : plus de DONNÉES (goulot résiduel = 9 preuves). Re-test de l'élargissement de modules de
pas 22 AVEC la grammaire enrichie : sur **16 modules candidats, toujours 0 slot in-grammaire ajouté**
(la plupart n'ont aucune macro intra-module ; ceux qui en ont — ex. `produit_extensionnalite`, 30 slots
— utilisent ENCORE d'autres constructeurs). Le levier « plus de modules » est donc **RÉFUTÉ une 2e
fois**. MAIS la probe des têtes hors-grammaire de ces modules révèle le vrai manque : **`conjonction_
elim_gauche/1` ×19** (proof-term unaire sur une hypothèse-Name) et **`inclus/2`**.

Ajout (couche proof/relation, bornée à quota ≤⅓) : `conjonction_elim_gauche/droite/1`, `inclus/2` +
poids TreeNN dédiés. Effet : (a) couverture des 3 modules **47 % → 51 %** (126 slots) ; (b) le module
`produit_extensionnalite` passe de **0 → 19 slots in-grammaire** = **+3 preuves DÉBLOQUÉES** (9 → 12),
ce que pas 22 croyait impossible — *enrichir la grammaire débloque AUSSI de nouvelles preuves*. Re-run
`proto_synth_torch` (140 slots, 12 preuves) :

| ranker | médiane | top-5 | moyenne |
|---|---|---|---|
| brut | 42 | 0 % | 471 |
| shallow (LogReg) | 14 | 46 % | 117 |
| **neuronal (TreeNN)** | **5** | 55 % | **61** |

**La MOYENNE du TreeNN s'effondre 151 → 61** (objectif des outliers systématiques de pas 22 ENFIN
atteint) : plus de preuves diverses + la nouvelle famille range modérément bien. Compromis : médiane
1 → 5, top-5 67 → 55 %, car la famille débloquée (choisir LA bonne hypothèse parmi ~|atomes|) est
intrinsèquement PLUS DURE que les termes-objets depth-2 (où le TreeNN touchait médiane 1) — benchmark
plus HONNÊTE, pas une régression du modèle. Pour la régénération END-TO-END (le but), la moyenne basse
(61 ≪ 117 shallow ≪ 471 brut) borne le **pire-cas de budget** : c'est le gain qui compte.

## Grammaire enrichie : proof-terms plats (pas 26, FAIT) — couverture 64 %, médiane 1 restaurée

Probe des têtes encore hors-grammaire (après pas 25) → 4 cibles PLATES, args déjà en base :
`equivalence_avant/1` (×9), `E.est_un_couple/1` (×5), `N.existe_temoin/2` (Name, littéral ; ×6),
`symetrie/2` (var-litt. ∪ Name ; ×10). [Le RESTE — `conjonction_intro` IMBRIQUÉ,
`equivalence_transitivite(_inst_dom…)`, `et_congruence(couple_diagonale…)`,
`equivalence_arriere(modus_ponens…)` — est DEEP/récursif ou helper module-spécifique → exige une
grammaire de preuve RÉCURSIVE, hors de cette couche plate ; documenté comme reste.]

Ajout (4 constructeurs + poids TreeNN dédiés `un1/exte/sym`). **Fix de budget** : les formules reçoivent
un budget **ADDITIF** (`pool[:MAXT]` objets + `forms[:MAXT]`), sinon le quota fractionnaire tronquait des
`couple/2` profonds (couvert 13→9) puis les `et/inclus` tardifs. Couverture **51 % → 64 %** (126 → 156
slots sur les 3 modules de référence ; couple restauré à 13). Re-run `proto_synth_torch` (178 slots de
ranking, 12 preuves, pool ~2500) :

| ranker | médiane | top-5 | moyenne |
|---|---|---|---|
| brut | 1004 | 0 % | 930 |
| shallow (LogReg) | 21 | 46 % | 98 |
| **neuronal (TreeNN)** | **1** | **69 %** | 87 |

Gain net sur pas 25 : **médiane 5 → 1** (restaurée) et **top-5 55 → 69 %** — les nouvelles familles
(`symetrie(var,Name)`, `existe_temoin(Name,litt.)`) ont une structure DISTINCTIVE que le TreeNN classe
en tête. La moyenne remonte un peu (61 → 87) car le pool a grossi (le brut EXPLOSE à 930), mais le
TreeNN (87) bat désormais le shallow (98) AUSSI sur la moyenne, et reste ≪ brut. Le brut s'effondre
(médiane 1004) : sans modèle la synthèse est intractable — tout l'intérêt du ranker structuré.

## Ce qui reste = passer à l'END-TO-END (torch/sklearn dispo)
- pas 27 (LE but) : **rebrancher `proto_synth_guide`** (synthèse end-to-end, kernel validant) avec le
  TreeNN comme ranker au lieu du LogReg + grammaire enrichie → régénération end-to-end depth-2 à BUDGET
  FIXE. Avec médiane 1 / top-5 69 % / moyenne 87, viser un taux **> 0 %** mesurable = le vrai
  generate-and-verify ;
- grammaire de preuve RÉCURSIVE (les proof-terms deep restants : conjonction_intro imbriqué, chaînes
  equivalence/modus_ponens) si l'end-to-end le réclame ;
- mise à l'échelle BEAM (K plus grand) ; niveau TACTIQUE ; GFlowNet/diffusion.
