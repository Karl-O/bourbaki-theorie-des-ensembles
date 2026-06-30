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

## Politique SÉQUENTIELLE (pas 12, FAIT) — `proto_sequential.py` : la marche guidée multi-pas

On supprime K pas et on RECONSTRUIT en chaînant la repair-policy apprise (top-1 par trou)
+ filtre noyau final = generate(politique)+verify(noyau), testé sur preuves TENUES À L'ÉCART :
remplissage **INDÉPENDANT** (top-1 par trou) vs **ITÉRATIF** (greedy + recompute : remplir le
trou de plus haute confiance d'abord, RECALCULER, recommencer) — sur preuves tenues à l'écart :

| K (pas supprimés) | indépendant | **itératif (pas 13)** |
|---|---|---|
| 1 | 100 % | 100 % |
| 2 | 41 % | **79 %** |
| 3 | 4 %  | **20 %** |

L'itératif **double K=2 et ×5 K=3** : recalculer après chaque remplissage réduit l'ambiguïté
d'assignation multi-trous. C'est la marche guidée multi-pas, le noyau ne jugeant qu'à la fin
(generate(politique) + verify(noyau)).

## Ce qui reste = enrichir le générateur appris (torch/sklearn dispo)
- BEAM search (au lieu de greedy top-1) + features plus riches pour relever K=3 ;
- bibliothèque INTER-preuves (générer un pas hors des statements de la preuve courante) ;
- niveau TACTIQUE (STATS.md) ; library-learning ; GFlowNet/diffusion ; mise à l'échelle données.
