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

## Limite V1 et étape suivante (la vraie « marche sur le DAG »)

`Theoreme` ne stocke que `(hypotheses, conclusion, justification)` — **pas ses
prémisses**. Donc le DAG d'inférence fin n'est pas dans l'objet ; cette V1 capture la
preuve au niveau **programme** (source). C'est déjà une paire (but → programme) utilisable
(cadre code-génération / GFlowNet sur tactiques).

**Étape suivante** : instrumenter les primitives `N.*` (wrapper de journalisation) pour
enregistrer, à chaque construction, le tuple `(règle, théorèmes-entrée, théorème-sortie)`.
On obtient alors la **trajectoire pas-à-pas** = la marche sur le DAG de dérivation, donnée
idéale pour une diffusion discrète / GFlowNet (forward = effacer des pas, reverse = les
reconstruire, kernel = filtre de validité à chaque pas). Voir mémoire
`meta-algo-diffusion-marche`.

## Aussi à exporter (passes ultérieures)
- les **traces d'erreurs** (`DECISIONS.md`/`ANOMALIES.md` : tautologies rejetées, verrous-τ,
  captures) = exemples NÉGATIFS / marches mortes étiquetées ;
- l'arbre `@livre` complet (chapitre→§→page) = structure conditionnelle (le « prompt » = le but).
