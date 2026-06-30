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

## Passes ultérieures
- générer un VRAI dataset de paires (corrompu→valide) multi-pas (corruption progressive) ;
- amorcer le *reverse* : un repaireur (même trivial : essayer les tactiques de la bibliothèque
  à l'emplacement corrompu, garder celle que le noyau accepte) = 1ᵉ « débruitage » ;
- arbre `@livre` complet (chapitre→§→page) = structure conditionnelle (le « prompt » = le but).
