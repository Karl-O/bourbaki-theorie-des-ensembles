# STATS — Pivot méta-algo « generate-and-verify » (récapitulatif autoritaire, pas 1→33)

Document capstone du pivot mené dans `outils_ia/corpus/`. Pour le détail pas-à-pas, voir `README.md`.
**Frontière de confiance intacte** : aucun `Theoreme` forgé ; le noyau LCF reste seul juge ;
`theorie_ensembles()` vaut toujours **22 axiomes** ; outillage SEULEMENT dans `outils_ia/`.

## 1. Le but

Construire l'amorce d'une **IA qui CRÉE des théories pour résoudre des problèmes** (cf. but final),
sur le principe **generate-and-verify** : l'IA propose, le **noyau LCF certifie**. Vision de l'utilisateur :
s'inspirer de la diffusion (DDPM/DDIM) mais comme **marche aléatoire DISCRÈTE** sur le DAG des
dérivations — forward = corrompre une preuve, reverse = la reconstruire, **noyau = vérificateur exact
gratuit à chaque pas** (la marche inverse est SAINE par construction : au pire inutile, jamais fausse).

## 2. Calibration du corpus (pas 4) — pourquoi le niveau TACTIQUE

Mesures (`stats_corpus.py`, 22 théorèmes tracés Ch II + export 282 théorèmes / 97 modules) :

| mesure | valeur | implication |
|---|---|---|
| trajectoires primitives (`N.*`) | médiane **5 402**, max **30 207** pas | preuves primitives ÉNORMES → mauvais espace de marche |
| espace d'actions primitif | **14 règles**, 92 % sur 4 (`modus_ponens` 41 %, `assume`/`loi_deduction` 18 %, `s3` 15 %) | choix de règle TRIVIAL au niveau primitif |
| bibliothèque tactique | dizaines de tactiques (`conjonction_intro` 20/22, `equivalence_avant` 13…) | vocabulaire RICHE = la bonne granularité |

→ **Décision de design (confirmée par les données)** : générer au niveau **TACTIQUE** (paire
`but → programme-preuve`), pas au niveau primitif ; la trace primitive sert de **vérification dense** +
oracle. C'est ce qui a guidé tout le pivot.

## 3. L'arc pas 14→33 — chiffres-clés à chaque jalon

| pas | jalon | résultat |
|---|---|---|
| 14-15 | repaireur appris + BEAM (reconstruire K pas supprimés) | data-flow décisif ; BEAM B=4 reconstruit 100 % jusqu'à K=4 |
| 16 | library-learning (macros multi-pas inter-preuves) | 1223 macros, 82 % des pas absorbés |
| 16-suite | copier un bloc-macro + re-bind variables | **1/103 (~0 %)** — les macros diffèrent au niveau TERME |
| 17-18 | **SYNTHÈSE des slots-termes** (générer, pas copier) | **11 %** (projection) > plafond 5 % de la copie = 1ʳᵉ vraie génération |
| 19-20 | prior shallow (sklearn) range les candidats | rang 396→140 mais PLAFONNE sur depth-2 (~557) |
| 21 | **TreeNN** (encode l'AST récursivement) range les termes | **rang MÉDIANE 1, top-5 60 %** (vs shallow 20/38 %, brut 41/0 %) |
| 22 | diagnostic stabilité | outliers SYSTÉMATIQUES, pas bruit ; goulot = GRAMMAIRE |
| 23-26 | **enrichir la grammaire** (littéraux, et, inclus, conjonction_elim, symetrie, existe_temoin…) | couverture **19 %→64 %** ; TreeNN médiane 1 / top-5 ~70 % |
| 27 | **END-TO-END** kernel-validé (holdout module identite) | BRUT 0 % → **TreeNN 50 %** (rang oracle 1034→178) |
| 33 | **consolidation** leave-one-module-out (corpus entier) | **27 % sur 43 blocs (vs 4 % brut, ~7×)** — headline ROBUSTE |

**Acquis principal** : le generate-and-verify appris **FONCTIONNE** — synthèse de termes structurés +
ranker TreeNN + noyau validant **régénère réellement 27 % de blocs depth-2 tenus à l'écart** (≈7× le brut),
chaque sortie certifiée par le noyau. 1ʳᵉ démonstration concrète et robuste de « l'IA crée, le noyau certifie ».

### Détail end-to-end leave-one-module-out (pas 33, CAP=200)

| module (holdout) | blocs | BRUT | TreeNN |
|---|---|---|---|
| projection_fonctionnelle | 20 | 10 % | **30 %** |
| identite_neutre | 2 | 0 % | 50 % |
| diagonale_couple | 8 | 0 % | 25 % |
| produit_extensionnalite | 11 | 0 % | 27 % |
| image_reciproque_props | 2 | 0 % | 0 % |
| fonctions_props2 | 0 | (0 bloc ≤2 slots) | — |
| **TOTAL** | **43** | **4 %** | **27 %** |

**Sensibilité au budget (pas 36, `proto_synth_capcurve.py`, leave-one-module-out, 43 blocs)** : le BRUT
reste PLAT à **4 %** (oracles depth-2 au rang ~1000+, inatteignables) ; le TreeNN MONTE avec le budget —
CAP 50/100/200/300/400 → **13 / 25 / 32 / 39 / 41 %**. Le ranker structuré rend le budget-noyau UTILE
(le noyau = vérificateur gratuit) : **41 % à CAP=400 SANS plus de données**. (Variance ±5 % E=1 vs E=2.)

## 4. La limite : l'EFFET MIROIR — un verrou de DONNÉES (diagnostiqué sur 5 angles)

Les 2 preuves d'identite sont des **miroirs** : `composee(vG, diagonale(vA))` vs `composee(diagonale(vB), vG)`
(même structure, arrangement OPPOSÉ). Sous holdout PROOF (tenir une sœur DANS le train), le ranking échoue.

| pas | angle d'attaque | résultat |
|---|---|---|
| 28 | holdout proof-level | la sœur miroir au train est **ADVERSARIALE** → 0 % (pire que holdout module) |
| 29 | scan 21 modules pour des arrangements non-miroir | **AUCUN** : la donnée n'existe pas dans le corpus |
| 30 | contexte du but (termes hors-bloc) | hors-bloc les miroirs sont **identiques** (`_tc`×2) → aucun signal AST |
| 31 | grammaire récursive (`conjonction_intro`) | oracles Name×Name budget-fragiles + ranking dur → ROI faible |
| 32 | encoder la **cible** kernel (le signal PARFAIT) | distincte & encodable, MAIS inexploitable à **n=2** ; dégrade même la réf 50 %→0 % |

→ **VERROU = DONNÉES** (diversité d'arrangements), ni outillage, ni modèle, ni signal. Conclusion robuste :
même le signal parfait (la cible) est inutile sans **plusieurs** exemples d'arrangement à apprendre.

## 5. Fichiers (qui fait quoi) — `outils_ia/corpus/`

| fichier | rôle |
|---|---|
| `export_corpus*.py`, `trace_preuve.py` | substrat : export du corpus + trace (observe le noyau) |
| `gen_paires_corruption.py`, `proto_mutation_verify.py` | forward (corruption) + `_statut` (verify noyau) |
| `repair_learned.py` | repaireur appris (sklearn ; data-flow `fournit_manquante`) |
| `proto_inter_preuves.py`, `proto_library_learning.py`, `proto_macro_*.py` | bibliothèque inter-preuves, macros, slots |
| `proto_synth_termes.py` | **grammaire de synthèse** : couche objets (composee/diagonale/couple/var) + couche formes/preuve (et/inclus/conjonction_elim/symetrie/existe_temoin/equivalence_avant/est_un_couple) |
| `proto_synth_prior.py` | prior shallow (LogReg) de référence |
| `proto_synth_torch.py` | **TreeNN** (`TreeEnc`/`Scorer`/`collecte_slots`/`_entraine`) ; corpus 6 modules ; ranking GroupKFold |
| `proto_synth_e2e.py` | **end-to-end** kernel-validé (`HOLDOUT="module"`/`"proof"`) |
| `proto_synth_lomo.py` | **leave-one-module-out** (headline corpus-wide pas 33) |
| `README.md` | arc détaillé pas 1→33 ; `STATS.md` (ce fichier) = capstone |

## 6. Reproductibilité

Depuis `V9/`, `PYTHONIOENCODING=utf-8` (python global 3.13 ; `.venv` cassé) :
```
python outils_ia/corpus/proto_synth_torch.py     # ranking TreeNN (médiane/top-5/moyenne), ~13 min
python outils_ia/corpus/proto_synth_e2e.py       # end-to-end holdout module (50 % identite), ~3 min
python outils_ia/corpus/proto_synth_lomo.py      # leave-one-module-out (27 % / 43 blocs), ~12 min
```
Corpus de données gitignorés (régénérables) ; les outils `.py` sont versionnés. Runs kernel BORNÉS
(CAP) ; `couple_diagonale` (6707 pas) écarté via `TEST_LOURD`.

**Cohérence vérifiée (pas 35)** après les reverts pas 30-32 : `proto_synth_termes` redonne **11 %**
(2/18, exact) ; `proto_synth_prior` LogReg **557 vs brut 1241** (−55 % appels-noyau ; chiffres reflétant
la grammaire enrichie — 156 slots — vs les figures historiques pas 19 à grammaire étroite) ;
`proto_synth_lomo` redonne **27 % / 43 blocs** (pas 33) ; tous les protos importent ; `theorie==22`.
Aucune régression.

## 7. Directions (au-delà de la boucle outils_ia)

1. **Formaliser plus de preuves d'arrangement** dans `bourbaki/` (≥3-4 par schéma `composee/diagonale`) =
   la cure DIRECTE du verrou de données → le ranker apprend l'appariement candidat↔but (la cible, déjà
   codée en pas 32 et dans l'historique git, redevient alors le bon levier).
2. **Niveau TACTIQUE** : régénérer des pas-tactiques entiers (pas seulement des termes), cf. §2.
3. **GFlowNet / diffusion sur le DAG** de dérivations (la vision DDPM→marche discrète + noyau-récompense).
