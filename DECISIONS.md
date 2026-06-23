# Journal des décisions (mode boucle autonome)

Décisions prises sans solliciter l'utilisateur (cf. CLAUDE.md). Une ligne par décision, datée.

## 2026-06-23 — Mise en place

- **Règle ≤10 = 10 entrées AU TOTAL** par dossier (fichiers + sous-dossiers confondus, `__init__.py`
  compris). Choix de l'utilisateur, le plus strict/lisible.
- **On garde les noms de paquets de 1er niveau** (`bourbaki/cardinaux`, `bourbaki/ordre`…) et on imbrique
  À L'INTÉRIEUR par section du livre → limite la réécriture d'imports (vs. passer à `chapN/…`).
- **Ordre de migration : feuilles d'abord.** `structures/` est le canari (paquet feuille : aucun module
  hors de `structures/` ne l'importe). Puis `ensembles/*`, `ordre`, `entiers`, et `cardinaux` en dernier
  (le plus gros, 140 fichiers, tests lourds ~16 min).
- **Fix Hessenberg** : `ensembles_hessenberg_vrai.py` importait `_u_inclus_reunion` sans l'importer →
  `NameError`. Corrigé (ajout à l'import depuis `ensembles_frame_extension_finale`). 6/6 tests verts.
- **1 dossier à 11 dans le plan** (`cardinaux/iii_6_infinis/hessenberg/assemblage_vrai`, `__init__.py`
  oublié dans le compte de l'agent) → à scinder lors de la migration de `cardinaux`.
- **Outillage** : `outils_ia/reorg_moves.json` (carte durable des déplacements) +
  `outils_ia/migration_arbre.py` (migration par paquet : `git mv` + `__init__.py` + réécriture d'imports
  `\bold.dotted\b → new.dotted`, mode `--dry-run`).

## 2026-06-23 — Migration (en cours)

- **Outil finalisé** : motif A (chemin pointé contigu `a.b.c`, couvre aussi `from a.b.c import (noms)`)
  + motif B (`from PARENT import NOM [as ALIAS]`, la **forme dominante** — 659× `ensembles_abrege`,
  416× `noyau_abrege`). Vérifié : pas d'imports relatifs, pas de multi-sous-modules sur une ligne dans le
  dépôt → ces deux motifs suffisent. Le canari a révélé l'oubli du motif B *avant* tout dégât (dry-run +
  revert propre).
- **Canari `structures/` (bourbaki/) MIGRÉ ✅** : 14 fichiers → `iv_1_structures_isomorphismes/` +
  `iv_2_morphismes_structures_derivees/` (≤10), 26 fichiers d'imports réécrits, collecte + **167 tests
  verts (1.8 s)**.
- **tests/ mirroring — À FAIRE** : `reorg_moves.json` ne couvre que `bourbaki/`. Chaque `tests/<paquet>`
  sera réorganisé en miroir (chaque `test_*.py` dans le sous-dossier de son module). `tests/structures`
  reste à plat (≤10 non encore satisfait côté tests) tant que non mirroré — prochain sous-pas.
- **Stratégie de vérification adoptée** : la migration ne fait que déplacer des fichiers + réécrire des
  chemins d'import (code des preuves byte-identique). Empiriquement confirmé : `ordre` 372 tests verts,
  `structures` 167 verts APRÈS déplacement. Donc **gate par paquet = `pytest --co` (collecte, ~8–30 s)**
  qui attrape toute casse d'import ; **vérif runtime aux jalons** (run des tests des paquets concernés) ;
  **suite complète** avant `cardinaux` et en fin d'ÉTAPE A. Baseline d'erreurs tolérée = 1
  (`familles_algebre`, cf. ANOMALIES).

## 2026-06-23 — Migration : 6/9 paquets faits

Migrés + commités (gate collecte vert, 1 erreur connue tolérée) :
`structures` (IV), `ordre` (III.1/2), `entiers` (III.4/5/6), `ensembles/fonctions` (II.3),
`ensembles/familles` (II.4/5), `ensembles` base/relations (II.1/2/3/6).
**Restent** : `logique` (le plus transverse — 400+ imports `noyau_abrege`/`ensembles_abrege`),
`cardinaux/arithmetique`, `cardinaux` (140 fichiers + fix du dossier `hessenberg/assemblage_vrai` à 11,
+ tests lourds ~16 min). À traiter avec un run de suite complète.

## 2026-06-23 — `logique` migré (7/9) + outil rendu ROBUSTE (mésaventure)

- **Bug 1** : l'outil pré-créait les `__init__.py` AVANT les `git mv` → collision quand un `git mv`
  déplaçait un `__init__.py` existant → exit 128 **migration partielle = dépôt cassé**. Pire, des `git mv`
  restés *staged* ont été aspirés par un commit d'outil ultérieur (HEAD contaminé). Récupéré par
  `git reset --hard HEAD~1` sur le commit « journal » (logique à plat).
- **Bug 2** : `_all_py()` ne scannait que `bourbaki/`+`tests/` → les imports de **`outils_ia/*.py`** et des
  scripts racine n'étaient PAS réécrits → 6 erreurs de collecte. Corrigé : scan de TOUT V9 (hors
  `__pycache__/.git/.venv/.pytest_cache`).
- **Exigence utilisateur** « empêche ça » → outil rendu **TRANSACTIONNEL** : préflight (arbre git propre +
  sources présentes + destinations libres) puis apply protégé avec **ROLLBACK auto** (`git reset --hard`
  + `git clean`) à la moindre exception. Plus jamais d'état partiel. Commits d'outil protégés par un garde
  anti-contamination (vérifier que seul l'outil est *staged*). Cf. [[outils-transactionnels]].
- **`logique` migré** : I.1/I.2/I.3/I.4, 754 imports réécrits (outils_ia inclus), collecte **3005/1**.
  Dossiers source vides (`logique/criteres`, `logique/tactiques`) nettoyés (`find -type d -empty -delete`).
- **TODO outil** : ajouter le nettoyage auto des dossiers source vides en fin de migration.
- **Restent** : `cardinaux/arithmetique`, puis `cardinaux` (fix `hessenberg/assemblage_vrai` 11→≤10 dans
  `reorg_moves.json` AVANT apply), avec run de suite complète (avec `--timeout`, cf. test lent pré-existant
  dans entiers/ensembles — cible ÉTAPE D).
