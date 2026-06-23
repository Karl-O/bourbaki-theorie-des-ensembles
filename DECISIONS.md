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
