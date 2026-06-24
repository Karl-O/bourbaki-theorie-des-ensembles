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

## 2026-06-23 — `cardinaux/arithmetique` migré (8/9) — paquet le plus retors

Le move-map d'arithmetique était d'un format différent (chemins relatifs au paquet + **déplacements de
DOSSIERS**, 4 sous-paquets renommés `ensembles_X` → `X`). Trois bugs successifs de l'outil, chacun corrigé
+ revalidé (rollback transactionnel à chaque fois, 0 dégât) :
1. **format** : chemins non V9-root → crash `rsplit('.')`. Fix : normalisation + validation de format
   (erreur claire). + `reorg_moves` : `hessenberg/assemblage_vrai` 11→6+6 (`step_b_prop5`).
2. **renommages de PAQUETS** : `from PKG import nom_reexporté` non suivi (68 erreurs). Fix : champ
   `renommages_paquets` + chemin pointé du paquet ajouté à rmap (motif A). 68→3.
3. **forme parenthésée** `from PKG import (\n module)` : motif B élargi `\(?\s*`. 3→1.
- **Limite connue de l'outil** (corrigée à la main pour 3 tests) : `from PARENT import OLDLEAF as X` quand
  le PAQUET est **renommé** (leaf change) n'est pas auto-réécrit (faudrait `from NEWPARENT import NEWLEAF
  as X`). Marchait par fallback namespace-package des dossiers vides ; exposé par `find -empty -delete`.
  → 3 tests arithmetique corrigés explicitement. **À surveiller pour `cardinaux`** : vérifier ses
  `renommages_paquets` et les imports `from cardinaux import <pkg>`.
- **Nettoyage** : `find -type d -empty -delete` retire les dossiers source vidés — mais expose les imports
  de paquets-namespace fantômes ; le faire AVANT le gate final, pas après le commit.

**RESTE** : `cardinaux` (140 fichiers, dernier). Puis suite complète `--timeout=120`, mirroring `tests/`,
dossiers-trous.

## 2026-06-23 — 🎉 ARBORESCENCE 9/9 PAQUETS MIGRÉE

`cardinaux` migré sans accroc (139 moves, 464 imports réécrits, move-map bien formé, 0 renommage de
paquet, 0 violation) → racine cardinaux/ = 8 entrées (arithmetique, ensembles_cantor_bernstein_final,
iii_2/3/4/5/6_*, __init__). **Gate 3005/1 partout.** TOUTE la structure de `bourbaki/` calque désormais
le livre, ≤10 entrées/dossier.
- Vérif runtime lancée : `pytest --timeout=1200` plein dépôt (20 min/test : Hessenberg ~16 min passe, le
  test qui pendait 1h20 sera tué → cible ÉTAPE D). Tâche `bbkjszyow`.
- ## 2026-06-23 — tests/ mirrorés + dossiers-trous : ÉTAPE A quasi finie

- **`tests/` mirroré** (outil `outils_ia/mirror_tests.py`, transactionnel ; cible déduite par résolution
  sur disque du module importé, formes contiguë + `from PKG import mod`) : structures, cardinaux (178),
  ensembles (74), entiers (56), ordre (34). **Tout `tests/` ≤10.**
- **`pytest.ini` ajouté : `--import-mode=importlib`** — INDISPENSABLE au mirroring : sinon, créer des
  `__init__.py` dans des sous-dossiers de test alors que `tests/<pkg>/` n'en a pas casse la résolution de
  paquet (`No module named 'iii_7_limites.test_cofinal'`). importlib ignore les `__init__` et tolère les
  basenames dupliqués. Baseline confirmée 3005/1 avec ce mode.
- **16 dossiers-trous créés** (TODO `__init__.py` par résultat manquant). 2 d'entre eux (II.3.1 graphes,
  II.3.9) débordaient `fonctions/` (10→12) → retirés, documentés dans `fonctions/ii_3_general/__init__.py`.
- ⚠️ **≤10 RESTE À CORRIGER : `bourbaki/ensembles/` = 11** (pré-existant de la migration ensembles, raté
  car gaté seulement à la collecte). Entrées : base, familles, fonctions, relations, ii_1, ii_2, ii_3,
  ii_4, ii_6, iii_3_ordre_cardinaux, __init__. Fix prévu : nester `relations/` sous `ii_3_correspondances/`
  (les deux = II.3) via une entrée synthétique dans reorg_moves + migration_arbre ; et/ou déplacer
  `iii_3_ordre_cardinaux/` (III.3 mal placé dans chap II) vers `cardinaux/` (cross-package). LEÇON : gater
  AUSSI le ≤10 après chaque migration, pas seulement la collecte.

**RESTE pour finir ÉTAPE A** : (0) corriger `ensembles/`=11 ; (1) confirmer le run runtime ; (2) **mirroring `tests/`** — les fichiers
  `tests/<paquet>/test_X.py` sont encore À PLAT (≤10 non satisfait côté tests) ; les ranger dans le
  sous-dossier miroir de leur module (déduire le sous-dossier depuis les imports `from bourbaki.<pkg>...`
  réécrits du test) ; (3) créer les **16 dossiers-trous** (normaliser les chemins, certains mal préfixés).
- Note : `ensembles_cantor_bernstein_final/` reste un sous-paquet autonome à la racine de cardinaux/
  (≤10 OK) ; à ranger sous iii_3 plus tard (cosmétique).
- **Outil migration_arbre.py = définitif** : transactionnel, scan tout V9, renommages de paquets, formes
  parenthésées, validation de format, garde anti-contamination. Aucune régression possible en silence.


## 2026-06-23 (nuit) - ETAPE D: diagnostic perf + PIVOT strategique

Profilage de trois_impair (proof cardinal ~400s, outils_ia/profil_hotspot.txt) : le cout est ALGORITHMIQUE, pas un hotspot cachable. Pour UNE preuve : ~46M modus_ponens, ~200M noeuds construits, hash = 70% du temps (434M appels). Cause : les tactiques s'etendent sur les formules-abreviations (impl=ou/non, et, equiv, pourtout) contenant le terme cardinal profond (~156k noeuds), generant un nombre polynomial/exponentiel d'operations.

- FAIT : memoisation subst_t/subst_f (lru_cache borne 1M) = gain 28% (551->397s), sound (fonction pure, sanity logique verte). Commitee.
- MUR : aller plus loin = refonte du noyau/tactiques (representation, partage, memoisation des theoremes) -> RISQUE sur la frontiere de confiance, HORS SCOPE d'une nuit autonome. Les preuves cardinales arithmetiques profondes (Hessenberg Lemme 2, trois_puiss_impair, division euclidienne, bon ordre cardinaux) restent donc PARTIELLES/MANQUANTES, documentees, perf-bloquees.
- PIVOT : concentrer ETAPE B sur les ~100+ resultats de l'audit NON bloques par cette perf (II.3 fonctions, II.4 familles, II.5 produits, II.6 equivalence, III.1 ordre, III.2 bon ordre : set/order-theoriques, peu/pas de cardinaux profonds). Fan-out de planification puis delegation d'implementation, un resultat a la fois, certifie noyau.


## 2026-06-24 - Epluchage PDF Ch I-IV + comblages (boucle autonome, garde-fou budget)

Audit page-par-page des 4 chapitres (workflow wfvn3moxp, 12 agents schema-valides) -> COUVERTURE.md :
707 notions, 305 closes (43%), 501 presentes (71%) ; sur 644 formalisables (hors meta subsumee
noyau) 47% closes, 78% presentes. Ch IV quasi clos (manquants = exemples renvoyant a d'autres
volumes). Garde-fou budget calibre (outils_ia/budget_tracker.json) : 928k tok = 38->55%, taux
54604 tok/pt, pause a 80% = 2293373 tok.

### Prop 2 Galois (E III.7-8) : retrait d'une hypothese non load-bearing
Bourbaki enonce 8 antecedents (u, v DECROISSANTES + 2 inegalites v(u(x))>=x et u(v(x'))>=x') et
conclut u∘v∘u=u ET v∘u∘v=v. DECISION : on formalise la PREMIERE egalite u∘v∘u=u sous 7 hypotheses,
en RETIRANT « v decroissante » -- la preuve Bourbaki de la 1re egalite ne la consomme PAS (« la
seconde s'etablit de meme » : c'est la DUALE qui l'utilise). Garder est_decroissante(v) eut ete une
hyp INERTE = padding. Coherent avec « conditionnel honnete » (hyps = antecedents reellement
consommes ; aucune parasite ; conclusion jamais en hypothese). Verifie INDEPENDAMMENT (cible
reconstruite via API publique E.valeur, 7 hyps, theorie==22). Contraste avec assoc_inter_famille (hyp
inerte J_λ≠∅ GARDEE car elle touchait la convention ∩_∅=E) : ici retirer v-decroissante ne change rien
au sens de la 1re egalite (theoreme strictement plus fort, fidele a la preuve). SUITE OPTIONNELLE : la
duale v∘u∘v=v (donc Prop 2 complete sous 8 hyps) reste a faire pour le resultat nomme integral.
Module : bourbaki/ordre/iii_1_relations_ordre/iii_1_5_applications_croissantes/ensembles_prop2_galois.py.

### II.1 : Russell + singleton-inclusion
¬Coll_x(x∉x) (E II.3, pas d'ensemble de Russell ; lemme propositionnel ¬(P⇔¬P) construit) et
x∈X⇔{x}⊂X (E II.4) ajoutes a ii_1/ensembles_theoremes.py, CLOS, verifies independamment.
Lecon reconfirmee : l'audit a des FAUX NEGATIFS (z∈{x}⇔z=x etait deja fait = singleton_membre) ->
TOUJOURS verifier l'absence reelle dans le code avant de deleguer un comblage.
