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

### III.2 Prop 2 + III.1.12 Prop 12 (reprise plafond 100%)
segment_extremite_strictement_croissant (E III.15-16) : x<y⇒S_x⊊S_y, conjonction de 2 briques closes
(seg_strict_monotone + seg_strict_propre), clos mod. 4 hyps. Verifie en reconstruisant la cible depuis
les briques memes.
borne_sup_critere_total (E III.14, Prop 12) : critere de sup en ordre total, equivalence double sens
close mod. 3 hyps. LECON DE FIDELITE : ma spec initiale codait « c<x » SANS le strict (c≠x), ce qui rend
l'equivalence FAUSSE (contre-ex E={0,1,2}, X={1}, b=2 : 2 majore {1} et tout c≤2 est « depasse » par
1≤2, or sup{1}=1≠2). Le NOYAU a refuse de prouver le faux (le sens ⇐ ne passe pas) ; l'agent a diagnostique
et retabli le « < » strict (c≠x), fidele au PDF et vrai. Confirme que le noyau LCF est le filet de
soundness ultime : une spec erronee ne produit pas un faux theoreme, elle bloque. Verifie independamment
(reconstruction COMPLETE de l'equivalence avec strict == thm.conclusion ; 3 hyps ; theorie==22).

### II.1 : Russell + singleton-inclusion
¬Coll_x(x∉x) (E II.3, pas d'ensemble de Russell ; lemme propositionnel ¬(P⇔¬P) construit) et
x∈X⇔{x}⊂X (E II.4) ajoutes a ii_1/ensembles_theoremes.py, CLOS, verifies independamment.
Lecon reconfirmee : l'audit a des FAUX NEGATIFS (z∈{x}⇔z=x etait deja fait = singleton_membre) ->
TOUJOURS verifier l'absence reelle dans le code avant de deleguer un comblage.

### II.2 #5 : caractérisation fonctionnelle des projections (E II.7) — via C45, pas de grappillage τ
`(∃y)(z=(x,y)) ⇔ x=pr₁z` (sous « z couple ») et son dual pr₂ : ajoutés à
ii_2_couples_produit/ensembles_projection_fonctionnelle.py. Conditionnels HONNÊTES
`{ univoque(R), est_couple(z) } ⊢ R ⇔ x=pr₁z`, conclusion==cible structurelle, theorie==22, 3 tests.
LEÇON D'ARCHITECTURE (réutilisable pour tout τ-fonctionnel) : ce résultat avait été classé « capture-dur »
après 4 approches structurelles ratées (∃-élim d'un conséquent portant pr₁z=τx(...) → α-renommage du liant).
La vraie voie est celle que Bourbaki CITE lui-même (« (I, p. 41) ») : le critère C45 (relations
fonctionnelles). ⇒ = `c45_avant(R,"x")` (univocité → R⇒x=τx R, et τx(R)≡pr₁z) ; ⇐ = `s6` (Leibniz) +
`existe_temoin` (identité-τ, existence). Le noyau construit τx(R) EN INTERNE, structurellement identique à
la projection → zéro renommage. RÈGLE : ne jamais bricoler un τ-fonctionnel à la main quand un critère C
le caractérise ; chercher d'abord le critère que Bourbaki invoque. Les deux hypothèses sont fidèles
(« fonctionnelle » = univoque + existe) ; univoque(R) est elle-même fermable via la Proposition 1 (résidu).

### II.3.8 dualité rétraction↔section (E II.19) : REJETÉE (tautologie déguisée) — 2026-06-30
Un agent-scout a trouvé et formalisé le « pont » `est_retraction(R,F,A) ⇒ est_section(F,R,A)`
(et dual), 5 tests verts, clos, theorie==22, énoncé==livre. **Re-vérification superviseur :
REJET, non commité.** Raison : les deux prédicats sont LITTÉRALEMENT la même condition r∘f=Id ;
le « théorème » est `P ⇒ α-renommage(P)` (vérifié : `alpha_egal(est_retraction(R,F,A),
est_section(F,R,A,y='z'))==True`). C'est une **tautologie déguisée** (règle « aucune tautologie
déguisée en théorème » ; cf. précédent `_est_iso_morph_reflexivite_triviale` gardé hors `__all__`).
Bourbaki lui-même la donne comme immédiate. Aucune version non-triviale possible (rien à sauver).
- BONUS : l'agent a re-trouvé le **collision-y connue** de `est_section` (liant ∀ défaut « y » ∩
  τ-muette « y » de `valeur` → formule dégradée ; `est_retraction` y échappe car liant « x »).
  DÉJÀ documentée (`ensembles_section_unique.py:23`) et gérée au cas par cas ; PAS de fix global
  (52 sites, `valeur` « y » rétro-compatible projet) — hors scope.
- LEÇON RE-CONFIRMÉE : la re-vérification indépendante du travail d'agent N'EST PAS optionnelle —
  « 5 tests verts / FAIT » de l'agent aurait committé une tautologie. §II.3.4-3.8 = SATURÉE
  (seul « trou » trouvé = α-trivial). Frontière réelle = chantiers cardinaux (lourds/lents).

---

## 12 août 2026 — UTILISER COQ/LEAN SANS LES IMPORTER

**Question de Karl** : mélanger Coq et Bourbaki, chacun là où il est bon ?

**La ligne, et elle n'est pas négociable** : la VÉRITÉ ne se mélange pas.
Importer un théorème de Coq ajoute son noyau, sa théorie des types et ses
axiomes à notre base de confiance. La frontière LCF du projet dit qu'un
`Theoreme` ne naît que des primitives du noyau — un pont Coq→nous la
détruirait, et avec elle la seule garantie que le projet offre.

**Ce qui se mélange, en revanche, c'est la CARTE.** Le coût d'un gros théorème
n'est pas dans les pas de preuve, il est dans l'architecture : quelle
décomposition en lemmes, quelles bornes intermédiaires, dans quel ordre. Cette
information est libre de fondations. La lire dans mathlib et la re-dériver chez
nous ne coûte RIEN en soundness, puisque notre noyau re-vérifie tout.
(C'est l'idée déjà consignée en mémoire : miner les énoncés, le DAG et la
stratégie — jamais les pas.)

**L'asymétrie qui rend l'échange intéressant** : ils ont l'étendue de
l'arithmétique élémentaire ; nous avons une chose qu'ils NE PEUVENT PAS écrire
— la forme sans quantificateur existentiel, parce que le τ de Hilbert est dans
nos fondations et pas dans les leurs. Partage naturel : leur bibliothèque comme
plan de route, notre noyau comme juge.

**LE RISQUE, à surveiller** : tout ce qui vient de mathlib n'est pas dans
Bourbaki, donc sort du comptage `@livre`. Or c'est cette discipline qui fait de
notre arbre un DÉTECTEUR DE TROUS du livre — un des rares outils du projet qui
ait vraiment payé. Un import mal rangé le casse silencieusement.

**Application immédiate envisagée** : le postulat de Bertrand est formalisé
dans mathlib. Lire sa décomposition en lemmes pourrait faire passer notre
estimation de « plusieurs mois » à « quelques semaines ». Le contenu formel
resterait intégralement construit ici, dans `recherche/`.

---

## 12 août 2026 — CE QUE LES 26 TOMES CONTIENNENT POUR BERTRAND (scan complet)

Karl a la collection Bourbaki complète. Scan des tables des matières et des
index, avec pages à l'appui. **Deux de mes affirmations précédentes étaient
fausses, dans des directions opposées** : « Legendre n'est dans aucun
Bourbaki » (faux), puis « sa machinerie est dans Algèbre commutative » (faux
aussi). Voici l'état réel.

### DÉMONTRÉ, directement utilisable

| repère Bourbaki | fichier / PDF | énoncé |
|---|---|---|
| **A I §4, th. 7 + cor.** | `2.1) Algèbre` **p. 59** | `a = ∏ p^{v_p(a)}`, unicité ; **`v_p(ab)=v_p(a)+v_p(b)`** ; **`a\|b ⟺ v_p(a)⩽v_p(b)`** |
| A I §4, déf. 16 | `2.1` p. 58 | définition de « premier » |
| A I §8 n°2, cor. 1 | `2.1` p. 104 | formule du binôme |
| A I §5 n°6, lemme | `2.1` p. 84 | `C(n,pʳ) ≡ m (mod p)` |
| A V §1 n°3, lemme 1 | `2.2` p. 107 | `p \| C(p,i)` pour `1⩽i⩽p−1` |
| A VII §1, th. 2 | `2.2` p. 335 | factorisation unique dans un anneau principal |
| **A VII §1, prop. 5** | `2.2` p. 337 | **« L'ensemble des nombres premiers est infini »** — SEUL résultat de répartition démontré dans un texte principal de toute la collection |
| AC VI §3, déf. 1 | `7.2` p. 96 | axiomes de valuation (`v_p` n'y est qu'un **exemple**, par renvoi à A VII) |
| FVR III §1 / V §3 | `4` p. 92 / 239 | exp, log ; formule de Stirling |

### ÉNONCÉ MAIS NON DÉMONTRÉ — et c'est une feuille de route

**`2.2) Algèbre`, page 384** (A VII.52), en exercices :

· **exerc. 19** — « l'exposant auquel figure un nombre premier `p` dans la
  décomposition de `n!` est `Σ_k ⌊n·p^{−k}⌋` ». **C'est la formule de
  Legendre.** Énoncée, non démontrée.

· **exerc. 20** — Tchebychev, avec les indications : *« remarquer que `C(2n,n)`
  est multiple du produit des premiers `q` tels que `n < q ⩽ 2n` … montrer que
  `C(2n,n)` divise `∏ p^{r(p)}` … remarquer que `2^{2n}(2n+1)^{−1} < C(2n,n)
  < 2^{2n}` »*. **C'est littéralement le squelette de la preuve d'Erdős**,
  écrit par Bourbaki, étapes dans l'ordre.

· exerc. 22 — l'intégralité des coefficients binomiaux, autre démonstration.

### CE QUI MANQUE DANS TOUTE LA COLLECTION

Aucune borne `Π_{p⩽n} p < 4ⁿ`, même en exercice. Aucun lemme de manipulation
de `⌊n/p⌋`. Le mot **« Bertrand » n'apparaît dans aucun des 26 volumes** ;
« Tchebychev » n'y est jamais arithmétique (approximation en EVT, convolution
en Intégration) ; le théorème des nombres premiers est **explicitement
sous-traité** à Ingham (1932) en note de bas de page.

**Verdict** : Bourbaki donne toute l'algèbre de la divisibilité et **zéro
arithmétique quantitative**. Le diagnostic du crible abstrait — « nos
réductions ne contiennent aucune arithmétique » — se prolonge intact jusqu'au
bout de la collection : ce n'est pas une lacune de notre travail, c'est une
frontière du traité lui-même.

### CORRECTION SUR LES BINOMIAUX — le trou est CHEZ NOUS

Les coefficients binomiaux de E III.42 portent les étiquettes **`cor. 1`** et
**`prop. 15`** : ce sont des résultats **démontrés dans le livre**, dont Sylow
(A I.74) et la formule du binôme (A I.94) se servent comme acquis. Notre dépôt
n'en a que les **énoncés** (`ensembles_combinatoire_enonces.py`). C'est donc du
rattrapage de couverture, pas de la création — et c'est le vrai premier pas.

### NOTE D'OUTILLAGE

Le PDF `1) Theorie Des Ensembles.pdf` est un **scan sans couche texte** : l'agent
n'a pas pu l'ouvrir et a reconstruit son contenu par les citations croisées des
25 autres volumes. Notre projet dispose pourtant d'un pipeline PDF qui
fonctionne (pymupdf) — à fournir aux agents de reconnaissance la prochaine fois.

## 2026-08-21 — Chantier division : la suite après le Th.1 complet

**Prochaine brique décidée : « a = bq ⟺ q = a/b » (E III.39, ligne sous la
Def.1).** C'est LA clé de toutes les identités de quotients de la page
((c+d)/b = c/b + d/b, (c−d)/b, a'/b = (a'/a)(a/b)) : elle convertit toute
équation de quotient en équation de PRODUIT, là où vivent les lois brutes.
Stratégie : le τ `quotient_cardinal(a,b)` satisfait sa propriété définissante
par le τ-axiome sous l'existence (témoin (q, 0), nécessite b·q+0 = b·q) ;
l'UNICITÉ du Th.1 complet identifie alors q au τ. Première consommation
réelle de `division_euclidienne` — le théorème sert dès sa naissance.

**Banc 2 du marcheur décidé : la distributivité pure a·(b+c) = a·b + a·c**
(exp6_pont_distributivite.py, écrit, à lancer machine libre). Le dépôt n'a
que la version niveau-ensembles Card(A×(B⊔C)) ; si la certification échoue,
la machine NOMME le pont manquant — les deux issues sont des résultats.

**III.5.7 inventorié** : énoncés formalisés (Prop.8, développement,
majoration a < b^a), DÉMONSTRATIONS NON DÉRIVÉES — gros PARTIEL, récurrence
sur k enchainant Prop.2 §4.2 / Prop.3 §5.2 / Prop.5 §5.4 / Cor.4 §4.4.
Parité (bas de E III.39) : déjà couverte (ensembles_parite_iii5).

## 2026-08-21 (21h15) — CIBLE CANTOR : lecture fidélité faite, plan posé

**Stratégie validée par Karl : cibles-qui-commandent** (les grands théorèmes
tirent la formalisation ; Goldbach = étalon de frontière ; jamais de tick
sans travail).

**Th.2 (Cantor), E III.30 L.20-21, PDF p.133 (scan VÉRIFIÉ, en-tête E III.30)** :
« Pour tout cardinal a, on a 2^a > a. » Démo L.22-28 : (i) Card(P(a)) = 2^a
par Prop.12 — DÉJÀ FORMALISÉE (iii_3_5_exposant/prop12_powerset :
powerset_deux, powerset_exp, prop12_fin) ; (ii) a ≤ 2^a par l'injection
x ↦ {x} de a dans P(a) ; (iii) a ≠ 2^a par la DIAGONALE : pour toute
f : a → P(a), X = {x ∈ a : x ∉ f(x)} n'est pas dans l'image (si x∈X,
x∉f(x) donc f(x)≠X ; si x∈a−X, x∈f(x) donc f(x)≠X).

FILE DE TRAVAIL CANTOR : (1) énoncé fidèle inf_strict_card(a, 2^a) sous
est_cardinal(a) ; (2) inventorier les briques : l'injection-singleton
existe-t-elle ? (grep singleton/injection dans iii_3) ; l'ensemble diagonal
= séparation/collectivisante (E II) ; (3) pointer marcher() sur l'énoncé
avec pool {prop12, briques ≤} → manques nommés = file de briques ;
(4) écrire les briques une à une. EN COURS AUSSI : identité (c+d)/b
(plan complet au journal de boucle, fichier quotient à 209 l).

## 2026-08-21 (21h25) — CANTOR : niveau ensembles DÉJÀ CLOS, il ne manque que le pont

Inventaire fait : `iii_3_equipotence_cardinaux/cantor/ensembles_cantor.py`
contient TOUT le cœur, certifié : injection-singleton (étape 1, X ≤ P(X)),
paradoxe_diagonal, aucune_surjection_parties, cantor_non_equipotent,
cantor_distinct, **cantor_strict ⊢ Card X < Card P(X)**. Et prop12_powerset
donne Card(P(a)) = 2^a.

CE QUI MANQUE pour le Th.2 du livre (E III.30 L.20-21, lu au scan) « pour
tout cardinal a, 2^a > a » : L'ASSEMBLAGE-PONT (≈ 60 l, patron du jour) :
  est_cardinal(a) ⇒ : cantor_strict(a) [Card a < Card P(a)] ;
  cardinal_de_cardinal [Card a = a] ; prop12 [Card P(a) = 2^a] ;
  réécritures (congruence sur <) → a < 2^a.
⚠️ la réécriture sous inf_strict_card = et(≤, ≠) : réécrire les DEUX
conjoints (congruence_terme sur chaque côté de ≤ et de ≠) ou lemme de
substitution d'égaux dans < s'il existe (grep reecrit/substitution ordre).
Fichier : cantor/ensembles_cantor_theoreme2.py (dossier à 3 entrées, OK)
+ test miroir + @livre Ch.III §3.6? NON — vérifier la SECTION du Th.2 :
la page E III.30 est §3 fin (avant §4) — marqueur « Ch.III §3.6 Th.2 » ?
le § imprimé en haut de page dit §3 n°6… vérifier le numéro de sous-section
au scan (p.133 : § 3 ? l'en-tête dit §4 ENTIERS NATURELS commence PLUS BAS
sur la page — le Th.2 est en §3.6 « le théorème de Cantor » probablement).

EN COURS : identité somme_quotients écrite, test en fond (blxaqyfwo).
