# V9 — Noyau de preuve strict pour la Théorie des Ensembles de Bourbaki

Repart sur des bases saines après le constat de la V8 : la couche
*syntaxique* (assemblages) était fidèle, mais le *moteur de démonstration*
ne réalisait pas vraiment ce que la théorie décrit (modus ponens heuristique,
actions non branchées, `est_significatif` ≡ `len ≤ 50`, apprentissage sur des
étiquettes). V9 reconstruit le **cœur logique** d'abord, en architecture LCF :
un petit noyau de confiance, tout le reste prouvé par-dessus.

## Couches

| Fichier | Rôle | Confiance |
|---|---|---|
| `assemblage.py` | Couche 0 — assemblages `(signes, liens)`, τ, substitution. Vérité de terrain, fidèle à Bourbaki. Liens canonicalisés. | — |
| `lecture.py` | Couche 1 — **lecture unique** (Appendice) : `depuis_assemblage`/`vers_assemblage`, prédicats `est_terme/est_relation/est_significatif` réels. | round-trip testé |
| `noyau.py` | Couche 2 — **noyau de confiance** : séquents `Γ⊢B`, `Theoreme` opaque + primitives `assume`, S1–S7, `axiome`, modus ponens correct, déduction (C6), généralisation (C27). | **à auditer** |
| `tactiques.py` | Couche 3 — règles dérivées : `affaiblissement`, `a_implique_a`, `syllogisme`, `distribution` (comb. S), `importation`, `mono_droite`/`mono_gauche`. | dérivé |
| `tactiques_prop.py` | Couche 3 — boîte à outils propositionnelle (toutes dérivées de S1–S4) : double négation (intro/élim), contraposition, syllogisme disjonctif, conjonction, `A⇔A`. | dérivé |
| `tactiques_egalite.py` | Couche 3 — `instanciation_en_x` (C30), `importation`, et les **propriétés de l'égalité** : `reflexivite` (Th1), `symetrie` (Th2), `transitivite` (Th3). | dérivé |
| `chercheur.py` | Couche 4 — **recherche branchée sur le noyau** : saturation MP + chaînage arrière (déduction) + instances de schémas. Renvoie un `Theoreme` ⇒ « trouvé » = « vérifié ». | dérivé |
| `chercheur_appris.py` | Couche 4 — recherche **meilleur-d'abord guidée par priors appris** (P(famille de schéma utile)), métrique « nœuds » réelle (= modus ponens vérifiés). | dérivé |
| `notation.py` | Couche 5 — traduction **lisible ⇄ assemblage** (`afficher`, `lire_formule`) pour dialoguer avec un LLM en `¬ ∨ ⇒ = τ`. | dérivé |
| `verificateur_preuve.py` | Couche 5 — **« brouillon + vérif »** : exécute une preuve proposée (script de tactiques) pas à pas dans le noyau ; certifie ou pointe la ligne fautive. Interface agnostique (`prouver_par_llm`). | dérivé |
| `exemples_livre.py` | Couche 5 — **8 démonstrations du livre** (C8, Th1–3, syllogisme, tiers exclu, contraposition) comme scripts certifiés par le noyau ; corpus *few-shot* pour l'IA. | dérivé |
| `encodeur.py` | Couche 5 — **encodage des valeurs pures** (assemblages) en vecteurs numériques (comptes, profondeur, `impl_reflexive`, répétition…), sans notation. | dérivé |
| `modele.py` | Couche 5 — **« ta propre IA »** : régression logistique from-scratch (Python pur, 0 dépendance) sur les vecteurs de l'encodeur. | dérivé |
| `propositions.py` | Couche 0 — **atomes propositionnels** (signes-relations de poids 0) : A⇒A est littéralement `∨¬AA`. | dérivé |
| `donnees_entrainement.py` | Couche 5 — jeu de données **étiqueté par le noyau** (positifs = théorèmes vérifiés, dont ceux démontrés du livre ; négatifs = négations). | dérivé |
| `chercheur_ia.py` | Couche 5 — recherche guidée par l'IA de pertinence (forward-only) + `benchmark_ia` (validation honnête). | dérivé |
| `couverture.py` | **Tableau de couverture** : inventaire des résultats nommés du livre (S/CS/CF/C/A, miné de V7) vs ce que V9 vérifie. Rend les manques explicites — anti-oubli. **30/100 critères nommés** (C = 23/63). | suivi |
| `criteres_C.py` | Critères logiques **C7–C25** (couverts via workflow multi-agents, re-vérifiés par le noyau dans `test_criteres_C.py`). | dérivé |
| `prouveur_goal.py` | Couche 4 (refonte) — **prouveur GOAL-DIRECTED** : déduction d'abord (R⇒R immédiat) ; feuilles armées par les **tactiques** (contraposition, double négation) comme macro-opérateurs. Couverture **12/12** vs 4/12 pour l'ancien. | dérivé |
| `test_*.py` | Round-trip + `A⇒A` + déduction + S5/S6/S7 + boîte à outils + généralisation + égalité (Th1–3) + recherche + apprentissage + notation + brouillon/vérif + corpus livre + encodeur + IA-valeurs. | 80/80 |

Tous les énoncés d'axiomes et de définitions ont été **vérifiés verbatim** sur le
PDF source (scan, lu via PyMuPDF) : conjonction (E.I.29), équivalence (E.I.30),
∃/∀ (E.I.32), S5 (E.I.33), S6/S7 (E.I.38).

## La frontière de confiance

Tout repose sur **`noyau.py`** (≈ 170 lignes). Un `Theoreme` ne peut être
créé qu'avec la clé privée `_CLE`, que seules les règles primitives possèdent.
Hors du noyau, impossible de fabriquer un théorème « à la main »
(`test_theoreme_inforgeable`). Donc : si le noyau est correct, toute preuve
qui en sort est correcte.

Le modus ponens y est **réel** : il *lit* la majeure `⊢(R⇒S)`, vérifie
structurellement la forme `∨ ¬R S` et que `R` coïncide avec la mineure, puis
reconstruit `S`. Plus aucune devinette de préfixe (cf. V8).

**Base de confiance actuelle** = {S1–S7, MP, axiome, `assume`, **C6/déduction**,
**C27/généralisation**}. C6 et C27 sont des primitives *de confiance* : leur
validité est exactement les théorèmes de la déduction et de la généralisation
que Bourbaki démontre (choix standard, cf. `DISCH`/`GEN` en HOL). Un raffinement
futur les démote en règles dérivées. Voir les notes de confiance dans `noyau.py`.

## Acquis

**Couche propositionnelle complète :**
- `⊢ A ⇒ A` démontré **par le noyau seul** (S1, S2, S4, MP), sur assemblages
  littéraux (`A = « a = b »`) ;
- loi de déduction (C6) + tactiques : affaiblissement (constructive),
  syllogisme (transitivité de ⇒), distribution (comb. S), importation.

**Base axiomatique S1–S7 complète et fidèle :**
- quantificateurs : définitions ∃/∀ via τ + schéma S5, primitives du noyau ;
- égalité : `=`, `⇔`, `et` + schémas S6, S7, primitives du noyau ;
- round-trip de lecture vérifié sur `(∃x)R`, `(∀x)R`, `=`, `⇔`.

**Théorèmes dérivés, tous vérifiés par le noyau :**
- boîte à outils propositionnelle (double négation, contraposition, conjonction
  intro/élim, équivalence intro/élim) — entièrement dérivée de S1–S4 ;
- généralisation (C27), instanciation universelle (C30), importation ;
- **propriétés de l'égalité** (E.I.39–40), reconstruites pas à pas selon Bourbaki :
  `⊢ x = x` (Th1), `⊢ (x=y)⇒(y=x)` (Th2), `⊢ ((x=y) et (y=z))⇒(x=z)` (Th3).

**Recherche branchée sur le noyau (le gap de V8, fermé) :** `chercheur.Prouveur`
trouve des démonstrations par saturation modus ponens + chaînage arrière
(déduction) + instances de schémas S1–S4, et **renvoie un `Theoreme` du noyau**.
Donc « preuve trouvée » == « preuve vérifiée » : on ne peut pas retourner un
théorème non démontré. (V8 cherchait sur des étiquettes et ne vérifiait rien.)

**Recherche guidée par priors appris (honnête) :** `ChercheurAppris` apprend
P(famille de schéma utile) en remontant la provenance des preuves trouvées, et
ordonne l'exploration (meilleur-d'abord) en conséquence. Les priors appris sont
sensés (S1, S2 utiles ; S3 rarement). **Gain de nœuds mesuré sur les buts-jouets
actuels : 0 %** — car l'heuristique de distance trouve déjà des preuves
quasi-minimales ; le mécanisme est correct mais ne *réduit* le coût que sur des
buts assez durs pour créer du branchement (travail futur). On rapporte le chiffre
réel, pas un gain postulé (contraste assumé avec les « 75 % » de V8).

64/64 tests verts. Démos :

```bash
PYTHONIOENCODING=utf-8 python3 V9/test_noyau.py            # A ⇒ A
PYTHONIOENCODING=utf-8 python3 V9/test_reflexivite.py      # x = x
PYTHONIOENCODING=utf-8 python3 V9/test_egalite.py          # symétrie, transitivité
PYTHONIOENCODING=utf-8 python3 V9/test_chercheur.py        # recherche → preuve vérifiée
PYTHONIOENCODING=utf-8 python3 V9/test_chercheur_appris.py # priors appris + benchmark
PYTHONIOENCODING=utf-8 python3 -m pytest V9/ -q
```

## Deux têtes d'IA, un seul garde-fou

Le noyau rend toute IA *sûre* : elle ne peut que proposer, le noyau certifie.
Deux têtes complémentaires, derrière le même garde-fou :

1. **LLM sur notation lisible** (`notation` + `verificateur_preuve`) : l'IA écrit
   une preuve en `¬ ∨ ⇒ = τ` ; le noyau la rejoue. *Brouillon + vérification.*
2. **IA sur valeurs pures** (`encodeur` + `modele` + `donnees_entrainement`) :
   un modèle numérique from-scratch lit directement l'assemblage et le score ;
   entraîné sur des théorèmes étiquetés par le noyau. *Construit et entraîné.*
   Deux encodages, comparés honnêtement :
   - `encoder` (comptes agrégés) : **0,685** test — les comptes perdent l'ordre
     et l'identité (∨¬AA et ∨¬AB ont presque les mêmes comptes) ;
   - `encoder_sequence` (sac de bi-grammes sur la séquence canonique, invariant
     par renommage) : **0,946** test — lire la *valeur pure elle-même* (∨¬AA ≠
     ∨¬AB) change tout.
   Le modèle reconnaît la *forme* d'un théorème ; il ne *décide* pas la
   théorémicité (indécidable) — le décideur reste le noyau. (Chiffres réels.)

**Boucle fermée — l'IA guide la recherche** (`chercheur_ia`) : un modèle de
*pertinence* « (intermédiaire, but) utile ? » entraîné sur les traces de preuves
vérifiées, branché en meilleur-d'abord. Tout résultat reste un `Theoreme` certifié.

**Validation à l'échelle (`benchmark_ia`) — résultat NÉGATIF, rapporté honnêtement :**
un mini-test favorable donnait −75 % de nœuds, mais sur un jeu plus large de buts
en test séparé, le gain **ne tient pas** (l'IA fait même un peu pire), et surtout
**la plupart des buts ne sont pas résolus du tout** (3/7). Le diagnostic : ce
n'est pas l'heuristique qui bloque, c'est le **prouveur** — la génération
d'instances de schémas (plafonnée, cubique) ne produit pas les instances requises
pour `¬B⇒¬B`, `(A∨D)⇒(A∨D)`, etc., donc la preuve est hors d'atteinte quel que
soit le guidage. **Le verrou est la recherche, pas l'IA.** (C'est précisément le
genre de chiffre que V8 maquillait ; ici on l'expose.)

**Réponse au verrou — refonte goal-directed (`prouveur_goal`)** : la déduction
(C6) résout toute implication `R⇒S` en supposant R et prouvant S — donc `R⇒R` et
les implications imbriquées deviennent immédiates (0 nœud), sans générer la
moindre instance. La recherche avant guidée ne sert plus que pour les *feuilles*
(non-implications : `X∨¬X`, `¬X`, …). **Couverture : 10/12 contre 4/12** pour
l'ancien forward-only, sur un jeu varié (R⇒R, tiers exclu, double négation,
contraposition). Puis les **tactiques prouvées comme macro-opérateurs de feuille**
(contraposée des hypothèses-implications, double négation des sous-formules) :
`(A⇒B)⇒(¬B⇒¬A)` et `A⇒¬¬A` se ferment en **1 nœud**, le tiers exclu `A∨¬A` en 28.
**Couverture finale : 12/12.**

**Ré-évaluation honnête du guidage IA (`benchmark_goal_ia`)** : sur ce terrain
équitable (recherche de feuille du tiers exclu, buts de test jamais vus), l'IA de
pertinence fait **pire** que la distance — **76 nœuds contre 56 (+36 %)**.
Conclusion sans détour : le modèle simple (régression logistique sur sacs de
bi-grammes) **ne bat pas l'heuristique de distance**, qui est un solide baseline
directement alignée sur le but. Le « −75 % » initial était un artefact d'un
mini-test.

**Traits d'alignement (option « modèle plus riche », `traits_alignement`)** :
distance d'édition + sous-formules canoniques partagées + containment +
recouvrement de bi-grammes. Résultat (seed fixé, reproductible) : **parité** avec
la distance (−4 %), pas de gain robuste. Surtout, on a découvert que le
benchmark est **dominé par le bruit** : selon `PYTHONHASHSEED`, l'écart oscille de
+46 % à −57 % (l'ordre des `set` change l'ordre du SGD). Verdict honnête : à cette
micro-échelle (2 buts), **l'effet est dans le bruit** ; trancher exigerait
beaucoup plus de buts et une moyenne multi-seeds. La distance reste le baseline à
battre.

**Corpus = les démonstrations du livre.** V7 contient 154 `Texte.tex` avec les
démonstrations de Bourbaki rédigées. Elles alimentent les deux têtes (exemples
few-shot, données d'entraînement). ⚠ Ces transcriptions sont *faillibles* (ex. la
preuve LaTeX du Th2 diffère du PDF) — le noyau V9 est précisément ce qui trie le
correct du faux.

## Suite (par ordre) — increments restants

1. **Buts plus durs / extension de la recherche** aux quantificateurs et à
   l'égalité (généralisation, S5–S7) — c'est là que les priors réduiront
   vraiment les nœuds (branchement réel).
2. **Critères de substitution CS1–CS5** et critères quantifiés restants
   (conditions « x non libre »).
3. (Raffinement) démoter C6 et C27 de primitives de confiance à règles dérivées.

### Limite connue de la recherche (v1)
La génération d'instances S4 est cubique en la taille du vocabulaire (bornée par
`_MAX_VOCAB`) ; le prouveur couvre le fragment propositionnel + implication, pas
encore les quantificateurs. C'est une base honnête et extensible, pas un
prouveur complet.

Conventions reprises de V6 : `.py` ≤ 300 lignes, un fichier = une
responsabilité, tests verts avant d'avancer.
