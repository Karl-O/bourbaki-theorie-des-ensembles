# Théorie de la trace — formaliser les chemins, erreurs et lois du processus de preuve

*Idée de Karl (25 juil. 2026) : « créer ou trouver une théorie qui permette de bien
renseigner tout ce qu'on enregistre — les erreurs, les chemins — pour une IA ; avec
des preuves en math, ou des stats pour des lois empiriques (moins bien qu'une preuve). »*

Le journal actuel (CAMPAGNE_DEMOS.md) est de la prose. L'objectif ici : que le
PROCESSUS de recherche de preuve devienne un objet formel de première classe —
comme les théorèmes le sont déjà. Personne ne fait ça (DreamProver/FERMAT gardent
les lemmes réussis, jettent le chemin ; LeanDojo trace les tactiques mais sans
théorie des échecs).

---

## Architecture en 3 étages + 1 principe

### PRINCIPE TRANSVERSAL — la hiérarchie de confiance (typée, obligatoire)
Toute assertion du corpus méta porte son STATUT :
1. **PROUVÉ** — certifié par le noyau (un Theoreme) ;
2. **MÉTA-PROUVÉ** — démontré rigoureusement SUR le formalisme (comme les
   métathéorèmes E I.19 : prose+preuve ou fonction Python vérifiable, jamais un
   Theoreme — convention déjà en place, cf. mémoire métathéorèmes-vs-théorèmes) ;
3. **EMPIRIQUE** — loi statistique sur les traces, avec effectif n, incertitude,
   et date de calcul. Explicitement « niveau ≤ preuve », révisable par nouvelles
   données.
Jamais de glissement silencieux d'un niveau à l'autre.

### ÉTAGE 1 — l'objet formel : le DAG de dérivation et de recherche
Définitions (méta-niveau, style chap. IV « structures ») :
- **Dérivation** : DAG dont les nœuds sont des séquents (hypotheses, conclusion)
  et les arêtes des instances de règles du noyau (s1-s7, mp, etc.) — c'est ce que
  M1 (axiomes_consommes + export DAG) rend extractible.
- **Trace de recherche** : sur-graphe de la dérivation incluant les branches MORTES :
  nœuds-tentatives, arêtes-stratégies, feuilles-échecs (avec symptôme).
- **Verrou** : classe d'échec récurrente (ex. « mineure ≠ antécédent par collision
  de nom ») ; **Remède** : transformation de trace qui convertit un échec en succès
  (ex. _inst_gen, alpha_bridge) — un remède EST une fonction sur les traces.
Méta-théorèmes visés (niveau 2, démontrables rigoureusement) :
- correction : tout nœud accepté par le noyau est dérivable (soundness du replay) ;
- monotonie des hypothèses le long des règles ; conservativité des théories dédiées
  (extension par définition) ; invariance α des classes de verrous ;
- terminaison/complétude de certains remèdes sur leur classe (ex. : _inst_gen
  résout TOUTE collision de nom d'argument dont le terme est clos — prouvable).

### ÉTAGE 2 — le schéma de données (vocabulaire contrôlé, machine-lisible)
Un événement = un enregistrement typé (JSON Lines, schéma versionné) :
- TENTATIVE {cible, stratégie, briques_invoquées, résultat: OK|ECHEC, coût: {temps,
  appels_noyau}, session, date}
- VERROU {symptôme_exact, classe, contexte (fichier, liants en jeu)}
- REMEDE {motif, classe_de_verrou, succès: bool}
- PERCÉE {item, nb_stratégies_avant_succès, briques_construites}
- MUR {brique_manquante, où_elle_devrait_vivre}  (= rapport de mur actuel, typé)
Rétro-remplissage : le journal existant (campagnes 24-25 juil : ~15 percées, 6
« bloqués faux », ~10 pièges nommés) se convertit à la main en premières instances.
Ensuite chaque tick émet ses événements (l'agent ou moi). C'est M3 durci.

### ÉTAGE 3 — les lois empiriques (statistiques sur les traces)
Mesures reproductibles calculées sur l'étage 2 (scripts dans outils_ia/) :
- taux de succès par (remède × classe de verrou) — ex. hypothèse à tester :
  « exotique+∀-clore+instancie résout >90 % des collisions de noms » ;
- distribution du nb de stratégies avant percée (données actuelles : médiane ~1-3,
  loi du « 3 stratégies puis mur » à valider) ;
- fréquence d'usage des briques (loi de Zipf attendue, comme dans mathlib) ;
- taux de « bloqué faux » (aujourd'hui 6 confirmés — prior fort : re-tester avant
  de croire un blocage documenté) ;
- coût moyen par famille de théorème (les N_existe ~5 min, suites ~2 h → données
  pour M2 cache-rejeu).
Usage IA : ces lois SONT la politique a priori du méta-algo (marche aléatoire
guidée sur le DAG, cf. mémoire méta-algo) — le prior de choix de stratégie,
appris des traces, raffiné par chaque campagne.

---

## ÉTAT DE L'ART — qui a déjà travaillé sur la donnée d'ERREUR en preuve ?
*(veille du 26 juil. 2026, demandée par Karl. Protocole @source : PDF enregistrés dans
V9/sources/ (catalogue : sources/INDEX.md), citations à la page. Conclusion : le travail existe — il ne faut PAS
tout construire — mais personne ne le fait sur un corpus certifié qu'il possède.)*

### A. LE prédécesseur direct : REPLica (Ringer, Sanchez-Stern, Grossman, Lerner — CPP 2020)
`@source sources/traces_et_erreurs/REPLica_Ringer_CPP2020.pdf` — 15 p. **C'est le travail le plus proche
de notre étage 2.** Ils instrumentent le REPL de Coq pour collecter des données
FINES sur le développement de preuves, « **failed proof attempts** and incremental
changes to definitions » (p.2), sur 8 ingénieurs de preuve pendant un mois, données
publiées avec consentement (p.2). Enseignements directement réutilisables :
- **L'objet « arbre de recherche »** : p.6, Figure 5 — « an example search tree,
  generated from the collected data […] the user attempting to apply a lemma, which
  fails until they first run the intros tactic ». C'est EXACTEMENT notre MDP/trace de
  recherche (§ ci-dessous) : nœuds = états, branches mortes conservées. **Validation
  externe de notre choix de représentation.**
- **La donnée-remède est un COUPLE (tentative annulée, tentative finale)** : p.6, §4.3
  — 96 tactiques annulées au profit d'une autre AU MÊME ÉTAT, classées en catégories
  (clause `;` ajoutée 13, retirée 4, même tactique à arguments modifiés 31…).
  ⇒ **notre type REMEDE doit stocker le COUPLE échec→succès à état constant**, pas
  seulement le remède. À corriger dans SCHEMA.md (v2).
- **Classification à 3 dimensions** des changements de termes (p.7, §5.1) + 4 patterns
  amenables à l'automatisation (p.7 : développement incrémental de types inductifs,
  refactoring répétitif d'identifiants, réparation répétitive de spécifications,
  découverte interactive). ⇒ modèle pour notre vocabulaire contrôlé de classes.
- **Méthodologie** : visualiser les changements en diffs, reconstruire l'état à chaque
  annulation, puis classer À LA MAIN avant d'automatiser (p.7, Methodology). ⇒ notre
  rétro-remplissage manuel d'events.jsonl est la bonne première étape, pas un pis-aller.
- Outil : github.com/uwplse/coq-change-analytics.

### B. La réparation de preuves comme TRANSFORMATION (Ringer, PUMPKIN PATCH)
`@source sources/traces_et_erreurs/PUMPKIN_PATCH_Ringer.pdf` + `sources/traces_et_erreurs/ProofRepairDataset_ITP2023.pdf`
(Building a Large Proof Repair Dataset, ITP 2023). Idée-clé transposable : **un remède
n'est pas une annotation, c'est une FONCTION sur les preuves** (transformation de terme
de preuve + décompilation vers un script) — exactement notre définition « remède =
fonction sur les traces ». Le dataset ITP 2023 montre qu'on peut construire un corpus
de réparations à grande échelle. Limite : centré sur la réparation après CHANGEMENT de
définitions (évolution), pas sur l'échec de RECHERCHE.

### C. Négatifs comme signal d'entraînement (littérature Lean 2025-26)
Pratique désormais courante : joindre à la génération de tactique « an explicit list of
tactics that have already failed earlier in the search, with their Lean error messages
attached as negative examples ». Et des taxonomies d'erreurs apparaissent (hallucination
de mathlib, erreur de typage, preuve incomplète, syntaxe) ainsi qu'une *fault taxonomy*
des pipelines de benchmark (Fidelity / Evaluation loopholes / Maintenance).
⇒ Les échecs comme données sont ADMIS par le domaine ; ce qui manque partout, c'est
leur STATUT FORMEL et leur conservation longue durée.

### D. Ce qui n'existe (toujours) pas — notre créneau, précisé
| Brique | REPLica | PUMPKIN/ITP23 | Lean/LLM 25-26 | NOUS |
|---|---|---|---|---|
| Échecs capturés | ✅ (humains, 1 mois) | partiel | ✅ (in-run, jetés après) | ✅ (agents, continu) |
| Données publiées/pérennes | ✅ | ✅ | ✗ (éphémère) | ✅ events.jsonl |
| Corpus de preuves POSSÉDÉ + noyau instrumentable | ✗ (Coq) | ✗ | ✗ | ✅ |
| Hiérarchie de confiance typée (prouvé/méta/empirique) | ✗ | ✗ | ✗ | ✅ |
| Ancrage à un texte source (page/ligne) | ✗ | ✗ | ✗ | ✅ @livre |
| Remèdes prouvés comme méta-théorèmes | ✗ | ✗ | ✗ | visé (étage 1) |
**Verdict** : ne PAS tout construire — reprendre (i) l'arbre de recherche de REPLica,
(ii) le couple annulé→final comme unité de remède, (iii) la classification manuelle
d'abord ; construire nous-mêmes (iv) le statut formel des remèdes (méta-théorèmes),
(v) la hiérarchie prouvé/méta/empirique, (vi) le lien DAG-certifié ↔ trace.

## REPRÉSENTATION MATHÉMATIQUE (question de Karl, 25 juil : « par quel type d'objet ? »)

### L'objet-mère n°1 — la preuve : un TERME dans l'algèbre des règles
Une dérivation est un **hypergraphe orienté acyclique étiqueté** : nœuds = séquents
(hypotheses, conclusion), hyper-arêtes = instances de règles (prémisses…)→conclusion,
étiquetées (nom de règle + paramètres : terme instancié, liant, trou). Vue équivalente
et plus maniable : **un terme de l'algèbre libre** sur la signature des règles
{mp(·,·), s6(t,u,w,R), assume(A), loi_deduction(A,·), …} avec PARTAGE des sous-preuves
(hash-consing ⇒ DAG, pas arbre). Nos preuves-programmes Python SONT déjà ce terme :
l'arbre d'appels de fonctions noyau. M1 le rend explicite : chaque Theoreme émet
(id = hash du séquent canonisé, règle, [ids prémisses], paramètres) → deux tables
(nœuds, arêtes) = le DAG en JSONL/Parquet, requêtable.

### L'objet-mère n°2 — la recherche : un MDP (processus de décision markovien)
La trace AVEC échecs est un **arbre de recherche dans un MDP** : états S = (but
courant, contexte, briques disponibles) ; actions A = (choisir stratégie / règle /
brique / remède) ; récompense terminale = succès(1)/échec(0) ; annotations d'arête =
symptôme, coût. Le dataset = trajectoires échantillonnées (état, action, résultat) —
exactement le format AlphaZero/politique. Les échecs ne sont PAS du bruit : ce sont
des trajectoires à récompense 0 étiquetées par le symptôme → elles entraînent (a) la
fonction de valeur, (b) le classifieur symptôme→remède (notre dataset unique).

### Le pont vers le jeu de données — trancher « DAG vs tokens » : ON GARDE LES DEUX
Le DAG est la SOURCE DE VÉRITÉ ; les données d'entraînement sont des VUES dérivées :
1. **Vue tokens** (pour LLM) : linéarisation canonique du DAG — ordre topologique
   déterministe + α-normalisation des liants (indices de de Bruijn ou noms canoniques)
   → séquences type Metamath/S-expressions.
2. **Vue graphe** (pour GNN/attention structurée) : adjacence + features de nœuds
   (le séquent, lui-même un terme → tree-encoding).
3. **Vue politique** : paires (but → action suivante) — format LeanDojo/tactic-prediction.
4. **Vue remèdes** : paires (symptôme, contexte) → remède — NOTRE spécificité.
5. **Vue alignement** : (texte du livre p.X L.a-b) ↔ (énoncé formel) via @livre.

### LE verrou technique : la CANONICITÉ
Deux preuves égales doivent donner la même donnée. Il faut une projection canonique :
α-normalisation (⚠️ dans NOTRE noyau les α-variants sont ≠ — c'est une feature pour
la fidélité, mais le dataset exige une couche de normalisation par-dessus), formes
canoniques des termes (le noyau a déjà l'égalité structurelle + interning), ordre
topologique déterministe, hash-consing. C'est un module à écrire (pur, hors noyau) —
prérequis de toutes les vues. À spécifier dans M1.

### Étage 3 typé : mesures empiriques
Une loi = une **mesure de probabilité empirique** sur un espace produit fini, ex.
P(succès | remède, classe_verrou) = tableau de contingence + intervalle de confiance
(events.jsonl suffit à les calculer). Statut EMPIRIQUE, n et date obligatoires.

## Exemples immédiats (données déjà disponibles dans le journal)
- VERROU classe « collision de nom d'argument » : ≥5 occurrences (q/distributivité,
  u/_couple_restriction, w/couple_egal, ifs/_NOMS_RESERVES, z/est_un_graphe) ;
  remède _inst_gen : 5/5 — candidat méta-théorème (étage 1) plutôt que loi.
- VERROU classe « α-variant de formule » : remède alpha_bridge 4/4.
- « bloqué » documenté ⇒ P(vraiment bloqué) ≈ faible (6 faux sur ~8 re-testés) —
  loi empirique la plus rentable de la campagne.

## Lien avec l'existant
- M1 (DAG/axiomes_consommes) fournit l'étage 1 ; M3 devient l'étage 2 ; l'étage 3
  est nouveau. La hiérarchie de confiance étend la convention métathéorèmes (E I.19).
- À chercher (veille) : « proof engineering metrics », « tactic prediction datasets »
  (LeanDojo), survival analysis sur processus de recherche — rien vu qui unifie
  formel + échecs + lois ; la théorie de la trace serait une contribution originale.
