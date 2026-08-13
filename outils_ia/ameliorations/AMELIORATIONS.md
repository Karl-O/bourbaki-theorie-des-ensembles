# Améliorations possibles — position stratégique du projet pour l'objectif IA

*Créé le 25 juil. 2026 (discussion Karl ↔ Claude, campagne FABLE-MAX).
But final rappelé : une IA qui CRÉE des théories pour résoudre des problèmes ;
la formalisation + les traces sont le SUBSTRAT, pas la fin.*

---

## Le pari stratégique (diagnostic honnête)

**Course frontale perdue d'avance** contre AlphaProof/OpenAI/mathlib :
- échelle : mathlib ≈ 150k+ théorèmes, set.mm ≈ 40k — nous ≈ 2 000 notions ;
- coût du feedback : nos preuves se RE-EXÉCUTENT (suite 2 h) vs replay Metamath en
  secondes — frein n°1 pour tout RL / recherche arborescente ;
- écosystème : un mainteneur + agents vs communautés.

**Pari défendable — la qualité du substrat plutôt que l'échelle** ; actifs quasi uniques :
1. **Le chemin comme donnée** : journal des stratégies ÉCHOUÉES, rapports de mur,
   pièges nommés — tout le monde jette le chemin, nous le gardons. Ce qu'une IA de
   création doit apprendre = la RECHERCHE, pas le produit fini.
2. **Vérificateur possédé** : noyau instrumentable à volonté (traçage, DAG, variantes).
3. **Boucle déjà opérationnelle** : jalons 1-3 (anti-unif → promotion MDL →
   conjectureur) avec théorème neuf certifié — l'hallucination est GRATUITE car le
   noyau re-vérifie.
4. **Homogénéité** : un livre, un style, motifs récurrents (recettes _inst_gen,
   alpha_bridge, patrons bijection) — signal dense pour compression/anti-unification.
5. **Ancrage livre↔formel** page/ligne (@livre) : donnée d'alignement rare
   (autoformalisation).

---

## Multiplicateurs prioritaires (ordre recommandé)

### M1 — Traçage `axiomes_consommes` + export DAG   [session dédiée noyau]
Ajouter au `Theoreme` un frozenset `axiomes_consommes`, propagé par CHAQUE règle
(union des supports des prémisses ; `N.axiome` ajoute le sien). Purement additif
(comptabilité, pas de déduction — la soundness n'y touche pas), mais c'est une
MODIFICATION DU NOYAU : session dédiée, suite complète en filet, jamais au fil de
l'eau. Gains : chaque théorème connaît sa théorie MINIMALE exacte (cf. discussion
« un théorème n'a pas besoin de tous les axiomes ») ; export du DAG de dérivations
= le corpus devient un jeu de données d'apprentissage ; répond à la question ouverte
« DAG vs tokens » par : avoir le DAG d'abord.

### M2 — Réduire le coût du feedback : cache/rejeu de preuves
Aujourd'hui chaque test reconstruit les théorèmes (N_existe ~5 min, suite 2 h).
Pistes : mémoïser les Theoreme construits (clé = (fonction, args) → sérialisation
sûre du séquent) ; mode « replay » qui vérifie une trace enregistrée au lieu de
reconstruire (rapprochement Metamath) ; cache inter-session des théorèmes lourds.
C'est LE goulet de tout méta-algo de recherche (marche aléatoire sur le DAG,
noyau-vérificateur exact — cf. mémoire méta-algo diffusion→marche).

### M3 — Journalisation systématique des échecs (continuer + structurer)
L'actif différenciant. Déjà bien fait par la campagne (rapports de mur, 3 stratégies
avant rapport, pièges consignés). Amélioration : format machine-lisible (un YAML/JSON
par échec : verrou, symptôme exact, stratégies tentées, remède final) pour que le
catalogue d'erreurs soit minable — cf. mémoire méta-corpus (structurer le catalogue
d'erreurs).

## Améliorations secondaires

- **M4 Vérificateur croisé indépendant** : un re-vérificateur minimal (autre langage
  ou Python minimal séparé) qui rejoue les séquents depuis les traces M2 — l'argument
  massue de Metamath (~20 vérificateurs) nous manque totalement.
- **M5 Miner set.mm comme carte de trous** (T1 de la mémoire méta-corpus) : énoncés +
  DAG + stratégie SEULEMENT (les pas ne se transfèrent pas : fondations ≠, τ-calcul).
- **M6 Autoformalisation sur l'ancrage @livre** : paires (texte du livre p.X L.a-b ↔
  énoncé formel) extraites automatiquement = données d'alignement fine-tuning.
- **M7 Générateur de variantes** : perturber les preuves existantes (noms, ordres,
  routes alternatives) pour densifier le corpus d'entraînement — possible car on
  possède le noyau (re-certification automatique).

## Veille concurrentielle (recherche web du 25 juil. 2026)

**La niche « τ-calcul natif + fidélité livre » reste VIDE** — confirmé :
- Le seul parent direct est toujours **Gaia** (José Grimm, Bourbaki en Coq, Journal of
  Formalized Reasoning) — repo rocq-community/gaia ACTIF (maj mars 2026). Grimm note
  lui-même que les quantificateurs de Coq ne sont PAS définis via le ε de Hilbert —
  notre implémentation native des assemblages/τ reste sans équivalent.
- Aucun assistant de preuve à ε/τ-calcul natif trouvé (la littérature ε est théorique :
  SEP, complexité de Herbrand). Aucun Bourbaki-Lean.
- holpy (Zhan, arXiv 1905.05970) confirme le noyau-Python comme choix viable ;
  + Knuckledragger (Zucker) comme expérience ITP Python récente.

**⚠️ MAIS le créneau wake-sleep/library-learning pour la preuve SE REMPLIT (2025-26)** :
- **DreamProver** (arXiv 2604.26311, avr. 2026) : agent wake-sleep qui fait évoluer des
  bibliothèques de lemmes transférables — voisin DIRECT de notre jalon 2 (volant).
- **FERMAT** (arXiv 2511.14778, nov. 2025) : environnement RL de formation ouverte de
  théories, « interestingness » scorée par LLM + abstraction de fonctions — voisin de
  notre jalon 3 (conjectureur).
- Contexte : Towards Autonomous Mathematics Research (2602.10177), AI Co-Mathematician
  (2605.06651), LeanMarathon (2606.05400), Avigad « Mathematicians in the Age of AI »
  (2603.03684).
**Conséquence sur le pari** : l'avantage défendable n'est PLUS le mécanisme wake-sleep
lui-même (d'autres l'ont) — c'est le SUBSTRAT : corpus certifié par un noyau possédé,
traces d'échecs conservées, fidélité livre↔formel, DAG exportable. Les multiplicateurs
M1-M3 deviennent d'autant plus prioritaires. À suivre : lire DreamProver et FERMAT en
détail (leurs benchmarks, ce qu'ils jettent que nous gardons).

## Vrais murs restants du corpus (rappel, cf. journal A5)
sup cardinal absent · comptes combinatoires opaques (30-42) · AXIOME_INTER_FAM I≠∅ ·
infra E/R-iso · Lemme 1 réunion filtrante · CST22.
