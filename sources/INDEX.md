# sources/ — les documents de référence du projet

**Règle du projet (décision Karl, 26 juil. 2026) : aucun choix sans preuve à l'appui.**
Toute notion, tout choix de conception vient soit d'une source enregistrée ICI et citée
à la page, soit d'une dérivation documentée, soit d'un « construit par nous » explicite
et justifié. Ce dossier est le stock de références — comme on tient un stock de
composants avant de fabriquer une carte : on lit les documentations, on pose les limites,
on justifie chaque valeur choisie.

## Protocole de citation

- **Livre de Bourbaki** → marqueur `@livre` (format historique, inchangé) :
  `# @livre Ch.<C> §<s>.<ss> <Type>.<n> | E <III.xx> L.<a>-<b> | PDF p.<phys>`
  Le PDF de référence est ici : `livre_bourbaki/Bourbaki_Theorie_des_ensembles.pdf`
  (349 p. ; offsets de pagination : Ch. I +0, II +51, III +103, IV +203, Résumé +303 —
  toujours confirmer l'en-tête imprimé de la page rendue).
- **Toute autre source** (article, rapport, thèse) → marqueur `@source` :
  `@source sources/<sous-dossier>/<fichier>.pdf p.<page PDF> [§<section>]`
  La page est celle du PDF (pas celle imprimée) sauf mention contraire ; ajouter le §
  quand il est visible. Vérifier à la page qu'on a bien retranscrit l'idée (rendu PNG
  via pymupdf si le PDF est un scan sans couche texte).

## Catalogue

### livre_bourbaki/ — LA source (fidélité)
| Fichier | Quoi | Sert à |
|---|---|---|
| `Bourbaki_Theorie_des_ensembles.pdf` | N. Bourbaki, *Théorie des ensembles*, 349 p. (scan) | Fidélité de CHAQUE notion formalisée ; cible du projet |

### grimm_gaia/ — le prédécesseur direct (Bourbaki en Coq, projet Gaia)
| Fichier | Quoi | Sert à |
|---|---|---|
| `RR-6999-v7.pdf` | J. Grimm, rapport de recherche INRIA (théorie des ensembles) | Modèle de rédaction ; difficultés surmontées |
| `RR-7150-v10.pdf` | J. Grimm, rapport de recherche INRIA (suite : ordinaux/cardinaux) | idem, chantiers cardinaux |
| `thalion,+jfra1.pdf` | J. Grimm, *Implementation of Bourbaki's Elements of Mathematics in Coq*, Part One (JFR) | Structure d'article ; écarts assumés au livre |
| `thalion,+jfra2.pdf` | idem, Part Two (JFR) | idem |
→ Synthèse : `../outils_ia/ameliorations/GRIMM_NOTES.md` (axes rédaction / difficultés /
divergences Coq-vs-τ-natif).

### traces_et_erreurs/ — état de l'art « donnée d'erreur et de chemin »
| Fichier | Quoi | Sert à |
|---|---|---|
| `REPLica_Ringer_CPP2020.pdf` | Ringer, Sanchez-Stern, Grossman, Lerner, *REPLica: REPL Instrumentation for Coq Analysis*, CPP 2020 | **Prédécesseur direct de notre étage 2** : capture des tentatives ÉCHOUÉES, arbre de recherche (p.6 fig.5), couple annulé→final (p.6 §4.3), classification manuelle d'abord (p.7) |
| `PUMPKIN_PATCH_Ringer.pdf` | T. Ringer et al., *Adapting Proof Automation to Adapt Proofs* (PUMPKIN PATCH) | Un remède = une TRANSFORMATION de preuve (fonction), pas une annotation |
| `ProofRepairDataset_ITP2023.pdf` | *Building a Large Proof Repair Dataset*, ITP 2023 | Faisabilité d'un corpus de réparations à grande échelle |
→ Synthèse : `../outils_ia/ameliorations/THEORIE_TRACE.md`, section « ÉTAT DE L'ART ».

### related_work/ — les 5 menaces majeures de l'article (lues, fiches dans `article/FICHES_MENACES.md`)
| Fichier | Quoi | Sert à |
|---|---|---|
| `arxiv_1911.12073.pdf` | Olšák-Kaliszyk-Urban, *Property Invariant Embedding* (ECAI 2020) | démarcation C7 : invariance APPRISE pour le guidage ≠ WL exact pour la coïncidence ; 0 « Weisfeiler », 0 dédup |
| `arxiv_2602.17016.pdf` | *M2F: Math-to-Formal* (2026) | démarcation C6 : provenance au span mais fidélité par « **manual audit** » (p.8) — notre verdict est dérivé |
| `arxiv_2605.29955.pdf` | FAIR Meta, *Formalizing Mathematics at Scale* / ATLAS (2026) | C5 : succès NON-TRANSITIF assumé (p.4) ; C8 : « skill guides » p.6 = plus proche voisin de notre boucle |
| `arxiv_2603.19514.pdf` | *Learning to Disprove* (2026) | C4 : branche réfutable industrialisée ; 0 mention d'un 3ᵉ statut (mesuré) |
| `arxiv_2606.06468.pdf` | *Goedel-Architect* (2026) | concurrent n°1 : 2 diagnostics sur 3, forfeits LLM (« believes », p.3) non certifiés, aucun corpus persistant |

## À ajouter (manquants identifiés, à télécharger)
- First, Brun, Garg, *Baldur : Whole-Proof Generation and Repair with LLMs* (ESEC/FSE 2023) —
  réparation conditionnée par les MESSAGES D'ERREUR ; le voisin direct de nos couples remède.
- Lample et al., *HyperTree Proof Search* (HTPS, NeurIPS 2022) — l'arbre de recherche
  politique/valeur à grande échelle ; notre équation d'environnement, industrialisée.
- Yang & Deng, *CoqGym* (ICML 2019) — le noyau comme environnement d'apprentissage, 71k preuves.
- Wang et al., *Voyager* (2023) — bibliothèque de compétences VALIDÉES PAR EXÉCUTION pour un
  agent ; le motif M(s) hors mathématiques.
- Ringer, *Proof Repair* (thèse, U. Washington) — vue d'ensemble.
- **Li & Bundy, *ABC Repair System for Datalog-like Theories*** (+ thèse *Automating the Repair
  of Faulty Logical Theories*, Édimbourg) — ⚠️ VOISIN DIRECT découvert à la vérification du
  2 août : la RÉPARATION DE THÉORIES est un champ publié (abduction + révision de croyances +
  reformation ; 10 opérations de réparation typées, 5 pour incompatibilités / 5 pour
  insuffisances — à comparer à nos E1–E7). Cadre Datalog, pas de noyau certifié — mais toute
  publication devra le citer et s'en démarquer.
- **arXiv 2606.16541, *The Faithfulness Gap: Certifying Semantic Equivalence…*** (juin 2026) —
  ⚠️ la CERTIFICATION DE FIDÉLITÉ est un sujet chaud 2026 (empreintes de prouvabilité
  bidirectionnelles). Leur cadre : équivalence NL↔formel ; le nôtre : fidélité au LIVRE à la
  page/ligne + infidélité comme événement E6 certifiable. Distinct mais à citer.
- **arXiv 2602.02990, *Learning to Repair Lean Proofs from Compiler Feedback*** (2026) — datasets
  d'essais échoués + réparations conditionnées par les messages du compilateur : la vague
  2025-26 de la donnée d'échec. Non certifié, pas de périmètre calculé — notre écart exact.
- **Azerbayev et al., *ProofNet*** — 371 énoncés alignés manuels de licence ↔ Lean : le
  précédent d'ancrage à des manuels (sans grain page/ligne ni audit mécanique).
- **Kim & Hwang, *Forward Deployed Engineering: A Taxonomy and Definition*** (SSRN) — la seule
  articulation académique du métier FDE (vérif. 2 août) : 3 propriétés constitutives (product
  ownership, flux de connaissance bidirectionnel, boucle de productisation), 3 générations
  (Palantir / OpenAI / AX). Taxonomie DESCRIPTIVE — pas de mise en œuvre mesurée.
- **arXiv 2603.09619, *Context Engineering: From Prompts to Corporate Multi-Agent
  Architecture*** (2026) — 5 critères de qualité du contexte : pertinence, suffisance,
  isolation, économie, **provenance**. Nos pratiques les instancient indépendamment
  (provenance = @source/@livre ; économie = protocole de sobriété ; isolation = leçon
  worktree) — et vont plus loin : la boucle est CERTIFIÉE par le noyau.
- **arXiv 2602.14690, *Harness Engineering for Agentic AI Coding Tools*** (2026) — le
  « harnais » (boucle plans/sous-agents/checkpoints/récupération d'échec) comme objet
  d'ingénierie : le cadre générique dont notre campagne est une instance instrumentée.
- DreamProver (arXiv 2604.26311) et FERMAT (arXiv 2511.14778) — voisins du volant
  wake-sleep / formation de théories (cf. veille dans AMELIORATIONS.md).
- LeanDojo (NeurIPS 2023) — format de dataset de tactiques.
*Si un téléchargement échoue (paywall, robots), demander à Karl : il télécharge et dépose
le fichier ici, puis on pose les `@source`.*
