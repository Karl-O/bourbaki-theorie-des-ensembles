# PASSATION → OPUS 5 (26 juil. 2026, 1h30) — plan modèles/niveaux jusqu'au retour de Fable

**Contexte** : Karl n'a plus que ~7 % de Fable ; retour de Fable **jeudi 31 juil. 22h**.
Le directeur de session devient **Opus 5 niveau max (6/6)**. Il peut tout faire, il
mettra juste plus de temps face aux verrous — donc : plus de paliers, briefs plus
chirurgicaux, et STOP plus tôt (2 stratégies au lieu de 3 avant rapport de mur).
La boucle cron Fable (a94b1943) a été SUPPRIMÉE — la relancer sous Opus si désiré
(même prompt : en tête de CHANTIERS_FABLE_MAX.txt / journal).

## Grille modèle × niveau par type de tâche (semaine Opus)

| Tâche | Modèle | Niveau | Notes |
|---|---|---|---|
| Directeur (briefs, diagnostics verrous, décisions, journal) | Opus 5 | 6/6 | c'est lui qui parle à Karl |
| Builds de preuves À MOTIF EXISTANT (patrons bijection, congruences, _inst_gen, recettes du journal) | Opus 5 (agents) | 5-6/6 | découpe en paliers OBLIGATOIRE ; livrer les paliers verts |
| Infra NEUVE dure (sup cardinal, combinatoire réelle, fonctorialité B3, réunion filtrante) | Opus 5 | 6/6 | max 2 tentatives/session puis rapport de mur — OU attendre Fable jeudi |
| Recon / lecture (Grimm, articles erreurs, re-cartage) | Opus 5 | 3-4/6 | voire Sonnet pour extraction pure |
| Mécanique (manifestes, relances de tests, events.jsonl, coches) | Sonnet | 1-2/6 | |
| Rédaction (rapport V9 LaTeX, notes Grimm) | Opus 5 | 4-5/6 | style = calquer Grimm/V8 |

## Backlog priorisé (du plus sûr au plus dur)

1. **Relancer LOT-2** (⋃/⋂ d'un ensemble : n°67 + n°95 + prépare n°140 + ferme H_rec
   de n°57) — l'agent est MORT EN RECON (limite), rien d'écrit ; le brief complet est
   au journal (section LOT-2). Vérifier d'abord la suite complète full_suite7
   (bzcamazs3, scratchpad/full_suite7.txt) : si elle est morte aussi, la relancer.
2. **LOT-3 : Prop.4 famille** (B2 famille de bijections + B3 fonctorialité produit) —
   débloque 102-108/112/113 ; motifs : adjonction (produit_adjonction_bij), somme
   constante ; rafraîchir la docstring stale de prop4_famille_cardinaux l.20-24.
3. **Queues A4** : 0!=1-def2 (briques cartographiées, cf. ensembles_factorielle_def2_rec) ;
   T3a Prop5b partition ; transitivité n°57 ; forme graphe n°60 ; cas c−d de n°26
   (exige la soustraction Cor.4 §III.5.2).
4. **A- restants du re-cartage A5** : n°52/53/54/56/78/86/88/91/94, n°66-2e moitié,
   n°118, n°112/113 (détail : journal section « A5 — RE-CARTAGE »).
5. **ÉTUDE GRIMM** (dossier sources/grimm_gaia : RR-6999-v7, RR-7150-v10, jfra1, jfra2) :
   synthèse → outils_ia/ameliorations/GRIMM_NOTES.md avec, pour CHAQUE enseignement,
   le marqueur @source (fichier, page, §) : (a) comment il STRUCTURE ses articles
   (énoncé/implémentation/écarts au livre — modèle pour notre rapport V9) ; (b) les
   DIFFICULTÉS qu'il a rencontrées et ses solutions (τ simulé, choix, quotients,
   familles…) mappées sur NOS chantiers restants ; (c) divergences Coq vs notre τ natif.
6. **VEILLE « représentation des erreurs/chemins »** (demande Karl) : chercher HAL/
   arXiv/GitHub qui a formalisé la donnée d'ERREUR en preuve. Pistes connues à
   vérifier/lire : **Talia Ringer — proof repair** (thèse + PUMPKIN PATCH : la
   réparation de preuves = LA littérature la plus proche de « exploiter les erreurs ») ;
   LeanDojo (traces de tactiques, incluant échecs) ; TacticZero ; DreamProver
   (2604.26311) et FERMAT (2511.14778) déjà notés (ils JETTENT le chemin — notre créneau).
   Télécharger les PDF dans **sources/traces_et_erreurs/** ; si téléchargement impossible →
   DEMANDER À KARL (il téléchargera). Puis synthèse dans THEORIE_TRACE.md.
7. **Pause réflexive « notion d'erreur »** (demande Karl) : affiner la représentation
   (THEORIE_TRACE.md : terme d'algèbre de règles + MDP + vues) à la lumière des
   lectures 5-6 ; chaque choix JUSTIFIÉ par une source @source ou marqué « construit
   par nous, faute d'existant » ; spécifier le module de canonicité (SPEC seulement —
   le noyau reste INTOUCHÉ jusqu'à session dédiée avec Fable).
8. **Murs B durs** (sup cardinal — le plus rentable —, comptes combinatoires réels,
   AXIOME_INTER_FAM I≠∅, E/R-iso, réunion filtrante, CST22) : Opus 6/6 par paliers,
   ou attendre Fable jeudi.

## NOUVEAU PROTOCOLE @source (décision Karl, 26 juil.)
Toute notion venant d'une source EXTERNE au livre de Bourbaki est justifiée comme
@livre : (1) le PDF de la source est ENREGISTRÉ dans le projet (sources/grimm_gaia/,
sources/traces_et_erreurs/…) ; (2) marqueur `@source <fichier.pdf> p.<n> §<paragraphe>` posé
au-dessus de l'usage ; (3) vérification À LA PAGE (pymupdf→PNG si scan) qu'on a bien
retranscrit l'idée. Philosophie (rapports G8C de Karl, Downloads/G8C_Mission1 (1).pdf
et G8C_Mission2 vf (1).pdf — À LIRE par le directeur Opus pour s'imprégner de la
méthode) : **aucun choix sans preuve à l'appui** — lire les documentations, poser les
limites du projet, tracer les courbes jusqu'aux équations, faire correspondre au
matériel disponible. Appliqué à nous : chaque choix de conception (représentation des
erreurs, schéma de données, encodage) = soit une source citée à la page, soit une
dérivation documentée, soit un « construit par nous » explicite avec justification.

## Garde-fous inchangés (rappel court)
Rien postulé ; noyau/subst INTOUCHÉS ; theorie_ensembles()==22 ; ≤300 l/fichier ;
≤10 entrées/dossier ; .bak avant édition d'existant ; liants exotiques ; τ-liant =
lettre simple ; gardes anti-collision = liants TRAVERSÉS seulement ; fidélité PDF ;
événements traces (outils_ia/traces/events.jsonl, schéma SCHEMA.md) à CHAQUE clôture ;
journal CAMPAGNE_DEMOS.md à chaque tick ; mémoire persistante en fin de chantier.

## État exact au moment de la passation
- A1-A4 TERMINÉS (factorielle Déf.2 bouclée, recollement indexé, bergers plein).
- A5 : re-cartage FAIT (~26/76 débloqués) ; LOT-1 FAIT (n°26 clos, n°60 valeurs,
  n°57 a+b) ; LOT-2 à relancer (agent mort en recon).
- Suite complète full_suite7 (bzcamazs3) était EN COURS à la passation — vérifier
  son verdict (la précédente s'était éteinte à 76 % sans bilan pendant une limite).
- 37 événements dans traces/events.jsonl ; améliorations : AMELIORATIONS.md,
  THEORIE_TRACE.md ; veille DreamProver/FERMAT notée.
