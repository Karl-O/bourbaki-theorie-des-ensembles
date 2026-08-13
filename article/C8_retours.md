# C8 — Les retours mesurés de la boucle de guidage M(s)

*(Consolidation du 2 août 2026, **réactualisée le 4 août 2026**. Base de preuve de la
revendication C8 de PLAN.md. Méthode : extraction d'`outils_ia/traces/events.jsonl`
(**163 événements** ; la version du 2 août en couvrait 95) ; chaque ligne cite son ou ses
événements source par numéro. Rien ici n'est un souvenir : tout est journalisé.)*

## L'affirmation exacte (à écrire telle quelle dans l'article)

> La boucle corpus→brief→agent a des retours **documentés instance par instance** : chaque
> échec payé une fois a, dans au moins un cas ultérieur mesuré, évité son repaiement.
> C'est une collection de cas tracés, PAS un effet moyen contrôlé (voir « validité » en bas).

## Le tableau avant/après

| # | ce que la boucle savait | source | AVANT (coût payé une fois) | APRÈS (comportement mesuré) |
|---|---|---|---|---|
| 1 | le squelette **révoqué** de `0!=1` + son certificat de vacuité, conservés | ev. 67, 81 | construction complète + révocation (26 juil) | après réparation de l'axiome, le brief prescrit « décharge H au lieu de la supposer » → le squelette se re-dérive **tel quel**, CLOS sans résidu, verdict adverse SOLIDE. **Un chantier de reconstruction économisé** |
| 2 | la route « n−1 » = cul-de-sac certifié (`difference_entiers` opaque) | ev. 84→85 | payée au tick sup_borne | le brief B3 porte l'interdit ; l'agent prend `succ(k)` **directement**, zéro tentative sur n−1. **Le mur n'est payé qu'une fois** |
| 3 | « BLOQUÉ » s'est révélé faux 9× → règle « re-mesurer avant de croire » dans chaque brief | ev. 61, 64, 65 (semaine) + les 6 antérieurs ev. 1, 8, 9, 10, 36, 37 (réconcilié 2 août : « + 5 antérieurs » était un compte de mémoire — liste canonique au README verite §4) | R-pivot : un « chantier multi-sessions » (8 fonctions / 6 fichiers) prescrit pour un problème déjà résolu | la sonde coûte des minutes (ex. : NN-instantiation « bloquée » passe en **4,7 s**) ; depuis la règle : **0 session perdue sur un mur fantôme** |
| 4 | l'enquête seg_ext complète (classes α, dérivation D1) | ev. 88 → 91 | ~1 h 35 de workflow d'enquête (2 agents) | le scan vectoriel refait la détection en **1,7 s** — ratio ~3 300× ; la prochaine incoherence de cette classe coûte une ligne de log |
| 5 | l'interdit du contre-théorème (« ne pas poser H, réparer l'axiome ») déplacé DANS le socle des briefs | ev. 67 (violation) → 81 | un agent a construit à 18h07 ce qu'un module proscrivait depuis 08h50 (fan-out aveugle aux interdits) | l'agent def2-zéro **respecte l'interdit et décharge** ; 0 récidive depuis que les interdits vivent dans les briefs |
| 6 | le piège de mémoïsation de M1 (2ᵉ appel sous-compte) | ev. 75 | découvert par mesure (−62 % sur `n_bien_ordonne`) | le vérificateur adverse suivant le **reproduit délibérément** (−62,5 %) comme contrôle au lieu d'en être victime : le piège est devenu un point de checklist |
| 7 | l'écart VARIABLES vs TERMES CLOS (9 388 vs 86 598 caractères) | ev. 63 | une session de diagnostic (26 juil) | réutilisé 2× sans coût : B3 mesure d'emblée que `h_seg` ne coïncide qu'aux termes clos ; la décharge de `bo` note « le piège n'a pas mordu » **parce que testé en premier** |
| 8 | les runs longs tués vers 50 min → découper par zone, logs au fil de l'eau | ev. 79 | 3 runs tués, dont un à 57 % avec **0 résultat rendu** | 3 suites intégrales menées à terme **par zones** (3 865, 3 888, 3 909 tests), chaque zone un acquis même en cas de mort |
| 9 | 2 agents ont écrit le même dossier sans isolation | ev. 72 | état fusionné testé par personne (sain **par chance** : 83 verts) | toutes les migrations suivantes en **un seul agent séquentiel** ; 0 incident de fusion depuis |
| 10 | un numéro de ligne @livre recopié se propage (5 sites, même valeur fausse) | ev. 86 | recomptage correctif sur 5 sites | règle « recompter sur le PNG, jamais recopier » dans les briefs → 2 conflits de marqueurs **détectés et corrigés** par les vérificateurs suivants, 0 nouvelle copie || 11 | **une carte de reports vieillit** : 4 entrées de `REPORTES` déclaraient ouverts des théorèmes déjà démontrés (Prop. 1 1°, Prop. 1 2°, Prop. 10 §III.1.10, Prop. 6) | ev. 151, 153 | j'ai commencé à réécrire `cone_unicite` — un théorème acquis — avant de tester en code que le report était réel | un OUTIL a été écrit dans la foulée (`outils_ia/audit/audit_reports.py`, ev. 153) : il croise chaque entrée `REPORTES` avec les marqueurs `@livre` du dépôt et sort le verdict en **une commande** (43 reports, 6 suspects, 5 déjà annotés résolus). La consigne « tester en code avant d'attaquer un report » est passée dans `CLAUDE.md` (ev. 154). **Le coût de re-vérification devient nul** |
| 12 | une hypothèse « honnête » peut être **insatisfiable** — donc rendre vacueux les théorèmes qui la portent | ev. 155 → 156 | trois théorèmes de C57 écrits sous une caractérisation du quotient NON gardée par le domaine : hors du domaine, `p(x)=τ_y((x,y)∈p)` porte sur une relation identiquement fausse et S7 identifie tous ces τ — aucun graphe de domaine borné ne peut la satisfaire | la faute réparée (section ET caractérisation gardées), la boucle a immédiatement **audité les 9 modules frères** écrits la même nuit (ev. 156) : toutes leurs formules d'hypothèses portent leur garde, le défaut était isolé. **Une faute a produit une vérification systématique, pas seulement un correctif local** |

## Les contre-exemples honnêtes (la boucle a aussi des échecs — les taire tuerait C8)

| cas | source | leçon tirée |
|---|---|---|
| le triage du directeur faux **21/21** (« cibles périmées » — aucun ne l'était) | ev. 94 | un pronostic transmis est un biais d'ancrage ; le brief disait heureusement « à vérifier, pas à croire », et l'agent a contredit |
| ~6,8 M tokens d'agents en 24 h, limite hebdo épuisée, 266 k perdus à 0 résultat | mémoire `sobriete-tokens-agents` | la grille modèle/effort existait et n'était pas appliquée aux sous-agents → protocole de sobriété |
| estimations de durée fausses ×2 (1 h 30–3 h annoncées, 6 h 15 réelles) | ev. 79 | le coût dominant est les tests, pas l'édition — intégré aux briefs suivants || le même mur payé **trois fois** avant d'être catalogué : appariement d'une brique (helpers privés, ev. 152), forme d'appel (ev. 158), puis la vraie cause — une collision de liants (le terme contenait « u », liant de `est_fonctionnel`) | ev. 152, 158, 161 → 162 | les deux premières leçons n'ont pas suffi à éviter la troisième : elles nommaient le SYMPTÔME (« modus ponens refuse »), pas la CLASSE de causes. La règle finalement écrite est diagnostique — « quand un MP refuse après substitution, tester d'abord une collision entre variable libre et liant, en changeant le NOM de l'objet » — et elle a permis de clore la Prop. 2 dans la foulée (ev. 162) |
| la suite complète a pris **5 h 46 au lieu de ~2 h** : un processus de test orphelin monopolisait le CPU depuis 4 h | ev. 160 | la règle « surveiller les tâches longues, tuer si pendu » existait DÉJÀ (mémoire du projet) et n'a pas été appliquée au lancement. Une règle en mémoire n'agit pas si elle n'est pas dans la checklist du geste concerné (ici : « avant de lancer une suite longue, lister et tuer les orphelins ») |

## Menace de validité (à écrire dans l'article, section Limitations)

Ces retours sont **observationnels** : on ne peut pas rejouer la semaine sans le corpus pour
mesurer un contrefactuel propre. La revendication C8 est donc : *« instances documentées de
non-repaiement, tracées de l'échec source au réemploi »* — pas un effet moyen. Ce qui la rend
solide malgré tout : (i) chaque instance est **datée et journalisée des deux côtés** (l'échec
ET le réemploi) ; (ii) plusieurs gains sont des **ratios mécaniques** indépendants de tout
contrefactuel (1,7 s vs 1 h 35 ; 4,7 s vs « multi-sessions ») ; (iii) les échecs de la boucle
sont journalisés avec la même discipline.

## Statut

C8 : 🟠 → **✅ consolidé** (ce document), **réactualisé au 4 août sur 163 événements**
(12 instances de non-repaiement, 5 contre-exemples honnêtes). Reste pour l'article :
traduire le tableau en LaTeX (§5-§6) et câbler les numéros d'événements en références
vérifiables du dépôt.

**Ce que la réactualisation ajoute à la thèse.** Les deux instances neuves (11, 12) sont
d'une nature différente des dix premières : elles ne portent pas sur un mur de PREUVE mais
sur la **fiabilité de la carte** et sur la **satisfiabilité d'une hypothèse**. L'instance 12
est le cas le plus net de « failure as a theorem » du corpus : le noyau n'a rien refusé —
les trois théorèmes étaient corrects — c'est l'INSTRUMENTATION qui a établi qu'ils étaient
vacueux, et la réparation a été vérifiée par re-mesure (3/4/3 hypothèses, 232 tests). Et le
contre-exemple neuf (le mur payé trois fois) précise la portée de C8 : une leçon ne prévient
le repaiement que si elle nomme la CLASSE de causes, pas le symptôme.
