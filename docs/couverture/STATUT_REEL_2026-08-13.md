# STATUT RÉEL — 13 août 2026 (mesure relancée, tout vérifié par exécution)

**Pourquoi ce document.** Relancer la mesure de couverture après sept semaines,
et surtout : savoir **où regarder ensuite**. Tous les chiffres ci-dessous sont
obtenus en lançant les outils, aucun n'est estimé.

## Les trois instruments, et ce que chacun voit

| instrument | granularité | résultat au 13 août |
|---|---|---|
| `gen_livre_manifestes.py` | **la page** | 2187 notions · 0 à caler · 0 marqueur non conforme · **5 parties « complet sur l'intervalle »** |
| `gen_trous_livre.py` | **la ligne** | 1940 marqueurs sous `bourbaki/` · **211 intervalles non couverts** |
| `audit_reports.py` | le report | **51 reports** · **6 SUSPECTS** · 8 déjà annotés résolus |

`outils_ia/audit/couverture.py` reste PÉRIMÉ — ne pas s'y fier (déjà dit dans
`CLAUDE.md`).

## Le résultat principal : le premier instrument est SATURÉ, le second ne l'est pas

`gen_livre_manifestes.py` déclare les cinq parties complètes sur leur
intervalle — E I 14-46, E II 1-48, E III 2-66 + 87, E IV 1-26, E R 3-32. Il ne
peut donc **plus rien trouver** : chaque page du livre, dans les intervalles
couverts, a ses notions formalisées et marquées. C'est un excellent résultat, et
c'est aussi la fin de son utilité comme détecteur.

`gen_trous_livre.py`, lui, travaille une graduation plus fin : il regarde, *à
l'intérieur* d'une page, les intervalles de lignes situés **entre deux notions
consécutives**. Il en trouve **211** qui ne sont couverts par aucun marqueur.
Une page peut être « complète » au sens du premier et receler dix lignes que
personne n'a formalisées.

**C'est le seul endroit du dépôt où un détecteur automatique voit encore
quelque chose.** Le reste demande d'ouvrir le PDF.

## Progression mesurée

| | 30 juin | 4 août | 13 août |
|---|---|---|---|
| notions (manifestes) | — | 2147 | **2187** |
| marqueurs `@livre` | 939 | — | **1940** |
| modules `bourbaki/` | 616 | — | **767** |
| reports suivis | — | 45 | **51** |

## Les 211 trous de ligne, par chapitre

| chapitre | marqueurs | trous | densité |
|---|---|---|---|
| I — Description de la mathématique formelle | 272 | 28 | 10,3 % |
| II — Théorie des ensembles | 482 | **69** | **14,3 %** |
| III — Ordonnés, cardinaux, entiers | 952 | 87 | 9,1 % |
| IV — Structures | 184 | 21 | 11,4 % |
| R — Résumé | 50 | 6 | 12,0 % |

Le chapitre III porte le plus de trous en valeur absolue (87) mais c'est aussi
le plus couvert (952 marqueurs) : sa densité est la plus BASSE. **Le chapitre II
est celui qui décroche** — 14,3 %, pour la matière qui sert de socle à tout le
reste (couples, produit, correspondances, familles, équivalences).

### Les 10 intervalles les plus larges — par où commencer

| lignes | chap | page | entre … et … |
|---|---|---|---|
| 31 | IV | p.221 | `cst16_famille_morphismes_produit` → `cst17_morphisme_caracterise_par_graphe` |
| 29 | IV | p.227 | `factorisation_unique_des_solutions` → (fin) |
| 26 | I | p.40 | `c44` → `relation_univoque_x` |
| 25 | II | p.61 | `graphe_de_triple` → `image_dans_img` |
| 24 | IV | p.225 | `cst21_quotients_egales` → `axiome_QM_I` |
| 23 | III | p.110 | `est_strictement_monotone` → `galois_uvu_egale_u` |
| 23 | I | p.27 | `distribution` → `c15` |
| 22 | I | p.20 | `cf7` → `cf8` |
| 21 | III | p.132 | `inf_egal_somme_invariant` → `prop13_si_somme` |
| 20 | II | p.86 | `produit_fini_recursion` → `distributivite_reunion_inter_inclusion_directe` |

Carte complète, une ligne par notion, triée par chapitre/page/ligne :
`docs/couverture/CARTE_LIVRE_2026-08-13.md` (2161 lignes).

⚠️ **« Trou potentiel » ≠ « notion manquante ».** Un intervalle non couvert est
soit (a) une notion réellement pas formalisée — le cas intéressant ; soit (b) du
texte de liaison, un exemple, une remarque sans contenu formel ; soit (c) une
notion formalisée dont le `@livre` couvre un intervalle trop étroit. La carte
dit **où regarder**, pas ce qu'on y trouvera. Les trancher exige le PDF.

## Les 6 reports suspects sont tous au même endroit

`audit_reports.py` signale 6 entrées `REPORTES` dont un module porte déjà le
repère — donc peut-être **déjà démontrées**, et qu'on risquerait de refaire.
Les six sont dans `iii_7_limites` :

- Prop. 3 §III.7.2 — deux modules l'annoncent résolue, deux entrées la déclarent encore reportée ;
- Th. 1 §III.7.4 a) et b) — `th1_proj/ensembles_th1_conditions.py` porte `condition_iii`, `condition_iv`, `cible_th1_a` ;
- Prop. 5 §III.7.4 — `ensembles_cofinal.py` porte `est_systeme_projectif_filtrant`.

⚠️ La consigne de `CLAUDE.md` s'applique : **tester en code (import + appel)
qu'un report est bien ouvert avant d'y passer une minute.** Quatre reports
périmés ont déjà été trouvés en 24 h début août.

## Ce qui reste NON mesuré — à dire

- **La suite de tests complète n'a pas fini** (36 % après 36 min à l'écriture).
  Le chargement des 627 modules et 719 fichiers de test est vérifié, 0 échec ;
  que toutes les preuves passent ne l'est pas.
- **`outils_ia/`** n'a pas pu être vérifié par chargement : des prototypes
  calculent à l'import et dépassent 10 min. Seule l'analyse statique s'y applique
  (0 import mort sur 1626 `.py` scannés).
- **La justesse des `@livre` eux-mêmes** : 0 marqueur *non conforme* au format,
  mais rien ne garantit qu'un marqueur pointe la bonne page ou le bon intervalle.
- **FAIT vs PARTIEL** — le manque le plus important. Les 2187 notions disent
  qu'une notion est *formalisée et marquée*, **pas qu'elle est close au sens du
  noyau** (0 hypothèse non déchargée). Croiser les `@livre` avec les théorèmes
  réellement clos donnerait le seul taux qui réponde à la question du projet :
  « démontré dans le livre » coïncide-t-il avec « vérifié par la machine » ?
  **Ce croisement n'existe pas.** C'est le prochain instrument à construire.
