# ARTICLE A2 — plan de campagne (ouvert le 20 août 2026)

**Cible** : preprint arXiv (cs.LO / cs.AI), puis AITP ou CICM. **Langue : anglais**
(décision de `article/PLAN.md`, 2 août) ; traduction française ensuite, comme A1 et A3.

**Titre de travail** : *The Last Mile Is Located, Not Crossed: A Kernel-Verified System
That Names What It Lacks.*

**Position** : **A2** du plan éditorial (`docs/articles/PLAN_ARTICLES.md`). Question
unique : *comment une machine sait-elle ce qui lui manque — et comment mesure-t-on la
distance qui reste, au lieu de la décréter ?*

**Thèse** : le dernier kilomètre ne se franchit pas d'un coup, il **se localise**. Un
système qui échoue en produisant l'énoncé exact de son manque vaut plus qu'un système
qui réussit une fois sur deux sans savoir pourquoi.

## La règle d'or (reprise de A1 et A3)

**Chaque phrase de l'article doit être adossée à un objet du dépôt.** Le tableau
ci-dessous EST l'article.

## ⚠️ État de vérification au 20 août — LIRE AVANT D'ÉCRIRE

Le matériau (`docs/articles/ORGANES.md`, `PIEGES_MESURES.md`) date des 10–12 août. Les
mesures d'aujourd'hui montrent qu'il a **déjà dérivé**, exactement comme A1 avant sa
révision. Constaté en code :

| ce que le document dit | ce que le code dit |
|---|---|
| « 15 tests dans `test_autonomie.py` » | **20** tests |
| « dix-neuf lignes » de catalogue | le tableau en compte **21** |
| `besoin.py` à 259 lignes de code | **387** lignes |
| v3 (« fusionner les manques de la voie directe ») | **aucune trace en code** — absorbé ou disparu |
| v20 et v21 catalogués comme organes | testés, mais **ailleurs** : `tests/outils_ia/corpus/` (11 tests) |

**Rien ne sera écrit dans A2 sans avoir été re-mesuré.** C'est la leçon de la journée du
20 août sur A1 : cinq chiffres périmés y ont survécu à une relecture adverse complète.

## Table des revendications (claim → preuve → statut)

| # | revendication | preuve dans le dépôt | statut |
|---|---|---|---|
| **N1** | **L'échec devient une donnée.** L'organe rend, au lieu de « échec », la liste des formules qui — ajoutées au pool — fermeraient le but | `outils_ia/decouvertes/besoin.py` (387 l.) ; `test_besoin_ferme_et_nomme_ses_manques` | 🔵 à re-mesurer |
| **N2** | 🎯 **L'OUTIL SE DÉDUIT DU DIAGNOSTIC.** 21 organes, aucun issu d'une architecture pensée d'avance : chacun répond à un échec rejouable. *La colonne « né de quel diagnostic » est plus informative que la colonne « ce qu'il fait ».* | `ORGANES.md` (catalogue) ; 20 tests dans `test_autonomie.py` + 11 dans `tests/outils_ia/corpus/` | 🔵 catalogue à recaler |
| **N3** | **La frontière chaînage / créativité, tracée par la machine.** Jusqu'à v9 l'organe *chaîne* ; v6 accepte qu'on lui *propose* ; v13 **fabrique**. Le passage n'a pas été décidé — c'est le manque `¬(n = n)`, **écrit par la machine**, qui l'a imposé | `test_organe_v13_temoin_canonique_fabrique` | 🔵 |
| **N4** | **Le progrès n'est pas quantitatif.** v13 ne ferme pas plus de buts que v10 ; il change la **forme** du manque (`∃p∃q…` → propriétés d'un τ-terme). Un indicateur de volume l'aurait déclaré inutile | `PIEGES_MESURES.md` §3 ; comparaison v10/v13 | 🔵 |
| **N5** | **Le premier compounding réel.** v15 retient les témoins qui ont fermé : sur `decomposition(N16)`, 1ʳᵉ passe **102 s**, 2ᵈᵉ **0 s** | `test_organe_v15_compounding_du_proposeur_appris` | 🔵 chiffres à refaire |
| **N6** | **La machine aborde une algèbre inventée le jour même.** `a ⊕ b := (a+b)+1`, deux lois brutes sur `+` données, rien d'autre : commutativité par v16, associativité par v17+v18 | `test_organe_v16/v17/v18` ; `reecriture.py`, `congruence.py` | 🔵 |
| **N7** | 🎯 **UNE SIGNATURE D'ÉCHEC EXPLOITABLE.** Une recherche qui échoue *en grossissant* (coût ×2 par palier, manques figés) ne se répare presque jamais par plus de budget : deux fois sur deux la cause était en amont — ordre d'exploration, ou borne fixée au jugé. Rapport mesuré **24×** | `ANOMALIES.md` (12 août) ; docstring de `reecrire_vers` | 🔵 |
| **N8** | **Les pièges payés, et une loi.** 14 pièges mesurés ; et la loi de structure : *les termes sont opaques, les formules se décomposent* — descente naïve 333 s → table **3 s**, facteur 100 | `PIEGES_MESURES.md` | 🔵 |
| **N9** | **Ce que ça ne fait pas.** Aucun organe ne produit d'information mathématique. Face à Goldbach, arsenal complet au pool, la machine **ne ferme pas** — elle nomme exactement ce qui manque, et c'est la conjecture | renvoi à A3 | ✅ acquis |

## Ce que l'article NE revendique PAS

- **Aucun théorème mathématique nouveau.** Les organes manipulent des énoncés ; `⊕` est
  une opération jouet dont les deux lois sont des corollaires immédiats de celles de `+`.
- **Pas une architecture d'agent.** Il n'y a ni planificateur, ni politique apprise, ni
  boucle d'entraînement. C'est un chaînage avant/arrière branché sur un noyau exact, plus
  des proposeurs de témoins.
- **Pas de généralité prouvée.** Les 21 organes ont été taillés sur deux sujets (Goldbach,
  puis une algèbre jouet). Rien ne dit que le vingt-deuxième problème n'en réclamera pas
  cinq de plus — c'est même ce que la thèse prédit.
- **La complétude du catalogue n'est pas établie** (règle `STYLE_ARTICLES.md` §8) : 21
  organes identifiés, la liste est ouverte.

## Squelette

1. Introduction + contributions ← ce tableau
2. Background : le noyau, le pool, ce qu'est un « manque » (court — renvoyer à A1)
3. L'organe de besoin : de « échec » à une liste d'obligations
4. **Le catalogue et sa loi de croissance** ← N2, le cœur
5. Chaîner, proposer, fabriquer : une frontière tracée par la machine ← N3, N4
6. Capitaliser : le premier compounding ← N5
7. Une algèbre neuve en trois organes ← N6
8. **Signatures d'échec exploitables** ← N7, N8
9. Related work
10. Limitations
11. Conclusion : ce que ça ne fait pas, et ce que A4 devrait faire

## Figures

- **Figure centrale** : la courbe des manques au fil des sondes (14 → 8 → 6 → 4 → 1),
  chaque chute étiquetée par l'organe qui l'a produite. ⚠️ **CES CHIFFRES SONT À
  RE-MESURER** — ils viennent d'un journal de session, pas d'une exécution refaite.
- Figure : la frontière chaîner / proposer / fabriquer, et le manque à chaque étage.
- Table : le catalogue, colonne « né de quel diagnostic » en évidence.

## Bibliographie

`../references.bib` (52 entrées vérifiées). Réutilisables : `ringer2020replica`,
`first2023baldur`, `reichel2023proofrepair`, `blanchette2011nitpick`,
`learningtodisprove2026`, `conjecturingsurvey2026`, `ellis2021dreamcoder`,
`lample2022htps`, `polu2020gptf`, `jakubuv2020enigma`.

⚠️ À vérifier avant citation, non encore dans le `.bib` : les travaux sur la
*proof repair*, les *premise selection* récents, et tout ce qui touche à la
« localisation de l'échec » en démonstration automatique.

## Décisions

- Anglais d'abord, français ensuite — mêmes conventions que A1 et A3.
- A2 **cite A3** (le cas Goldbach) et **A1** (le noyau, la dette, les objets d'échec) :
  les deux sont publiés, la dépendance est donc saine.
- Le préambule de lisibilité de `STYLE_ARTICLES.md` §2 s'applique dès la première ligne.
