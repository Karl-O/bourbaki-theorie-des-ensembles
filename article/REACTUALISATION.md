# RÉACTUALISATION DES CHIFFRES — avant gel v1

*(5 août 2026. Chaque ligne dit sa MÉTHODE de mesure, pour que la valeur soit
re-dérivable par un relecteur. Règle appliquée : les chiffres qui décrivent la
**semaine instrumentée** (26 juillet – 2 août) sont HISTORIQUES et ne doivent PAS
être touchés ; seuls les chiffres présentés comme « at the time of writing » sont
réactualisés. Confondre les deux falsifierait le compte rendu d'expérience.)*

## ✅ Appliqué — méthode reproductible, aucun arbitrage

| ligne | affirmation | avant | après | méthode |
|---|---|---|---|---|
| 200 | notions ancrées (§2, état du corpus) | 2 033 | **2 181** | `python outils_ia/audit/gen_livre_manifestes.py` |
| 407 | notions ancrées (§4, « at the time of writing ») | 2 033 | **2 181** | idem |
| 201 | journal d'événements certifiés (§2) | 95 | **223** | `wc -l outils_ia/traces/events.jsonl` |
| 741 | événements certifiés (Limitations, §Scale) | 95 | **223** | idem |

**Non touché volontairement** — ligne 584, tableau de la semaine : « **95** entries at
week's end (37 predate the week) ». C'est le relevé de la semaine instrumentée, pas
l'état courant. Le modifier détruirait la mesure.

## ✅ Appliqué — le compte de tests

`3{,}909` apparaissait 7 fois. Le papier dit « **collected** tests » : l'instrument
exact est donc `python -m pytest tests --collect-only -q`, qui rend **4 089** en
9 secondes — pas besoin d'attendre une exécution complète pour ce chiffre-là.

- l. 200 (« the corpus at the time of writing ») → **4 089** ✅
- l. 813 (future work, taille du corpus) → **4 089** ✅
- l. 60, 104, 478, 582, 583 → **inchangés, volontairement** : ils racontent la
  semaine (« ended with the full 3 909-test suite green », tableau
  « 3 850 → 3 909 », « green under the repaired axiom »). Ce sont des relevés
  d'expérience, pas l'état courant.

**Reste en attente** : le verdict VERT de la suite complète (en cours, ~35 %,
zéro échec à ce stade) et la durée réelle, qui dira si les `2\,h\,43` des
lignes 608 et 744 tiennent encore.

## ✅ Appliqué — les théories dédiées

L. 192 disait « 66 at the time of writing », un compte que je ne pouvais pas
reproduire faute d'outil. L'outil reconstruit le rend maintenant mesurable :
**60 fabriques `theorie_*`, dont 19 paramétriques** (`scan_jumeaux.fabriques()`).
L. 192 et 741 mises à jour avec ce chiffre et sa méthode.

## ✅ Vérifié inchangé — rien à faire

| affirmation | méthode | verdict |
|---|---|---|
| invariant **22 axiomes** (l. 168, 237, 258, 298, 433, 435, 448, 568, 800) | `len(E.theorie_ensembles().axiomes)` | **22** ✓ |
| couverture « complet sur l'intervalle » des 5 parties (E I 14-46, E II 1-48, E III 2-66+87, E IV 1-26, E R 3-32) | `gen_livre_manifestes.py` | ✓ **0 fichier à caler, 0 marqueur non conforme** |
| **69** références triées, **57** requêtes, 4 zones (l. 612, 635) | en-tête de `RELATED.md` | ✓ concordant |
| bibliographie | `python article/scripts/check_bib.py` | ✓ **47 citées / 47 définies, 0 orpheline** |

## ✅ RÉSOLU — le scan C7 est reconstruit, livré et testé

**Décision de Karl : reconstruire.** Fait le 5 août.

Livré : `outils_ia/vecteurs/phi_terme.py` (le vecteur WL, K = 3, d = 512) et
`outils_ia/vecteurs/scan_jumeaux.py` (le balayage), plus
`tests/outils_ia/test_vecteurs.py` — **8 tests verts**. La phrase de
reproductibilité du papier est désormais VRAIE, et elle nomme la commande.

**La validation la plus parlante** : le balayage reconstruit retrouve
`h_iso_max` à **0,9911** là où juillet publiait **0,9912**. Reproduction à la
quatrième décimale, par un code réécrit de zéro depuis la spec — c'est une
vérification indépendante de la mesure d'origine, pas une redite.

| mesure | publié (31 juil.) | re-mesuré (5 août) |
|---|---|---|
| axiomes vectorisés | 43 | **65** |
| théories dédiées scannées | 40 | **41** |
| durée | 1,7 s | **3,0 s** |
| paires au-dessus de θ = 0,90 | 24 | **34** |
| jumeaux (cos ≥ 0,95 ET même terme) | 1 (`h_iso_max`, 0,9912) | **1** (`h_iso_max`, **0,9911**) |
| fabriques paramétriques écartées | 25 | **19** |
| similarité maximale du balayage | 0,9961, termes ≠ | **1,0000**, termes ≠ |

Le §5 du papier a été réécrit avec ces valeurs. La similarité maximale à
**1,0000** entre deux axiomes caractérisant des termes DIFFÉRENTS est une
illustration plus forte que celle de juillet : le score seul aurait déclenché
l'alarme la plus bruyante du corpus, la conjonction ne déclenche rien.

**Un apport de méthode, trouvé par un faux positif.** Le premier critère
« même terme caractérisé » prenait tous les symboles propres à l'axiome. Il
appariait `axiome_majorants_F` (m ∈ U ⇔ (m ∈ [0,a] et …)) et
`axiome_intervalle_entiers` (x ∈ [a,b] ⇔ …) parce que les deux contiennent
`interv_ent` — mais le premier ne fait que le MENTIONNER. Deux axiomes qui
mentionnent un terme ne sont pas en conflit ; seuls deux qui le DÉFINISSENT le
sont. Le critère durci ne retient que le **définiendum**, membre gauche de
l'équivalence. Le jumeau parasite disparaît, `h_iso_max` reste seul, et le §5
gagne un paragraphe : c'est ce qui sépare un score d'un verdict, et c'était
invisible tant que le détecteur n'avait pas produit une alarme vérifiable à la
main. Test de régression : `test_mentionner_un_terme_n_est_pas_le_caracteriser`.

## 📜 Archive — l'état du problème avant reconstruction

**Le fait, vérifié.** L'article écrit (l. 620-621) :

> The corpus, the journal, and every script cited here ship in the repository snapshot
> referenced on the title page.

Or le détecteur d'axiomes jumeaux — l'instrument de la revendication **C7**, celui qui
produit « 43 axiomes de 40 théories dédiées en **1,7 s**, 24 paires au-dessus du seuil,
candidat `h_iso_max` à 0,9912, 25 fabriques paramétriques écartées », avec ses
paramètres cités en Reproductibilité (`K = 3`, `d = 512`, `θ = 0,90`) — **n'existe nulle
part dans le dépôt**. Recherché :

- `outils_ia/vecteurs/` : **le dossier n'existe pas** ;
- `phi_terme.py`, `table_features.py` (nommés dans `VECTORISATION.md` §6) : introuvables ;
- aucun fichier de `outils_ia/` (75 `.py`) ne contient `512`, ni d'implémentation
  Weisfeiler-Lehman ;
- `h_iso_max` n'apparaît que comme TERME mathématique dans `bourbaki/`, jamais dans un
  script d'analyse.

`VECTORISATION.md` §6 liste ces fichiers sous « **Infrastructure à construire** » : ils
n'ont jamais été écrits. Le scan a bien eu lieu (journal du 31 juillet : « scan des
axiomes jumeaux v1 — premier détecteur d'incohérence VECTORIEL »), mais **par un script
transitoire qui n'a pas été conservé**.

**Pourquoi c'est le vrai bloquant.** C'est plus grave que les placeholders. C7 est l'une
des neuf revendications, donnée « ✅ mesuré » ; un relecteur qui veut la reproduire ne
trouvera rien, et il trouvera en plus une phrase du papier qui affirme le contraire.
C'est exactement le type de défaut que la thèse du papier — l'instrumentation qui rend
les échecs vérifiables — rend impardonnable chez lui.

**Les trois issues possibles, à toi de trancher :**

1. **Reconstruire le scan** (`outils_ia/vecteurs/phi_terme.py` + le scan par paires) et
   le relancer. Avantage : C7 redevient pleinement reproductible et le §Reproductibilité
   redevient vrai. Risque : les chiffres re-mesurés (43 / 24 / 1,7 s) ne coïncideront
   probablement pas avec ceux du 31 juillet — le corpus a grossi — donc il faudra
   réécrire le paragraphe avec les nouvelles valeurs, ce qui est **plus honnête** mais
   demande une passe de rédaction.
2. **Restreindre la phrase de reproductibilité** : dire que le corpus et le journal
   sont au dépôt, et que le prototype du scan a été exécuté ad hoc, avec ses paramètres
   et ses résultats journalisés mais son code non conservé. Honnête, immédiat, mais
   affaiblit C7 d'une revendication « mesurée et reproductible » à « mesurée ».
3. **Retirer C7 de la v1** et la garder pour une v2 avec l'outil. Le plus coûteux.

Ma recommandation : **l'option 1**, parce que le scan est petit (WL à profondeur 3 +
hachage + cosinus par paires ; l'essentiel du travail est le marcheur `.sous/.termes/
.args`, déjà décrit dans `VECTORISATION.md`) et parce qu'un article dont la thèse est
la vérifiabilité ne peut pas se permettre l'option 2. Dis-moi et je l'écris.

## 🟡 À arbitrer aussi — « 66 théories dédiées »

L. 192 dit « 66 at the time of writing » ; l. 545-548 dit « 43 axiomes de **40** théories
dédiées » plus « **25** fabriques paramétriques écartées ». Les deux se réconcilient
(40 scannées + 25 écartées ≈ 65), donc **il n'y a pas de contradiction interne** — mais
je n'ai pas pu **reproduire** le compte 66, faute du script.

Ce que je mesure aujourd'hui, par une méthode explicite (`grep "^def theorie_"` sur
`bourbaki/`) : **38 fabriques de théories définies, dont 33 paramétriques et 5 sans
argument**, et **43 identifiants `theorie_*` distincts** référencés. Aucun de ces
nombres n'est 66 ; ils comptent autre chose (des fabriques, pas des instances mintées).
Tant que le script du scan n'est pas reconstruit, **je laisse 66 tel quel** plutôt que
d'y substituer un nombre obtenu par une autre méthode — ce serait remplacer un chiffre
non reproductible par un autre.

## Statut

Appliqué : 4 corrections. En attente : le total de tests (suite en cours). À décider :
le script C7 (bloquant réel), et le compte « 66 » qui en dépend.
