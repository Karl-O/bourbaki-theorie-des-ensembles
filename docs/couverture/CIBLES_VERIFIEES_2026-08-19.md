# Cibles HAUTE vérifiées en code — 19 août 2026

**C'est CE document, et non le tri, qui est la file de travail.** Le tri du
18 août classait 38 cibles « HAUTE » en lisant le PDF ; il ne pouvait pas
savoir ce que le dépôt contient déjà. Vérification faite, 767 fichiers `.py`
passés au crible :

| verdict | n | ce que ça veut dire |
|---|---:|---|
| **ABSENTE** | 17 | rien dans le dépôt : vraie formalisation à écrire |
| **DÉJÀ UNE `def`** | 20 | le nom existe — vérifier l'ÉNONCÉ avant de conclure |
| **PARTIELLE** | 1 | le sujet est touché, aucune `def` au nom attendu |

⚠️ **Ce que cette vérification ne dit PAS.** Une `def` au bon nom ne prouve
pas que son énoncé est celui de Bourbaki, ni qu'elle est close. Pour les
lignes « DÉJÀ UNE def », l'étape suivante est de lire la fonction ET la page
du livre — c'est la seule chose qui tranche, le noyau ne juge que la
soundness. Croiser aussi avec `statut_notions.py` pour FAIT/PARTIEL.

⚠️ **Piège d'outillage rencontré, à ne pas refaire.** Le premier passage a
été fait par `grep` lancé en sous-processus : le runtime MSYS de Git-Bash
EXPAND LES ACCOLADES des arguments, si bien que `pr.{0,6}surject` devenait
`pr.0surject` + `pr.6surject`, ce second morceau pris pour un nom de
fichier (`returncode 2`, sortie vide, comptée « 0 trouvé »). Tous les motifs
à quantificateur étaient donc faussés. Refait en `re` Python, sans shell.

---

## ABSENTES — la vraie file de travail (17)

| # | chapitre | cible | motif cherché |
|---|---|---|---|
| 3 | Ch.I p.31 | distrib. ou sur et (C24) | `ou_distrib\w*_et|distrib\w*_ou_sur_et` |
| 4 | Ch.I p.33 | déf. théorie quantifiée | `def theorie_quantifiee|est_theorie_quantifiee` |
| 7 | Ch.II p.54 | C49 | `\bc49\b` |
| 8 | Ch.II p.60 | R admet un graphe | `admet_un_graphe|admet_graphe` |
| 12 | Ch.II p.77 | déf. ∪ ∩ binaires (Bourbaki) | `def reunion_binaire|def inter(section)?_binaire` |
| 18 | Ch.II p.92 | graphe de R_f = F⁻¹∘F | `graphe_relation_associee|rf_graphe|relation_associee_graphe` |
| 19 | Ch.II p.93 | partition ⇒ équivalence | `partition\w*_(donne|definit|implique)\w*_equivalence` |
| 21 | Ch.II p.94 | relation déduite / passage au quotient | `passage_au_quotient|relation_deduite` |
| 22 | Ch.II p.95 | C57 clause h=f∘s | `c57_h_egale|h_egale_f_rond_s|c57_section` |
| 26 | Ch.III p.123 | Prop.4 Zorn fort | `zorn_fort|prop4_zorn|partie_bien_ordonnee_majoree` |
| 28 | Ch.III p.130 | Prop.6 neutres niveau FAMILLE | `neutre_famille|famille_neutre|somme_famille_zero` |
| 29 | Ch.III p.131 | Prop.10 a^b = ∏ (famille) | `prop10_puissance_produit|exposant_produit_famille` |
| 30 | Ch.III p.133 | pas d'ensemble de tous les cardinaux | `pas_ensemble_cardinaux|ensemble_de_tous_les_cardinaux|aucun_ensemble_cardinal` |
| 31 | Ch.III p.139 | Cor.4 𝔓(fini) est fini | `parties_fini_est_fini|powerset_fini|parties_ensemble_fini` |
| 32 | Ch.III p.139 | Cor.1/2 réunion & produit finis | `reunion_famille_finie_est_finie|produit_famille_finie_est_fini` |
| 34 | Ch.III p.152 | Cor.2/3/4 de a²=a | `cor[234]_\w*(hessenberg|puissance|denombrable)` |
| 36 | Ch.III p.167 | Prop.7 limite inductive | `prop7_\w*induct|induct\w*_prop7` |

## DÉJÀ UNE `def` — à NE PAS réécrire sans vérifier (20)

| # | chapitre | cible | `def` trouvée | fichier |
|---|---|---|---|---|
| 1 | Ch.I p.25 | ex falso quodlibet | `_ex_falso` | ensembles_ordre_treillis_props.py |
| 2 | Ch.I p.31 | assoc. de « ou » (C24) | `_assoc_ou` | ensembles_algebre_booleenne.py |
| 5 | Ch.I p.40 | équation / solution complète | `equation_au_point` | ensembles_c60_final.py |
| 9 | Ch.II p.66 | prolonge ses restrictions | `prolongement_un_point_dans_produit` | ensembles_produit_adjonction_briques.py |
| 10 | Ch.II p.66 | élément invariant par f | `est_invariant` | ensembles_abrege.py |
| 11 | Ch.II p.75 | monotonie ⋃/⋂ indices fixes | `monotonie_reunion_famille` | ensembles_familles.py |
| 13 | Ch.II p.78 | trace de X sur A | `trace` | ensembles_trace.py |
| 14 | Ch.II p.80 | Déf.7 partition | `est_partition` | ensembles_abrege.py |
| 15 | Ch.II p.85 | Cor.1 pr_α surjective | `prop3_surjection_inf_egal` | ensembles_prop3_prop4cor_iii3.py |
| 16 | Ch.II p.89 | (⋂X)×(⋂Y)=⋂(X×Y) | `produit_inter_egal_inter_produits` | ensembles_produit_inter_ii5.py |
| 17 | Ch.II p.90 | ∏(X^E) ≅ (∏X)^E | `diagonale` | ensembles_abrege.py |
| 20 | Ch.II p.94 | saturée ⇔ réunion de classes | `famille_de_saturees_reunion` | ensembles_saturees_famille.py |
| 23 | Ch.II p.96 | h injective / k canonique (R_A) | `H_injective` | ensembles_parties_equipotentes.py |
| 24 | Ch.II p.96 | classes de l'image réciproque | `image_reciproque_relation` | ensembles_quotient_complements.py |
| 25 | Ch.II p.97 | (E/S)/(R/S) ≅ E/R | `relation_quotient_RS` | ensembles_decomposition_quotient.py |
| 27 | Ch.III p.124 | Cor.2 de Zorn (stable par réunion) | `cor2_maximal` | ensembles_ordre_fini_iii4.py |
| 33 | Ch.III p.142 | partie entière du quotient | `partie_entiere_quotient` | ensembles_entiers_notions_arith.py |
| 35 | Ch.III p.154 | Prop.7 récurrence nœthérienne | `est_noetherien` | ensembles_infinis.py |
| 37 | Ch.IV p.207 | espèce de structure / transportable | `relation_transportable_instance` | ensembles_especes_typification.py |
| 38 | Ch.IV p.216 | plus fine / moins fine | `plus_fine` | ensembles_abrege.py |

## PARTIELLES — sujet touché, pas de `def` au nom attendu (1)

| # | chapitre | cible | fichiers touchés |
|---|---|---|---|
| 6 | Ch.II p.54 | Coll_x R (déf.) | 5 |
