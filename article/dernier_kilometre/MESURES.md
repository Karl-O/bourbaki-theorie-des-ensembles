# A2 — les mesures, refaites le 20 août 2026

**Pourquoi ce document.** `ORGANES.md` et `PIEGES_MESURES.md` datent des 10–12 août.
Avant d'en tirer une seule phrase d'article, tout a été re-mesuré. **Huit chiffres sur
huit avaient dérivé.** C'est ce document, et non le matériau, qui fait foi pour A2.

Commande unique, exécution complète :

```bash
python -m pytest outils_ia/decouvertes/ tests/outils_ia/corpus/ -q --durations=0
```

---

## 1. La suite : 42 passed en 32 min 50, exit 0

Lu sur la **dernière ligne** du fichier de sortie, pas sur une notification.

| fichier | tests |
|---|---:|
| `outils_ia/decouvertes/test_autonomie.py` | 20 |
| `outils_ia/decouvertes/autonomie/test_general.py` | 9 |
| `outils_ia/decouvertes/test_lemmes_algebre.py` | 1 |
| `outils_ia/decouvertes/test_lemmes_decouverts.py` | 1 |
| `tests/outils_ia/corpus/test_analogie_preuves.py` (v21) | 8 |
| `tests/outils_ia/corpus/test_notions_candidates.py` (v20) | 3 |
| **total** | **42** |

Le dossier `outils_ia/decouvertes/` seul en compte donc **31**, là où le document en
annonçait 24.

---

## 2. Ce qui a dérivé — huit écarts

| ce que le matériau dit | ce qui est mesuré | nature de l'écart |
|---|---|---|
| 15 tests dans `test_autonomie.py` | **20** | des tests ont été ajoutés, le document n'a pas suivi |
| 24 passed dans `decouvertes/`, 40 min | **31** passed ; 42 avec `corpus/`, **32 min 50** | idem, et c'est plus RAPIDE qu'annoncé |
| catalogue de « dix-neuf lignes » | **21** organes | le document se contredit lui-même |
| `besoin.py` à 259 lignes | **387** | +128 lignes |
| **v3** « fusionner les manques de la voie directe » | **aucune trace en code** | absorbé ou supprimé, jamais consigné |
| v16 : **0,29 s** | **1,75 s** | ⚠️ voir la réserve ci-dessous |
| v18 : **8 s** | **16,43 s** | ⚠️ idem |
| v15 : **102 s → 0 s** | test entier en **2,87 s** | ⚠️ le 102 s n'est pas reproductible tel quel |

### ⚠️ Réserve sur les trois derniers : on ne compare pas la même chose

`--durations` mesure **le test entier** — imports, construction du pool, les deux passes
— tandis que les chiffres du document mesuraient vraisemblablement **l'appel de l'organe
seul**. Les deux séries ne sont donc pas comparables, et il serait malhonnête d'écrire
« le document se trompait ».

Ce qui est établi, en revanche, et suffit à l'article :

- **v16 ferme la commutativité de `⊕` en moins de 2 s**, v17 la chaîne de réécritures en
  **3,40 s**, et **v18 l'associativité en 16,43 s** — le tout depuis deux lois brutes ;
- **v15 boucle ses deux passes en 2,87 s au total**, ce qui rend le « 102 s » du document
  impossible à obtenir dans la configuration actuelle : soit le test a changé, soit la
  mesure portait sur un autre réglage. **Le compounding reste vrai** (le test l'asserte),
  mais son AMPLEUR n'est pas celle annoncée.

**Conséquence pour l'article** : citer les durées de test, dire qu'elles incluent le
décor, et ne PAS réutiliser les chiffres du document. Un rapport de 102/0 ferait un bel
effet ; il n'est pas soutenu par ce qui tourne aujourd'hui.

---

## 3. Les durées qui comptent (extraits de `--durations=0`)

| test | durée |
|---|---:|
| `test_euclide_infinitude` | **1 361,87 s** (22 min 42) |
| `test_briques_euclide_cas_premier_et_transitivite` | 275,72 s |
| `test_diviseur_premier_universel` | 187,66 s |
| `test_fermeture_autonome_miniature` | 53,34 s |
| **`test_organe_v18_associativite_d_une_operation_derivee`** | **16,43 s** |
| `test_la_machine_retrouve_les_notions_posees_a_la_main` (v20) | 15,87 s |
| `test_organes_v6v7v8_integration_goldbach` | 6,47 s |
| `test_besoin_ferme_et_nomme_ses_manques` | 4,48 s |
| **`test_organe_v17_chaine_de_reecritures`** | **3,40 s** |
| **`test_organe_v15_compounding_du_proposeur_appris`** | **2,87 s** |
| **`test_organe_v16_congruence_automatique`** | **1,75 s** |
| `test_organe_v19_oracle_refute_avant_de_chercher` | 1,71 s |

Un seul test consomme **69 %** du temps total de la suite. C'est un fait d'ingénierie
utile en soi : la protection des organes coûte quelques secondes, c'est la
démonstration d'Euclide qui coûte cher.

---

## 4. Ce qui N'A PAS pu être re-mesuré

- **La courbe des manques (14 → 8 → 6 → 4 → 1).** Elle vient d'un journal de session et
  aucun script ne la rejoue. Elle était prévue comme figure centrale de A2 :
  **elle ne sera pas tracée**. Une courbe qu'on ne peut pas reproduire n'a pas sa place
  dans un article dont la thèse est qu'on mesure au lieu de décréter.
- **Le facteur 100 de la loi des termes (333 s → 3 s)** et **le rapport 24×** du palier
  v16–v18 : tous deux issus du journal, non rejoués ici. À citer comme mesures d'époque,
  datées, ou à refaire — pas à présenter comme des mesures d'aujourd'hui.

---

## 5. Invariants, vérifiés

`theorie_ensembles()` = 22 · 0 SyntaxError · 0 marqueur non conforme
(`python outils_ia/audit/verifie.py`).
