# `recherche/` — les résultats qui ne sont PAS dans le livre

## Pourquoi ce dossier existe

`bourbaki/` **calque la table des matières du livre** : c'est ce qui fait de
l'arborescence un détecteur de trous — un dossier vide = un résultat de
Bourbaki pas encore formalisé. Y déposer un théorème absent du livre casserait
ce mécanisme et fausserait tous les rapports de couverture.

Or la conjecture de Goldbach n'est pas dans *Théorie des ensembles*. Les
résultats produits par le projet **au-delà du livre** vivent donc ici.

## La règle de partage

| | `bourbaki/` | `recherche/` |
|---|---|---|
| contenu | ce que Bourbaki démontre | ce que le projet démontre en plus |
| marqueur | `@livre` obligatoire (page + lignes) | **pas** de `@livre` — rien à caler |
| arborescence | calque la table des matières | par sujet |
| couverture | comptabilisée dans `LIVRE.md` | hors comptage |

**Ce qui ne change pas** : la frontière de confiance. Tout `Theoreme` d'ici est
produit par les **mêmes primitives du noyau**, sans `_CLE`, sans monkeypatch,
et `theorie_ensembles()` vaut **22 axiomes** à chaque exécution. Un résultat de
recherche n'est pas moins certifié — il est seulement hors-livre.

## Contenu

- **`goldbach/`** — la carte machine de la conjecture de Goldbach : réductions
  et équivalences certifiées. La conjecture **reste ouverte** ; ce qui est
  acquis, ce sont les réductions. Vue d'ensemble :
  `docs/articles/CARTE_GOLDBACH.md`.

  | module | ce qu'il porte |
  |---|---|
  | `enonces.py` | le socle : prélèvements **vérifiés par recomposition**, et `atteste` |
  | `crible.py` | `P₂ₖ`, son miroir `Q₂ₖ`, et l'équivalence crible ⟺ décomposition gardée |
  | `pont_tau.py` | Goldbach **sans quantificateur existentiel**, et les familles de témoins |
  | `composes.py` | Goldbach ⟺ sa restriction aux `k` **composés** (les `k` premiers sont gratuits) |
  | `synthese.py` | ⊢ [ ∀k composé, rencontre(k) ] ⇒ Goldbach — le point de convergence |
  | `symetrie.py` | les solutions vont **par paires**, `m ↦ 2k − m` |
  | `demi.py` | de chaque paire l'un est `≤ k` ⇒ chercher dans **la moitié** suffit |
  | `audit_fidelite.py` | le théorème de **défaut** de `est_premier` (soundness ≠ fidélité) |
  | `capstone.py` | rejeu des 18 maillons, **jugés par le noyau** |

  ⚠️ **Le dossier est à 10 entrées — la limite.** Le prochain ajout impose
  d'éclater en sous-dossiers par thème (`equivalences/`, `structure/`,
  `audit/`), conformément à la convention du projet. Ne pas y déposer un
  onzième fichier « juste cette fois ».

## Statut

Ce dossier consomme `bourbaki/` (il en importe les théorèmes) et
`outils_ia/` (numéraux, primalité, organe de besoin). L'inverse est
**interdit** : rien dans `bourbaki/` ne doit dépendre de `recherche/`.

## Deux gardes propres à ce dossier

**« clos » ne veut pas dire « sans axiome ».** `N.axiome(theorie, f)` rend un
théorème dont `hypotheses` est vide : `est_clos` est donc vrai même pour un
résultat qui repose entièrement sur une théorie dédiée. Le crible en a deux
(`AXIOMES_CRIBLE`). Chaque fonction concernée passe par `atteste(th,
axiomes=…)`, et le capstone porte une colonne dédiée. **Confondre les deux
serait la seule tricherie réellement possible ici.**

**Un test garde la porte.** `test_goldbach_reste_ouverte` balaie tous les
exports et échoue si l'un d'eux conclut `H` — la conjecture — tout seul. Tout
ce que ce dossier produit doit rester de la forme « X ⇒ Goldbach » ou
« Goldbach ⟺ Y ». Si un jour ce test tombe, ce n'est pas une bonne nouvelle à
publier : c'est un énoncé à auditer immédiatement.
