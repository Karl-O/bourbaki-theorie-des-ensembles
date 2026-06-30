# Scoping — GÉNÉRATION FORWARD (découvrir des faits nouveaux, pas 39, PROBE-FIRST)

Question : la génération FORWARD (appliquer des tactiques aux prémisses → nouveaux faits kernel-validés,
sans oracle tenu à l'écart) échappe-t-elle au mur de données de la régénération ? C'est le vrai but
« créer des théories ». **Probes seulement.**

## Mécanique vérifiée

`_statut` exec le src dans `ns = dict(mod.__dict__)` (tactiques + objets dispo) → `ns[name]()` renvoie un
`Theoreme` (`.conclusion : Formule`, `.hypotheses : frozenset`, `.est_clos`, `.justification`). Tout
`Theoreme` produit par les primitives/tactiques est **valide par construction** (frontière de confiance).
Donc « forward » = appliquer des tactiques aux faits dispo → nouveaux Theoremes valides.

## Probe : branchement & trivialité d'un pas forward

Seeds = les **2 théorèmes prouvés** du module identite_neutre (faits valides connus). 1 pas forward :

| tactique | résultats valides | dont triviaux (recombinaison de connus) | dont contenu NOUVEAU |
|---|---|---|---|
| `conjonction_intro` (binaire, paires) | **4** (= P²) | 4 (tous = `A∧B` de faits connus) | **0** |

→ Tous les faits « nouveaux » sont des **CONJONCTIONS `A∧B`** (ou `sym(A)`, `A∨B`…) de faits déjà connus :
**valides mais 0 contenu mathématique nouveau**, et le branchement est **P² par tactique binaire** (P =
nb de faits dispo, qui CROÎT à chaque pas). Avec ~71 tactiques et P grandissant, le branchement explose
et est **dominé par des recombinaisons triviales**.

## Verdict

- **Forward NON-GUIDÉ ERRE** (semi-décidable) : branchement combinatoire (P²·#tactiques), sortie dominée
  par des faits valides TRIVIAUX (conjonctions/symétries/disjonctions de connus). Le noyau valide tout
  mais l'« intérêt » n'est pas capturé → c'est le problème classique de l'ATP forward.
- **Découvrir des faits NON-TRIVIAUX exige un GUIDAGE** : soit un BUT (→ proof search dirigé, = la
  régénération déjà faite, oracle-dirigée), soit une fonction-VALEUR d'« intérêt » APPRISE → qui est le
  problème de politique apprise **data-limité** (le mur de données, 3ᵉ confirmation).
- → la génération forward **n'échappe PAS** à la contrainte de corpus.

## CONSTAT MÉTA FINAL (3 frames indépendants)

La contrainte liante de TOUT le méta-algo in-scope est la **TAILLE / DIVERSITÉ DU CORPUS**, confirmée sur
**3 frames** :
1. **régénération de TERMES** (pas 28-32) : effet miroir = mur de données d'arrangement ;
2. **régénération de TACTIQUES** (pas 38) : classifieur `fn` 18 % top-1 = baseline (sparsité 71 classes) ;
3. **génération FORWARD** (pas 39) : sans guidage → erre/trivial ; avec guidage appris → data-limité.

**Acquis solide** : generate-and-verify MARCHE (régénération end-to-end 27→41 %, kernel-validé). **Cure
unique et HORS boucle outils_ia** : agrandir le corpus = **formaliser plus de preuves dans `bourbaki/`**
(le projet principal). Le méta-algo in-scope (outils_ia) est **exhaustivement bouclé** ; il fournit le
substrat appris (TreeNN, grammaire, e2e, cible) prêt à payer dès que le corpus grandit.
