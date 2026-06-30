# Scoping arc (2) — génération au niveau TACTIQUE (pas 38, PROBE-FIRST)

Question : après le pivot term-synthesis (qui remplit les term-args d'un squelette-macro, fn connue),
passer au niveau TACTIQUE = **prédire le PAS-TACTIQUE entier** (la fonction `fn` appelée **+** ses args),
étant donné le contexte de preuve, noyau validant. Espoir initial : le corpus a plus de pas-tactiques
que de term-slots → peut-être DÉPASSER le mur de données. **Probes seulement, aucun gros run.**

## Structure du corpus au niveau tactique (9 modules)

| mesure | valeur |
|---|---|
| preuves | 24 |
| pas-tactiques | 350 |
| **tactiques DISTINCTES** | **71** |
| tactiques bien peuplées (≥5 occ.) | 19 / 71 |
| **hapax (1 seule occ.)** | **30 / 71** |
| top tactiques | `modus_ponens` 65, `assume` 35, `loi_deduction` 23, `et` 15, `conjonction_elim_*` 12, `var`/`appartient`/`generalisation`/`existe_elimination` 10 |

## Tâche envisagée & machinerie réutilisable

« Régénérer un pas-tactique tenu à l'écart » = (1) **prédire `fn`** (classification sur 71 tactiques,
depuis le contexte : tactiques précédentes + data-flow) ; (2) **synthétiser les args** (le TreeNN
term-synthesis EXISTANT) ; (3) **vérifier au noyau** (oracle GRATUIT = le vrai pas de la preuve).
Machinerie réutilisable : `_proofs`/`sigs` (signatures (fn, n_args)), `repair_learned` (data-flow),
le TreeNN pour les args. La SEULE brique NOUVELLE = le classifieur `fn`.

## Verdict de faisabilité (la brique `fn` ne généralise PAS)

Probe décisif — classifieur `fn` (LogReg, contexte prev/prev2/position, **GroupKFold par preuve**) :

| prédiction `fn` | top-1 | top-5 |
|---|---|---|
| baseline marginale (toujours `modus_ponens`) | 18 % | — |
| bigramme top-1 (IN-SAMPLE, optimiste) | 47 % | — |
| **classifieur appris (CROSS-VALIDÉ)** | **18 %** | 50 % |

→ **Le classifieur cross-validé n'égale que la baseline marginale (18 % top-1)** : le contexte ne
prédit PAS la tactique suivante sur des preuves tenues à l'écart. Le 47 % bigramme était du SUR-AJUSTEMENT
in-sample. Signal faible existant (top-5 50 % ≫ aléatoire 7 %), mais top-1 nul.

**Cause = MÊME MUR DE DONNÉES** : 71 classes / 30 hapax / 350 pas / 24 preuves → trop peu d'exemples par
tactique pour généraliser. Le niveau tactique a PLUS de pas bruts mais PLUS de classes et PLUS de
parcimonie → la donnée par-classe n'est pas meilleure, et la généralisation échoue (18 % = baseline).

## Conclusion & recommandation

- **Arc (2) est structurellement faisable** (fn + args + noyau, oracle gratuit) MAIS **bute sur le même
  mur de données** que term-synthesis — le construire reproduirait le diagnostic « verrou de données » à
  un nouveau niveau. **Non prioritaire avant d'agrandir le corpus.**
- **Constat MÉTA (le plus important)** : la contrainte liante de TOUT le méta-algo est la **TAILLE DU
  CORPUS**, confirmée sur DEUX frames indépendants (term-arrangement pas 28-32 ; tactique pas 38). La cure
  est unique et HORS boucle outils_ia : **FORMALISER PLUS DE PREUVES** dans `bourbaki/` (le projet
  principal). Avec un corpus plus grand, et le classifieur `fn` ET le TreeNN args ET la cible (codée en
  pas 32, en historique git) redeviendraient des leviers payants.
- Arc (3) GFlowNet/diffusion DAG = encore plus data-hungry → même verdict a fortiori.

**Probe-first a, ici encore (7ᵉ fois), évité de construire une grosse brique vouée au mur de données.**
