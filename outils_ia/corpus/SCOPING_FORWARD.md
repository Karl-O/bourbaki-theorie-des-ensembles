# Scoping — GÉNÉRATION FORWARD (découvrir des faits nouveaux, pas 39-40, PROBE-FIRST)

Question : la génération FORWARD (appliquer des tactiques aux faits dispo → nouveaux faits
kernel-validés, sans oracle tenu à l'écart) échappe-t-elle au mur de données de la régénération ?
C'est le vrai but « créer des théories ». **Probes seulement, aucun gros run.**

## Mécanique vérifiée

`_statut` exec le src dans `ns = dict(mod.__dict__)` (tactiques + objets dispo) → `ns[name]()` renvoie un
`Theoreme` (`.conclusion : Formule`, `.hypotheses : frozenset`, `.est_clos`, `.justification`). Tout
`Theoreme` produit par les primitives/tactiques est **valide par construction** (frontière de confiance).
Donc « forward » = appliquer des tactiques aux faits dispo → nouveaux Theoremes valides. Le noyau juge la
VALIDITÉ ; il ne juge pas l'« intérêt ».

## Probe A (pas 39) — tactique RECOMBINANTE : `conjonction_intro`

Seeds = les 2 théorèmes prouvés du module identite_neutre. 1 pas forward :

| tactique | résultats valides | dont triviaux (recombinaison) | dont contenu NOUVEAU |
|---|---|---|---|
| `conjonction_intro` (binaire, paires) | **4** (= P²) | 4 (tous = `A∧B` de connus) | **0** |

→ Les tactiques **recombinantes** (`conjonction_intro`, `∨-intro`, `symetrie`) **FIRENT abondamment**
(branchement P² par tactique binaire, P croissant) mais produisent **100 % de trivialités** (`A∧B`,
`sym(A)`, `A∨B` de faits connus) : valides, 0 contenu mathématique nouveau.

> ⚠️ **Correction (pas 40) de la conclusion de pas 39** : pas 39 n'avait testé QUE `conjonction_intro`
> (la tactique trivialement recombinante) et avait conclu « forward erre/trivial ». C'était le bon
> *verdict* mais sur un *seul cas* — incomplet. Pas 40 le complète avec les tactiques **productrices de
> contenu**, et trouve un fait STRUCTUREL encore plus fort (ci-dessous).

## Probe B (pas 40) — tactiques PRODUCTRICES DE CONTENU (type-matching strict)

`proto_forward_probe.py`. Seeds = **150 théorèmes CLOS prouvés** de `logique` + `ensembles` (97 modules ;
ordre/structures écartés : proofs lourdes). Parmi eux : **37 égalités, 35 équivalences, 47 implications**.
1 pas forward avec les tactiques de contenu (le maillon central / l'antécédent doit COÏNCIDER) :

| tactique de contenu | pool | attempts (paires) | **feasible** (type-match) | success | NON-TRIV |
|---|---|---|---|---|---|
| `composer_egalites` (T=U, U=V → T=V) | 37 | 1332 | **0** | 0 | 0 |
| `equivalence_transitivite` (A⇔B,B⇔C → A⇔C) | 35 | 1190 | **0** | 0 | 0 |
| `modus_ponens` (R, R⇒S → S) | 47 | 7050 | **0** | 0 | 0 |

**Sur la bibliothèque des théorèmes clos, les tactiques de contenu ne FIRENT PAS DU TOUT** (feasible=0).
Diagnostic (`--diag`, structurel — vérifié, pas un bug de détecteur) :

- **`composer_egalites`** : sur 37 égalités, l'ensemble des **membres-droits ∩ membres-gauches = 0**.
  La bibliothèque prouve des **réductions** `terme_complexe = terme_simple`
  (`dom(reciproque(G))=img(G)`, `reciproque(produit(X,Y))=produit(Y,X)`, …) ; les membres-droits simples
  (`img(G)`, `A`…) **ne reparaissent jamais** comme membre-gauche d'une autre identité, et les variables
  libres diffèrent (`G`/`Gp`/`Y`/`G3`). **Aucune paire ne chaîne.**
- **`modus_ponens`** : sur 47 implications, **antécédents ∩ conclusions-prouvées = 0**. Les antécédents
  sont des **conditions à ASSUMER** (`z∈produit(…)`, `Ap≠Bp`, `(∃x)…`), pas des faits déjà clos. MP ne
  trouve jamais sa mineure. Idem `equivalence_transitivite` (maillon ⇔ central jamais partagé).

> Le probe matche les termes **littéralement** (pas d'unification). Introduire une unification pour
> *fabriquer* des paires chaînables, c'est introduire une RECHERCHE — guidée par un but (dirigée) ou par
> une heuristique d'intérêt (apprise). C'est exactement le guidage dont on teste la nécessité : le probe
> mesure donc fidèlement si les faits du corpus chaînent « tels quels ». Ils ne chaînent pas.

## Probe C (pas 41) — CONTRÔLE POSITIF : les mêmes tactiques FIRENT, guidées par un but

Le négatif (feasible=0) n'est rigoureux que confronté à un **positif** : les mêmes tactiques de contenu
FIRENT-elles dans le contexte LOCAL d'une vraie preuve, où le but met en place les termes partagés ?
`proto_forward_positif.py` — (A) parse AST statique de **621 fichiers** `bourbaki/` (pas d'exécution → ne
pend pas sur cardinaux ; pas de monkeypatch) ; (B) exécution légère de proofs `ensembles`.

**(A) Call-sites de tactiques de contenu (le corpus en réalise massivement) :**

| tactique de contenu | appels | nature |
|---|---|---|
| `composer_egalites` (= transitive) | **701** | dont **114 IMBRIQUÉS** (chaînes multi-maillons `c(c(a,b),d)`) |
| `equivalence_transitivite` | 400 | chaînage ⇔ |
| `syllogisme` (R⇒S, S⇒T → R⇒T) | 299 | chaînage ⇒ |
| `congruence_terme` (T=U → V{T}=V{U}) | 265 | substitutivité = |
| `instancie` (∀x R → (T\|x)R) | 3498 | ∀-élimination (instancie un universel) |
| `equivalence_avant` (A⇔B → A⇒B) | 1516 | décomposition (brique, ≠ chaînage pur) |

Chaînage de contenu STRICT (transitivité =/⇔, syllogisme, congruence) = **1665 appels** ; + `instancie`
3498. Par chapitre : cardinaux 3418, ensembles 1493, ordre 964, entiers 651, logique 90, structures 63.

**(B) Exécution live (preuve renvoie un `Theoreme` valide ⟹ tous ses appels de contenu ont FIRÉ) :**
6 proofs `ensembles` exécutées, **100 % `FIRE ✓`**, 22 appels de contenu firés in-context. Ex. :
`prop9b_factorisation_valeur` = `instancie×1 + congruence_terme×2 + composer_egalites×2` → `=`-Theoreme
valide ; `image_composee_membre` = `equivalence_transitivite×6` → Theoreme valide. **Ce sont les MÊMES
modules `ensembles`** dont les théorèmes CLOS EXPORTÉS ne chaînaient pas (feasible=0, pas 40) : en
interne, leurs preuves chaînent abondamment car le but a monté le contexte à termes-partagés.

**LE CONTRASTE (cœur du contrôle positif) :**

| régime | `composer_egalites` | fire-rate |
|---|---|---|
| bibliothèque DÉCONNECTÉE (faits clos, pas 40) | 0 / 1332 paires | **0 %** |
| contexte DIRIGÉ-PAR-BUT (vraies preuves, pas 41) | 701 appels (114 chaînes) | **100 %** (chaque appel exige la coïncidence du maillon, fournie par le but) |

→ `feasible=0` n'est **PAS un artefact d'outillage** mais une propriété STRUCTURELLE : la même tactique
fire **0× déconnectée, 100 % guidée**. **Le guidage ≡ le contexte à termes-partagés que le but induit.**

## Verdict (NUANCÉ, 2 régimes de tactiques + contrôle positif)

La génération forward **non-guidée** se scinde en deux régimes, et AUCUN ne découvre de contenu :

1. **Tactiques RECOMBINANTES** (conjonction/disjonction/symétrie) : firent en P² mais sortie **100 %
   triviale** (recombinaisons de connus). Le noyau valide tout ; zéro intérêt.
2. **Tactiques de CONTENU** (transitivité =/⇔, modus ponens) : produiraient du non-trivial, mais sur la
   bibliothèque des 150 théorèmes clos elles **firent 0 fois** — les faits sont des résultats nommés
   INDÉPENDANTS qui ne partagent ni maillon (=) ni antécédent (⇒). Le chaînage de contenu exige un
   **contexte de travail** de faits mutuellement reliés (mêmes termes) — ce qui n'existe que dans un
   **état de preuve dirigé vers un but** (hypothèses partagées) = la régénération oracle-dirigée DÉJÀ
   étudiée, ou une recherche par unification (= guidage).

→ **Découvrir des faits NON-TRIVIAUX exige un GUIDAGE** (un BUT qui met en place le contexte à termes
partagés, ou une fonction-VALEUR d'« intérêt » apprise pour choisir QUELS contextes monter). La fonction
d'intérêt est une politique apprise → **data-limitée** (le mur de données). Conclusion confirmée
**mécaniquement** (pas seulement « ça erre ») : la génération forward **n'échappe PAS** à la contrainte de
corpus, et le probe pas-40 **résout** l'inquiétude « conclusion trop hâtive » de pas 39.

## CONSTAT MÉTA FINAL (3 frames indépendants — méta-algo in-scope bouclé)

La contrainte liante de TOUT le méta-algo in-scope est la **TAILLE / DIVERSITÉ DU CORPUS** :
1. **régénération de TERMES** (pas 28-32) : effet miroir = mur de données d'arrangement ;
2. **régénération de TACTIQUES** (pas 38) : classifieur `fn` 18 % top-1 = baseline (sparsité 71 classes) ;
3. **génération FORWARD** (pas 39-41) : recombinant → trivial ; contenu → ne fire pas sur la biblio des
   faits clos (réductions indépendantes) ; **contrôle positif** : les mêmes tactiques firent 6679× dans
   les vraies preuves (guidées par un but) → le guidage ≡ contexte à termes-partagés → valeur d'intérêt
   apprise → **data-limité**. Frame forward DÉMONTRÉ complet (négatif feasible=0 + positif 6679 firings).

**Acquis solide** : generate-and-verify MARCHE (régénération end-to-end 27→41 %, kernel-validé). **Cure
unique et HORS boucle outils_ia** : agrandir le corpus = **formaliser plus de preuves dans `bourbaki/`**
(le projet principal). Le méta-algo in-scope (outils_ia) est **exhaustivement bouclé** sur 3 frames ; il
fournit le substrat appris (TreeNN, grammaire, e2e, cible) prêt à payer dès que le corpus grandit.

**Probe-first a, ici encore (8ᵉ fois), payé** : tester les tactiques de contenu AVANT de conclure a
remplacé un verdict hâtif (« forward trivial », 1 tactique) par un fait structurel mesuré (feasible=0 sur
150 faits), et a évité de construire un mini-explorateur forward voué à ne rien firer sans guidage.
