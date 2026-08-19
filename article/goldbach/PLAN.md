# ARTICLE A3 — plan de campagne (ouvert le 19 août 2026)

**Cible** : preprint arXiv (cs.LO / math.LO), puis AITP ou CICM. **Langue : anglais**
(décision reprise de `article/PLAN.md`, 2 août) ; traduction française de travail ensuite.

**Titre de travail** : *Charting the Open: Certified Reductions of Goldbach's Conjecture,
and a Measurement of What They Do Not Contain.*

**Position dans le plan éditorial** (`docs/articles/PLAN_ARTICLES.md`, 10 août) : c'est
**A3**, « Face à l'ouvert ». Question unique : *que peut produire une IA vérifiée sur un
problème ouvert, où la réussite est exclue d'avance ?*

## La règle d'or (reprise de A1)

**Chaque phrase de l'article doit être adossée à un objet du dépôt.** Une affirmation
sans ancre = une docstring qui ment, en public. Le tableau ci-dessous EST l'article.

## ⚠️ Rapport à l'article A1 (`article/main.tex`)

A1 contient déjà **§6.2 « Second case study: an open statement under instrumentation »**
(~120 lignes), qui couvre l'arc Goldbach **jusqu'au 5–6 août** : les deux défauts
d'énoncé, l'équivalence « moitiés », la dette en trois nombres, le conjectureur
(60 théorèmes), l'abstraction sélective (`even(6)`), le volant wake-sleep (4 → 18
notions).

**A3 ne réécrit pas §6.2 : il commence où elle s'arrête.** Tout le contenu ci-dessous
est postérieur au 10 août. Règle de partage à tenir à la rédaction :

| va dans A1 §6.2 | va dans A3 |
|---|---|
| la dette en 3 nombres (0/14/53, 0/14/73) | la carte, GG19–GG25, la synthèse GG24 |
| le conjectureur, l'abstraction sélective | la symétrie, le demi-intervalle |
| le volant wake-sleep | **le crible abstrait** (le résultat central) |
| les 2 défauts d'énoncé de l'énoncé pair | le défaut `est_premier` et sa réparation |

À la soumission de A3, **§6.2 de A1 doit être réduite** à un paragraphe qui renvoie à
A3, sinon les deux articles se recouvrent et aucun des deux ne tient seul.

## Table des revendications (claim → preuve → statut)

| # | revendication | preuve dans le dépôt | statut |
|---|---|---|---|
| **G1** | Une **carte certifiée** d'un problème ouvert : 18 maillons jugés par le noyau, rejoués en processus frais, invariant 22 partout | `recherche/goldbach/capstone.py::verifie_chaine` — **18/18 CLOS**, `theorie_ensembles()`=22, ~7 min 30 | ✅ **mesuré le 19 août** |
| **G2** | La conjecture réduite à **un seul objet** : les trois lignes du projet (bornée `n≤86`, composés, crible) convergent sur la rencontre | `synthese.py::composes_impliquent_goldbach` (GG24) ; absorption par GG25 / GG22 | ✅ clos (2 ax. ad hoc) |
| **G3** | **Goldbach sans `∃`** : chez Bourbaki `∃x φ(x)` *est* `φ(τx φ)` ; la conjecture devient trois propriétés de deux termes nommés | `pont_tau.py::forme_canonique` (GG9/GG10) ; primitives `existe_temoin`, `s5` (E I.32) | ✅ clos, 0 ax. ad hoc |
| **G4** | 🎯 **LE RÉSULTAT CENTRAL — les réductions ne contiennent aucune arithmétique.** La *même preuve*, `S` en paramètre, ferme sur un prédicat totalement opaque, sur la primalité (= Goldbach) et sur un prédicat trivial | **les 4 réductions** : `equivalence_abstraite.py::equivalence_abstraite` (GG19 ⇐ et ⇒), `::rencontre_des_elements` (GG22), `crible_abstrait.py::symetrie_additive`, `demi_abstrait.py::restriction_a_la_moitie` ; `tests/recherche/additif/` **13 tests verts, 5 min 53** | ✅ **COMPLET (19 août)** — voir l'historique ci-dessous |
| **G5** | **Deux voies refermées PAR LA NÉGATIVE**, pour la même raison : le comptage brut (tiroirs `2·π(2k) > 2k+1` faux pour tout `k≥2`) et l'équationnel (après les organes v16–v18, le manque a une forme *strictement identique*) | `CARTE_GOLDBACH.md` §7 et §8 ; `RESONDE1_goldbach_v18.py` | ✅ mesuré (numérique pour §7 — **pas une preuve**) |
| **G6** | Un **défaut de fidélité certifié**, puis réparé : `est_premier(p)` ne contraint pas `p` à être un entier, donc `goldbach()` est *plus faible* que la conjecture ; la garde `premier_ent := Fini ∧ est_premier` est **gratuite sur les numéraux** | `audit_fidelite.py::indivisible_implique_premier` ; maillon A2 du capstone (50 s) | ✅ clos, 0 ax. ad hoc |
| **G7** | Deux **faits de structure** sur la rencontre : les solutions vont par paires (involution `m ↦ 2k−m`, point fixe `k`) ; et **la moitié suffit** (`m ≤ k` ou `m' ≤ k`) | `symetrie.py::symetrie_du_crible` (GG23) ; `demi.py::demi_intervalle`, `rencontre_se_restreint` | ✅ clos |
| **G8** | **« Clos » ≠ « sans axiome »** — et le dépôt le dit lui-même : 11 maillons sur 18 sont libres, 7 reposent sur les 2 axiomes du crible ; `atteste()` porte la colonne | `recherche/README.md` ; `AXIOMES_CRIBLE` ; colonne du capstone | ✅ mesuré |
| **G9** | Un **test garde la porte** : il balaie tous les exports et échoue si l'un conclut `H` tout seul. Si ce test tombe, ce n'est pas une bonne nouvelle — c'est un énoncé à auditer | `test_goldbach_reste_ouverte` | ✅ en place |

## L'historique de G4 — une surdéclaration trouvée, puis refermée (19 août)

**Ce document a d'abord porté une réserve, et elle est devenue une section de
l'article** (§5.3, `sec:overclaim`). Le récit vaut d'être gardé ici parce qu'il est
l'argument le plus concret du papier.

**L'écart.** `CARTE_GOLDBACH.md` §12 et la docstring de `demi_abstrait.py` écrivaient,
depuis le 12 août : « les **quatre** grandes réductions ne portent aucun contenu
arithmétique ». Le code n'en établissait que **deux** — symétrie et demi-intervalle.
Ni GG19 ni GG22 n'existaient sous forme paramétrique (`grep` sur `recherche/additif/` :
aucune occurrence de `composes` ni de `equivalence_crible`). L'affirmation était en
route vers la section centrale de l'article.

**La détection.** Le 19 août, en relisant le code contre notre propre prose pendant la
rédaction de A3. **Aucun test ne pouvait l'attraper** : le noyau garantit la soundness,
jamais la fidélité d'un commentaire. C'est le même défaut que G6, un cran plus haut —
là l'énoncé formel dérivait du livre, ici l'affirmation informelle dérivait de l'énoncé
formel.

**La fermeture, le jour même.** `recherche/additif/equivalence_abstraite.py` — GG19 les
deux sens + GG22, clos sur les trois prédicats, 13 tests verts en 5 min 53. Le portage
s'est révélé **mécanique** : les preuves concrètes ne se servent de la primalité que
comme d'un conjoint opaque, jamais ouvert. *Il n'y avait rien d'arithmétique à porter*
— ce qui est la thèse même de G4, sous une forme plus nette que prévu.

**Un gain de généralité au passage** : l'équivalence abstraite vaut pour un `b`
QUELCONQUE, alors que la version du dépôt est écrite sur `b = 2k` sans jamais utiliser
que `b` est un double. Seul GG22 en a besoin, et seulement pour une réflexivité.

**Ce qui reste non mesuré, et qui est écrit aux Limitations** : « les quatre grandes
réductions » est notre jugement de ce qui porte la charge. Les maillons plus petits
(pont τ, arc borné absorbé par GG25) n'ont pas été re-dérivés en paramétrique.

## Ce que l'article NE revendique PAS (à écrire noir sur blanc)

- **Aucun fait arithmétique nouveau sur les nombres premiers.** Ce sont des réductions.
  La conjecture est exactement aussi ouverte qu'au premier jour.
- **G5 n'est pas un théorème d'impossibilité.** « Le comptage brut ne suffit pas » est
  une mesure numérique sur `π` ; « l'obstruction n'est pas équationnelle » est une
  observation sur la forme d'un manque produit par *nos* organes, à un état donné.
- **G4 ne dit pas que Goldbach est indémontrable par ces méthodes** au sens de la
  logique : il dit qu'une preuve qui ne distingue pas `S` d'un ensemble sans structure
  ne peut pas établir un énoncé qui, lui, en dépend. C'est une délimitation, pas une
  borne inférieure.
- **Pas de nouveauté sur la « formalisation d'un problème ouvert »** en général — ce
  qui est neuf est la composition : noyau exact + formalisme τ de Bourbaki + la
  *mesure* de la vacuité arithmétique par paramétrisation exécutable.

## Squelette

1. Introduction + contributions ← ce tableau
2. Background : le noyau, τ, l'arithmétique cardinale gardée (court — renvoyer à A1)
3. The certified map : les formes équivalentes, la convergence, GG24
4. The structure of the meeting : symétrie, demi-intervalle
5. **What the reductions do not contain** : le crible abstrait ← G4, le cœur
6. Two paths closed by the negative : comptage, équationnel ← G5
7. Fidelity : le défaut `est_premier` et sa réparation certifiée ← G6
8. Reproducibility : capstone 18/18, « clos ≠ sans axiome », le test de garde ← G1/G8/G9
9. Related work
10. Limitations
11. Conclusion

## Bibliographie

Réutiliser `../references.bib` (**47 entrées, toutes vérifiées** au 2 août) via
`\bibliography{../references}`. Entrées directement réutilisables : `mathias2002term`
(la longueur du terme τ), `grimm2010gaia` (Bourbaki en Coq), `guilloud2023lisa`,
`knuckledragger`, `ellis2021dreamcoder`, `blanchette2011nitpick`,
`learningtodisprove2026`, `conjecturingsurvey2026`.

⚠️ **Références à ajouter et à VÉRIFIER avant le gel** (aucune n'est encore dans le
`.bib` ; ne rien citer avant vérification aux sources — la règle « 0 entrée (v?) » de
A1 s'applique) : vérification numérique de Goldbach à grande borne ; Goldbach ternaire ;
formalisations existantes du Goldbach ternaire ; travaux sur la paramétricité / le
contenu calculatoire des preuves. **Statut : liste de courses, pas des citations.**

## Décisions prises (déléguées, révocables par Karl)

- Anglais, arXiv d'abord ; `article/goldbach/` séparé de `article/` (deux articles,
  un `.bib` commun).
- G4 énoncé sur sa **portée mesurée** (2 réductions), avec la réserve écrite au texte.
- La figure centrale est le graphe des équivalences de `CARTE_GOLDBACH.md`, refait en
  TikZ, avec la flèche pointillée = ce qui reste ouvert.
