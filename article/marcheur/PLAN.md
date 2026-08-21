# ARTICLE A4 — plan de campagne (ouvert le 21 août 2026)

**Cible** : preprint arXiv (cs.LO), après A1/A3/A2. **Langue : anglais d'abord**,
traduction française ensuite — mêmes conventions que les trois premiers.

**Titre de travail** : *The Walk Across the Last Mile: a Kernel-Guarded
Search That Invents Its Own Waypoints.* (Le titre du plan éditorial —
« Apprendre à proposer » — est ABANDONNÉ : le code ne retient rien entre
deux marches, il n'apprend pas ; un titre qui promet plus que le code viole
la règle de fidélité. Continuité avec A2 : A2 localise, A4 traverse.)

**Position** : **A4** du plan éditorial (`docs/articles/PLAN_ARTICLES.md`).
Question unique : *comment une machine apprend-elle à fabriquer le témoin — ou
le lemme — qu'aucun enchaînement ne trouve ?*

## ⚠️ LA PORTE (décision du plan éditorial, 10 août)

> Ne pas publier A4 avant que le marcheur ait fermé au moins un but que le
> chaînage seul ne ferme pas.

Tout ce document est suspendu à cette porte. Tant qu'elle n'est pas franchie
**en code, avec un test qui asserte les deux côtés** (le chaînage échoue ET le
marcheur ferme), A4 n'existe pas.

## La règle d'or (reprise de A1, A2, A3)

**Chaque phrase de l'article doit être adossée à un objet du dépôt.**
Aucun chiffre sans re-mesure le jour de l'écriture (leçon des 8/8 de A2).
`STYLE_ARTICLES.md` s'applique en entier.

## Le marcheur — design v1 (à construire, RIEN n'est mesuré)

Une marche discrète sur les états de dérivation, le noyau en garde-fou exact.
État = (but, pool de faits certifiés). Un pas :

1. **Sentir** : `besoins(but, pool)` — fermé ? fini. Sinon la liste des manques.
2. **Proposer** : miner le but lui-même — les motifs de termes répétés
   (critère MDL de v20, transposé des formules aux termes) ; instancier sur
   chaque motif les schémas de lois (commutativité, associativité, …).
3. **Réfuter à bas prix** : `oracle_num.contre_exemple` sur petits entiers —
   une conjecture fausse meurt en millisecondes, jamais en minutes de noyau.
   ⚠️ MESURÉ le 21 août : la table de l'oracle ignore `successeur(somme)` —
   les conjectures sur une opération dérivée lui sont invisibles (`None`).
   Extension nécessaire (une couche `successeur` sur la table existante).
4. **Certifier** : `besoins(conjecture, pool)` — le noyau juge. Une conjecture
   certifiée devient un fait du pool : **c'est le pas de compression**
   (idée 16 du plan éditorial : nommer, certifier, mesurer l'économie).
5. **Re-essayer** le but. Aucun pas nouveau → s'arrêter et rendre les manques
   terminaux (le marcheur, comme l'organe, échoue en nommant).

**Principe de sûreté inchangé** (ev.374) : le marcheur SUGGÈRE, le noyau JUGE.
Un mauvais pas coûte une route morte, jamais un faux théorème.

## Le but de la porte (expérience en cours, 21 août)

Banc ⊕ de v16–v18 : `a ⊕ b := (a+b)+1`, pool = les deux lois brutes sur `+`.

- **B4** := `((a⊕b)⊕c)⊕d = a⊕(b⊕(c⊕d))`. La chaîne brute attendue dépasse le
  budget mesuré du moteur (`max_pas=5`, v18 : la chaîne minimale du cas à 3
  éléments les consomme TOUS). Attendu : `besoins(B4, brut)` échoue.
- Le marcheur doit : certifier `⊕-assoc` (le but de v18) comme LEMME, l'ajouter
  au pool, refermer B4 en ≤ 2 applications de la loi dérivée.
- Garde-fou : une variante FAUSSE de B4 doit rester ouverte à travers toute la
  marche (et mourir à l'oracle une fois l'extension faite).

STATUT : expérience lancée (exp_marcheur.py), résultats non encore lus.
**Si EXP1 ferme B4 directement, ce but ne franchit pas la porte** — en trouver
un plus profond (5 éléments, ou commutations mêlées), et le DIRE dans l'article.

## Table des revendications (claim → preuve → statut)

| # | revendication | preuve attendue dans le dépôt | statut |
|---|---|---|---|
| **P1** | **La porte est franchie** : un but que le chaînage seul (21 organes, budgets mesurés) laisse ouvert est fermé par la marche | test qui asserte les DEUX côtés | 🔴 à construire |
| **P2** | **Le pas de compression** : le lemme certifié raccourcit la chaîne sous le budget — mesuré (pas bruts vs pas dérivés, temps) | mesures dans MESURES.md | 🔴 |
| **P3** | **La proposition vient du but** : les motifs sont minés dans le but lui-même (MDL), pas nommés par nous | code du mineur + test « la machine retrouve ⊕ sans qu'on le lui dise » | 🔴 |
| **P4** | **La réfutation avant la dépense** : l'oracle tue les schémas faux (idempotence…) avant tout appel noyau | test + coût comparé | 🔴 |
| **P5** | **L'échec reste une donnée** : une marche qui ne ferme pas rend ses manques terminaux | test négatif | 🔴 |
| **P6** | **Ce que ça ne fait pas** : aucune information mathématique nouvelle ; sur Goldbach le marcheur ne fait que reformuler le manque | renvoi A3 + test | 🔴 |

## Ce que l'article NE revendiquera PAS

- Aucun apprentissage statistique : pas de politique apprise, pas de réseau.
  « Apprendre à proposer » = retenir ce qui a payé (v15) + proposer depuis la
  structure du but. Si le titre promet plus que le code, changer le TITRE.
- Aucune généralité prouvée : un banc (⊕), peut-être deux. Le dire.
- La liste des schémas de lois est OUVERTE (règle des énumérations,
  STYLE_ARTICLES §8).

## Squelette prévisionnel

1. Introduction : la porte, et pourquoi elle existait
2. Background court (renvois A1/A2)
3. Le marcheur : état, pas, garde-fous
4. La porte franchie : B4, les deux côtés mesurés
5. Le pas de compression, chiffré
6. Ce que la marche ne trouve pas (Goldbach, renvoi A3)
7. Related work / Limitations / Conclusion

## Journal de campagne

- **21 août** : dossier ouvert. Oracle : trou `successeur(somme)` mesuré.
  EXP1/EXP2 (porte B4) lancées, résultats à lire. Rien d'autre n'existe.
