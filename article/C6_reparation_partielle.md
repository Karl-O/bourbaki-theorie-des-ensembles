# C6 — une réparation de fidélité VERTE et pourtant à moitié faite

*(Consolidation du 5 août 2026. Base de preuve d'un ajout à §4 « Fidelity auditing »
ou aux Limitations. Méthode identique à `C8_retours.md` : chaque ligne cite son
événement source dans `outils_ia/traces/events.jsonl`. Rien ici n'est un souvenir.)*

## Pourquoi ce cas mérite d'entrer dans l'article

L'article affirme déjà, en toutes lettres (main.tex l. 414-415) :

> *Infid* is semi-decidable: one can always *find* an infidelity, never certify its
> absence — which is why our audit is a standing process rather than a coverage
> percentage.

Le cas ci-dessous en est **l'instance empirique la plus nette du corpus**, et elle est
plus forte que l'énoncé actuel : ce n'est pas seulement qu'on ne peut pas certifier
l'absence d'infidélité *en général*. C'est qu'une infidélité **précisément identifiée,
réparée, et dont la réparation a été validée par un test dédié VERT**, était encore à
moitié présente — et que rien dans l'instrumentation ne pouvait le dire.

Ce cas ne contredit aucune revendication du papier. Les deux défauts d'axiome de §4
ont été établis par **contradiction dérivée au noyau**, ce qui est une route plus forte.
Ici il s'agit d'un défaut de **définition**, et il n'a été révélé que par un blocage de
preuve situé très en aval.

## Les faits, datés

| étape | date | événement | ce qui s'est passé |
|---|---|---|---|
| détection | 4 août | — | la définition du « système projectif » (§III.7.1) ne portait que les deux conditions NUMÉROTÉES de Bourbaki, (LP_I) cocycle et (LP_II) identité. Le livre pose AVANT elles, en prose, le typage : « soit f_{αβ} une application de E_β dans E_α ». Écart consigné dans `docs/journal/ANOMALIES.md` |
| réparation | 5 août ~03h | ev. 207-208 | `transitions_typees` ajouté et rendu CONJOINT de `est_systeme_projectif` ; la signature a dû gagner la famille `Efam` en tête — le manque était inscrit dans le TYPE, pas seulement dans le corps |
| validation | 5 août ~03h | ev. 207-208 | le test `test_definition_systeme_projectif_est_fidele_au_livre` est **INVERSÉ** : il épinglait l'absence du typage, il épingle désormais sa présence. Suite verte. L'écart est déclaré COMBLÉ |
| **réfutation** | 5 août ~15h | **ev. 217** | en butant sur l'inclusion réciproque de la Proposition 3, mesure des hypothèses résiduelles indémontrables : ce sont des conditions de **DOMAINE**, « (∃y)((t,y) ∈ f_{αβ}) ». Or « application de E_β dans E_α » dit **TROIS** choses — graphe fonctionnel, défini sur tout E_β, à valeurs dans E_α — et `transitions_typees` n'en capturait qu'**une**, les valeurs |
| réparation complète | 5 août ~15h | ev. 217 | `transitions_applications` : f_{αβ} ∈ (E_α)^(E_β), l'EXPOSANT (graphes) et non 𝓕(E_β;E_α) (triplets) ; `transitions_fonctionnelles_et_totales` en tire fonctionnalité et domaine par `axiome_exposant` |
| **quantification** | 5 août ~18h | **ev. 219-222** | les deux moitiés sont chacune porteuse, à des endroits différents : **6** hypothèses résiduelles réclament le DOMAINE (couvertes par `transition_definie_en`), **3** réclament les VALEURS (couvertes par `transition_valeur_dans_E`). Appariement vérifié **sur les instances réelles** (`port.conclusion == h`, pas une ressemblance) : 6/6 et 3/3 |

## L'affirmation exacte (à écrire telle quelle)

> A fidelity repair can be *green and incomplete*. In August 2026 we detected that our
> definition of a projective system carried only Bourbaki's two numbered conditions and
> not the typing stated in prose before them; we added the missing conjunct, inverted
> the pinning test so that it would witness the presence rather than the absence of the
> repair, and the suite was green. Eleven hours later, a blocked proof three sections
> downstream showed the repair had captured one of the three components of ``$f_{\alpha
> \beta}$ is an application of $E_\beta$ into $E_\alpha$'' --- the values --- and neither
> of the other two. The missing half was not detectable by any test we had: a form test
> can witness that a conjunct is *present*, never that a conjunct is *complete*.

## La leçon méthodologique (le contenu réel de l'ajout)

**Un écart de fidélité se mesure par ce qu'il empêche de DÉMONTRER, pas par ce qu'un
test de forme accepte.** Trois conséquences, toutes vérifiables au dépôt :

1. **Le manque était structurellement invisible.** Tant que les conditions de domaine
   bloquaient, le besoin de conditions de valeurs ne pouvait pas se manifester : une
   preuve s'arrête au premier obstacle. Un défaut n'est révélé que par le premier
   consommateur qui en a besoin — et l'ordre des besoins est arbitraire.
2. **Le test de fidélité doit épingler chaque CONJOINT, pas la notion.** Notre test
   inversé vérifiait « le typage est présent dans la définition ». Il aurait fallu
   « chacune des trois composantes du typage est présente ». La granularité du test
   d'ancrage doit être celle de la phrase du livre, pas celle du concept.
3. **Le verdict de guérison a la même semi-décidabilité que le verdict d'infidélité.**
   L'article dit qu'on ne peut jamais certifier l'absence d'infidélité ; ce cas ajoute
   qu'on ne peut pas non plus certifier la COMPLÉTUDE d'une réparation. « Repair proved
   effective by the impossibility of re-deriving the contradiction » (main.tex l. 425-426)
   reste vrai pour les deux défauts d'axiome — la contradiction est un témoin objectif —
   mais ne se transpose PAS aux défauts de définition, où il n'y a pas de contradiction
   à re-dériver, seulement des preuves qui passent ou ne passent pas.

## Où l'insérer

- **§4 (Fidelity auditing)**, à la suite des deux défauts d'axiome : un troisième cas,
  de nature différente (définition, pas axiome ; blocage de preuve, pas contradiction).
- **ou Limitations**, comme borne honnête sur la portée du verdict de guérison.

Le point 3 ci-dessus est le seul endroit où le texte actuel demande une nuance : la
phrase « both repairs were proved effective by the impossibility of re-deriving it »
est exacte pour les deux axiomes, et il faut éviter que le lecteur la généralise aux
réparations de définitions. Une subordonnée suffit.

## Statut

🟠 rédigé, **non transcrit en LaTeX** — décision de Karl (l'article est en attente de
gel v1 : nom d'auteur, commit+tag du dépôt, relecture humaine).
