# RECHERCHE.md — journal d'hypothèses et d'idées nées des résultats

Principe (décidé avec Karl le 2026-08-22) : le formaliseur (Claude) vit dans le
bac à sable ; chaque résultat — vert, rouge, ou surprenant — peut suggérer une
idée de recherche. On les consigne ICI au fil de l'eau, avec un verdict qui
évolue. Le « mode découverte » actif (des ticks dédiés à explorer ces questions)
s'enclenche après Hessenberg ; d'ici là ce journal accumule.

Statuts : `OUVERTE` (à explorer) · `EN COURS` · `CLOSE` (résolue/utilisée) ·
`ABANDONNÉE` (avec la raison).

---

## R-1 (2026-08-19, CLOSE) — L'astuce du clamp : borner une règle τ sans toucher aux évaluations
**Née de** : le verrou de la borne V (l'itération de Dedekind exigeait
`regle_dans_V(T,E)`, impossible pour une règle u arbitraire).
**Idée** : composer la règle avec un garde `clamp_E(t) = τ_z((t∈E∧z=t)∨(t∉E∧z=x0))` ;
la borne devient dérivable sous la seule hypothèse `x0∈E` (double tiers exclu),
et le clamp est *invisible* sur le domaine utile (déclampage sous `g(n)∈E`).
**Portée générale** : technique réutilisable pour TOUTE construction par
récursion dans le calcul du τ où la règle n'est pas nativement bornée. Candidat
à un lemme générique et à une section d'article (ingénierie de preuve du τ).

## R-2 (2026-08-21, CLOSE — leçon majeure) — Soundness ≠ fidélité : la « récursion » qui était une tabulation
**Née de** : l'audit du C60 déposé — il prouvait une équation affaiblie
(tabulation), pas `f(x) = T(f|seg x)`.
**Observation de recherche** : un noyau LCF garantit zéro faux théorème mais ne
protège PAS d'un énoncé silencieusement affaibli. La reconstruction complète
(C60-vrai → C63-vrai, ~30 ticks) a montré que l'écart était réparable *dans le
système*. Matériau d'article : taxonomie des « affaiblissements silencieux »
et méthode de détection (relecture PDF + assertions de forme).

## R-3 (2026-08-22, OUVERTE) — Mesurer le « 1 » de Bourbaki (vérifier Mathias)
**Née de** : la question de Karl « peut-on faire de la recherche ? ».
**Idée** : écrire un déplieur-compteur qui expanse intégralement un terme
(τ, ⊃, définitions) et MESURE sa taille — confronter l'estimation de Mathias
(~10^54 symboles pour le chiffre 1) à une mesure machine exacte, première
mondiale. Ne demande pas de prouveur ; quelques jours. Après Hessenberg.

## R-4 (2026-08-22, OUVERTE) — La machine, 3 étages
**Née de** : discussion avec Karl (plan détaillé dans DECISIONS du 2026-08-22).
Étage 1 automate (tautologies S1-S4, chaînes d'égalités, ∀ évidents) — accélère
le chantier lui-même ; étage 2 chaînage arrière sur la bibliothèque ; étage 3
LLM suggéreur + noyau juge (« LLM + calcul du τ », sujet vierge).

## R-5 (2026-08-22, OUVERTE) — Taxonomie des captures : 14+ leçons = un résultat en soi
**Née de** : l'accumulation des leçons de capture (liants ∀-clos aux noms frais,
paramètres-lieurs réutilisés (leçon 13), et()-encodé, témoins ∃ à α-renommer…).
**Idée** : ces pièges sont *spécifiques au τ de Bourbaki* et nulle part
documentés mécaniquement. Les systématiser (catalogue + contre-exemples
machine-vérifiés) = contribution originale sur l'ingénierie de preuve du τ.

## R-6 (2026-08-22, OUVERTE) — Le patron « familles S8 dédiées » comme principe général
**Née de** : Dfam_rec/Dglob_rec (le terme PORTE son graphe — leçon seg_ext) et
des théories S8 jamais auto-référentes.
**Idée** : formuler le principe (« toute construction paramétrique passe par une
théorie dédiée conservative ») et prouver sa conservativité au-dessus des 22
axiomes — un mini-théorème métathéorique sur NOTRE architecture, publiable dans
le rapport et l'article A1.

## R-7 (2026-08-22, CLOSE — leçon d'outillage) — MAX_PATH 260 sur l'arbre profond
**Née de** : import impossible du module D1b (chemin absolu à 261 caractères) ;
symptôme piégeux : listdir voit le fichier, stat/import échouent (WinError 3).
**Leçon** : sur un dépôt qui calque la table des matières (arbres profonds),
la limite Windows MAX_PATH mord ; noms de dossiers/fichiers COURTS près des
feuilles. Candidat outillage : un lint CI qui borne la longueur des chemins.

## R-8 (2026-08-22, OUVERTE) — La chaîne K6 paramétrique : un « foncteur de preuve »
**Née de** : l'assemblage D1d — toute la chaîne K6 (itération, valeurs,
injectivité, équipotence) est PARAMÉTRIQUE en (u, x0) : l'instancier aux
termes concrets h∘ι, h(m) a suffi, aucune preuve refaite.
**Idée** : ce motif (bibliothèque de théorèmes à paramètres-termes + décharges
par coupure) est l'analogue LCF-τ des foncteurs/locales d'Isabelle. À
systématiser et à mesurer (coût des substitutions sur gros termes vs re-preuve)
— matériau pour l'article ingénierie de preuve du τ.

## R-9 — Dériver l'absorption 𝔟+𝔟=𝔟 (résidu 1/3 de Hessenberg)

**Statut : plan établi, toutes les briques repérées, non encore écrit.**

L'absorption n'est PAS un théorème global à importer : au maximal elle se tire
de la bijection φ₀ elle-même (𝔟·𝔟=𝔟), ce qui la rend LOCALE et donc dérivable
dans la portée. Chaîne :

    𝔟 + 𝔟  =  𝔟·(1+1)   [distributivite_operations, a=𝔟, b=c=1]
           =  𝔟·1 + 𝔟·1  ↔  𝔟+𝔟          [produit_cardinal_un ×2]
    2 ≤ 𝔟                                  [deux_inf_egal_infini, S₀ infini]
    𝔟·2 ≤ 𝔟·𝔟                              [produit_cardinale_monotone_droite]
    𝔟·𝔟 = 𝔟                                [maximal_carre_egal, la bijection φ₀]
    𝔟 ≤ 𝔟+𝔟                                [_inf_egal_somme_gauche_t]
    ⇒ 𝔟+𝔟 = 𝔟                              [inf_egal_antisymetrique_card]

**Difficulté attendue** : les « 1 » ne sont pas au même niveau — `produit_cardinal_un`
parle de l'ENSEMBLE {∅}, `DEUX = successeur(UN)` de la SOMME de cardinaux. Il
faudra des ponts de Leibniz entre `singleton(∅)` et `Card({∅})`, comme
`successeur_zero_egale_un` en fournit déjà un.

Les deux autres résidus : le TRANSPORT (déjà isolé et nommé en amont, la
bijection canonique Card A → A) et le PAQUET ψ (le vrai calcul cardinal de
Bourbaki : la zone (S₀∪U)² ∖ (S₀×S₀) a le cardinal 𝔟, donc se met en bijection
avec U). Le paquet est le plus gros ; il consomme précisément 𝔟·𝔟=𝔟 et 𝔟+𝔟=𝔟.

## R-9 — RÉSOLU (2026-08-23) : absorption 𝔟+𝔟=𝔟 DÉRIVÉE

`absorption_au_maximal` : { S₀ infini, φ₀ bijection } ⊢ Card S₀+Card S₀ = Card S₀.
199,9 s, 2 hypothèses — toutes deux DONNÉES DU MAXIMAL, donc fournies par
`unpack_sous_maximal` : l'absorption disparaît des résidus (3 → 2).
Difficulté réelle rencontrée : les trois « un » et les deux niveaux de ≤ —
voir LEÇON 16 dans DECISIONS.

## R-10 — Dériver le TRANSPORT (résidu 2/3, dernier « petit »)

**Énoncé** (`_transport_sous_ensemble_hyp`, déjà isolé et nommé en amont) :

    (∃U)( U ⊂ Card A  et  Card U = c )  ⇒  (∃V)( V ⊂ A  et  Card V = c )

**Idée** : la bijection canonique g : Card A → A (témoin de Eq(A, Card A)
symétrisée) transporte U en V := g⟨U⟩.

**Brique clé repérée** : `injection_donne_equipotent_image(F,c,a)` (CLOSE, 0
hypothèse) — « ⊢ est_injection_de(F,c,a) ⇒ Eq(c, image(F,c)) » : une injection
est une bijection sur son image. Avec F := g restreinte à U, elle donne
Eq(U, g⟨U⟩), donc Card g⟨U⟩ = Card U = c.

**Point délicat attendu** : la RESTRICTION de g à U ⊂ Card A — montrer que
c'est encore une injection de U dans A. C'est le seul maillon sans brique
toute faite ; chercher `restriction`, `induit`, `graphe_restreint` avant
d'écrire, et appliquer la règle des 4 essais.

**Puis** : le PAQUET ψ (résidu 3/3, le gros morceau) et `donnees_recollement`.

## R-10 — RÉSOLU SANS ÉCRIRE UNE LIGNE DE PREUVE (2026-08-23)

Le transport n'était PAS un trou : le dépôt le ferme depuis
`iii_4_entiers_finis/ordinal_cardinal/realisation_segment/ensembles_transport_sous_ensemble.py`
(GAP B), par `existe_sous_ensemble_cardinal_transporte(c, A, V)` — **0 hypothèse**.
L'astuce y est de ne PAS transporter une partie de Card A vers A, mais de
réaliser directement c ≤ A par transitivité (c ≤ Card A ≤ A via Eq(A,Card A)).

Mon `existe_u_cadre` appelait encore l'ANCIENNE version
(`existe_sous_ensemble_cardinal`), celle qui porte le transport en hypothèse
honnête. Un seul changement d'import : les résidus de Hessenberg passent de
2 à **1** (il ne reste que le garde ∀U, c'est-à-dire le paquet ψ).

**Règle qui en découle** (à appliquer AVANT de traiter un résidu comme ouvert) :
chercher une variante `_transporte` / `_clos` / `_prouve` du même nom. Un
résidu nommé peut avoir été fermé ailleurs sans que ses appelants soient
recâblés. Le grep « qui utilise la version close ? » montre d'ailleurs que
`step_b_prop5/` et `assemblage_vrai/` l'utilisaient déjà — mon module neuf
était le seul en retard.

## R-11 — PISTE : `negation_strict_sous_maximal_reunion` (step_b_prop5/stepb3)

Sa docstring annonce ¬(𝔟 < Card E) sous la SEULE maximal-data (+ résidus ∀∀ de
`fini_downward_thm`) — donc SANS le paquet ψ, qu'elle construirait elle-même
via `cadre_card_trois_b_reunion` (le calcul cardinal de la zone). Si c'est
exact en code, le dernier résidu de Hessenberg tombe.
⚠️ À VÉRIFIER EN CODE, jamais sur la foi de la docstring (leçon des agents).

### R-11 — VÉRIFIÉ EN CODE (2026-08-23, 05h43)

`negation_strict_sous_maximal_reunion("E","S0","phi0")` :
  • conclusion == ¬( Card S₀ < Card E )  ✔ (comparaison par `==`, pas de lecture)
  • **7 hypothèses, AUCUNE ne mentionne Ucadre, ψ ni uwit** ✔
  • deux d'entre elles sont CLOSES (aucune variable libre) — vraisemblablement
    les résidus ∀∀ de `fini_downward_thm` ; les cinq autres ne parlent que de
    S₀, φ₀, E.
  • coût : 384 s.

Donc la docstring dit vrai : ce module construit LUI-MÊME le paquet ψ (via
`cadre_card_trois_b_reunion` et le recâblage RÉUNION qui dissout le mur de la
somme disjointe) et n'en laisse aucune trace en hypothèse.

**Conséquence** : il est plus fort que mon `non_strict_clos`, qui porte le
paquet en résidu ∀U. Le brancher dans `claim_clos` ferait tomber le DERNIER
résidu de Hessenberg. Prix à payer : 384 s contre ~30 s — donc garder les DEUX
chemins (le rapide, à résidu nommé, pour l'itération ; le complet, marqué
`slow`, pour la certification).

## R-12 — Prouver « une différence d'entiers est un entier » : est_cardinal(a − b)

**Pourquoi** : c'est l'unique brique qui bloque le recâblage de la division
euclidienne sur la downward-closure GARDÉE (cf. ANOMALIES 2026-08-23). Sans
elle, `_diff_est_fini` doit passer par l'universel nu, non satisfait, et les
deux modules de division restent vides.

**Énoncé visé** : { a ≥ b (ou : Fini a, b ≤ a) } ⊢ est_cardinal( diff_somme(a,b) ).

**Piste** : sous `b ≤ a`, `existe_temoin` donne un témoin c avec a = b + c, et
`diff_somme(a,b)` EST ce τ. Il faudrait alors montrer que ce c peut être choisi
CARDINAL — typiquement en le réalisant comme `Card(A ∖ B)` pour des ensembles
témoins, ce qui relie R-12 à `_card_E_somme` (déjà utilisé par
`complement_grand` : Card E = Card S₀ + Card(E∖S₀)).

**Retombée** : la division euclidienne est l'un des gros chantiers ouverts listés
dans CLAUDE.md ; cette brique la débloquerait au niveau de la fidélité, pas
seulement de la couverture.

## R-13 — CARTE des données du recollement (mesurée en code, 2026-08-23)

`frame_de_recollement()` réclame **11** hypothèses (et non 9 comme le disait sa
docstring). Classées, avec leurs variables libres :

| # | contenu | libres | statut |
|---|---------|--------|--------|
| 1 | domaine couvrant : tout point de US×US est dans le domaine d'un membre | 𝔇,US | à faire |
| 2 | injectivité de l'union (forme couple) | 𝔇 | à faire |
| 3 | famille COMPATIBLE (deux membres coïncident là où les deux sont définis) | 𝔇 | à faire |
| 4 | famille DIRIGÉE (p,q ∈ 𝔇 ⇒ ∃r les prolongeant) | 𝔇 | à faire |
| 5 | MEMBRES INJECTIFS : (∀p)(p∈𝔇 ⇒ injectif_graphe(p)) | 𝔇 | ✅ CLOSE (`membres_famille_injectifs`) |
| 6 | fonctionnalité de l'union | 𝔇 | à faire |
| 7 | surjectivité du recollement | 𝔇,US | à faire |
| 8 | US ⊂ E | E,US | ✅ CLOSE (`us_inclus_E`) |
| 9 | dom(⋃𝔇) ⊂ US×US | 𝔇,US | à faire |
| 10 | image(⋃𝔇, US×US) ⊂ US | 𝔇,US | à faire |
| 11 | US infinie | US | ✅ CLOSE (`us_infini`) |

**Le blocage précis de (5).** La route naturelle est celle de `pr1_inclus_E` :
g ∈ 𝔇 donne (∃q)(q∈C ∧ g = pr₂ q) par `membre_famille` (CLOS) ; q ∈ C ⊂ 𝔉 donne
`est_bijection_de(φ, S×S, S)`. Mais `est_bijection_de` fournit l'injectivité au
niveau VALEUR (`injective_dans`), tandis que (5) la réclame au niveau COUPLE
(`injectif_graphe`). Le dépôt ne possède que le pont dans l'AUTRE sens :

    injectif_graphe_implique_injective_dans : {est_fonctionnel, injectif_graphe}
                                              ⊢ injective_dans(F, dom F)

**Brique manquante nommée** : la RÉCIPROQUE,
`{ est_fonctionnel(F), injective_dans(F, dom F) } ⊢ injectif_graphe(F)`.
Elle est vraie (si f est une fonction et que ses valeurs distinguent les points,
deux antécédents d'une même image coïncident) et elle débloquerait (5), donc
vraisemblablement aussi (2) et (6) qui portent sur l'union des mêmes graphes.
C'est le prochain objectif naturel, avant d'attaquer (3) et (4) qui, eux,
dépendent de l'ORDRE de la chaîne et non de la structure de graphe.


### R-13, suite (2026-08-23, 07h15) — donnée (5) CLOSE, le pont a payé

Le pont réciproque écrit au tick précédent débloque exactement ce qui était
annoncé. Deux briques neuves :

  • `pr2_injectif` : { p ∈ 𝔉(E) } ⊢ injectif_graphe(pr₂ p) — miroir de
    `pr1_inclus_E` pour la seconde projection ; le corps du frame donne la
    bijection, dont on extrait fonctionnalité et injectivité-VALEUR, que le
    pont convertit en forme COUPLE. 0,4 s, 1 hypothèse.
  • `membres_famille_injectifs` : { chaîne } ⊢ membres_injectifs(𝔇(C)) —
    la donnée (5). 0,2 s, 1 hypothèse.

**Piège évité** : le pont relaie vers `couple_donne_valeur`, qui attend des
NOMS ; on l'appelle donc par le nom du liant (`nphi`), jamais par le terme.
C'est la LEÇON 17 appliquée avant de se cogner, pour une fois.

`union_fam_egale` ré-éprouvée au passage (LEÇON 17) : elle échoue TOUJOURS,
même erreur qu'avant. Le contournement `inclus_dans_union_fam` reste la voie.

**Reste 8 des 11.** Les prochaines dans l'ordre de facilité présumée : (2) et
(6), injectivité et fonctionnalité de l'UNION — mêmes graphes, et le dépôt a
`union_famille_injective` dans `ensembles_recollement_famille_injectif.py` :
RELIRE L'AMONT avant d'écrire.
