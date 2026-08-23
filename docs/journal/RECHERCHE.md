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
| 2 | injectivité de l'union (forme couple) | 𝔇 | ✅ CLOSE (`union_dirigee_injective`) |
| 3 | famille COMPATIBLE | 𝔇 | ✅ CLOSE (`famille_compatible_de_chaine`) |
| 4 | famille DIRIGÉE (p,q ∈ 𝔇 ⇒ ∃r les prolongeant) | 𝔇 | ✅ CLOSE (`famille_dirigee_de_chaine`) |
| 5 | MEMBRES INJECTIFS : (∀p)(p∈𝔇 ⇒ injectif_graphe(p)) | 𝔇 | ✅ CLOSE (`membres_famille_injectifs`) |
| 6 | fonctionnalité de l'union | 𝔇 | ✅ CLOSE (`union_compatible_fonctionnelle`) |
| 7 | surjectivité du recollement | 𝔇,US | à faire |
| 8 | US ⊂ E | E,US | ✅ CLOSE (`us_inclus_E`) |
| 9 | dom(⋃𝔇) ⊂ US×US | 𝔇,US | ✅ CLOSE (`dom_union_inclus_carre`) |
| 10 | image(⋃𝔇, US×US) ⊂ US | 𝔇,US | ✅ CLOSE (`img_union_inclus_us`) |
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

### R-13, suite (07h20) — DÉPENDANCES : il ne reste que DEUX briques à écrire

Relecture de l'amont (`ensembles_recollement_famille_injectif.py` et
`ensembles_c60_coeur.py`) : **deux des données restantes sont déjà des
théorèmes du dépôt**, il suffit de leur fournir leurs hypothèses.

  • `union_famille_injective(𝔇)` : { famille_dirigee(𝔇), membres_injectifs(𝔇) }
    ⊢ injectif_graphe(⋃𝔇)  — c'est la donnée **(2)** ;
  • `union_famille_fonctionnelle(𝔇, p="pcf", q="qcf", …)` — c'est la donnée
    **(6)**, et ses liants `pcf`/`qcf` sont EXACTEMENT ceux de la donnée (3)
    dans la carte : elle se déduit donc de la compatibilité.

D'où la structure réelle :

    (2)  ⟸  (4) dirigée  +  (5) membres injectifs ✅
    (6)  ⟸  (3) compatible

**Il ne reste donc que DEUX briques à écrire dans ce cluster** — (3) et (4) —
toutes deux tirées de « C est une CHAÎNE » :

    p, q ∈ 𝔇(C)  ⇒  p = pr₂u, q = pr₂v avec u,v ∈ C        [membre_famille, CLOS]
    C totalement ordonnée par Γ𝔉  ⇒  (u,v) ∈ Γ𝔉  ou  (v,u) ∈ Γ𝔉
    (u,v) ∈ Γ𝔉  ⇒  pr₁u ⊂ pr₁v  et  pr₂u ⊂ pr₂v            [frame_ordre_membre_t]
    ⇒ (4) : prendre r := le plus grand des deux ;
    ⇒ (3) : deux graphes emboîtés coïncident là où les deux sont définis.

Briques repérées : `frame_ordre_membre_t` (frame_zorn/ensembles_frame_ordre_axiome.py:91),
`frame_ordre_reflexive` (…_est_ordre.py:64), `membre_famille` (CLOS).

Ordre d'attaque révisé : (4) dirigée d'abord — elle donne (2) immédiatement —
puis (3) compatible, qui donne (6). Restera (1), (7), (9), (10).

### R-13, suite (07h30) — donnée (4) dirigée : essai 2/4, deux étages sur trois

Module écrit : `h2_garde/claim/ensembles_famille_dirigee.py` (marqué EN CHANTIER).

**Ce qui PASSE** : l'α-renommage du second témoin — `membre_famille` fixe le
nom de son liant existentiel, l'appeler deux fois donnait deux ∃ homonymes
impossibles à éliminer imbriqués sans capture — et `_branche`, qui tire
X ⊂ Y de la comparabilité dans Γ𝔉 en transportant par les deux égalités
X = pr₂(u), Y = pr₂(v).

**Ce qui ÉCHOUE** : l'introduction existentielle finale (S5). La mineure
`((q∈𝔇 et p⊂q) et q⊂q)` ne coïncide pas avec le corps de `famille_dirigee`
substitué en r := q.

**Piège déjà rencontré et corrigé en route** : `inclus` construit un ∀ — il
n'a donc pas d'attribut `.termes`. Relire un terme sur une conclusion de type
inclusion lève un IndexError ; il faut prendre les termes sur les ÉGALITÉS.

**Suspect n°1 pour le prochain essai** : le LIANT interne de l'inclusion.
`inclus(t,u,z="z")` change de liant si « z » est libre dans t ou u, et
`inclusion_reflexive_terme` pourrait en produire un troisième. Méthode :
comparer les deux formules terme à terme (booléens seulement) AVANT de
retoucher la preuve — ne pas deviner.


### R-13, suite (07h35) — données (4) et (2) CLOSES : 5 sur 11

`famille_dirigee_de_chaine` : { chaîne } ⊢ famille_dirigee(𝔇(C)), 0,1 s, 1 hyp.
`union_dirigee_injective` : { chaîne } ⊢ injectif_graphe(⋃𝔇(C)), 0,4 s, 1 hyp —
elle tombe des données (4) et (5) par `union_famille_injective`, déjà dans le
dépôt. C'est le rendement direct du travail de cartographie.

**Ce qui avait bloqué, et ce qui l'a débloqué.** Deux essais perdus à soupçonner
le liant de `inclus`. La comparaison des formules — imposée au 3ᵉ essai — a
écarté ce suspect en trois lignes et montré le vrai défaut : dans une des deux
branches, les deux inclusions du corps étaient INTERVERTIES. Le corps attend
« p⊂r PUIS q⊂r » ; quand r := q c'est la dérivée puis la réflexivité, mais
quand r := p c'est l'inverse. Une asymétrie que la symétrie apparente du
raisonnement mathématique masque complètement.

**LEÇON 18** : quand une preuve échoue sur « mineure ≠ antécédent », COMPARER
les deux formules avant de toucher à la preuve. Le suspect intuitif (ici le
liant) est souvent innocent, et chaque essai à l'aveugle coûte plus cher que
le script de comparaison.

**Reste 6 sur 11** : (1) domaine couvrant, (3) compatible, (6) fonctionnalité
de l'union (⟸ 3), (7) surjectivité, (9) et (10) les deux inclusions.

### R-13, suite (07h40) — `pr2_fonctionnel`, la brique de la donnée (3)

`pr2_fonctionnel` : { p ∈ 𝔉(E) } ⊢ est_fonctionnel(pr₂ p), 0,4 s, 1 hyp.
Jumelle de `pr2_injectif` — même squelette, mais sans pont : la fonctionnalité
est directement le premier conjoint de `est_bijection_de`.

**Plan pour la donnée (3)**, famille_compatible(𝔇) =
(∀p)(∀q)(∀a)(∀b)(∀c)( ((p∈𝔇 et q∈𝔇) et ((a,b)∈p et (a,c)∈q)) ⇒ b=c ) :

  p = pr₂u, q = pr₂v avec u,v comparables dans Γ𝔉 (même départ que la donnée 4,
  squelette réutilisable tel quel) ;
  cas (u,v)∈Γ𝔉 : p ⊂ q, donc (a,b)∈q ET (a,c)∈q ; `pr2_fonctionnel` sur v donne
  est_fonctionnel(q), qu'on instancie en a,b,c ⇒ b=c ;
  cas (v,u) : symétrique, les deux couples atterrissent dans p.

⚠️ Attention à l'ORDRE ici aussi (LEÇON 18) : selon la branche, c'est (a,b) ou
(a,c) qu'il faut transporter par l'inclusion, et `est_fonctionnel` attend
(u,v)∈F puis (u,z)∈F dans cet ordre — la conclusion b=c n'est PAS symétrique
en b,c du point de vue de la construction.

Puis la donnée (6) tombera par `union_famille_fonctionnelle` (c60_coeur.py:180),
exactement comme (2) est tombée de (4)+(5).


### R-13, suite (07h45) — données (3) et (6) CLOSES : 7 sur 11

`famille_compatible_de_chaine` : { chaîne } ⊢ famille_compatible(𝔇(C)), 0,5 s,
1 hyp — **du premier coup**, l'avertissement LEÇON 18 ayant fait traiter
l'asymétrie dès l'écriture : c'est le couple du PETIT qu'on transporte, donc
(a,b) quand le majorant est q, mais (a,c) quand c'est p.

`union_compatible_fonctionnelle` : { chaîne } ⊢ est_fonctionnel(⋃𝔇(C)), 0,1 s —
tombe de (3) par `union_famille_fonctionnelle`, déjà dans le dépôt.

`_inclusion_membres` a été remonté au niveau module pour servir les deux
données sans duplication (non-régression vérifiée sur la dirigée).

**Reste 4 sur 11** : (1) domaine couvrant, (7) surjectivité, (9) dom(⋃𝔇) ⊂
US×US, (10) image(⋃𝔇, US×US) ⊂ US. Ces quatre-là mêlent 𝔇 ET US : elles
demanderont le lien entre `union_premiere(C)` et les pr₁ des membres, là où
les sept premières ne parlaient que de 𝔇.

### R-13, suite (07h50) — `pr1_inclus_union` : la brique des quatre dernières

{ u ∈ C } ⊢ pr₁(u) ⊂ ⋃S(C), 0,1 s, 1 hyp. Les sept données closes ne parlaient
que de 𝔇 ; les quatre restantes mêlent 𝔇 et US, et toutes passeront par ce
pont : la première projection d'un membre est contenue dans leur réunion.

Emploi ARRIÈRE de `membre_union_premiere` — S5 introduit l'existentielle au
témoin u — là où `us_inclus_E` l'employait dans le sens avant. Le corps et le
liant de cette existentielle sont LUS sur l'axiome (`antecedent_consequent`),
jamais reconstruits : c'est ce qui protège de la LEÇON 15.

**Reste à faire pour (9)** : de x ∈ dom(⋃𝔇) tirer un membre, puis son domaine
pr₁u × pr₁u, puis conclure par monotonie du produit pour ⊂ — chercher
`produit_monotone_inclusion` AVANT d'écrire.

⚠️ `claim/` atteint 10 entrées : le prochain module exigera un sous-dossier.

### R-13, suite (07h55) — `produit_monotone_carre`, et une question de PLACE

{ A ⊂ B } ⊢ A×A ⊂ B×B, 0,1 s, 1 hyp. Le dépôt ne l'avait pas (grep : aucune
monotonie du produit pour ⊂). C'est le dernier maillon de la donnée (9), après
`pr1_inclus_union`.

**Décision d'architecture** : l'énoncé a été écrit dans `ii_2_2_produit_deux_ensembles/`,
au chapitre du PRODUIT, et non dans la machinerie du §III.6 qui le réclame.
Il est général, la règle « l'arborescence calque la table des matières » le
place là, et `claim/` avait de toute façon atteint ses 10 entrées. Un lemme
écrit pour un besoin local mais d'énoncé général se range à son vrai chapitre.

**Il reste pour (9)** : assembler — z ∈ dom(⋃𝔇) → membre p=pr₂u → dom(pr₂u) =
pr₁u×pr₁u (corps du frame) → ⊂ US×US par les deux briques.

### R-13, suite (08h00) — `dom_pr2_egale_carre` : la donnée (9) n'attend plus que l'assemblage

{ p ∈ 𝔉(E) } ⊢ dom(pr₂ p) = pr₁(p) × pr₁(p), 0,3 s, 1 hyp, du premier coup.
Le corps du frame donne « dom φ = S×S » ; deux transports de Leibniz (φ → pr₂p,
S → pr₁p) suffisent.

Son intérêt est de mettre le domaine d'un membre sous forme de CARRÉ — la seule
que `produit_monotone_carre` sache faire croître. Les trois pièces de la donnée
(9) sont donc en place :

    z ∈ dom(⋃𝔇) → un membre p=pr₂u le contient       [membre_union_famille + membre_famille]
    dom(pr₂u) = pr₁u × pr₁u                          [dom_pr2_egale_carre]
    pr₁u ⊂ US  ⇒  pr₁u×pr₁u ⊂ US×US                  [pr1_inclus_union + produit_monotone_carre]

Il ne reste que le chaînage — mais attention, il faudra passer de « (z,y) ∈ p »
à « z ∈ dom(p) » (axiome du domaine, sens arrière) avant d'appliquer l'égalité.


### R-13, suite (08h05) — donnée (9) CLOSE : 8 sur 11

`dom_union_inclus_carre` : { chaîne } ⊢ dom(⋃𝔇(C)) ⊂ US×US, 0,4 s, 1 hyp.
Trois descentes existentielles emboîtées (un y, le membre p contenant (z,y),
le u de la chaîne dont p est la seconde projection), deux remontées.

**Un seul essai raté, et la LEÇON 18 l'a réglé en une ligne** : l'échec était
sur « mineure ≠ antécédent », et le coupable n'était pas la preuve mais le
LIANT — `pr1_inclus_union` produit une inclusion de liant « xup », alors que
`produit_monotone_carre` en attend une de liant « z » (le défaut de `inclus`).
Il a suffi de demander le bon liant à la première. Comparer plutôt que deviner
a encore payé.

**Reste 3 sur 11** : (10) image(⋃𝔇, US×US) ⊂ US, (1) domaine couvrant,
(7) surjectivité. La (10) devrait suivre le même schéma que la (9), avec
l'axiome de l'IMAGE au lieu de celui du domaine, et `pr2 ⊂ US` en bout de
chaîne — c'est-à-dire que l'image d'un membre est incluse dans US, ce qui
demandera un pendant de `pr1_inclus_union` côté image.

### R-13, suite (08h10) — plan CORRIGÉ pour la donnée (10)

Vérification en code avant d'écrire, et elle corrige l'intuition du tick
précédent : `est_bijection_de(φ,S×S,S)` se déplie en
`(fonctionnel et dom=S×S) et est_bijective(φ,S×S,S)`, et
`est_bijective(f,a,b) = injective_dans(f,a) et est_surjective(f,a,b)` — il n'y
a donc PAS de conjoint « image(φ,S×S)=S » directement lisible. L'idée
« l'image d'un membre est sa première projection » demande de passer par
`est_surjective`, dont la forme reste à lire.

**Mais l'axiome de l'image RANGE offre un chemin plus court** :

    AXIOME_IMG :  ( y ∈ img(G) )  ⇔  (∃x)( (x,y) ∈ G )

De « (x,w) ∈ p » on obtient donc w ∈ img(p) par S5 — sans passer par le
domaine ni par une image directe. Il ne resterait qu'à relier img(pr₂u) à
pr₁u, ce qui est exactement le contenu de la surjectivité du membre.

**Plan pour (10)**, à exécuter au prochain tick :
  1. lire `est_surjective(f,a,b)` en code (forme exacte) ;
  2. en tirer `img(pr₂u) ⊂ pr₁u` — brique à écrire, jumelle de
     `dom_pr2_egale_carre` mais côté image ;
  3. chaîner comme (9) : AXIOME_IMAGE, membre_union_famille, membre_famille,
     puis AXIOME_IMG et `pr1_inclus_union`.

⚠️ Ne pas oublier d'aligner le LIANT de l'inclusion finale (LEÇON 18) : c'est
ce qui a coûté l'unique essai raté de la donnée (9).


### R-13, suite (08h15) — donnée (10) CLOSE : 9 sur 11

`img_union_inclus_us` : { chaîne } ⊢ image(⋃𝔇(C), US×US) ⊂ US, 0,4 s, 1 hyp,
**du premier coup**. Jumelle de la (9) : même descente en trois existentielles
emboîtées, mais l'axiome de l'IMAGE au départ et `valeur_dans_pr1` à l'arrivée.

L'avertissement sur le liant, laissé après l'essai raté de la (9), a été
appliqué d'emblée — `pr1_inclus_union(C, vu, x="z")`. Deux données consécutives
sans essai perdu : les leçons 17 et 18 se paient d'elles-mêmes.

**Reste 2 sur 11** : (1) domaine couvrant et (7) surjectivité. Toutes deux de
la forme « tout point est atteint par un membre » : elles iront dans l'autre
sens que les précédentes — `membre_union_premiere` en sens AVANT pour DÉFAIRE
l'appartenance à US, puis S5 pour produire le témoin réclamé.

### R-13, suite (08h20) — énoncés EXACTS des deux dernières, et `valeur_atteinte`

Lus en code (et non devinés) :

    (7) surjectivité   : (∀w)( w ∈ US ⇒ (∃p)( p∈𝔇 et (∃a)( (a,w) ∈ p ) ) )
    (1) domaine couvrant : (∀a)( a ∈ US×US ⇒ (∃p)( p∈𝔇 et (∃w)( (a,w) ∈ p ) ) )

Elles disent donc : tout point de US est une VALEUR d'un membre, tout point de
US×US est dans le DOMAINE d'un membre.

`valeur_atteinte` (0,4 s, 1 hyp, du premier coup) fournit la pièce de la (7) :
{ p ∈ 𝔉(E) } ⊢ (∀w)( w ∈ pr₁p ⇒ (∃a)((a,w) ∈ pr₂p) ) — réciproque de
`valeur_dans_pr1`, c'est la surjectivité `image(φ,S×S)=S` lue dans l'autre sens.

**Assemblage restant pour (7)** : w ∈ US donne u ∈ C avec w ∈ pr₁u
(`membre_union_premiere` sens AVANT) ; `valeur_atteinte` donne l'antécédent ;
le membre cherché est pr₂u, à produire par `membre_famille` en sens ARRIÈRE.

**Pour (1)** : a ∈ US×US donne deux composantes dans US, donc DEUX membres de
la chaîne, qu'il faut comparer pour les loger dans un seul —
`_inclusion_membres` (ensembles_famille_dirigee.py) le fait déjà, mais il
faudra son conjoint pr₁ (`conjonction_elim_droite(conjonction_elim_gauche(corps))`)
et non le conjoint pr₂ qu'il extrait actuellement.
