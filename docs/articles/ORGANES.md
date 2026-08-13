# Les organes de l'organe de besoin — catalogue au 10 août 2026

L'« organe de besoin » prend un but, un pool de théorèmes, et rend soit une
preuve certifiée, soit **la liste des formules qui, ajoutées au pool, la
fermeraient**. Il a grandi par accrétion : **chaque organe est né d'un manque
observé**, jamais d'une architecture pensée d'avance. C'est la thèse de
l'article A2, et voici sa pièce à conviction.

**Deux natures.** Les organes *internes* vivent dans `besoin.py` et changent
la stratégie de recherche. Les *proposeurs* sont des fonctions passées en
paramètre : `besoin.py` ne les connaît pas, il expose seulement un point
d'extension (v6). Le noyau juge dans les deux cas — un mauvais candidat ne
coûte qu'une route morte.

---

| # | Nature | Ce qu'il fait | **Né de quel diagnostic** |
|---|---|---|---|
| **v2** | interne | les conjoints d'un antécédent sont re-soumis au pool, puis recomposés (∧-intro structurel) | les conjoints étaient *nommés* comme manques mais jamais re-testés : les faits qui les fermaient n'étaient pas consultés (PB14-15) |
| **v2b** | interne | ne nommer que les conjoints **récalcitrants** | le reporting était binaire : un conjoint fermable réapparaissait comme manque |
| **v3** | interne | fusionner les manques de la voie directe | `besoins_generaux` jetait `_m_direct` : des manques réels disparaissaient du rapport |
| **v4** | interne | instancier les faits-∀ du pool sur le but | l'hypothèse de récurrence `S{n}` restait **inerte** dans le pool |
| **v5** | interne | les faits-∀ d'implication deviennent des **routes** (ré-ouverture par instanciation à leur propre variable) | même diagnostic, côté implications : `universels_de` filtre, il ne génère pas |
| **v6** | interne | **point d'extension** : accepte des proposeurs de témoins | manque terminal écrit par la machine : `σ` ne proposait que `p := n`, donc `¬(n = n)` — « il me faut un générateur de témoins » |
| **v7** | interne | ∃-descente : viser `φ[x:=t]` puis ré-introduire (jugé noyau) | aucun but existentiel n'était **jamais** décomposé |
| **v8** | interne | un but-conjonction est éclaté puis recomposé | le cœur additif de Goldbach (`∃p∃q…`) exigeait la conjonction |
| **v9** | interne | un but `t = t` ferme par réflexivité | mesuré : la route « jumelle » traînait `2k = 2k` comme un manque |
| **v10** | proposeur | témoins = les `t` des faits `t ∈ A` du pool | premier proposeur **générique** : il ignore le problème |
| **v11** | proposeur | témoins = les **variables libres** des faits | v10 n'extrayait que les termes de tête ; or `est_fini(c)` a le tag `non` (prédicat défini) et **enfouit** son argument |
| **v13** | proposeur | **fabrique** le témoin canonique `τx(φ)` depuis le but seul | v10/v11 *choisissent* : quand le pool ne nomme aucun objet, ils sont muets (mesuré sur GG24) |
| **v14** | interne | une route-témoin qui échoue ne **jette** plus les manques de sa descente | avec v13, le but `∃` restait reporté tel quel alors que la descente avait déjà nommé les obligations sur le témoin |
| **v15** | proposeur | **retient** les témoins qui ont fermé, et les re-propose | aucun proposeur n'apprenait : à chaque but, tous repartaient de zéro |
| **prop.** | infra | les proposeurs traversent `besoins_generaux` (∀, ⇒, voie directe, feuille) | ils ne franchissaient pas cette couche : aucun `∃` enfoui sous un `∀` n'était attaquable |
| **v16** | interne | **fabrique** la congruence : ramène `C[a] = C[b]` à `a = b` en abstrayant un sous-terme | la machine savait *chaîner* une congruence donnée, pas la construire — mesuré sur la commutativité d'une opération dérivée `a ⊕ b := (a+b)+1` |
| **v17** | interne | enchaîne les réécritures du pool (largeur d'abord, deux sens, composition par transitivité) | l'ASSOCIATIVITÉ de la même opération : les deux membres ne sont pas `f(u)`/`f(v)`, une congruence seule n'y suffit pas |
| **v18** | interne | les lois du pool sont **instanciées au moment d'être appliquées** (match du membre gauche contre les sous-termes, noyau juge) | v17 cherchait le membre gauche *littéralement* : le pool dit `a+b`, le but contient `(a+b)+1` — la loi était bonne, c'est son INSTANCE qui manquait |
| **v19** | interne | **CALCULER avant de démontrer** : un but numériquement FAUX est réfuté d'emblée | le système ne calculait JAMAIS pour se guider — or le résultat le plus rentable de la campagne Goldbach fut une mesure (le critère des tiroirs tué par un crible d'Ératosthène), jamais une preuve |
| **v20** | **notions** | **PROPOSE des définitions** : mine les sous-formules récurrentes des ÉNONCÉS et les score par compression MDL | aucun organe ne CRÉAIT de notion — tous manipulaient des notions existantes ; or l'histoire des mathématiques est d'abord une histoire de définitions |
| **v21** | **analogie** | **RAPPROCHE deux preuves** de même squelette d'inférence : le vocabulaire de LIAISON (fréquent) garde son identité, celui de DOMAINE (rare) est effacé ; distance d'édition sur multiensembles | le système ne travaillait que dans un seul sujet, alors que le transport d'une structure d'un domaine vers un autre est le geste inventif par excellence — et il retrouve seul `demi ≈ demi_abstrait`, que personne ne lui avait montrée |

---

## Ce que le catalogue montre

**1. L'outil se déduit du diagnostic.** Aucune de ces dix-neuf lignes ne vient
d'une intuition d'architecte : chacune répond à un échec qu'on peut rejouer.
La colonne de droite est plus informative que celle du milieu.

**2. La frontière chaînage / créativité, tracée par la machine.** Jusqu'à v9,
l'organe *chaîne* ce qu'on lui donne. À partir de v6, il accepte qu'on lui
*propose*. Avec v13, il **fabrique**. Le passage n'a pas été décidé : c'est le
manque `¬(n = n)` — écrit par la machine elle-même — qui l'a imposé.

**3. Le progrès n'est pas quantitatif.** v13 ne ferme pas plus de buts que v10 ;
il change la **forme** du manque restant (`∃p∃q…` → propriétés d'un τ-terme).
Un indicateur de volume l'aurait déclaré inutile.

**4. Elle finit par capitaliser.** v15 retient les témoins qui ont fermé.
Mesuré sur `decomposition(N16)` : la première passe coûte **102 s** (le
proposeur calcule), la seconde **0 s** — le proposeur appris seul, sans aucun
accès à l'arithmétique, suffit. C'est le premier compounding réel du projet,
et le premier morceau concret du marcheur (article A4).

**5. Ce que ça ne fait pas.** Aucun de ces organes ne produit d'information
mathématique. Face à Goldbach, avec tout l'arsenal au pool et les proposeurs
actifs, la machine **ne ferme pas** — elle nomme exactement ce qui manque : la
rencontre de `P₂ₖ` avec son miroir, pour `k` composé. C'est la conjecture.

---

**Protection** : 15 tests dans `test_autonomie.py` (un par organe à partir de
v2), suite complète du dossier `outils_ia/decouvertes/` verte à **24 passed**
(40 min, le test lent d'Euclide inclus).

**Reproductibilité** : les 17 scripts de l'arc Goldbach sont rejoués en
sous-processus par `VERIF_TOUS.py` — **17/17 sans erreur**, invariant 22
partout, 17 minutes. Coûts dominants : `PB29b` (GG15, finitude de P₂ₖ) 493 s,
`PB30` 319 s ; tout le reste sous 80 s.

---

## Le palier v16–v18 : la machine étudie une opération qu'on vient d'inventer

Les quinze premiers organes ont tous été taillés sur **Goldbach**. Les trois
suivants viennent d'une question différente, posée le 11 août : *la mécanique
de recherche stagne-t-elle, ou sait-elle aborder une algèbre neuve ?*

Le protocole est volontairement nu. On définit une opération que le dépôt ne
connaît pas —

    a ⊕ b := (a + b) + 1

— on ne donne à la machine que **deux lois brutes** sur `+` (associativité
itérée, commutativité), et on lui demande les propriétés de `⊕`.

| but | avant | après |
|---|---|---|
| `a ⊕ b = b ⊕ a` | échec, « aucune route » | **v16**, 0,29 s |
| `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)` | échec à tout budget (95 s en profondeur 7) | **v17 + v18**, 8 s, clos, 0 hypothèse |

**Ce que le second cas a appris, et qui vaut au-delà de lui.** L'échec avait
l'allure d'un mur exponentiel : coût ×2 par palier de profondeur, nombre de
manques figé à 1. Le diagnostic a montré tout autre chose — un organe écrit
**deux fois** (cf. `ANOMALIES.md`, 12 août) et une borne `max_pas` calibrée à
3 quand la chaîne minimale en fait **5** :

    ((a+b)+1)+c = (a+b)+(1+c) = (a+b)+(c+1) = a+(b+(c+1)) = a+((b+c)+1)

Un cran de budget, et une largeur d'abord à la place d'une profondeur d'abord.
Le rapport est de 24× — 4 s de succès contre 95 s d'échec, sur le même pool.

**Leçon d'outillage, généralisable.** Une recherche qui échoue *en grossissant*
(coût qui explose, manques qui stagnent) ne se répare presque jamais en lui
donnant plus de budget. Les deux fois où le projet a rencontré cette signature,
la cause était en amont : un ordre d'exploration inadapté, ou une borne fixée
au jugé plutôt qu'à la mesure. **Mesurer la longueur de la chaîne attendue
avant de régler la borne** est devenu la règle — c'est ce que fait désormais la
docstring de `reecrire_vers`, qui porte ses chiffres.

**Ce que ça ne dit pas.** Rien de tout cela ne produit de mathématique neuve :
`⊕` est une opération jouet, et ses deux lois sont des corollaires immédiats de
celles de `+`. Ce qui est acquis est plus modeste et plus solide — la machine
**peut désormais raisonner équationnellement** sur une structure qu'elle n'a
pas vue en apprentissage, sans qu'on lui pré-mâche les instances. C'est le
prérequis de tout le reste, pas un résultat en soi.

