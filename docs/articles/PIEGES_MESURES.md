# Les pièges, mesurés — matériau transversal (A1 et A2)

Chaque entrée est un piège **rencontré et payé**, pas une bonne pratique
recopiée. C'est le genre de matériau qui donne son autorité à un article de
méthode : on ne raconte pas ce qu'il faudrait faire, on raconte ce qui a
cassé.

---

## A. Sur la vérification (ce qui fait croire qu'on a mesuré)

**1. Le test qui n'a pas tourné.** J'ai conclu « le proposeur v12 ne ferme
rien » à partir d'un appel qui, faute du bon paramètre, était retombé
silencieusement sur `(None, [])`. Le test n'avait jamais tourné. *Règle :
asserter la CAPACITÉ avant de mesurer* — `inspect.signature` coûte une ligne.
En cherchant pourquoi, j'ai trouvé le vrai défaut (les proposeurs ne
franchissaient pas la couche `besoins_generaux`).

**2. Le test qui réussit des deux côtés.** Pour montrer que v13 (fabrique un
témoin) dépasse v10 (choisit un témoin), mon cas d'essai était fermé par les
deux. *Un test que les deux branches passent ne discrimine rien* — il faut
construire le cas où l'une échoue.

**3. Le mauvais indicateur.** J'ai d'abord jugé v13 sur le NOMBRE de manques
produits. Or l'apport n'était pas quantitatif : le manque passait de `∃p∃q…`
(le but intact) à `¬(…τp…)` (les propriétés d'un terme). *C'est la FORME du
résultat qu'il fallait mesurer, pas son volume.*

**4. L'horloge estimée.** Sur un marathon de plusieurs heures, j'ai déduit
l'heure en cumulant les durées d'exécution. Dérive mesurée : **2 h 30** — de
quoi clore un créneau bien avant terme et horodater faux quinze entrées de
journal. *Une donnée qu'on ne peut pas déduire du contexte doit être lue.*
Réglé structurellement par un hook qui injecte l'heure à chaque tour.

---

## B. Sur la fidélité (ce qui fait prouver la mauvaise chose)

**5. La garde qui porte sur le mauvais argument.** `est_premier(p)` gardait le
DIVISEUR mais pas `p` : un objet non-cardinal n'étant divisible par rien, la
clause universelle devenait vraie à vide et « premier » se réduisait à `p ≠ 1`.
L'énoncé de Goldbach était donc **plus faible que la conjecture** — sans que
le noyau ait rien à redire. *La soundness ne protège pas de viser à côté.*

**6. Le blocage qui parle de l'énoncé.** Le sens ⇒ de l'équivalence refusait
de se fermer. J'ai cherché un lemme manquant ; il n'en manquait aucun.
*Un blocage persistant est un signal sur l'énoncé, pas sur la preuve.*
Confirmation par l'usage : avec l'énoncé corrigé, le sens ⇒ se ferme **et
consomme exactement la garde ajoutée**.

**7. La sélection non bornée.** Un axiome de compréhension posé sans borne
avait rendu la théorie contradictoire (incident de juillet). Depuis, toute
sélection est bornée par un ensemble déjà construit — `{x ∈ [0,b] : …}`, jamais
`{x : …}`.

---

## C. Sur le formalisme (ce qui casse à l'exécution)

**8. La collision de liants.** Instancier un axiome `∀x(x∈Q ⇔ ∃y …)` en un
terme qui porte le nom `y` capture la variable. *Ne pas RECONSTRUIRE la
matrice d'un `∃` : LIRE le liant que le noyau a effectivement produit*
(`.lieur` / `.sous[0]`), puis asserter que la matrice instanciée est celle
attendue.

**9. L'extraction par navigation.** `et(a,b)` est `¬(¬a ∨ ¬b)` et `∀` est
`¬∃¬` : atteindre une sous-formule à coups de `.sous[0].sous[1]` est illisible
et casse au premier changement. *Reconstruire la sous-formule attendue et
asserter l'égalité* — le miroir sert de test.

**10. Le prédicat défini qui enfouit son argument.** `est_fini(c)` a le tag
`non` (il se déplie) : extraire « les termes de tête » ne rend rien. Il faut
passer par les **variables libres**, qui traversent le dépliage. C'est ce qui
sépare le proposeur v10 du v11.

**11. La généralisation impossible.** On ne peut pas éliminer `∃m` quand la
conclusion contient `m` libre. Le noyau refuse — à raison. *L'erreur était
dans ma formulation, pas dans le code* : l'énoncé correct généralise sur `m`
au lieu de l'éliminer, et il est d'ailleurs plus fort.

---

## D. Sur la conduite d'un chantier long

**12. Le faux « bloqué ».** Six fois, un blocage annoncé s'est révélé faux
après re-sonde. *Re-mesurer après chaque organe ; ne jamais faire confiance à
une carte de la veille.*

**13. Mesurer avant d'investir.** Avant de formaliser l'inclusion-exclusion
(plusieurs jours), un calcul de dix minutes a montré que le critère visé
**ne tient pour aucun k ≥ 2**. *Un résultat négatif bon marché vaut mieux
qu'un chantier coûteux.*

**14. L'écart entre ce qui est prouvé et ce qui est ressenti.** Il est facile,
après quinze théorèmes, d'écrire « nous avons réduit Goldbach ». La formule
honnête est : *nous avons certifié des équivalences ; la conjecture reste
ouverte, et aucun fait arithmétique nouveau n'a été produit.*

---

## 12 août 2026 — LOI : LES TERMES SONT OPAQUES, LES FORMULES NE LE SONT PAS

**Découverte en construisant l'oracle numérique, et valable pour tout futur
évaluateur, simplificateur ou analyseur de termes.**

Dans ce noyau, `N(7)` et `N(3) + N(4)` sont **tous deux** des τ-termes de
`tag == 'tau'` avec **un seul argument** (une formule). Il n'y a donc rien à
décomposer dans un terme arithmétique : `SC(a, b)` n'est PAS un nœud binaire
d'enfants `a` et `b`.

**Conséquence** : aucun évaluateur ne peut fonctionner par descente dans les
termes. La seule voie est la **reconstruction** — bâtir le terme attendu et
comparer. C'est praticable parce que les assemblages sont hashables et que
l'égalité est en O(1) ; c'est impraticable si l'on reconstruit à chaque appel.
D'où : **une table bâtie une fois**.

**Les FORMULES, en revanche, se décomposent normalement** (`¬`, `∨`, `∃`, `=`).
Et comme `et`, `⇒`, `∀` en sont des abréviations, évaluer les primitives les
donne gratuitement. La frontière « formule décomposable / terme opaque » est
la structure obligée de tout outil de ce genre.

**Mesure** : descente naïve 333 s → table 3 s, **facteur 100**, sur le même
jeu de six évaluations.

**J'ai fait l'erreur DEUX FOIS en vingt minutes** — d'abord sur les termes,
puis sur la reconnaissance des prédicats, où je naviguais à coups de
`.sous[0].sous[1].sous[0]`. La seconde fois, appliquer la loi qu'on venait
d'écrire a marché du premier coup. C'est le même défaut que
`PIEGES_MESURES` §9 (« ne pas naviguer dans les sous-formules ; reconstruire
et asserter »), généralisé : **ne jamais supposer une structure, la regarder.**
Une introspection de trois lignes (`type`, `tag`, `len(args)`) a réglé en
quelques secondes ce que deux hypothèses successives avaient coûté.

