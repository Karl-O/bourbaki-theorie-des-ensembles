# La carte machine de Goldbach — état au 10 août 2026, 10h35

> **L'énoncé d'entrée** (GG24, clos) :
>
> ```
> ⊢  [ ∀k composé,  les premiers ≤ 2k rencontrent leur miroir ]  ⇒  Goldbach
> ```
>
> Tout le reste — les k premiers, le passage de la rencontre à la
> décomposition, le pont vers l'énoncé du dépôt — **est démontré**.

## Le graphe des équivalences (tout est certifié, sauf la flèche pointillée)

```
                        goldbach()                    ← l'énoncé du dépôt
                            ‖  (équivalence close)
                            H              « ∀k, 2k est somme de 2 premiers »
              ┌─────────────┼─────────────┐
        GG7 ‖ │             │ ‖ GG10      │ ⇑ GG24
              │             │             │
             HC            H_τ      [ ∀k composé : rencontre(k) ]
       composés seuls   sans ∃ (τ)        │
                                          │  ‖ GG19  (les deux sens)
                                          │
                                  ∃m ( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ )
                                          │
                                    ┌─────┴─────┐
                              GG22  │           │  GG23
                        k premier ⇒ │           │ ⇒ m et son partenaire
                          rencontre │           │   2k − m y sont aussi
                                    └───────────┘
                                          ⋮
                                    ⋮ (la conjecture)
                                          ⋮
                              établir la rencontre pour k composé
```

`P₂ₖ` = les premiers ≤ 2k (**non vide**, GG14 · **fini**, GG15).
`Q₂ₖ` = son miroir = `{ x : ∃y premier, 2k = x + y }`.
`‖` = équivalence certifiée · `⇑` = implication certifiée · `⋮` = ouvert.

**Les trois lignes du projet convergent ici.** Le travail sur Goldbach avait
suivi trois directions ; elles se rejoignent toutes sur la rencontre :

| ligne | acquis | absorbée par |
|---|---|---|
| **bornée** | Goldbach vérifié pour tout `n ≤ 86` | **GG25** — tout témoin concret donne la rencontre |
| **composés** | les `k` premiers sont gratuits | **GG22** — `m := k` témoigne |
| **crible** | `P₂ₖ` rencontre son miroir | forme d'arrivée |

Autrement dit, **tout ce qui a été démontré sur Goldbach dans ce dépôt se lit
désormais comme un énoncé sur la rencontre** — un seul objet à étudier au lieu
de trois.

**Statut global : la conjecture RESTE OUVERTE.** Ce document ne recense pas
une preuve, mais un réseau d'**équivalences et de réductions certifiées par le
noyau**, plus les obligations exactes qui restent à chaque feuille. Tous les
théorèmes cités sont clos (0 hypothèse non déchargée) sauf mention contraire,
et `theorie_ensembles()` vaut 22 axiomes à chaque exécution.

Les scripts vivent dans le scratchpad de session (non promus au dépôt : les
dossiers `conjectures/` et `decouvertes/` sont pleins — l'éclatement est une
décision de Karl).

**Tout est reproductible.** `CAPSTONE_crible.py` rejoue les 12 maillons en
43 s avec une assertion finale qui casse si l'un cède ; `VERIF_TOUS.py`
relance les **17 scripts** de l'arc en sous-processus — **17/17 sans erreur,
invariant 22 partout**, 17 minutes. La suite `outils_ia/decouvertes/` est à
**24 passed**.

---

## 1. Le tronc : quatre formes équivalentes

| # | Énoncé | Statut | Coût | Script |
|---|--------|--------|------|--------|
| — | `goldbach()` — tout pair ≥ 4 est somme de deux premiers | référence | — | dépôt |
| H | forme **moitiés** : `∀k decomp(k+k)` | ⟺ goldbach | — | dépôt |
| HC | forme **composés** : idem, restreint à `¬premier(k)` | ⟺ H (GG7) | 0 s | `GG7_reduction_composes.py` |
| Hτ | forme **canonique** : `∀k( A(k) ⇒ C(k) )`, **sans ∃** | ⟺ H (GG10) | 0 s | `GG9_pont_tau.py` |

**GG7** — les `k` premiers sont gratuits (`2k = k+k`), donc la conjecture ne
porte que sur les composés. Tiers exclu sur `premier(k)`, branche premier via
la famille `{2p}` et le pont-α **GG6** (`premier₁ ⇒ premier₂`, α sur les deux
habits `d1q1`/`d2q2`).

**GG9/GG10** — chez Bourbaki `∃x φ(x)` **est** `φ(τx φ)` : les deux primitives
du noyau (`existe_temoin`, `s5`, E I.32) éliminent le quantificateur. La
conjecture devient trois propriétés de deux termes nommés
`T := τp(∃q mat)` et `Q := τq(mat[p:=T])` :
`premier₁(T) ∧ premier₂(Q) ∧ 2k = T+Q`.

---

## 2. La descente

**GG8** (`⊢ H_rec ⇒ H`, 240 s, `PB22_descente.py`) — la récurrence forte du
dépôt branchée sur Goldbach : il suffit de prouver le pas
`∀n( S{n} ⇒ R{n} )`. Le résidu `pfu` est déchargé.

Fait notable de méthode : **c'est la machine qui a écrit ce pas**, comme son
manque, puis l'a décomposé (structure fractale premier/composé).

---

## 3. Les témoins : une stratégie = un couple de termes

**PB28** — le générateur `route_temoin(T, Q)` compile *n'importe quels* termes
en route certifiée (`s5` ×2, gratuit) :

> `⊢ ∀k( premier₁(T) ∧ premier₂(Q) ∧ 2k = T+Q ⇒ decomp(2k) )`

Quatre stratégies versées d'un coup, avec leurs obligations respectives :

| stratégie | T | obligation dure |
|-----------|---|-----------------|
| gloutonne | plus grand premier ≤ 2k | `2k − T` premier |
| décalée | plus grand premier ≤ 2k−2 | idem |
| **jumelle** | `T = Q = k` | **`k` premier** (subsume la famille `{2p}`) |
| canonique | `τp(∃q mat)` | les deux primalités (= GG9) |

---

## 4. L'ensemble des premiers bornés

`P_2k := { p : premier(p) ∧ p ∈ [0,2k] }` — terme opaque + axiome dans une
théorie dédiée (moule de l'intervalle d'entiers ; sélection **bornée**, donc
sans risque de la faute d'incohérence de juillet).

| # | Énoncé | Coût |
|---|--------|------|
| GG14 | `∀k( H(k) ⇒ 2 ∈ P_2k )` — **non vide** | 49 s |
| GG14b | `∀k( H(k) ⇒ P_2k ≠ ∅ )` | — |
| GG15 | `∀k( Fini k ⇒ P_2k fini )` | 4 min |
| GG16 | `∀k( H(k) ⇒ premier(T°) )`, `T° := τm(m ∈ P_2k)` | 84 s |
| GG17 | `∀k( H(k) ∧ premier(2k−T°) ⇒ decomp(2k) )` | 247 s |

**GG16 est le premier témoin symbolique dont la primalité est effectivement
prouvée** (le τ dénote parce que `P_2k` est non vide). GG17 décharge toute
l'intendance — mais `T°` est un premier *arbitraire*, donc son hypothèse ne se
déduit pas : **impasse propre**, qui indique la sortie.

---

## 5. La forme crible (l'état actuel)

En quantifiant sur les témoins plutôt qu'en en fixant un :

> **GG19** : `⊢ ∀k(  ∃m( m ∈ P_2k ∧ m ∈ Q_2k )  ⟺  2k = p+q avec p,q premiers )`
> — les **deux sens**, 2 s, avec `Q_b := { x : ∃y( premier(y) ∧ b = x+y ) }`.

Le miroir est défini par un **∃ interne** : ni soustraction, ni
commutativité, ni cardinalité du complément.

**Le sens ⇒ n'est démontrable qu'avec l'énoncé gardé** (§6) : il consomme
`Fini(p)` via `prop2_sous_fini`. Re-sondé, l'organe nomme cette rencontre,
mot pour mot, comme son unique manque (`PB35`).

**La forme crible absorbe la réduction aux composés** — GG22 (6 s) : si `k`
est premier, la rencontre est témoignée par `m := k` lui-même. D'où le
théorème d'entrée, **GG21 + GG19a + GG22 + tiers exclu** :

> **GG24** : `⊢ [ ∀k composé, rencontre(k) ] ⇒ H` (6 s)

Il ne reste donc qu'**une seule chose à prouver** — et c'est la conjecture.

**La rencontre est symétrique** — GG23 (6 s) : tout point `m` de la rencontre
vient **avec son partenaire**, et les deux somment à `2k`.

> `⊢ ∀k ∀m ( m ∈ P₂ₖ ∩ Q₂ₖ ⇒ ∃m' ( m' ∈ P₂ₖ ∩ Q₂ₖ ∧ 2k = m + m' ) )`

La rencontre est donc stable par l'involution `m ↦ 2k − m`, dont le point fixe
est `k` — exactement le cas GG22. **Les décompositions de Goldbach vont par
paires.**

**L'organe suit** : le proposeur **v10** (générique — face à `(∃x)φ(x)`, les
témoins sont les `t` des faits `t ∈ A` du pool) ferme la chaîne complète
`{c ∈ P, c ∈ Q} ⊢ décomposition`, là où sans lui elle reste ouverte. Premier
proposeur qui ne sait rien du problème.

**Et il finit par refaire GG9 seul.** Les proposeurs v10/v11 *choisissent* un
témoin parmi les objets nommés ; quand le pool n'en nomme aucun, ils sont
muets (mesuré sur GG24). Le proposeur **v13** *fabrique* le témoin canonique
`τx(φ)` depuis le but seul, et **v14** empêche que les manques d'une
route-témoin échouée soient jetés. Effet observable, à pool vide :

| proposeur | manque nommé sur `decomposition(2k)` |
|---|---|
| v10 (choisit) | `∃pgb ∃qgb …` — le but, **intact** |
| v13 (fabrique) | `¬( … τpgb(…) … )` — les **propriétés du terme** |

Autrement dit la machine ramène d'elle-même « il existe p, q premiers sommant
à 2k » à « propriétés de deux termes nommés » : le geste de §1 (GG9), fait à
la main, est devenu un organe. Elle ne crée aucune information — elle change
la forme de la question.

---

## 6. L'audit de fidélité (⚠️ décision d'énoncé en attente)

`est_premier(p)` ne garde que le **diviseur** ; comme `divise_propre(d,p)`
exige `p = Card(d×q)`, un `p` non-cardinal n'est divisible par rien et
« premier » s'y réduit à `p ≠ 1`. Certifié :

> `⊢ ( p ≠ 1 ∧ (∀d)¬divise_propre(d,p) ) ⇒ est_premier(p)`

Donc `goldbach()` **quantifie sur des témoins non entiers** : l'énoncé
formalisé est plus faible que la conjecture. Soundness intacte, fidélité en
défaut. Correction `premier_ent(p) := Fini(p) ∧ est_premier(p)`, **gratuite**
sur les numéraux. Détail : `docs/journal/ANOMALIES.md`.

---

## 7. Ce qui est fermé, et ce qui reste

**Fermé** — les équivalences ci-dessus ; Goldbach vérifié pour tout `n ≤ 86`
(script paramétré, ~23 primalités certifiées à la volée) ; la sanité complète
de `est_premier` (démontre 2, 3, 5, 7… et réfute 0, 1, 4, 6, 9).

**Fermé par la négative** — la voie du **comptage brut** : le critère des
tiroirs `2·π(2k) > 2k+1` ne tient **pour aucun `k ≥ 2`** (π/k tombe de 0,50 à
0,18 à `2k = 2·10⁵`), alors que le nombre réel de décompositions croît
(2 → 1417). *Mesure numérique, pas une preuve.* Conséquence assumée : ne pas
formaliser l'inclusion-exclusion pour ce problème — il faut une information
sur la **répartition** de `P_2k`, pas sur son cardinal.

**Ouvert** — la rencontre elle-même, c'est-à-dire la conjecture. Les pistes
non explorées : le sens retour de la réduction aux composés sous forme
crible ; des familles de témoins définis plus fines ; et le proposeur appris
(cf. `PLAN_ARTICLES.md`, A4), seul candidat à produire un témoin qu'aucun
enchaînement ne trouve.

---

## 8. Re-sonde du 12 août : l'obstruction n'est PAS équationnelle

La carte ci-dessus a été dressée avec une machine qui ne savait pas raisonner
**équationnellement** : elle ne fabriquait pas de congruence (organe v16), ne
chaînait pas de réécritures (v17), n'instanciait pas les lois du pool aux
sous-termes rencontrés (v18). Or le cœur de Goldbach est une équation sur des
sommes cardinales, `2k = p + q`. Le cycle du projet — *besoin → comblement →
re-sonde* — imposait donc de repasser les obligations devant l'outil neuf.

**Mesure** (`RESONDE1_goldbach_v18.py`, pool réduit aux deux lois brutes) :

| obligation | verdict | coût |
|---|---|---|
| `2k = p+q ⊢ 2k = q+p` | fermé | 0 s |
| `(p+q)+k = p+(q+k)` | fermé | 0 s |
| symétrie du crible : `2k = m+y ⊢ 2k = y+m` | fermé | 0 s |
| **`rencontre(k)` générique** | **OUVERT, 1 manque** | 0 s |

**Lecture honnête.** Les deux commutations n'étaient **pas** hors de portée
avant : le journal du 11 août atteste que v17 fermait déjà `a+b = b+a` en
0,0 s. Seule la **réassociation** est neuve, et elle l'est parce que
l'associativité itérée a été promue au dépôt le 12 août — pas parce qu'un
organe a progressé.

**Le point qui compte.** Le manque de `rencontre(k)` a **exactement la même
forme** qu'avant les trois organes :

    ∃m ¬( m ∈ premiers_ent_bornes(2k) ⇒ ¬ m ∈ miroir_ent(2k) )

La frontière n'a pas bougé d'un pouce. C'est cohérent, et c'est une
information : **l'obstruction de Goldbach n'est pas de nature équationnelle**,
donc aucun renforcement de l'algèbre — associativité, distributivité,
réécriture plus profonde — ne l'entamera. Les organes v16–v18 sont réels et
utiles, et strictement **orthogonaux** à cette conjecture.

Cela referme par la négative une seconde voie, après celle du comptage brut
(§7). Ce qui reste ouvert reste ouvert pour la même raison qu'au premier jour :
il faut produire un objet — un premier `m ≤ 2k` dont le complément `2k − m` est
premier — et aucune manipulation formelle de l'énoncé ne le fabrique.

---

## 9. Où lire tout cela dans le code (12 août)

L'arc n'est plus dans des scripts de session : il vit sous `recherche/goldbach/`,
testé et rejouable. Correspondance des repères de cette carte aux modules :

| repère de la carte | module | fonction |
|---|---|---|
| forme sans ∃ (GG9/GG10) | `pont_tau.py` | `forme_canonique` |
| familles de témoins | `pont_tau.py` | `route_temoin`, `plus_grand_premier`, `somme_du_temoin` |
| réduction aux composés (GG7) | `composes.py` | `equivalence_composes` |
| forme crible (GG19) | `crible.py` | `equivalence_crible` |
| raccord à l'énoncé du dépôt (GG21) | `synthese.py` | `gardee_implique_depot` |
| branche « k premier » (GG22) | `synthese.py` | `rencontre_des_premiers` |
| **la synthèse (GG24)** | `synthese.py` | `composes_impliquent_goldbach` |
| symétrie des solutions (GG23) | `symetrie.py` | `symetrie_du_crible` |
| **le demi-intervalle** | `demi.py` | `demi_intervalle`, `rencontre_se_restreint` |
| défaut de fidélité (§6) | `audit_fidelite.py` | `indivisible_implique_premier` |
| rejeu complet | `capstone.py` | `verifie_chaine` — 14/14 CLOS |

**Deux colonnes, pas une.** Le capstone distingue « clos » (le noyau accepte la
preuve) de « axiomes ad hoc » (de quelle théorie dédiée elle dépend) : 10
maillons sont libres, 4 reposent sur les deux axiomes du crible. Un théorème
tiré par `N.axiome` a zéro hypothèse — `est_clos` ne dit donc rien sur les
axiomes ajoutés. Les confondre serait la seule tricherie possible ici.

**Ce qui a été abandonné, et pourquoi.** Les résultats bâtis sur un
`premiers_bornes` NON gardé (GG14, GG15, GG16, GG17) ne sont pas migrés : ils
portent sur un ensemble mathématiquement différent de celui du crible, dont la
garde `Fini` est justement la correction du défaut §6. Les réintroduire
demanderait de les re-démontrer sur l'ensemble gardé — c'est du travail neuf.

---

## 10. La symétrie du crible — une contrainte de RÉPARTITION

Les sections 7 et 8 ont refermé deux voies par la négative, et toutes deux
disaient la même chose : il faut de l'information sur **où** se trouvent les
premiers de `P₂ₖ`, pas sur combien ils sont ni sur la forme de l'énoncé. La
symétrie en est une, et elle est maintenant certifiée sur les vraies
définitions du crible :

> ⊢ (∀k)(∀m)[ m ∈ P₂ₖ ∩ Q₂ₖ ⇒ (∃m')( m' ∈ P₂ₖ ∩ Q₂ₖ ∧ 2k = m + m' ) ]

Les solutions vont **par paires**, stables sous l'involution `m ↦ 2k − m`,
dont le point fixe est `k`. C'est conditionnel — « s'il y en a une, il y en a
deux » — donc rien sur l'existence.

**Ce que le portage a coûté, et pourquoi c'est instructif.** La version
d'exploration donnait à `P` et au miroir **la même graphie** de primalité, ce
qui évitait toute difficulté. Sur les définitions réelles les deux habits α se
croisent : le partenaire sort du miroir en habit 2 et doit entrer dans `P` en
habit 1, pendant que `m` fait le trajet inverse. Il a fallu le pont-α dans les
**deux** sens — d'où sa paramétrisation (`pont_alpha_premier(source, cible)`).
Une simplification commode dans un script d'exploration peut ainsi cacher tout
le travail réel ; c'est un motif à surveiller lors des migrations.

⚠️ Le pont **nié** `¬premier₂ ⇒ ¬premier₁` reste indisponible, et ne se déduit
pas de la paramétrisation : une implication ne se contrapose pas gratuitement
ici. `HC` porte bien `¬premier₁`, et c'est délibéré.

---

## 11. La moitié suffit — et ce que ça ne donne pas

La symétrie (§10) dit que les solutions vont par paires sommant à `2k`. Il
manquait le pas suivant : **de chaque paire, un membre tombe dans la première
moitié.**

> ⊢ (∀k)(∀m)(∀m')[ ( Fini k ∧ Fini m ∧ Fini m' ∧ 2k = m + m' )
>                  ⇒ ( m ≤ k  OU  m' ≤ k ) ]

C'est un fait d'**arithmétique cardinale pure** — aucun nombre premier n'y
figure. Assemblé avec la symétrie, il donne l'équivalence :

> ⊢ (∀k)[ Fini k ⇒ ( rencontre(k) ⟺ (∃m)( m ∈ P₂ₖ ∩ Q₂ₖ ∧ m ≤ k ) ) ]

**La route, et pourquoi elle évite le strict.** Les inégalités strictes coûtent
cher dans ce noyau. On s'en passe : comparabilité des cardinaux pour ouvrir les
deux cas ; dans le cas `k ≤ m`, le complément existe (Prop. 13), donc
`m = k + d` ; alors

    k + k  =  m + m'  =  (k + d) + m'  =  k + (d + m')

et la **simplification additive finie** (Cor. 3 §III.5.2) donne `k = d + m'`,
d'où `m' ≤ k` par la Prop. 2. Pas une seule inégalité stricte.

⚠️ **La garde `Fini` n'est pas de la prudence.** La simplification additive est
**fausse** pour les cardinaux infinis : `ℵ₀ + 1 = ℵ₀ + 2` sans que `1 = 2`.
Sans la garde, l'énoncé serait faux — pas seulement indémontrable. C'est le
même défaut de fidélité qu'au §6, pris à temps cette fois.

**CE QUE ÇA NE DONNE PAS, et il faut le dire net.** Diviser par deux un espace
de recherche qui reste infini en `k` ne rapproche d'aucune preuve. La
conjecture est exactement aussi ouverte qu'avant. Ce qui est acquis est une
équivalence certifiée de plus et une contrainte structurelle exacte — de la
matière pour la carte, pas un pas vers la solution.

**Une remarque de méthode, qui vaut plus que le résultat.** L'étape de
réassociation `(k+d)+m' = k+(d+m')` utilise l'**associativité itérée de
l'addition cardinale**, qui n'existait pas au dépôt et qui a été démontrée le
matin même — sur un tout autre chantier, celui d'une opération algébrique
inventée pour tester si la machine stagnait. Le trou comblé pour une raison a
servi pour une autre, quelques heures plus tard. C'est l'argument le plus
concret en faveur de combler les trous *quand on les voit*, sans attendre d'en
avoir l'usage.

---

## 12. Ce que ces réductions ne contiennent pas — le crible ABSTRAIT

Toute la carte qui précède décrit des réductions certifiées de Goldbach. La
question qu'il fallait finir par poser : **combien d'arithmétique y a-t-il
là-dedans ?**

La réponse est mesurée, pas argumentée. Le dossier `recherche/additif/` reprend
la construction du crible avec le prédicat en **paramètre** — une fonction
`Terme → Formule` :

    P_b := { x : Fini x ∧ S(x) ∧ x ∈ [0,b] }
    Q_b := { x : (∃y)( Fini y ∧ S(y) ∧ b = x + y ) }

et démontre **les quatre grandes réductions** — forme crible (GG19, les deux
sens), réduction aux composés (GG22), symétrie, demi-intervalle — **sans jamais
ouvrir `S`**. La même preuve, mot pour mot, ferme sur :

| `S` | temps | ce que c'est |
|---|---|---|
| `x ∈ 𝕊`, `𝕊` totalement opaque | 5 s | aucune propriété supposée |
| `est_premier(x)` | 4 s | **Goldbach** |
| `est_pair_propre(x)` | 4 s | un ensemble pour lequel la question est triviale |

**Le verdict.** Une démonstration qui ne distingue pas les nombres premiers
d'un ensemble sans structure ne peut pas servir à démontrer Goldbach. Ce n'est
pas un défaut de nos preuves : c'est une propriété des énoncés qu'elles
établissent. Les quatre grandes réductions de cette carte — composés, crible,
symétrie, demi-intervalle — **ne portent aucun contenu arithmétique**.

**⚠️ CETTE PHRASE A ÉTÉ FAUSSE DU 12 AU 19 AOÛT, et c'est instructif.** Écrite
le 12, elle annonçait QUATRE réductions ; le code n'en établissait que DEUX
(symétrie et demi-intervalle). Ni GG19 ni GG22 n'existaient sous forme
paramétrique — `grep composes|equivalence_crible recherche/additif/` ne rendait
rien. L'écart a été trouvé le 19 août **en relisant le code contre cette
prose-ci**, pendant la rédaction de l'article A3, et refermé le jour même par
`equivalence_abstraite.py` (GG19 les deux sens + GG22, clos sur les trois
prédicats, 13 tests verts en 5 min 53). Le portage s'est révélé **mécanique** :
les preuves concrètes ne se servaient de la primalité que comme d'un conjoint
opaque, jamais ouvert — *il n'y avait rien d'arithmétique à porter*, ce qui est
la thèse même de cette section.

*La leçon, à retenir au-delà du cas : aucun test n'attrape une phrase de
document qui ment sur le code. Le noyau garantit la soundness, jamais la
fidélité de ce qu'on écrit à côté.*

**Où c'est démontré :**

| réduction | module abstrait | fonction |
|---|---|---|
| forme crible GG19 (⇐ et ⇒) | `additif/equivalence_abstraite.py` | `equivalence_abstraite` |
| composés GG22 | `additif/equivalence_abstraite.py` | `rencontre_des_elements` |
| symétrie GG23 | `additif/crible_abstrait.py` | `symetrie_additive` |
| demi-intervalle | `additif/demi_abstrait.py` | `restriction_a_la_moitie` |

**Pourquoi c'est un résultat et pas un aveu.** Il délimite la conjecture : ce
qui est structurel d'un côté, ce qui est arithmétique de l'autre, avec la
frontière tracée en code plutôt qu'à l'estime. Il explique aussi, d'un seul
coup, les deux voies déjà refermées par la négative (§7 le comptage, §8
l'équationnel) : elles échouent pour la même raison, elles ne regardent jamais
*quels* entiers sont dans `S`. Et « Goldbach est une instance » n'est pas une
affirmation de la prose — c'est une exécution, dans
`tests/recherche/additif/`.

**Un effet de bord qui confirme.** Dans la version concrète, la symétrie exige
un pont d'habit α (`premier₂ ⇒ premier₁` et retour), parce que l'énoncé du
dépôt impose deux graphies de `est_premier`. En abstrait, avec un prédicat
unique, **ce pont disparaît entièrement**. Il n'était donc pas une étape
mathématique : c'était un artefact de notation, et il avait coûté du travail
réel.

**Ce que ça laisse ouvert.** Tout. La conjecture n'a pas avancé d'un pouce, et
ce module dit précisément pourquoi aucune des routes empruntées ne pouvait la
faire avancer. Ce qu'il faudrait est ce que la carte réclame depuis le §7 : une
information sur **quels** entiers sont premiers — c'est-à-dire de
l'arithmétique, la seule chose que ces réductions ne contiennent pas.

