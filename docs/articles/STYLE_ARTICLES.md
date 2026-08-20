# Style des articles — ce qu'on a appris en écrivant A3 (20 août 2026)

**Portée.** Ces règles valent pour A1, A2, A3, A4 et tout ce qui suivra. Elles sont
nées d'un retour de Karl sur A3 : *« l'article est bien organisé, le texte est bien
consistant, mais y a trop de gros pavés, ça donne pas envie de lire »*, complété par
*« si c'est compliqué à lire c'est qu'on a mal compris la chose ; faut souvent aller au
plus simple, mettre des équations, des graphes, expliquer des passages de l'équation »*.

Chaque règle ci-dessous est adossée à une mesure ou à un incident réel. Aucune n'est
une préférence esthétique.

---

## 1. Mesurer la densité AVANT de diagnostiquer

L'explication évidente était « les paragraphes sont trop longs ». **Elle était fausse**,
et la mesure l'a montré en une minute :

| | A3 (dont on se plaignait) | A1 (dont on ne se plaignait pas) |
|---|---|---|
| paragraphes de corps | 72 | 63 |
| longueur médiane | **544 car.** | 652 car. |
| pavés ≥ 800 car. | **14** | 25 |

A3 était donc **déjà moins dense** que A1. Le problème n'était pas le texte, c'était la
**mise en page**. Diagnostiquer à l'œil aurait conduit à charcuter de la prose correcte.

**Outil** : `article/scripts/densite.py` — médiane, maximum, répartition par seuil et les
douze plus gros paragraphes d'un `.tex`. À lancer **avant** toute réécriture motivée par
« c'est illisible » :

```bash
python article/scripts/densite.py article/goldbach/main_fr.tex article/main_fr.tex
```

Il rend un verdict explicite : au-dessus d'une médiane de ~700 caractères, le texte est
en cause ; en dessous, c'est le préambule (§2). ⚠️ Il ne voit **pas** la longueur de
ligne ni l'interligne — c'est-à-dire, très souvent, la vraie cause. Il le dit lui-même
plutôt que de laisser croire qu'il mesure la lisibilité.

*(Il vit dans `article/scripts/` et non `outils_ia/audit/` : c'est un outil de rédaction,
et le dossier d'audit est déjà à 15 entrées pour une limite de 10 — dette signalée, on
ne l'aggrave pas.)*

---

## 2. Les deux réglages typographiques qui font tout

Les deux causes réelles du « pavé », et leur correction :

| cause | avant | après |
|---|---|---|
| ligne trop longue | `margin=2.7cm` → 15,6 cm ≈ **90 caractères** | `textwidth=13.8cm` ≈ **72 caractères** |
| rien entre les paragraphes | `\parskip` = 0 (défaut LaTeX) | `\parskip = .55em plus .15em minus .1em` |

Plus `\linespread{1.06}` et `\parindent{1.1em}`. Le bloc à copier en préambule est en
tête de `article/goldbach/main_fr.tex`, commenté.

**L'optimum de lecture est de 65 à 75 caractères par ligne.** Au-delà, l'œil perd le
début de la ligne suivante et n'importe quel paragraphe devient un bloc gris — quelle
que soit sa longueur. C'est pour ça que la mesure du §1 semblait contredire le ressenti :
les deux articles souffraient, A1 autant que A3.

⚠️ **Ça coûte des pages** : A3 est passé de 16 à 21 pages sans un mot de plus. C'est le
prix, et il est bon à payer. Un article de 16 pages qu'on ne lit pas vaut moins qu'un
article de 21 qu'on lit.

---

## 3. Une preuve qui se raconte en prose doit s'AFFICHER

C'est la règle la plus rentable du lot, et elle vient de Karl : *aller au plus simple,
mettre des équations, expliquer des passages de l'équation.*

Dans un article sur des dérivations certifiées, un paragraphe qui **narre** un calcul est
toujours moins lisible que le calcul **affiché et annoté**. Exemple réel, le lemme du
demi-intervalle de A3 — même contenu, deux rendus :

**Avant** (un pavé de six lignes) :
> « Sa preuve évite entièrement les inégalités strictes en utilisant la comparabilité
> pour ouvrir deux cas, l'existence d'un complément dans le cas `k ≤ m` pour écrire
> `m = k + d`, puis la simplification additive finie sur `k + k = (k+d) + m' = k + (d + m')`
> pour obtenir `k = d + m'`. »

**Après** (un tableau aligné, une justification par ligne) :

```
  k + k  =  m + m'         l'hypothèse
         =  (k + d) + m'   d existe car k ≤ m (Prop. 13 : le complément)
         =  k + (d + m')   associativité itérée
  ─────────────────────────────────────────────────────────
      k  =  d + m'         simplification additive — EXIGE Fini
     m'  ≤  k              Prop. 2 : un sommant est sous la somme
```

Le lecteur voit d'un coup où la garde `Fini` mord — ce que la prose noyait. **Colonne de
droite obligatoire** : chaque ligne dit *pourquoi*, sinon on a déplacé le problème.

**Quand appliquer.** Dès qu'un paragraphe contient trois `=` ou plus, ou décrit une
suite d'étapes. Candidats dans les autres articles : les dérivations de réparation de A1,
la chaîne des organes de A2, les routes de témoins de A3.

---

## 4. Une affirmation chiffrée agrégée appelle une COURBE

Deuxième application du même principe. Si le texte dit « X s'effondre pendant que Y
croît », le lecteur doit le *voir*, pas le croire sur parole.

Exemple : le §6 de A3 affirmait en deux phrases que la densité des premiers tombe
pendant que le nombre de décompositions monte. Une figure à deux axes montre les deux
courbes se croiser, et l'argument est compris en une seconde.

**Protocole** (déjà dans `CLAUDE.md`, ici précisé) :
- matplotlib → PNG, **script de génération versionné à côté du PNG**
  (`article/goldbach/figures/gen_comptage.py` → `comptage.png`) ;
- le script **recalcule les données**, il ne recopie pas des chiffres d'un document ;
- il **imprime les valeurs clés** en fin d'exécution, pour que le texte les cite sans
  les réinventer ;
- la légende dit ce que la figure **ne prouve pas** : « mesure numérique par crible, pas
  une preuve ; aucune de ces valeurs n'entre dans un théorème ».

⚠️ **Trois pièges de mise en page vus le même jour**, tous invisibles dans le log LaTeX
et trouvés en OUVRANT le PNG : une légende posée dans le cadre recouvrait une courbe et
donnait l'illusion d'un trou dans les données ; une grille en deux morceaux laissait une
vraie coupure ; une annotation calée à droite chevauchait la seconde courbe.
**Toujours regarder l'image, jamais se fier au fait qu'elle a été produite.**

---

## 5. Recalculer les chiffres en les intégrant — jamais les recopier

En traçant la courbe du §4, les valeurs mesurées ne correspondaient **pas** à celles que
l'article avait héritées d'un document interne (`0,50 → 0,18` et `2 → 1417` annoncés,
`1,00 → 0,18` et `1 → 1031` mesurés, en paires non ordonnées sur `2k = 4 … 192 152`).
L'écart venait d'une convention de comptage jamais écrite.

**Règle** : tout chiffre d'un article est produit par une exécution faite pour l'article,
et la convention est écrite à côté. Un chiffre repris d'un document interne est un
chiffre non vérifié.

---

## 6. Traduire est le meilleur relecteur mécanique dont on dispose

La traduction française de A3 a fait tomber **quatre restes périmés** qu'aucun grep ni
compilateur n'avait vus : une figure affichant les anciens temps, un verdict qui ne
parlait que de deux réductions sur quatre, une conclusion annonçant « quatre secondes »
au lieu de 110, et deux commentaires d'ancre.

Aucun n'était détectable autrement qu'en lisant chaque phrase. **Traduire force à
relire** — c'est le seul contrôle systématique qu'on ait contre la prose qui ment sur le
dépôt. Faire la traduction *avant* de figer, pas après.

---

## 7. Un signe qu'on écrit est un signe qu'on suppose

⚠️ **Règle de RÉDACTION, pas de contenu d'article.** Elle appartient à ce document et
n'a rien à faire dans le texte publié : le lectorat d'un article de méthodes formelles
sait qu'on n'emploie pas un symbole hors de la théorie qui l'introduit. L'écrire noir
sur blanc dans l'article est condescendant. Ce qui compte est que l'article le
**fasse**, pas qu'il l'annonce. *(A3 avait une Remarque là-dessus ; elle a été
supprimée.)*

**Corollaire, et il se balaie mécaniquement : aucune notation ne doit être employée
avant d'être introduite.** Karl a relevé trois fautes de cette famille une par une ;
corriger les trois n'était que traiter des instances. `article/scripts/notations.py`
traite la classe — il donne, pour chaque notation en mode mathématique, sa première
utilisation et le premier endroit qui l'introduit, et classe en `JAMAIS` / `APRÈS` / `OK`.

```bash
python article/scripts/notations.py article/main.tex article/goldbach/main_fr.tex
```

Ce qu'il a trouvé au premier passage, et qu'aucune relecture n'avait vu : **A3 employait
`⊢` d'un bout à l'autre sans jamais l'introduire** — A1 le pose, A3 déférait au compagnon
sans le dire. Et `□` y était utilisé sans qu'on précise ce qu'il marque.

⚠️ **L'outil range, il ne tranche pas**, et il le dit lui-même : il ne comprend pas le
texte, sa liste `STANDARD` exempte les notations usuelles à la main, et il renonce
explicitement à suivre les `$…$` multilignes — une désynchronisation ferait prendre des
pages de prose pour des formules, et il vaut mieux qu'il sous-signale que qu'il invente.
Le jugement reste humain ; l'outil garantit seulement que rien n'échappe à l'examen.

La règle, posée par Karl le 20 août après deux erreurs relevées sur A3 : **utiliser un
signe, c'est déclarer qu'on travaille dans une théorie qui le possède.** Elle est facile
à enfreindre sans s'en apercevoir, et le noyau ne l'attrape pas — il vérifie des
dérivations, pas le sens qu'on prête aux symboles dans une phrase de prose.

Les deux fautes réelles, à ne pas refaire :

- **`=` hors d'une théorie égalitaire.** L'article écrivait `τx(∈ x y) = τ ∈ ▢ y`. Or
  `=` est un signe relationnel de poids 2 introduit en **E I.38 (§I.5)**, avec les
  schémas qui le gouvernent ; il n'existe pas au niveau §I.1 où vivent les assemblages.
  Ce qu'on voulait dire était une **identité métalinguistique** — deux notations
  désignent la même suite de signes et de liens. Écrire « *est l'assemblage* », pas `=`.
  (Les `=` de l'arithmétique cardinale sont légitimes : on y est dans la théorie des
  ensembles, qui est égalitaire.)

- **`τx(A)` écrit comme s'il contenait encore `x`.** Former `τx(A)` lie chaque occurrence
  de `x` au `τ` **puis la remplace par ▢** : le terme ne contient plus la lettre
  (E I.16 L.1-4, exemple L.5). Donc jamais `φ(τx φ)` — ni la notation fonctionnelle, ni
  le `x` fantôme. La forme correcte est la substitution `(τx(R) | x) R`.

**Le réflexe à avoir** : avant d'écrire un symbole dans une section qui parle du niveau
logique, se demander *à quel chapitre du livre ce signe est-il introduit, et suis-je déjà
dedans ?* Les marqueurs `@livre` du dépôt répondent en une recherche.

---

## 8. La règle d'or, rappelée

Elle précède tout le reste et ne change pas : **chaque phrase d'un article doit être
adossée à un objet du dépôt** — théorème, mesure, événement, source. Une affirmation sans
ancre est une docstring qui ment, en public.

**Une erreur de brouillon n'est pas de la matière d'article — on la retire.** Deux
réflexes fautifs, vus le même jour sur la même remarque de A3 :

1. écrire « *on lit parfois* $(\exists x)\varphi(x) = \varphi(\tau x\varphi)$ » alors que
   personne d'autre ne l'avait écrit — c'était nous. Une affirmation sur ce que contient
   la littérature est une affirmation comme une autre : sans référence vérifiée, elle
   n'a pas sa place ;
2. corriger l'attribution puis **garder la remarque** en la déguisant en avertissement
   pédagogique. Elle ne l'était pas. Le lecteur n'a que faire d'une notation qu'on a mal
   écrite dans un brouillon ; la remarque a été supprimée.

⚠️ **Ne pas confondre avec le §5.3 de A3**, qui raconte une surdéclaration de notre fait
et la garde. La différence est nette : là, l'erreur avait *propagé dans le dépôt* et sa
détection dit quelque chose sur la méthode — c'est un résultat. Ici, c'était une coquille
de rédaction rattrapée avant publication : ça n'apprend rien à personne. **Publier ses
erreurs quand elles enseignent, les effacer quand elles ne sont que du bruit.**

Corollaire acquis en écrivant A3 : le noyau garantit la *soundness*, **jamais** la
fidélité de ce qu'on écrit à côté. Aucun test n'attrape une phrase fausse sur le code.
Une surdéclaration a survécu sept jours dans une docstring, s'est propagée dans un
document de carte, et allait entrer dans la section centrale de A3 — elle a été prise en
relisant le code contre la prose, pas par un outil. Cette relecture-là est obligatoire
avant tout gel.
