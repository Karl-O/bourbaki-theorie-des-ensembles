# Étude de José Grimm (projet Gaia, Bourbaki en Coq) — notes pour V9

*Lecture ciblée des 4 sources locales (`sources/grimm_gaia/`), 26 juil. 2026.
Aucune modification de code. Protocole `@source` : toute affirmation externe est
calée à la page PDF, comme `@livre` pour Bourbaki.*

Sources et volumétrie :

| fichier | pages PDF | contenu |
|---|---|---|
| `RR-6999-v7.pdf` | 217 | Rapport INRIA, **E.I + E.II** (logique formelle, ensembles, corresp., familles, produits, équivalences) + exercices + annexes |
| `RR-7150-v10.pdf` | 830 | Rapport INRIA, **E.III** (ordres, bons ordres, cardinaux, entiers, ensembles infinis) + ordinaux/CNF/cofinalité + ℤ,ℚ,ℝ + 180 p. d'exercices + chapitre « compatibilité » |
| `thalion,+jfra1.pdf` | 48 | Article JFR 2010 — condensé de RR-6999, **le meilleur texte sur les axiomes et le τ** |
| `thalion,+jfra2.pdf` | 52 | Article JFR 2016 — condensé de RR-7150 côté nombres, **conclusion avec les divergences assumées** |

Les 4 PDF ont une couche texte exploitable (aucun scan).

---

## A. RÉDACTION / STRUCTURE — ce qui est copiable pour `V9/rapport/`

### A1. Découpage : calqué sur le livre, pas sur le code
Un **chapitre de rapport = une section de Bourbaki**, avec **le titre de Bourbaki** :
« Each of the six sections of Bourbaki gives a chapter in this report (we use the same
titles as in Bourbaki) ». `@source sources/grimm_gaia/RR-6999-v7.pdf p.7 §1.2`
Le découpage du **code** suit le même axe (`set5.v`…`set10.v` = §III.1 à §III.6), et
le rapport annonce en tête quels fichiers il décrit. `@source sources/grimm_gaia/RR-7150-v10.pdf p.6 §1.2`
Deux rapports pour un livre : RR-6999 = chap. I–II, RR-7150 = chap. III (+ ℤ, ℚ, ℝ hors
Bourbaki). Le chap. IV n'est couvert par aucun (cf. B15).

### A2. Gabarit récurrent d'une notion
1. **prose** : énoncé Bourbaki *cité entre guillemets français* avec sa référence page
   (« Proposition 2 in [4, p. 160] says that… ») ;
2. **commentaire d'écart** : ce que Grimm change et pourquoi (« Bourbaki assumes Xι ⊂ X,
   which is not needed », `@source sources/grimm_gaia/RR-6999-v7.pdf p.86 §4.3`) ;
3. **preuve informelle en français mathématique** — c'est la partie qui porte l'information ;
4. **bloc de code sans preuve** (`Definition` / `Lemma` / `Theorem` seulement).
   « The document gives no proofs, except for the exercises. In order to show how difficult
   some theorems are, the numbers of lines of the proof is sometimes indicated in a comment. »
   → marqueurs `(* 58 *)`, `(* 250 *)` accolés aux énoncés difficiles. `@source sources/grimm_gaia/RR-6999-v7.pdf p.22 « Notes »` ; exemple `(* 250 *)` sur Zermelo `@source sources/grimm_gaia/RR-7150-v10.pdf p.65 §3.3`

### A3. Renvois au livre
Convention déclarée une fois : « A reference of the form E.II.4.2 refers to [2], Theory of
Sets, Chapter 2, section 4, subsection 2 ». Et **toute** proposition citée porte sa page
(`[4, p. 179]`). `@source sources/grimm_gaia/RR-6999-v7.pdf p.22 « Notes »`

### A4. Conventions de nommage (table donnée en intro, avant tout code)
- préfixe `OS_` / `CS_` / `NS_` = « cet objet est un ordinal / cardinal / entier » ;
- suffixe `R`, `S`, `A`, `T` = réflexif, symétrique, antisymétrique, transitif ;
- suffixe `C`, `A`, `D`, `I` = commutatif, associatif, distributif, involutif ; `M` = monotonie
  (`csum_Mlele`) ; suffixe `2` = version binaire ; suffixe `P` = énoncé sous forme d'équivalence ;
- racine = l'opération (`csum`, `cprod`, `oprod`, `binom`) → tous les lemmes d'une opération
  partagent le même préfixe et se cherchent par complétion. `@source sources/grimm_gaia/RR-7150-v10.pdf p.8 §1.4`

### A5. Exercices : chapitre séparé, gabarit strict
Un chapitre « Exercices », une **section par section du livre**, et pour chaque exercice :
énoncé Bourbaki **verbatim** → paragraphe « **Note.** » (ambiguïtés, hypothèses manquantes,
erreurs, « points (c) and (d) remain to do ») → « **Solution.** » (preuve informelle) → code. `@source sources/grimm_gaia/RR-7150-v10.pdf p.548-549 §13.2` ; `@source sources/grimm_gaia/RR-6999-v7.pdf p.141 §7.2`
Taux affiché honnêtement : « There are many exercises, two third of them are solved. » `@source sources/grimm_gaia/RR-7150-v10.pdf p.7 §1.2`

### A6. Statistiques de couverture
Grimm compte **par fichier et par version**, y compris les régressions :
« there are 171 lemmas in jset, 98 in jfunc, 424 in set2 … In Version 3, many trivial theorems
have been removed, so that these numbers are respectively 202, 397, 338 and 242. » `@source sources/grimm_gaia/RR-6999-v7.pdf p.22 « Notes »`
Bilans globaux : partie 1 = 6 fichiers, 400 définitions, 1600 théorèmes, 53 tactiques,
18 000 lignes (22 000 après passage à ssreflect, +8 % de caractères) `@source sources/grimm_gaia/thalion,+jfra1.pdf p.46 §6` ;
partie 2 = 8 fichiers, 360 définitions, 71 notations, 2700 lemmes, 34 000 lignes = **20 % de Gaia** `@source sources/grimm_gaia/thalion,+jfra2.pdf p.49 §6`.

### A7. Annexes (chapitre « Summary » / « Compatibility »)
1. **liste intégrale des schémas S1–S8 et axiomes A1–A5**, puis **la même liste en ZF**
   (B0–B4, SS, SC, AC, AF) avec les commentaires de correspondance ; `@source sources/grimm_gaia/RR-6999-v7.pdf p.188-189 §8.1-8.2`
2. **« Changes from previous versions »** : le code *supprimé* est conservé **en commentaire**
   avec la raison de sa suppression ; `@source sources/grimm_gaia/RR-6999-v7.pdf p.189-193 §8.3` et `@source sources/grimm_gaia/RR-7150-v10.pdf p.776 et p.779 (« Changes in Version 6 / 9 »)`
3. **liste des tactiques** maison ; `@source sources/grimm_gaia/RR-6999-v7.pdf p.194-199 §8.4`
4. **« List of Theorems »** = table `énoncé numéroté de Bourbaki → nom Coq → page du rapport →
   citation exacte entre guillemets français`, section par section. **C'est le modèle exact de nos
   manifestes `LIVRE.md`.** `@source sources/grimm_gaia/RR-6999-v7.pdf p.199-202 §8.5`
5. index notations/définitions. `@source sources/grimm_gaia/RR-6999-v7.pdf p.202 §8.6` et `@source sources/grimm_gaia/RR-7150-v10.pdf p.782`
6. un **chapitre entier « Compatibility »** archive les preuves *alternatives* et les théorèmes
   *retirés* : 4 preuves différentes de Cantor-Bernstein, l'ancienne construction des
   pseudo-ordinaux, les théorèmes déplacés. `@source sources/grimm_gaia/RR-7150-v10.pdf p.730 ch.14`

---

## B. DIFFICULTÉS RENCONTRÉES ET SURMONTÉES

### B1. Le τ de Hilbert n'existe pas en Coq
**Problème.** Les quantificateurs de Coq ne sont pas définis via τ ; de `∃x, p x` on ne peut pas
extraire un témoin (« there is no function y → x »). `@source sources/grimm_gaia/RR-6999-v7.pdf p.17 §1.5`
**Solution.** Axiome `chooseT : ∀ (p:t→Prop), inhabited t → t` + `chooseT_pr : ex p → p (chooseT p q)`
(2ᵉ argument = preuve que le type est habité, pour couvrir le type vide) ; puis
`choose p := chooseT (refined_pr p) …` où `refined_pr` impose **`choose p = ∅` quand aucun témoin
n'existe** (le terme devient total) ; puis `rep X := choose (fun y => inc y X)`. `@source sources/grimm_gaia/RR-6999-v7.pdf p.25-27 §2.1-2.2` et `p.190 §8.3` ; `@source sources/grimm_gaia/thalion,+jfra1.pdf p.15 §2.3, p.19 §3.1`
**Écart assumé, dit explicitement** : « Note that if p and q are equivalent properties, we do not
pretend that C(p) = C(q). **Thus C(p) is not equivalent to Bourbaki's τ.** » `@source sources/grimm_gaia/RR-6999-v7.pdf p.27 §2.2`
**Chez nous.** τ est natif ⇒ problème absent. La leçon transposable est la **totalisation par
valeur par défaut** : un terme défini pour tous les arguments supprime des hypothèses de
non-vacuité dans des dizaines d'énoncés en aval.

### B2. Le schéma S7 est FAUX chez Grimm
**Problème/constat.** Dans le chapitre « Exercices », il démontre S1–S6, S8, A1–A4 dans son
cadre, et écrit sèchement : « **Scheme S7 does not hold.** » `@source sources/grimm_gaia/RR-6999-v7.pdf p.138 §7.1`
Confirmé en conclusion : « Scheme S7 is not an axiom in Gaia; in other terms, ∀x, P ⇔ Q does not
imply τₓP = τₓQ. » `@source sources/grimm_gaia/thalion,+jfra2.pdf p.50 §6`
**Conséquence en cascade** : partout où Bourbaki définit par τ (cardinaux, ordinaux, types
d'ordre), Grimm **doit** changer de définition (→ B6).
**Chez nous.** C'est notre avantage comparatif principal : avec τ natif au niveau des assemblages,
S7 est disponible et on peut suivre Bourbaki *littéralement* là où Grimm dévie. À documenter
comme tel dans le rapport.

### B3. Le représentant `rep` remplace τ presque partout
**Problème.** Beaucoup d'usages de τ chez Bourbaki servent seulement à nommer un élément d'un
ensemble non vide.
**Solution.** `r(X) := τ_z(z ∈ X)` (« the representative »), qui satisfait `r(X) ∈ X` dès que X ≠ ∅ ;
pour une relation d'équivalence, `x = r(C(a))` et **S7 devient inutile** pour prouver
`P(a,b) ⟺ r(C(a)) = r(C(b))`. « Whenever possible we shall use r rather than τ. There are two
exceptions: for defining cardinals and ordinals. » `@source sources/grimm_gaia/RR-6999-v7.pdf p.18 §1.5`

### B4. Définition par cas sans `if-then-else`
**Problème.** Pas de booléens décidables ⇒ pas de `if P then a else b`.
**Solution.** `by_cases`/`Yo(P,x,y)` : on applique τ à la relation « pour toute preuve p de P,
y = A(p) ; pour toute preuve q de ¬P, y = B(q) », légitimée par le tiers exclu ; la
*proof irrelevance* (admise ou non) rend le résultat indépendant de la preuve choisie. `@source sources/grimm_gaia/RR-6999-v7.pdf p.19-20 §1.5` (définition `Yo` `p.26 §2.1`, historique `p.190 §8.3`)
Exemple d'usage pour éviter `if-then-else` dans une définition d'ensemble :
`{t ∈ U, U ≠ I ⇒ t ∉ I}` — « this strange definition avoids the if-then-else construction ». `@source sources/grimm_gaia/RR-6999-v7.pdf p.38 §2.9`

### B5. ⋂ de la famille vide — **notre mur `AXIOME_INTER_FAM`**
**Problème.** Bourbaki définit ⋂ des Xι ⊂ E comme partie de E ; si I = ∅ l'intersection vaut E,
donc **dépend du contexte**.
**Solution de Grimm (à copier).** Définir l'intersection par **séparation dans la réunion** :
`intersection x := Zo (union x) (fun y => forall z, inc z x -> inc y z)`, d'où `setI_0 :
intersection emptyset = emptyset`. Commentaire : « If the family is empty, then Bourbaki defines
the intersection to be E. **We do not like this definition, since it depends on the context.**
Taking for E the union of the family solves the problem. » `@source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7` ; reformulé `@source sources/grimm_gaia/thalion,+jfra1.pdf p.29 §3.4`
Il conserve ensuite l'hypothèse `I ≠ ∅` **uniquement dans les énoncés qui en ont besoin**
(compléments d'unions/intersections, Prop. 5). `@source sources/grimm_gaia/RR-6999-v7.pdf p.83 §4.1 et p.86 §4.3`
**Chez nous.** Exactement notre situation : on a un **axiome** restreint à I ≠ ∅ là où Grimm a une
**définition totale**. Passer de l'axiome à la définition par séparation supprime le mur.

### B6. Cardinaux : abandon de τ pour von Neumann
**Problème.** `Card(X) = τ_Z(Eq(X,Z))` est **indécidable** : pour A = {∅}, « it is impossible to
prove a = A or a ≠ A (non-definiteness of τ) ». `@source sources/grimm_gaia/RR-7150-v10.pdf p.72 ch.4 (intro)`
**Solution.** Ordinal au sens **de Bourbaki lui-même** (« any transitive subset of E is either E or
an element of E », `ordinalp`), cardinal = **plus petit ordinal équipotent**. Alors :
`x ≤card y` ⟺ `x ⊆ y` ⟺ `x ≤ord y`, l'antisymétrie vient de Cantor-Bernstein, et le Théorème 1
(les cardinaux sont bien ordonnés) « is trivial in our framework ». `@source sources/grimm_gaia/RR-7150-v10.pdf p.74 §4 (déf.), p.91-92 §4.2 (ordre)`
**Chez nous.** À arbitrer. Le coût de garder `Card = τ` est mesurable dans son texte : tout ce
qui suit (sup, comptages, ω) devient trivial en von Neumann. Si on garde τ, il faut au minimum
importer le lemme-pivot de B7.

### B7. Sup d'une famille de cardinaux — **notre mur « sup cardinal absent »**
**Problème.** Bourbaki (Prop. 2, [4, p. 160]) prouve l'existence du sup par « a strange argument »
(il exhibe un E tel que aι ⊂ E, prend a = Card E, se ramène à `C_a` bien ordonné à plus grand élément). `@source sources/grimm_gaia/RR-7150-v10.pdf p.95 §4.2 « Supremum of a family of cardinals »`
**Solution 1 (von Neumann).** `\csup := union` tout court ; `\osup := union` aussi. `@source sources/grimm_gaia/RR-7150-v10.pdf p.10 §1.4` et `p.81 §4 « Ordinal supremum »`
Preuve que ⋃A est un cardinal : si b équipotent à a=⋃A avec b <ord a, il existe c ∈ A avec
b <ord c ≤ord a, d'où trois cardinaux égaux et c ≤ord b, absurde. Lemmes livrés :
`CS_sup`, `card_ub_sup`, `card_sup_ub`, `card_sup_image`, `cardinal_supremum1/2` (= Prop. 2). `@source sources/grimm_gaia/RR-7150-v10.pdf p.95 §4.2`
**Solution 2 (le lemme-pivot réutilisable même sans von Neumann).**
`cardinals_le a := Zo (osucc a) cardinalp` **et** `cardinals_le_alt : cardinals_le a =
fun_image (\Po a) cardinal` — « Note that Ca is the set of all cardinals in a⁺ (our definition)
**as well as the set of all card(t), where t ∈ P(a) (the Bourbaki definition)** ». `@source sources/grimm_gaia/RR-7150-v10.pdf p.95 §4.2`
**Chez nous.** C'est exactement la brique manquante : « l'ensemble des cardinaux ≤ a existe, car
c'est l'image de P(a) par Card ». Elle est constructible **avec τ** et débloque le sup sans changer
notre définition de cardinal.

### B8. Réunion filtrante de bons ordres — **notre mur « Lemme 1 »**
**Problème.** Prouver que la réunion d'une famille compatible de bons ordres est un bon ordre.
**Solution de Grimm (`Zermelo_aux`).** Il introduit deux outils :
- `Q(G)` : G est un bon ordre sur A ⊆ E tel que **tout segment `S_a` de G vérifie `S_a ∈ S` et
  `p(S_a) = a`** (l'ordre « code » sa propre construction) ;
- `G ⊗ G'` := l'ensemble des x où les deux segments initiaux **coïncident** (comme ensembles *et*
  comme ordres) ; il montre que c'est un segment des deux ;
- `q(G,G')` := « A ⊆ A', les ordres coïncident sur A, et A est un **segment** de G' ».
Alors `Q(G) ∧ Q(G')` ⇒ `q(G,G') ∨ q(G',G)`, donc la famille est **totalement ordonnée par
prolongement**, donc **la réunion est un ordre qui satisfait encore Q**. Coût annoncé : `(* 250 *)`. `@source sources/grimm_gaia/RR-7150-v10.pdf p.64-65 §3.3`
Réemployé tel quel pour Zorn **sans axiome du choix** (`Zorn_aux_eff` : « this result is
independent of the axiom of choice »). `@source sources/grimm_gaia/RR-7150-v10.pdf p.65-66 §3.4`
Variante « quotient de bons ordres sans AC » (utile si on refuse le représentant) :
`worders E`, `worders_eq`, `worders_quo`, avec re-démonstration à la main de
« a ∈ x ∈ Q ⇒ x = class a » « because the standard proof uses the representative of x, hence AC ». `@source sources/grimm_gaia/RR-7150-v10.pdf p.733-734 §14.2`
**Chez nous.** L'ordre des lemmes (⊗ → segment commun → comparabilité → réunion) est transposable
tel quel ; c'est le squelette qui manque à notre Lemme 1.

### B9. Récursion transfinie C60 / C62 / C63 — **notre chantier `c62/fonction_recursion_NN`**
**Problème.** C60 énonce l'existence d'une **fonction surjective** f avec `f(x) = T(f|Sx)` ;
l'unicité passe, l'existence est le point dur.
**Solution, en 4 temps.**
1. **Passer d'abord par les graphes** : `transfiniteg_def` (graphe fonctionnel de domaine E) et
   prouver l'équivalence avec la version fonction surjective (`transfinite_def_prop1/2`). Motif :
   « a surjective function is uniquely determined by its graph ».
2. **Unicité** : plus petit élément où les deux diffèrent.
3. **Existence** : (a) prolongement d'un segment `S` à `S ∪ {x}` (`transfinite_aux3`) ;
   (b) **la réunion des solutions sur une famille de segments est une solution**
   (`transfinite_aux2`, `(* 58 *)`) — la preuve utilise l'unicité pour montrer que `f_S` est la
   restriction de `f_S'` ; (c) AC pour choisir `f_S`, puis stabilité par réunion ⇒ E ∈ S.
4. **Variante « stable » sans AC** : si `T(h) ∈ F` pour toute h à valeurs dans F, alors la cible est
   ⊆ F (`transfinite_definition_stable`). « Note: in this special case, the axiom of choice is not needed. » `@source sources/grimm_gaia/RR-7150-v10.pdf p.61-64 §3.2`
**C62/C63 (récurrence sur ℕ).** Grimm reconstruit la preuve Bourbaki : `M(u)` = borne sup du
domaine de u, `R(y,u)` : « u = ∅ et y = a, ou u ≠ ∅ et y = S(u(M(u))) », `T(u) = τ_y R(y,u)`.
Il signale que Bourbaki renvoie en note de bas de page à une borne sup *prolongée aux ensembles
non majorés* et **donne deux façons de la définir**, dont une **sans τ** :
`N'(u)` = les plus petits majorants, `M(u) = ⋃N'(u)`. Puis il simplifie :
`M'(u) := cardinal (source u)` (égal à M(u) pour les cardinaux de von Neumann), et
`T u := Yo (source u = ∅) a (h (cpred (source u)) (Vf u (cpred (source u))))`. `@source sources/grimm_gaia/RR-7150-v10.pdf p.201-203 §7.2`
**Alerte utile** : la méthode Bourbaki pour `f(n+1) = h(n, f(n))` **exige d'exhiber un ensemble E
stable par h**, ce qui est pénible (son exemple `z_{n+1} = x_{n+1}^{z_n}` demande de construire un
ensemble énorme). Sa méthode par terme fonctionnel évite ce détour : « Our method is better, since
there is no need to introduce this set E. » `@source sources/grimm_gaia/RR-7150-v10.pdf p.202 §7.2`

### B10. Opérations partielles rendues totales par convention
Division euclidienne : pour que `a = bq + r` vaille **toujours**, il pose `q = 0, r = a` quand `b = 0`
(« In order to simplify proofs… This means that a = bq+r holds in any case »), la divisibilité
n'étant définie que pour b ≠ 0. `@source sources/grimm_gaia/RR-7150-v10.pdf p.756 §14.6`
Même recette pour la soustraction cardinale (`card_sub` = 0 hors domaine). `@source sources/grimm_gaia/RR-7150-v10.pdf p.755 §14.6`

### B11. Comptages combinatoires — **notre mur `Card{injections}`, binomial**
**Le lemme-pivot unique : le principe du berger.**
`card_partition_induced : cardinal A = csumb B (fun x => cardinal (Vfi1 f x))` puis
`shepherd_principle : (∀x ∈ target f, card(f⁻¹⟨{x}⟩) = c) → card(source f) = card(target f) × c`.
Grimm note que la surjectivité exigée par Bourbaki (Prop. 9, [4, p. 179]) est **superflue**. `@source sources/grimm_gaia/RR-7150-v10.pdf p.152 §6.8`
**Nombre d'injections** (Prop. 10) : récurrence sur A ; l'application « restriction »
`G'(A∪{a} → B) → G(A → B)` a des fibres de cardinal `n − m` constant ⇒ berger ⇒ factorielle
décroissante `n^(m) := ∏_{i<m}(n−i)`, puis `card_injections_spec : n!/(n−m)!`. Les permutations
en découlent (`card_permutations = n!`). `@source sources/grimm_gaia/RR-7150-v10.pdf p.153-154 §6.8`
**Nombre de partitions à cardinaux imposés** (Prop. 11) : même berger, appliqué à
`Φ : permutations(E) → partitions_pi(p,E)`, `Φ(g)_i = g⟨f_i⟩`, dont les fibres sont `∏ Q(f_i)`. `@source sources/grimm_gaia/RR-7150-v10.pdf p.157-158 §6.8`
**Binomial** : défini par double récurrence via `induction_term` produisant un **graphe fonctionnel
sur ℕ**, `binom n m := Vg (induction_term … n) m` — et Grimm reconnaît lui-même que
« the definition is a bit obscure ». Pascal est ensuite prouvé par récurrence. `@source sources/grimm_gaia/RR-7150-v10.pdf p.162 §6.8` et `p.166 §6.8`
**Stratégie parallèle** qu'il utilise beaucoup : définir sur le type `nat` de Coq (donc avec la
bibliothèque existante), puis **transporter** via `nat_to_B` vers les cardinaux de Bourbaki. `@source sources/grimm_gaia/RR-7150-v10.pdf p.7 §1.2` et `p.756 §14.6`
**Chez nous.** Un seul théorème (le berger) fait tomber `Card{injections}`, les permutations et les
partitions. Nos comptes opaques sont opaques parce que ce pivot manque.

### B12. Familles indexées, ∑/∏ de cardinaux — **notre mur « fonctorialité indexée du produit »**
**Définition directe** : `csum x := cardinal (disjointU x)`, `cprod x := cardinal (productb x)`,
plus les variantes `csumb I f` / `cprodb I f` indexées par un terme.
Conséquence : la Prop. 4 (§III.3.3 : `card(∑Eι) = ∑card(Eι)`) est immédiate —
`csum_pr0 : csumb I f = csumb I (fun i => cardinal (f i))`, `csum_pr`, `cprod_pr`. `@source sources/grimm_gaia/RR-7150-v10.pdf p.96-97 §4.3`
**Changement d'indice sans objet-fonction** : `quasi_bij f I J` = un *terme fonctionnel* + 3
propriétés (f envoie I dans J, injectif sur I, surjectif sur J) ⇒ `csum_Cn2 : csumb J g =
csumb I (fun z => g (f z))` (idem produit). C'est la version « sans emballage » de la Prop. 5. `@source sources/grimm_gaia/RR-7150-v10.pdf p.98 §4.3`
Associativité/commutativité générales : `csum_Cn`, `csum_An` (par partition de l'index),
`cprodDn` (distributivité produit/somme), puis `csum_An2` (échange de deux sommations) obtenu
en appliquant le cas général à I × J avec les deux projections comme partitions. `@source sources/grimm_gaia/RR-7150-v10.pdf p.97-98 §4.3`
Côté ensembles (E.II.5), l'extension aux produits est traitée par
`ext_map_prod` + `ext_map_prod_compose` (Prop. 11), avec preuve **directe** de l'injectivité
au lieu de l'inverse à gauche de Bourbaki (« because it is easier »). `@source sources/grimm_gaia/RR-6999-v7.pdf p.110-111 §5.7`

### B13. Correspondances vs graphes — **notre mur « forme graphe des bijections »**
**Constat frontal de Grimm** : « Our work shows that the **Bourbaki notion of correspondence is an
unnecessary complication**: in theory, an order (or an equivalence) is a correspondence, in
practice it is just a graph. The other use of correspondences is to define functions; but it
suffices simply to say that a function is a triple, formed of a source, a target and a graph. » `@source sources/grimm_gaia/thalion,+jfra1.pdf p.46 §6`
Application : une équivalence **est** un graphe (« this differs from Bourbaki's definition, where an
equivalence is a correspondence ») `@source sources/grimm_gaia/RR-6999-v7.pdf p.114 ch.6` ; et la Prop. 1
de §II.6.1 est prouvée « for graphs rather than correspondences » `@source sources/grimm_gaia/RR-6999-v7.pdf p.117 §6.1`.
Il analyse aussi les **deux lectures possibles** de « f est une bijection de A sur B » (triplet
existentiel vs prédicat sur le triplet) et montre qu'elles donnent des assemblages différents mais
**égaux**, la seconde étant la seule praticable pour la composition. `@source sources/grimm_gaia/RR-7150-v10.pdf p.506-507 §12.1`

### B14. Quotients — **notre mur « infra E/R-iso »**
Chaîne de briques, dans l'ordre :
`substrate r` → `class r x := fun_image (Zo r (fun z => P z = x)) Q` → `quotient r` → `classp r x`
(prédicat « x est une classe ») → `canon_proj r := Lf (class r) (substrate r) (quotient r)` (surjective)
→ `rep` → `section_canon_proj r := Lf rep (quotient r) (substrate r)` (**inverse à droite** de la
projection) → `compatible_with_equiv` → **`fun_on_quotient r f := f ∘ (section_canon_proj r)`**. `@source sources/grimm_gaia/RR-6999-v7.pdf p.118-120 §6.2` et `p.125-127 §6.5`
**Le point décisif** : l'application induite sur le quotient n'est pas obtenue par une propriété
universelle mais **par une formule** (`x̄ ↦ f(rep x̄)`), et l'unicité
(`exists_unique_fun_on_quotient`) est prouvée ensuite. Idem pour le double quotient :
`fun_on_quotients r r' f := (canon_proj r' ∘ f) ∘ section_canon_proj r`, avec le carré commutatif
`canon_proj r' ∘ f = fun_on_quotients r r' f ∘ canon_proj r`. `@source sources/grimm_gaia/RR-6999-v7.pdf p.126-128 §6.5`
Il signale au passage que **le critère C55 de Bourbaki est mal énoncé** (« The correct statement
would be: R⟨x,y⟩ if and only if x ∈ E and y ∈ E and p(x) = p(y). The proof is a bit strange »). `@source sources/grimm_gaia/RR-6999-v7.pdf p.120 §6.2`

### B15. Chapitre IV (structures), CST1/CST2 — **NON TRAITÉ par Grimm**
« Bourbaki has a whole Chapter of Book I that deals with structures. Its definitions are so far
from the common use that **nobody (even Bourbaki himself) uses them**; an implementation of these
ideas in Gaia has started. […] This idea seems nice and effective but **only partially implemented
in Gaia for lack of time**. » `@source sources/grimm_gaia/thalion,+jfra2.pdf p.3 §1.2`
Discussion du problème (σ-morphismes, ordre comme structure, transport à un monoïde ordonné) : `@source sources/grimm_gaia/RR-6999-v7.pdf p.6 §1.1`
**Chez nous.** Aucun modèle à copier pour CST1/CST2 : c'est un terrain où V9 peut être premier —
et où le journal du « pourquoi » (mémoire *but final*) a le plus de valeur.

### B16. Erreurs signalées **dans** Bourbaki (à intégrer à la fidélité @livre)
- Le terme (\*) censé désigner **1** (E.III p.158) est **faux** : l'injectivité de u manque, il décrit
  une surjection. Et l'estimation « plusieurs dizaines de milliers de signes » est fausse : la taille
  réelle est **4,52·10¹²** signes pour (\*) et **18,1·10¹²** pour la version corrigée (179 618 517 981
  liens pour (\*)). `@source sources/grimm_gaia/thalion,+jfra1.pdf p.1 §1.1` ; `@source sources/grimm_gaia/RR-7150-v10.pdf p.508-509 ch.12` et `p.516-517 §12.2`
- « Bourbaki pretends that a finite ordered set has a maximal element, which is true only if the set
  is non-empty ». `@source sources/grimm_gaia/thalion,+jfra1.pdf p.3 §1.5`
- Éd. anglaise : `1≤i≤j<n` au lieu de `1≤i<j≤n` p.182 ; `X` au lieu de `x` dans les preuves de C26/C27
  p.37 ; définition de « partition » différente entre éditions FR et EN (sets non vides ou non). `@source sources/grimm_gaia/thalion,+jfra1.pdf p.3 §1.5`
- Prop. 5 §II.4.3 : l'hypothèse `Xι ⊂ X` est inutile. `@source sources/grimm_gaia/RR-6999-v7.pdf p.86 §4.3`
- Exercices : « as stated above, the formula is wrong; we have to assume H non-empty » `@source sources/grimm_gaia/RR-7150-v10.pdf p.664` ; « Note. Statement (b) is wrong » `@source sources/grimm_gaia/RR-7150-v10.pdf p.574` ; coquilles ω(ξ)/w(ξ) `@source sources/grimm_gaia/RR-7150-v10.pdf p.693` ; « the last G should be replaced by F. This is a
  misprint of the French Edition » `@source sources/grimm_gaia/RR-7150-v10.pdf p.702`.

### B17. Les axiomes ajoutés (liste exacte, à comparer à nos 22)
`Ro : ∀ x:Set, x → Set` + `R_inj` (injectivité) ; `extensionality` ; `chooseT` + `chooseT_pr` ;
`IM` + `IM_P` (remplacement, « more powerful than S8 ») ; `p_or_not_p` (tiers exclu) ;
`arrow_extensionality`. `@source sources/grimm_gaia/RR-6999-v7.pdf p.25-26 §2.1` ; `@source sources/grimm_gaia/thalion,+jfra1.pdf p.14-16 §2.3`
Retirés en cours de route, **et documentés comme tels** : `iff_eq` (P⇔Q ⇒ P=Q) « removed in Version 5 » ;
`proof_irrelevance` et `prod_extensionality` mis en commentaire ; les axiomes `prop_realization` /
`true_proof_realization_empty` de Simpson (qui faisaient `R 2 = Prop` !) abandonnés. `@source sources/grimm_gaia/RR-6999-v7.pdf p.19 §1.5` et `@source sources/grimm_gaia/thalion,+jfra1.pdf p.16 §2.3`

### B18. Performance
« Coq was much slower on Q than on Z » — cause : la taille des formes normales explose (le gcd
apparaît 22 fois dans une somme réduite). Remèdes appliqués : sortir les théorèmes de la base
`auto`, supprimer les bases secondaires, rendre la fonction cardinal **opaque** via `Module Type`. `@source sources/grimm_gaia/thalion,+jfra1.pdf p.8 §1.8` ; `@source sources/grimm_gaia/thalion,+jfra2.pdf p.49 §6`
Symptôme jumeau de nos « tests cardinaux 13–18 min ».

---

## C. DIVERGENCES DE FOND AVEC V9

| | Grimm (Gaia) | Nous (V9) |
|---|---|---|
| τ | **simulé** par `chooseT`, non extensionnel | **natif** au niveau des assemblages |
| S7 | **faux** | disponible |
| quantificateurs | primitifs Coq, typés, α-conversion | définis via τ, pas d'α-conversion (pas de x dans τₓR) |
| cardinaux | von Neumann (par nécessité) | τ possible (à arbitrer) |
| axiome de l'infini | **gratuit** (`nat` est un ensemble) | à poser (A5) |
| noyau | CIC de Coq + 6 axiomes | LCF Python |
| fidélité | à l'énoncé, pas à l'assemblage | page/ligne (`@livre`), assemblages |

### Transposable tel quel
- **Découpage et gabarit** du rapport (A1–A7), en particulier la table
  « énoncé Bourbaki → nom → page → citation exacte » et le journal des versions.
- **Ordre des lemmes** de tous les gros théorèmes : Zermelo (B8), C60/C62 (B9), berger (B11),
  sup des cardinaux (B7), Cantor-Bernstein (4 preuves, `@source RR-7150-v10.pdf p.730-732 §14.1`).
- **Choix de modélisation** : graphe plutôt que correspondance (B13) ; famille = graphe fonctionnel ;
  opérations totalisées par convention (B10) ; ⋂ par séparation dans ⋃ (B5) ;
  `quasi_bij` (terme + 3 propriétés) au lieu d'un objet bijection (B12) ;
  application induite sur le quotient = **formule** `f ∘ section` (B14).
- **Protocole erratum** : signaler l'écart au livre là où le livre se trompe (B16).
- **Discipline de rédaction** : preuve informelle en prose *avant* le code, coût en lignes en
  commentaire, code supprimé conservé commenté avec sa raison.

### Non transposable
- Toute la couche **tactique** (ssreflect `=> / case: / rewrite`, `Ltac`, notations
  `{inc d &, injective P}`) : c'est du pilotage de moteur, sans équivalent LCF. `@source sources/grimm_gaia/RR-6999-v7.pdf p.194-199 §8.4`
- Les **types dépendants** et l'astuce fondatrice `a : b ↦ a' ∈ b` (`Ro`/`R_inj`, `CoInductive Zorec`,
  `IM`, sigma-types) : c'est la façon *de Coq* d'être une théorie des ensembles. `@source sources/grimm_gaia/thalion,+jfra1.pdf p.13-15 §2.3`
- Le **recours à `nat`** comme ensemble infini et le transport `nat_to_B` (chez nous il faut A5).
- L'**abandon assumé de la fidélité aux assemblages** — et il argumente contre notre approche :
  « I am convinced that it is a bad idea to try to reduce the object under consideration to its
  basic components (a kind of normal form) and apply low-level theorems to it; Fermat's theorem
  cannot be proved by exhibiting an assembly that is a proof in the sense of Bourbaki. » `@source sources/grimm_gaia/RR-7150-v10.pdf p.505 ch.12`
  → À prendre au sérieux : notre τ natif ne doit **jamais** exiger de normaliser un assemblage en
  signes ; il doit rester une construction *symbolique* (c'est déjà notre cas, cf. le fix subst).

---

## ACTIONS POUR NOUS

1. **[P0 — B5] Remplacer `AXIOME_INTER_FAM` par une définition.**
   `⋂ F := séparation dans ⋃F de « ∀ z ∈ F, y ∈ z »`, d'où `⋂∅ = ∅` gratuitement, et ne garder
   `I ≠ ∅` que dans les énoncés Bourbaki qui l'exigent. Un axiome en moins sur nos 22.
2. **[P0 — B11] Formaliser le principe du berger comme lemme-pivot unique.**
   `Card E = Σ_{x∈F} Card(f⁻¹⟨{x}⟩)`, puis le corollaire à fibres constantes. Débloque d'un coup
   `Card{injections}`, `Card{permutations}`, `Card{partitions à cardinaux imposés}`.
3. **[P0 — B7] Prouver `{cardinaux ≤ a} = image de P(a) par Card`.**
   C'est la brique qui rend `C_a` un ensemble et donc le sup cardinal atteignable **sans**
   basculer sur von Neumann. Enchaîner `card_ub_sup` / `card_sup_ub` / Prop. 2 §III.3.2.
4. **[P1 — B9] Re-router `c62/fonction_recursion_NN` sur la route Grimm.**
   (a) énoncer d'abord la **version graphe** et prouver le pont graphe ↔ fonction surjective ;
   (b) unicité par plus petit contre-exemple ; (c) existence = prolongement d'un pas + **réunion
   sur une famille de segments** ; (d) ajouter la variante « stable dans F » qui évite l'AC.
   Bonus : sa définition de la borne sup prolongée **sans τ** (`M(u) = ⋃ N'(u)`).
5. **[P1 — B12] Définir ∑/∏ de cardinaux directement comme `Card(union disjointe)` / `Card(produit)`.**
   La fonctorialité indexée (Prop. 4 §III.3.3) devient alors `csum_pr0` en une ligne. Remplacer
   partout « il existe une bijection f » par un prédicat `quasi_bij` sur un terme fonctionnel.
6. **[P1 — B14] Poser l'infra E/R dans l'ordre de Grimm.**
   `class → quotient → classp → canon_proj → rep → section_canon_proj → fun_on_quotient := f ∘ s`,
   avec l'unicité après coup. Ne pas chercher la propriété universelle : viser un **terme**.
7. **[P2 — B8] Attaquer le Lemme 1 (réunion filtrante) avec `G ⊗ G'`.**
   Définir « segment commun », prouver qu'il est segment des deux, en déduire la comparabilité
   par prolongement, puis la réunion. Prévoir un chantier long (250 lignes chez lui).
8. **[P2 — A7] Aligner `V9/rapport/` sur les annexes de Grimm.**
   (i) table finale `énoncé Bourbaki → nom V9 → page rapport → citation exacte` (nos `LIVRE.md`
   en sont l'embryon) ; (ii) chapitre « changements de version » gardant le code retiré + la raison ;
   (iii) chapitre « compatibilité » archivant les preuves alternatives. Sert directement
   l'objectif « documenter le pourquoi et les erreurs autant que les preuves ».
9. **[P2 — B16] Ajouter un champ `erratum` au protocole `@livre`.**
   Le PDF contient des énoncés faux (max d'un ordonné fini vide, C55, exercices, le terme « 1 »
   lui-même). Sans ce champ, la fidélité page/ligne nous fera formaliser des faux.
10. **[P3 — B15] Chap. IV / CST1-CST2 : assumer qu'il n'y a pas de modèle.**
    Grimm ne l'a pas fait, personne ne l'a fait. Le journaliser comme front ouvert et documenter
    les tentatives — c'est exactement le type de trace qui a de la valeur pour le but final.
