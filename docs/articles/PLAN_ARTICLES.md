# Plan éditorial — les articles du projet (10 août 2026)

**Règle de partage : une QUESTION par article.** Si deux articles répondent à
la même question, ils fusionnent. Les « grosses idées » sont numérotées et
attribuées à UN SEUL article : ce qui circule ailleurs y est cité, pas
re-expliqué.

## Statut (21 août 2026)

| article | état | où |
|---|---|---|
| A1 | **écrit, relu par Karl, poussé** (EN 28 p + FR 30 p) | `article/` |
| A3 | **écrit, relu par Karl, poussé** (EN 21 p + FR 22 p) | `article/goldbach/` |
| A2 | **écrit, relu par Karl le 21 août, poussé** (EN 14 p + FR 14 p) | `article/dernier_kilometre/` |
| A4 | **écrit le 21 août** — porte franchie EN CODE (marche 414 s vs échec direct 692 s, tests des deux côtés verts en 2673 s) ; EN 10 p + FR 10 p ; relecture Karl en attente | `article/marcheur/` |

La soumission arXiv est l'étape suivante ; elle passe par le compte de Karl
(licence + endorsement). Catégorie suggérée : cs.LO principal.

---

## A1 — Une théorie de Bourbaki dans une machine

**Question** : que faut-il pour qu'une théorie mathématique *existe* dans une
machine — au sens où « démontré dans le livre » et « vérifié par la machine »
coïncident ?

**Thèse** : un noyau LCF minuscule suffit à garantir qu'aucun faux théorème
n'est produit ; **ce qu'il ne garantit pas, c'est qu'on démontre le bon
énoncé**. Cette seconde garantie est un problème d'ingénierie à part entière,
et elle a ses propres outils.

**Grosses idées**
1. **La frontière de confiance** — un `Theoreme` ne naît que des primitives du
   noyau ; jamais de clé, jamais de théorème fabriqué à la main. Tout le reste
   du dépôt est du code ordinaire.
2. **Soundness ≠ fidélité** — deux incidents mesurés : l'axiome d'intersection
   contradictoire (26 juil.) et `est_premier` qui ne contraint pas son argument
   à être un entier (10 août). Dans les deux cas le noyau n'a rien à se
   reprocher : c'est l'énoncé qui visait à côté.
3. **L'arbre calqué sur la table des matières** — un trou de couverture devient
   un dossier vide. La citation `@livre` (page + lignes) est *le détecteur de
   trous*, pas une décoration.
4. **Métathéorème ≠ théorème** — un schéma « pour toute relation R… » est un
   générateur Python, jamais un objet du noyau. La frontière entre les deux est
   la ligne que le projet ne franchit pas.

**Figure centrale** : les couches (assemblages τ → formules abrégées → noyau →
tactiques), avec la frontière tracée en travers.

**Ce qui n'y va pas** : tout ce qui concerne la recherche automatique de
preuves (→ A2), et Goldbach (→ A3).

---

## A2 — Le dernier kilomètre : faire dire à une machine ce qui lui manque

**Question** : comment une machine sait-elle *ce qui lui manque* — et comment
mesure-t-on la distance qui reste, au lieu de la décréter ?

**Thèse** : le dernier kilomètre ne se franchit pas d'un coup, il **se
localise**. Un système qui échoue en produisant l'énoncé exact de son manque
vaut plus qu'un système qui réussit une fois sur deux sans savoir pourquoi.

**Grosses idées**
5. **L'organe de besoin** — au lieu de rendre « échec », la machine rend la
   liste des formules qui, ajoutées au pool, fermeraient le but. L'échec devient
   une donnée exploitable.
6. **Diagnostic mesuré → organe** — les neuf organes (v2…v9) ne viennent pas
   d'une architecture pensée d'avance : chacun naît d'un manque observé
   (conjoints jamais re-soumis, manques jetés en route, faits universels
   inertes, égalité réflexive comptée comme manque…). *L'outil se déduit du
   diagnostic.*
7. **Chaînage vs créativité** — la machine a tracé sa propre frontière : elle
   enchaîne les théorèmes du pool, mais ne fabrique pas un témoin. Le manque
   terminal qu'elle a écrit (`¬(n = n)`) est un aveu exploitable, et il désigne
   l'organe suivant.
8. **Le faux « bloqué »** — six fois, un blocage annoncé s'est révélé faux
   après re-sonde. Corollaire de méthode : *re-mesurer après chaque organe*,
   ne jamais faire confiance à une carte de la veille.

**Figure centrale** : la courbe des manques au fil des sondes (14 → 8 → 6 → 4 →
1), avec l'organe qui a produit chaque chute.

**Le moment fort de A2** (acquis du 10 août) : les proposeurs v10/v11
*choisissent* un témoin parmi les objets nommés ; quand le pool n'en nomme
aucun, ils sont muets. Le proposeur **v13** *fabrique* le témoin canonique
`τx(φ)` depuis le but seul. Effet mesuré, à pool vide : le manque passe de
`∃p∃q…` (le but intact) à `¬(…τp…)` (les propriétés d'un terme nommé).
**La machine refait donc seule le geste que l'auteur avait fait à la main
(GG9)** — sans créer d'information : elle change la forme de la question.
C'est l'illustration la plus nette de la thèse « le dernier kilomètre se
localise ».

**Matériau annexe** : `PIEGES_MESURES.md` — 14 pièges payés (tests qui n'ont
pas tourné, indicateurs trompeurs, gardes mal placées…). C'est ce qui donne
son autorité à un article de méthode : on raconte ce qui a cassé.

**Deux pièges de méthode ajoutés le 12 août, qui valent au-delà du projet.**

*Une recherche qui échoue en GROSSISSANT ne se répare pas par plus de budget.*
Signature : le coût explose (×2 par palier) et l'information stagne (nombre de
manques figé). Deux fois sur deux, la cause était en amont — un ordre
d'exploration inadapté, ou une borne fixée au jugé plutôt qu'à la mesure. La
règle adoptée : *mesurer la longueur de chaîne attendue avant de régler la
borne*.

*Une simplification commode dans un script jetable peut escamoter tout le
travail réel.* Mesuré à la migration : le script d'exploration de la symétrie
donnait aux deux ensembles la même graphie de primalité. Sur les définitions
réelles, les habits se croisent et il faut un pont supplémentaire. Le script
« marchait » — il ne démontrait simplement pas ce qu'on croyait.

**Ce qui n'y va pas** : le contenu mathématique de Goldbach (→ A3), et les
mécanismes d'apprentissage encore prospectifs (→ A4).

---

## A3 — Face à l'ouvert : une machine qui cartographie plutôt qu'elle ne prouve

**Question** : que peut produire une IA vérifiée sur un problème *ouvert*, où
la réussite est exclue d'avance ?

**Thèse (renforcée le 12 août)** : elle produit une **carte certifiée** — un
réseau d'énoncés équivalents, de réductions et d'obligations exactes. Mais
surtout, elle peut **mesurer ce que cette carte ne contient pas**. En
reprenant les réductions avec le prédicat « être premier » remplacé par un
paramètre, on constate qu'elles ferment toutes à l'identique : elles ne
distinguent pas les nombres premiers d'un ensemble sans structure. *Une IA
vérifiée peut donc délimiter la difficulté d'un problème ouvert — dire où
l'arithmétique commence — même sans avancer d'un pas vers la solution.* C'est
un objet mathématique, pas un compte rendu d'échec.

**Grosses idées**
9. **La carte plutôt que la preuve** — Goldbach reste ouvert ; ce qui est
   acquis, ce sont des équivalences certifiées : la forme moitiés, la réduction
   aux composés (les `k` premiers sont gratuits), la descente branchée sur la
   récurrence forte — et le pas de récurrence *écrit par la machine elle-même*.
10. **Goldbach sans « il existe »** — chez Bourbaki `∃x φ(x)` **est**
    `φ(τx φ)` : la conjecture se réécrit sans quantificateur existentiel, comme
    trois propriétés de deux objets nommés. La question posée à la machine
    change de nature.
11. **Une stratégie = un choix de témoins** — un générateur compile n'importe
    quel couple de termes en route certifiée ; l'espace des preuves devient un
    espace de témoins définis (glouton, décalé, jumeau, canonique).
12. **La forme crible et le résultat négatif** — l'ensemble des premiers ≤ 2k,
    construit, non vide et fini ; la conjecture devient une *rencontre* de deux
    parties finies ; et le comptage brut est **certifié insuffisant** — savoir
    pourquoi une voie échoue est un résultat.
13. **L'audit né du blocage** — le sens retour refusait de se fermer : la cause
    n'était pas un lemme manquant mais un énoncé infidèle. *Un blocage
    persistant est un signal sur l'énoncé, pas sur la preuve.* (Principe posé
    en A1, récit ici.)

**Figure centrale** : le graphe des équivalences de Goldbach, chaque arête
étiquetée par son théorème, chaque feuille par l'obligation qui reste
(déjà dessiné dans `CARTE_GOLDBACH.md`).

**Le résultat qui structure A3** (acquis du 10 août) — la synthèse GG24 :

> `⊢ [ ∀k composé, les premiers ≤ 2k rencontrent leur miroir ] ⇒ Goldbach`

et surtout la **convergence des trois lignes** du projet : le borné (n ≤ 86)
est absorbé par GG25, les k premiers par GG22, et tout se lit désormais comme
un énoncé sur la rencontre. *Un seul objet à étudier au lieu de trois* — c'est
la forme la plus économique atteinte, et c'est ce qu'un article doit livrer.

**Annexe reproductible** (refaite le 12 août) : l'arc n'est plus une pile de
scripts de session. `recherche/goldbach/` est un dossier permanent de 8 modules,
et `capstone.verifie_chaine()` rejoue **15 maillons** en les jugeant PAR LE
NOYAU — l'ancienne version en vérifiait deux par sous-processus et recherche de
la chaîne `"CLOS: True"` dans `stdout`, ce qui n'était pas une vérification.
`tests/recherche/goldbach/` : 18 tests. Un lecteur peut tout revérifier, et
surtout un maillon ne peut plus passer au vert par accident.

**Réserve d'honnêteté à tenir dans le texte** : aucun fait arithmétique
nouveau sur les nombres premiers n'a été produit. Ce sont des réductions.

**Idée 14 — les deux voies refermées PAR LA NÉGATIVE, et ce qu'elles désignent
ensemble** (acquis des 10 et 12 août). Le **comptage** brut : le critère des
tiroirs `2·π(2k) > 2k+1` ne tient pour aucun `k ≥ 2`. L'**équationnel** : après
avoir doté la machine de la congruence, de la réécriture chaînée et de
l'instanciation des lois, la re-sonde de Goldbach donne un manque de **forme
strictement identique** — la frontière n'a pas bougé d'un pouce. Deux angles
différents, une même conclusion : *il faut de l'information sur la RÉPARTITION
de `P₂ₖ`, ni sur sa taille, ni sur la forme de l'énoncé.* Un article sur
l'ouvert tire sa valeur de ce genre de verdict : savoir où NE PAS chercher est
un résultat, et c'est un résultat que la machine a produit.

**Idée 15 — la symétrie comme premier fait de répartition.** Les solutions vont
par paires : `m ∈ P₂ₖ ∩ Q₂ₖ` entraîne l'existence de son partenaire
`m' = 2k − m` dans le même ensemble. La rencontre est stable sous une
involution de point fixe `k`. C'est conditionnel — rien sur l'existence — mais
c'est la première information du type que les idées 12 et 14 réclament.

**Ce qui n'y va pas** : le détail des organes (→ A2), l'infrastructure (→ A1).

---

## A4 — (programme) Apprendre à proposer : le marcheur

**Question** : comment une machine apprend-elle à *fabriquer* le témoin qu'aucun
enchaînement ne trouve ?

**Statut** : à distinguer nettement des trois premiers — **il y a du construit
et testé** (anti-unificateur + promotion sous critère de compression, volant
wake-sleep avec compounding mesuré, conjectureur produisant un théorème neuf
certifié), mais la thèse, elle, est prospective.

**Grosses idées**
14. **Génération de preuves comme marche guidée** — la parenté avec les modèles
    de diffusion : marche discrète sur le graphe des dérivations, avec un
    vérificateur exact en garde-fou. Le noyau rend l'exploration *sûre par
    construction* : une mauvaise proposition ne coûte qu'une route morte.
15. **Le corpus comme carte de trous** — miner les bibliothèques existantes
    (set.mm, mathlib) pour les *énoncés* et la *structure de dépendance*, pas
    pour les pas de preuve (les fondations diffèrent).
16. **Compresser pour progresser** — inventer un nom, le certifier, mesurer ce
    qu'il économise : le critère de compression comme moteur d'abstraction.

**Recommandation** : ne pas publier A4 avant que le marcheur ait fermé au moins
un but que le chaînage seul ne ferme pas. Sinon, le réduire à une section
« programme » à la fin de A2.

---

## Ordre de rédaction conseillé

**A1 d'abord** (il fonde le vocabulaire et il est le plus complet), **A3
ensuite** (c'est le plus spectaculaire et il tient debout seul), **A2 en
troisième** (il gagne à citer des exemples de A3), **A4 en dernier** ou en
section.

**Titres de travail** — A1 « Fidélité et confiance : une théorie de Bourbaki
dans une machine » · A2 « Le dernier kilomètre : une machine qui nomme son
manque » · A3 « Cartographier l'ouvert : Goldbach vu par un noyau LCF » ·
A4 « Apprendre à proposer ».

## A5 (esquisse) — « Nommer la brique manquante : la boucle livre-solveur et les leçons de capture nominale »
Pitch : A4 a montré (EXP6/EXP7) qu'un marcheur peut NOMMER la brique qui lui
manque, et qu'un humain qui l'écrit dans le livre rend le but facile à tous.
La session des 21-22 août fournit le second volet : DOUZE leçons de capture
nominale (lieurs τ, keystones-à-noms, trous de congruence, variables C54)
accumulées en fermant le Lemme 2 (ℵ₀·ℵ₀=ℵ₀) — chaque leçon est une brique
de MÉTHODE que la boucle a nommée en échouant, puis consignée, puis réusitée
avec succès (3 sous-lemmes verts du premier coup ensuite). Matériau :
DECISIONS.md leçons 1-12, la pile W, les temps de certification (figure du
rapport V9). Statut : idée, à écrire après la CIBLE 2.
