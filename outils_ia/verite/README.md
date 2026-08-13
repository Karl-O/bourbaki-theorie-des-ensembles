# `outils_ia/verite` — l'étude mathématique des erreurs

Établie les 26–31 juillet 2026, pendant la campagne qui a trouvé et réparé trois défauts
d'axiomes. Chaque définition ci-dessous a un **cas réel mesuré** dans le dépôt ; les
événements correspondants sont dans `outils_ia/traces/events.jsonl`.

Principe fondateur : **un échec de preuve n'est pas une note de journal — c'est un
théorème sur l'espace de recherche, muni d'un certificat vérifiable et d'un périmètre
calculé.** Un échec dont le certificat ne tient pas est *rejeté du corpus*.

## Ancrage dans l'état de l'art (protocole `@source`, cf. `sources/INDEX.md`)

Cette étude ne part pas de zéro — elle reprend trois briques de la littérature et en
construit trois autres (répartition établie dans `outils_ia/ameliorations/THEORIE_TRACE.md`,
tableau §D) :

**Repris de la littérature :**
- **L'arbre de recherche avec branches mortes conservées** —
  `@source sources/traces_et_erreurs/REPLica_Ringer_CPP2020.pdf p.6 fig.5` : REPLica
  instrumente le REPL de Coq et capture les « failed proof attempts » de 8 ingénieurs
  pendant un mois. Validation externe de notre représentation trace/DAG.
- **L'unité de remède = le COUPLE (tentative annulée → tentative finale) À ÉTAT
  CONSTANT** — `@source sources/traces_et_erreurs/REPLica_Ringer_CPP2020.pdf p.6 §4.3` :
  96 réparations classées ainsi. C'est ce qui a motivé le format v2 de l'événement
  `REMEDE` dans `outils_ia/traces/SCHEMA.md`.
- **Classer À LA MAIN avant d'automatiser** — même source, p.7 (Methodology) : le
  rétro-remplissage manuel d'`events.jsonl` est la bonne première étape, pas un pis-aller.
- **Un remède est une TRANSFORMATION, pas une annotation** —
  `@source sources/traces_et_erreurs/PUMPKIN_PATCH_Ringer.pdf` ; et la faisabilité d'un
  corpus de réparations à grande échelle :
  `@source sources/traces_et_erreurs/ProofRepairDataset_ITP2023.pdf`.

**Construit par nous (le créneau que personne n'occupe, THEORIE_TRACE §D) :**
- le **statut FORMEL** de l'échec : un certificat qui est un *théorème du noyau*,
  re-vérifié, avec périmètre calculé (la littérature capture les échecs, ne les
  certifie pas) ;
- la **mesure de dette** `Ax(D)` et la trichotomie des résidus (aucun équivalent
  identifié) ;
- l'ancrage de chaque objet à un **texte source** (page/ligne, `@livre`) et la
  hiérarchie de confiance prouvé / méta / empirique.

## 0. Socle

```
T = (nom, A_T)          théorie : un nom, un ensemble fini d'axiomes
T₀                      la théorie de référence (les 22 axiomes de theorie_ensembles())
θ = (H, C, j)           théorème : hypothèses, conclusion, justification
⊥ := ∅ ∈ ∅              témoin d'absurdité (car ⊢ ¬(∅ ∈ ∅) est clos depuis AXIOME_VIDE)
```

## 1. Les six définitions

**Consommation et dette** (outil : `axiomes_consommes.py`)

```
Ax(D)    := { (T, α) : la règle axiome(T, α) apparaît dans la dérivation D }
Dette(θ) := H(θ) ∪ { α : (T, α) ∈ Ax(D), T ≠ T₀ }
« rien postulé »       ⟺  Dette(θ) = ∅
invariant CORRECT      ⟺  Ax(D) ⊆ {T₀} × A_T₀        (≠ « |A_T₀| = 22 » !)
```

Le compte d'hypothèses mesure ce que la *décharge* a laissé ; il ne mesure pas ce que la
*dérivation* a consommé. Deux quantités sans rapport — cas mesuré : `n_bien_ordonne`,
annoncé « CLOS, 0 hypothèse », consomme **53 axiomes étrangers** (invariant 22 vrai à
chaque instant).

**Vacuité**

```
Vac(θ)  ⟺  A_T ∪ H(θ) ⊢ ⊥
```

θ peut être *correctement démontré* et sans valeur. Le noyau ne peut pas le voir : ce
n'est pas une propriété de la dérivation. Cas réel : `0! = 1` démontré sous l'hypothèse
H-graphe, réfutable — révoqué, puis **réhabilité tel quel** quand la réparation de
l'axiome a rendu H démontrable.

**Infidélité** (semi-décidable)

```
Φ := φ(𝓑)  la transcription des énoncés du livre
Infid  ⟺  A_T₀ ∪ Φ ⊢ ⊥
```

On peut toujours *trouver* une infidélité, jamais certifier son absence — d'où l'audit
permanent, jamais un « % de couverture ». Cas réel : `AXIOME_PRODUIT_FAM` amputé du
conjoint `F ⊂ I×⋃X_ι` ; le corpus réfutait E II.32 à zéro hypothèse.

**Trichotomie des résidus** (outil : `classer_residu.py`)

```
Dechargeable(h) ⟺ A_T₀ ⊢ h       le « mur » était FANTÔME
Refutable(h)    ⟺ A_T₀ ⊢ ¬h      tout θ portant h est VACUEUX
Independante(h) ⟺ ni l'un ni l'autre — AUCUN effort de preuve ne fermera h ;
                  le seul coup légal est d'étendre la théorie (δ) ou d'en changer (ι)
```

Cas réels des trois classes, la même semaine : `bo(≤,ℕ)` déchargeable (0 hyp, 344 s) ;
H-graphe réfutable ; HW/HN indépendantes.

**Dérive**

```
Derive(R) ⟺ R complète ∧ conclusion(R) ≠ cible        (égalité SYNTAXIQUE)
```

Le théorème se construit, reste clos, passe les tests — et démontre *autre chose*. Seul
un test comparant à une cible **reconstruite hors du module** l'attrape. Cas réel :
`membre_but` (conclusion passée de 6 908 à 8 592 caractères, test n'assertait que
`est_clos`).

**Mur fantôme**

```
Fantome(r) ⟺ sym(r) ⊄ Σ  (r n'est pas même un énoncé)  ∨  A_T₀ ⊢ r
```

Cas réels : le résidu adossé à `factorielle_existe` (symbole jamais codé) ;
`AXIOME_INTERV_ENT` cité 3 fois, défini nulle part.

## 2. La taxonomie E1–E7, avec certificats

| classe | définition | certificat valide | cas réel |
|---|---|---|---|
| E1 dérive | conclusion ≠ cible | test syntaxique (pas de théorème) | `membre_but` |
| E2 vacuité | {h} ⊢ ⊥ | théorème dont la conclusion est ⊥, hyps ⊆ résidu | H-graphe / `0!=1` |
| E3 impasse | aucune continuation ne clôt | élague toute route qui l'étend | — |
| E4 dette | Ax(D) ⊄ {T₀}×A_T₀ | mesure M1 (process frais) | `n_bien_ordonne` (53) |
| E5 fantôme | résidu déjà prouvable ou mal formé | théorème CLOS = le résidu ; ou grep | `bo(≤,ℕ)` |
| E6 infidélité | axiomes ∪ livre ⊢ ⊥ | preuve close π + référence φ(b) | produit, `seg_ext` |
| E7 erreur de mesure | la sonde a menti | contre-mesure | sonde à noms devinés |

## 3. Les objets (outil : `echec.py`)

```
Échec = (but, classe, certificat, rebroussement, périmètre)
Mur   = (condition, prédicat, certificat)
```

`verifier(É)` rejette tout Échec dont le certificat ne correspond pas à sa classe. Le
`prédicat` d'un Mur **calcule** son périmètre au lieu de le supposer (cas réel : la
réfutation H-graphe n'atteint que les produits d'index *littéralement* vide — H2/H3
prouvées hors d'atteinte, un seul fichier révoqué).

## 4. Ce que les outils NE détectent PAS (limites mesurées)

- **`axiomes_consommes`** n'est valide qu'au **premier appel d'un process frais** : au
  2ᵉ appel la mémoïsation sous-compte (mesuré : −62 %). Les DEUX implémentations de la
  règle `axiome` doivent être surveillées (`regles_surveillees()` doit rendre 2 fichiers),
  sinon faux négatif silencieux. Surcoût ×1,5–×3 : outil d'audit, pas de suite de tests.
- **Le critère syntaxique d'indépendance n'est PAS suffisant** — réfuté par la mesure :
  `symboles_libres(bo(≤,ℕ)) ≠ ∅` alors que `bo_graphe_NN()` est close à 0 hypothèse. Le
  critère seul aurait fabriqué un faux mur DE PLUS (on ne le numérote pas : les comptes
  nus dérivent, cf. ci-dessous). Il ne s'applique qu'**après** l'échec du prouveur
  (4ᵉ position dans `classer`).
- **`classer` ne mesure pas Ax(D) du certificat du prouveur** : un prouveur qui consomme
  une théorie dédiée serait classé « déchargeable » à tort (c'est un E4, pas un
  déchargement). Couplage automatique refusé pour cause de coût — à composer à la main.
- **« inconnu » n'est PAS « bloqué »** : c'est une dette de mesure, la classe à re-passer
  après chaque fix d'infrastructure. C'est elle qui a produit **neuf** faux murs
  (réconciliation du 2 août 2026 — critère : « déclaré bloqué / verrou / chantier lourd,
  re-mesuré ouvert ou déjà résolu » ; **l'énumération fait foi, pas le compte**) :
  ev. 37 `complement`, ev. 1 verrou-τ global, ev. 8 `n_bien_ordonne`, ev. 9
  instanciation C60-final sur `ensemble_NN` (la sonde à 4,7 s), ev. 10
  `carte_cardinaux_valeur`, ev. 36 `est_partition` — les six AVANT la semaine
  instrumentée — puis ev. 61 capstone (∃!f) C62, ev. 64 R-pivot, ev. 65 assemblage O1,
  les trois PENDANT. Exclus (autres modes de défaillance, pas des murs déclarés) :
  ev. 46 (docstrings menteuses), ev. 53 (mauvaise route par défaut), ev. 58 (témoin
  confondu avec hypothèse). Historique de la dérive : le docstring de `classer_residu`
  disait « six » (exact à sa date, avant la semaine), C8_retours disait « 7× = 3 + 5
  antérieurs » (compte de mémoire, faux : ils étaient 6) — deux nombres nus, zéro liste.
- Un mutant de test qui meurt sur `TypeError` est un mutant **cassé** : son « kill » ne
  prouve rien.

## 5. La mesure de progrès, et pourquoi elle est piégeuse

```
Π := Σ_θ |Dette(θ)|
progrès    : Π ↓          honnêteté : Π ↑
```

Les deux pointent en sens inverse : découvrir une dette invisible *augmente* Π alors que
le corpus s'améliore. Toute métrique qui ignore `Infid` et `Dette` **récompense
mécaniquement le mensonge** — c'est la raison structurelle des fausses victoires du
journal (« la boucle Déf.2 est fermée »).

## 6. Règles d'hygiène dérivées (toutes mécanisables)

1. Tout symbole cité dans un résidu est vérifié par grep **au moment où on l'écrit**.
2. Deux marqueurs `@livre` citant le même texte à des lignes différentes ⇒ l'un est faux
   (recompter sur le PNG ; ne jamais recopier un numéro).
3. Un constructeur de terme porte **tous** ses paramètres dans `app(...)`, et tout axiome
   le caractérisant est ∀-clos dessus (passe AST : 21 fautifs trouvés ; deux
   contradictions dérivées, `seg_ext` et `interv_ff`).
4. Jamais de statut collectif (« tous CLOS ») dans un en-tête de dossier.
5. Cible de test reconstruite **hors du module**, comparaison `==` syntaxique,
   hypothèses par égalité exacte de `frozenset` — jamais un `len`.
