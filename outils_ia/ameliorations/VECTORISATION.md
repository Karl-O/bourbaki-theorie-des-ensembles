# VECTORISATION — rendre le corpus consommable par un système apprenant

*(31 juil. 2026. Répond à la question de Karl : « il nous faut des chiffres, des vecteurs,
une infrastructure pour insérer la théorie dans un système ». Prototype mesuré le jour même —
les cosinus ci-dessous sont RÉELS, calculés sur les formules du dépôt.)*

## 0. Le principe : trois représentations, trois consommateurs

| niveau | objet | consommateur | coût |
|---|---|---|---|
| N0 — features scalaires | nombres déjà mesurés | modèles classiques, tri, heuristiques | nul (extraction) |
| N1 — vecteur structurel φ(t) | ℝ^d par Weisfeiler-Leman | similarité, clustering, sélection de prémisses | déterministe, sans entraînement |
| N2 — séquence de tokens | sérialisation de l'arbre ABRÉGÉ | LLM (politique π, conjecture) | dépend du modèle |

La question ouverte « DAG vs tokens » (mémoire méta-algo) a pour réponse : **les deux, pour des
consommateurs différents**. N1 pour la géométrie, N2 pour la génération.
⚠️ N2 sérialise TOUJOURS l'arbre abrégé, JAMAIS le dépliage τ (le « 1 » déplié = 4,5·10¹² signes).

## 1. N1 — l'équation du vecteur structurel

Étiquetage Weisfeiler-Leman itéré sur l'arbre du terme/de la formule :

```
ℓ⁰(v)    = (type(v), tag(v), nom(v), lieur(v))          l'identité locale du nœud
ℓᵏ⁺¹(v)  = ( ℓᵏ(v), multiensemble{ ℓᵏ(c) : c enfant de v } )
φ(t)     = normalisé( Σ_{k≤K} Σ_v  e_hash(k, ℓᵏ(v)) mod d )      ∈ ℝ^d
sim(t,u) = ⟨φ(t), φ(u)⟩                                  (cosinus)
```

**Lecture.** Chaque nœud résume son voisinage de rayon k ; l'histogramme haché de ces résumés
est le vecteur. Deux formules structurellement proches ont des vecteurs proches — sans aucun
entraînement, et en respectant l'interdit `repr()` (on marche l'arbre, on ne l'imprime pas).

**Mesures du prototype (K=3, d=512), sur les VRAIES formules :**

```
cos( H2 , H3 )               = 0,9412    même famille, index ≠        (33 vs 29 nœuds)
cos( H2 , bo(≤,ℕ) )          = 0,7437    sans rapport
cos( bo , ax_seg(R₁) )       = 0,8254    parlent tous deux d'un ordre
cos( ax_seg(R₁), ax_seg(R₂) )= 0,9521    ← LE détecteur d'incohérence
```

La dernière ligne est l'application tueuse : **deux axiomes quasi identiques (cos > 0,95)
caractérisant le MÊME terme** est exactement la signature du défaut `seg_ext` (deux ordres,
un terme). Un scan par paires sur les théories dédiées la détecte mécaniquement.

**Deux leçons de conception payées pendant le prototype** (même famille que le test de mutation) :
1. étiquette `tag OU nom` → tous les `app` se confondent (cos(H2,H3)=1,0000 à tort) ;
   l'étiquette doit porter **tag ET nom**.
2. les enfants d'un `Terme` vivent dans `.args` (pas `.termes`) — un marcheur qui l'ignore
   s'arrête au 1er niveau et rend les formules indistinguables. **Valider toute feature map
   sur des paires dont la similarité est CONNUE d'avance.**

## 2. N0 — la table de features (les « chiffres » déjà possédés)

Par théorème/dérivation, déjà mesurés dans la campagne :

```
x(θ) = ( |H(θ)|, |Ax(D)|, |dette|, nb théories étrangères, taille(conclusion),
         profondeur, temps de construction, classe E de l'échec éventuel,
         classe trichotomie de chaque résidu, nb mutants tués/injectés )
```

Sources : `outils_ia/traces/events.jsonl` (90 événements), mesures M1 (Ax(D) de 8 capstones),
sorties de tests. À extraire en table unique (`outils_ia/vecteurs/table_features.py`, à créer).

## 3. L'équation de l'environnement (le vrai branchement d'un modèle)

Le substrat est un **environnement RL à récompense vérifiable** :

```
état s      = ( D, Ouv(D), features N0/N1 des buts ouverts )
action a    = (règle r, instanciation σ)  |  conjecture  |  extension (T → T∪{δ})
transition  = le NOYAU accepte ou refuse         ← récompense exacte, infalsifiable
r(s,a)      = +1 si arête acceptée / but fermé ; certificat d'Échec sinon (donnée aussi)
```

C'est le format sur lequel les modèles de la génération Kimi K3 sont justement entraînés
(RL sur domaines vérifiables). **Notre valeur n'est pas le modèle : c'est l'environnement +
les labels certifiés.** N'importe quelle politique π s'y branche ; le noyau reste l'arbitre.

## 4. Les jeux de données à labels CERTIFIÉS (aucun autre corpus n'a ça)

| tâche | entrée | label (certifié par) | données aujourd'hui |
|---|---|---|---|
| sélection de prémisses | φ(but) | Ax(D) mesuré (M1) | 8 capstones, extensible à tout le dépôt |
| trichotomie d'un résidu | φ(h) ⊕ contexte | preuve / réfutation / indép. (noyau) | cas réels : bo, H, HW/HN + events |
| classe d'échec E1–E7 | features de route | verifier(É) (noyau) | 90 événements |
| coût de construction | φ(θ) | chronométrage | toutes les mesures de la campagne |
| remède (couple REPLica) | (état, tentative annulée) | tentative finale + tests verts | events v2, à densifier |

**Honnêteté d'échelle** : 90 événements et 8 mesures M1 = PETITES données. Ordre de marche :
N0/N1 + modèles classiques (plus proches voisins, régression logistique) d'abord — mesurables
immédiatement ; LLM par prompting/RAG sur le corpus ensuite ; fine-tuning seulement quand la
table aura des milliers de lignes (l'extraction systématique d'Ax(D) sur tout le dépôt y suffit).

## 5. Kimi K3 (arXiv 2607.24653) — évaluation pour NOTRE objectif

2,8 T paramètres MoE (104 G activés), contexte 1 M tokens, poids ouverts, RL multi-domaines.
- **Pour** : poids ouverts (politique π inspectable/adaptable), 1 M de contexte (nos formules
  aux termes clos font ~87 k caractères : elles TIENNENT), entraîné exactement au format
  « environnement vérifiable » du §3.
- **Contre** : intraçable localement (multi-GPU serveur) ; et notre goulot n'est PAS la
  puissance de la politique, c'est la TAILLE du jeu de données certifié (§4).
- **Verdict** : ne pas marier le projet à un modèle. Construire l'interface (N0/N1/N2 + env §3) ;
  tout modèle — K3 via API, un petit modèle local, un GNN — s'y branche. Le substrat est à nous,
  la politique est remplaçable.

## 6. Infrastructure à construire (ordre de marche, sobre)

1. `outils_ia/vecteurs/phi_terme.py` — N1 industrialisé (marcheur `.sous/.termes/.args`,
   étiquette tag+nom+lieur, garde anti-τ-cardinal) + tests sur paires à similarité connue.
2. `outils_ia/vecteurs/table_features.py` — N0 : extraction events.jsonl + M1 → une table.
3. Scan « axiomes jumeaux » : paires (cos > 0,95, même terme caractérisé) sur les 66 théories
   dédiées — le détecteur d'incohérence du §1, en une passe.
4. `outils_ia/vecteurs/serialiseur.py` — N2 : tokens de l'arbre abrégé (préfixe + liants).
5. Plus tard : `outils_ia/env/environnement.py` — reset(T,P) / step(coup) du §3.

## 7. Sources à ajouter (`sources/`, protocole @source — Karl télécharge si paywall)

- Alemi et al., *DeepMath — Deep Sequence Models for Premise Selection*, NeurIPS 2016.
- Paliwal et al., *Graph Representations for Higher-Order Logic and Theorem Proving* (HOList/GNN).
- Polu & Sutskever, *GPT-f* (Metamath) — politique LLM + vérificateur, l'ancêtre direct du §3.
- Blaauwbroek et al., *Graph2Tac* — embeddings en ligne de nouvelles définitions.
- Mikuła et al., *Magnushammer* — sélection de prémisses par transformers.
- Yang et al., *LeanDojo* (NeurIPS 2023) — déjà listé dans sources/INDEX.md (« à ajouter »).
- Shervashidze et al., *Weisfeiler-Lehman Graph Kernels*, JMLR 2011 — le fondement de N1.
