# PLAN ÉTAPE F — fan-out d'audit 3 sections (2026-06-30) + frontière réelle

Audit parallèle (3 agents Explore, lecture seule) des sections sous-vérifiées, chaque
trou re-confirmé **dans le code** (grep+Read) — la carte `docs/couverture/` (24 juin) étant
périmée et sur-déclarant « manquant ». Résultat net : **le front des gains rapides est saturé ;
le restant est constitué de chantiers modérés-à-lourds.**

## §II.6 — Relations d'équivalence : **0 GAP (saturé 100 %)**
11/11 résultats nommés formalisés, ~90 % clos. Prop.1, C55, C56, C57, parties saturées,
relation induite, quotient R/S, produit R×R', classes d'objets : tous présents.
Seul résidu honnête : factorisation effective de la **décomposition canonique** (déjà
signalée partielle). La carte listait du « manquant » → faux.

## §III.2 — Ensembles bien ordonnés : **lourd, largement fait — PAS une cible de flux**
Bon ordre, segment (`_seg(R,E,a)=]←,a[` EST la définition), récurrence transfinie C59,
**Zermelo** (Th.1), **Zorn** (Th.2), **trichotomie** (Th.3, bundle de 60+ fichiers clos) :
tout présent/clos. Les « gaps » de l'agent (Prop.1/2, Lemmes 1-4) sont soit embarqués dans
la trichotomie close, soit dépendent de la machinerie lourde. Re-vérifié : `est_segment`,
`est_segment_propre`, `image_segment_est_segment`, `intersection_segments_segment` existent.
→ Section non prioritaire pour le flux continu (lourde, tests lents).

## §II.5 — Produit d'une famille : **17/18 ; 2 candidats re-vérifiés**
- **[GAP1] Prop.2 (E II.31)** — « f ↦ v∘f∘u injective » : RÉSIDU DUR documenté
  (`ensembles_currying_ii5.py` : VERROU = construction du graphe-terme de la conjugaison
  f↦v∘f∘u). La composition d'injections elle-même est close (`theoreme1_a_injective`).
  → Pas un comblage rapide ; reporté avec le verrou τ.
- **[GAP2] Cor. de Prop.8 (deux familles, E II.36 p.87)** —
  `(⋂_ι X_ι)∪(⋂_κ Y_κ) = ⋂_{(ι,κ)∈I×K}(X_ι∪Y_κ)` : GENUINE.
  **Tractable (choice-free dans LES DEUX SENS pour deux familles)** : le sens ⊃, exclu pour
  la Prop.8 générale (choix), est ici prouvable par TIERS EXCLU (cas (∀ι)x∈X_ι / ∃ι₀ x∉X_ι₀).
  Nécessite le paramétrage C54 (théorie locale, familles nommées par paramètres) comme
  `ensembles_prop8_distrib_directe_ii5.py`. → **EN COURS** (agent d'implémentation délégué,
  ne committe pas ; superviseur vérifie). Effort ~100 lignes, théorie locale, theorie==22.

> Prop.8 générale : seule l'inclusion directe (⊂) est formalisée ; le sens ⊃ est
> **bloqué par le choix** (résidu honnête fidèle au livre, E II.36).

## Conclusion stratégique
Foundational (I.1-4, II.1-6, III.1-2) **saturé** pour les gains rapides. Frontière réelle =
chantiers modérés-lourds : **II.5 GAP2** (en cours), II.5 conjugation-verrou, et les gros
chantiers cardinaux (Hessenberg a²=a III.6, Cantor 2^a>a, division euclidienne III.5 — lents,
13-18 min/test). Les prochains ticks visent ces chantiers documentés, plus de chasse au
gain-rapide (le fan-out l'a confirmée vaine).
