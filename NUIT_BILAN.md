# Bilan de la session autonome (2026-06-24, soir → nuit)

Dépôt propre ; suite verte ; invariant `theorie_ensembles() == 22` maintenu partout ;
chaque résultat **vérifié indépendamment** (reconstruction de la conclusion + clôture +
gate 0 erreur) avant commit. Aucun `Theoreme` forgé, aucun `_CLE`/monkeypatch, primitives
`N.*` uniquement.

## 1. Ce qui a été produit cette session

### Cartographie
- **Audit page-par-page Chap. I–IV** → `COUVERTURE.md` + `COUVERTURE_CHAP_{I,II,III,IV}.md` :
  **707 notions** recensées, 305 closes (43 %), 501 présentes (71 %) ; offset PDF Ch III corrigé.
- **`PLAN_ETAPE_B_v3.md` : 100 % `[x]`** (plan ciblé entièrement épuisé).

### Comblages (≈ 23 résultats certifiés)
Plan curé (Galois, segments, Prop 12 sup, Prop 8/10 produits, cofinale⟺plus-grand, Russell…)
PUIS manquants larges de l'audit :
- **III.1.2 Proposition 1 — caractérisation d'un ordre par son graphe**, formalisée comme
  **ÉQUIVALENCE complète** : `est_ordre(G,E) ⇔ (G∘G=G ∧ G∩G⁻¹=Δ_E)` sous `{champ G⊂E×E}`
  (sens direct `4896e88` + réciproque/équivalence `3aededb`). Algèbre de graphes complète.
- **II.1** antitonie du complément `A⊂B ⇔ ∁B⊂∁A` (`09013d3`).
- **II.2** caractérisation du couple `z=(x,y) ⇔ (z couple ∧ x=pr₁z ∧ y=pr₂z)` (`e8baf51`).
- **II.3 (correspondances, E II.10–11)** : `G ⊂ pr₁G×pr₂G` (`7e8db55`) ; `G⟨pr₁G⟩=pr₂G`
  (`b9bb471`) ; projection vide ⇒ `G=∅` principal+dual (`1898b4d`) ; corollaire
  `A⊃pr₁G ⇒ G⟨A⟩=pr₂G` (`5981b0e`) ; involution `(G⁻¹)⁻¹=G` (`6d51891`).
- **II.6.4 (parties saturées, E II.43–44)** — cluster complet : `A∪B`, `A∩B` saturées
  (`3901929`) ; `∁_E A` saturée sous {symétrie, relation-dans} (`3a99fe0`) ; version FAMILLE
  `⋃X_ι`, `⋂X_ι` saturées (`20303c5`).
- **Rapport LaTeX** `V9/rapport/` à jour, compilé **20 p.** (`f2f2e6a`).

**≈ 28 résultats certifiés** au total. Areas set-théoriques fondamentales **confirmées
quasi complètes** par sondage exhaustif (correspondances, composition, réciproque, images,
algèbre de familles, De Morgan, associativité, monotonie, parties saturées) — les clusters
nets restants y sont **épuisés**.

## 2. État du « reste à faire » (honnête)

Les manquants encore ouverts se répartissent en familles **non triviales**, écartées en
mode autonome nocturne pour ne jamais forcer une preuve risquée :

1. **Bloqués par la performance (cardinaux profonds)** — tests de 10–18 min, infaisables en
   boucle : Hessenberg `a²=a` (III.6), Cantor `2^a>a`, division euclidienne (III.5), bon ordre
   des cardinaux (III.3), arithmétique cardinale infinie. *Nécessitent l'optimisation du noyau
   (cf. CLAUDE.md « Performance »), hors scope d'une nuit.*
2. **Dépendants de l'axiome du choix** — distributivités Prop 8 (réciproque) / Prop 9 et leurs
   corollaires (II.5.6), surjectivité de pr_α, etc. *Nécessitent la machinerie de choix-τ.*
3. **Nécessitant de l'infrastructure à bâtir** — prédicat `partition`/`recouvrement` (II.4) ;
   ordre quotient d'un préordre (III.1.3) ; bijections canoniques quotient (II.6, E II.46–48) ;
   produit d'équivalences ; lemmes de Zermelo/Zorn (Lemme 3, Prop 4, E III.19–21) ; limites
   projectives non-vides (III.7).
4. **Méta-mathématique subsumée par le noyau** (`non_applicable`) — critères CS/CF, schémas Sx,
   C49–C52 (collectivisantes/séparation), Théorème 1 sur ∅.

Les aires set-théoriques « faciles » (correspondances, images, algèbre de familles, ordre
treillis/filtrants de base) sont désormais **très largement couvertes** — les candidats nets
restants y sont rares.

## 3. Suite
La boucle nocturne continue à sonder les aires moins couvertes (structures Ch IV simples,
bon ordre/segments III.2, propriétés correspondances/composition restantes) pour les derniers
résultats nets tractables, à pace mesuré. Pour aller plus loin sur les familles 1–3 ci-dessus,
une décision est nécessaire (optimiser le noyau pour débloquer les cardinaux ; bâtir l'infra
choix/partition/quotient) — ce sont des chantiers, pas des comblages.
