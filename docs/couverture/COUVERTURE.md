# Couverture globale — *Théorie des ensembles* de Bourbaki, formalisation V9

Synthèse de l'**épluchage page-par-page du texte principal** (Chap. I–IV), chaque notion du
livre confrontée au code certifié par le noyau LCF. Source = PDF du livre lu page par page
(cf. `outils_ia/pdf/pdf_index.md`). Cartes détaillées : `COUVERTURE_CHAP_{I,II,III,IV}.md`.

Date : 2026-06-24.

## Chiffre de couverture (707 notions recensées sur les 4 chapitres)

| Chapitre | notions | clos | partiel | **manquant** | n/a (subsumé noyau) |
|---|---:|---:|---:|---:|---:|
| **I** Logique | 136 | 58 | 11 | 20 | 47 |
| **II** Ensembles | 222 | 107 | 56 | 52 | 7 |
| **III** Ordre & cardinaux | 237 | 98 | 72 | 60 | 7 |
| **IV** Structures | 112 | 42 | 57 | 11 | 2 |
| **TOTAL** | **707** | **305** | **196** | **143** | **63** |

### Lecture brute (sur les 707 notions)
- **Closes (certifiées, énoncé == livre)** : 305 → **43,1 %**
- **Présentes (closes + partielles)** : 501 → **70,9 %**
- **Manquantes** : 143 → 20,2 %
- **Non applicables** (métamathématique réalisée structurellement par le noyau : critères CS/CF,
  schémas de formation, méta-concepts « démonstration/théorie ») : 63 → 8,9 %

### Lecture honnête (sur les 644 notions *formalisables*, hors n/a)
- **Closes** : 305 / 644 → **47,4 %**
- **Présentes** : 501 / 644 → **77,8 %**
- **Manquantes** : 143 / 644 → **22,2 %**

> Le noyau garantit la *soundness* (aucun faux théorème) ; la *fidélité* (énoncé == Bourbaki)
> repose sur cette relecture page-par-page. **0 écart majeur** détecté sur Ch I et Ch IV ;
> 41 écarts majeurs cumulés sur Ch II+III (dont 2 résolus via la brique produit, cf. cartes).

## Où sont réellement les trous (priorité de comblage)

**Chap. IV — quasi clos.** Les 11 « manquants » sont à 9/11 des **Exemples renvoyant à
d'autres volumes** (Topologie, Algèbre : complété d'espace uniforme, groupe topologique libre,
variété d'Albanese, anneau d'opérateurs d'un module…) → **hors périmètre** de *Théorie des
ensembles*, à reclasser non_applicable-par-portée. Vrai trou interne : la définition de
*l'ensemble des structures d'espèce Σ sur E* (E IV.4). → Chap. IV essentiellement terminé.

**Chap. I — vrais trous logiques (formalisables) :**
- §I.4 quantifiés : **C26** (∀x R ⇔ (τ_x(¬R)|x)R), **C39–C42** (distribution ∀/∃ sur ⇒, et,
  ou ; échange de quantificateurs typiques) — déclarés « workflow-vérifiés, lock-in à finir ».
- §I.5 égalitaires : **C43** (Leibniz : T=U ⟹ R{T}⇔R{U}), **C45** (R univoque en x ⇔ R ⟹ x=τ_x(R)),
  déf **relation univoque en x**, déf **relation fonctionnelle en x** (∃x R et univoque) —
  socle logique des fonctions, à formaliser.
- Métathéorie (théorie plus forte / équivalente, C2–C5) : à reclasser **non_applicable**
  (on travaille dans une théorie fixe ; le noyau ne compare pas deux théories).

**Chap. II — 52 manquants** (cf. `COUVERTURE_CHAP_II.md`), dont les plus saillants :
- ¬Coll_x(x∉x) « pas d'ensemble de Russell », z∈{x}⇔z=x, x∈X⇔{x}⊂X
- produits (24)(25)(26) via la brique `produit_egalite_par_couples`
- f⁻¹ (17)
- réflexivité/transitivité de ⊂ (rangées à tort en III.1) — écart structurel à corriger.

**Chap. III — 60 manquants** (cf. `COUVERTURE_CHAP_III.md`), dont :
- Prop 1 (G∘G=G et G∩G⁻¹=Δ), **Prop 2 connexion de Galois** (u∘v∘u=u), ordre sur F^E.

## Méthode
- Rendu PDF→PNG (`pdftoppm -r 150`), lecture image par les agents, grep du code, sortie
  schema-validée (workflow `wfvn3moxp`, 12 agents, 1/sous-section ; Ch II/III : audits antérieurs).
- Statuts : **clos** (Theoreme certifié, énoncé complet) · **partiel** (cas particulier / modulo
  hypothèses honnêtes / niveau valeurs) · **manquant** · **non_applicable** (subsumé noyau LCF).
