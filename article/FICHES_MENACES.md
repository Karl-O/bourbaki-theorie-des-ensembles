# Fiches de lecture — les 5 menaces majeures (2 août 2026)

*(Protocole : PDF déposés dans `sources/related_work/`, lus au texte (pymupdf), chaque
affirmation citée à la page. Ces fiches CORRIGENT trois démarcations de RELATED.md — c'est
leur travail : une démarcation écrite sur un abstract est une docstring en sursis.)*

---

## F1 — Olšák, Kaliszyk, Urban, *Property Invariant Embedding for Automated Reasoning* (ECAI 2020)

`@source sources/related_work/arxiv_1911.12073.pdf` — 8 p.

**Ce qu'ils font vraiment.** Un **GNN** dont les symboles sont des nœuds *sans étiquette* —
invariance au renommage de variables, de fonctions/prédicats, et à la négation (p.1). Tâches :
**guidage** de leanCoP (calcul de connexions, p.3), **sélection de prémisses** (DeepMath, p.4),
et un « symbol guessing task ».

**Correction de ma démarcation.** Le mot « Weisfeiler » apparaît **0 fois** — leur invariance
vient de l'*architecture apprise*, pas d'un noyau WL exact. Et « dedup » : **0 occurrence** —
aucune détection de doublons ou de jumeaux, nulle part.

**Démarcation C7, durcie et vérifiée :** eux = invariance *apprise* au service du **guidage**
intra-preuve ; nous = invariance *exacte* (WL de Shervashidze, zéro apprentissage) au service
de la **détection de coïncidence** inter-théories. Ni la méthode, ni la tâche, ni le régime de
garantie ne se recouvrent. Menace rétrogradée : voisin méthodologique, à citer comme tel.

---

## F2 — Wang et al., *M2F: Math-to-Formal* (arXiv 2602.17016, fév. 2026)

`@source sources/related_work/arxiv_2602.17016.pdf` — 30 p.

**Ce qu'ils font vraiment.** Autoformalisation à l'échelle du *projet* (479 pages de manuels →
Lean compilable bout à bout), avec **provenance au span** reliant chaque déclaration au texte
source (p.2). Leur « verifier-certified » (VeriRefine) certifie… la **compilation des
éditions** (accept/revert par le toolchain), pas la fidélité.

**La phrase décisive, p.8 :** « *statement faithfulness is enforced by a provenance-linked
**manual audit*** » ; et p.7 : couche d'énoncés « ***manually** verified* against
provenance-linked spans (Appendix A.3) ».

**Démarcation C6, confirmée verbatim :** chez M2F, l'ancrage est mécanique mais **le verdict
de fidélité est humain**. Chez nous, le verdict est **dérivé** : l'infidélité est établie par
une contradiction prouvée au noyau contre le texte ancré, et la guérison est re-certifiée.
L'ancrage fin n'est plus neuf ; le verdict mécanique l'est.

---

## F3 — Rammal et al. (FAIR Meta), *Formalizing Mathematics at Scale* / ATLAS (arXiv 2605.29955, mai 2026)

`@source sources/related_work/arxiv_2605.29955.pdf` — 27 p.

**Ce qu'ils font vraiment.** Des milliers d'agents LLM → ATLAS, 45 000+ déclarations Lean
depuis 26 manuels. Politique axiomes/sorry explicite (p.4). Deux trouvailles de lecture :

1. **Leur critère de succès est NON-TRANSITIF, par choix assumé** (p.4) : une preuve qui
   invoque un lemme contenant un `sorry` est « réussie » — le lemme, non. Le filtrage des
   échecs hérités remonte au root cause **pour l'évaluation seulement** (p.25).
2. **p.6 — le plus proche voisin de C8 jamais trouvé** : un « trace analyzer », agent
   persistant par tâche échouée, qui maintient des « ***skill guides** containing lessons from
   past attempts* » que les workers **doivent lire avant de retenter**. C'est notre boucle
   corpus→briefs, publiée par Meta.

**Démarcations, ajustées :** C5 — leur comptabilité de dette est *délibérément* non-transitive
et binaire (axiome/sorry présent ou non) ; la nôtre est **quantifiée par dérivation**
(`Ax(D)`, 53 axiomes mesurés derrière un « 0 hypothèse ») avec classes de légitimité.
C8 — leurs *skill guides* sont de la prose LLM non vérifiée, sans retour tracé ; nos briefs
citent des **certificats** et le retour est mesuré instance par instance. Mais la *forme* de la
boucle est publiée : notre claim porte sur la **certification des maillons**, plus sur la boucle.

---

## F4 — *Learning to Disprove* (arXiv 2603.19514, mars 2026)

`@source sources/related_work/arxiv_2603.19514.pdf` — 21 p.

**Ce qu'ils font vraiment.** Fine-tuning de LLM pour la **génération de contre-exemples
formels** vérifiés par Lean 4, avec données synthétisées par mutation symbolique (abstract,
p.1). « Counterexample » : 108 occurrences.

**La mesure qui compte : `undecid` 0, `independen` 0, `unresolved` 0, `neither` 0.** Le
papier ne *mentionne même pas* l'existence d'un troisième statut. Tout énoncé est à prouver
ou à réfuter.

**Démarcation C4, confirmée au plus fort :** la branche réfutable est industrialisée — acquis
du domaine, on le cite. La branche **indépendante** et la *procédure de décision* à trois
sorties restent absentes de la littérature, y compris de son représentant le plus récent.

---

## F5 — Chung et al., *Goedel-Architect* (arXiv 2606.06468, juin 2026)

`@source sources/related_work/arxiv_2606.06468.pdf` — 13 p.

**Ce qu'ils font vraiment.** Le système globalement **le plus proche du nôtre**. Blueprint =
graphe de dépendances ; chaque nœud échouant porte **un de deux diagnostics** (p.2) :
STATEMENT WRONG — adossé à un **contre-exemple formellement vérifié** (« formally negated
node ») — ou preuve-trop-dure. À l'épuisement du budget, le prouveur doit écrire un
« **forfeit** » structuré en trois parties : diagnostic, analyse forensique, pistes (p.7).
99,2 % sur MiniF2F.

**Démarcations, ajustées avec précision :** (a) leur dichotomie opérationnelle articule
**2 branches sur 3** — réfutable (certifiée par le compilateur !) et trop-dure — jamais
*indépendante* : notre claim C4 se formule désormais « la **troisième** branche et la
décision qui en découle » ; (b) leurs forfeits sont des **objets structurés mais rédigés par
le LLM** (« where it *believes* the gap lies », p.3) — pas de certificat noyau, pas de
périmètre calculé ; (c) tout est **par run** : pas de corpus persistant, pas de retour tracé,
pas de texte source. C'est le concurrent à citer en premier et à démarquer sur ces trois axes.

---

## Bilan des ajustements appliqués

| fiche | effet sur RELATED/PLAN |
|---|---|
| F1 | menace C7 **rétrogradée** (GNN appris ≠ WL exact ; aucune dédup chez eux) |
| F2 | démarcation C6 **verbatim** : « manual audit » p.8 — citation d'or |
| F3 | ATLAS = plus proche voisin de **C8** (skill guides p.6) ; C5 démarqué sur la non-transitivité assumée p.4 |
| F4 | C4 confirmé : 0 mention d'un 3ᵉ statut dans le papier le plus récent du domaine |
| F5 | Goedel-Architect = **concurrent n°1** ; C4 reformulé « la 3ᵉ branche » ; C2 démarqué « believes » vs certificat |
