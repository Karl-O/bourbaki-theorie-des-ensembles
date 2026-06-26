# PLAN ETAPE E — audit FRAIS Chap III §1 (relations d'ordre, E III.1–14)

Audit fan-out 3 lecteurs (Explore) du 2026-06-26, pages **E III.1–14** (PDF p.104–117), confronté
à `bourbaki/ordre/`. But : régénérer une liste de cibles EXACTE (les cartes COUVERTURE_* de
2026-06-24 et les PLAN_ETAPE_B/C/D sont CLOS/périmés — la plupart des manquants listés sont depuis
comblés : Galois Prop2, ordre F^E, singletons, C39–C45, CST8…).

**Bilan §1 : très couvert.** Agent B (E III.6–10) : 0 absent, 6/6 défs closes. Les « absents »
signalés par A et C sont en partie des FAUX POSITIFS (les agents sur-déclarent « absent ») — TOUTE
cible doit être re-vérifiée (grep + Read) AVANT implémentation. Règle inchangée : UNE cible à la
fois, preuve CLOSE (primitives N.* only), theorie==22, énoncé==livre calé PDF, test qui APPELLE le
théorème, vérif indépendante (cible reconstruite depuis primitives BRUTES) AVANT commit.

---

## [x] preordre_equivalence_associee  [E III.3 §1.2 | PDF p.106]  — FAIT (2026-06-26)
- enonce: `⊢ est_relation_preordre(R) ⇒ est_relation_equivalence(S)`, `S{x,y}:=R{x,y} et R{y,x}`.
- Bourbaki E III.3 verbatim : « Mais en tout cas la relation (R{x,y} et R{y,x}) est une relation
  d'équivalence S{x,y}… Si R{x,y} est une relation de préordre dans E, S{x,y} est une relation
  d'équivalence dans E. »  PDF rendu+lu (p.106).
- FAIT : `bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre.py` (à côté de
  `preordre_oppose_est_preordre`). Preuve pure : S symétrique = commutation de ∧ (sans hyp) ;
  S transitive = transitivité de R appliquée en (x,y,z) et (z,y,x). Réflexivité du préordre NON
  utilisée (équivalence II.6.1 = sym∧trans). Vérif indép : conclusion==cible reconstruite depuis
  primitives BRUTES (sans E.est_relation_*), est_clos=True, hyps vides, non-tautologie, theorie==22,
  aucun _CLE/Theoreme/N.Theorie, 10 tests verts (test_ordre.py), 241 lignes code, ordre_treillis 9/10.

---

## FAUX POSITIFS de l'audit (NE PAS re-traiter — vérifiés PRÉSENTS)
- **Prop.11 (E III.14) « strictement monotone ⇒ injective »** : déclaré « absent » par l'agent C, mais
  EXISTE et est CLOS : `ordre_treillis/ensembles_ordre_treillis_props.py:656` (`strictement_monotone_injective_graphe`,
  + variantes croissante/décroissante). Leçon : re-vérifier chaque « absent ».
- **Définition des 4 types d'intervalle (E III.14)** : déclarée « absente » par l'agent C, mais les
  4 types EXISTENT — `intervalle_ferme`/`intervalle_ouvert` (`ensembles_abrege.py:664,669`),
  `intervalle_semi_ouvert_droite`/`_gauche` (`ordre_treillis/ensembles_ordre_vocab.py:70,76`), + variantes
  illimitées. 2e faux positif de l'agent C → les agents d'audit SUR-DÉCLARENT « absent » massivement.

## BILAN §1 (2026-06-26) : essentiellement CLOS.
Agent B (E III.6–10) : 0 absent. Agents A/C (E III.1–5, 11–14) : la quasi-totalité des « absents » sont
des faux positifs (Prop.11, intervalles présents) OU des fidélité-@livre (faits) OU 1 vraie cible faite
(preordre→équivalence). Reste : candidats doutex (C58) / lourds (familles sup indexées). → Pour le
prochain lot, AUDITER UNE SECTION MOINS COUVERTE (Chap III §3 cardinaux, §5 entiers, §7 limites) plutôt
que §1 ; toujours re-vérifier chaque « absent » par grep+Read avant d'implémenter.

## Cibles candidates À VÉRIFIER (absence non confirmée — re-grep + Read avant de déléguer)
- **C58 / conditions (RO_I–RO_IV)** [E III.4] : l'agent A donne une transcription DOUTEUSE des
  conditions ; rendre E III.4 (p.107) et lire l'énoncé EXACT avant toute formalisation. Possiblement
  méta/subsumé. PRIORITÉ BASSE tant que l'énoncé n'est pas confirmé.
- **Sup d'une famille — Prop.6 indexée, Corol. (sous-famille J⊂I), Prop.7 générale (recouvrement),
  Corol. (famille double)** [E III.11] : formes binaires/génériques présentes
  (`bornes_sup/ensembles_sup_*`) ; les formes INDEXÉES/recouvrement général peuvent manquer.
  Vérifier l'existant familles (`ii_4`) avant — risque de machinerie lourde (familles indexées).
- **Définition des 4 types d'intervalle** [E III.14] : Prop.13 (intersection) existe
  (`iii_1_12_totalement_ordonnes/ensembles_intervalles_prop13.py`) ; la DÉF formelle des 4 intervalles
  [a,b]/]a,b[/[a,b[/]a,b] serait absente — vérifier puis rendre E III.14 pour les énoncés exacts.

## [x] Fidélité — @livre AJOUTÉS (2026-06-26 ; PDF E III.6–7 rendu+lu AVANT, cf. leçon CST8)
- PDF confirmé : §1.5 « Applications croissantes » = E III.7/p.110 (Déf.1 croissante/décroissante/
  monotone ; Déf.2 strict×3) ; §1.4 « Produit d'ensembles ordonnés » = E III.6/p.109 (ordre produit).
- `ensembles_ordre_monotone.py` : 6 marqueurs posés — est_croissante/decroissante/monotone (Def.1,
  E III.7) + est_strictement_croissante/decroissante/monotone (Def.2, E III.7).
- `ensembles_ordre_vocab.py:186` : ordre_produit (Def.- §1.4, E III.6).
- 93 tests ordre_treillis verts ; marqueurs bien formés (grep). [Prop.11 « strict monotone ⇒ injective »
  confirmée à E III.14 par le renvoi de E III.7 « cf. III, p.14, prop.11 ».]

## Reporté (méta / lourd)
- Prop.7 recouvrement GÉNÉRAL, Prop.8 produit ordonné (résidu honnête) : machinerie familles/produit.
