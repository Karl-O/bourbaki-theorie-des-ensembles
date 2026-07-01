# Campagne « plus de trous » — journal multi-agent (gap-filling)

**But** : combler TOUS les trous def/théorème du livre jusqu'à couverture complète, à
plusieurs agents, en gardant la frontière de confiance (noyau seul, `theorie==22`, jamais
poser le choix). Chaque itération : vérifier → formaliser → tester → commit → consigner.
Ce journal EST une donnée pour le méta-algo (generate-and-verify) : il documente le
« pourquoi », les techniques et les pièges (cf. [[meta-algo-diffusion-marche]], [[but-final]]).

## ⚠️ LEÇON N°1 (2026-07-01) — AUCUN doc de couverture n'est fiable ; VÉRIFIER EN CODE
L'audit fan-out (8 agents, TOC livre vs code) et MÊME `FIDELITE_PDF.md` produisent des
**faux négatifs ET des faux positifs** :
- **Faux négatifs** : l'agent Ch-II.1–3 a marqué MANQUANT des résultats fondamentaux
  DÉMONTRABLEMENT présents (`caracterisation_couple` Prop.1, `composee_associative` Prop.4,
  `paire`, `est_injective/est_surjective` Def.10, `est_retraction/est_section` Def.11).
- **Faux positifs** : l'algèbre du complémentaire (∁∁X=X, X∪∁X=E, X∩∁X=∅, disjonction 14e,
  recouvrement 14f) était listée MANQUANT (Résumé §1.14) — or les **5 lois sont CLOSES**
  (`complement_involution`, `reunion_complement_plein`, `inter_complement_vide`,
  `disjonction_complement`, `recouvrement_complement`). Cause : `FIDELITE_PDF.md` a une liste
  `manquant` PÉRIMÉE en tête + une section `COMBLÉS` en bas ; l'agent a lu la première.

**Règle** : pour CHAQUE cible candidate, `grep` le théorème dans le code AVANT tout effort
(nom + contenu math + variantes). « grep ne trouve pas le nom » n'est PAS une preuve
d'absence (peut être nommé autrement) → confirmer par un agent de recon ciblé. Ne jamais
formaliser sur la foi d'un doc de couverture.

## Confirmés FAITS malgré l'audit « MANQUANT » (ne pas reformaliser)
- Algèbre du complémentaire (5 lois) — `ii_1_axiomes_algebre/` (+ `ii_1_algebre_booleenne/`).
- `est_permutation`, `est_permutation_triple` — `fonctions/ii_3_general/ensembles_fonctions_complements.py`.
- Involution de la réciproque (G⁻¹)⁻¹=G — `fonctions/ii_3_2_reciproque/ensembles_reciproque_involution.py`.
- **Symétrie canonique E×F≅F×E** — `eq_produit_commute` (CLOS, vérifié) dans
  `cardinaux/arithmetique/iii_3_3_produit/ensembles_produit_commute.py` (+ swap_graphe_*).
  ⚠️ 2e FAUX POSITIF d'affilée (FIDELITE_PDF l.137 disait « manquant »). Le code prime.
- (Rappel session : II.5 Prop.2 conjugaison 1°+2° + `retraction_construite_par_tau`, cf. git.)

## LEÇON N°2 (2026-07-01) — la phase « tractable » est PLUS avancée que tout doc
2 cibles « faciles » d'affilée (complément, symétrie canonique) = déjà closes. Le vrai
front est probablement les résidus DURS (famille B). STRATÉGIE : au lieu de recon 1-par-1
(coûteux, retombe sur du déjà-fait), faire UNE passe de vérification-batch multi-agent
(present/absent EN CODE) sur toutes les cibles tractables restantes → liste absente
définitive, puis formaliser sans surprise. Ne PAS relancer de recon sur une cible sans
avoir d'abord vérifié le CODE (pas le doc).

## File d'attente — cibles VÉRIFIÉES ABSENTES EN CODE (passe batch 7 agents, 2026-07-01)
FAIT ✅ : **Triplet (a,b,c)=((a,b),c) + 3 projections** (`ii_2_couples_produit/ensembles_triplet.py`,
`triplet_projection_1/2/3` CLOS). ⚠️ ii_2_couples_produit atteint 10 entrées → prochaine
addition II.2 = créer un sous-dossier.
Restantes tractables (present=NON confirmé en code) :
1. **(24) pr₁⁻¹(X)=X×F** et **(25) si Y≠∅, pr₁(X×Y)=X** — Résumé §3 items 3e-f.
2. **(17) f⁻¹(Y)=f⁻¹(Y∩f(E))** — Résumé §2 item 7.
3. **Application majorée/minorée/bornée + borne sup d'une application** — Résumé §6 item 7
   (majorant/borne_superieure existent sur ENSEMBLES ; étendre aux applications via image f(A)).
4. **Familles `(X_ι)` croissantes/décroissantes de parties** — Résumé §6 item 12
   (est_croissante/monotone existent sur applications ; spécialiser aux familles I→𝔓(E) pour ⊂).
5. **Eq(E,F) ⇒ Eq(𝔓E,𝔓F)** — Résumé §7 item 1 (construire bijection 𝔓E→𝔓F par image directe).
6. **⋂_{ι∈∅}X_ι = E** — Résumé §4 (40) — DÉLICAT : l'axiome AXIOME_INTER_FAM omet x∈E (écart connu).
DÉJÀ FAITS (audit disait manquant) : assoc (E×F)×G≅E×(F×G) `eq_produit_associatif` ;
invariance produit `eq_produit_invariant` ; bon ordre cardinaux `cardinaux_bien_ordonnes_close` ;
(14)(18)(19) réciproque ; (22)(23)(26) produit ; C56/C57 ; Prop.1 équivalence.
OUI_PARTIEL (à compléter) : bijection {a}×F→F (seulement équipotence) ; (47-48) pointwise ;
bijectivité effective des quotients (E/R, décomposition canonique) — reportée « théorèmes durs ».
Puis résidus durs (audit famille B) : objet-conjugaison II.5 ; division euclidienne III.5.6
(dossier vide) ; Hessenberg a²=a inconditionnel III.6.3 ; limites III.7 ; cœur σ/Σ (Ch IV) ;
itérées f^n (dépend récursion entiers).

## Méthode multi-agent qui marche (pour le système IA)
- **Recon fan-out** (agents Explore, lecture seule) : pinner l'API exacte + énoncés fidèles +
  `@livre` + confirmer absence, EN PARALLÈLE. Puis **écrire la preuve INLINE** (le noyau donne
  un feedback exact et rapide ; la construction de preuve reste séquentielle — cf. τ-lock).
- **Probe-first** : tester empiriquement un primitif douteux (ex. `graphe_terme_valeur` capture
  le liant « y » si le terme contient `valeur(·)` → liants frais) AVANT d'écrire 150 lignes.
- **Cible == énoncé reconstruit indépendamment** dans le test (`cible_*`), + `est_clos` + `theorie==22`.

## Ledger
| Date | Cible | Verdict | Action |
|------|-------|---------|--------|
| 2026-07-01 | Complément (5 lois) | déjà CLOS (faux positif audit) | aucune ; loggé |
| 2026-07-01 | permutation, involution récip. | déjà présents | aucune ; loggé |
| 2026-07-01 | Symétrie canonique E×F≅F×E | déjà CLOS (2e faux positif) | aucune ; loggé |
| 2026-07-01 | Passe batch 7 agents (present/absent EN CODE) | liste absente définitive | queue mise à jour |
| 2026-07-01 | **Triplet + 3 projections** | absent → **FORMALISÉ CLOS** | `ensembles_triplet.py` + test (51 verts) |
