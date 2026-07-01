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
- (Rappel session : II.5 Prop.2 conjugaison 1°+2° + `retraction_construite_par_tau`, cf. git.)

## File d'attente — cibles grep-ABSENTES (à confirmer par recon puis formaliser)
Priorité tractabilité (Résumé / II.2–II.3) :
1. **Symétrie canonique `E×F ≅ F×E`** via (x,y)↦(y,x) — Résumé §3 item 4 (PDF p.137). [EN RECON]
2. **Produit ternaire `E×F×G` + triplets + assoc. canonique** — Résumé §3 item 12 (p.139).
3. **Itérées `f^n`** — Résumé §2 item 11 (p.113) — dépend récursion entiers (plus lourd).
4. **Application majorée/minorée/bornée + borne sup d'une application** — Résumé §6 item 7 (p.221).
5. **Familles `(X_ι)` croissantes/décroissantes de parties** — Résumé §6 item 12 (p.223).
Puis résidus durs (audit famille B) : objet-conjugaison II.5 ; division euclidienne III.5.6
(dossier vide) ; Hessenberg a²=a inconditionnel III.6.3 ; limites III.7 ; cœur σ/Σ (Ch IV).

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
| 2026-07-01 | Symétrie canonique E×F≅F×E | grep-absent | recon lancé |
