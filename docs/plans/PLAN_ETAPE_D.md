# PLAN ETAPE D -- cibles issues de l'audit Chap IV + Résumé (workflow wlddmzbc4, 2026-06-26)

Audit fan-out 5 lecteurs (Chap IV structures p.204-231 + Résumé p.305-309), notions NOMMÉES classées
contre `bourbaki/structures/` et `bourbaki/ensembles/`. Bilan : **132 notions — 59 closes, 46 partielles,
27 absentes, 8 closables**.

Chap IV : très couvert. Le gros des 46 partiels = **schémas CST** (CST1/CST2/CST3…) prouvés seulement en
INSTANCES (identité, cas objet) ; la preuve générale par **récurrence sur le schéma d'échelon** est reportée
(méta — gros chantier, hors palier simple). NE PAS forcer ici.

Règle (comme ETAPE C) : implémenter UNE cible à la fois, preuve CLOSE (primitives N.* only), `theorie==22`
(ou dépendance S8/théorie-dédiée DOCUMENTÉE si la notion l'exige réellement — cf. ANOMALIES 2026-06-26),
énoncé==livre calé PDF, test qui APPELLE le théorème, vérif indépendante AVANT commit. Re-vérifier l'absence
(grep) au début de chaque délégation.

---

## Lot Résumé — algèbre des parties (Chap II, énoncés listés au Résumé E.R)
*Ces résultats sont du contenu Chap II.1 (algèbre des parties) résumé en E.R ; les placer dans les dossiers
thématiques `bourbaki/ensembles/` (ii_1_algebre_booleenne / ii_1 selon le thème), PAS un dossier « Résumé ».*

## [x] resume_egalite_leibniz_parties  [E.R.3 n°11 | PDF p.306]  — FAIT (2026-06-26 ; |- ((x=y)⇔(∀X)(x∈X⇒y∈X)) clos ; S6 pour ⇒, témoin {x}+appartient_singleton pour ⇐ ; verif indep concl==cible, est_clos, theorie==22, pur 22-ax ; ii_1_algebre_booleenne/)
- enonce: `|- (x=y) ⇔ (∀X)((x∈X) ⇒ (y∈X))`  (égalité = appartenir aux mêmes parties).
- note audit: absent (grep négatif). Cible logique : S6/Leibniz (⇒) + extensionnalité/instanciation X:={y} ou X∋x (⇐).
- fichier: à placer (Chap II ; vérifier cap dossier). PDF p.306 (offset Résumé +303 → E.R.3).

## [x] resume_disjonction_complement  [E.R.4 n°14e | PDF p.307]  — FAIT (2026-06-26 ; {inclus(X,E)} |- (X∩Y=∅ ⇔ X⊂∁_E Y) ; hyp X⊂E HONNÊTE = contexte « parties de E » du n°14 ; verif indep concl==cible, theorie==22, pur 22-ax. 3e terme Y⊂∁X non ajouté.)
- enonce: `|- (X∩Y=∅) ⇔ (X⊂∁Y)`  (+ ⇔ (Y⊂∁X) si faisable d'un bloc).
- note audit: absent. Extensionnalité + lois du complément déjà présentes (ii_1_algebre_booleenne).

## [x] resume_recouvrement_complement  [E.R.4 n°14f | PDF p.307]  — FAIT (2026-06-26 ; {X⊂E,Y⊂E} |- (X∪Y=E ⇔ ∁_E X⊂Y) ; 2 hyps honnêtes (X∪Y⊂E exige les deux) ; verif indep concl==cible, theorie==22, pur 22-ax)
- enonce: `|- (X∪Y=E) ⇔ (∁X⊂Y)`  (dual de 14e).
- note audit: absent. Dual ; mêmes lemmes.

## [x] resume_monotonie_union_inter  [E.R.5 n°14h | PDF p.308]  — FAIT (2026-06-26 ; verif indep concl==(X∪Z⊂Y∪Z et X∩Z⊂Y∩Z), hyps=={inclus(X,Y)}, theorie==22, pur 22-ax via AXIOME_REUNION/INTER ; ii_1_algebre_booleenne/)
- enonce: `|- (X⊂Y) ⇒ ( (X∪Z ⊂ Y∪Z) et (X∩Z ⊂ Y∩Z) )`  (monotonie de ∪/∩).
- note audit: absent au niveau binaire. Suit des lois de treillis des parties.

## [x] resume_inf_sup_universel_binaire  [E.R.5 n°14i | PDF p.308]  — FAIT (2026-06-26 ; 2 théorèmes clos : inf (Z⊂X et Z⊂Y⇔Z⊂X∩Y) + sup (X⊂Z et Y⊂Z⇔X∪Y⊂Z) ; verif indep concl==cible, est_clos, theorie==22, pur 22-ax ; ii_1_algebre_booleenne/)
- enonce: `|- ( (Z⊂X) et (Z⊂Y) ) ⇔ (Z ⊂ X∩Y)`  et  `|- ( (X⊂Z) et (Y⊂Z) ) ⇔ (X∪Y ⊂ Z)`.
- note audit: absent au niveau binaire (existe en version FAMILLES ii_4 sup/inf univ — possible spécialisation). VÉRIFIER d'abord si dérivable trivialement de la version familles.

## [x] resume_trace  [E.R.5 n°16 | PDF p.308]  — FAIT (2026-06-26 ; déf trace(X,A)=A∩X + 3 identités : (1)∪-distrib clos, (2)∩ clos (idempotence), (3)∁ sous {inclus(A,E)} honnête ; verif indep concls==cibles, theorie==22, pur 22-ax ; ii_1_algebre_booleenne/ 8→9)
- enonce: déf `trace(X,A) := A∩X` + identités `(X∪Y)_A=X_A∪Y_A`, `(X∩Y)_A=X_A∩Y_A`, `∁_A X_A=(∁_E X)_A`.
- note audit: absent (déf + 3 props, NOUVELLE). Plus lourd (une déf + 3 lemmes) — découper.

## [x] resume_fonction_constante  [E.R.6 §2 n°3 | PDF p.309]  — FAIT (2026-06-26 ; déf fonction_constante=fonction_terme(E,a,C) + graphe fonctionnel (clos, dépend théorie dédiée theorie_graphe_terme héritée — documenté) + valeur=a sous {u∈E} ; 2 propriétés == les 2 assertions verbatim de n°3 ; verif indep, theorie==22 ; ii_3_6_fonction_terme/)
- enonce: déf fonction constante (valeur a ; relation fonctionnelle y=a).
- note audit: absent (ni `est_constante` ni fonction constante). Cible simple : définition dédiée. (Chap II.3 fonctions.)

---

## Chap IV — cible logique propre
## [x] cst8_inversibilite_implique_iso  [E IV.12 CST8 | PDF p.215]  — FAIT (2026-06-26)
- FAIT : `iv_2_morphismes_structures_derivees/ensembles_cst8_inversible_iso.py` :
  `{ morph(E,𝒮,E',𝒮',f), morph(E',𝒮',E,𝒮,g), g=f⁻¹ } |- est_iso_morph(E,𝒮,E',𝒮',f) = morph(f) ∧ morph(f⁻¹)`.
  Inversibilité bilatère résumée fidèlement par son conséquent `g=f⁻¹` (= corollaire II.18, brique reportée
  comme CST3/12/20). Vérif indép : conclusion==cible reconstruite depuis primitives BRUTES, hyps EXACTES=ces 3,
  est_clos=False (conditionnel), theorie==22, pas de _CLE/Theoreme/N.Theorie, 5 tests verts, dossier 8/10.
- ⚠️ MISMATCH ÉTIQUETTE rapporté dans ANOMALIES (2026-06-26), NON corrigé : deux fonctions nommées `CST8`
  (`ensembles_structures_complements.py:324` avec @livre fautif E IV.12 p.215 ; `ensembles_structures_props.py:377`)
  encodent en fait le critère IV.3.1 « unicité solution universelle à iso près ». À auditer côté PDF (E IV.27/p.~230).

---

## Partiels notables (NON cibles immédiates — reportés/méta)
- **CST1/CST2/CST3** (fonctorialité / inj-surj / réciproque de l'extension canonique ⟨f⟩^S) : prouvés en
  INSTANCES seulement (identité, objet) ; général = récurrence sur le schéma d'échelon → gros chantier méta.
- 46 partiels au total (extensions canoniques opaques au niveau objet, espèces niveau-objet, etc.). Voir
  sortie workflow wlddmzbc4 pour le détail.
