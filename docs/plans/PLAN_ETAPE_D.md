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

## [ ] resume_egalite_leibniz_parties  [E.R.3 n°11 | PDF p.306]
- enonce: `|- (x=y) ⇔ (∀X)((x∈X) ⇒ (y∈X))`  (égalité = appartenir aux mêmes parties).
- note audit: absent (grep négatif). Cible logique : S6/Leibniz (⇒) + extensionnalité/instanciation X:={y} ou X∋x (⇐).
- fichier: à placer (Chap II ; vérifier cap dossier). PDF p.306 (offset Résumé +303 → E.R.3).

## [ ] resume_disjonction_complement  [E.R.4 n°14e | PDF p.307]
- enonce: `|- (X∩Y=∅) ⇔ (X⊂∁Y)`  (+ ⇔ (Y⊂∁X) si faisable d'un bloc).
- note audit: absent. Extensionnalité + lois du complément déjà présentes (ii_1_algebre_booleenne).

## [ ] resume_recouvrement_complement  [E.R.4 n°14f | PDF p.307]
- enonce: `|- (X∪Y=E) ⇔ (∁X⊂Y)`  (dual de 14e).
- note audit: absent. Dual ; mêmes lemmes.

## [x] resume_monotonie_union_inter  [E.R.5 n°14h | PDF p.308]  — FAIT (2026-06-26 ; verif indep concl==(X∪Z⊂Y∪Z et X∩Z⊂Y∩Z), hyps=={inclus(X,Y)}, theorie==22, pur 22-ax via AXIOME_REUNION/INTER ; ii_1_algebre_booleenne/)
- enonce: `|- (X⊂Y) ⇒ ( (X∪Z ⊂ Y∪Z) et (X∩Z ⊂ Y∩Z) )`  (monotonie de ∪/∩).
- note audit: absent au niveau binaire. Suit des lois de treillis des parties.

## [ ] resume_inf_sup_universel_binaire  [E.R.5 n°14i | PDF p.308]
- enonce: `|- ( (Z⊂X) et (Z⊂Y) ) ⇔ (Z ⊂ X∩Y)`  et  `|- ( (X⊂Z) et (Y⊂Z) ) ⇔ (X∪Y ⊂ Z)`.
- note audit: absent au niveau binaire (existe en version FAMILLES ii_4 sup/inf univ — possible spécialisation). VÉRIFIER d'abord si dérivable trivialement de la version familles.

## [ ] resume_trace  [E.R.5 n°16 | PDF p.308]
- enonce: déf `trace(X,A) := A∩X` + identités `(X∪Y)_A=X_A∪Y_A`, `(X∩Y)_A=X_A∩Y_A`, `∁_A X_A=(∁_E X)_A`.
- note audit: absent (déf + 3 props, NOUVELLE). Plus lourd (une déf + 3 lemmes) — découper.

## [ ] resume_fonction_constante  [E.R.6 §2 n°3 | PDF p.309]
- enonce: déf fonction constante (valeur a ; relation fonctionnelle y=a).
- note audit: absent (ni `est_constante` ni fonction constante). Cible simple : définition dédiée. (Chap II.3 fonctions.)

---

## Chap IV — cible logique propre
## [ ] cst8_inversibilite_implique_iso  [E IV.12 CST8 | PDF p.215]
- enonce: `{ f σ-morphisme E→E', g σ-morphisme E'→E, g∘f=Id_E, f∘g=Id_E' } |- f isomorphisme de E sur E' (et g l'iso réciproque)`.
- ⚠️ MISMATCH ÉTIQUETTE à corriger : les fonctions code nommées `CST8` (solution_isomorphisme_unique,
  solution_universelle_iso_unique, @livre E IV.12) encodent en fait le CST8 « unicité de la solution universelle
  à iso près » (IV.3.1, p.235) — énoncé DIFFÉRENT. Le vrai CST8 « inversibilité ⟹ iso » (E IV.12, IV.2.1) est
  ABSENT. Auditer/corriger les @livre fautifs en même temps.
- fichier: bourbaki/structures/iv_2_morphismes_structures_derivees/ (vérifier cap).

---

## Partiels notables (NON cibles immédiates — reportés/méta)
- **CST1/CST2/CST3** (fonctorialité / inj-surj / réciproque de l'extension canonique ⟨f⟩^S) : prouvés en
  INSTANCES seulement (identité, objet) ; général = récurrence sur le schéma d'échelon → gros chantier méta.
- 46 partiels au total (extensions canoniques opaques au niveau objet, espèces niveau-objet, etc.). Voir
  sortie workflow wlddmzbc4 pour le détail.
