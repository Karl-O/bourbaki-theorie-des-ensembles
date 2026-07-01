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
1. **(24) pr₁⁻¹(X)=X×F** — Résumé §3 item 3e (image réciproque de projection).
   ✅ (25) `pr₁⟨X×Y⟩=X` (Y≠∅) + dual `pr₂⟨X×Y⟩=Y` (X≠∅) FAIT
   (`ii_3_correspondances/ensembles_projection_produit.py`, `pr1_produit`/`pr2_produit` CLOS).
2. ✅ **(17) f⁻¹(Y)=f⁻¹(Y∩img f)** — Résumé §2 item 7 FAIT
   (`fonctions/ii_3_2_reciproque/ensembles_reciproque_intersection_image.py`, CLOS,
   inconditionnel via img f = pr₂⟨f⟩). Piège : membre_image_reciproque lie « x » (=liant
   AXIOME_IMAGE) → couple_dans_img casse (lie « x » aussi) ; contourné par couple_dans_dom
   (liant « y ») sur f⁻¹ + pr1_reciproque (dom f⁻¹=img f).
3. ✅ **Application majorée/minorée/bornée + borne sup/inf d'application** — Résumé §6 item 7
   FAIT (`ordre/iii_1_relations_ordre/ordre_treillis/ensembles_application_bornee.py` :
   5 défs via img F + 4 th CLOS : borne sup⇒majorée, bornée⇒majorée/minorée…).
4. ✅ **Familles `(X_ι)` croissantes/décroissantes de parties** — Résumé §6 item 12
   FAIT (`familles/ii_4_reunion_intersection_familles/ensembles_famille_monotone.py` :
   2 défs via valeur_famille + inclus, + 2 th de dépliage CLOS).
5. **Eq(E,F) ⇒ Eq(𝔓E,𝔓F)** — Résumé §7 item 1. ⏳ EN COURS : recon (2 agents) confirme
   ABSENT ; témoin H=graphe_terme(𝔓E, f⟨Y⟩, 'Y') ; FONDATION CLOSE (pilier 1 fonctionnel,
   pilier 2 dom=𝔓E, valeur H(Y)=f⟨Y⟩ — image(·,·) est ATOMIQUE donc pas de capture-τ).
   PILIER 3 amorcé : `image_reciproque_image_inclus_si_injective` (f⁻¹⟨f⟨X⟩⟩⊂X sous
   est_fonctionnel(f⁻¹)=f injective) CLOS dans `ii_3_2_reciproque/ensembles_image_reciproque_props.py`
   — miroir de (19) sur f⁻¹ ; combiné à (18) donne f⁻¹⟨f⟨X⟩⟩=X ⇒ f⟨Y⟩=f⟨Y'⟩⇒Y=Y'.
   Piège : couple_reciproque appelle couple_egal_implique_composantes qui lie « w » →
   ne PAS nommer un témoin « w » (renommé « m »).
   PILIER 3 CLOS : `H_injective` (⊢ H_app(E,f) ⇒ f⁻¹func ⇒ injective_dans(H,𝔓E)) via
   f⁻¹(f(Y))=Y + congruence. Piliers 1,2,3 + valeur FAITS. CŒURS piliers 3+4 clos
   (f⁻¹∘f=Id, f∘f⁻¹=Id sur 𝔓) + f⁻¹⟨Z⟩⊂E — tous dans ensembles_image_reciproque_props.py.
   RESTE : ASSEMBLAGE pilier 4 image(H,𝔓E)=𝔓F (témoin Y=f⁻¹⟨Z⟩) + est_bijection_de + ∃-intro.
   ⚠️ LEÇON PILIER 4 (assemblage repoussé) — NŒUD DE LIANTS : l'élément-image est FORCÉ à
   « z » par extensionnalite_appliquee/inclus (A1 lie « z »), mais « z » collisionne avec
   (a) les liants internes des lemmes appelés, et (b) le liant auto-frais de inclus(f⁻¹⟨z⟩,E)
   puisque z est LIBRE dans f⁻¹⟨z⟩. Correctifs à appliquer au prochain tick : (1) beaucoup de
   lemmes n'acceptent QUE des NOMS, pas des termes → wrapper term-version par
   generalisation+instanciation (fait `_mgt` pour membre_graphe_terme ; idem image_croissante
   [passer des noms], image_reciproque_inclus_domaine [SET=nom≠« z », puis généraliser]) ;
   (2) nommer l'élément-image autrement que « z » et construire l'inclus final avec un liant
   EXPLICITE cohérent (ne pas dépendre de l'auto-fraîcheur). Bâtir d'abord tous les
   term-wrappers, PUIS assembler. Piège récurrent : couple_reciproque/couple_egal_implique_
   composantes lient « w ».
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
| 2026-07-01 | **(25) pr₁⟨X×Y⟩=X (Y≠∅) + dual** | absent → **FORMALISÉ CLOS** | `ensembles_projection_produit.py` + test (piège : couple_dans_produit n'accepte que des NOMS → couple_dans_produit_ssi qui prend des termes) |
| 2026-07-01 | **Application majorée/minorée/bornée + bornes** | absent → **FORMALISÉ CLOS** | `ensembles_application_bornee.py` (5 défs + 4 th) ; ordre_treillis atteint 10 entrées |
| 2026-07-01 | **Familles croissantes/décroissantes de parties** | absent → **FORMALISÉ CLOS** | `ensembles_famille_monotone.py` (2 défs + 2 th) ; piège : pourtout a tag « non » (¬∃¬), pas « pourtout » |
