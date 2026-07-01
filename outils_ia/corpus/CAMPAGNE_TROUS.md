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
1. ✅ **(24) pr₁⁻¹(X)=X×F** — Résumé §3 item 3e — **FAIT / CLOS**
   (`ii_3_2_reciproque/ensembles_projection_reciproque_produit.py`, `pr1_reciproque_produit` :
   ⊢ X⊂E ⇒ image(reciproque(graphe_terme(E×F,pr₁(k),'k')), X) = X×F, 0 hyp, theorie==22 ;
   commit 7980160, 2 tests verts).
   ⭐ **LEÇON τ (réutilisable, distincte du nœud « z »)** — quand un LEMME lie un existentiel à
   un nom fixe (ici `membre_image_reciproque` lie « x ») et qu'un TERME du graphe lie le MÊME
   nom (pr₁(k)=τx(∃y(k=(x,y)))), la collision est fatale (couple_reciproque casse) ET le
   renommage-α est IMPOSSIBLE (le round-trip x→s→x recapture le τx → liant « @0 » qui ne
   s'aligne plus). FIX : ne PAS renommer l'existentiel ; construire le TERME (pr₁) avec un liant
   FRAIS « i1 » via un portage binder-configurable du lemme de projection (`_proj1`), utilisé
   PARTOUT de façon cohérente (terme de G, `_mgt`, reconstruction du couple). Les liants α-variant
   NE sont PAS égaux dans ce noyau (τi1≠τx littéralement) → cohérence obligatoire. pr₂ garde son
   liant par défaut car il n'apparaît JAMAIS sous l'existentiel. Rebinder final « t »→« z » (A1).
   Pièges annexes : membre_image_reciproque/couple_reciproque renvoient des ÉQUIVALENCES → toujours
   `equivalence_avant/arriere` avant un MP ; `_reconstruction_couple` ASSUME t∈A×B → décharger avec
   le t∈A×B DÉRIVÉ (sinon « t libre dans une hypothèse » au generalisation).
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
5. ✅ **Eq(E,F) ⇒ Eq(𝔓E,𝔓F)** — Résumé §7 item 1 — **FAIT / THÉORÈME CLOS**
   (`parties_equipotentes/ensembles_parties_equipotentes.py`, `equipotent_parties` :
   ⊢ Eq(E,G)⇒Eq(𝔓E,𝔓G), 0 hyp, énoncé==Bourbaki, theorie==22 ; 7 tests verts, commits
   5dd3580 pilier 4 + f8073cf assemblage). Témoin H=graphe_terme(𝔓E, f⟨Y⟩,'Y'). Piliers :
   1 fonctionnel / 2 dom=𝔓E (inconditionnels, image(·,·) ATOMIQUE ⇒ pas de capture-τ) ;
   3 injective via f⁻¹∘f=Id sur les parties (`image_reciproque_image_egal_si_injective`)+A1 ;
   4 image via f∘f⁻¹=Id (`image_image_reciproque_egal_si_surjective`)+A1, témoin Y=f⁻¹⟨Z⟩.
   ⭐ **LEÇON PILIER 4 — comment DÉNOUER le nœud de liants « z » (technique réutilisable).**
   Problème : dans une double inclusion via A1 (`extensionnalite_appliquee`), l'élément est
   VERROUILLÉ au liant de A1 = « z » (A1 encode ⊂ avec `inclus(...,z='z')`). Mais « z »
   collisionne avec (a) le liant interne « z » de `est_fonctionnel` (3ᵉ variable), et (b) le
   liant par défaut « z » de `inclus` dans les antécédents Z⊂f⟨E⟩ des lemmes de surjectivité,
   et (c) l'auto-fraîcheur de inclus(f⁻¹⟨z⟩,E) car z est LIBRE dans f⁻¹⟨z⟩. La substitution
   du noyau, PRUDENTE, α-renomme alors des liants en « @0 » qui ne s'alignent plus entre
   sous-preuves bâties indépendamment (MP « mineure ≠ antécédent »).
   **FIX qui marche** : mener TOUT le raisonnement-témoin de la direction ⊃ avec un élément
   NEUTRE « p » (jamais « z ») — zéro collision partout — pour prouver `⊢ p∈PF ⇒ p∈im(H,𝔓E)`,
   PUIS renommer le liant en « z » seulement au tout dernier `generalisation` via
   `generalisation("z", instancie(generalisation("p", corps_p), var("z")))`. Marche parce
   que les DEUX membres (p∈PF, p∈im) sont ATOMIQUES → aucun liant interne à renommer, donc
   ∀z(...) reconstruit == `inclus(PF, imgHPE, 'z')` exactement (ce qu'attend A1). La direction
   ⊂ (membres atomiques aussi) tolère « z » directement.
   ⭐ **Term-wrappers indispensables** (lemmes n'acceptant que des NOMS → généraliser+instancier
   un SET-nom ≠ élément) : `_mgt` (membre_graphe_terme), `_recip_inclus_E` (f⁻¹⟨Z⟩⊂E),
   `_feq_surj` (f∘f⁻¹=Id) — le SET interne est « Zs » (≠ « z »/« p »), d'où pas de capture.
   ⭐ **Assemblage final (bridges RÉUTILISÉS, tous déjà en dépôt — vérifier-en-code paie)** :
   `couple_valeur_dans_graphe` (H_app depuis dom f=E) ; `reciproque_fonctionnelle`
   ({func f,dom f=E,inj(f,E)}⊢func(f⁻¹), = Prop.7) ; `bijection_de_conjoints` (assembleur pur
   des 4 conjoints en est_bijection_de) ; S5 pour ∃-intro + `existe_elimination` pour extraire
   f. **Hygiène de liants de `equipotent`** : Eq(X,Y)=(∃F)bij(F,X,Y) lie « F » → le codomaine
   ne doit PAS s'appeler « F » (sinon capturé) ⇒ 2ᵉ ensemble nommé « G » ; et le témoin de
   Eq(E,G) est α-renommé « F »→« f » (`alpha_existe`) pour que H=graphe_H(f,E) soit sans « F ».
   Piège persistant : couple_reciproque/couple_egal_implique_composantes lient « w » (ne pas
   nommer un témoin « w »).
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
| 2026-07-01 | **Eq(E,F)⇒Eq(𝔓E,𝔓F)** (Résumé §7.1) | absent → **THÉORÈME CLOS** | `equipotent_parties` (commits 5dd3580+f8073cf) ; nœud de liants « z » du pilier 4 levé par élément NEUTRE « p » + renommage-au-generalisation-final ; assemblage via couple_valeur_dans_graphe + reciproque_fonctionnelle + bijection_de_conjoints + S5 ; 7 tests verts |
| 2026-07-01 | **(24) pr₁⁻¹(X)=X×F** (Résumé §3.3e) | absent → **CLOS** | `pr1_reciproque_produit` (commit 7980160) ; nœud τ (existentiel « x » de membre_image_reciproque vs τx de pr₁) levé par liant FRAIS « i1 » pour pr₁ (`_proj1` binder-configurable), α-rename impossible (recapture) ; 2 tests verts |
| 2026-07-01 | **Pont surjectivité image↔valeur** (§II.3, REPORTÉ) | absent → **CLOS** | `surjective_image_donne_valeur` (commit 5f6d8fb) : est_fonctionnel(f)⇒(∀y∈f⟨A⟩)(∃x∈A)y=f(x) ; AXIOME_IMAGE + valeur_caracterisation ; 2 tests verts. Débloque la moitié « image→valeur » de section_construite_par_tau |
| 2026-07-01 | **Prop.2 Corollaire bijectif** (§II.5.2 E II.31) | **BLOQUÉ (REPORTÉ confirmé)** | Vérif ultracode (workflow 5 agents) : PAS un assemblage tractable malgré 1er recon optimiste. 1° needs s=section(u)+r=retraction(v) ; 2° needs rp=retraction(u)+sp=section(v) → 4 maps. section/retraction_construite_par_tau émettent le témoin τ INLINÉ (u(τx(y=u(x)))=y), ≠ le composé OPAQUE valeur(u,valeur(s,p)) de H8/H10 (s symbole libre) → PAS α-égaux, MP impossible. Emballer le τ-témoin en OBJET-graphe section re-déclenche le verrou-τ. Le pont image↔valeur (1 des 2 bloqueurs) est MAINTENANT fait ; RESTE le bloqueur OBJET-τ. NE PAS retenter l'assemblage naïf |
| 2026-07-01 | **section_compose_valeur** (§II.3.8 Déf.11) | absent(REPORTÉ) → **CLOS** | commit d53a089 : (u∈B)⇒(f∘s)(u)=u, dual carbone de retraction_compose_valeur. Piège levé : est_section défaut lie « y »=liant interne de valeur → self-capture ; passer y=point « u ». Ajouté dans ensembles_composee_valeurs.py ; 3 tests verts |

### File d'attente du hunt (6 agents, 2026-07-01) — ⚠️ RÉVISÉE après verify-in-code
**LEÇON : le hunt-workflow a produit des FAUX POSITIFS** (agents ont grep le nom proposé, pas
les variantes → raté des lemmes existants sous d'autres noms dans ii_4_image_famille). LEÇON N°1
s'applique AUSSI à la sortie des agents/workflows : re-grep le CONTENU avant de formaliser.
1. ~~image_reunion_famille~~ **FAUX POSITIF** — déjà clos = `image_reunion_egal` (Γ⟨⋃X⟩=⋃Γ⟨X⟩, ii_4_image_famille).
2. ~~image_inter_famille_inclusion~~ **FAUX POSITIF** — déjà clos = `image_inter_incluse` (Γ⟨⋂X⟩⊂⋂Γ⟨X⟩, idem).
3. **monotonie_reunion_sous_indices_image** — grep négatif (peut-être absent) ; NON re-vérifié à fond, se méfier.
4. ✅ **f∘id=f / id∘f=f au niveau VALEUR** — **FAIT** (commit 48988e0) : `composee_diagonale_neutre_valeur`
   (G∘Δ_A)(x)=G(x) + dual, corollaires de Leibniz des neutralités-graphe. Bien plus simple que le
   plan « moderate » du hunt (pas besoin de composition_valeur_t : congruence directe sous valeur(·,x)).
5. ⚠️ **composition_associative_valeur** — risque τ RÉEL (composition_valeur_t en point-valeur τ, capture « y »). Technique liant-frais requise. NON vérifié absent à fond.
6. **equipotent_singletons** (E III.23) — import cardinaux LOURD (tests 13-18 min) ; NON vérifié.
→ Reste à re-vérifier-en-code #3, #5, #6 avant tout effort. Les gains rapides fonctions/valeurs sont quasi saturés.

## CARTE EXACTE du front (re-vérifiée EN CODE, 2026-07-01) — les docs étaient STALE
Audit fiable (exécution/grep du code, pas les docs) des « gros chantiers » :
- **Cantor 2^a>a = FAIT** (`cantor_strict` ⊢ X<P(X) CLOS) ; **Hessenberg a²=a = ASSEMBLÉ**
  (`hessenberg/assemblage_vrai`) ; **Cantor-Bernstein = FAIT** ; **divisibilité entiers = FAIT**
  (`divise`/`est_diviseur`/`multiple_ssi_divise`, hors dossier iii_5_6 vide → « dossier vide » FAUX signal).
- **VRAI trou restant = division euclidienne EXISTENCE** (a=bq+r,r<b, th.1 REPORTÉ) **BLOQUÉ** :
  l'arithmétique binaire entière b·q+r n'est PAS un terme (`plus_ent`/`prod_ent` opaques) ⇒ exige de
  bâtir toute l'arithmétique binaire entière d'abord (multi-chantier). Idem `puissance_entiers` a^b.
- Partiels non exhaustivement audités : limites III.7 (familles), structures Ch IV (IV.1/IV.2).
→ **Front rapide+medium SATURÉ.** Restant = deep-fondational (arith. entière→division) ou verrou-τ objet.
Décision : campagne multi-tick entiers OU T1 set.mm (carte fiable). NE PAS re-auditer ces chantiers.
