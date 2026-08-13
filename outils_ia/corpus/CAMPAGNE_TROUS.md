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

## JALON 1 du système IA auto-améliorant (2026-07-01) — organe SLEEP-abstraction CONSTRUIT
Suite au design multi-agent (3 architectes DreamCoder/AlphaProof/société-d'experts → convergence),
le 1er organe du volant wake-sleep est bâti et VALIDÉ sur le vrai corpus rapide (102 modules,
490 preuves). Deux outils, aucun ne touche la frontière (analyse AST + gate noyau, `theorie==22`) :
- **`outils_ia/corpus/antiunif_notions.py`** — l'ANTI-UNIFICATEUR (la brique manquante identifiée
  pas 16-suite) : dual du remplisseur-de-slots du TreeNN. Sur les N instances d'une macro (n-gramme
  `(fn,arité)` de `proto_library_learning`), calcule le least-general-generalization = TEMPLATE +
  SLOTS (positions divergentes = paramètres). Deux clés : (1) **α-normalisation** des locales
  assignées dans le bloc (`_v0…`) sinon les noms de dataflow parasitent tout — c'est CE QUI
  manquait à la mesure « verbatim ~0 % » du pas 14/16 ; après α-norm on retrouve 105 blocs 0-slot
  inter-modules ; (2) anti-unif STRUCTURELLE générique (`ast.iter_fields`) → slot au bon grain.
  Résultat empirique : détecte EXACTEMENT les slots prédits — `{pr1,pr2}`, `{AXIOME_PAIRE,RÉUNION,
  INTER}`, `{identite_projectif,inductif}`, littéraux `'x'/'y'`. Histogramme #params : 0→105,1→63,
  2→100,3→197,… (1310 macros inter-preuves).
- **`outils_ia/corpus/promo_notion.py`** — PROMOTION en tactique dérivée + **GATE noyau (MDL)** :
  params = entrées-libres (`p…`) ∪ slots ; émet `def notion_…`; réécrit CHAQUE preuve (bloc→1 appel)
  et RE-VÉRIFIE au noyau (`_statut`, OK==conclusion==cible). Garde SSI toutes re-passent + corpus
  strictement plus court. DRY-RUN (préflight, ne mute pas `bourbaki/`).
- **Tests** : `test_antiunif_notions.py` (4 verts, AST pur, 2 s).

**Résultat (funnel honnête sur 155 candidates)** : 75 désalignées (n-gramme `(fn,arité)` GROSSIER →
faux-jumeaux structurels), 57 gate-fail, 21 gain≤0, **2 PROMUES** kernel-OK : `notion_modus_ponens…`
(réutilisée dans 5 preuves) et `notion_instancie…` (3 preuves). **Le gate n'a JAMAIS admis un
théorème faux** — le noyau juge chaque réécriture (soundness sauve, comme prévu).

**LEÇONS (données pour le méta-algo)** :
1. La boucle *invente→nomme→certifie→compresse* TOURNE end-to-end sur noyau+corpus réels.
2. Point dur n°1 de la synthèse CONFIRMÉ empiriquement : gains petits + peu de notions sur PETIT
   corpus rapide — le flywheel est borné par la TAILLE/DIVERSITÉ du corpus, pas l'outillage.
3. Le n-gramme `(fn,arité)` est un pré-filtre grossier ; l'anti-unif + le gate noyau sont le VRAI
   filtre (75+57 rejets légitimes). Améliorable : matcher sur l'AST des args, pas juste la signature.
4. MDL récompense le FRÉQUENT pas le FÉCOND (notions promues = blocs-utilitaires, pas « Galois »).
   La vraie invention de notion féconde exige un signal prospectif (réutilisation future) = front ouvert.
→ **JALON 2** possible : brancher une notion promue dans le solveur (proto_synth) et re-mesurer la
couverture leave-one-module-out — tester l'hypothèse pas 22-25 (réifier les macros ↑ couverture SANS
données neuves). OU **muter réellement** le dépôt (outil transactionnel préflight+rollback) sur les 2
notions promues. Voir [[bourbaki-jalon1-organe-abstraction]].

## JALON 2 (2026-07-01) — le volant COMPOSE (compounding démontré), `flywheel.py`
`outils_ia/corpus/flywheel.py` assemble les organes en UN tour wake-sleep et MESURE ce qui distingue
« s'auto-améliorer » de « accumuler ». WAKE = corpus clos ; SLEEP-abstraction = `promo_notion.promouvoir`
(refactoré pour exposer les notions + leur empreinte par preuve) ; MESURE + persistance. Résultat :
- **(1) Portée sous budget CAP AVANT/APRÈS** (une notion = 1 primitif ⇒ preuve plus courte ⇒ passe sous
  le CAP) : à CAP=15 **+2 preuves** atteignables (`theoreme1_a/b_…valeur` 16→14 pas franchissent 15) ;
  à CAP=10 **+2** (`theoreme1_f…` 12→10, `section_implique_surjective_valeur` 11→10). 5 preuves raccourcies.
  C'est LE mécanisme du compounding (`compounding_loop` de la synthèse), mesuré avec des notions
  kernel-certifiées — pas une promesse.
- **(2) Compounding d'ORDRE 2** (signal DreamCoder) : re-miner le corpus COMPRESSÉ trouve **18 macros
  récurrentes qui UTILISENT une notion promue** (`assume → notion_instancie_3p_25 → modus_ponens`, 3
  preuves). Une notion du tour t devient une brique d'un motif de plus haut niveau → le tour t+1
  promouvrait des notions de 2ᵉ ordre = découvrir en profondeur croissante.
- **(3) Persistance** : `notions_apprises.py` (bibliothèque apprise, régénérée chaque tour) + journal
  `flywheel_journal.jsonl` (tour #, funnel, gain MDL, ordre2, cap_gain) = l'actif qui grossit.

**LEÇON** : la boucle *invente→nomme→certifie→compresse→**mesure la portée gagnée*** tourne
end-to-end ; le compounding est RÉEL (deux signaux indépendants), à petite échelle (corpus rapide petit).
Prochain cran naturel : **promouvoir les notions de 2ᵉ ordre** (gate noyau sur des tactiques qui
appellent la biblio) = fermer visiblement la spirale ; puis JALON 3 (conjectureur mutation-de-but).

## JALON 3 (2026-07-01) — le CONJECTUREUR (trouve des problèmes & les résout), `conjecturer.py`
`outils_ia/corpus/conjecturer.py` réalise la vision « trouver des problèmes → solutions » dans le SEUL
régime qui fire (pas 39-41 : forward guidé par TERME PARTAGÉ). Deux moteurs, tous deux tranchés noyau :
- **TRANSITIVITÉ** : `T1 ⊢ A⇒B`, `T2 ⊢ B⇒C` partageant B → conjecture `A⇒C`, prouvée en 4 pas noyau
  (`assume(A)` ; `modus_ponens` ×2 ; `loi_deduction(A, ·)`). Sound par construction.
- **DÉTACHEMENT** : `T ⊢ A⇒B` et A déjà prouvé → nouveau `⊢ B` (modus ponens).
La DÉCOUVERTE = l'énoncé est CLOS, absent du corpus, non trivial (A≠C). Aucun axiome, 22 intact.
- **Détail technique clé** : `impl(A,B) = ou(¬A, B)` ⇒ implication ssi `tag=='ou' & sous[0].tag=='non'`.
  Corpus MIXTE : `thm.conclusion` est soit `Formule` (couche abrégée `noyau_abrege`, a `.tag`) soit
  `Assemblage` (couche primitive `noyau`, pas de `.tag`) → `_comme_impl` protégé par `getattr(f,'tag')`,
  on ne conjecture que sur les Formule. (Piège rencontré : sinon crash `Assemblage has no attribute tag`.)
- **Résultat** (corpus rapide) : 158 théorèmes clos, 57 implications A⇒B → **1 nouveau théorème** clos
  certifié par transitivité (`graphe_egal_par_valeurs ∘ coincidence_meme_graphe`), 0 par détachement.
- **Test** : `test_conjecturer.py` (3 verts, via schémas S2/S3 du noyau).

**LEÇON** : le conjectureur MARCHE (trouve+prouve un vrai théorème neuf, noyau juge), mais l'appariement
EXACT (B==A) est strict → peu de conjectures sur ce corpus. Prochain cran = matching RELÂCHÉ (unification
à α-renommage près / sous-formule) pour élargir le pool — c'est là que le nombre de découvertes explose.
Rappel honnête : gains bornés par le corpus (verrou triangulé) ; formaliser plus reste le vrai levier.
→ Bilan : JALONS 1-3 buildables FAITS (organe d'abstraction, volant+compounding, conjectureur). Restent
JALON 4 (cadencer un tour complet flywheel+conjecturer dans `/loop`) et 5-7 (front-ouvert : POET,
définitions conservatives, GFlowNet). Voir [[bourbaki-jalon1-organe-abstraction]].

## JALON 4 (2026-07-01) — le BLACKBOARD qui tourne, `tour.py`
`outils_ia/corpus/tour.py` = point d'entrée UNIQUE d'un tour complet du système auto-améliorant.
Cadence en une passe les deux moitiés du volant : SLEEP-abstraction (`flywheel.executer`, refactoré
pour exposer la logique de tour + `_journaliser`) PUIS DÉCOUVERTE (`conjecturer`). Écrit un
enregistrement/tour dans `tour_journal.jsonl` (funnel, notions, gain MDL, ordre2, cap_gain,
implications, conjectures). Un appel = un tour de blackboard — c'est « cadencer le volant dans /loop ».
Run tour #1 : 2 notions promues (compounding +2 preuves sous CAP, 18 macros d'ordre 2) + 1 théorème
neuf découvert. Tout kernel-safe, 7 tests verts. Refactor flywheel validé (executer/main/tour importent).

**BILAN — JALONS BUILDABLES 1-4 TOUS FAITS.** Le système : (J1) invente des notions par compression
[antiunif_notions+promo_notion], (J2) les compose [flywheel : portée-CAP + ordre 2], (J3) trouve &
résout des problèmes [conjecturer], (J4) tourne en un tour cadencé [tour.py]. Restent : matching
RELÂCHÉ du conjectureur (unification à α-renommage près via generalisation+instancie — soundness
garantie car noyau juge le résultat final ; c'est là que le nb de découvertes explose) ; promotion
2ᵉ ordre ; fronts-ouverts 5-7 (POET/anti-collapse, définitions conservatives, GFlowNet/diffusion-DAG).
Rappel : gains bornés par le corpus rapide (petit) — FORMALISER plus reste le vrai levier exogène.

## Conjectureur — MATCHING RELÂCHÉ (2026-07-02) : découvertes ×50
Ajout à `conjecturer.py` : transitivité RELÂCHÉE. Au lieu d'exiger `B == A2` littéralement, on
UNIFIE l'antécédent de T2 avec B au 1er ordre (`_match`, lie les variables LIBRES de T2), puis on
applique σ à T2 **par le noyau** (`_instancier` = `instancie(N.generalisation(v, thm), t)` par var,
`instancie` ∈ `tactiques_abrege2`), et on chaîne. Les liaisons IDENTITÉ (`v→v`) sont filtrées (sinon
le cas exact se mislabellise `transit.σ`). **Soundness garantie** : le noyau construit le théorème
final et on vérifie `conclusion == cible` ⇒ un mauvais match ne fait que RATER une découverte, jamais
en fabriquer une fausse (le point qui rend le relâchement sans risque pour la frontière).
- **Résultat** : 1 → **50 nouveaux théorèmes** clos certifiés (tous `transit.σ`), ex.
  `produit_inclusion_facile ∘ pr1_reciproque_produit`, `couple_dans_produit ∘ produit_projections`,
  `inclus_image_reciproque_image ∘ image_croissante`. Tour #2 (`tour.py`) : 50 découvertes,
  frontière re-vérifiée **== 22 axiomes**. 9 tests verts (2 nouveaux : `_match` renommage + transit.σ).
- **LEÇON** : c'est LE levier de recall du conjectureur (l'exact était trop strict, cf. pas 41). Le
  noyau comme juge du résultat final = pourquoi on peut relâcher le matching SANS toucher la soundness.
  Prochains crans : détachement relâché aussi ; filtrer les découvertes « intéressantes » (bcp sont
  des variantes) ; promotion des notions de 2ᵉ ordre.

## Conjectureur — FILTRE D'INTÉRÊT + dédup + détachement relâché (2026-07-02)
Trois ajouts à `conjecturer.py` : (1) **dédup α-canonique** (`_cle_canon` : toutes variables renommées
par 1ʳᵉ apparition ⇒ les variantes à renommage près = UNE découverte ; nouveauté testée sur la clé
canonique, pas la forme littérale) ; (2) **détachement relâché** (symétrique de la transitivité :
`_match(A, φ)` d'une conclusion connue φ contre l'antécédent, instancié noyau, puis modus ponens) ;
(3) **score d'intérêt** `_interet` = (pont INTER-MODULES, distance de Jaccard des symboles
antécédent/conséquent, parcimonie) → tri qui fait remonter les vraies lemmes lisibles.
- Garde-fous corpus MIXTE : `_cle_canon` et `_match` protégés contre les `Assemblage` (pas de `.tag`).
- **Résultat** : **106 théorèmes distincts** (58 détachement + 48 transitivité), **101 PONTS
  inter-modules**. Top par intérêt = lemmes propres, ex. `dom(f)=E ⇒ image(G,image(f⁻¹,Z))⊂image(G,E)`
  (`image_reciproque_inclus_domaine ∘ image_croissante`), `pr1_produit ∘ image_reciproque_inclus_domaine`.
  Tour #3 : 106 découvertes, frontière **==22**, 9 tests verts.
- **LEÇON** : le tri par intérêt (pont inter-modules + symboles disjoints + parcimonie) est ce qui
  transforme « 100 variantes » en « quelques vraies lemmes » ; le pont inter-modules est le meilleur
  proxy de surprise. Prochain cran : promotion des notions de 2ᵉ ordre ; ou brancher ces théorèmes
  découverts comme nouvelles briques du conjectureur (tour t+1 chaîne sur les découvertes de t).

## Conjecture ITÉRÉE — découverte en PROFONDEUR croissante (2026-07-02) : compounding côté découverte
`conjecturer.iterer(impls, preuve_de, rounds, garder)` : les théorèmes trouvés au tour t deviennent
des BRIQUES (nommées `D<t>#k`, seules les `garder` meilleures par intérêt réinjectées) du tour t+1 ;
dédup α-canonique en agrandissant `connus` ⇒ chaque tour est strictement nouveau. `_profond(s1,s2)`
détecte les découvertes qui chaînent une brique `D<t>#…`. Option `--rounds N`.
- **Résultat** (corpus rapide) : tour 1 = 106, tour 2 = **109 (tous profondeur ≥2**, ex. `pr1_produit
  ∘ D1#1`, `D1#1 ∘ image_croissante`), tour 3 = **216 (tous profondeur ≥3**, ex. `pr1_produit ∘ D2#1`).
  **431 théorèmes** certifiés, 425 ponts inter-modules, frontière **==22**, 6 tests verts. Exemples
  profonds réels : `dom(f)=E ⇒ image(G,image(G,image(f⁻¹,Z)))⊂image(G,image(G,E))`.
- **LEÇON** : c'est le PENDANT côté découverte du compounding d'abstraction (ordre-2 macros) — le
  système découvre en profondeur croissante, chaque tour bâtissant sur le précédent, noyau juge, 22
  axiomes intacts. Les DEUX axes de la boucle auto-améliorante composent maintenant. NB : la
  complexité des énoncés croît avec la profondeur (nested image(G,image(G,…))) → le filtre d'intérêt
  (parcimonie) reste essentiel pour garder les découvertes lisibles ; un critère de « fécondité »
  (réutilisation prospective) reste le front-ouvert (MDL/intérêt récompensent le présent, pas le futur).

## Consolidation (2026-07-02) — `README_SYSTEME_AUTO_AMELIORANT.md`
Doc d'architecture du système auto-améliorant : les 8 organes (`antiunif_notions`, `promo_notion`,
`flywheel`, `notions_apprises`, `conjecturer`, `tour`, 2 tests, journaux), les DEUX axes avec leur
compounding, comment lancer un tour (`tour.py`), les métriques mesurées, la frontière (22 axiomes),
et le front-ouvert. **Bilan** : la partie BUILDABLE est complète sur ses deux axes ; le reste
(fécondité prospective, POET/anti-collapse, définitions conservatives, GFlowNet) est de la RECHERCHE
ouverte, prototypable mais sans point d'arrêt net. Point d'entrée : `python outils_ia/corpus/tour.py`.

## Front-ouvert #1 : signal de FÉCONDITÉ prospectif (prototype, 2026-07-02)
`conjecturer.fecondite(...)` (+ `--fecondite`) mesure la GÉNÉRATIVITÉ d'un théorème dans le DAG de
découverte = combien de découvertes en AVAL le chaînent (sur `rounds` tours). C'est le signal que MDL
(fréquence passée) et l'intérêt (parcimonie/pont) N'ONT PAS : un théorème vu UNE fois peut engendrer
un sous-arbre entier → fécond sans être fréquent.
- **Résultat** (corpus rapide) : top hubs = un MIX de (a) lemmes-pivots du corpus — `image_croissante`
  (79 usages, la monotonie de l'image qui se re-chaîne partout), `coincidence_meme_graphe` (53),
  `pr1_reciproque_produit` (44) — ET (b) surtout des DÉCOUVERTES du système devenues elles-mêmes des
  hubs (11/15 du top, la plus féconde = D1#19 à 94 usages). 11 tests verts.
- **LEÇON** : la fécondité RÉVÈLE les pivots générateurs (dont les propres découvertes du système),
  invisibles à MDL/parcimonie. Mais ce n'est encore qu'un signal A POSTERIORI (mesuré après avoir
  dépensé les tours). Le VRAI front-ouvert = APPRENDRE à le prédire A PRIORI (un modèle qui, vu un
  théorème, estime sa générativité future) → fermerait la boucle de l'invention féconde. C'est la
  frontière de recherche ; au-delà : POET/anti-collapse, définitions conservatives, GFlowNet.

## Front-ouvert #2 : PRÉDICTEUR de fécondité — RÉSULTAT NÉGATIF honnête (2026-07-02)
`fecondite_predicteur.py` teste si la fécondité (usage mesuré) est prédictible A PRIORI depuis les
features STATIQUES d'un théorème (taille, symboles applicatifs, pont). RandomForest, validation croisée,
labels = usage de `fecondite`. **Résultat sur 158 théorèmes** (25 féconds ≥3 / 133) :
- classification « fécond vs non » : accuracy **0.885 vs baseline 0.842 = +4,4 pts** (marginal) ;
- régression de l'usage : **R² = −2,5** (PIRE que prédire la moyenne) ;
- **VERDICT (négatif, informatif)** : la fécondité N'EST PAS prédictible depuis la SYNTAXE seule. Elle
  dépend du CONTEXTE GLOBAL — un théorème est fécond par sa CONNECTIVITÉ aux autres, pas par sa forme.
  Propriété RELATIONNELLE (graphe de dérivations) → la prédire exige des features de graphe, pas de syntaxe.
- **LEÇON** (« pourquoi/erreur » du but-final) : on a cru amorcer l'invention féconde par un prédicteur
  syntaxique → faux. Le vrai chemin = features de GRAPHE. Prochain cran concret (sans GNN) : features de
  CONNECTIVITÉ (nb de théorèmes partageant un symbole / unifiables) puis re-test ; si ça remonte, ça
  CONFIRME constructivement que la fécondité est relationnelle.
- **SUITE (connectivité testée)** : ajout de `deg_aval`/`deg_amont` (degrés de chaînage unifiable via
  `_match`) + `deg_symbole`. Résultat : classif 0.885→0.892 (~inchangé), **R² −2,5 → −0,8** (bond +1,7
  mais TOUJOURS <0). Les **3 features de degré DOMINENT** l'importance (deg_amont/deg_aval/deg_symbole).
  **CONCLUSION de l'arc fécondité** : la fécondité est RELATIONNELLE — *direction confirmée
  constructivement* (les degrés écrasent la syntaxe, l'erreur s'effondre). MAIS le degré LOCAL (1 saut)
  ne suffit pas à prédire la magnitude (R² encore <0) → prédiction exacte = structure PROFONDE du graphe
  (voisinage multi-sauts / GNN sur le DAG de dérivations). Le degré reste un PRIOR de tri utilisable.
  → Arc caractérisé proprement en 3 expériences (mesure → syntaxe négatif → relationnel confirmé) ;
  le cran suivant (GNN multi-sauts) est un gros chantier ML, borné par la taille du corpus.

## Documentation (2026-07-02) — rapport V9 (LaTeX)
Ajout de `rapport/fragments/annexes/frag_systeme_auto_ameliorant.tex` (annexe « Vers un système
auto-améliorant ») + `\input` dans `main.tex`. Couvre : les 2 axes + compounding, résultats mesurés
(table), l'arc fécondité (résultat négatif → relationnel), la garantie noyau. **Compile** (pdflatex,
exit 0 ; latexmk KO car perl absent) → `main.pdf` 696 Ko, section p.28 dans la TOC. Livrable mandaté fait.
→ TOUT le concret fini : système buildable complet+documenté (README + rapport + capstone), front-ouvert
caractérisé. Le prochain grand cran (GNN / corpus plus grand / promouvoir les découvertes en lemmes)
mérite l'orientation de Karl — décision stratégique, pas un tick autonome.

## STRESS-TEST sur cibles dures + exercices → AMÉLIORATION MESURÉE (2026-07-02)
Demande Karl : « tester l'IA sur des th Bourbaki durs pas faits + des exos, pour l'améliorer ». Fait :
- **Harnais d'atteignabilité** `eval_cibles.py` : held-out (retire un th, l'IA le redécouvre-t-elle ?) +
  cibles formelles. Validé : contrôle positif (une découverte) = ATTEINT prof.1 ; faits de base = NON ATTEINT.
- **Curation** (workflow 5 agents, synthèse Opus qui a EXÉCUTÉ le code) : théorèmes durs (division
  euclidienne, Hessenberg, Lemme ℕ⊂infini, base-b, Galois Prop.2, ordre Prop.1) + 6 exercices II/III + contrôles.
- **VERDICT (mesuré, décisif)** : le vrai clivage n'est PAS facile/dur ni chaînable/profond, c'est
  **IMPLICATION (¬A∨B) vs TOUT LE RESTE (=, ⇔, ∃, ∀∃)**. Le moteur ne voyait que 57 implications ; la
  MAJORITÉ du contenu (égalités de graphes, équipotences, De Morgan, associativité, TOUS les exercices) est
  invisible à `_comme_impl`. Le « positif-vedette » du scout (`composee_associative`) est NON ATTEINT (c'est
  une ÉGALITÉ). 0/57 implications re-dérivables held-out (zone verte = découvertes neuves seules).
- **AMÉLIORATION N°1 LIVRÉE** (chaînage des ÉGALITÉS) : `conjecturer.chainer_egalites` + `_comme_egal` +
  `egalites_de` + mode `--egalites`. Transitivité de `=` (T1⊢a=b, T2⊢b'=c, σ(b')=b → a=σ(c)) via la
  primitive noyau `composer_egalites`, même matching σ. **MESURÉ** : 39 égalités-corpus → **12 NOUVELLES
  égalités certifiées** (0 avant) : `(A∪B)∪C=(B∪C)∪A`, De Morgan composé `E∖(A∪B)=(E∖B)∩(E∖A)`,
  distributivités… 12/12 ponts inter-modules. 14 tests verts, frontière==22.
- **LEÇON** : le stress-test sur du dur ne « résout » pas le dur — il DÉLIMITE pourquoi c'est hors d'atteinte
  et pointe l'amélioration à fort levier / faible risque. Ici : « implications-only » → « + égalités »
  débloque des dizaines de cibles déjà formalisées, à coût-moteur. Prochains crans : chaînage des ÉQUIVALENCES
  (⇔) ; intégrer les égalités dans `iterer`/`tour` (compounding) ; ∃-intro pour existentiels ; le dur restant
  (division, Hessenberg, Zorn) exige corpus/définitions/induction, pas du chaînage.

## AMÉLIORATION 2 + RELIE : équivalences + intégration 3 régimes (2026-07-02)
Suite directe du stress-test, les deux crans suivants LIVRÉS :
- **Chaînage des ÉQUIVALENCES** (`_comme_equiv` + `equivalences_de` + `chainer_equivalences`, mode
  `--equivalences`) : détection `equiv(A,B)=et(A⇒B,B⇒A)=¬(¬(A⇒B)∨¬(B⇒A))` (vérifie que les deux
  implications sont mutuellement inverses) ; transitivité de ⇔ dérivée en 8 pas noyau
  (`equivalence_avant/arriere` ×2, chaîne A⇒B⇒C et C⇒B⇒A par assume+MP+loi_deduction,
  `conjonction_intro`). **MESURÉ** : 32 ⇔-corpus → **20 caractérisations nouvelles** certifiées
  (`x∈X ⇔ {x}∪X=X`, `x∈X ⇔ {x}∩X={x}`, inclusion⇔Leibniz, couple-dans-produit-distribué…).
- **Compounding des ÉGALITÉS** (`iterer_egalites`, briques `E<t>#k`, dédup inter-tours) : tour 1=12 →
  tour 2=19 → tour 3=**147** (toutes prof.≥2) = **178 identités**. La croissance EXPLOSE quand les
  identités se composent — le compounding le plus fort observé sur les 3 régimes.
- **RELIE** : `tour.py` section (5) ALGÈBRE — un tour complet couvre désormais les 3 régimes (⇒, =, ⇔),
  journal enrichi (`n_egalites`, `egal_prof2`, `n_equivalences`). **Tour #4 : 304 découvertes**
  (106 ⇒ + 178 = + 20 ⇔) vs 106 avant = **×2,9 par tour**. 16 tests verts, frontière ==22.
- **LEÇON** : chaque régime syntaxique du langage (⇒, =, ⇔) a SA transitivité dérivable au noyau et son
  compounding propre ; le moteur générique = (détecteur de forme, matching σ, composeur noyau, dédup α,
  tri intérêt). Restent : ∃ (existentiels, exige témoin), ∀-pur, et l'inclusion ⊂ (qui est un ∀ d'impl —
  candidat naturel au chaînage suivant : transitivité de ⊂ existe déjà dans le corpus).

## RÉGIME 4 (⊂) + PONT INTER-RÉGIMES S6 + FILTRE DE SUBSOMPTION (2026-07-02, autonomie)
- **Régime ⊂** : `_comme_inclus` (t⊂u = ¬∃z¬(z∈t⇒z∈u), retourne aussi le liant) + `_composer_inclusions`
  (transitivité en 6 pas noyau : instancier les DEUX ∀ sur le liant de la CIBLE — choisi frais par
  `formule.inclus` — chaîner MP, décharger, re-généraliser ; robuste aux liants des sources, PAS de
  wrapper sur `inclusion_transitive`) + `chainer_inclusions` (matching σ).
- **PONT =→⊂ (`egal_vers_inclusions`)** : ⊢B=C → (⊢B⊂C, ⊢C⊂B) via `N.s6(b,c,'w', z∈w)` + MP +
  equivalence_avant/arriere + generalisation. CHAQUE égalité (corpus ET découverte) nourrit le régime ⊂
  → c'est LE multiplicateur : 6 ⊂-corpus seulement, mais 434 dérivées → **20 102 inclusions nouvelles**.
- **FILTRE DE SUBSOMPTION (anti-collapse POET, jalon 5 partiel)** : la masse brute contenait des
  σ-instances de théorèmes universels connus (∅⊂X∪b = instance de `vide_inclus_partout`) — vraies mais
  sans valeur. `universels_de` + `_est_instance_connue` (un _match du patron corpus sur la découverte)
  écartent ces instances AVANT composition (économise aussi le noyau). Le top-intérêt est désormais du
  contenu réel : `a⊂b∪a`, `b∩a⊂a`, `X⊂img(Δ_X⁻¹)`, `restriction(F,X)⊂F∪b`.
- **Tour #6 (4 régimes reliés)** : **20 406 découvertes** (106 ⇒ + 178 = + 20 ⇔ + 20 102 ⊂), 18 tests
  verts, frontière ==22. Journal enrichi (`n_inclusions`, `incl_via_pont`).
- **LEÇONS** : (1) le PONT inter-régimes vaut plus que chaque régime isolé (6 ⊂-corpus → 20 102 via =) ;
  (2) l'explosion combinatoire d'un régime productif EXIGE le gate de subsomption (prédit par POET/
  anti-collapse — maintenant construit) ; (3) composer directement au noyau (6 pas) est plus robuste
  que wrapper un lemme paramétré (liants). Reste : ∃-intro ; promotion des découvertes 4-régimes en
  catalogue ; rapport V9 à mettre à jour.

## CATALOGUE ALGÉBRIQUE 4-RÉGIMES + rapport à jour (2026-07-02, autonomie)
- **`promouvoir_algebre.py`** → `outils_ia/decouvertes/lemmes_algebre.py` (+ test) : **24 lemmes nommés**
  (8 =, 8 ⇔, 8 ⊂) promus depuis les découvertes tour-1 dont les 2 sources sont corpus (ou pont S6 sur
  égalité corpus). Re-dérivation au noyau à l'appel : `_sigma` (matching σ + `_instancier`), helpers
  `_egal`/`_equiv`/`_incl` ; pour les ponts, les 2 sens d1/d2 sont ESSAYÉS et la conclusion attendue
  (repr stockée) tranche — pas de comptabilité de sens fragile. Test vert : chaque lemme se re-certifie
  (clos + cible + theorie==22). Total suite : **19 tests verts**.
- **Rapport V9** mis à jour (fragment auto-améliorant : ¶ « Quatre régimes syntaxiques, reliés » +
  table étendue) et recompilé (exit 0, 699 Ko).
- **DETTE reconnue** : `conjecturer.py` = 683 lignes (>300, multi-responsabilités : base matching +
  4 régimes + fécondité + CLI). Plan de découpage SÛR au prochain tick dédié : `conj_base.py`
  (matching/détecteurs/intérêt/subsomption) + `conj_regimes.py` (4 chaîneurs + pont + itérations) +
  `conjecturer.py` (corpus/CLI + RE-EXPORTS pour ne casser aucun importeur — tests, tour, eval_cibles,
  fecondite_predicteur, catalogues émis).

## DETTE ÉLIMINÉE — découpage du moteur (2026-07-02, autonomie)
Exécuté comme planifié : `conj_base.py` (219 l. : _match/σ, _instancier, 4 détecteurs de forme,
_cle_canon, _taille/_apps/_interet, _fmt, universels_de/_est_instance_connue) + `conj_regimes.py`
(223 l. : chaîneurs =/⇔/⊂, pont S6, pool, iterer_egalites) + `conjecturer.py` (289 l. : moteur ⇒,
iterer, fécondité, CLI, **ré-exports intégraux** — aucun importeur cassé). **Validation : 19 tests
verts** (dont les 2 catalogues émis) + smoke CLI identique (20 ⇔). Tous fichiers ≤300 lignes.
LEÇON process : consigner la dette au moment où on la crée + la traiter en tick DÉDIÉ à contexte
frais (pas en fin de tick chargé) = zéro casse.

## RÉGIME 5 (∃-intro) — les 5 RÉGIMES DU LANGAGE COUVERTS (2026-07-02, autonomie)
`conj_existe.py` (96 l.) : le stress-test classait les existentiels « hors de portée (exige témoin) » ;
le cas SOLUBLE est le sens INVERSE — le témoin est déjà là. De ⊢φ(t) clos, ABSTRAIRE un sous-terme
composite t récurrent (x frais, `_abstraire` structurel) et dériver ⊢(∃x)φ[t→x] en UN pas noyau :
`N.modus_ponens(⊢φ, N.s5(R, t, x))` — S5 recalcule (t|x)R et vérifie ==φ (capture/occurrence liée ⇒
MP échoue, jamais de faux). Anti-bruit : min_occ=2 (« le même objet joue ≥2 rôles »), dédup α,
subsomption, cap/théorème. **Résultat : 100 théorèmes ∃ certifiés**, ex. `∃x₀((A=x₀ ∨ B=x₀) ⇒
A×B=x₀)` (existence d'un absorbant), abstraction de l'encodage de Kuratowski. Intégré à `tour.py`
(section 5, journal `n_existentiels`). **20 tests verts, frontière ==22.**
**BILAN MOTEUR : les 5 régimes syntaxiques accessibles (⇒, =, ⇔, ⊂, ∃) sont couverts**, reliés
(pont S6), gardés (subsomption), avec compounding (⇒ et = itérés) — moteur générique factorisé en
3 modules ≤300 l. Ce qui reste hors moteur : ∀-intro non triviale, induction, définitions neuves =
front-ouvert/corpus. Prochain cran utile : tour complet 5-régimes de mesure + catalogue ∃.

## TOUR #7 — chiffre final du volant 5-régimes + doc à jour (2026-07-02)
**Tour #7 : 20 506 découvertes certifiées** (106 ⇒ + 178 = + 20 ⇔ + 20 102 ⊂ + 100 ∃), frontière ==22.
README (`README_SYSTEME_AUTO_AMELIORANT.md`) et rapport V9 (fragment + table, recompilé exit 0) à jour
avec les 5 régimes, le pont S6, la subsomption, le découpage 4-modules et les 2 catalogues durables.
**CAP SUIVANT (levier corpus)** : campagne DIVISION EUCLIDIENNE — recon statique faite, plan affûté
dans la mémoire [[bourbaki-chantier-division-euclidienne]] (distributivite_cardinale EXISTE ;
récurrence forte à encoder via C61 avec P'(n)=« ∀a≤n… » ; soustraction/ordre en place). Étape 1 :
module d'énoncé `iii_5_6…/ensembles_division_euclidienne.py` (vraies opérations cardinales) + cas
facile a<b → (q,r)=(0,a) ; tests lourds en background.

## CAMPAGNE DIVISION — ÉTAPE 1 ÉCRITE (2026-07-02) : le CAS PETIT
`bourbaki/entiers/iii_5_calcul_entiers/iii_5_6_divisibilite_division_euclidienne/
ensembles_division_cas_petit.py` (le dossier iii_5_6, VIDE depuis le début, reçoit sa 1ʳᵉ pièce) :
`division_cas_petit(a,b)` ⊢ **(Card a < b) ⇒ (∃q)(∃r)(b·q + r = Card a et r < b)** avec les VRAIES
opérations (`somme_cardinale_binaire(produit_cardinal_binaire(b,q), r)`). Chaîne : produit_cardinal_zero
+ congruence_terme (contexte Card(w ⊔ Card a)) + cardinal_vide_egale_vide + congruence +
somme_cardinale_zero_neutre (term-wrapper B:=Card a) + _cardinal_idempotent_t → composer_egalites ×3 ;
puis conjonction avec l'ordre, S5 (r:=Card a), S5 (q:=∅), loi_deduction → CLOS. Témoins (0, Card a).
Test miroir marqué slow, lancé en BACKGROUND (imports cardinaux 10-18 min) → log
`outils_ia/corpus/division_cas_petit_test.log`. Prochaine étape (après le vert) : cas a≥b par
récurrence encodée C61 (P'(n)=« ∀a≤n… »), puis assemblage du Th.1 complet + unicité.
- **RÉSULTAT : VERT DU PREMIER COUP, en 1,9 s** (`1 passed in 1.90s`, clos, cible exacte, 22 axiomes).
  DOUBLE LEÇON : (1) la recon exhaustive AVANT d'écrire (orientations, formes de termes, wrappers)
  paie — zéro itération de debug sur une preuve de ~40 lignes noyau ; (2) le coût « 13-18 min »
  ne vaut QUE pour les théorèmes cardinaux PROFONDS (Hessenberg…) — les briques d'arithmétique
  cardinale (lois du zéro, congruences, idempotence) sont RAPIDES à construire → la campagne
  division peut itérer de façon quasi interactive, l'économie change complètement.

## CAMPAGNE DIVISION — ÉTAPE 2a : RECOMPOSITION DU PAS (2026-07-02), VERTE EN 7,8 s
`iii_5_6…/ensembles_division_pas.py` : `division_pas_recomposition` ⊢ {est_cd b, est_cd a, b≤a,
a−b=b·q+r} ⊢ **b + (b·q+r) = a** — le maillon central du cas a≥b, en 3 pas d'égalité
(soustraction_caracterisation rôles échangés + congruence contexte b+w + symétrie/transitivité).
Test miroir : hypothèses honnêtes EXACTES vérifiées (2 formules), theorie==22. **2 tests iii_5_6
verts en 7,8 s** — la méthode recon-d'abord-puis-écrire donne le vert du 1ᵉʳ coup pour la 2ᵉ fois.
Reste du pas : réarrangement b+(b·q+r)=b·(q+1)+r (vérifier orientation distributivite_cardinale +
convention successeur d'abord), puis l'enveloppe C61 + trichotomie → Th.1 existence complet.

## Campagne « tout le livre » — non formalisés (15 juil 2026)

Issus de la passe @livre intégrale (13 agents ; 1776 notions au manifeste racine,
0 fichier sans marqueur). Chaque entrée = du TEXTE du livre SANS code hôte.
Les pages E III encore « manquantes » au manifeste racine (17, 33, 40, 42-44, 59)
sont toutes couvertes par cette liste.

- E IV.24 L.7-38 (PDF p.227) — Démonstration de CST22 (construction de F_E comme produit des X_λ, λ∈L) : preuve REPORTÉE, seul l'énoncé est formalisé (critere_CST22)
- E IV.26 L.6-11 (PDF p.229) — §3.3 Ex.IV : Extension de l'anneau d'opérateurs d'un module
- E IV.26 L.12-19 (PDF p.229) — §3.3 Ex.V : Complétion d'un espace uniforme (séparé complété)
- E IV.26 L.31-40 + E IV.27 L.1-5 (PDF p.229-230) — §3.3 Ex.VII : Groupes topologiques libres
- E IV.27 L.6-14 (PDF p.230) — §3.3 Ex.VIII : Fonctions presque périodiques sur un groupe topologique
- E IV.27 L.15-23 (PDF p.230) — §3.3 Ex.IX : Variété d'Albanese (fin du texte principal du chap. IV ; E IV.28 = Exercices)
- E III.4 L.1-3 (PDF p.107) — fin de la démonstration (commencée E III.3) que R'{X,Y} est un ordre sur E/S + « relation d'ordre associée à R{x,y} » : l'ordre quotient sur E/S n'est formalisé nulle part
- E III.4 L.4-12 (PDF p.107) — préordre sur un ensemble E comme correspondance Γ=(G,E,E) ; critère Δ⊂G et G∘G⊂G (⇒ G∘G=G) ; graphe de S = G∩G⁻¹ ; graphe de l'ordre associé = partie G' de (E/S)×(E/S) : version graphe du préordre non formalisée
- E III.4 L.13-16 (PDF p.107) — Exemple (petit texte) : divisibilité à droite dans un anneau à élément unité = relation de préordre — prose hors théorie des ensembles (renvoie à A, I §8), rien à formaliser ici
- E III.5 L.7-9 (PDF p.108) — C58 : x≤y équivalente à « x<y ou x=y » ; « x≤y et y<z », « x<y et y≤z » entraînent x<z — critère cité par plusieurs docstrings (_strict, ordre strict graphe) mais jamais démontré comme théorème/Meta
- E III.5 L.10-15 (PDF p.108) — démonstration de C58 (via critère C24, transitivité) — suit le sort de C58
- E II.48 L.3-6 (§6.9) : « f = (t ↦ A{t}) est une bijection de Θ sur l'ensemble quotient F/R » (cas R relation d'équivalence dans F) — énoncé non formalisé ; la page est comptabilisée par un marqueur Rem sur ensemble_classes_objets (ensembles_quotient_complements.py)
- E II.2 L.32 (§1.2) : vocabulaire « x est la partie pleine de x » — non formalisé (une ligne de prose dans la zone Prop.1, dont le marqueur existant L.30-30 est dans i_2_theoremes/tactiques/tactiques_abrege.py)
- §7.4 Prop.5 (E III.58 L.1-4, démo L.5-14) : f_α : E→E_α surjective si I filtrant à partie cofinale dénombrable et f_αβ surjectives — seule l'HYPOTHÈSE est calée (est_systeme_projectif_filtrant, ensembles_cofinal.py) ; conclusion + démo (récurrence β_n, réduction à I=N) non formalisées
- §7.4 prose (E III.58 L.15-25) : conditions (i)/(ii)/(ii') sur les ensembles S_α de parties de E_α (second critère de non-vacuité) — notion sans fichier hôte
- §7.4 Th.1 (E III.58 L.26-33) : (i)-(iv) ⇒ a) f_α(E)=∩_{β≥α} f_αβ(E_β) (19) et b) E≠∅ — non formalisé (déjà listé REPORTES)
- §7.4 Demo Th.1 (E III.58 L.34-36 ; E III.59 L.1-37 page entière ; E III.60 L.1-7) : ensemble Σ des familles (20)-(21), parties 1°-4° (inductif, maximal, A_α={x_α}, a) puis b)) via III p.21 cor.1 — non formalisée
- §7.4 Rem.1 (E III.60 L.8-17) : condition affaiblie (iii') et validité de b) — non formalisée
- §7.4 Exemples I-II (E III.60 L.18-32) : E_α finis/compacts (TG I §9) ; A-modules artiniens, espaces affines, variétés linéaires affines — prose non formalisable ici
- §7.5 Lem.1 (E III.62 L.8-14, démo L.15-20) : relèvement fini dans lim→ ((i) tout système fini vient d'un E_α ; (ii) égalisation par un β≥α) — non formalisé (REPORTES)
- §7.6 Prop.6 (E III.62 L.21-32, démo L.33-39 + fin E III.63 L.1-4) : propriété universelle de lim→ ((23) u_β∘f_βα=u_α ⇒ ∃!u vérifiant (24) ; critères 2° surjectif / 3° injectif) — non formalisée (seuls les Cor.1/2 pointwise le sont)
- §7.6 Demo du corollaire de la Prop.7 (E III.65 L.9-21) : preuves des identités (26) lim→ u_α(M_α)=u(lim→ M_α) et (27) lim→ u_α^{-1}(a'_α)=u^{-1}(a') — non formalisées (l'énoncé L.1-8 est calé sur systeme_image_directe)
- E III.39 L.10-19 §5.6 Th.1 division euclidienne — énoncé général + démo NON formalisés (seuls cas partiels marqués : b=2 dans parite, cas a<b, recomposition du pas, identité b(q+1)=b+bq)
- E III.39 L.20-23 §5.6 Def.1 — reste, multiple de b, divisible par b, diviseur, quotient a/b
- E III.39 L.24-26 §5.6 — prose : partie entière du quotient (cf. TG IV §8) + convention d'écriture a/b
- E III.39 L.27-31 §5.6 — prose : stabilité des multiples (a'/b=(a'/a)(a/b) ; (c±d)/b = c/b ± d/b)
- E III.40 L.1-21 §5.7 Prop.8 + démo — E_k lexicographique ≅ intervalle (0, b^k−1) (dossier iii_5_7 vide)
- E III.40 L.22-29 §5.7 — a<b^a, existence/unicité et définition du développement de base b
- E III.40 L.30-39 et E III.41 L.1-21 §5.7 — petit texte : chiffres, symbole numérique, systèmes dyadique/décimal (prose, rien à formaliser ; aucun fichier hôte)
- E III.41 L.33-42 + E III.42 L.1-4 §5.8 Prop.10 — n!/(n−m)! = nombre d'applications injectives
- E III.42 L.5-7 §5.8 Cor. — nombre de permutations d'un ensemble fini = n!
- E III.42 L.8-21 §5.8 Prop.11 — recouvrements disjoints à cardinaux prescrits : n!/∏ p_i!
- E III.42 L.22-24 §5.8 Cor.1 — nombre de parties à p éléments = n!/(p!(n−p)!)
- E III.42 L.25-28 §5.8 — définition du coefficient binomial (n p) + symétrie (n p)=(n n−p) (prose/notation)
- E III.43 L.1-6 §5.8 — petit texte : bijection X↦E−X ; convention (n p)=0 si p>n
- E III.43 L.7-13 §5.8 Cor.2 — nombre d'applications strictement croissantes E→F = (n p)
- E III.43 L.14-16 §5.8 Prop.12 — Σ_p (n p) = 2^n
- E III.43 L.17-25 §5.8 Prop.13 — formule de Pascal (n+1 p+1)=(n p+1)+(n p)
- E III.43 L.26-27 §5.8 — petit texte : preuve calculatoire de la prop.13 (prose, rien à formaliser)
- E III.43 L.28-30 + E III.44 L.1-5 §5.8 Prop.14 — nombre de couples 1≤i≤j≤n (resp. i<j) = n(n+1)/2 (resp. n(n−1)/2)
- E III.44 L.6-10 §5.8 Cor. — Σ_{i=1..n} i = n(n+1)/2
- E III.44 L.11-26 §5.8 Prop.15 — nombre d'applications u:E→(0,n) avec Σu(x)≤n (resp. =n) : (n+h h) / (n+h−1 h−1)
- E III.44 L.27-30 §5.8 — petit texte : monômes de degré total ≤ n (prose, rien à formaliser)
- CS6 — (T|x)(A et B) identique à « (T|x)A et (T|x)B » | E I.29 L.14-16 (aucun cs6 dans i_1_2_criteres_CS.py)
- CS7 — (T|x)(A ⇔ B) identique à (T|x)A ⇔ (T|x)B | E I.30 L.38-40 (aucun cs7)
- C45 sens RÉCIPROQUE (R ⇒ (x=T) théorème ⟹ R univoque) | E I.41 L.14-19 (marqueur Demo posé avec note « non formalisé » sur c45_avant)
- Def « relation fonctionnelle en x dans 𝒯 » (∃x)R et au plus un x | E I.41 L.20-23
- C46 — R fonctionnelle ⇔ (x = τx(R)) | E I.41 L.24-36
- Rem « symbole fonctionnel Σ » (prose) | E I.41 L.37-40 + E I.42 L.1-4
- C47 — S{τx(R)} équivalente à (∃x)(R{x} et S{x}) | E I.42 L.5-13
- Introduction du chapitre I (prose pure, pas de fichier hôte) | E I.7-13
- E.R.21 item 12b — (47) ∏Xι = ⋂_ι pr_ι⁻¹(Xι), version famille (PDF p.324, bas de page ; l'analogue binaire (24) est clos, cf. E.R.12 item 3e)
- E.R.21 item 12c — (48) pr_κ(∏Xι) = X_κ si ∏_{ι≠κ}Xι ≠ ∅, version famille (PDF p.324, dernières lignes ; analogue binaire (25) clos, cf. E.R.12 item 3f)
- E.R.22 item 12e — bijection ∏Yι ≅ ∏_{ι∈J2}Xι (Yι={aι} sur J1, partition (J1,J2) de I) par projection (PDF p.325, L.4-11)
- E.R.22 item 13 — bijection canonique (∏Aι)^E ≅ ∏(Aι^E) (PDF p.325, milieu de page)
- E.R.22 item 15 (forme générale) — recollement d'une FAMILLE (fι) coïncidant sur les Aι∩Aκ, et bijection F^A ≅ ∏F^{Aι} (PDF p.325, bas ; seul le cas binaire à domaines disjoints est clos : reunion_graphes_fonctionnelle)
- E.R.22-23 §5 item 1 (a,b) — la relation « il existe ι tel que x∈Aι et y∈Aι » associée à une partition, sa réflexivité et sa symétrie (PDF p.325 bas - p.326 haut ; la caractérisation par le graphe C est close, cf. Prop.1 II.6.1)
- E.R.23 item 2 (fin) — l'égalité x=y est une relation d'équivalence, application canonique x↦{x} bijective (PDF p.326, milieu)
- E.R.23 item 3 (début) — relation pr₁(z)=pr₁(z') dans E×F : correspondance biunivoque (E×F)/R ≅ E (PDF p.326, L. sous « 3. »)
- E.R.24 item 5 (fin) — correspondance biunivoque canonique f(A) ≅ A/R_A, z↦f(φ(g⁻¹(z))) (PDF p.327, haut)
- E.R.25 item 9 (fin) — correspondance biunivoque (E/R)/(T/R) ≅ E/T (PDF p.328, milieu)
- E.R.25 item 10 (fin) — bijection canonique (E/R)×(F/S) ≅ (E×F)/(R×S), (u,v)↦u×v (PDF p.328, bas)
- E.R.26 item 2 (fin) — « l'ensemble N des entiers positifs est ordonné par x≤y » (PDF p.329 ; l'ordre ≤ cardinal est clos en III.3.2 mais pas l'énoncé restreint à N)
- E.R.26 item 3 — équivalences de notation strict/large : « x≤y ⟺ (x<y ou x=y) », « x≤y et y<z ⇒ x<z » (PDF p.329, bas)
- E.R.27 item 4 (début) — trichotomie exclusive (x<y, x=y, x>y s'excluant mutuellement) ; la partie vide est totalement ordonnée (PDF p.330, haut)
- E.R.27 item 5 (milieu) — N bien ordonné ; une partie de N a un plus grand élément ssi elle est finie non vide (PDF p.330)
- E.R.27 item 5 (fin) — dans P(E) : 𝔉 possède un plus petit (resp. plus grand) élément ssi ⋂𝔉 ∈ 𝔉 (resp. ⋃𝔉 ∈ 𝔉) (PDF p.330, bas)
- E.R.30 item 13 — identification E' ≅ lim→ E'α quand les fβα sont injectives (réunion croissante de parties) (PDF p.333, L.12-18)
- E.R.30 item 13 (fin) — produit de deux limites inductives : bijection canonique D = lim→(Aα×Bα) ≅ A×B (PDF p.333, bas)
- E.R.30 item 13 — critères complets d'injectivité/surjectivité de g = lim→ gα (PDF p.333, milieu ; couverts seulement en partie par passage_limite_ind)
- E.R.31 item 14 (Remarque petit texte) — « E peut être vide même si les Eα sont non vides et les fαβ surjectives » (PDF p.334 ; remarque-contre-exemple, non formalisée)
- E.R.31 item 14 (milieu) — critère d'injectivité de g : E' → lim← Eα (∀x'≠y' ∃α gα(x')≠gα(y')) (PDF p.334 ; l'existence/unicité de g sont closes via cone_existence/cone_unicite)
- E.R.7 item 3 — application canonique de A dans E (injection canonique x↦x de A⊂E dans E) | PDF p.310
- E.R.7 item 4 — partie X stable par f (f(X)⊂X) et stable par un ensemble d'applications | PDF p.310
- E.R.8 item 5b — équivalence « X≠∅ » ⇔ « f(X)≠∅ » | PDF p.311
- E.R.8 item 7 fin — « f application de E sur F » ⇔ « X≠∅ ⇒ f⁻¹(X)≠∅ » | PDF p.311
- E.R.10 item 10d — équivalence « f⁻¹(f(X))=X et f(f⁻¹(Y))=Y qqs X,Y » ⇔ « f bijective » (les deux moitiés sous hypothèse inj/surj sont FAITES et déjà marquées E.R.9) | PDF p.313
- E.R.10 item 11 — itérées fⁿ (récurrence f¹=f, fⁿ=fⁿ⁻¹∘f, f^{m+n}=f^m∘f^n) | PDF p.313
- E.R.10-11 item 12 — réciproque : si g∘f est une permutation de E et f∘g une permutation de F, alors f et g sont bijectives | PDF p.313-314
- E.R.11 item 14 — représentation paramétrique : seule la surjection sous-jacente est formalisée (marquée sur est_surjective), pas le vocabulaire ensemble des paramètres | PDF p.314
- E.R.13 item 4 — l'application diagonale x↦(x,x) est une bijection de E sur Δ (le graphe Δ et sa symétrie Δ⁻¹=Δ sont FAITS) | PDF p.316
- E.R.13 item 5 — correspondance biunivoque entre parties fonctionnelles de 𝔓(E×F) et ensemble des applications d'une partie de E dans F | PDF p.316
- E.R.14 item 7 — correspondance biunivoque 𝔓(E×F) ↔ applications de E dans 𝔓(F) (la coupe elle-même est FAITE) | PDF p.317
- E.R.14 item 8 fin — « K⊂K' » ⇔ « K(x)⊂K'(x) quel que soit x∈E » | PDF p.317
- E.R.16 item 13 — fonctions de trois arguments et plus (seul le cas de deux arguments est formalisé, marqué avec note) | PDF p.319
- E.R.16 item 14 — préservation de l'injectivité/surjectivité/bijectivité par f×g×h | PDF p.319
- E.R.18 item 3 — (36) ⋃_{ι∈J₁∪J₂}X_ι = (⋃_{J₁})∪(⋃_{J₂}) (cas particulier binaire de (35)) | PDF p.321
- E.R.18 item 3 — (38) (⋃X_ι)×(⋃Y_κ)=⋃_{(ι,κ)}(X_ι×Y_κ) au niveau famille (cas binaire (22) FAIT) | PDF p.321
- E.R.19 item 6 — (40) ⋂ sur J=∅ vaut E (la déf. formalisée de ⋂ exige I≠∅) | PDF p.322
- E.R.19 item 7 — règle de dualité (métathéorème, candidat type Meta en prose ; aucun fichier hôte) | PDF p.322
- E.R.19 item 8 — (43) (⋂X_ι)×(⋂Y_κ)=⋂_{(ι,κ)}(X_ι×Y_κ) au niveau famille (cas binaire (23) FAIT) | PDF p.322
- E.R.20 item 8 — (44) (⋂X_ι)×(⋂Y_ι)=⋂_ι(X_ι×Y_ι) (même ensemble d'indices) au niveau famille | PDF p.323
- E.R.20 item 9 — ∏ sur la famille vide = ensemble à un élément ; ∏X_ι=E^J si X_ι=E qq soit ι | PDF p.323
- E.R.20 item 10 — équivalence « (∀x)(∃y)R{x,y} » ⇔ « il existe une application f de E dans F telle que (∀x)R{x,f(x)} » (principe de choix fonctionnel ; seul le choix-τ ponctuel Prop.6 §II.5.4 est FAIT) | PDF p.323
- E III.30 L.29-33 — COROLLAIRE (du Th.2 Cantor) : « Il n'existe pas d'ensemble dont tout cardinal soit élément » — aucun hôte trouvé dans tout le dépôt (grep) ; seul le voisin aucun_plus_grand_cardinal (∀X∃Y X<Y) existe, marqué sur Th.2 L.22 et non sur ce corollaire
- E III.33 L.1-15 (PDF p.136) : Remarque §4.3, variante 1 du principe de récurrence — récurrence « forte » (S{n} = (∀p)(p entier et p<n ⇒ R{p}), déduite de C61)
- E III.33 L.16-26 (PDF p.136) : Remarque §4.3, variante 2 — « récurrence à partir de k »
- E III.33 L.27-33 (PDF p.136) : Remarque §4.3, variante 3 — « récurrence limitée à un intervalle »
- E III.33 L.34-36 + E III.34 L.1-7 (PDF p.136-137) : Remarque §4.3, variante 4 — « récurrence descendante »
- Def.3 forme FAMILLE (produit/somme cardinale d'une famille (a_i)_{i in I}) — E III.25 L.32-34 — seul le cas binaire est formalisé et marqué
- Prop.4 (le cardinal du produit/de la somme d'une famille d'ensembles est le produit/la somme cardinale) — E III.26 L.3-5, démo L.6-8
- Corollaire de Prop.4 (Card(reunion E_i) <= somme des Card(E_i)) — E III.26 L.9-10, démo L.11-12
- Prop.5 a) b) c) (invariance par bijection d'indices, associativité, distributivité — forme famille) — E III.26 L.13-23, démo L.24-32 et E III.27 L.1-2 (les cas binaires sont formalisés : produit_commute/somme_commute/somme_associe/distributivite)
- Prop.6 (somme/produit inchangés en retirant les a_i=0 resp. a_i=1 — forme famille) — E III.27 L.15-18, démo L.19-23 (cas binaire = Cor.1 L.24, formalisé)
- Cor.2 de §3.4 (ab = somme de b copies de a ; b = somme de b copies de 1) — E III.27 L.25-27, démo L.28-30
- Prop.10 (a^b = produit d'une famille constante indexée par I, Card I = b) — E III.28 L.25-26, démo L.27-28 (le Cor.1 et le Cor.3 sont clos dans le projet SANS passer par Prop.10 : bijections explicites + Cantor-Bernstein)
- Prop.14 forme FAMILLE (somme/produit monotones sur un ensemble d'indices quelconque) — E III.30 L.4-6 (cas binaire formalisé et marqué Prop.14)
- Cor.1 de §3.6 (somme/produit sur une sous-famille J de I) — E III.30 L.12-13, démo L.14-15
- Remarque en petit texte après Prop.13 (pas de « différence » a-b en général) — E III.30 L.1-3 (prose ; hôte naturel = props_restantes, hors périmètre)
- Lemme 1 (tout ensemble infini contient un ensemble équipotent à N) — énoncé E III.47 L.33, démo E III.47 L.34-36 + E III.48 L.1-2
- Cor.1 du Th.2 (a^n = a pour a infini, n≥1) — E III.49 L.5-6
- Cor.2 du Th.2 (produit d'une famille finie de cardinaux non nuls dont le plus grand est infini) — E III.49 L.7-11
- Cor.3 du Th.2 (somme d'une famille de cardinaux ≤a indexée par un ensemble de cardinal ≤a) — E III.49 L.12-16
- Cor.4 du Th.2 (ab = a+b = sup(a,b)) — E III.49 L.17-19
- Prop.1 §6.4, 2e et 3e assertions (produit fini / réunion d'une suite de dénombrables) — E III.49 L.23-27 (1ère assertion seule formalisée, PARTIEL, hôte ensembles_infinis_props.py)
- Prop.2 §6.4 (tout ensemble infini dénombrable est équipotent à N) — E III.49 L.30-32
- Prop.3 §6.4 (partition d'un infini en dénombrables infinis) — E III.50 L.1-3
- Prop.4 §6.4 (fibres dénombrables sur un infini ⇒ équipotence) — E III.50 L.4-8
- Prop.5 §6.4 (l'ensemble F(E) des parties finies d'un infini E est équipotent à E) — E III.50 L.9-17
- Corollaire de la Prop.5 (l'ensemble S des suites finies d'éléments de E est équipotent à E) — E III.50 L.18-23
- Prop.6 §6.5 (élément maximal ⇔ suites croissantes stationnaires) — E III.51 L.1-12
- Cor.1 de la Prop.6 (bien ordonné ⇔ suites décroissantes stationnaires) — E III.51 L.13-17
- Cor.2 de la Prop.6 (suite croissante d'un ensemble ordonné fini est stationnaire) — E III.51 L.18-21
- Prop.7 §6.5 (principe de récurrence nœthérienne) — E III.51 L.24-28
- Cor. de Prop.4 (Card ∪E_ι ≤ Σ Card E_ι) — E III.26 L.9-10, démo L.11-12 — hôte HORS périmètre (iii_3_equipotence_cardinaux/props_restantes/ensembles_prop3_prop4cor_iii3.py, marqué là-bas L.13-16 avec un comptage divergent)
- Def.3 / Prop.4 / Prop.5 formes FAMILLE générales (∏/Σ sur un ensemble d'indices I quelconque) — E III.25 L.32-34, E III.26 L.3-32 — seules les formes BINAIRES sont formalisées (dossiers iii_3_6_familles/ et iii_3_7_inegalites/ vides)
- Prop.6 forme famille (termes 0/1 dans somme/produit) — E III.27 L.15-18, démo L.19-23 — seuls les cas binaires du Cor.1 (a+0=a·1=a) sont couverts
- Cor.2 de la Prop.6 (ab = Σ de b copies de a, b = Σ de b copies de 1) — E III.27 L.25-27, démo L.28-30 — aucun hôte trouvé (grep)
- Prop.7 (∏a_ι ≠ 0 ⟺ ∀ι a_ι ≠ 0) — E III.28 L.1-2, démo L.3-4 — hôte HORS périmètre (props_restantes_prop7.py)
- Prop.10 forme famille (a^b = ∏_{ι∈I} a, Card I = b) — E III.28 L.25-26, démo L.27-28 — pas de produit-famille dans le projet ; ses conséquences binaires (Cor.1 via prop9_exp_somme/, Cor.2, Cor.3 currying) sont couvertes
- Prop.13 (a ≥ b ⟺ ∃c a = b+c) — E III.29 L.29-30, démo L.31-33 — hôte HORS périmètre (props_restantes, sens direct conditionnel)
- Cor.1 de la Prop.14 (sommes/produits partiels sur J ⊂ I) — E III.30 L.12-13, démo L.14-15 — aucun hôte dans le périmètre (forme famille)
- Cor. du Th.2 (il n'existe pas d'ensemble dont tout cardinal soit élément) — E III.30 L.27, démo L.28-31 — hôte HORS périmètre (definitions_cardinaux/ensembles_cardinaux_consequences.py)
- E III.16 L.34-39 — Prop.3 (énoncé) : famille d'ensembles bien ordonnés deux à deux segments l'un de l'autre ⇒ ordre unique sur la réunion, bien ordonné
- E III.17 L.1 et L.19-32 — Démonstration de la Prop.3 (via le lemme 1) : aucun fichier hôte
- E III.17 L.2-7 — Lemme 1 (ordre unique sur la réunion d'une famille FILTRANTE d'ensembles ordonnés) + Demo L.8-18 : aucun fichier hôte (grep 'filtrante' ne touche que III.4/III.7)
- E III.17 L.34-36 — Lemme 2 (ensemble de segments clos par réunion et par S_x∪{x} contient tout segment) + Demo L.37-38 et E III.18 L.1-4 : non formalisé en tant que tel ; le dépôt prouve C59 par plus-petit-contre-exemple
- E III.20 L.35-36 — Prop.4 (énoncé propre) + Demo L.37-41/E III.21 L.1-10 : seul Th.2 est clos (via Bourbaki–Witt) ; les lignes de la démo du livre sont recensées sur zorn_theoreme avec note d'écart de route
- E III.21 L.11-12 — Cor.1 de Th.2 (élément maximal m ≥ a) + Demo L.13-14 : cité verbatim dans la docstring d'ensembles_zorn mais pas de théorème
- E III.21 L.15-17 — Cor.2 de Th.2 (famille de parties close par réunion/intersection de chaînes ⇒ élément maximal/minimal)
- E III.22 L.18-24 — Cor.2 du Lemme 4 (isos croisés ⇒ S=E, T=F, f et g réciproques) : pas de host direct
- E III.22 L.25-30 — Cor.3 (tout sous-ensemble A d'un bon ordre E est isomorphe à un segment de E) : pas de host dans iii_2
- E III.46 L.14-20 §6.2 Crit.C62, DERNIERE phrase (« L'ensemble U et l'application f sont alors determines de facon unique par cette condition ») — **unicite NIVEAU LIVRE**, c.-a-d. (∀g)( func ∧ graphe ∧ dom=ℕ ∧ g(z)=T{g|seg z} ) ⇒ g=f : **NON formalisee et NON assemblable** en l'etat. Le (∃!f) clos le 26 juil. (`existence_unicite_fonction_c62`, iii_6_2_recursion_c62/ensembles_c62_fonction_unicite.py) l'est au niveau VALEUR-REGLE f(z)=T(z), ou l'unicite est facile parce que g(x)=T(x)=f(x) ne depend pas de la fonction. Au niveau livre l'argument de T DIFFERE entre les deux candidats (T{g|seg x} vs T{f|seg x}) : `graphe_egal_par_valeurs` ne s'applique plus. Route attendue = RECURRENCE TRANSFINIE sur la coincidence g|seg x = f|seg x (vrai travail). Asymetrie a retenir : cote EXISTENCE la forme du livre EXISTE deja (`equation_restriction_fonction`, 4 hyps dont essais_restriction), cote UNICITE non.
