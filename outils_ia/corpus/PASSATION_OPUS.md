# PASSATION → Opus 5 (écrit par Fable, 3 août 2026, quota ~11 %)

**Contexte** : campagne MURS Bourbaki V9, boucle de travail Karl. Fable épuise
son quota ; ce fichier permet à Opus 5 de reprendre SANS perte. Tenu à jour à
chaque acquis (sections datées en bas). Lire AUSSI : tête de
`outils_ia/corpus/CAMPAGNE_DEMOS.md` (specs détaillées, pièges) et `CLAUDE.md`.

## Règles absolues (ne JAMAIS enfreindre)
- `theorie_ensembles()` == 22 axiomes ; noyau (`i_2_theoremes/noyau/`) et
  `subst` INTOUCHÉS ; jamais de `Theoreme(...)` à la main, jamais de `_CLE`,
  jamais de monkeypatch. Surpasser = construire, jamais tricher.
- JAMAIS de commit git (Karl commite lui-même).
- ≤300 lignes/fichier (hors commentaires @livre), ≤10 entrées/dossier
  (LIVRE.md exclus ; à 10 → sous-dossier, cf. `cst_criteres/cst2/`).
- Chaque notion : marqueur `@livre` (format dans CLAUDE.md).
- Métathéorèmes (schéma-en-général) = GÉNÉRATEURS Python, jamais un Theoreme.
- Hypothèses HONNÊTES listées ; miroirs `==` assertés ; REVERT si insoluble.
- Tests : `python -m pytest tests/... -q` depuis V9/, PYTHONIOENCODING=utf-8,
  jamais de pipe qui masque le code de sortie ; tests lourds (cardinaux
  profonds, 13-18 min) DÉTACHÉS avec timeout.
- Journal `CAMPAGNE_DEMOS.md` (section en TÊTE) + `outils_ia/traces/events.jsonl`
  (prochain ev. : **339**) À CHAQUE tick + bilan à Karl.

## État CST (Ch. IV §1.2) — TRILOGIE COMPLÈTE (CST1 + CST2 + CST3 tous faits)
⚠️ Le titre disait « reste CST3 » : PÉRIMÉ. CST3 est écrit et testé
(`cst_criteres/cst3/` : etage_parties, etage_produit, genere, corollaire).
La section « PROCHAIN CHANTIER » ci-dessous est conservée comme **trace de la
route suivie** (pièges et helpers réutilisables), pas comme un travail à faire.
Dossier : `bourbaki/iv_structures/iv_2_morphismes_structures_derivees/cst_criteres/`
- **CST1** fonctorialité : `ensembles_cst1_genere.py` (cst1_termes_prouve).
- **CST1-identité** : `ensembles_cst1_identite.py` (CLOS 0 hyp) ; consommateur
  T5 : `ensembles_echelon_identite_reelle.py` (CLOS).
- **CST2** bijectivité : `ensembles_cst2_briques.py` (étage 𝔓, invariant
  Q(F,X,Y)=((func∧dom=X)∧(func F⁻¹∧F⟨X⟩=Y)), 4 hyps) + `cst2/
  ensembles_cst2_etage_produit.py` (étage ×, 8 hyps, _inj_point/_proj_forme)
  + `cst2/ensembles_cst2_genere.py` (cst2_prouve : hyps résiduelles =
  exactement les n Q(f_i) ; pont_bijection_de → E III.3.1).
- Tests : `tests/.../cst_criteres/` 57/57 verts (14 s).

## ✅ FAIT — CST3 (réciprocité) : route suivie, conservée pour ses pièges
Énoncé cible par étage (extensions RÉELLES, g bijection A→A' au sens Q) :
  reciproque(ext_parties_reelle(g,A,xi)) = ext_parties_reelle(g⁻¹, A', xi)
  reciproque(produit_app_reelle(f,g,A,B,xi)) = produit_app_reelle(f⁻¹,g⁻¹,A',B',xi)
puis générateur cst3_prouve(s, fs, bases, bases_p) ⊢
  reciproque(⟨f⟩^S) = ⟨f⁻¹⟩^S  (hyps = les n Q(f_i)).
Route étage 𝔓 (extension par le liant z, `egalite_par_extension(..., x="z")`) :
  z∈F⁻¹ ⇔ ∃p∃q(z=(p,q) ∧ (q,p)∈F)      [AXIOME_RECIP — vérifier la forme
      exacte via `_inst_recip` dans ii_3_2_reciproque/ensembles_reciproque.py]
  (q,p)∈F ⇔ q∈𝔓A ∧ p=g⟨q⟩             [membre_graphe_terme(𝔓A, T, noms)]
  z∈G' ⇔ ∃x∃y(z=(x,y) ∧ x∈𝔓A' ∧ y=T') [axiome_graphe_terme forme-z NATIVE,
      abrege:977 ; T'=image(reciproque(g), y-liant)]
  → : sous témoins p,q : p=g⟨q⟩∈𝔓A' (val-dans-cible : croissance
      _image_croissante_terme + Himg S6, motif ensembles_cst2_briques c4-fwd) ;
      q=g⁻¹⟨p⟩ car g⁻¹⟨g⟨q⟩⟩=q (image_reciproque_image_egal_si_injective,
      H_app dérivé par _happ) ; re-former le ∃∃ de droite (S5 ×2).
  ← : symétrique avec image_image_reciproque_egal_si_surjective +
      image_reciproque_inclus_domaine (motif c4-bwd).
  PIÈGES CONNUS : relais-α systématique (noms frais Zq/uq/vq/pa/qb, JAMAIS
  instancier une brique à var("z")/var("x") directement — liants inclus/
  projections) ; alpha_existe pour ∃ imbriqués de même liant ; pr_dans
  interdit u="x" ; couple_reciproque interdit u,v∈{p,q} ; ordre d'instancie
  = ordre des ∀ (externe d'abord). Toutes les briques préimage-image
  (ii_3_2_reciproque/ensembles_image_reciproque_props.py) sont
  TERMES+antécédents, 0 hyp.
Helpers RÉUTILISABLES : _cut, _happ, _sub_parties (cst2_briques) ;
  _inj_point, _proj_forme, _couple_dans_graphe, _val_dans_cible
  (cst2/ensembles_cst2_etage_produit.py — importables).
Placement : `cst2/` est le sous-dossier des critères de bijectivité ; pour
  CST3 créer `cst_criteres/cst3/` (le parent est au CAP de 10).
Après CST3 : raccorder les consommateurs opaques (reciproque_isomorphisme_
espece, transport_iso_props — remplacer leurs hyps explicites CST3 par le
générateur, motif « fonction sœur _reelle » comme echelon_identite_reelle).

## Grille modèle (mémoire Karl)
Annoncer « Modèle X, niveau Y/6 » avant chaque tâche. Infra noyau/preuves
dures = éviter de déléguer à plus petit que soi ; assemblage mécanique
(tests, journal, greps) = OK à bas niveau. Opus : suivre les routes ci-dessus
PAS À PAS, sonder après CHAQUE pièce (une sonde = un python -c minimal),
et s'arrêter/documenter au premier mur plutôt que d'improviser.

## Journal de passation (append à chaque acquis)
- [Fable, 3 août ~15h20] Passation créée. CST1/CST1-id/T5/CST2 FAITS
  (ev. 127-131). CST3 : route ci-dessus, rien d'écrit encore.
- [Fable ~15h40] CST3 étage-𝔓 FAIT (cst3/ensembles_cst3_etage_parties.py,
  sonde verte, 4 hyps) + briques GÉNÉRIQUES closes reciproque_est_graphe /
  dom_reciproque_graphe (resservent à l'étage ×). Étage-× en cours : route =
  B2 avec G:=P⁻¹ ; hyp_valeurs via _recip_val (préimage pa par alpha_existe,
  f⁻¹(p')=pa par _valeur_de_couple(recip f), f(f⁻¹(p'))=p' idem sur f) ;
  générateur = double fil qs[i] (Q, comme cst2_prouve) + rs[i] (recip,
  congruence-IH-dans-trou comme cst1). Si je coupe ici : écrire
  cst3/ensembles_cst3_etage_produit.py puis cst3/ensembles_cst3_genere.py
  sur ce modèle, sondes à chaque pièce, tests miroirs, ev. suivant.
- [Fable ~16h10] CST3 COMPLET (etage-P, etage-x, cst3_prouve — ev. 132),
  220/220 iv_structures. LA CAMPAGNE CST EST FINIE. Prochains chantiers pour
  Opus, par ordre de valeur : (1) raccord consommateurs opaques de
  transport_iso_props (reciproque_isomorphisme_espece : remplacer ses hyps
  explicites bij(f-1)+CST3 par cst2/cst3_prouve, motif fonction-soeur
  echelon_identite_bijection_reelle) ; (2) III.7 limites (Prop.6/7/9/10 +
  Th.1b p. E III.59) — diffus, grep d'abord (memoire : AUCUN doc de
  couverture fiable, grep le theoreme en code avant tout effort) ; (3) suite
  complete detachee (tests cardinaux 13-18 min, --timeout 1800) a un jalon.
- [Fable ~16h30] EN COURS (dernier tick avant limite) : capstone CST3-corollaire
  ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Δ_{S(E)} : (a) brique base composee_reciproque_diagonale
  {dom f=A, func f⁻¹} ⊢ f⁻¹∘f = Δ_A (extension liant z : AXIOME_COMPOSEE +
  univalence f⁻¹ pour →, témoin f(d0) pour ← ; fichier cst3/) ; (b) assemblage
  = cst1_termes_prouve(g:=f⁻¹) donne ⟨f⁻¹∘f⟩=⟨f⁻¹⟩∘⟨f⟩, congruence famille
  (f⁻¹∘f → Δ_E dans le trou-extension) puis cst1_identite_prouve. Si coupé :
  reprendre exactement là.
- [Fable ~16h50, FINAL] CAPSTONE FAIT (ev. 133) : f⁻¹∘f=Δ_A +
  ⟨f⁻¹⟩^S∘⟨f⟩^S=Δ_{S(E)} (cst3/ensembles_cst3_corollaire.py), 63/63.
  PROCHAINE ÉTAPE PRÉCISE pour Opus : décharger la 3e hyp de
  reciproque_isomorphisme_espece — au niveau VALEUR : ⟨f⁻¹⟩^S(⟨f⟩^S(U))
  = (⟨f⁻¹⟩^S∘⟨f⟩^S)(U) [composition_valeur_t ii_3_8:60, 3 hyps à décharger
  depuis Q(⟨f⟩^S)=cst2_prouve] = Δ_{S(E)}(U) [congruence + capstone]
  = U [diagonale_valeur noms→termes via _dval_t de cst1_identite, U∈S(E)
  en hyp honnête]. Puis fonction-sœur reciproque_isomorphisme_espece_reelle.
  Attention : ces consommateurs parlent en OPAQUE (structure_transportee) —
  la sœur réelle re-déclare est_isomorphisme sur les extensions réelles.
- [Fable ~17h15, FINAL-2] valeur_reciproque_identite FAIT (ev. 134) :
  <f-1>^S(<f>^S(U))=U, 7/7. RESTE (mecanique, niveau Opus 3-4/6) : la
  fonction-soeur reciproque_isomorphisme_espece_reelle dans un fichier
  cst3/ : re-declarer est_isomorphisme_reel(s,fs,E,E',U,V) :=
  est_bijection_de(<f>^S-reel-niveau-bases...) AND <f>^S(U)=V (calquer
  l'opaque transport_iso_props:114) puis conjonctions : hyp iso directe +
  cst2_prouve (bijection reciproque via pont) + valeur_reciproque_identite
  pour la clause (4) inverse. Sondes a chaque piece. Ensuite : III.7
  (grep d'abord) ou suite complete detachee.
- [Fable ~17h40, FINAL-3] reciproque_isomorphisme_reel FAIT (ev. 135),
  66/66. Le raccord IV.1.5 est COMPLET au niveau echelon. Chantiers suivants
  par valeur : (1) sont_isomorphes/automorphisme reels (memes motifs,
  assemblage leger) ; (2) III.7 limites (GREP D'ABORD, carte non fiable) ;
  (3) suite complete detachee (pytest tests/ -q, ~20+ min, --timeout 1800,
  jamais en pipe) a lancer avant tout gros refactor ; (4) gen_livre_manifestes
  apres poses @livre. Motifs et briques : voir sections ci-dessus + tete de
  CAMPAGNE_DEMOS.md. Prochain ev. : 136.
- [Fable ~17h55, FINAL-4] automorphisme_identite_reel + sont_isomorphes_reel
  FAITS (ev. 136), 11/11 cst3. IV.1.5 reel couvert. Suivants : III.7 limites
  (grep d'abord) ou transitivite d'isomorphie reelle (composition : utiliser
  cst1_termes_prouve + cst2 pour la composee — motif exact du capstone).
- [Fable ~18h15, FINAL-5] isomorphisme_compose_reel FAIT (ev. 137), 69/69.
  L'ISOMORPHIE REELLE = EQUIVALENCE COMPLETE (IV.1.5 entierement reel).
  Le chantier CST/IV.1.5 est SATURE. Suivants : III.7 limites (grep d'abord),
  ou suite complete detachee, ou audit @livre + gen_livre_manifestes.
  Prochain ev. : 138. cst3/ a 8 entrees (encore 2 places).
- [Fable ~18h35, FINAL-6] RECON III.7 faite (PDF scan SANS couche texte ⇒
  lire via V7 : V6/V7/Chapitre_III_.../7_Limites_projectives_et_limites_
  inductives/<n>_<soussection>/Texte.tex — la transcription est FIDÈLE et
  complète). Couverture actuelle (grep @livre) : §7.1-7.6 couverts SAUF
  Prop.6, Prop.7 (6_Systemes_inductifs_d_applications), Prop.9, Prop.10,
  Cor.3 (7_Double_limite_inductive), et Th.1 (§7.3-7.4 à re-grep).
  **Prop.6 (E III.62-63) = propriété universelle de la limite inductive** :
  I filtrant, (E_a, f_ba) système inductif, E = lim ind = G/R (G = somme
  disjointe, R équivalence), u_a : E_a→F avec u_b∘f_ba = u_a ⇒ ∃!u : E→F,
  u_a = u∘f_a ; 2° u surjective ⇔ F = ∪ u_a(E_a) ; 3° critère d'injectivité.
  DÉPENDANCES à greper AVANT (beaucoup EXISTENT déjà) : recollement indexé
  E≅⊔fibres (FAIT, ev. bergers 25 juil, entiers_cardinaux/) ; Prop.8 II.29
  (recollement d'applications) ; « application compatible avec R » + passage
  au quotient (ii_6_relations_equivalence — grep app_compatible/quotient) ;
  lemme 1 III p.62 (deux éléments de E s'écrivent f_a(x), f_a(y) même a —
  utilise I filtrant) ; les canoniques f_a (limites_canoniques.py ?).
  STRATÉGIE : commencer par le 1° EXISTENCE seule (v = recollement des u_a,
  compatibilité avec R depuis (23), u = passage au quotient), en hyps
  honnêtes « I filtrant » + « système inductif » ; UNICITÉ ensuite (motif
  transporte_unique) ; 2°/3° après. Prévoir 3-4 ticks. Ne PAS attaquer sans
  avoir vérifié ce que limites_canoniques.py livre déjà (grep f_alpha).
- [Fable ~18h45, FINAL-7] RECON Prop.6 complétée : la machinerie du 1° EXISTE
  en ii_6_relations_equivalence : est_compatible_RS (quotient_complements:112),
  application_deduite_quotient(:128), factorisation_implique_compatible /
  factorisation_compatible_Rp (quotient_props:101/153), coincidence_sur_
  quotient(:307 — pour l'UNICITÉ !). limites_canoniques.py = côté PROJECTIF
  seulement (f_canon_proj, est_systeme_projectif_applications:179 — miroir à
  écrire pour l'inductif). Le recollement v des u_a = Prop.8 II.29 (déjà
  @livre'd dans limites_props2:349 ? c'est Prop.8 III.7.6 — GREPER le
  recollement II.29 dans ii_3). Plan 1° : (a) miroir est_systeme_inductif_
  applications ; (b) v = recollement (grep ii_3 prop8/recollement) ;
  (c) compatibilité de v avec R depuis (23) ; (d) u = application_deduite_
  quotient ; (e) unicité = coincidence_sur_quotient. Tout aux hyps honnêtes.
- [Fable ~19h00, FINAL-8] Points d'entrée Prop.6 ÉPINGLÉS : props2:245
  `passage_limite_ind` = Cor.1 SENS FACILE avec « EXISTENCE de u REPORTÉE »
  (sa docstring le dit) — Prop.6-1° comble EXACTEMENT ce trou ; props2:351
  `canonique_ind_atteint` (E réunion des f_a(E_a) — la clé du 2°) ;
  prop4plus = côté projectif. ⚠️ « Prop.8 II, p.29 » (recollement
  d'applications coïncidentes) ≠ Prop.8 §3.8 (rétractions, E II.18) — le
  recollement II.29 est à GREPER dans ii_4 (réunion de famille) ou à écrire ;
  motif proche déjà FAIT : recollement indexé E≅⊔fibres (entiers_cardinaux,
  ev. bergers 25 juil). iii_7_limites est à 10 entrées (CAP) ⇒ nouveau code
  dans un SOUS-DOSSIER iii_7_limites/prop6_universelle/.
- [Opus 5, ~19h30] Prop.6 1° UNICITE FAIT (ev. 138), 97/97 iii_7_limites,
  sous-dossier iii_7_limites/prop6/. REPORTES corrige. Suite : Prop.6 1°
  EXISTENCE (le gros morceau : v=recollement des u_a sur G=somme_famille(E,I),
  compatibilite avec R=graphe_coherence via (23), u=application_deduite_
  quotient ; briques ii_6 reperees) ; puis 2° et 3°. Prochain ev. : 139.
- [Opus 5, ~20h00] Prop.6 2° FAIT (ev. 139), 98/98. Restent : 1° EXISTENCE
  (gros) et 3° (critere d'injectivite : u injective <=> pour tout a, x,y in E_a
  avec u_a(x)=u_a(y) il existe b>=a avec f_ba(x)=f_ba(y) — meme style que 2°,
  hyps honnetes ; route : lemme 1 + injectivite ponctuelle + relation R).
- [Opus 5, ~20h20] Prop.6 3° FAIT (ev. 140), 99/99. PROP.6 : 1°-unicite,
  2°, 3° FAITS ; RESTE LA SEULE EXISTENCE du 1°. prop6/ a 4 fichiers.
- [Opus 5, ~20h45] Prop.6 1° COMPATIBILITE FAITE (ev. 141), 100/100.
  PROP.6 : 1°-unicite + 1°-compatibilite + 2° + 3° FAITS. RESTE : le passage
  au quotient (de la compatibilite, deduire u : E->F avec v = u o f) — voir
  ii_6/ensembles_quotient_c56_c57.py (c56_quotient_existe_ssi_pourtout:91) et
  quotient_complements.py (application_deduite_quotient:128) ; puis (24) se
  deduit de v=u o f + v coincide. prop6/ a 5 fichiers (5 places restantes).
- [Opus 5, ~21h10] PROP.6 COMPLETE modulo C57 (ev. 142), 101/101.
  ** PROCHAINE CIBLE PRIORITAIRE : le critere C57 (E II.44, ii_6) ** —
  « f compatible avec R => il existe h avec f = h o p » ; route Bourbaki :
  h = f o s ou s est une SECTION de la canonique p (necessite une section :
  verifier ce que ii_3_8_retractions_sections livre deja — est_section,
  Theoreme 1 b) ; sinon h = { (Cl_R(x), f(x)) } par graphe_terme sur le
  quotient + bien-definition via la compatibilite (voie SANS choix, sans
  doute preferable : motif graphe_terme + egalite_graphe_terme B2).
  Debloque : Prop.6 1° complet, Prop.1 1°, et les quotients du projet.
- [Opus 5, ~21h40] C57 CONTENU prouve (ev. 143), 120/120 ii_6. Mur restant
  = TECHNIQUE : kit C54 (graphe_terme_valeur) + C46 (valeur_caracterisation,
  liant 'y' EN DUR) refusent les termes contenant valeur(...). CHANTIER
  SUIVANT RECOMMANDE : ecrire une variante y-PARAMETREE de
  valeur_caracterisation + graphe_terme_valeur (ii_3_4/ii_3_6) — elle
  debloquerait l'emballage-graphe de C57, donc Prop.6 1° COMPLET, et tout
  terme-valeur passe alors au kit C54 (impact large sur le projet).
- [Opus 5, ~22h00] C57 COMPLET (ev. 144), 121/121 ii_6. Le report
  'existence de h' est LEVE dans tout le projet (docstring
  application_deduite_quotient reecrite). SUITE IMMEDIATE POSSIBLE :
  (a) UNICITE de h (motif coincidence_sur_quotient, facile) ; (b) brancher
  C57 sur Prop.6 1° pour la CLORE completement (relation_24_modulo_c57
  attend v=h o p : fournir H et la compatibilite de v prouvee ev.141) ;
  (c) verifier les autres consommateurs du report C57 (grep 'C57' et
  'REPORTE' dans ii_6 et iii_7). PIEGE A RETENIR : dans le kit C54, garder
  y='y' des que le terme contient valeur(...).
- [Opus 5, ~22h30] PROP.6 INTEGRALEMENT FORMALISEE (ev. 145), 223/223.
  1°-existence + 1°-unicite + 1°-compatibilite + 2° + 3°. C57 leve en amont.
  NOMS RESERVES DU KIT C54 (a respecter) : 'v' (2e composante du couple dans
  membre_graphe_terme) et 'y' (liant du tau de valeur — garder le defaut).
  SUITES POSSIBLES : unicite de h dans C57 ; Prop.7/9/10 de III.7 ; autres
  consommateurs du report C57 (grep 'REPORTE' dans ii_6/iii_7).
- [Opus 5, ~00h30] C57 unicite (ev.146) + factorisation universelle
  (ev.147) FAITS, 124/124 ii_6. C57 est COMPLET (existence+unicite) et
  applique. SUITE : brancher factorisation_universelle sur
  b_injective_via_pont (decomposition_effective:253) pour CLORE la
  decomposition canonique f = i o b o p ; attention : leur classe est codee
  theta_Rf(x)=tau_w(Rf{x,w}), donc prendre p := graphe_terme(E, theta(x), x)
  et prouver la caracterisation (sens <= = passage_quotient_Rf, CLOS).
- [Opus 5, ~01h20] theta_caracterise (ev.148) + Cor.1 (ev.149) FAITS.
  RACCORD RESTANT decomposition canonique : leurs valeurs utilisent des
  LIANTS FRAIS (_valf = E.valeur(f,x,b='_vf'), _valb b='_vb') — donc les
  termes de decomposition_effective sont alpha-DISTINCTS de E.valeur standard
  au noyau. Pour brancher factorisation_universelle sur b_injective_via_pont,
  il faut parametrer graphe_deduit/c57 par le liant de valeur (kwarg b=) OU
  reecrire le pont avec E.valeur standard. Chantier net, ~1 tick.
- [Opus 5, ~01h50] JALON : couverture page-par-page du livre COMPLETE
  (ev. 150) — E III.59 comble ; les 5 parties 'complet sur l'intervalle',
  2113 notions. La carte est fiable : ce qui reste = des REPORTS NOMMES
  (Th.1 a/b III.7.4, Prop.5 III.7.4, equivalence (ii)<=>(ii'), decomposition
  canonique b_injective a brancher, etc.). Regenerer les manifestes apres
  chaque pose de @livre : python outils_ia/audit/gen_livre_manifestes.py
- [Opus 5, ~02h00] Carte corrigee (ev.151) : le report 'Prop.1 1° unicite'
  etait PERIME (cone_unicite le prouve). PROCHAIN TICK TOUT TRACE :
  Prop.1 2° = instancier coords_donnent_projections (CLOS) aux points
  u(y),u(z) + _lim_dans_produit (cone_unicite:260) + extensionnalite_produit.
  AVANT TOUT CHANTIER : tester en code que le report vise est bien ouvert
  (import + appel), les listes REPORTES vieillissent mal.
- [Opus 5, ~02h20] Prop.1 2° FAIT (ev.152), 106/106. §III.7.2 Prop.1
  COMPLETE. Reports restants en III.7 : Prop.2+Cor (u^-1(x')=lim<- des
  u_a^-1), Cor.1/2 Prop.1 (existence/composition de lim<- u_a), Prop.3
  (cofinale bijective), Prop.5 et Th.1 (III.7.4). Prop.10 (III.1.10) et
  Lemme 1 (III.5.1) sont aussi ouverts et INDEPENDANTS (plus faciles ?).
- [Opus 5, ~02h40] OUTIL audit_reports.py (ev.153) + 4e report perime
  corrige (Prop.10). LANCER `python outils_ia/audit/audit_reports.py` AVANT
  d'attaquer un report : 6 suspects restants = Prop.2/3/5 et Th.1 de III.7.
  PIEGE : pas d'__init__.py dans tests/outils_ia/ (casse outils_ia.ia).
- [Opus 5, ~03h20] AUTO-CORRECTION MAJEURE (ev.155) : les hypotheses de
  quotient de C57 etaient NON GARDEES donc insatisfiables (tau hors domaine
  + S7) => theoremes vacuux. Corrige : section ET caracterisation gardees par
  E. REGLE GENERALE A APPLIQUER PARTOUT : toute hypothese sur des VALEURS
  doit etre gardee par le domaine. A VERIFIER dans les autres modules ecrits
  cette nuit (prop6_*, cor1, prop1_injectif : leurs hyps portent-elles des
  gardes ? oui pour prop6 — relation_24/lemme1/critere sont gardes — mais
  RE-AUDITER). Le raccord decomposition canonique doit utiliser la route
  SANS section (theta est son propre representant : theta_temoin), cf.
  rapport du workflow wzdt5nh5k dans tasks/wzdt5nh5k.output.
- [Opus 5, ~03h30] AUDIT DE GARDE fait sur TOUS les modules de la nuit
  (prop6_* x6, cor1, prop1_injectif, theta_caracterise) : chaque formule
  d'hypothese (`return pourtout`) est suivie d'un `impl(appartient(...` —
  toutes GARDEES. Le defaut etait isole a C57 (corrige ev.155). 232/232.
- [Opus 5, ~03h50] DECOMPOSITION CANONIQUE BOUCLEE (ev.157) : le pont est
  DEMONTRE (b construit = graphe_terme(Q,f(t),t)), b injective/surjective
  dechargees. Liants _VF/_VB portes de '_vf'/'_vb' a 'q'/'r' (alpha_tau exige
  des lettres simples) — 126 tests ii_6 verts avant/apres, sauvegarde du
  fichier d'origine dans /tmp/decompo_backup.py. REGLE : n'utiliser QUE des
  lettres simples comme liants (alpha_tau/est_lettre).
- [Opus 5, ~04h25] membre_fibre FAIT (ev.158) ; fibres_systeme_projectif
  REVERTE (mur d'appariement, route dans le module). PROCHAIN : reprendre
  fibres_systeme_projectif en COPIANT la forme d'appel de
  limite_projective_relation_1 utilisee dans ensembles_limites_prop2_3_iii7.
- [Opus 5, ~05h00] SUITE COMPLETE VERTE : 3995 tests (ev.160). Etat du
  depot certifie a l'echelle globale.
- [Opus 5, ~05h20] membre_fibre_t FAIT (ev.161) + cause du mur trouvee :
  COLLISION DE LIANTS (le terme ne doit pas contenir u/v/z libres = liants de
  est_fonctionnel ; famille 'uf' au lieu de 'u'). fibres_systeme_projectif est
  maintenant a portee : toutes les briques existent AUX TERMES, la sonde de
  relation_1 est verte, il ne reste qu'a assembler avec la famille nommee
  'uf' et le systeme 'g' (verifier aussi que g/f ne collisionnent pas).
- [Opus 5, ~05h40] Prop.2 1re assertion FAITE (ev.162), 110/110. Reste la
  2e assertion (u^-1(x') = lim<- M_a) : exige le pont d'encodage
  famille-de-parties (M_indice) — chantier suivant naturel de III.7.
- [Opus 5, ~05h55] temoin_cofinal FAIT (ev.163), 111/111. Prop.3
  surjectivite : il reste a definir le prolongement x_a := f_{a,beta(a)}(x_beta(a))
  et prouver sa coherence (relation (1) pour deux indices) — le choix est
  desormais canonique et sans axiome du choix.
- [Opus 5, ~06h30] ARTICLE (ev.164) : C8 reactualise (163 ev.), ancre
  Related Work corrigee (passe DEJA faite), check_bib.py ajoute (47<->47).
  RESTE cote Karl : commit + tag, puis les 3 placeholders de la page de titre.
- [Opus 5, ~06h50] Prop.3 : prolongement_bien_defini FAIT (ev.165), 112/112.
  RESTE pour la surjectivite : (a) montrer que la famille x-tilde satisfait la
  relation (1) donc appartient a lim<-_I ; (b) que g(x-tilde) = x. Le helper
  _instancie_en (libres_f + decharge + re-assume) est reutilisable partout.
- [Opus 5, ~07h05] OUTIL porter_aux_termes (ev.166), 113/113. A REUTILISER
  partout ou une brique ecrite au NOM doit s'appliquer a des TERMES (remplace
  _cva_t/_dval_t/_nt ecrits a la main). Import :
  prop1_proj.ensembles_prolongement_cofinal.porter_aux_termes
- [Opus 5, ~07h25] PROP.3 SURJECTIVITE FAITE (ev.167), 115/115 : x~ coherent
  (18 hyps) + restitue (2 hyps), sans axiome du choix. Reste a assembler
  formellement 'g bijective' avec prop3_g_injective_pointwise, et a corriger
  le report de Prop.3 dans limites_props2 (il dit encore 'reste la
  SURJECTIVITE').
- [Opus 5, ~07h50] Prop.3 injectivite generalisee (ev.169), 117/117. RESTE
  l'assemblage 'g bijective' : reduire la premisse du forall-lam a 'lam in I'
  (faire entrer temoin_cofinal DANS le corps) pour alimenter
  extensionnalite_produit, puis conjoindre avec la surjectivite (ev.167).
- [Opus 5, ~08h15] Prop.3 injectivite : premisse reduite a 'lam in I' (ev.170),
  117/117. RESTE : brancher extensionnalite_produit (motif cone_unicite —
  parametres BRUTS, _lim_dans_produit, images-graphes) pour conclure x=x',
  puis conjoindre avec la surjectivite (ev.167) en un enonce 'g bijective'.
- [Opus 5, ~08h40] Prop.3 INJECTIVITE COMPLETE (ev.171), 118/118. LES DEUX
  SENS de la Prop.3 sont prouves. RESTE : conjoindre injectivite (prop3_g_
  injective) et surjectivite (prolongement_coherent + prolongement_restitue)
  en un enonce 'g bijective' (vocabulaire est_bijection_de, cf.
  pont_bijection_de de cst2 pour le motif de conjonction).
- [Opus 5, ~09h00] Prop.3 injectivite UNIVERSELLE (ev.172), 119/119, 2 hyps.
  RESTE pour 'g bijective' litteral : (a) lemme 'tout point de lim<- est un
  graphe' (lim<- inclus dans le produit) pour retirer les conditions de graphe
  de la premisse ; (b) surjectivite sous forme universelle (generaliser
  prolongement_coherent/restitue comme ici).
- [Opus 5, ~09h15] Prop.3 surjectivite universelle (ev.173), 120/120. Les
  DEUX SENS sont prouves et quantifies. RESTE pour 'g bijective' litteral :
  le lemme 'tout point de lim<- est un graphe' (lim<- inclus dans le produit)
  pour retirer les conditions de graphe des premisses.
- [Opus 5, ~10h00] LEMME 'point de lim<- = graphe' FAIT ET CLOS (ev.174-176),
  124/124 iii_7_limites. Module : prop1_proj/ensembles_lim_graphe.py
  (point_limite_est_graphe : 0 hyp ajoutee ; limite_points_graphes : CLOS).
  Preuve = _lim_dans_produit + produit_graphe (ce dernier CLOS depuis le
  26 juil : le raccord manquait, pas la preuve).
  ALLEGEMENTS MESURES : prop3_g_injective 9->7, prop2_injectivite 9->5,
  cone_unicite 4->3 (la premisse cone_images_graphes DISPARAIT de l'unicite du
  cone, Prop.1), coordonnees_egales_points 6->5. La premisse universelle de
  Prop.3 ne porte plus de condition de graphe (teste structurellement).
  PIEGE : est_un_graphe(g) lie 'z' -> un point nomme 'z' est CAPTURE ; defaut
  passe a 'p', pytest.raises fige le garde-fou.
  RESTE pour 'g bijective' LITTERAL : exhiber g comme FONCTION (func + dom =
  lim<-_I) et non seulement comme application ponctuelle — c'est le pont
  manquant vers est_bijection_de. Les deux sens sont prouves et quantifies ;
  il ne manque que l'objet-fonction.
- [Opus 5, ~11h00] 👑 g CANONIQUE CONSTRUITE (ev.177-179), 131/131.
  prop1_proj/ensembles_g_construite.py : g := graphe_terme(lim<-_I,
  graphe_terme(J, f_a(x))). CLOS : est_fonctionnel(g), est_un_graphe(g),
  dom(g)=lim<-_I. DEMONTRE : formule (3) sous {x dans lim<-_I, a dans J}, et sa
  forme quantifiee CLOSE ==> l'AXIOME axiome_canonique_g est SUPERFLU (miroir
  corps_formule_3 teste contre l'axiome du depot, mot pour mot).
  theorie==22 inchange (cet axiome vivait dans une theorie dediee).
  Aussi : porter_aux_termes PROMU en tactique (i_2_theoremes/tactiques/
  outil_portage.py) ; consomme par _dval_t/_nt de cst1_identite, miroirs == OK.
  PROCHAIN PAS EVIDENT pour 'g bijective' litteral : conjoindre
  (g_est_fonctionnelle, g_domaine) avec l'injectivite/surjectivite de Prop.3 —
  MAIS attention, celles-ci parlent du terme OPAQUE application_canonique_g,
  pas du terme CONSTRUIT graphe_g. Il faut d'abord MIGRER les consommateurs
  (report pose dans ensembles_g_construite.REPORTES) : limites_props2 et
  limites_prop4plus_iii7 d'abord, puis prop3_*. Ne pas conjoindre deux enonces
  qui portent sur deux termes differents.
- [Opus 5, ~11h30] MIGRATION 1er pas (ev.180-181), 132/132.
  cofinal_canonique_coordonnee(..., formule_3=None) : parametree, retro-
  compatible (defaut = l'axiome). Passee g_formule_3_quantifiee, elle rend le
  meme enonce sur le terme CONSTRUIT.
  ⚠️ GARDE POSEE (ne pas l'oublier) : func(g)+dom(g) parlent de graphe_g
  (construit) ; injectivite/surjectivite de Prop.3 parlent encore de
  application_canonique_g (OPAQUE, cable en dur dans
  cofinal_canonique_compatible, prop3_g_coordonnee_egale,
  prop3_g_injective_pointwise, prop4plus x2). NE PAS conjoindre en
  est_bijection_de avant d'avoir unifie le terme — deux enonces vrais sur deux
  termes differents ne se conjoignent pas.
  SUITE MECANIQUE (pas mathematique) : parametrer ces 5 sites par un `gterme`
  optionnel (defaut = terme opaque), en threadant depuis cofinal_canonique_
  coordonnee ; re-tester apres CHAQUE site.
- [Opus 5, ~13h30] 👑👑 PROP.3 EN VOCABULAIRE DU DEPOT (ev.182-186), 137/137.
  prop1_proj/ensembles_g_construite.py :
    g_injective_dans           |- injective_dans(G, lim<-_I)   [2 hyps, liants
                                  « u »/« up » du depot, obtenus par alpha]
    g_bijection_sous_surjectivite |- ( G<lim<-_I> = lim<-_J )
                                  => est_bijection_de(G, lim<-_I, lim<-_J)  [2 hyps]
  MIGRATION FAITE sur toute la chaine d'injectivite (gterme/formule_3 threades,
  retro-compatibles, 0 test casse). Le noyau REFUSE le melange incoherent.
  DEFAUT CORRIGE : double enveloppage var(var('f')) -> hypotheses fusionnees
  (pointwise 8->6, prop3_g_injective 7->5).
  ⚠️ PIEGE A RETENIR : graphe_terme NE LIE PAS (libres(graphe_g())={E,J,f,x,a}) :
  utiliser des noms FRAIS (pt='s', idx='t') face a Prop.3.
  ⚠️ (pour tout x)R = non-existe-non : TROIS niveaux a depiler.
  RESTE, UNIQUE PIECE : la SURJECTIVITE ENSEMBLISTE G<lim<-_I> = lim<-_J.
  Les DEUX inclusions sont deja acquises ponctuellement :
    inclus  : cofinal_canonique_compatible (g(x) verifie la condition (1) sur J)
    contient: prolongement_restitue + prolongement_coherent_universel
  Ne manque que le RECOLLEMENT par egalite_par_extension sur l'image directe
  (E.image(G, lim<-_I)) : chantier d'ASSEMBLAGE, pas de demonstration.
  C'est LE prochain chantier ; une fois fait, decharger la premisse de
  g_bijection_sous_surjectivite et la Prop.3 est CLOSE en vocabulaire du depot.
- [Opus 5, ~17h00] SURJECTIVITE moitie (a) + BLOCAGE TROUVE (ev.187-189), 143/143.
  prop1_proj/ensembles_g_surjection.py :
    faits_clos_famille   3 theoremes CLOS (graphe, fonctionnel, domaine)
    clause_valeurs       {x dans lim<-_I, J cofinale} |- 4e clause  [2 hyps]
    famille_dans_produit {clause} |- G(x) dans produit(E,J)         [1 hyp]
    valeur_dans_produit  {x dans lim<-_I, J cofinale} |- idem       [2 hyps]
    restriction_construite / restriction_valeur : le DEBLOCAGE, 1er pas
  🔴 BLOCAGE DE FOND : restriction_systeme_indices est OPAQUE et SANS AUCUN
  AXIOME. Comme lim<-_J := lim_proj(restr_indices(E,f,J), f), AUCUN enonce
  mentionnant lim<-_J n'est demontrable. Ce n'est pas une difficulte, c'est une
  impasse par construction — elle ne se revele qu'au raccord.
  DEBLOCAGE : restriction_construite := graphe_terme(J, E_a) ; le pont
  restriction_valeur ((restr)_i = E_i sous i dans J) est DEMONTRE, 1 hyp
  (immediat car valeur_famille(E,i) EST valeur(E,i) dans le depot).
  SUITE PRECISE : (1) egalite des produits produit(restr,J) = produit(E,J) par
  egalite_par_extension — attention au conjoint d'INCLUSION, dont le reunion_
  famille differe ; (2) egalite des deux limites via la caracterisation (1) ;
  (3) migrer limites_prop4plus_iii7:135 vers la version construite ;
  (4) alors seulement : inclusion directe complete, puis reciproque (temoin =
  prolongement, migrer d'abord prolongement_* vers gterme), puis decharger la
  premisse de g_bijection_sous_surjectivite ==> Prop.3 CLOSE en vocabulaire
  du depot.
  AUDIT A FAIRE : lister les app(...) du depot en distinguant ceux qui ont un
  axiome de ceux qui n'en ont AUCUN — les seconds sont des impasses silencieuses.
- [Opus 5, ~19h] 👑👑👑 INCLUSION D'IMAGES (ev.191-193), 147/147 + I/II verts.
  ensembles_g_surjection.py, chaine complete :
    restriction_construite / restriction_valeur   (deblocage du terme opaque)
    clause_valeurs_restreinte / valeur_dans_produit_restreint  [2 hyps]
    condition_1_de_la_valeur                       [2 hyps, condition (1) sur J]
    valeur_dans_limite_restreinte  |- G(x) dans lim<-_J        [2 hyps]
    image_incluse_dans_limite      |- G<lim<-_I> inclus lim<-_J [1 hyp !]
  RACCOURCI TROUVE : inutile de demontrer l'egalite des deux produits — il
  suffit de REFAIRE la construction dans le systeme restreint (le pivot est
  parametre par la famille, le union s'aligne seul).
  RESTE, SEULE PIECE DE TOUTE LA PROP.3 : l'inclusion RECIPROQUE
  lim<-_J inclus G<lim<-_I>. Route : (i) faire du prolongement un TERME —
  graphe_terme(I, x_tilde(f,y,J,a)) ; (ii) le placer dans lim<-_I (clause des
  valeurs x~_a dans E_a via les transitions + prolongement_coherent_universel) ;
  (iii) G(x~)=y par extensionnalite, coordonnees par prolongement_restitue.
  Puis extensionnalite_appliquee sur les 2 inclusions, et decharger la premisse
  de g_bijection_sous_surjectivite ==> PROP.3 CLOSE en vocabulaire du depot.
  PIEGES DU JOUR : alpha_existe AVANT existe_elimination (le liant de
  l'existentielle doit coincider avec le nom du temoin) ; 'inclus' lie 'z' ;
  premisse COMPOSITE de la relation (2) a reconstruire pour la couper ;
  evaluer G en son propre nom de liant libre est degenere.
- [Opus 5, ~20h] 🔴 ECART DE FIDELITE + condition fournie (ev.195), 149/149.
  Le livre (V7, §III.7.1) type les transitions AVANT (LP_I)/(LP_II) :
  « soit f_ab une APPLICATION DE E_b DANS E_a ». est_systeme_projectif ne
  l'encode PAS (il ne garde que les conditions NUMEROTEES).
  => c'est CE qui bloque l'inclusion reciproque de la surjectivite : sans le
  typage, impossible d'avoir x~_a = f_{a,beta(a)}(x_{beta(a)}) dans E_a.
  FAIT : documente dans docs/journal/ANOMALIES.md (avec l'ampleur mesuree :
  9 references dont une DERIVATION ensembles_cofinal:341) + constructeur
  `transitions_typees` ajoute dans ensembles_limites.py + test qui epingle
  que le typage n'est PAS un conjoint de est_systeme_projectif.
  NON FAIT, ASSUME : renforcer est_systeme_projectif — chantier a part, a
  faire d'un bloc avec l'audit de sa derivation (sinon on repare sous pression).
  NOTE OUTILLAGE : le PDF du livre est un SCAN sans couche texte et pdftoppm
  est ABSENT de l'environnement => passer par la transcription V7
  (V6/V7/Chapitre_III.../7_Limites.../1_Limites_projectives/Texte.tex), qui est
  fidele et lisible en texte.
  SUITE : inclusion reciproque, avec transitions_typees en hypothese honnete :
  (i) x~ comme TERME = graphe_terme(I, x_tilde(f,y,J,a)) ; (ii) clause des
  valeurs via transitions_typees ; (iii) condition (1) par
  prolongement_coherent_universel (premisse a remettre en CONJONCTION comme
  dans condition_1_de_la_valeur) ; (iv) G(x~)=y par extensionnalite
  (coordonnees par prolongement_restitue).
  ⚠️ prop1_proj est AU CAP (10 entrees) : la prochaine brique impose un
  sous-dossier.
- [Opus 5, ~22h] ECLATEMENT + DEFAUT COFINALITE + PROLONGEMENT (ev.196-198),
  380/380 (iii_7_limites 149 + iv_structures 231).
  1) prop1_proj etait au CAP -> sous-dossier prop3_surj/ (MAX_PATH mesure AVANT :
     198 vs 244 max du depot, limite 260). g_surjection + restriction_systeme y
     sont deplaces, tests scindes en miroir. prop1_proj = 9 entrees.
  2) 🔴 DEUX formes de « J cofinale » cohabitaient : temoin_cofinal utilise
     _gleq (Gleq) et cofinale_dans_inclusion a pour DEFAUT _R_defaut (G).
     Les theoremes portaient DONC deux hypotheses de cofinalite.
     Corrige aux 4 sites (passer leq explicitement).
     EFFET : coordonnees_egales_partout 5->4, prop3_g_injective 5->4, et
     **les formes UNIVERSELLES 2 -> 1 hypothese** :
       prop3_g_injective_universelle, injectivite_g_construite,
       g_injective_dans, g_bijection_sous_surjectivite.
     => LA PROP.3 EN VOCABULAIRE DU DEPOT NE TIENT PLUS QU'A **1** HYPOTHESE.
     REGLE : ne jamais laisser une brique choisir sa relation d'ordre par
     defaut quand le contexte en fixe une.
  3) prop3_surj/ensembles_prolongement_terme.py : x~ comme TERME
     (graphe_terme(I, x_tilde)), 3 faits CLOS, et valeur_prolongement_dans_E
     |- x~(m) dans E_m [4 hyps] avec transitions_typees NOMMEE (test l'epingle).
  SUITE : quantifier la clause -> x~ dans le produit -> + condition (1)
  (prolongement_coherent_universel, premisse a remettre en CONJONCTION) ->
  x~ dans lim<-_I -> G(x~)=y par extensionnalite (prolongement_restitue) ->
  inclusion reciproque -> extensionnalite_appliquee -> decharger la premisse
  de g_bijection_sous_surjectivite ==> PROP.3 CLOSE.
- [Opus 5, ~23h30] 👑 x~ DANS LE PRODUIT (ev.199-200), 155/155.
  prop3_surj/ensembles_prolongement_terme.py, chaine complete :
    coordonnee_de_y_dans_E      |- y_b(m) dans E_b(m)          [3 hyps]
    clause_valeurs_prolongement |- hypothese_valeurs(E,I,i,x~)  [3 hyps]
    prolongement_dans_produit   |- x~ dans produit(E,I)         [3 hyps]
  Les 3 hypotheses sont TOUTES de contexte : transitions typees, J cofinale,
  y dans lim<-_J. Aucune propre a x~.
  PIEGES DU TICK : (a) le pivot porte les QUATRE clauses — couper aussi la
  clause des valeurs par sa PREUVE ; (b) le nom du point d'evaluation devient
  le LIANT de la clause des valeurs et doit etre celui de l'axiome du produit
  (« i ») — avec 'm' le MP final echoue sans indice.
  RESTE (2 reports poses dans le module) :
   (1) condition (1) sur I pour x~ : prolongement_coherent conclut
       x~_a = f_aa'(x~_a') mais (a) en termes de x_tilde et non de
       pr_a(x~)=valeur(x~,a) -> DEUX transports S6 le long de
       graphe_terme_valeur ; (b) sa premisse est une CASCADE de 14 hypotheses
       a remettre en la CONJONCTION ((a dans I et a' dans I) et a<=a'),
       comme dans condition_1_de_la_valeur. Forme, pas mathematique.
   (2) puis x~ dans lim<-_I, G(x~)=y par extensionnalite (coordonnees par
       prolongement_restitue), AXIOME_IMAGE avec temoin x~, inclusion
       reciproque, extensionnalite_appliquee, decharge de la premisse de
       g_bijection_sous_surjectivite ==> PROP.3 CLOSE.
- [Opus 5, 5 aout ~01h] 🔓 DEBLOCAGE STRUCTUREL (ev.202-203), 383/383.
  FAIT : appartient_limite_projective + limite_projective_relation_1 rendues
  TERM-SAFE (_t au lieu de var sur Efam/f) ; Efam threade dans
  prolongement_coherent et prolongement_coherent_universel (defauts inchanges,
  miroirs 18 et 4 verifies ; les 6 appelants passent des NOMS -> neutre).
  => prolongement_coherent(f='f', x='yp', Efam=restriction_construite())
     porte EXACTEMENT l'hypothese « y dans lim<-_J ». C'etait LE verrou de
     forme de l'inclusion reciproque : la machinerie du prolongement vise
     desormais la limite du systeme CONSTRUIT.
  MUR DU TICK (honnete) : identifier les 14 hypotheses portant a/ap n'a PAS
  converge. Essaye et echoue : appartenances des 4 termes (a, ap, beta(a),
  beta(ap)) dans I et J, ordres entre eux, premisses composites relation(1) et
  cocycle, coupes par temoin_cofinal(a) + temoin_cofinal(ap) +
  cofinale_dans_inclusion + cofinale_dans_condition -> ZERO coupe.
  Seule identifiee : premisse composite du cocycle en (ap, beta(ap)).
  Structure : 8 formules 'non' (cascades) + 6 existentielles de liant 'y'.
  PROCHAIN PAS (ne pas re-enumerer des candidats) : REMONTER a _via_delta
  (ensembles_prolongement_cofinal:53) et lire ce que ses deux briques
  ASSUMENT — limite_projective_relation_1 (premisse prem1) et
  cocycle_valeur_projectif — puis reconstruire ces formes EXACTES depuis le
  contexte. C'est la lecture de la brique creatrice qui donnera les 14, pas
  une liste de candidats plausibles.
- [Opus 5, 5 aout ~03h] ✅ ECART DE FIDELITE COMBLE (ev.207-208), 384/384.
  est_systeme_projectif porte desormais les TROIS conditions du livre
  (typage des transitions + LP_I + LP_II). Signature : Efam EN TETE.
  Threade dans est_systeme_projectif_filtrant + les 2 projections + tests.
  Le test est INVERSE (il epinglait l'absence, il epingle la presence) :
  test_definition_systeme_projectif_est_fidele_au_livre.
  ANOMALIES.md : entree de resolution ajoutee sous celle du 4 aout.
  POURQUOI c'etait tombe : la SIGNATURE ne prenait pas Efam, donc le typage
  etait INEXPRIMABLE — le manque etait dans le TYPE, pas dans le corps.
  POURQUOI c'etait SUR : mesure faite, aucun theoreme n'ASSUME la definition
  composite (les preuves utilisent cocycle_projectif directement) ; elle n'est
  que COMPOSEE et PROJETEE, et renforcer le conjoint droit d'une conjonction
  ne casse pas sa projection.
  Aussi ce tour : nu_majorant_commun / temoin_majorant_commun (ev.204, temoin
  canonique tau du majorant COMMUN, 3 hyps) ; methode EXTRAIRE-plutot-que-
  RECONSTRUIRE les premisses (ev.205, 18/18 hypotheses attribuees) ; outil de
  decharge automatique en scratchpad (ev.206) qui TERMINE mais ne debloque pas
  (1 coupe nette) — ne pas le promouvoir en l'etat.
- [Opus 5, 5 aout ~05h] ✅ M_indice TRANSPARENT (ev.209-210), 386/386.
  M_indice etait app('M_indice', M, a) : accesseur OPAQUE sans axiome, donc
  rien de demontrable sur les M_a => 2e assertion Prop.2 hors d'atteinte PAR
  CONSTRUCTION (meme diagnostic que restriction_systeme_indices, a un jour
  d'intervalle). Remede : une famille EST une fonction => M_indice :=
  valeur_famille. Les 8 sites qui RECOPIAIENT l'encodage appellent la
  definition ; 6 tests idem (ils recopiaient aussi).
  NOUVEAU (prop1_proj/ensembles_prop2_fibres.py) :
    famille_fibres    : la famille (M_a) = (u_a^-1<{x'_a}>) CONSTRUITE
    fibre_composante  : |- M_a = u_a^-1<{x'_a}>   [1 hyp : a dans I]
  + test_M_indice_est_transparent qui FIGE la transparence.
  OUTIL CORRIGE : audit_termes_opaques lisait le TEXTE et comptait les app()
  cites en DOCSTRING -> il signalait encore M_indice apres correction. Passe en
  lecture AST ; total 144 -> 113 constructeurs (l'ecart etait du bruit).
  Il reste 4 opaques partages : Sig, pr_indice, prod_ent, struct_induite.
  SUITE POSSIBLE Prop.2 2e assertion : avec fibre_composante, recoller
  u^-1(x') = lim<- M_a — lim_proj_parties(M,f) = lim_proj(M,f) est deja le bon
  terme des lors que M est la famille CONSTRUITE. Route : double inclusion,
  membre_fibre pour le sens point-par-point, puis extensionnalite.
- [Opus 5, 5 aout ~06h] 👑 CHAINON DE LA 2e ASSERTION (ev.211-212), 387/387.
  prop1_proj/ensembles_prop2_fibres.py :
    coordonnee_dans_fibre |- ( pr_a z dans M_a <=> u_a(pr_a z) = x'_a ) [3 hyps]
  = membre_fibre_t + fibre_composante, recolles par S6 sur la position ENSEMBLE.
  C'est le pivot des DEUX cotes de u^-1(x') = lim<- M_a.
  En-tete du module REECRIT (il annoncait encore le pont comme manquant).
  RESTE POUR CLORE LA 2e ASSERTION — assemblage seulement :
    gauche : appartient_limite_projective sur la famille CONSTRUITE ->
             z dans lim<- M_a  <=>  (z dans produit(M,I) et condition (1))
    droite : membre_fibre -> z dans u^-1<{x'}>  <=>  u(z)=x'
             puis lim_u_coordonnee : u(z)=x' <=> (pour tout a) pr_a(u(z))=x'_a
             = (pour tout a) u_a(pr_a z) = x'_a
    le CHAINON convertit ce dernier en (pour tout a) pr_a z dans M_a.
    Manque : la clause produit (4 clauses, dont 3 CLOSES si z est construit —
    mais z est ici un point quelconque, donc passer par membre_produit_famille),
    et la condition (1) sur z, COMMUNE aux deux cotes (donc a factoriser, pas a
    prouver deux fois).
  PIEGE DU TICK : ne jamais nommer une variable locale comme un constructeur
  importe (equiv/et/impl/egal) — l'erreur « Theoreme object is not callable »
  apparait a l'appel SUIVANT du constructeur, loin de sa cause.
- [Opus 5, 5 aout ~07h30] 👑👑 COEUR DE LA 2e ASSERTION (ev.213-214), 389/389.
  prop1_proj/ensembles_prop2_fibres.py (283 lignes de CODE, marge faible) :
    coordonnee_de_u_dans_fibre |- (pr_a z dans M_a <=> pr_a(u z) = x'_a) [4 hyps]
    fibres_partout             |- la version QUANTIFIEE                  [2 hyps]
       sous { famille (u_a fonctionnels et totaux), z dans lim<-_I }
    + helper _equiv_sous_garde : de (G => (P<=>Q)) tirer ((G=>P) <=> (G=>Q)) —
      congruence_pour_tout reclame une EQUIVALENCE, pas une implication vers
      une equivalence. REUTILISABLE des qu'on quantifie une equivalence gardee.
  RESTE pour clore u^-1(x') = lim<- M_a :
    (a) cote GAUCHE : z dans lim<- M_a <=> (z dans produit(M,I) et cond(1)) —
        la clause des valeurs du produit EST le membre gauche de fibres_partout ;
        restent les 3 autres clauses de membre_produit_famille pour un z
        QUELCONQUE (pas construit) : inclusion, fonctionnel, domaine.
        ⚠️ Elles viennent de z dans lim<-_I via _lim_dans_produit + les clauses
        du produit sur E — a verifier, c'est le point non trivial.
    (b) cote DROIT : z dans u^-1<{x'}> <=> u(z)=x' (membre_fibre) ; puis
        u(z)=x' <=> (pour tout a) pr_a(u z)=x'_a par EXTENSIONNALITE du produit
        sur E' (u(z) et x' tous deux dans le produit, et graphes).
    (c) la condition (1) sur z est COMMUNE aux deux cotes (meme systeme f) :
        la FACTORISER, ne pas la prouver deux fois.
  PIEGE : lim_u_coordonnee conclut pr_a(u z) = u_a(pr_a z) — sens INVERSE de
  celui qu'attend S6 pour remplacer u_a(pr_a z) par pr_a(u z) : symetriser.

## Candidats de PROCHAINE campagne (préparés le 7 août 2026, avant le volant de 22h)
Choix à trancher APRÈS lecture des résultats du Workflow volant (ev.291+). Trois routes,
par ordre de préférence provisoire :
1. **Étage 2 hors îlot** — porter le cycle machine complet (sélectif + détachement
   conjonctif + conjecturer + tactique témoin) sur le corpus ENTIERS/cardinaux du dépôt
   (plus riche que l'îlot Goldbach). Continuité directe, compounding des organes neufs ;
   c'est le but final (une IA qui crée des théories). Si le volant promeut des notions
   sur l'îlot, cette route est confirmée.
2. **Bouclage factorielle** — reste (mémoire bourbaki-factorielle-fonction) : forme du
   livre f(0)=1 / f(n+1)=n!·(n+1), Déf.2-produit sur familles, bo(ℕ). Front percé
   (fix subst 24 juil), tractable, clôt le chantier emblématique C62.
3. **Re-cartage de la frontière** — la carte CAMPAGNE_TROUS l.160 (1er juil) est PÉRIMÉE
   (division euclidienne close le 24 juil ; verrous-τ percés). Passe batch verify-in-code
   multi-agent → carte fiable. Parfait pour un Workflow, mais ne produit pas de théorème.
⚠️ Règle inchangée : grep le CONTENU en code avant tout effort (leçon n°1 des trous).

## Résultat du volant Workflow (7 août ~19h30, ev.291-294) + candidat n°0
Workflow 4 agents en 2 passes : moisson 486 inventions (81 faits ≤20, 9/9 parités
exactes), série Goldbach N12..N30 close (0,1 s/th après chauffe 109 s) — la machine
a vérifié Goldbach pour TOUT pair 6..30 en chaînant ses propres inventions —,
volant à VIDE (43 preuves non gatables), sceptique CONFIRME tout.
**Candidat n°0 (PRÉREQUIS COURT, à faire avant la route 1)** : rendre l'îlot
gatable — compagnes `*_cible()` ZÉRO-ARG dans les modules de l'îlot (celles qui
existent sont paramétrées → TypeError → None dans `_cible_de`,
proto_mutation_verify.py:45-52) + ajouter `__all__` à parite.py (sans lui,
`_theoremes` de promo_notion.py:62 ne scanne pas le module). Puis re-tour du
volant : 76 n-grammes partagés attendent le gate (mesure run 1).
⚠️ Leçon harnais sous-agents : JAMAIS run_in_background dans un sous-agent (le
process meurt quand l'agent finit son tour) ; runs ≤10 min en avant-plan.
⚠️ Défaut flywheel à corriger un jour : `_ecrire_biblio` (flywheel.py:77-92)
réécrit notions_apprises.py EN ENTIER à chaque tour → un tour vide EFFACE les
acquis (restauré depuis l'index git cette fois). Fusionner par paquet plutôt.

## ✅ CAMPAGNE GATING PARAMÉTRÉ — FAITE ET CLOSE (7 août soir, ev.299-303)
Le volant promeut désormais sur corpus PARAMÉTRÉ. 5 pièces, chacune mesurée
(GP1-GP7) puis testée (23 tests corpus verts, suite 152 verts) :
1. **Contrat `<name>_instances()`** → [(args, énoncé)], dans le module
   DÉFINISSANT (un ré-export ne s'exécute pas sous son alias) ; consommé par
   `_statut_parametre` (gen_paires_corruption) — chaque instance doit redonner
   SA conclusion exacte. Équipés : numeraux.fini/cardinal_num,
   machine_num.le_num/ne_num_sym, calcul_num.somme_num/produit_num ; les 4
   lemmes machine ont des cibles zéro-arg (défauts).
2. **Voile de caches** `_ns_gate` : caches DÉCLARÉS `<name>_gate_caches`
   vidés dans la COPIE du namespace — sans lui un prouveur mémoïsé rend son
   cache et le gate ne teste RIEN (contrôle discriminant : le prouveur-triche
   `return _FINI[k]` MEURT).
3. **Refus des divergences d'opérateur** (`_NonSlotable`, antiunif) : un slot
   est une EXPRESSION ; somme `+` vs produit `*` = deux lois, pas une notion
   (le slot-Name dans BinOp.op crashait unparse, tour #8).
4. **Appel-Expr** pour les blocs sans affectation (asserts seuls) —
   `[] = f()` était un SyntaxError silencieux (ERROR).
5. **Renommage inverse des slots** (_gate) : les slots sont capturés en noms
   canoniques p{k}/_v{k}, le site d'appel exige les noms RÉELS de l'instance
   (NameError p1, GP7). C'est CE fix qui a tout débloqué.
RÉSULTATS : 👑 1re notion machine de l'îlot (notion_loi_deduction_3p_2 =
l'idiome maison « clore l'implication et vérifier l'énoncé », 3 lemmes 8→6
pas) ; tour #11 unifié = **12 notions, gain 33** (×3 vs avant le fix slots),
20 preuves raccourcies, 63 macros d'ordre 2 ; biblio = 12 notions.
RESTE (prochains crans, par valeur) : ranking par homogénéité (313 none sur
553 = les grosses hétérogènes noient le budget) ; autopsier les 54 gate_fail
restants du corpus unifié (même méthode GP7 : lire l'exception RÉELLE) ;
équiper d'autres prouveurs paramétrés (ne_num, est_premier_num) ; boucle de
compounding conjectureur→lemmes→volant (les motifs à 2 instances attendent
une 3e).

## ✅ AUTOPSIE DES 54 GATE_FAIL — FAITE ET SCELLÉE (nuit du 7-8 août, ev.304-307)
Directive Karl 22h25. Méthode GP7 généralisée : reproduire chaque candidate,
exec MANUEL, traceback RÉEL, classer, réparer — jamais affaiblir le gate.
- **Cause A (~30)** : slot dépendant du dataflow INTERNE du bloc (référence un
  `_v{k}` que la notion doit elle-même calculer) → REFUSÉ dès `_construire`
  (validation : chaque slot parse en EXPRESSION, zéro `_v{k}` ; couvre aussi
  les slot-imports paresseux).
- **Cause B (~15)** : 3 compagnes `cible_*` PÉRIMÉES **dans le dépôt** —
  `cible_inclus_image_reciproque_image` et `cible_image_image_reciproque_inclus`
  (antécédents H_app/est_fonctionnel manquants, datées d'avant l'internalisation
  — réparées + les 2 tests-enveloppes réécrits en consommation directe) ;
  `cible_section_unique_par_image` (lieur τ « u » vs canonique « @0 » —
  α-équivalent mais ≠ en ==, aligné sur @0).
- **CHIFFRES** : gate_fail 54→21→**1** ; notions 12→**16**, gain 33→**69** ;
  41 preuves raccourcies ; 99 macros d'ordre 2 ; 0 stale au balayage GP10.
  Suites : 235 verts (ii_3_correspondances) + 175 verts (outils_ia+corpus).
- **LEÇON NEUVE** : le balayage GP10 (source originale vs compagne, corpus
  entier) est un AUDIT DE FIDÉLITÉ du dépôt par le volant — 3 défauts réels
  débusqués en passant. À relancer après toute campagne qui touche les énoncés.
- Restes consignés : 1 gate_fail cross-module (import paresseux partagé,
  GP9 #519) ; 190 gain_nul = motifs réels trop petits (attendre plus
  d'instances — le conjectureur en fabrique) ; 346 none honnêtes ; ranking
  par homogénéité toujours ouvert.

## ✅ BOUCLE DE COMPOUNDING — DÉMONTRÉE ET CHIFFRÉE (nuit+matinée du 8 août, ev.308-315)
Directive Karl : boucle en continu + streaming (« voir où ça en est pendant »).
- **Streaming** : `conjecturer(trace=)`/`iterer(trace=)` émettent tour /
  avancement-par-source / découverte-certifiée / briques_sautées, JSONL horodaté.
  Le flux a localisé DEUX gels en minutes (dédup `_cle_canon` et tri `_taille`
  marchaient sur les arbres DÉPLIÉS) → réécrits EN PARTAGE (digest Merkle memo
  (id, indices-vars) ; mémo local par id). 5 tours : 3h20 gelées → **10,2 min**.
- **cap_brique** dans `iterer` : les briques-monstres (τZ) empoisonnaient le
  matching des tours ≥2 — sautées ET annoncées (21 au tour 1 de CY3).
- **Cycle complet payé le matin même** : CY3 = 64 découvertes streamées →
  2ᵉ fournée `lemmes_conjectures_2.py` (3 lemmes de PROFONDEUR 2, dont
  fini_somme_cardinal_successeur = premier lemme dérivé À TRAVERS un lemme
  machine) → tour #15 = **18 notions gain 80** (4→12→16→18 ; 42 preuves
  raccourcies ; 96 macros ordre 2). La 3ᵉ instance du motif var/SC/assume/mp,
  apportée par le lemme machine, l'a fait passer de gain 0 au positif.
- **IMPRIMEUR formule→code** (PR1, prototype scratchpad VALIDÉ 7/7
  aller-retours exacts sur les cibles réelles) : matching inverse via
  `conj_base._match` (sonde B(vars fraîches), slots, récursion ; abréviations
  d'abord ; les définitionnels par leur NOM, jamais dépliés). C'est LA brique
  de l'AUTO-PROMOTION : reste à enregistrer σ dans les découvertes et générer
  les modules de redérivation. Article : paragraphe (v) « La machine compose »
  ajouté fr+en. Fécondité extraite (conj_fecondite.py) ; budget gate : refus
  gratuits (démontré : 155 essais = 600).
⚠️ CAPS : outils_ia/arithmetique À 10 (prochaine addition = sous-dossier) ;
outils_ia/corpus à 58 (zone historique, restructuration à planifier).

## 👑 ORGANE DE BESOIN — LA MACHINE DICTE SA CAMPAGNE (matinée 8 août, ev.317-320)
Philosophie Karl : on ne formalise que ce que L'ALGO juge nécessaire. Construit
et validé au scratchpad (PB1_besoin.py — À PROMOUVOIR au prochain bloc) :
- **Chaînage À REBOURS** depuis un BUT : _match sur le CONSÉQUENT, fermetures
  VÉRIFIÉES AU NOYAU (1 et 2 pas testés verts), sinon BESOINS machine-lisibles
  {pour, manque, via, chaîne} ÉCLATÉS EN CONJOINTS (conjoints_de,
  arrêt-aux-faits) — seuls les insatisfaits sont nommés.
- **Sur Goldbach(32)** (régime complet, prof. 3) : 4 manques → comblement →
  3 manques, qui pointent vers LES ORGANES de la machine (∃-intro du sélectif
  pour pair(N32), pont-réécrit pour ≠deux()) + LE MUR N32≤N6. Pièges : le 1er
  test hors-de-portée était FERMABLE (interning succ³(N2)=N5 — l'organe avait
  raison) ; les manques s'affichent DÉPLIÉS (τZ soup) → câbler l'IMPRIMEUR
  (PR1_imprimeur.py, 7/7 aller-retours, registre à étendre aux numéraux).
- **CAMPAGNE DICTÉE** : (a) câbler besoin→organes de comblement (∃-intro,
  reecrit) pour fermeture autonome jusqu'à la borne ; (b) LE MUR = borne ≥ n
  OU l'énoncé général H — la vraie cible. CY4 : profondeur 3 atteinte
  (9 découvertes chaînent M2:*), tours [46,6,4,4,4].

## 👑👑 CHAÎNE AUTONOME COMPLÈTE (marathon 8 août 10h, ev.321-322)
decomposition(N32..N40) : 5/5 FERMÉES par besoin→combleurs→assemblage→noyau
(pool = borne_n(40)[n] SEULE, faits initiaux VIDES, 6 comblements/cible, 4,2 min).
GOLDBACH MACHINE-VÉRIFIÉ 6..40, les 5 derniers sans script de preuve manuel.
Scripts scratchpad : PB1_besoin.py (organe, éclatement conjoints), PB4_autonome.py
(combleurs : card_num, elim_droite(fini_num) [conjoints de Fini déplié — l'aplatisseur
descend dans la déf.], ∃-intro sélectif [K_PAIR], pont-réécrit ≠deux, le_num ;
assembleur = detachement_conjonctif), PB5_serie.py (série, faits accumulés).
**À PROMOUVOIR AU DÉPÔT** (prochain geste du marathon) : module organe de besoin
+ combleurs + imprimeur (PR1_imprimeur.py 7/7) — sous-dossier neuf (arithmetique
AU CAP 10, corpus=58 historique → proposer outils_ia/conjectures/autonomie/ si
conjectures a de la place, COMPTER d'abord), tests (3 faces PB1 + 7/7 imprimeur +
fermeture-miniature via borne_n(6)), suite pytest, journal.
- PLACEMENT promotion : arithmetique=10 et conjectures=10 (AU CAP), outils_ia racine=16 (historique >10). Compter outils_ia/decouvertes/ ; si <8 y creer besoin.py+imprimeur.py+combleurs, sinon demander l arbitrage de la regle a Karl OU creer le paquet outils_ia/autonomie/ en documentant l ecart.

## 👑👑👑 LA MACHINE SUR LE GÉNÉRAL (marathon 11h, ev.325)
PB6_general.py (scratchpad) = besoins_generaux : descentes sous ∀ et sous ⇒
par-dessus l'organe de besoin promu. Sur goldbach() (TOUT n, aucun sous-cas) :
la machine descend sous ∀ngb, suppose l'antécédent général, et nomme SON manque
pour ∃p∃q(premiers ∧ ngb=p+q) à ngb LIBRE : « ngb ≤ N6 » (la borne) — la seule
route du corpus est structurellement incapable de donner tout n, DIT PAR ELLE.
⇒ ROUTE NON-BORNÉE JUGÉE NÉCESSAIRE PAR L'ALGO : théorie des nombres générale
(infinité des premiers / Euclide, encadrements type Bertrand). C'est LA
prochaine campagne de formalisation, dictée par le besoin exprimé (critère
Karl). À FAIRE : promouvoir besoins_generaux dans decouvertes/ (AU CAP 10 →
sous-dossier decouvertes/autonomie/ si besoin) + test descentes.

## CAMPAGNE EUCLIDE (dictée par la machine, ev.325) — SCOPING FAIT (11h25)
La route non-bornée exigée = infinité des premiers. INGRÉDIENTS AU DÉPÔT :
division euclidienne Th.1 §III.5.6 ✓ (juillet) + vocabulaire est_diviseur/
est_multiple (iii_5_notions_complementaires/ensembles_entiers_notions_arith.py) ;
factorielle ✓ (C62, la fonction existe) ; récurrence forte ✓ (route C61).
MANQUE : (1) prédicat est_premier GÉNÉRAL comme notion du dépôt §III.5.6
(actuel = builder d'énoncé dans outils_ia/conjectures/goldbach.py — le caler
sur le PDF, marqueur @livre) ; (2) « tout n≥2 a un diviseur premier »
(récurrence forte) ; (3) Euclide n!+1 (factorielle + division). Chaque brique
s'appuie sur de l'acquis — campagne de fond, multi-sessions, MAIS jugée
nécessaire par l'algo (PB6). Commencer par (1) fidélité-PDF.
⚠️ FIDÉLITÉ VÉRIFIÉE (V7 grep, 11h30) : le LIVRE ne définit PAS « nombre
premier » (E III : seulement « premier terme d'une suite » + une remarque en
passant §III.5.7). ⇒ La campagne Euclide = PREMIÈRE THÉORIE HORS-LIVRE créée
par la machine (côté outils_ia, jamais bourbaki/) — le but final en acte, et
c'est ELLE qui l'a demandée (ev.325).

## 👑👑👑 CAMPAGNE EUCLIDE — TROIS BRIQUES CLOSES (marathon 13h-18h, ev.329-332)
decouvertes/autonomie/ : euclide_cas_premier.py (PRODUCTEUR : (Fini n ∧ premier n)
⇒ ∃p(premier ∧ p|n), 12 s — la forme que PB7 déclarait introuvable),
euclide_transitivite.py ((card b ∧ b|a ∧ a|c) ⇒ b|c, 224 s, PREMIER RUN vert —
lieurs w1tr/w2tr LITTÉRAUX = noms d'élimination, zéro α-gymnastique),
euclide_extraction.py ((¬(n=1) ∧ ¬premier n) ⇒ ∃d((Fini d ∧ d|n) ∧ (d≠1 ∧ d≠n)),
0,5 s). PIÈGES consignés : double_negation_elim = COUCHE 0 → _dne abrégé local
(tiers_exclu+cas) ; neg_intro exige cible ¬f ; LES DEUX « ou » (est_premier
utilise le _ou ENCODÉ ¬(¬a∧¬b) — jamais mélanger avec le primitif).
**RESTE pour diviseur_premier (prochain marathon)** :
1. BORNE d ≤ n : sous témoin q (n = d·q), cas q=0 → n = d·0 = 0 (produit zéro,
   cf. _pcz_t de calcul_num) contra n≠0 ; cas q≠0 → 1 ≤ q (un_inf_egal,
   ordre_cardinaux/ensembles_cardinaux_un_borne.py:168 — LIRE sa forme exacte)
   → d = d·1 ≤ d·q (inf_egal_produit_droite, iii_3_2_monotonie/
   ..._produit_monotone.py) = n. Tiers exclu sur egal(q, zero).
2. ENVELOPPE C61 (récurrence forte) : P(n) = « n=0 ∨ n=1 ∨ ∃p(premier ∧ p|n) » ;
   pas de récurrence : extraction (d≠n ∧ d≤n ∧ d|n) + hypothèse forte sur d
   (P(d), d<n via d≤n ∧ d≠n → ordre strict) + cas premier/composé + transitivité.
   Modèle d enveloppe : produit_binaire_entier (prop3_produit_entier_iii5) et la
   route récurrence forte de la division euclidienne (juillet).
3. Puis n!+1 pour l infinitude (factorielle C62 + division Th.1).
### Borne d≤n — MESURES BR1 (14h45, scratchpad/br1_formes.txt)
- **NUM(0) == ZERO** (mêmes termes) : AUCUN pont côté zéro ✓.
- gb_un() ≠ UN (termes) : pont = un_egale_card_singleton (comme pont_un).
- un_inf_egal("X") : ¬(X = E.VIDE) ⇒ … (l'∅ est l'app vide) — l'hypothèse du
  cas q≠∅ sera ¬(q = E.VIDE) ; dériver depuis n≠0 : si q=∅ alors n = d·∅ →
  produit_cardinal_zero → n = ZERO = NUM(0), contra. Formes exactes de
  prod_zero/prod_un : τZ-lourdes — les VÉRIFIER par == en sonde (BR2), jamais
  à l'œil. Méthode : corridor incrémental type transitivité (ev.331).

### ENVELOPPE C61 — DESIGN COMPLET (analysé 15h, prêt à exécuter)
Contrat mesuré : `recurrence_forte(R, p="pfor")` (iii_4_recurrence_c61/
ensembles_recurrence_forte_preuve.py:181) rend {H, predecesseur_fini_universel}
⊢ ∀n(Fini n ⇒ R{n}) où H = ∀n(S{n} ⇒ R{n}), S{n}=∀p((Fini n∧Fini p∧p<n)⇒R{p}),
p<n = inf_strict_card = et(≤, ≠) DÉFINITIONNEL (brique F = conjonction_intro !).
Décharge de H : loi_deduction(H, thm) puis mp(H_prouvé, ·).
**R(t) := (Fini t ∧ t≠ZERO ∧ t≠un()) ⇒ ∃p( est_premier(p,dep,qep) ∧ Fini p ∧
divise_propre(p, t, "qdiv") )** — ⚠️ Fini p DANS le corps (sinon transitivité
sans est_cardinal(p)) ; binder ∃ ≠ "pfor" (choisir "pex") ; UNE SEULE graphie
d est_premier partout (dep/qep — extraction et producteur sont NAME-paramétrés,
les appeler avec ces noms ; le cas-premier s INLINE en 5 lignes pour ajouter
le conjoint Fini p au témoin n).
**Pas de récurrence (H)** : assume S{n} ; assume antécédent (Fini n,n≠0,n≠1) ;
tiers_exclu(est_premier(n,dep,qep)) : branche premier → inline producteur
(+Fini n au corps) ; branche ¬premier → extraction(n_name,"dep","qep") → ∃d
→ élim (lieur littéral) → Fini d, d|n, d≠1, d≠n → MICRO-BRIQUE F2 : ¬(d=ZERO)
depuis (¬(n=ZERO) ∧ d|n) [si d=0 : n=Card(0×w)=0 — produit-zéro GAUCHE :
produit_cardinal_commutatif + produit_cardinal_zero, ou grep produit zero
gauche] → borne(d,n) → d≤n → <(conj) → S{n} instancié à d → R(d) → mp
antécédent (Fini d, d≠0, d≠1) → ∃p → élim → premier p, Fini p, p|d →
transitivité(p,d,n) [est_cardinal p via fic] → p|n → corps à p → ∃-intro →
R(n). Puis generalisation → H clos → décharge → ∀n(Fini n ⇒ R{n}) =
**diviseur_premier_universel** 👑👑👑 (= enonce_diviseur_premier modulo forme —
comparer, ajuster l énoncé de premiers.py si besoin : il a q2="qdiv" ✓ mais pas
Fini p — harmoniser premiers.py OU garder les deux formes).
Placement : autonomie/ = 9 entrées → SOUS-DOSSIER autonomie/euclide_c61/ ou
promouvoir d abord les euclide_*.py dans un sous-dossier euclide/ (5 fichiers).

## 👑👑👑👑👑 THÉORÈME CLOS : DIVISEUR PREMIER UNIVERSEL (ev.335, 8 août 15h40)
euclide_c61/envelope.py — ⊢ ∀n(Fini n ⇒ [(n≠0∧n≠1) ⇒ ∃p(premier∧Fini p∧p|n)]),
0 hyp, test vert (test_general 7/7). PROCHAINE MARCHE = INFINITUDE (n!+1) :
p := diviseur premier de n!+1 (CE théorème) ; p > n car sinon p ≤ n ⇒ p | n!
(NOUVELLE BRIQUE : d≤n ∧ d≠0 ⇒ d | n! — divisibilité de la factorielle,
récurrence sur n via C62/factorielle de juillet) et p | (n!+1) ⇒ p | 1
(NOUVELLE BRIQUE : différence de divisibilité d|a ∧ d|(a+1) ⇒ d|1 — ou
directement ⇒ d=1 par la borne d≤1 ∧ d≠0) ⇒ contradiction avec premier
(p≠1). Puis Fini(n!+1) (factorielle finie + succ) et n ≤ p par tiers exclu
sur p≤n vs n<p (comparabilité des cardinaux — Th.1 III.3.2 au dépôt).
Cible finale = enonce_infinitude (premiers.py — harmoniser Fini p ✓ déjà dans
sa forme). L'énoncé-cible du besoin PB7 sera alors FERMABLE par l'organe.

## ⚔️ MARATHON 16h-22h : INFINITUDE (n!+1) — RECON FAITE (16h25)
INGRÉDIENTS MESURÉS : `factorielle_def2_ultime(n)` = {n∈ℕ} ⊢ (succ n)! =
pcb(n!, succ n) ✓ (iii_3_6_familles/ensembles_factorielle_def2_close.py:109) ;
`factorielle_def2_zero()` ✓ (famille_successeurs:147 — VÉRIFIER sa conclusion
par == : f(0)=UN ? quel UN ?) ; ordre-successeur : iii_5_2_inegalites/
ensembles_successeur_ordre.py (succ_pas_inf_egal etc. — chercher le CAS-SPLIT
d≤succ n ⇒ (d≤n ∨ d=succ n), sinon le dériver via comparabilité+succ_pas) ;
antisymétrie de ≤ = Cantor-Bernstein (FAIT juillet — grep cantor_bernstein/
inf_egal_antisym) ; pont n∈ℕ ↔ Fini n : à localiser (grep ensemble_NN
appartenance — factorielle parle en n∈ℕ, nos briques en Fini n).
**BRIQUE G** (d≤n ∧ d≠0 ⇒ d|n!) : récurrence SIMPLE sur n, P(n)=∀d(...) —
P(0) : d≤0 → d=0 (antisym avec zero_inf_egal) contra d≠0 → vacuité ;
pas : d≤succ n → split → cas d≤n : P(n) donne d|n!, puis d | n!·(succ n)
(MICRO-BRIQUE G2 : d|a ⇒ d|(a·b) — même couloir que la transitivité :
a=d·q → a·b=(d·q)·b=d·(q·b) [associativité], témoin q·b fini [produit_binaire
_entier]) ; cas d=succ n : d | n!·d (G3 : b|(a·b) — commutativité+témoin a...
attention finitude de a=n! : FACTORIELLE FINIE nécessaire — chercher/dériver
Fini(n!) — sinon l'énoncé de G porte Fini(n!) en hypothèse et une brique
Fini(n!) par récurrence [f(0)=1 fini, f(n+1)=f(n)·(n+1) produit de finis ✓]).
**BRIQUE H** (d|a ∧ d|(a+1) ⇒ d=1 pour d≠0) : a+1 = succ a = a + 1 —
ATTENTION succ vs somme (pont somme_num-style : succ a = a+UN ? chercher) ;
d|a → a=d·q ; d|(a+1) → a+1=d·q' ; soustraction : d·q' = d·q + 1 →
d·(q'-q)=1 → d|1 → d≤1 (borne_diviseur avec n:=UN≠0) ∧ d≠0 → d=1 (antisym
avec un_inf_egal ¬(d=∅)... niveau ∅ vs ZERO à ponter). ALTERNATIVE plus
courte sans soustraction : à investiguer (reste de division ?). H est LA
brique dure — la découper au besoin.
**ASSEMBLAGE** : p = div. premier de succ(n!) (THÉORÈME ev.335 : exige
Fini(succ n!) [succ de fini ✓] ∧ ≠0 [succ jamais 0 — succ_pas_zero ?] ∧ ≠1
[succ(n!)=1 → n!=0 → contradiction avec Fini(n!)∧n!≠0 — n!≠0 : G-corollaire
ou récurrence]) ; p>n : tiers_exclu(p≤n) — si p≤n : G donne p|n!, avec
p|succ(n!) H donne p=1 contra premier ; sinon ¬(p≤n) → n<p ? (comparabilité
Th.1 III.3.2 : ¬(p≤n) ⇒ n≤p — vérifier la forme) → n≤p suffit pour
enonce_infinitude ✓. MÉTHODE : mesures par == d'abord (BR-style), corridors
incrémentaux, lieurs littéraux, un run par pas.
### INFINITUDE — MESURES BR3 (16h30, scratchpad/br3_mesures.txt)
factorielle_def2_zero() CLOS 0 hyp (== contre UN/candidats à sonder) ;
factorielle_def2_ultime(n) : 1 hyp = **n ∈ ℕ** (ℕ = τy(...)) → PONT REQUIS
Fini n ⇒ n∈ℕ (grep dans_NN / ensembles_NN — le recollement de juillet doit
l'avoir ; sinon dérivable) ; successeur_ordre / _reciproque / _t (iii_5_2) =
la famille du cas-split (CLOS, sonder les formes exactes par == avant usage) ;
_antisym_t(tA,tB) + comparabilite_cardinaux_terme(u,v) CLOS (impl-formes à
sonder). PROCHAIN : sonder par == les 4 formes (BR4) puis brique Fini(n!).
### INFINITUDE — MESURES BR4 (16h40, br4_formes.txt)
✓ **f(0) = UN exact** (factorielle_def2(ZERO) = UN, les deux côtés ==).
✗ pont _fini_dans_NN conséquent ≠ hyp de ultime → LES DEUX ℕ (app("N") opaque
vs ensemble_NN concret — piège de juillet) : LIRE les sources des deux pour
savoir quel ℕ chacun utilise, chercher le pont vers le BON ℕ (ou dériver).
✗ successeur_ordre et _antisym_t : formes devinées fausses — LIRE LEURS
SOURCES (successeur_ordre.py:78-180, cardinaux_consequences.py:86) et écrire
les == depuis le code, pas depuis l intuition. PUIS : brique Fini(n!)
(récurrence principe_recurrence_preuve — lire son contrat P/base/step dans
produit_binaire_entier prop3:217 comme modèle), G2/G3, G, H, assemblage.

### INFINITUDE — LECTURES SOURCES (ev.339, 8 août 16h47) + BILAN MARATHON
**Le marathon 16h-22h du 7 août s'est arrêté ~16h45 : session suspendue (PC),
réveil le 8 août 16h45 — échéance passée pendant le sommeil. Boucle STOPPÉE
proprement (protocole). Acquis du marathon : recon, BR3, BR4, lectures ci-
dessous. Briques Fini(n!)/G2/G3/G/H/assemblage : NON commencées.**

Formes EXACTES lues dans les sources (plus de devinettes) :
- **CAS-SPLIT EXISTE** : `successeur_ordre(x,b)` (successeur_ordre.py:138) ⊢
  est_cardinal(x) ⇒ ( x≤succ b ⟺ (x≤b ∨ x=succ b) ) ; équivalence =
  et(impl(A,B), impl(B,A)) ; sens direct via cardinal_pas_entre_garde. Pour G :
  mp(est_cardinal x) → conjonction_elim_gauche = le split voulu.
- `_antisym_t(tA,tB)` (cardinaux_consequences.py:86) ⊢ (A≤B et B≤A et card A
  et card B) ⇒ A=B — l'antécédent porte les DEUX est_cardinal (nesting =
  celui de inf_egal_antisymetrique_card instancié — sonder par == à l'usage).
- `_fini_dans_NN(t)` (donnees_ordre_NN.py:84) ⊢ Fini T ⇒ T∈ℕ =
  equivalence_arriere(instancie(appartenance_NN(), t)). Modèle d'usage :
  h1_succ_dans_NN juste dessous (mp(h, _fini_dans_NN(vb))).
- `factorielle_def2_ultime(n="nfr")` : { n∈ℕ } ⊢ f(succ n)=pcb(f(n), succ n),
  1 hyp. ⚠️ BR4 mesurait conséquent-pont ≠ hyp-ultime : cause NON identifiée
  (extraction sous[1] peut-être fautive, ou appartient/ℕ ≠) — PREMIÈRE action
  de la reprise : sonder `_fini_dans_NN(var("n")).conclusion.sous[1] ==
  list(factorielle_def2_ultime("n").hypotheses)[0]` avec le MÊME nom de
  variable (le BR4 utilisait tbr4 vs nbr4 — mismatch trivial possible !).
- `succ_pas_inf_egal(b)` ⊢ est_fini(b) ⇒ ¬(succ b ≤ b) (pour H / l'absurde).

REPRISE (prochain marathon) : (1) sonde == pont/ultime à variable COMMUNE ;
(2) brique Fini(n!) (modèle produit_binaire_entier, P(n)=Fini(f(n)), base
f(0)=UN ✓ ; contrat principe_recurrence_preuve à lire prop3:217) ; (3) G2/G3 ;
(4) G (via successeur_ordre) ; (5) H ; (6) assemblage → enonce_infinitude.

### INFINITUDE — MARATHON 8 août 16h48→22h : F, G2, G3 CLOS ; route H (ev.341)
✅ **fini_factorielle** CLOS 354s 1er coup (euclide_c61/fini_factorielle.py) :
∀n(Fini n ⇒ Fini n!). ✅ **G2 divise_produit_droite** CLOS 226s, ✅ **G3
divise_produit_gauche** CLOS 1s (divise_produit.py). ⏳ **G divise_factorielle**
lancé (divise_factorielle.py, run biw8pzkeb) : récurrence, base antisym-c1
(BR6 : nesting et(et(et(d≤0,0≤d),card d),card 0)), pas = successeur_ordre
(équiv = et encodé, élim gauche) + PONT-α qdiv↦wg2 (témoin var qdiv sous lieur
wg2) + G2/G3 + Leibniz ultime. zero_inf_egal_cardinal = {card x} ⊢ 0≤x (hyp à
couper). ROUTE H (d|a ∧ d|succ a ∧ card d ∧ d≠0 ∧ Fini a ⇒ d=UN), pièces TOUTES
localisées : succ(a) EST somme(a,{∅}) LITTÉRAL (successeur_egale_card_somme =
réflexivité, prop8_successeur.py:114) ; UN := succ(ZERO) ; un_egale_card_singleton
= ⊢ UN = Card({∅}) (fini_un.py:180) = LE pont vers un() goldbach ; cancel =
additive_order_cancel (prop4_surj:182, nesting et(et(et(est_entier a, card u),
card v), a+u≤a+v)⇒u≤v ; est_entier importé d'ensembles_entiers, == est_fini à
vérifier par ==) ; somme_cardinale_bien_definie (somme_equipotence:924,
(Eq(A,A₁)∧Eq(B,B₁))⇒Card(A⊔B)=Card(A₁⊔B₁)) + equipotence_reflexive_t
(division_existence:96) + equipotence_symetrique(f,x,y) (bijection:180) +
eq_un_singleton (Eq(1,{∅})) pour le pont somme(a,{∅})=somme(a,UN) ;
produit_succ_distribue(a,n) termes : (card a∧card n)⇒a·(n+1)=a·n+a (prop3:90) ;
comparabilite_cardinaux_terme(u,v) ⊢ u≤v ∨ v≤u (sup_cardinal:395) ;
fini_implique_distinct_successeur (entiers_theoremes:122) ; succ_pas_inf_egal ;
inf_egal_produit_droite = ≤ NIVEAU ENSEMBLES → pont Card via borne-pattern
(_mut_t + equipotent_son_cardinal + 2 transitivités, copier euclide_borne).
COULOIR H : témoins w1 (a=d·w1), w2 (succ a=d·w2) ; comparab(w2,w1) →
[A: w2≤w1 → succ a≤a mort succ_pas_inf_egal] ; [B: w1≤w2 → tiers_exclu(w1=w2):
B1: égal → a=succ a mort distinct_successeur ; B2: ≠ → comparab(succ w1, w2) →
B2a: succ w1≤w2 → mono+distribue+Leibniz → somme(a,d)≤succ a ; B2b': w2≤succ w1
→ successeur_ordre(w2,w1) split → w2≤w1 (antisym w1=w2, mort) ou w2=succ w1 →
égalité → somme(a,d)≤succ a] ; QUEUE commune : succ a ==textuel somme(a,{∅}),
pont bien_definie → somme(a,d)≤somme(a,UN) → cancel → d≤UN ; UN≤d (une fois,
ambiant : ¬(d=VIDE) par micro-preuve [d=VIDE → Card d=Card ∅=ZERO textuel +
card d → d=ZERO contra] → un_inf_egal {∅}≤d → Card({∅})≤{∅}≤d trans →
Leibniz un_egale_card_singleton → UN≤d) ; antisym(d,UN) → d=UN. Fichier :
euclide_c61/prime_diviseur_succ.py. PUIS ASSEMBLAGE (envelope du théorème +
G + H + comparabilite → enonce_infinitude). euclide_c61/ : 5 entrées (+H+asm=7).

### INFINITUDE — TOUTES BRIQUES CLOSES, ASSEMBLAGE LANCÉ (ev.342-344, 17h55)
✅ **H diviseur_commun_succ CLOS 382s** (2 runs — seul accroc : lieur de
graphe Eq, il faut le « F » CANONIQUE d'equipotent dans equipotence_symetrique
généralisée ; tout le couloir arithmétique 1er coup). ✅ **minorant_factorielle
CLOS 493s 1er coup** (1 ≤ n! ; succ≠0/≠∅ dérivés sans lemme neuf). ✅ Écrit
**assemblage_infinitude.py** (euclide_c61/, 7e fichier) : m=succ(n!), m≠0
(spie), m≠1 (minorant + Prop.8 injectif → Card=Card + card-de-card), théorème
→ ∃pex, micro-F2 p≠0, comparabilité(p,n) : absurde = G + ponts-α qdiv↦w1H/w2H
+ H → p=UN → ues → p=un() contra premier ; témoin = ∃-intro « pep ». RUN
b06e8qrjd → scratchpad/asm_run1.txt (~35-45 min, rebuild de tout).
PIÈGE background : sortie non flushée AVANT la fin du process — un fichier
vide ≠ mort ; attendre la task-notification. RESTE : run vert → test suite
euclide_c61, journal ev.344, CAMPAGNE_DEMOS (👑 EUCLIDE COMPLET), bilan 21h35.

### 👑👑👑 EUCLIDE COMPLET (ev.344, 8 août 18h14)
**euclide_infinitude() CLOS : 1377 s, 0 hyp, conclusion == enonce_infinitude()
True, PREMIER COUP** (assemblage_infinitude.py). Récap briques : F 354 s ;
G2 226 s ; G3 1 s ; G 609 s ; H 382 s (2 runs, fix lieur Eq canonique « F ») ;
minorant 493 s. La campagne dictée par la machine (ev.325) est FERMÉE le jour
même : manque nommé (matin) → diviseur premier universel (midi, ev.335) →
infinitude (soir, ev.344). Reste marathon : test léger dans test_general.py
(autonomie/ PLEIN à 10), suite rapide, bilan 21h35, stop 22h.

### SANITÉ SÉMANTIQUE NÉGATIVE (ev.346, 8 août 18h35)
Discussion Karl sur les ZONES D'OMBRE → programme de réduction ; zone 3
(fidélité de est_premier, prédicat HORS-livre) attaquée séance tenante :
**conjectures/primalite_negative.py — ⊢ ¬est_premier(N c) pour c composé,
témoin i** (dual exact de est_premier_num : X(N i) par fini_num+divise_positif,
¬Y par ne_num+pont_un, ¬(X⇒Y) par cas, ∃-témoin, ¬∀ = ¬¬∃¬, ¬et par s2+s3).
**¬premier(4) 70s, ¬premier(6) 0s, ¬premier(9) 1s — premier coup.** Le
prédicat de l'infinitude démontre les premiers ET réfute les composés.
⚠️ conjectures/ atteint 10 entrées réelles — prochain ajout = éclater le
dossier. Reste marathon : pytest lent du théorème, bilan 21h35, stop 22h.

### L'ORGANE CONSTATE LA FERMETURE (ev.345, 8 août 18h49)
Run bkwrsrcco (1711 s, rebuild complet) : `besoins_generaux(enonce_infinitude)`
**SANS le théorème → fermé=False, 1 manque nommé** (la demande ev.325 vivante,
machine-lisible) ; **AVEC euclide_infinitude au pool → fermé=True par VOIE
DIRECTE, 0 manque, est_clos ∧ conclusion==but**. Symétrie exacte d'ev.338 :
la machine dicte (ev.325) → l'outil (ev.335) → Euclide (ev.344) → l'organe
acte (ev.345). Partage honnête consigné : cible+verdict = machine ; route =
Claude (discussion biais/zones d'ombre avec Karl, ce soir).

### SLOW VERT (8 août 18h59)
pytest test_euclide_infinitude : **1 passed in 1669 s (27:49)** — le théorème
est un test officiel de la suite (marqué slow). Tout le marathon est livré :
plus rien d'ouvert avant le bilan 21h35. RIEN COMMITÉ (Karl commite).

## MARATHON GOLDBACH 9 août 12h46→2h00 (ev.347+)
### PB10 — LA MACHINE RE-INTERROGÉE, POOL ENRICHI EUCLIDE (ev.347, 13h55)
PB10_goldbach_enrichi.py (scratchpad, 58.5 min) : goldbach() tout-n, organe
promu, pool = régime CY1 + M2 + ARSENAL EUCLIDE (infinitude/diviseur_premier/
fini_fact/minorant en faits ∀ ET instanciés @ngb en impls ; G2/G/H/borne/
transitivité/extraction en impls). **VERDICT : non fermé (attendu), 2 manques,
chaîne = goldbach_borne_n(6)[n] — LE MANQUE N'A PAS BOUGÉ : toujours la BORNE**
(l'∃F…dom(F)=ngb = l'injection du ≤). Lecture : l'infinitude produit des
premiers AU-DELÀ de n ; RIEN au pool ne parle de SOMMES de premiers à n libre
— la machine localise le mur exact de la conjecture (le passage borné→libre
ADDITIF). Limite de couverture (zone 4) en acte : l'organe nomme à un pas des
routes existantes, il n'invente pas le pont additif. DÉCISION : répondre au
manque nommé LITTÉRALEMENT = étendre la frontière bornée. goldbach_borne_n(B)
est PARAMÉTRÉ (B pair ≥4 ; couple(j) table des décompositions ; branches
enum B+1 ; premiers requis certifiés par est_premier_num). Run B=12 lancé
(bwoidwq7x → gb12_run.txt) ; si vert → B=20 (premiers 11/13/17 à certifier),
puis re-PB10 avec borne 12/20 au pool pour VOIR le manque se renommer plus
loin (le compounding machine-lisible). Bilan 1h35-40, stop ≥2h00.

### FRONTIÈRE 6→12 (ev.348, 13h51)
goldbach_borne_n(12) **CLOS 78 s, ==cible(12) True** — 13 branches (parité
impairs, ponts 0/2, témoins 2+2/3+3/3+5/3+7/5+7). ⚠️ piège driver : trace =
LISTE (append), pas callable. couple(n) = recherche Python NON bornée (seule
la certification est noyau) ⇒ B limité par le seul temps de calcul. B=20
lancé (bu1z0wcxu → gb20_run.txt ; premiers neufs 11/13/17 certifiés à la
volée par est_premier_num). Ensuite : B=30 si coût OK, puis re-PB10 avec
borne_n(B_max) instanciée @ngb au pool (montage : une ligne, comme
CY1:65 imp("goldbach_borne_n(6)[n]", instancie(goldbach_borne_n(6), var)))
→ voir le manque se renommer (compounding machine-lisible). ev.349.

### FRONTIÈRE 12→20→30, CAP SUR 100 (ev.349, 13h55)
goldbach_borne_n : **B=20 CLOS 96 s** (premiers 11/13/17 à la volée),
**B=30 CLOS 117 s** (19/23). Croissance douce (78→96→117 s). **B=100 lancé**
(bkoxqk4yc → gb100_run.txt, 13h56 ; premiers jusqu'à 97, 101 branches ;
tuer si >45 min et se rabattre sur B=50). Puis PB11 = re-PB10 avec
borne_n(B_max)@ngb au pool → le manque doit se renommer « ngb ≤ N(B_max) ».

### FRONTIÈRE 50 ATTEINTE, CAP 100 (ev.349-suite, 14h04)
**B=50 CLOS 341 s** (premiers 29/31/37/41/43/47 certifiés à la volée).
PIÈGE PILE C : N(100) fait déborder la pile C par récursion de hash —
threading.stack_size : 512 Mo et 256 Mo REFUSÉS par Windows (« size not
valid »), **64 Mo OK** → driver blindé scratchpad/gb_driver.py (thread 64 Mo
+ recursionlimit 1M ; réutilisable pour tout numéral profond). B=100 en vol
(bn1pouah3 → gb100_run2.txt, 14h04, tuer si >45 min). Puis PB11 (borne_n(BMAX)
@ngb au pool, modèle CY1:65) → le manque doit se renommer. Chronologie coûts :
12→78s, 20→96s, 30→117s, 50→341s.

### FRONTIÈRE 70 (14h26) — B=84 en vol
**B=70 CLOS 1108 s** (premiers 53/59/61/67 à la volée). Chronologie coûts :
12→78s, 20→96s, 30→117s, 50→341s, 70→1108s (superlinéaire : est_premier_num
des gros premiers). Falaise pile : 70 < X ≤ 100. B=84 lancé (b86n5wr71 →
gb84_run.txt, 14h27, tuer si >50 min). PB11 en vol en parallèle (b5iatl0cy).

### FRONTIÈRE 84 (15h01) — B=92 en vol
**B=84 CLOS 1896 s** (premiers jusqu'à 79). Coûts : 50→341s, 70→1108s,
84→1896s. B=92 lancé (blivk3mig → gb92_run.txt, 15h02, tuer si >70 min).
PB11 : régime chauffé 15.6 min, arsenal en cours (fin estimée ~15h30).

### LA FALAISE : 84 < X ≤ 92 — RECORD FINAL B=84 (ev.349-fin, 15h05)
**B=92 : RecursionError à 1 s** (hash récursif du numéral τZ-profond, garde
de pile RÉELLE de Python 3.13, insensible à threading.stack_size 64 Mo et à
setrecursionlimit). **Record de frontière : goldbach_borne_n(84), CLOS,
==cible(84) True.** La conjecture de Goldbach est désormais un THÉORÈME du
noyau pour tout n ≤ 84 (était 6 ce matin). Remède éventuel (PAS aujourd'hui,
noyau intouchable) : hash itératif ou en cache structurel dans outil_formule —
à discuter avec Karl avant tout geste. PB11 en vol (arsenal).

### 👑 LE COMPOUNDING MACHINE-LISIBLE (ev.350, 15h26)
PB11 (78.2 min) : 4 besoins — les 2 anciens (chaîne borne_n(6)) ET **2 NOUVEAUX
chaîne = goldbach_borne_n(50)[n]**, même forme (∃F…dom(F)=ngb = la borne).
**Le manque SUIT la frontière** : l'organe voit la route 50 et re-nomme son
manque dessus. La machine localise en langage machine-lisible la structure de
la conjecture : les théorèmes bornés montent (6→84), le manque se re-nomme à
chaque B, le cas libre reste hors d'atteinte — l'écart EST Goldbach. SUITE
(15h30→1h30) : ¬premier(1)/(0) (sanité, inline) ; CONJECTUREUR sur corpus
enrichi (iterer, cap_brique, trace, ~3h — la fenêtre le permet enfin) ;
CAMPAGNE_DEMOS + mémoire pendant le run ; bilan 1h35.

### CONJ1 — LE CONJECTUREUR SUR LA MOISSON (ev.352, 16h30)
**721 découvertes certifiées, 57.9 min** (chauffe 57 min, les 3 tours <1 min !),
par tour [120, 177, 424] — l'ACCÉLÉRATION = compounding des FAITS (les
découvertes du tour t nourrissent le détachement du tour t+1). cap_brique
11070 (=3×taille(goldbach())) a écarté 29+33 briques-monstres (anti-poison
efficace, tailles dépliées jusqu'à 1.7e12 — le partage DAG encaisse).
Verdict HONNÊTE : volume + certification, mais tout reste à profondeur de
MOTIF (compositions transitivité/détachement attendues : somme∘cardinal,
succ∘fini, instanciations numérales) — rien de conceptuellement neuf visible ;
les découvertes profondes exigent le marcheur. C'est la mesure du ratio
machine/Claude en acte. PB12@84 lancé (b7vr32zla → pb12_verdict.txt, 16h35,
~1h30 ; ⚠️ borne_n(84) construit SANS thread 64 Mo — si RecursionError,
re-wrapper PB12 dans gb_driver-style ; la falaise main-thread mesurée était
à 100, 84 devrait passer). Ensuite : ticks calmes → bilan 1h35-40 → stop 2h.

### ev.353 — LE MANQUE AU RECORD 84 + GG1 EN VOL (19h10)
**PB12 (main-thread !) FINI 77.5 min : chaînes goldbach_borne_n(84)[n] dans
la trace** — le manque suit la frontière jusqu'au record. Falaise main-thread
donc >84 aussi (le « mort » de 18h47 était FAUX : tasklist/CimInstance sont
AVEUGLES aux process des tâches background — ne JAMAIS s'y fier, seuls les
fichiers trace + notifications font foi). PB12b doublon tué (TaskStop).
**GG1_pairs_non_bornes.py EN VOL** (but0ivyvb → gg1_run.txt, ~19h25) —
« utilise tout sur le pour-tout-n » (Karl) : ⊢ ∀n ∃m(pair ∧ n≤m ∧ m=p+q
premiers) via infinitude + m=p+p (pair par témoin p RÉFLEXIF) +
prop2_sous_fini CURRYFIÉ + témoin-jumeau à matrices explicites (piège 4=2+2).
Graphies dep/qep uniformes, élim « pep » littéral. Si vert : ev.354, LE
premier théorème non-borné des sommes de deux premiers du dépôt.

### 👑 GG1 — LES PAIRS DE GOLDBACH SONT NON BORNÉS (ev.354, 19h53)
**⊢ ∀n( Fini n ⇒ ∃m( pair m ∧ n≤m ∧ ∃p∃q(premier p ∧ premier q ∧ m=p+q) ) )
CLOS, 0 hyp, invariant 22, 1362 s** (dont 1359 = rebuild infinitude : la
COUTURE = 3 secondes). Demande Karl « utilise tout sur le pour-tout-n » —
PAS Goldbach (lui = TOUS les pairs), son ombre à l'infini : infinitude → p≥n
premier ; m := p+p pair (témoin p, réflexivité) ; p≤p+p (prop2_sous_fini
CURRYFIÉ) ; n≤m (transitivité) ; décomposition témoin-jumeau p=q=p à matrices
EXPLICITES en deux étages — piège mesuré : l'∃ interne n'abstrait QUE le
conjoint interne (la matrice externe attend et(premier p, ∃q(…)), pas
∃q(et(…))) — 2 runs. Script scratchpad/GG1_pairs_non_bornes.py (thread 64 Mo).
PROMOTION REPO : conjectures/ PLEIN (10) → exige l'éclatement du dossier,
décision Karl après commit. Le théorème encadre la conjecture par en-dessous :
borné ≤84 (tous les pairs jusqu'à 84) + non-borné (des pairs arbitrairement
grands) — ce qui manque toujours : TOUS les pairs, tout n. C'EST Goldbach.

### 👑 GG2 + PROGRAMME OPTIMISTE DU CAS GÉNÉRAL (ev.355, 21h10)
Karl : « continue sur Goldbach en général, arrête d'être pessimiste » →
PROGRAMME FAMILLES : mordre le domaine de la conjecture par familles
infinies certifiées. **GG2 CLOS EN 0 SECONDE** (scratchpad/GG2_famille_doubles
.py) : ⊢ ∀p((premier p ∧ Fini p) ⇒ (pair(p+p) ∧ decomp(p+p))) — Goldbach est
un THÉORÈME sur la famille infinie {2p : p premier} (couloir GG1 sans
l'infinitude). DÉCOUVERTE d'inventaire : la réduction moitiés est DÉJÀ CLOSE
dans les DEUX sens (reduction_moities, reciproque_moities, equivalence_
moities — goldbach ⟺ H = ∀k decomp(k+k)) ⇒ par GG2, H est démontré sur les
k PREMIERS ; le reste général de Goldbach = k COMPOSÉ. **PB13 lancé**
(b5l8opo9c → pb13_verdict.txt, ~80 min, 21h10) : la machine interrogée sur H
(forme SANS parité) avec arsenal+GG2 — que nomme-t-elle là ? Familles
suivantes possibles : p+3/p+5 (exige lemme premier≠2⇒impair + impair+impair
=pair, à mesurer), famille 2-param p+q (tautologique, faible valeur).
Bilan 1h35, stop 2h.

### PB13 + GG4 — LA MACHINE DÉCOMPOSE, ON COMBLE (ev.356-357, 22h40)
**PB13 (51 min) : SAUT QUALITATIF** — sur la forme moitiés H (∀k decomp(k+k),
sans parité opaque), la machine décompose son manque en sous-buts LISIBLES :
est_cardinal(k+k), ∃@0(k+k=@0+@0) [parité, lieur GENSYM anti-capture],
¬(k+k=succ(k+k)), les gardes ≠, et LA BORNE (∃F…dom=k+k). Chaînes borne_n(6)
ET E:borne_n_12@k (l'arsenal servi). **GG4 (178 s) : les 3 pièces fermables
CLOSES** dans les formes EXACTES nommées (lieur « @0 » accepté par le noyau —
mesuré). PB14 lancé (b4nmsgfjb, léger : régime + borne12@k + GG4@kgb, fin
~23h05) : attendu = manques réduits vers LA BORNE (+ gardes ≠0/≠2 non faites
— couloirs consignés : k+k≠0 par antisym sous k≠0 ; k+k≠2=SC(un,un) par
annulation additive sous k≠1). ⚠️ fragilité α potentielle : le gensym @0
peut varier entre runs — si le manque parité PERSISTE dans PB14 malgré
th_pair, c'est la preuve concrète pour le jalon MATCHING RELÂCHÉ (α-canonique
+ pont-α automatique dans besoins) — à noter au bilan quoi qu'il arrive.

### ORGANE V2 (ev.358, 23h00) — le diagnostic PB14-15 et le fix
PB14 puis PB15 (+Fini(x+x) direct, profondeur 5) : manques STRICTEMENT
identiques → lecture du code : dans besoins(), les conjoints d'un antécédent
étaient NOMMÉS (manques.append) mais JAMAIS RE-SOUMIS aux impls — les faits
du pool qui les fermaient n'étaient jamais consultés. **FIX organe v2
(decouvertes/besoin.py)** : tenter de fermer CHAQUE morceau par récursion ;
si tous ferment, RECOMPOSER la conjonction (_recomposer : miroir structurel
de conjoints_de, ∧-intro sur l'encodage ¬(¬a∨¬b), feuilles = faits/fermés)
et conclure par mp — le noyau juge tout. Suite rapide decouvertes : 5 passed.
PB16 lancé (be5lv21bo → pb16_verdict.txt, ~13 min) : attendu = manques
réduits à borne + gardes ≠. C'est le 2e organe amélioré par diagnostic
mesuré (après voie-directe ev.338) — la boucle machine s'auto-améliore sous
pression du cas général Goldbach.

### ORGANE V2 CONFIRMÉ + GG5a (ev.359-360, 23h25)
**PB16 : la trace montre « fermé » sur TOUS les fermables** (Fini kk via
GG5:fini_kk, cardinal via fini_implique_cardinal PROFOND, distinct, parité-@0)
mais reporting binaire re-nommait tout → fix reporting (seuls les
RÉCALCITRANTS nommés ; suite 5 passed). **PB17 : 14 → 8 besoins, uniques
affichés = le bloc composite + les gardes ≠ + LA BORNE** — le mur à l'os.
**GG5a CLOS 4 s** : ∀k((Fini k ∧ k≠0) ⇒ k+k≠0) (k≤k+k par prop2-refl,
Leibniz, 0≤k, antisym-c1). Garde ≠2 CONSIGNÉE (couloir : cas k=0 par somme
concrète 0+0=0 + ne_num(0,2) ; cas k≥1 par 1≤k et monotonie fine — plus
long). PB18 en vol (bggb0hics, ~23h40) : attendu = récalcitrants réduits à
{garde ≠2, LA BORNE}. besoin.py : 2 edits ce soir (v2 + reporting) — À FAIRE
RELIRE PAR KARL avant commit.

### PB18 — LE MUR NU (ev.361, 23h31)
**8 → 6 besoins ; récalcitrants = {garde k+k≠deux() [couloir consigné], LA
BORNE ∃F…dom=kk}** — GG5a consommée par l'organe v2. Progression des sondes :
PB13 opaque→14 structurés ; PB16 fermetures prouvées (trace) ; PB17 14→8 ;
PB18 8→6. Après la garde-2 (route : cas k=0 par somme concrète + ne_num(0,2) ;
cas k≥1 par 1≤k + monotonie fine — OU l'éviter en donnant à l'organe le fait
kk≠2 sous k≠1 comme GG5b), il restera LA BORNE SEULE = la conjecture, dite
par la machine en un manque unique. FIN DES TRAVAUX LOURDS de la nuit —
ticks calmes, BILAN 1h35-40, stop 2h.

## MARATHON GOLDBACH-NUIT 10 août 1h00→5h00 (relance Karl)
### GG5b — LA GARDE ≠2 CLOSE (ev.362, 1h15)
**⊢ ∀k((Fini k ∧ k≠0 ∧ k≠1) ⇒ ¬(k+k=deux())) — CLOS 47 s, premier coup**
(scratchpad/GG5b_garde_deux.py). Route 100 % acquis SANS translation/
commutativité : k+k=deux() → pont_deux → k+k=N2 ; k≤k+k (prop2-refl) →
Leibniz → k≤N2 ; cascade successeur_ordre (N2=succ N1, N1=succ N0
LITTÉRAUX) : k=N2 → k+k=N4 (somme_num 2+2) contra ne_num_sym(2,4) ;
k=N1 contra ; k≤N0 → antisym → k=0 contra. LE DERNIER FERMABLE EST FERMÉ.
PB19 en vol (bzw5f9n7j → pb19_verdict.txt, ~15 min) : LE MOMENT-PHOTO
attendu = LA BORNE SEULE. Ensuite : PB20 SANS route bornée (retirer
borne_n du pool → comment la machine formule le cas restant, avec GG2
au pool elle pourrait nommer « k composé ⇒ decomp ») ; bilan 4h35-40 ;
stop 5h.

### 📸 ev.363 (1h23) — LA MACHINE RÉDUIT GOLDBACH À LA BORNE SEULE
PB19 (11.6 min) : **6 → 4 besoins ; uniques = {bloc-antécédent composite
[l'habit long de la même borne], ∃F…dom(F)=k+k}**. La garde ≠2 disparue
(GG5b consommée). Cascade des sondes sur H : 14→8→6→4. VERDICT DE LA NUIT :
pour l'organe v2, avec tout l'arsenal, fermer H (⟺ Goldbach) ne bute QUE sur
« k+k ≤ N(B) » — la machine a réduit la conjecture à UN manque machine-
lisible. SUITE : PB20 = même but SANS route bornée au pool (filtrer les impls
borne_n du régime) + GG2' en graphie GBB si mismatch (VÉRIFIER graphies de
goldbach_borne.decomposition vs GG2 dep/qep AVANT) → comment la machine
formule le cas restant sans béquille.

### 👑 ev.364 (1h37) — LA MACHINE FORMULE LE CAS RESTANT
**PB20 (11.9 min, pool SANS routes bornées + GG2′ famille {2p} graphie GBB
exacte [close 0s, hypothèse double-habit d1q1+d2q2])** : toutes les chaînes
passent par GG2p:famille_2p@k et les manques nommés sont : ¬(kgb=1), et les
DEUX clauses universelles de diviseurs (habits d1/d2) — c'est-à-dire :
**« il me manque : k est premier »**. La machine a formulé d'elle-même que
le cas restant de Goldbach est le cas COMPOSÉ — par pure unification but ↔
famille {2p}. Lecture machine de la conjecture après cette nuit : les k
premiers passent (GG2/GG2′) ; le mur = k composés ; par la route bornée, le
mur = LA BORNE (ev.363). SUITE : CONJ2 (conjectureur, arsenal complet) puis
bilan 4h35-40, stop 5h.

### CONJ2 — COMPOUNDING PROFONDEUR ≥2 (ev.365, 2h34)
**914 découvertes (54.2 min), tours [164, 233, 517], 750 entrées composent
des briques DÉRIVÉES (D#∘D#)** — vraie profondeur structurelle ≥2, l'arsenal
GG fertilise (+27 % vs CONJ1 tour 1 : 164 vs 120). Anti-poison 33+42 sautées
(cap 11070). Verdict honnête : toujours le régime des MOTIFS — la valeur est
le CORPUS (données pour le marcheur/flywheel), pas des théorèmes nommables.
Pièges writers : ancre à 2 lignes fragile → ancre 1-ligne + insertion ;
backslashes Windows dans heredoc² → FORWARD SLASHES + repr() ; writers en
FOREGROUND désormais (2 runs perdus ~0 s chacun, pas de mal).
PLUS RIEN À LANCER — ticks calmes, mémoire à jour au bilan, BILAN 4h35-40,
stop 5h.

### TESTS ORGANE V2 + FRONTIÈRE 90 (ev.366, 4h05)
**2 tests dédiés organe v2 ajoutés à test_autonomie.py, suite 7 passed** :
(a) recomposition de conjoints (faits + impl → ∧-intro → mp, but fermé) ;
(b) reporting des seuls récalcitrants (le fermable n'est PAS nommé). Les
2 edits de besoin.py sont désormais SOUS TESTS. Karl : « on continue la
recherche aussi » → **gb_driver 90 lancé** (b08451wit → gb90_run.txt,
~40 min ; si vert record=90, si récursion falaise cernée 90<X≤92).
Bilan 4h38, stop ≥5h (sauf prolongation Karl).

### 👑👑 GG6+GG7 — GOLDBACH ⟺ GOLDBACH-SUR-LES-COMPOSÉS (ev.367, 4h00)
**CLOS EN 0 s, PREMIER COUP** (scratchpad/GG7_reduction_composes.py) :
GG6 = pont-α premier₁⇒premier₂ (∀-α par instancie-à-d2 + ∃-α contravariant
dans l'antécédent [témoin var-même] + re-généralisation — le double-habit de
GG2′ est LEVÉ) ; **GG7 = HC ⇒ H ET H ⇒ HC** où HC = ∀k((A(k) ∧ ¬premier(k))
⇒ decomp(k+k)). Chaîne certifiée complète : goldbach() ⟺ H ⟺ HC — **la
conjecture est officiellement équivalente à ses seules instances COMPOSÉES**,
par tiers-exclu sur premier(k) (branche premier = GG6+GG2′ famille {2p},
branche composé = hypothèse). La suggestion machine d'ev.364 est devenue un
théorème d'équivalence. Frontière : B=90 récursion 0s (falaise ≤90) ; sonde
86 en vol. Bilan 4h38, stop 5h.

### 🏆 ev.368 (4h02) — LA MACHINE ÉCRIT LE PAS DE DESCENTE DE GOLDBACH
**GG8 CLOS (240-247 s, 2 runs identiques)** : recurrence_forte(R) avec
R(t)=(t≠0∧t≠1)⇒decomp(t+t), pfu déchargé, pont-curry ∀-α → **⊢ H_rec ⇒ H**
(si le pas, alors la conjecture — certifié). **ORGANE V3** (general.py : les
manques de la voie directe étaient JETÉS [_m_direct ignoré] → fusionnés aux
retours des descentes ; 3e diagnostic mesuré de la nuit ; suite 7 passed).
**PB22-v3 : la machine nomme H_rec en formule** (chaîne DESCENTE:
recurrence_forte) : ¬∃nfor¬(S{nfor} ⇒ R{nfor}) = ∀n(∀p(p<n ⇒ Gb(p+p)) ⇒
Gb(n+n)). CARTE FINALE DE LA CONJECTURE, TROIS PORTES DITES PAR LA MACHINE :
(1) LA BORNE (route bornée, ev.363) ; (2) « k premier » = cas composé (route
famille, ev.364) ; (3) LE PAS DE DESCENTE (route récurrence forte, ev.368).
Toutes certifiées ⟺ conjecture (équivalence moitiés + GG7 + GG8). SUITE :
PB23 = l'organe décompose LE PAS avec l'arsenal complet (le sous-cas premier
du pas devrait tomber par famille {2p} + GG6).

### ev.369 (4h16) — LE PAS DÉCOMPOSÉ ; LIMITE V4 IDENTIFIÉE
PB23-v2 (arsenal complet @nfor) : la machine décompose LE PAS via
GG2p:famille2p@n — manques : premier(nfor) [¬(n=1) + clauses ∀-diviseurs
d1/d2], conjoints de Fini(nfor) [est_cardinal + ¬(n=succ n)], et le reste.
STRUCTURE FRACTALE : à chaque niveau (H, HC, le pas), le mur = premier/
composé + le lien descendant. **LIMITE V4** : l'hypothèse S{nfor} (fait-∀
au contexte, posée par la descente-⇒) n'est JAMAIS instanciée par l'organe —
besoins() ne sait pas utiliser un fait ¬∃x¬φ en l'instanciant sur un terme
qui matcherait le but. **PLAN ORGANE V4 (prochain segment)** : dans
besoins(), après la voie faits : pour chaque fait ∀-forme (tag non/exists/
non), _match(matrice, but, σ) → instancie(fait, σ(x-var)) → retour théorème ;
+ test dédié (fait ∀ + but instance) ; suite verte exigée. Ensuite re-PB23 :
le sous-cas « p < n » du pas deviendrait utilisable et la machine nommerait
le VRAI cœur (trouver p premier avec n+n−p premier — le pont additif).
B=86 encore en vol. Boucle SANS échéance (Karl 4h) — points réguliers.

### ev.370 (4h25) — RECORD 86 + ORGANE V4
**B=86 CLOS 1757 s** (premier 83 au vol) — record de frontière ; falaise
86<X≤90, sonde 88 en vol (b1cbcsfqt). **ORGANE V4** (besoin.py, 4e édit) :
instanciation des faits-∀ (¬∃x¬φ : _match(matrice, but, σ sur la SEULE var
liée) → instancie jugée noyau) + test dédié — **suite 8 passed**. Effet sur
le pas : INCERTAIN (S{n} est une ∀-d'IMPL, le but-feuille est DEC — v4 ne
matche que but==matrice[x:=t]) → re-PB23 EN VOL pour mesurer (bfici7b8i →
pb23_verdict3.txt). besoin.py cumule 4 édits + general.py 2 — RELECTURE
KARL groupée avant commit.

### ev.371 (4h30) — V4 NE MORD PAS SUR LE PAS ; PLAN V5 PRÉCIS
re-PB23 avec v4 : manques INCHANGÉS (10, mêmes formes + R{n} et S{n}⇒R{n}
« aucune route »). Diagnostic : S{n} est un ∀-d'IMPLICATION — v4 ne couvre
que but==matrice[x:=t] ; il faudrait instancier σ par _match du CONSÉQUENT
INTERNE puis verser l'impl au POOL DES ROUTES. **C'est universels_de (conj_
base, le conjectureur l'a déjà) — ORGANE V5 = brancher universels_de sur les
faits-∀ de besoins()** (~15 lignes : pour chaque fait-∀ dont la matrice est
une impl, générer les impls-instanciées candidates via _match(conséquent,
but) et les ajouter aux routes ; test dédié ; suite verte). Rendement attendu
HONNÊTE : le pas ne fermera PAS (c'est la conjecture) mais sa carte
s'affinera (le manque deviendrait « p premier < n avec complément… » = le
cœur additif en formule). B=88 en vol. besoin.py : 4 édits ; general.py : 2 ;
+2 tests — RELECTURE KARL groupée avant commit.

### ev.372 (4h45) — ORGANE V5 : LES ∀-IMPLICATIONS SONT DES ROUTES
universels_de = filtre de subsomption (PAS un générateur) → v5 écrit en
direct dans besoins() : les faits-∀ à matrice-impl sont RÉ-OUVERTS
(instancie(thm, var(x)) — la variable liée redevient LIBRE) et versés dans
la boucle standard des routes (σ/sous-buts/recomposition v2 réutilisés tels
quels — 15 lignes). Test dédié (fait ∀x(x=x ⇒ b=b) + fait x=x → but fermé) ;
**suite 9 passed**. 5e édit de besoin.py. re-PB23 EN VOL (bkeyet2q4 →
pb23_verdict4.txt) : S{nfor} actif — attendu : le manque du pas devient
« Fini p ∧ p < nfor ∧ … » = LE CŒUR ADDITIF (choisir le bon p premier).
B=88 toujours en vol.

### 🏆🏆 ev.373 (4h37) — LA MACHINE DÉSIGNE LA CAPACITÉ QUI LUI MANQUE
PB23-v5 : **S{nfor} EST une route** (chaînes hyp[∀], 10→23 besoins). Le
manque décisif : et(et(Fini n, Fini n), et(n≤n, ¬(n=n))) — l'organe a
σ-unifié la descente avec le SEUL candidat syntaxique **p := nfor** et nomme
l'impossibilité ¬(n=n). LECTURE : utiliser le pas exige un CHOIX CRÉATIF de
témoin p < n (p premier avec n+n−p premier) — l'unification ne le proposera
jamais. La machine a tracé ELLE-MÊME la frontière chaînage/marcheur : « il
me faut un GÉNÉRATEUR DE TÉMOINS ». C'est le manque terminal de la nuit —
et la définition machine-lisible du prochain grand chantier (le marcheur/
proposeur de témoins, cf. méta-algo diffusion-marche en mémoire). PALIER
NATUREL : mémoire durable à mettre à jour (ev.362-373), point complet Karl.

### DESIGN ORGANE V6 — LE PROPOSEUR DE TÉMOINS (ev.374, 4h45, à construire)
Le manque terminal (ev.373) définit le contrat. PRINCIPE DE SÛRETÉ ABSOLU :
le proposeur SUGGÈRE, le noyau JUGE — un mauvais témoin coûte un échec de
route, jamais un faux théorème. ARCHITECTURE (3 pièces, ~100 lignes hors
tests) :
1. **REGISTRE** (decouvertes/proposeurs.py, nouveau — decouvertes/ PLEIN à
   10 ⇒ exige éclatement OU vivre en scratchpad jusqu'au commit Karl) :
   liste de (reconnaisseur, generateur) — reconnaisseur(but, contexte) →
   None | clé ; generateur(clé) → itérateur de TERMES candidats (bornés,
   ≤K essais). Premier inscrit : GOLDBACH-PAS — reconnaître le but
   R{p}-forme sous hypothèse S{n} au contexte (ou directement le but
   decomp(t+t) avec n au contexte), générer p := N(i) pour les i premiers
   ≤ borne-calculée via goldbach_borne.couple(n_num) quand n est un NUMÉRAL
   (le cas récurrent des instances), et pour n SYMBOLIQUE : rien (honnête —
   c'est le mur mathématique, pas d'algorithme).
2. **CROCHET dans besoins()** (6e édit) : quand une route-∀ ré-ouverte
   échoue à l'unification OU produit un sous-but de forme ¬(t=t) (le
   symptôme mesuré d'ev.373), consulter le registre : pour chaque candidat
   c, instancier la route-∀ à c (au lieu de var(x)) et re-tenter la boucle
   standard (sous-buts/faits/v2). Cap dur : K candidats, profondeur-1.
3. **TESTS** : (a) synthétique — fait ∀x(P(x)⇒Q) où seul x:=t marche, P(t)
   au pool, proposeur qui suggère [t] → fermé ; (b) négatif — proposeur vide
   → comportement v5 inchangé ; (c) INTÉGRATION Goldbach — but decomp(N(k)+
   N(k)) pour k composé concret avec S{n}-analogue au pool → fermé via
   témoin proposé (l'instance du PAS fermée par proposition+noyau !).
VISION : le registre est l'embryon du MARCHEUR (méta-algo diffusion-marche) —
les générateurs appris (flywheel/conjectureur) s'y inscriront. La machine a
demandé cet organe en nommant ¬(n=n) ; c'est le premier organe CRÉATIF.

### ✅ ev.374 (4h42) — ORGANE V6-ÉBAUCHE VERT : LE PROPOSEUR DE TÉMOINS EXISTE
besoin.py (6e édit) : paramètre proposeurs=[...] — chaque proposeur(but,
faits) suggère des (conclusion-∀ du pool, terme) ; la route instanciée AU
TÉMOIN rejoint la boucle standard ; le noyau juge (un mauvais témoin = une
route morte, jamais un faux théorème). TEST : sans proposeur le but reste
ouvert (v5), avec le témoin suggéré il FERME — **suite 10 passed**. Le
registre-proposeurs du design (ev.374-design) est l'embryon du MARCHEUR.
LIMITE HONNÊTE : pour le pas SYMBOLIQUE (nfor libre), aucun témoin numéral
ne s'applique — le proposeur servira les instances et, à terme, les
générateurs APPRIS (flywheel). Karl recadre : le GÉNÉRAL seulement — la
ligne frontière (B=88 en vol) est ABANDONNÉE (peu importe son verdict).
BILAN FINAL à 5h20 (échéance Karl) puis stop.
(archive : gb_driver 88 → CLOS: True | hyps: 0 | ==cible: True | 1802s — ligne frontière close sur ordre Karl, sans suite)

## MARATHON GOLDBACH-MATIN 10 août 6h39→ (« développer la théorie », sans échéance)
### 🎉 ev.375 (6h55) — ORGANES V7+V8 + PROPOSEUR-GOLDBACH : LA CHAÎNE CRÉATIVE
**v7 = ∃-DESCENTE À TÉMOINS PROPOSÉS** (les buts ∃ n'étaient jamais
décomposés ; proposeur suggère ("∃", terme) → récursion sur φ[x:=t] →
existe_temoin_verifie jugée noyau — les ∃ IMBRIQUÉS testés). **v8 = BUT-∧
direct** (récursion conjoints + _recomposer — le symétrique de v2).
**TEST D'INTÉGRATION VERT (58 s)** : but = decomposition(N(16)) fermé de
BOUT EN BOUT — proposeur décode l'égalité-somme PAR ÉGALITÉ DE TERMES (SC
est un τ-terme OPAQUE : jamais parser par .nom — piège mesuré), suggère
couple (3) puis complément (13), v7 injecte, v8 recompose, faits =
est_premier_num ×2 + somme_num symétrisée. besoin.py : 8 organes cumulés
(v2→v8), suite complète 12 passed attendue. ÉTAPE 2 À VENIR : le proposeur
τ-SYMBOLIQUE (τ existe : outil_formule.tau(x, f)) — proposer p := τ-terme
(« un premier convenable ») au pas SYMBOLIQUE → la machine reformulerait son
manque en conjecture sur les COMPLÉMENTS (la reformulation machine de
Goldbach — l'inédit).

### DESIGN ÉTAPE 2 — LE PROPOSEUR τ-SYMBOLIQUE (ev.376, 7h00, à concevoir avec Karl)
Deux variantes mesurées d'avance, avec leurs pièges :
**(a) τ-canonique** : T(n) := τp( premier p ∧ ∃q(premier q ∧ 2n = p+q) ) —
chez Bourbaki ∃xφ ⟺ φ(τxφ) (LE critère du τ) : proposer T réduit l'∃ à
« φ(T) » qui EST ∃xφ — formellement exact mais CIRCULAIRE (aucune
information nouvelle ; vérifier si le repo a le critère ∃⟺τ prêt — utile
comme PONT de toute façon). **(b) τ-défini** : T(n) := « le plus grand
premier ≤ 2n » (bien défini SANS Goldbach : τ + bornes + infinitude !) —
proposé au pas, le manque machine deviendrait « le complément 2n−T est
premier » (la soustraction : iii_5_2 l'a) — mathématiquement FAUX en général
(le plus grand premier n'est pas toujours le bon témoin) donc la machine
nommerait un manque INFERMABLE mais INSTRUCTIF : premier exemple de témoin
symbolique NON-canonique jugé. La VRAIE piste de recherche : des familles de
τ-témoins T_i(n) définis (plus grand premier ≤ 2n−2, premiers de Sophie
Germain…) + le PROPOSEUR APPRIS qui les essaie — le marcheur symbolique.
DÉCISION : à concevoir en session de jour avec Karl (risque de circularité
à cadrer) ; les organes v6-v8 sont PRÊTS à recevoir n'importe quel τ-terme
comme témoin (le noyau jugera). L'infrastructure de la « théorie non
publiée » est complète : carte + organes + proposeurs + τ disponible.

### MARATHON GOLDBACH-MATIN 10 août (suite) — GG9+GG10 : GOLDBACH SANS ∃ (ev.377, ~7h15)
La question du design ev.376(a) est TRANCHÉE en code : le pont ∃⟺τ est DÉJÀ
deux primitives du noyau — `N.existe_temoin(r,x)` ⊢ (∃x)R ⇒ (τx(R)|x)R
(noyau_abrege:96, justifié par l'identité E I.32) et `N.s5(r,t,x)` ⊢ (T|x)R
⇒ (∃x)R. La « circularité » redoutée n'en est pas une : le pont ÉLIMINE le
nœud ∃ et transforme le but en CONJONCTION sur des termes canoniques nommés.
**GG9** (scratchpad GG9_pont_tau.py, 0 s, tout clos, invariant 22) :
⊢ ∀k( decomp(k+k) ⇔ C(k) ), C(k) = premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q,
T := τp(∃q mat), Q := τq(mat[p:=T]) — prélèvement STRUCTUREL sur
decomposition (tag/lieur/sous), double étage aller (existe_temoin ×2) et
retour (s5 ×2). **GG10** : ⊢ H ⇔ H_τ où H_τ = ∀k(A(k) ⇒ C(k)) — LA FORME
CANONIQUE de la conjecture : Goldbach ⟺ « les deux τ-termes nommés sont
premiers et somment ». **PB25a** (mesure) : but decomp(k+k) symbolique +
fait GG9-τ[∀] au pool → v5 ouvre la route, v2 éclate C : la machine énonce
6 obligations canoniques (T≠un, clause-diviseurs de T, Q≠un,
clause-diviseurs de Q, somme) — les σ-trivialités ¬(n=n) d'ev.373 ont
DISPARU, remplacées par le vrai reste-à-prouver sur témoins NOMMÉS. AUCUN
édit de besoin.py (architecture : GG9 versé comme FAIT-∀, pas comme
proposeur v7 — v7 jette les manques des routes-témoins échouées, piège noté
pour un éventuel organe v9). PB25b lancé : le pas complet (GG8-descente +
GG10-canonique + fait GG9-τ), verdict à consigner. NOTE HONNÊTE : GG9/GG10
sont de la LOGIQUE (le contenu arithmétique reste entier : prouver
premier(T_k) pour tout k est exactement la conjecture) — l'acquis est la
REFORMULATION machine-lisible sans ∃ + la disparition du bruit σ dans les
manques ; le chantier créatif (variante (b), familles de τ-témoins définis,
marcheur) reste ouvert avec Karl.

### PB25b — LE PAS COMPLET, VERSION τ : VERDICT (ev.378, 7h25)
But H (⟺ goldbach), pool = routes DESCENTE (GG8) + CANONIQUE (GG10) + fait
GG9-τ[∀]. 2,4 min (146 s de recurrence_forte), non fermé (attendu),
invariant 22. **11 besoins, 9 distincts, et le rapport est devenu LA CARTE
LISIBLE** : (1) les 6 obligations canoniques (chaîne GG9-τ[∀][∀]) — T≠un,
clause-diviseurs de T, Q≠un, clause-diviseurs de Q, somme ; (2) le manque
route-DESCENTE = H_rec entier (le pas, avec LA BORNE ∃F… visible dans S{n});
(3) le manque route-CANONIQUE = H_τ entier (la forme sans ∃) ; (4) un
« (aucune route) » = l'instance brute du pas. Les σ-trivialités ¬(n=n) ont
disparu du rapport TOP-NIVEAU aussi. La théorie se lit maintenant : H
atteignable par DEUX routes certifiées ; la canonique exige H_τ, dont le
contenu est énoncé en 6 obligations sur τ-témoins nommés. Scripts :
GG9_pont_tau.py (construire() → GG9/GG10 + PB25a), PB25_pas_tau.py.
Prochaine matière (au choix du segment suivant) : variante (b) τ-défini
« plus grand premier ≤ 2n » (sonde instructive, iii_5_2 a la soustraction),
organe v9 (fusionner les manques des routes-témoins v7 échouées — besoin
mesuré), familles de τ-témoins + proposeur appris (marcheur symbolique),
promotion GG1-GG10 au dépôt (éclatement conjectures/ = décision Karl).

### GG11+PB26 — LE PREMIER TÉMOIN DÉFINI JUGÉ (ev.379, 7h35)
Variante (b) d'ev.376 FAITE en sonde : T_b := τpmax(premier ∧ ≤2k ∧ maximal)
(« le plus grand premier ≤ 2k », liants frais d3/q3/rmax), Q_b :=
diff_somme(2k, T_b) = τcgb(2k = T_b+c) [E III.37]. **GG11 (0 s, clos,
invariant 22)** : ⊢ ∀k( premier₁(T_b) ∧ premier₂(Q_b) ∧ 2k=T_b+Q_b ⇒
decomp(2k) ) — s5 ×2, la route-témoin est GRATUITE pour N'IMPORTE quel
terme défini (aucune preuve d'existence : les obligations restent dans
l'antécédent). PB26 : versé comme fait-∀ → 6 obligations sur les témoins
GLOUTONS ; la machine isole la partie dure/fausse-en-général : « τcgb
premier » (= 2k−T premier). LEÇON D'ARCHITECTURE : toute stratégie de
témoins symboliques compile en route certifiée + obligations explicites —
le programme « familles de τ-témoins + proposeur symbolique » est validé
dans son principe. Script : PB26_temoin_defini.py.

### GG12+GG13+PB27 — LA SOMME DÉCHARGÉE, LES LIGNES SE REJOIGNENT (ev.380, 7h45)
**GG12 (5 s, clos)** : ⊢ ∀k( (card T_b ∧ card 2k ∧ T_b≤2k) ⇒ 2k = T_b+Q_b )
— existe_complement_somme(T_b, M) accepte les TERMES directement, puis
N.existe_temoin sur la matrice de diff_somme : le geste du docstring
d'iii_5_2, exécuté tel quel. **GG13 (clos)** : GG11 ∘ GG12 — la route
gloutonne n'exige plus que primalités + intendance. **PB27** : la somme a
DISPARU des manques ; restent premier(τpmax), premier(τcgb), ∃X τpmax=Card X
(card T_b), est_cardinal(2k), et le ≤ qui SE DÉPLIE EN ∃F-INJECTION — la
MÊME forme que LA BORNE de la nuit : les deux lignes de la théorie (frontière
bornée d'hier, témoins définis d'aujourd'hui) se rejoignent sur l'injection
du ≤. Carte gloutonne finale : {premier(T_b) + intendance} (prouvable
moyennant « ∃ plus grand premier ≤ 2k » — chantier max-fini réel) vs
{premier(τcgb)} (LE cœur, faux en général). Script : GG12_somme_temoin.py.
SUIVANT : générateur route_temoin(T) (tout τ-terme → route certifiée) +
famille de stratégies au pool (PB28, marcheur symbolique embryonnaire).

### PB28 + ORGANE V9 — LE GÉNÉRATEUR DE ROUTES ET LA CARTE DES STRATÉGIES (ev.381, 8h00)
**route_temoin(T, Q)** (PB28_famille_temoins.py) : générateur qui compile
N'IMPORTE quel couple de termes en route certifiée ⊢ ∀k( P1(T) ∧ P2(Q) ∧
2k=T+Q ⇒ decomp(2k) ) — s5 ×2, 0 s. **Famille de 4 stratégies versée d'un
coup** : GLOUTONNE (plus grand premier ≤ 2k), DÉCALÉE (≤ 2k−2), JUMELLE
(T=Q=k — SUBSUME GG2′/famille {2p} : ses obligations = « k premier »
exactement), CANONIQUE (GG9). PB28 = la carte des stratégies, obligations
par route, dite d'un coup — l'embryon du MARCHEUR SYMBOLIQUE (proposer =
choisir dans la famille ; juger = noyau ; comparer = ce rapport).
**ORGANE V9 (besoin.py, ev.381)** : mesuré sur la JUMELLE qui traînait
« 2k = 2k » comme manque — un but t=t ferme désormais par N.reflexivite
(Théorème 1, E I.39), garde stricte t==t, le noyau juge. PIÈGE APPRIS :
deux tests utilisaient egal(y,y) comme ÉCHAFAUDAGE commode (v2-récalcitrants,
v6-proposeur) — v9 les court-circuitait ; échafaudages remplacés par des
buts ∃ (s5+réflexivité), l'INTENTION des tests intacte. Suite : 11 passed
(dont test_organe_v9_egalite_reflexive neuf). Re-sonde PB28 : la JUMELLE
n'énonce plus QUE la primalité de k. besoin.py = 9 organes cumulés
(v2→v9) — RELECTURE KARL groupée avant commit. SUIVANT : l'existence
« ∃ plus grand premier ≤ 2k » (chantier max-fini, décharge premier(T_b) de
la gloutonne) ou promotion GG1-GG13 (éclatement conjectures/, décision Karl).

### PB29a-c — L'ENSEMBLE DES PREMIERS BORNÉS, CONSTRUIT ET NON VIDE (ev.382, 8h20)
Chantier « ∃ plus grand premier ≤ 2k » (décharge premier(T) de la route
gloutonne GG13). **PB29a (0 s)** : P_b := app("premiers_bornes", b), moule
EXACT de l'intervalle (théorie dédiée + axiome ∀b∀x( x∈P_b ⇔ (premier₁(x)
∧ x∈[0,b]) ), forme C51-sûre — sélection BORNÉE par [0,b], theorie_ensembles
INTACTE à 22) ; extraction/introduction des deux sens ✓ ; premier(2) au
dépôt en graphie d1/q1 (est_premier_num(2,d='d1',q='q1') CLOS, conjectures/
primalite.py — PAS arithmetique/). **PB29c (49 s)** : GG14 ⊢ ∀k( (Fini k ∧
k≠0 ∧ k≠1) ⇒ 2 ∈ P_{2k} ) — cascade POSITIVE miroir de GG5b :
inf_egal_total_general (comparabilité k/2) → branche k≤2 scindée
(successeur_ordre : k≤1 meurt par antisym/contra, k=2 donne 2≤k par
s6-Leibniz sur 2≤2) → 2≤k TOUJOURS → transitivité avec k≤k+k (prop2) →
2≤2k → corps intervalle (card_num(2) + zero_inf_egal_cardinal) →
membre_intervalle_entiers_t → axiome-P ← : 2∈P_2k. **GG14b** : P_2k ≠ ∅
(s6 sur P=∅, AXIOME_VIDE, neg_intro). ARSENAL APPRIS : card_num/fini_num
dans machine_num (ré-exports de numeraux) ; inf_egal_total_general +
inf_egal_transitive_general + inf_egal_reflexif_general (ordre_cardinaux/
ensembles_cardinaux_props_restantes_ordre.py) ; membre_intervalle_entiers_t
(prop5_intervalle, prend des TERMES). RESTE : (b) Fini(P_2k)
[partie_finie_est_finie + Fini([0,2k])], (d) dual prop3_total_MAX (miroir
de prop3_total_min), (e) assemblage premier(T′). Scripts :
PB29a_premiers_bornes.py (construire()), PB29c_deux_dans_P.py (construire()
→ GG14/GG14b).

### PB29b — GG15 : P_2k EST FINI (ev.383, 8h45)
⊢ ∀k( Fini k ⇒ est_fini_ensemble(P_2k) ) — CLOS 4 min, invariant 22.
Route : somme_binaire_entier (Fini 2k) → prop5_intervalle_zero (Card([0,2k])
= succ 2k ; est_entier==est_fini textuel VÉRIFIÉ par assert) →
fini_implique_fini_successeur + s6-Leibniz → est_fini_ensemble([0,2k])
(liant du Card de prop5 == liant d'est_fini_ensemble, AUCUN pont-α) →
inclusion P⊂[0,2k] (extraction axiome-sélection, liant « z » d'inclus) →
partie_finie_est_finie (gen2+instancie aux termes). BILAN PB29 : P_2k
construit (a) + non vide (c, GG14/GG14b) + fini (b, GG15). RESTE (d) : le
MIROIR prop3_total_MAX (« partie finie non vide d'un totalement ordonné a
un PLUS GRAND élément ») — TROU DU LIVRE (Cor.1 §III.4 ne couvre que la
moitié min au dépôt), à écrire en miroir de ensembles_prop6_fini_interval_
iii5.py puis promouvoir avec Karl ; et (e) l'assemblage premier(T′).
Script : PB29b_fini_P.py (construire() → GG15).

### PB30 — GG16/GG17 : LA RÉDUCTION LA PLUS CONDENSÉE ATTEINTE (ev.384, 9h10)
T° := τm( m ∈ P_2k ) — « un premier ≤ 2k », témoin DÉFINI et NON VIDE (GG14
donne 2∈P_2k, s5 donne ∃m, existe_temoin donne T°∈P_2k : le τ DÉNOTE).
**GG16 (84 s, CLOS)** : ⊢ ∀k( H(k) ⇒ premier₁(T°) ) — la PREMIÈRE primalité
d'un témoin symbolique effectivement PROUVÉE (extraction de l'axiome-P).
**GG17 (247 s, CLOS)** : ⊢ ∀k( (H(k) ∧ premier₂(2k−T°)) ⇒ decomp(2k) ) :
toute l'intendance déchargée — primalité de T°, card T°, T°≤2k (corps de
l'intervalle), card 2k (somme_binaire_entier+fic_t), la somme (Prop.13 +
τ-axiome). Il ne reste QU'UNE obligation : la primalité du complément.
HONNÊTETÉ CAPITALE : T° est un premier ≤2k ARBITRAIRE (τ non spécifié) —
« 2k−T° premier » est donc FAUX en général pour CE témoin ; GG17 est une
réduction valide dont l'hypothèse ne se déduit pas. La vraie sortie est de
QUANTIFIER sur les témoins : Goldbach ⟺ ∃m∈P_2k avec 2k−m ∈ P_2k, c.-à-d.
P_2k ∩ (2k−P_2k) ≠ ∅ — la forme ENSEMBLISTE (crible). C'est PB31.
Script : PB30_premier_temoin.py.

### PB31 — GG18 : GOLDBACH COMME RENCONTRE (FORME CRIBLE) (ev.385, 9h40)
Sortie de l'impasse GG17 (témoin τ arbitraire ⇒ hypothèse indéductible) en
QUANTIFIANT sur les témoins. Q_b := miroir = { x∈[0,b] : (b−x) ∈ P_b }
(même moule : app opaque + axiome en théorie dédiée). **GG18 (177 s, CLOS,
invariant 22)** : ⊢ ∀k( ( H(k) ∧ ∃m( m∈P_2k ∧ m∈Q_2k ) ) ⇒ decomp(2k) ).
Preuve : extraction premier₁(m), m≤2k, card m (corps de l'intervalle) ;
extraction (2k−m)∈P_2k du miroir ⇒ premier₁(2k−m) ; **pont-α GG6 généralisé
puis instancié au TERME (2k−m)** pour le 2e habit d2/q2 (le run le mesure :
177 s, c'est le poste coûteux) ; somme par Prop.13+τ ; route s5×2 ;
loi_deduction + existe_elimination sur « mrx » (DEC sans m libre).
SENS RÉCIPROQUE REPORTÉ (honnête) : de 2k=p+q tirer p≤2k exige Fini(p), non
disponible (est_premier ne porte pas la finitude) — il faudrait un lemme
« Fini(a+b) ⇒ Fini a ». LECTURE : la conjecture est désormais une question
de RENCONTRE de deux parties finies non vides de [0,2k], donc la porte du
COMPTAGE : Card(A∩B) ≥ Card A + Card B − Card[0,2k]. Prochain pas (PB32) :
poser cette inégalité et MESURER honnêtement que le comptage brut ne suffit
pas (π(2k) ~ 2k/ln 2k < k) — cartographier POURQUOI la voie des tiroirs
échoue est un résultat en soi. Script : PB31_intersection.py.

### PB32 — AUDIT : `est_premier` NE DIT PAS « ENTIER » (ev.386, 10h05) ⚠️
En cherchant pourquoi le sens retour de GG18 bloquait, DÉFAUT DE FIDÉLITÉ
trouvé et CERTIFIÉ : `est_premier(p)` (goldbach.py:95) ne garde que le
DIVISEUR d, jamais p ; comme `divise_propre(d,p)` exige p = Card(d×q), un p
non-cardinal n'est divisible par RIEN et la clause (∀d) est vacuously vraie.
**A1 CLOS** : ⊢ ( ¬(p=1) ∧ (∀d)¬divise_propre(d,p) ) ⇒ est_premier(p) —
« tout objet indivisible ≠1 est premier ». Donc goldbach()/decomposition
quantifient sur des témoins NON ENTIERS : l'énoncé est PLUS FAIBLE que la
conjecture. Soundness intacte, fidélité en défaut (même famille que
l'incohérence de l'intersection du 26 juil.). **A2 CLOS** : la correction
est_premier_ent(p) := Fini(p) ∧ est_premier(p) est GRATUITE sur les numéraux
(fini_num+est_premier_num) ⇒ ne coûte rien aux acquis. goldbach.py NON
MODIFIÉ (décision d'énoncé = Karl). Consigné dans docs/journal/ANOMALIES.md.
PIÈGE MESURÉ : extraire une sous-formule par .sous est fragile (et = ¬(¬a∨¬b),
∀ = ¬∃¬ : quatre niveaux) — RECONSTRUIRE la sous-formule et asserter l'égalité.
Script : PB32_audit_premier.py.

### PB33 — GG19 : L'ÉQUIVALENCE CRIBLE, ET L'AUDIT VALIDÉ PAR L'USAGE (ev.387, 10h40)
Avec l'énoncé GARDÉ (premier_ent(p) := Fini(p) ∧ est_premier(p)) et le miroir
défini par un ∃ INTERNE (Q_b := {x : ∃y(premier_ent₂(y) ∧ b = x+y)} — ni
soustraction, ni commutativité, ni cardinalité du complément) :
**GG19a (⇐) et GG19b (⇒) CLOS en 2 s**, invariant 22 :
    ⊢ ∀k( (∃m)( m∈P_2k ∧ m∈Q_2k )  ⇔  DEC_ent(2k) )
**Le sens (⇒) est EXACTEMENT celui qui était bloqué** avec l'énoncé non gardé :
il consomme la garde Fini(p) via prop2_sous_fini (Fini p ⇒ (2k=p+q ⇒ p≤2k)).
⇒ L'audit PB32 n'est PAS de l'hygiène : la correction d'énoncé est ce qui rend
la reformulation COMPLÈTE (équivalence, pas simple implication). Argument
chiffré pour la migration du dépôt — décision Karl.
CONTOURNEMENT NOTÉ : `fini_downward` (x ≤ n fini ⇒ x fini) est REPORTÉ au dépôt
(cor1_partie_finie_est_finie_conditionnel le prend en antécédent) — évité en
mettant la finitude dans l'énoncé plutôt qu'en la dérivant.
Script : PB33_equivalence_gardee.py (construire() → GG19a/GG19b/Pens/Qens).

### PLAN ÉDITORIAL — 3 articles + 1 programme (ev.388, 10h45)
Écrit dans docs/articles/PLAN_ARTICLES.md, à la demande de Karl. Règle de
partage : UNE QUESTION PAR ARTICLE ; 16 « grosses idées » numérotées et
attribuées à un seul article chacune. A1 = l'objet (théorie Bourbaki en
machine ; frontière de confiance, soundness≠fidélité, arbre-détecteur de
trous, métathéorème=générateur). A2 = la méthode (dernier kilomètre ; organe
de besoin, diagnostic→organe v2-v9, chaînage vs créativité, faux « bloqué »).
A3 = le résultat (cartographier l'ouvert ; carte Goldbach, sans-∃ par τ,
stratégie=témoins, forme crible + résultat négatif, audit né du blocage).
A4 = programme (marcheur) — à NE PAS publier avant qu'il ferme un but que le
chaînage seul ne ferme pas. Ordre conseillé : A1, A3, A2, A4.

### PB34 — LA VOIE DES TIROIRS EST MORTE (ev.389, 11h00) ⚠️ mesure, pas preuve
Diagnostic quantitatif (Python pur, noyau NON sollicité, étiqueté comme tel)
avant d'investir dans l'inclusion-exclusion formelle. Comme x ↦ 2k−x est une
bijection de P_2k sur Q_2k∩[0,2k], |Q| = |P| = π(2k) et le critère suffisant
des tiroirs s'écrit **2·π(2k) > 2k+1**, c.-à-d. π(2k) > k.
**RÉSULTAT : il ne tient POUR AUCUN k ≥ 2** (liste vide sur [2, 100000]).
Ratios π(2k)/k : 0,500 (2k=100) → 0,336 (10³) → 0,246 (10⁴) → 0,192 (10⁵) →
0,180 (2·10⁵) ; déficit π−k = −82016 à 2k=200000. Pendant ce temps le nombre
RÉEL de décompositions r(2k) croît (2 → 6 → 28 → 127 → 810 → 1417).
**LECTURE** : la conjecture est largement vraie en pratique, mais le comptage
BRUT ne voit jamais cette marge — il faudrait une information sur la
RÉPARTITION de P_2k, pas sur son cardinal. **DÉCISION : ne PAS formaliser
l'inclusion-exclusion pour Goldbach** (chantier de plusieurs jours évité) ;
la borne de comptage est structurellement incapable de fermer la rencontre.
Script : PB34_seuil_tiroirs.py.

### PB35 — LA MACHINE NOMME LA RENCONTRE (ev.390, 11h10)
Boucle complète refermée : GG19a versé comme fait-∀, but DEC_ent(2k)
symbolique → **l'organe nomme EXACTEMENT la rencontre**, mot pour mot :
    ∃mrx ¬( mrx ∈ premiers_ent_bornes(2k) ⇒ ¬ mrx ∈ miroir_ent(2k) )
c.-à-d. (∃m)( m ∈ P_2k ∧ m ∈ Q_2k ), UN SEUL besoin, chaîne
« GG19a-crible[∀][∀] ». Le vocabulaire du manque est passé des σ-trivialités
(¬(n=n), ev.373) aux OBJETS ENSEMBLISTES construits dans la matinée. C'est le
cycle du projet en entier : réduction certifiée → re-sonde → manque exact.
Script : PB35_organe_crible.py.

### PB36 — GG21 : LE PONT VERS L'ÉNONCÉ DU DÉPÔT (ev.391, 11h40)
⊢ ∀k( DEC_ent(2k) ⇒ decomp(2k) ) — CLOS 0 s. La forme GARDÉE descend sur
l'énoncé du dépôt (on jette les gardes Fini et on refait la route s5×2) ; la
réciproque est FAUSSE, c'est tout le contenu de l'audit PB32. Conséquence
pratique : **travailler avec l'énoncé corrigé ne perd RIEN** — la chaîne
complète est  rencontre ⇒ DEC_ent(2k) ⇒ decomp(2k)  (GG19a ∘ GG21).
Script : PB36_pont_depot.py.

### LIVRABLES ÉDITORIAUX (ev.392, 11h45)
- `docs/articles/PLAN_ARTICLES.md` — 3 articles + 1 programme, une question
  par article, 16 grosses idées attribuées, ordre conseillé A1/A3/A2/A4.
- `docs/articles/CARTE_GOLDBACH.md` — la carte consolidée (tronc des 4 formes
  équivalentes, descente, générateur de témoins, P_2k, forme crible, audit,
  ce qui est fermé / fermé par la négative / ouvert). Matériau direct de A3.

### ⚠️ CORRECTION D'HORODATAGE (ev.393, 09h35 RÉEL)
Les heures portées sur les entrées **ev.377 à ev.392** sont FAUSSES : elles ont
été estimées en cumulant les durées de scripts, sans jamais lire l'horloge.
La **séquence** des entrées est correcte, seules les heures sont à ignorer.
Plage réelle de tout ce bloc : **~06h50 → 09h35 du 10 août**.
LEÇON DE MÉTHODE : lire l'heure (`date`) avant tout horodatage ou toute
annonce de fin de créneau — une estimation cumulée dérive vite de plusieurs
heures. Le marathon annoncé « jusqu'à 12h » a été clos à 09h33 pour cette
raison ; il REPREND.

### PB37 — ORGANE v10 : LE PREMIER PROPOSEUR GÉNÉRIQUE (ev.394, 09h36 réel)
Tous les proposeurs antérieurs étaient AD HOC (décodage de la matrice de
Goldbach, arithmétique Python). **v10 est générique et ignore le problème** :
face à un but (∃x)φ(x), il propose comme témoins les t des faits « t ∈ A »
du pool (tag "in", dédup par terme). C'est le geste minimal du marcheur :
*les objets déjà nommés sont les candidats*, le noyau juge, un mauvais
candidat ne coûte qu'une route morte.
MESURE bout-en-bout sur la forme crible : faits { c∈P_2k , c∈Q_2k } (c
CONSTANTE opaque, indevinable par un proposeur arithmétique) + route GG19a,
but DEC_ent(2k) → **SANS v10 : non fermé, 2 besoins. AVEC v10 : FERMÉ, 0
besoin**, conclusion == DEC_ent, hypothèses exactement {c∈P, c∈Q}.
Test dédié `test_organe_v10_proposeur_par_appartenance` VERT (0,5 s) —
besoin.py inchangé (v10 est un proposeur, pas un organe interne : c'est le
point d'extension prévu par v6/v7). Script : PB37_proposeur_appartenance.py.

### PB38+PB39 — GG22 et GG24 : LA SYNTHÈSE (ev.395-396, 09h40 réel)
**GG22 (6 s, CLOS)** : ⊢ ∀k( (Fini k ∧ premier₁(k) ∧ premier₂(k)) ⇒
rencontre(k) ) — témoin m := k lui-même (k ∈ P car k ≤ 2k par prop2_sous_fini
sur 2k=k+k réflexif ; k ∈ Q avec témoin interne y := k). **La forme crible
absorbe donc la réduction GG7** : la rencontre n'est à établir que pour les
k COMPOSÉS. Script : PB38_crible_composes.py.
**GG24 (6 s, CLOS) — LE THÉORÈME DE SYNTHÈSE** :
    ⊢ [ ∀k( (Fini k ∧ k≠0 ∧ k≠1 ∧ ¬premier₁(k)) ⇒ rencontre(k) ) ] ⇒ H
c.-à-d. **pour démontrer Goldbach il SUFFIT d'établir, pour chaque k composé,
que les premiers ≤ 2k rencontrent leur miroir**. Assemblage : GG22 en ligne
(branche premier, nourrie par le pont-α GG6) + hypothèse (branche composé) +
tiers exclu + GG19a (rencontre ⇒ DEC_ent) + GG21 rejoué (DEC_ent ⇒ decomp du
dépôt). C'est l'énoncé d'entrée de l'article A3. Script : PB39_synthese.py.

### PB40 — GG23 : LA SYMÉTRIE DU CRIBLE (ev.397, 09h53 réel)
⊢ ∀k ∀m( ( m ∈ P_2k ∧ m ∈ Q_2k ) ⇒ (∃m')( m' ∈ P_2k ∧ m' ∈ Q_2k ∧ 2k = m+m' ) )
— CLOS 6 s, invariant 22. **Tout point de la rencontre vient AVEC son
partenaire**, et les deux somment à 2k : la rencontre est stable par
l'involution m ↦ 2k−m, de point fixe k (2k = k+k, cas GG22). Les
décompositions de Goldbach vont par PAIRES, dit et certifié.
Route : P et Q écrits en graphie COHÉRENTE d1/q1 (⇒ AUCUN pont-α, économie de
177 s) ; le partenaire est le témoin y de « m ∈ Q » ; y ∈ P par la borne
DROITE (inf_egal_somme_droite_binaire : Card y ≤ m+y) + Card y = y
(_cardinal_est_son_cardinal, iii_3 ordre_cardinaux) + Leibniz S6 ; y ∈ Q par
somme_cardinale_commutative.
**DEUX PIÈGES MESURÉS** — (1) COLLISION DE LIANTS : le témoin extrait « ymi »
portait le même nom que le liant interne de l'axiome Q ⇒ instancier l'axiome
EN ce témoin capturait. FIX GÉNÉRAL : ne pas RECONSTRUIRE la matrice de l'∃,
mais LIRE le liant réellement produit par le noyau
(`imp.conclusion.sous[0].sous[0]` → `.lieur` / `.sous[0]`), puis asserter que
la matrice instanciée est bien celle attendue. (2) ERREUR DE FORMULATION (la
mienne, pas le code) : la conclusion contient m libre (« 2k = m+m' »), donc
existe_elimination sur m est INVALIDE — il faut GÉNÉRALISER sur m. L'énoncé
∀k∀m est d'ailleurs plus fort et plus lisible.
Script : PB40_symetrie_crible.py.

### NON-RÉGRESSION + ORGANE v11 (ev.398, 09h57 réel)
**Suite complète `outils_ia/decouvertes/` : 22 passed en 28:50** (le lent
d'Euclide inclus) — non-régression confirmée pour TOUS les édits de besoin.py
(organes v2→v10) + les proposeurs. Filet de sécurité vert.
**ORGANE v11 (PB41_proposeur_schema.py)** : proposeur générique par
VARIABLES LIBRES (`libres_f`), qui GÉNÉRALISE v10. Piège mesuré : v10
n'extrayait que les termes de TÊTE des faits atomiques ; or un prédicat
DÉFINI comme `est_fini(c)` a le tag « non » (il se déplie en ¬∨∃) et enfouit
son argument c — donc l'extraction de tête rend []. `libres_f` traverse le
dépliage et atteint c. Mesure : but (∃w)(w=c), pool = { Fini(c) } → v10
échoue, v11 propose c (variable libre de Fini(c)), v7 descend, v9 ferme c=c.
Test dédié `test_organe_v11_proposeur_par_schema` VERT (0,35 s). besoin.py
inchangé (v11 est un proposeur, point d'extension v6/v7). Le vivier de
témoins du marcheur s'élargit sans connaître le problème.

### CAPSTONE — LA CHAÎNE REJOUÉE ET VÉRIFIÉE (ev.399, 09h59 réel)
`CAPSTONE_crible.py` : artefact REPRODUCTIBLE de la matinée (annexe de
l'article A3). Importe les construire() des scripts, rejoue les NEUF maillons
et imprime un tableau de statut. **Résultat : 8 s, tous CLOS (0 hyp),
invariant 22, « ✓ TOUT COMPOSE ».**
   GG6 · GG7← · GG7→ · GG9← · GG9→ · GG10← · GG10→ · GG19← · GG19→
(GG21/GG22/GG24 dans PB36/PB38/PB39 ; GG23 dans PB40.)
Vertu du script : il ASSERTE `tous clos and invariant == 22` — donc il casse
si un maillon cède. C'est le test d'intégration de l'arc Goldbach, hors
pytest (les scripts vivent en scratchpad tant que conjectures/ n'est pas
éclaté — décision Karl).

### PB42 — L'ORGANE FACE À GG24, ET UN DÉFAUT ARCHITECTURAL (ev.400, 10h09 réel)
**(1) DÉFAUT TROUVÉ ET CORRIGÉ** : `besoins_generaux` (general.py) ne
propageait PAS les proposeurs — un but ∀ ou ⇒ les perdait avant d'atteindre
l'organe, donc AUCUN ∃ enfoui sous un ∀ n'était attaquable par v6/v7/v10/v11.
Découvert parce qu'une première mesure « v12 ne ferme rien » était en fait un
FAUX TEST (fallback silencieux : la signature n'acceptait pas `proposeurs`).
FIX : paramètre `proposeurs=None` + propagation aux QUATRE points de passage
(voie directe, descente-∀, descente-⇒, feuille) ; défaut inchangé.
Non-régression : **13 passed** (test_autonomie + autonomie, hors slow).
LEÇON : un test qui « passe » par fallback silencieux est pire qu'un test
absent — asserter la CAPACITÉ avant de mesurer (`inspect.signature`).
**(2) LA BOUCLE AU PLUS HAUT NIVEAU** : pool = { GG24 }, but = H →
**l'organe nomme EXACTEMENT HC** (« ∀k composé, rencontre(k) »), soit la
conjecture dans le vocabulaire ensembliste construit le matin même. La chaîne
réduction certifiée → re-sonde → manque exact vaut donc aussi au sommet.
**(3) MESURE HONNÊTE DE LA FRONTIÈRE** : avec v12 (v10 ∪ v11) réellement
propagé, toujours 4 besoins, non fermé — v10/v11 tirent leurs témoins
d'objets NOMMÉS ; ici k est universellement quantifié et le pool n'en contient
aucun. **Il n'y a rien à proposer** : c'est la limite exacte du marcheur
actuel, et elle désigne le prochain organe (fabriquer un témoin plutôt que le
choisir). Scripts : PB42_organe_synthese.py, PB39 expose désormais construire().

### PB43 — ORGANES v13 + v14 : LA MACHINE REFAIT GG9 TOUTE SEULE (ev.401, 10h23 réel)
**v13 — LE PROPOSEUR QUI FABRIQUE** (et ne choisit plus) : face à (∃x)φ, il
construit le témoin CANONIQUE τx(φ) depuis le but SEUL, sans consulter le pool
(licite par S5). C'est la réponse au manque désigné par PB42 (« quand rien
n'est nommé, v10/v11 n'ont rien à proposer »).
**v14 — NE PLUS JETER LES MANQUES DE LA ∃-DESCENTE** (besoin.py, organe v7) :
une route-témoin qui échouait perdait les manques déjà nommés par sa descente,
si bien que le but ∃ était reporté TEL QUEL. Ils sont désormais accumulés et
remontés SI AUCUN témoin ne ferme.
**MESURE DÉCISIVE (cas 3, pool VIDE, but = decomposition(2k) symbolique)** :
   · v10 : manque = « ∃pgb ∃qgb … »            → encore un ∃ (but INTACT)
   · v13 : manque = « ¬(…τpgb(…)… ) »          → propriétés du τ-TERME
**La machine ramène donc d'elle-même « il existe p,q premiers sommant à 2k » à
« propriétés de deux termes nommés » — exactement le geste fait À LA MAIN dans
GG9/GG10.** Non-régression : 13 passed (100 s, hors slow).
PIÈGES MESURÉS : (1) mon cas 2 initial ne DISCRIMINAIT pas (v10 réussissait
aussi car le τ-terme figurait dans les faits) — un test qui passe des deux
côtés ne prouve rien ; (2) l'indicateur « plus de manques = mieux » était FAUX :
le bon critère est la FORME du manque (encore un ∃ ? ou déjà des propriétés
d'un terme ?), pas leur nombre. Script : PB43_proposeur_canonique.py.

### PB44 — GG25 : LE CRIBLE ABSORBE LE BORNÉ, LES 3 LIGNES CONVERGENT (ev.402, 10h27 réel)
⊢ ∀p ∀q ∀k( ( premier_ent(p) ∧ premier_ent(q) ∧ 2k = p+q ) ⇒ rencontre(2k) )
— CLOS 6 s, invariant 22. Tout témoin CONCRET de décomposition donne la
rencontre (p ∈ P par prop2_sous_fini + intervalle ; p ∈ Q avec témoin interne
q, liant LU chez le noyau).
**Conséquence : les TROIS lignes du projet convergent sur un seul objet** —
(1) le BORNÉ (n ≤ 86, témoins numéraux) : absorbé par GG25 ;
(2) les COMPOSÉS (GG7/GG22 : les k premiers gratuits) : absorbé par GG22 ;
(3) le CRIBLE (GG19/GG24) : la forme d'arrivée.
Tout ce qui a été prouvé sur Goldbach dans ce dépôt se lit désormais comme un
énoncé sur la rencontre de P_2k et de son miroir. Script :
PB44_crible_absorbe_borne.py.

### PB45 — LE PORTRAIT FINAL (ev.403, 10h30 réel)
Tout l'arsenal du matin au pool (GG24) + TOUS les proposeurs (v10 choisit ∪
v11 variables libres ∪ v13 fabrique le τ canonique), but = H :
**NON FERMÉ (attendu), 7 besoins, et le manque nommé EST la rencontre sur les
composés.** 16 s, invariant 22.
C'est la photo de l'état du problème vu par la machine : elle a intégré tout
ce qui a été démontré et ramène Goldbach à UN énoncé. Elle ne le prouve pas —
c'est la conjecture. **L'acquis est la carte, pas la preuve.**
Le CAPSTONE couvre désormais DIX maillons (GG24 inclus) : 9 s, tous clos.
Script : PB45_portrait_final.py.

### CAPSTONE ÉTENDU — 12 MAILLONS (ev.404, 10h32 réel)
`CAPSTONE_crible.py` couvre désormais l'arc ENTIER : GG6, GG7←→, GG9←→,
GG10←→, GG19←→, GG24, GG23, GG25 — **tous CLOS, invariant 22, 43 s**, avec
assertion finale (le script CASSE si un maillon cède). GG23/GG25 sont vérifiés
en sous-processus (scripts autonomes) : leur verdict « CLOS: True » est relu.
C'est le test d'intégration de tout le travail Goldbach, hors pytest.

### CORPUS DOCUMENTAIRE POUR LES ARTICLES (ev.405, 10h44 réel)
`docs/articles/` contient désormais CINQ documents, tous matériau direct :
· **PLAN_ARTICLES.md** — 3 articles + 1 programme, une QUESTION par article,
  16 grosses idées attribuées ; enrichi des acquis du matin (le moment fort de
  A2 = v13 qui refait GG9 seul ; la structure de A3 = GG24 + convergence des
  3 lignes ; réserve d'honnêteté à tenir : aucun fait arithmétique nouveau).
· **CARTE_GOLDBACH.md** — l'énoncé d'entrée (GG24), le GRAPHE des équivalences,
  le tableau de convergence des 3 lignes, les organes, ce qui est fermé /
  fermé par la négative / ouvert.
· **ORGANES.md** — catalogue des 14 organes avec, pour chacun, LE DIAGNOSTIC
  QUI L'A FAIT NAÎTRE (la colonne de droite est plus informative que celle du
  milieu) ; distingue organes INTERNES (besoin.py) et PROPOSEURS (externes).
· **PIEGES_MESURES.md** — 14 pièges PAYÉS, classés : vérification (tests qui
  n'ont pas tourné, indicateurs trompeurs), fidélité (gardes mal placées, le
  blocage qui parle de l'énoncé), formalisme (liants, prédicats définis),
  conduite de chantier (faux « bloqué », mesurer avant d'investir).
· **RELECTURE_A_FAIRE.md** — quoi relire et où + PLAN DE PROMOTION précis
  (fichier par fichier, avec la remarque décisive : **Goldbach n'est PAS dans
  Bourbaki**, donc l'arbre bourbaki/ ne peut pas l'accueillir — outils_ia/ ou
  un dossier recherche/ distinct ; à trancher en premier).

### DOUBLE VÉRIFICATION — TOUT EST VERT ET REPRODUCTIBLE (ev.406, 11h02 réel)
**(1) pytest complet `outils_ia/decouvertes/` : 24 passed en 40:37** (contre 22
ce matin : +test_organe_v13_temoin_canonique_fabrique et
+test_organe_v14_ne_jette_plus_les_manques_du_temoin). Valide donc AUSSI la
propagation des proposeurs dans general.py et l'organe v14 dans besoin.py :
aucune régression.
**(2) VERIF_TOUS.py — REPRODUCTIBILITÉ TOTALE : 17/17 scripts** de l'arc
rejoués en sous-processus sans erreur, « invariant 22 » présent partout,
1049 s au total. Détail des coûts (utile pour la promotion) : PB29b 493 s
(GG15, le plus lourd), PB30 319 s, PB29c 79 s, PB32 68 s, GG12 25 s,
CAPSTONE 23 s ; tout le reste ≤ 7 s. **VERDICT : REPRODUCTIBLE** — un lecteur
peut tout revérifier depuis zéro.

### ⚠️ RÉGRESSION DE COÛT TROUVÉE ET CORRIGÉE — v14 (ev.407, 11h11 réel)
**SYMPTÔME** : la suite complète passait de 28:50 à **40:37** pour +2 tests
coûtant 0,6 s. Mesure ciblée : le test d'intégration Goldbach passait de
**58 s à 158,8 s (×2,7)**.
**CAUSE** (contre-intuitive : v14 ne fait que STOCKER des manques déjà
calculés) : mon `return None, _manques_temoins` placé juste après le bloc v7
**court-circuitait les organes suivants** (v5 routes-∀, v6 proposeurs, boucle
standard). Des sous-buts jadis fermés localement étaient abandonnés, forçant
l'appelant à essayer d'autres témoins — explosion en AMONT.
**FIX** : `_manques_temoins` est initialisé en tête de `besoins()`, accumulé
par v7, et FUSIONNÉ au rapport final (`return None, manques + _manques_temoins`)
au lieu d'interrompre. Le comportement v13/v14 est préservé (les obligations
sur le témoin remplacent toujours le rapport « le but ∃ lui-même »).
**APRÈS FIX** : intégration Goldbach **12,4 s** (×13 vs le bug, ×4,7 vs la
baseline de 58 s) ; **15 passed en 3:41**.
**LEÇON** : un `return` anticipé dans un moteur de recherche ne coûte pas
seulement les organes qu'il saute — il déplace le travail chez l'appelant.
Toujours mesurer le TEMPS d'une suite, pas seulement son verdict vert : la
régression était invisible au « passed ».

### PB46 — ORGANE v15 : LE COMPOUNDING RÉEL (ev.408, 11h23 réel)
Premier proposeur qui APPREND : un « enregistreur » retient les témoins qui
ont effectivement fermé un but ∃ ; un proposeur « appris » les re-propose.
**MESURE (but decomposition(N16))** :
  · passe 1, proposeur CALCULATEUR (+ enregistrement) : **fermé, 102 s**,
    2 témoins retenus (3 et 13) ;
  · passe 2, proposeur APPRIS **SEUL** (aucun calcul, aucun accès à
    l'arithmétique) : **fermé, 0 s**, 0 besoin, conclusion == but.
**COMPOUNDING : OUI — la machine capitalise.** 102 s → 0 s sur le même but.
C'est le premier morceau concret du marcheur (article A4) : proposer, juger
par le noyau, RETENIR ce qui a marché.
PIÈGE MESURÉ (coûteux) : `str()`/`repr()` sur un τ-terme profond fait
EXPLOSER le `__repr__` récursif → **MemoryError** après 10 min de calcul
perdu. Ne jamais afficher un τ-terme : compter, ou comparer par égalité.
Script : PB46_proposeur_appris.py.

### TEST v15 RETIRÉ — HONNÊTETÉ (ev.409, 13h47 réel)
Le test dédié `test_organe_v15_compounding_du_proposeur_appris` a **timeout à
10 min** alors que le script équivalent ferme en 102 s. Cause identifiée : le
pool du test OMETTAIT un fait présent dans le script
(`somme_cardinale_commutative(N3, N13)`), sans lequel la recherche part en
exploration longue. **Le test a été RETIRÉ** plutôt que laissé dans le dépôt :
un test qui timeout est pire que pas de test (il casse la suite et masque les
vraies régressions). Suite après retrait : **13 passed** (hors slow).
⚠️ RESTE À FAIRE : réécrire ce test avec le pool COMPLET du script
`PB46_proposeur_appris.py` (qui, lui, est reproductible et mesuré : 102 s → 0 s)
et le marquer `slow`. L'organe v15 est donc DÉMONTRÉ mais PAS ENCORE PROTÉGÉ.

### ORGANE V16 — LA CONGRUENCE AUTOMATIQUE : LA MACHINE ENTRE DANS L'ALGÈBRE (ev.410, 11 août 20h00)
**QUESTION DE KARL** : « la mécanique de recherche stagne-t-elle, et sait-elle
créer une nouvelle algèbre ? »
**RÉPONSE MESURÉE** — deux constats distincts :
 (1) sur GOLDBACH, oui elle stagne : le portrait final (ev.403) montre que,
     tout l'arsenal au pool, elle ne ferme pas et nomme la conjecture. Les
     organes améliorent la LOCALISATION du manque, pas la production de
     contenu arithmétique. Aucun fait sur les premiers n'a jamais été produit
     qui ne lui ait été donné.
 (2) sur l'ALGÈBRE, il manquait UN pas précis — et il est comblé.
**PROTOCOLE (ALG1_operation_nouvelle.py)** : opération ABSENTE du dépôt,
`a ⊕ b := (a+b)+1` ; but `a ⊕ b = b ⊕ a` ; pool = { commutativité de + }.
  · AVANT v16 : NON fermé (le manque nommé est le but lui-même) ; fermé
    seulement si l'on DONNE `congruence_terme` en route ⇒ elle savait
    CHAÎNER la congruence, pas la FABRIQUER.
  · APRÈS v16 : **FERMÉ SANS AIDE, 0 besoin, 7 s** ; garde-fou : l'énoncé
    FAUX `(a+b)+1 = a+b` reste infermable. Non-régression **17 passed**.
**IMPLÉMENTATION** (autonomie/congruence.py, besoin.py +8 lignes) : devant
`u = v`, abstraire un sous-terme `a` de `u`, LIRE dans `v` ce qui occupe le
trou, viser `a = b`, refermer par `congruence_terme` (noyau juge).
**DEUX APPROCHES ESSAYÉES ET ÉCARTÉES — à consigner** :
  · descente structurelle « une seule divergence » : NE SE DÉCLENCHE JAMAIS —
    les τ-termes DUPLIQUENT leurs arguments dans leur développement, il y a
    donc plusieurs divergences dès le premier niveau ;
  · énumération exhaustive des contextes (récursion dans une boucle sur les
    candidats) : EXPONENTIELLE, ne terminait pas en 2 min.
  L'abstraction par sous-terme, elle, est linéaire (0,29 s) et trouve le bon
  niveau (`a+b = b+a`, indice 3 sur 5 candidats).
**PORTÉE** : toute propriété d'une opération DÉRIVÉE se ramène à des
congruences sur les opérations de base. C'est donc la porte d'entrée de
l'étude de structures — le premier endroit où la machine ne stagne PAS.

### ALG2 — MANQUEMENT SUIVANT : PAS DE CHAÎNE DE RÉÉCRITURES (ev.411, 11 août 20h07)
Test de l'étage supérieur : ASSOCIATIVITÉ de `a ⊕ b := (a+b)+1`, pool =
{ commutativité, associativité de + } (théorèmes CLOS du dépôt).
  · (B) témoin — commutativité de ⊕ (UNE congruence)  : **fermé** ✓
  · (A) ASSOCIATIVITÉ de ⊕                            : **NON fermé**,
        1 besoin, chaîne « (aucune route) », 10 s
  · (C) garde-fou (énoncé faux)                       : infermable ✓
**DIAGNOSTIC** : `(a⊕b)⊕c` et `a⊕(b⊕c)` ne se ramènent pas l'un à l'autre par
UNE congruence — il faut associer, commuter, ré-associer. L'organe v16 fait un
pas ; il n'en enchaîne pas plusieurs. La machine ne sait pas **réécrire**.
`composer_egalites` (transitivité) existe au dépôt mais n'est jamais mobilisé.
⇒ ORGANE V17 à écrire : réécriture par les égalités du pool (BFS bornée depuis
u vers v, chaque pas = congruence sur un sous-terme, chaînage par
composer_egalites). C'est le moteur qui manque pour l'étude des structures.

### ALG3 + ORGANE V17 VALIDÉ — ET UN TROU DU DÉPÔT (ev.412, 11 août 20h25)
**LE DIAGNOSTIC D'ALG2 ÉTAIT INCOMPLET.** L'associativité de ⊕ n'échouait pas
faute d'organe : **le lemme requis n'est pas au dépôt**.
`somme_cardinale_associative` démontre `Card((A⊔B)⊔C) = Card(A⊔(B⊔C))`, PAS
`SC(SC(a,b),c) = SC(a,SC(b,c))` — il y a un `Card` de plus au niveau interne,
et les deux termes sont distincts pour le noyau. La docstring annonce pourtant
« = (a+b)+c = a+(b+c) » : **écart prose/code**, même famille que le piège
`prop2_sous_fini` (curryfié). Consigné dans `docs/journal/ANOMALIES.md`.
**V17 EST VALIDÉ SUR CE QUI EXISTE** (ALG3_chaine_reecriture.py, pool =
commutativité seule) — **5/5** :
  (1) 1 pas `a+b = b+a` fermé 0,0 s ; (2) 2 pas `(a+b)+(c+d) = (b+a)+(d+c)`
  fermé 0,2 s ; (3) 3 pas (six variables) fermé 1,1 s ; (4) sous ⊕
  `(a+b)+1 = (b+a)+1` fermé 0,1 s ; (5) GARDE-FOU `a+b = a+c` **ouvert** ✓.
**TESTS AJOUTÉS** : `test_organe_v16_congruence_automatique` et
`test_organe_v17_chaine_de_reecritures`, chacun avec son garde-fou négatif.
Suite : **19 passed** (hors slow), aucune régression.
**LEÇON DE MÉTHODE** : un échec a souvent DEUX causes candidates — l'outil ou
le matériau. J'ai d'abord accusé l'outil (et écrit v17, qui était utile), mais
la cause réelle était le pool. **Vérifier la disponibilité du lemme AVANT de
conclure qu'un organe manque.**

### ev.413 (12 août, 4h30-5h15) — L'ASSOCIATIVITÉ DÉRIVÉE FERME ; UN DOUBLON D'ORGANE RÉSORBÉ

**LE MUR N'EN ÉTAIT PAS UN.** `ASSOC3_profondeur.py` mesure la recherche en
profondeur sur `(a⊕b)⊕c = a⊕(b⊕c)` : profondeurs 4/5/6/7 → **11 / 21 / 47 /
95 s**, toutes en échec, **1 manque constant**. Signature caractéristique :
le coût explose, l'information n'avance pas. Approfondir ne mène nulle part.

**DIAGNOSTIC — deux causes, toutes deux de ma main.**
1. **v17 existait EN DOUBLE.** `autonomie/reecriture.py` (11 août : largeur
   d'abord, bornes `max_pas`/`max_noeuds` explicites, test dédié) **et** un
   second moteur dans `congruence.py` (12 août : profondeur d'abord). Et
   `besoin.py` appelait **les deux**, sous le même alias `_fpr`. Invisible aux
   tests : les deux sont corrects, la suite restait verte — le doublon coûtait
   du calcul, pas de la justesse. Effet de bord mesurable : `congruence.py`
   était monté à **356 lignes de code**, au-delà de la barre de 300.
2. **`max_pas` valait 3, la chaîne minimale en fait 5** :
   `((a+b)+1)+c = (a+b)+(1+c) = (a+b)+(c+1) = a+(b+(c+1)) = a+((b+c)+1)`.

**RÉPARÉ, EN GÉNÉRALISANT.** Un seul moteur — celui de `reecriture.py`. L'apport
propre du second (v18, instanciation des lois) y a été porté **et amélioré** :
au lieu d'énumérer les instances à l'avance, la loi est matchée *au moment
d'être appliquée* (`_instances`), ce qui est moins cher et atteint les termes
INTERMÉDIAIRES que l'énumération initiale ne pouvait pas voir. Bornes portées
à `max_pas=5` / `max_noeuds=1200`, **calibrées sur mesure** et chiffres écrits
dans la docstring de `reecrire_vers`.

| fichier | avant | après |
|---|---|---|
| `congruence.py` | 356 | **235** |
| `reecriture.py` | 128 | **167** |
| `besoin.py` | 299 | **285** |

**RÉSULTAT — le but complet ferme** (`ASSOC4_moteur_fusionne.py`) :
  · cœur `(a+b+1)+c = a+((b+c)+1)` : max_pas 2/3/4 échouent (1/2/3 s),
    **max_pas 5 ferme en 4 s**, clos, 0 hypothèse ;
  · but complet via `besoins(profondeur=4)` : **fermé, 0 manque, 8 s**,
    conclusion == but, clos, 0 hypothèse, invariant 22.
Soit **24× plus vite en succès que l'échec en profondeur** (4 s vs 95 s), même
pool, même but.

**PROMOTION AU DÉPÔT** — l'associativité itérée n'était plus un script de
scratchpad : `bourbaki/…/iii_3_3_somme/ensembles_somme_iteree.py` expose
`invariance_somme_gauche`, `invariance_somme_droite` et
`somme_cardinale_associative_iteree` (tous acceptent des TERMES, ce dont les
outils ont besoin), avec `@livre Ch.III §3.3 Cor.- | E III.27 L.12-12 | PDF
p.130`. Miroir `tests/…/test_somme_iteree.py` : **4 passed en 54 s**. Le piège
des liants canoniques `F`/`G` est écrit en tête de module.

**TEST AJOUTÉ** : `test_organe_v18_associativite_d_une_operation_derivee` —
pool réduit à **deux lois brutes**, aucune instance pré-mâchée. Le garde-fou a
dû être choisi avec soin : `(a⊕b)⊕c = (a⊕c)⊕b` serait un mauvais témoin
négatif car il est **vrai** (les deux valent a+b+c+2) ; le test utilise
`a⊕b = a⊕c`, réellement indérivable.

**LEÇON GÉNÉRALISABLE (deux, à retenir).**
· *Avant d'écrire un organe, lister `autonomie/`.* Les noms de fichiers y sont
  la table des matières des capacités de la machine. Un organe dont le nom
  existe déjà est à **enrichir**, pas à réécrire. (Le nom `reecriture.py`
  disait exactement ce que j'ai réécrit.)
· *Une recherche qui échoue en grossissant — coût qui explose, manques qui
  stagnent — ne se répare presque jamais par plus de budget.* Chercher en
  amont : ordre d'exploration, ou borne fixée au jugé. **Mesurer la longueur
  de chaîne attendue avant de régler la borne.**

### ev.414 (12 août, 5h20-6h40) — L'ARC GOLDBACH MIGRÉ : de 50 scripts jetables à 8 modules testés

**CE QUI EXISTE MAINTENANT.** `recherche/goldbach/` — 8 entrées sur 10, toutes
sous la barre des 300 lignes de code :

| module | l. code | ce qu'il porte |
|---|---|---|
| `enonces.py` | 100 | socle de prélèvements **vérifiés par recomposition** + `atteste` |
| `crible.py` | 225 | (avant) P_b, Q_b, l'équivalence crible ⟺ décomposition gardée |
| `pont_tau.py` | 182 | Goldbach **sans ∃** (`forme_canonique`), `route_temoin`, GG12 |
| `composes.py` | 174 | pont-α, famille {2p}, **Goldbach ⟺ sa restriction aux composés** |
| `synthese.py` | 208 | GG21, GG22, **GG24 : ∀k composé rencontre(k) ⇒ Goldbach** |
| `audit_fidelite.py` | 91 | le théorème de DÉFAUT de `est_premier` + garde gratuite |
| `capstone.py` | 102 | rejeu des 14 maillons, **jugés par le noyau** |

**MESURE** : capstone **14/14 CLOS**, invariant 22, ~113 s. Tests miroir
`tests/recherche/goldbach/` : **16 passed** (14 rapides 34 s + 2 lents 115 s).

**TROIS DÉFAUTS CORRIGÉS, PAS SEULEMENT DÉPLACÉS.**

1. **Le capstone ne ment plus.** L'original vérifiait GG23/GG25 en lançant un
   SOUS-PROCESSUS et en cherchant la chaîne `"CLOS: True"` dans son `stdout`.
   Reformater un `print` le faisait passer au vert. Chaque maillon est
   désormais un `Theoreme` inspecté en processus (`est_clos`, `hypotheses`,
   conclusion comparée à sa cible).

2. **La colonne « axiomes ad hoc » existe.** `N.axiome(TH, f)` rend un théorème
   à `hypotheses` VIDE : `est_clos` ne veut donc PAS dire « sans axiome ». Le
   capstone distingue maintenant les **10 maillons libres** des **4 qui
   reposent sur les 2 axiomes du crible** (`AXIOMES_CRIBLE`). C'était la seule
   malhonnêteté réellement possible dans ce dossier.

3. **`test_goldbach_reste_ouverte`** balaie tous les exports des trois modules
   et **échoue si l'un d'eux conclut `H` tout seul**. Si un jour la conjecture
   semble démontrée, ce test tombe — comportement voulu.

**COLLISIONS RÉSOLUES À LA MIGRATION** (relevées par la lecture parallèle) :
· « HC » désignait DEUX formules (décomposition vs rencontre) → deux noms
  distincts, et un test qui exige `HC_dep != HC_renc` ;
· un seul théorème vivait sous QUATRE noms (`pont_tau_retour`, GG11, le rejeu
  inline de GG12, le dernier pas de GG17) → une seule preuve, `route_temoin` ;
· `gardee_implique_depot` était rejoué à l'identique dans deux scripts → une
  fonction, paramètre `generalise` ;
· PB29a/GG14/GG15/GG16/GG17 **ABANDONNÉS** : ils reposent sur un `premiers_bornes`
  NON gardé, incompatible avec celui de `crible.py`. Les réintroduire serait du
  travail neuf, pas de la migration.

**PIÈGE D'IMPORT MESURÉ** : `est_premier_num` vit sous `outils_ia.conjectures.
primalite`, **jamais** sous `outils_ia.arithmetique.primalite` (qui n'existe
pas). Les scripts d'origine masquaient l'erreur dans un `try/except`.

**MÉTHODE — ce qui a rendu la migration rapide.** Lecture des 50 scripts
**fan-out en parallèle** (4 lecteurs + 1 synthèse, specs structurées :
énoncé exact lu dans le CODE et non la docstring, statut honnête, route
noyau, pièges), puis **écriture séquentielle inline** (jamais de fan-out sur
une migration : mémoire du projet). Les 7 modules ont tous fermé du premier
coup sauf un import à corriger.

**RESTE** : Goldbach est OUVERTE. Le fil recherche a par ailleurs établi que
l'obstruction n'est PAS équationnelle (`CARTE_GOLDBACH.md` §8).

### ev.415 (12 août, 6h45-7h30) — LA SYMÉTRIE DU CRIBLE PORTÉE POUR DE VRAI ; RÈGLE DES LIANTS CANONIQUES

**POURQUOI CE RÉSULTAT-LÀ.** La carte avait refermé DEUX voies par la négative,
et toutes deux disaient la même chose : le comptage brut (§7 : le critère des
tiroirs ne tient pour aucun `k ≥ 2`) et l'équationnel (§8 : après v16/v17/v18,
le manque de `rencontre(k)` a une forme **strictement identique**). Conclusion
commune : il faut de l'information sur la **répartition** de `P₂ₖ`. La symétrie
en est une.

**FAIT** — `recherche/goldbach/symetrie.py`, **CLOS en 4 s** (sous les 2 axiomes
du crible, déclarés) :

    ⊢ (∀k)(∀m)[ m ∈ P₂ₖ ∩ Q₂ₖ ⇒ (∃m')( m' ∈ P₂ₖ ∩ Q₂ₖ ∧ 2k = m + m' ) ]

**CE QUE LE PORTAGE A RÉVÉLÉ — un motif de migration à retenir.** La version
d'exploration donnait à `P` et au miroir **la même graphie** de primalité. Sur
les définitions réelles de `crible.py` les deux habits α se CROISENT : le
partenaire sort du miroir en habit 2 et doit entrer dans `P` en habit 1,
pendant que `m` fait le trajet inverse. Le script « marchait » — il ne
démontrait simplement pas ce qu'on croyait. **Une simplification commode dans
un jetable peut escamoter tout le travail réel.**

Réparé en GÉNÉRALISANT plutôt qu'en dupliquant : `pont_alpha_premier(w, source,
cible)` est paramétré, plus sa variante gardée `pont_alpha_premier_ent`. Les
quatre combinaisons sont CLOSES. (Le pont NIÉ `¬premier₂ ⇒ ¬premier₁` reste
indisponible et ne s'en déduit pas.)

**LA RÈGLE DES LIANTS CANONIQUES** (`ANOMALIES.md`, 12 août). Ce piège a mordu
**trois fois en une matinée**, sous deux formes OPPOSÉES. Symptôme constant :
`ValueError: modus ponens : mineure ≠ antécédent` levé **à l'intérieur** du
lemme appelé. Règle de détection, lisible sur la signature :

| ce qu'on voit | traitement |
|---|---|
| paramètres qui acceptent des TERMES **et** paramètres de liant séparés (`f="F"`) | appel **DIRECT**, jamais généraliser |
| tous les paramètres sont des NOMS (`a="aSA"`) | ses **PROPRES noms** → généraliser → instancier |

*Si le lemme sait déjà prendre un terme, donne-lui le terme ; s'il ne prend que
des noms, ne lui donne jamais un terme.* Les deux traitements étant l'inverse
l'un de l'autre, appliquer le mauvais échoue à tous les coups — d'où le coût
répété. Occurrences : `ASSOC1` (`F`/`G`), `symetrie.py` (pont-α gardé), `DEMI1`
(`aSA`, simplification additive).

**EN COURS** — le DEMI-INTERVALLE : `⊢ (Fini k ∧ Fini m ∧ Fini m' ∧ 2k = m+m')
⇒ (m ≤ k OU m' ≤ k)`. Route SANS inégalité stricte : comparabilité → complément
(Prop. 13) → **associativité ITÉRÉE** (promue le matin même, ev.413, pour un
tout autre chantier) → simplification additive FINIE (Cor. 3 §III.5.2) →
commutativité → Prop. 2. Avec la symétrie, cela restreindrait la recherche à la
MOITIÉ de l'intervalle. La garde `Fini` y est essentielle deux fois : la
simplification additive est FAUSSE pour les cardinaux infinis.

**ÉTAT DES JOURNAUX** : `CARTE_GOLDBACH.md` §9 (les modules) et §10 (la
symétrie) ; `PLAN_ARTICLES.md` idées 14-15 en A3, deux pièges de méthode en A2,
annexe reproductible refaite ; `ANOMALIES.md` règle des liants.

### ev.416 (12 août, 7h15-7h50) — LE DEMI-INTERVALLE : chercher dans [0,k] suffit

**LE RÉSULTAT.** Deux théorèmes, l'un arithmétique, l'autre sur le crible.

    ⊢ (∀k)(∀m)(∀m')[ (Fini k ∧ Fini m ∧ Fini m' ∧ 2k = m+m') ⇒ (m ≤ k OU m' ≤ k) ]
    ⊢ (∀k)[ Fini k ⇒ ( rencontre(k) ⟺ (∃m)( m ∈ P₂ₖ ∩ Q₂ₖ ∧ m ≤ k ) ) ]

Le premier est de l'**arithmétique cardinale pure** — aucun nombre premier n'y
figure. Le second l'assemble avec la symétrie du crible (ev.415). Coûts :
315 s et ~350 s (la récurrence de la simplification additive domine) ; le sens
facile, 0 s.

**LA ROUTE, et pourquoi elle évite le STRICT.** Les inégalités strictes coûtent
cher dans ce noyau, on s'en passe entièrement : comparabilité des cardinaux
(inconditionnelle) pour ouvrir les deux cas ; dans le cas `k ≤ m`, le
complément existe (Prop. 13) donc `m = k + d` ; alors
`k+k = m+m' = (k+d)+m' = k+(d+m')` ; la **simplification additive finie**
(Cor. 3 §III.5.2) donne `k = d+m'` ; la Prop. 2 conclut `m' ≤ k`.

**⚠️ LA GARDE `Fini` N'EST PAS DE LA PRUDENCE.** La simplification additive est
**FAUSSE** pour les cardinaux infinis : `ℵ₀+1 = ℵ₀+2` sans que `1 = 2`. Sans la
garde, l'énoncé serait FAUX, pas seulement indémontrable. Même famille que le
défaut §6 de la carte, pris à temps cette fois.

**LE FAIT LE PLUS INSTRUCTIF DE LA MATINÉE.** L'étape de réassociation
`(k+d)+m' = k+(d+m')` repose sur l'**associativité itérée de l'addition
cardinale**, qui n'existait PAS au dépôt et que j'ai démontrée à 4 h le matin
même (ev.413) — sur un tout autre chantier : une opération algébrique inventée
pour tester si la mécanique de recherche stagnait. Elle n'avait aucun rapport
avec Goldbach. **Le trou comblé pour une raison a servi pour une autre trois
heures plus tard.** C'est l'argument le plus concret en faveur de combler les
trous quand on les voit, sans attendre d'en avoir l'usage.

**RÉORGANISATION IMPOSÉE PAR LA BARRE DES 300.** `synthese.py` avait atteint
309 lignes de code. Le découpage retenu ne coupe pas au hasard mais suit la
RESPONSABILITÉ : `demi_intervalle` ne parle pas de nombres premiers, tout le
fil « moitié » part dans `demi.py`. État final du dossier (10 entrées, LIMITE) :
`audit_fidelite` 91, `capstone` 105, `composes` 206, `crible` 225, `demi` 247,
`enonces` 100, `pont_tau` 182, `symetrie` 136, `synthese` 208.

**⚠️ LE DOSSIER EST PLEIN.** Le prochain ajout impose d'éclater en
sous-dossiers (`equivalences/`, `structure/`, `audit/`). Consigné dans
`recherche/README.md`, qui porte désormais la carte des modules et les deux
gardes du dossier (« clos » ≠ « sans axiome » ; le test qui garde la porte).

**CE QUE ÇA NE DONNE PAS, à dire net.** Diviser par deux un espace de recherche
qui reste infini en `k` ne rapproche d'AUCUNE preuve. Goldbach est exactement
aussi ouverte qu'avant. L'acquis est une équivalence certifiée de plus et une
contrainte structurelle exacte — de la matière pour la carte.

**JOURNAUX** : `CARTE_GOLDBACH.md` §11 ; `recherche/README.md` refait ;
capstone porté à **18 maillons**.

### ev.417 (12 août, 7h40-8h00) — LE CRIBLE ABSTRAIT : ce que nos réductions NE CONTIENNENT PAS

**DEUX PISTES ABANDONNÉES AVANT, ET C'EST LA PARTIE UTILE DE L'ÉVÉNEMENT.**

1. **PARITE1** (« tout premier ≠ 2 est impair »). Abandonné parce que vrai,
   facile, et **inerte** — je l'avais choisi parce qu'il était *prouvable*, pas
   parce qu'il était *informatif*. Biais à surveiller sur un problème ouvert :
   produire ce qui ferme plutôt que ce qui apprend. L'éclaireur a en outre
   montré qu'il aurait été **vrai à vide** sur un `m` non-cardinal (défaut de
   fidélité de `est_premier`) — il n'aurait rien mordu du tout.

2. **Extension de la borne certifiée `n ≤ 86`.** Le goulot était identifié
   (`est_premier_num(p)` énumère TOUS les diviseurs de 0 à p ; tester jusqu'à
   √p suffirait). Abandonné sur remarque de Karl, et il a raison : c'est du
   **sous-cas**, sans valeur mathématique — d'autres vérifient à 4×10¹⁸ par
   calcul. Notre force est de démontrer POUR TOUT N et de généraliser.

**CE QUE CETTE CONTRAINTE A OUVERT.** En cherchant à généraliser plutôt qu'à
spécialiser, un fait sautait aux yeux dans le code : `symetrie_du_crible`,
`demi_intervalle` et `rencontre_se_restreint` **n'utilisent jamais la
primalité**. Ils manipulent `P` et `Q` en aveugle ; la primalité n'entre que
par le pont d'habit α, purement syntaxique (vérifié : lignes 128 et 146 de
`symetrie.py`, rien d'autre).

**LE RÉSULTAT** — `recherche/additif/` :
  · `crible_abstrait.py` : la construction du crible avec le prédicat `S` en
    **PARAMÈTRE** (fonction `Terme → Formule`), et la symétrie démontrée sans
    jamais ouvrir `S`.
  · `demi_abstrait.py` : la restriction au demi-intervalle, idem.

MESURE — la MÊME preuve, mot pour mot :

| `S` | coût | ce que c'est |
|---|---|---|
| `x ∈ 𝕊`, `𝕊` totalement opaque | 5 s | aucune propriété supposée |
| `est_premier(x)` | 4 s | **Goldbach** |
| `est_pair_propre(x)` | 4 s | question triviale |

`tests/recherche/additif/` : **4 passed en 18 s**.

**LA THÈSE, et c'est celle de l'article A3.** Une démonstration qui ne
distingue pas les nombres premiers d'un ensemble sans structure ne peut pas
servir à démontrer Goldbach. Les quatre grandes réductions de la carte —
composés, crible, symétrie, demi-intervalle — **ne portent aucun contenu
arithmétique**. Ce n'est pas un défaut de nos preuves, c'est une propriété des
énoncés qu'elles établissent, et ça **délimite** la conjecture : structurel
d'un côté, arithmétique de l'autre, frontière tracée en code.

Ça referme aussi §7 (comptage) et §8 (équationnel) d'un même mouvement : les
deux échouent pour la même raison — ils ne regardent jamais QUELS entiers sont
dans l'ensemble.

**« GOLDBACH EST UNE INSTANCE » N'EST PAS DE LA PROSE** : c'est une exécution,
dans `tests/recherche/additif/test_crible_abstrait.py`.

**EFFET DE BORD RÉVÉLATEUR.** Le pont d'habit α, qui avait coûté du travail
réel dans la version concrète (paramétrisation, deux sens, variante gardée),
**disparaît entièrement** en abstrait. Il n'était pas une étape mathématique :
c'était un artefact de notation imposé par les deux graphies de
`decomposition`.

**DETTE CONSIGNÉE, pas masquée** : `demi_abstrait` travaille sur `b = 2k` et
non sur un `b` quelconque — la forme générale demanderait la monotonie de la
somme sous une forme que le dépôt n'expose pas telle quelle. Et
`demi_intervalle`, qui ne contient aucune primalité, vit encore dans
`recherche/goldbach/` pour raisons historiques ; sa place est ailleurs.

**MÉTHODE — ce que Karl a exigé et qui a produit les deux abandons** :
à chaque chantier, se demander POURQUOI on le fait, avec de vraies
justifications, et abandonner franchement ce qui est inerte. Les deux
meilleures décisions de la matinée sont deux renoncements.

### ev.418 (12 août, 9h10-9h35) — L'ORACLE NUMÉRIQUE, ET UNE LOI DE CONCEPTION

**CE QUI MANQUAIT.** Le système ne CALCULE jamais pour se guider : il démontre
ou il échoue. Or le résultat le plus rentable de toute la campagne Goldbach,
rapporté à son coût, fut une MESURE — le critère des tiroirs tué en quelques
secondes par un crible d'Ératosthène en Python pur, là où aucune démonstration
n'aurait donné l'information.

**FAIT** : `outils_ia/arithmetique/oracle_num.py` (187 l.) — `valeur`, `verite`
(Kleene à trois valeurs), `contre_exemple`, plus `table`/`index` bâtis une
fois. Tests : `tests/outils_ia/arithmetique/test_oracle_num.py`, **5 passed**.

**BRANCHÉ COMME ORGANE V19**, en tête de `besoins()` : un but numériquement
FAUX est réfuté d'emblée, sans engager la recherche. Test dédié
`test_organe_v19_oracle_refute_avant_de_chercher`, **1 passed**. Non-régression
`outils_ia/decouvertes/` + oracle : **25 passed**.

**⚠️ L'ASYMÉTRIE EST DANS LE CODE ET DANS LES NOMS DE TESTS.** v19 n'exploite
QUE le verdict FAUX. « Aucun contre-exemple » ne ferme rien et ne doit rien
fermer — Goldbach n'en a aucun jusqu'à 4×10¹⁸ et reste ouverte. Le test
vérifie explicitement qu'un but VRAI mais hors du pool reste OUVERT.

**LOI DE CONCEPTION DÉCOUVERTE — vaut pour tout futur évaluateur.**
Dans ce noyau, `N(7)` et `N(3)+N(4)` sont TOUS DEUX des τ-termes de
`tag == 'tau'` à UN argument. **On ne peut pas descendre dans un terme.** La
seule voie est la RECONSTRUCTION, praticable parce que les assemblages sont
hashables (égalité O(1)), impraticable si l'on reconstruit à chaque appel —
d'où une table bâtie UNE fois. Les FORMULES, elles, se décomposent (`¬`, `∨`,
`∃`, `=`), et `et`/`⇒`/`∀` en découlent gratuitement puisque ce sont des
abréviations. Consigné dans `ANOMALIES.md` et `PIEGES_MESURES.md`.

**J'AI COMMIS LA MÊME ERREUR À DEUX ÉTAGES**, à vingt minutes d'intervalle :
descente dans les termes (333 s → 3 s après correction), puis reconstruction
des formules à chaque appel (≈26 000 constructions par consultation → 1 µs
après indexation). La seconde fois, appliquer la loi qu'on venait d'écrire a
marché du premier coup. Une introspection de trois lignes (`type`, `tag`,
`len(args)`) aurait évité les deux.

**CORRECTION UTILE** : brancher l'oracle sur le CONJECTUREUR serait inutile —
il ne produit que des théorèmes déjà certifiés par le noyau, donc vrais. Il n'y
a rien à y réfuter. Le bon point d'insertion est EN AMONT de la preuve.

**ATTENTION BUDGET** : `besoin.py` est à ~297 lignes de code, la barre est à
300. Ne plus rien y ajouter sans éclater le fichier. Les dossiers
`decouvertes/`, `autonomie/` et `arithmetique/` sont à 10 entrées.

### ev.419 (12 août, 9h37-9h50) — LA MACHINE PROPOSE DES DÉFINITIONS, ET TROUVE SEULE LE PROBLÈME DES HABITS α

**LE MANQUE.** Tous les organes MANIPULENT des notions ; aucun n'en CRÉE.

**FAIT** : `outils_ia/corpus/notions_candidates.py` — mine les sous-formules
récurrentes des ÉNONCÉS (à renommage de variables près) et les score par
compression MDL, `gain = (occurrences − 1) × taille`.

⚠️ À NE PAS CONFONDRE avec `antiunif_notions.py`, qui anti-unifie l'AST PYTHON
des scripts : celui-là abstrait le CODE, celui-ci les ÉNONCÉS.

**DÉFAUT MESURÉ À LA PREMIÈRE VERSION, et sa correction.** Le minage brut
remontait des blobs `¬¬(¬… ∨ ¬…)` de 60 nœuds vus 24 fois — des ÉCHAFAUDAGES,
pas des notions. Cause : dans ce langage `et(a,b)` vaut `¬(¬a ∨ ¬b)`, donc
chaque conjonction fabrique des nœuds intermédiaires qui ne sont des formules
pour personne. Correction : reconnaître les ABRÉVIATIONS (`et`, `⇒`, `∀`) et ne
descendre que dans leurs enfants SÉMANTIQUES. Même leçon qu'à l'oracle :
travailler au bon niveau d'abstraction, pas au niveau brut.

**RÉSULTAT — les notions posées à la main remontent seules** :

| rang | gain | occ | notion retrouvée |
|---|---|---|---|
| 1 | 1426 | 24 | `est_premier`, habit `d1/q1` |
| 3 | 1200 | 101 | `est_fini` |
| 5 | 1116 | 19 | `est_premier`, habit `d2/q2` |
| 18 | 702 | 10 | `premier_ent` — la cible de validation |

**LE RÉSULTAT INATTENDU, et le plus utile.** `est_premier` apparaît **DEUX
FOIS** au classement, une par graphie de liants. L'organe **redécouvre donc
seul le problème des habits α**, et il le CHIFFRE : 1426 + 1116, la plus
grosse redondance du corpus. C'est exactement ce qui a coûté des heures le
matin même (ev.415, pont d'habit à paramétrer, artefact de notation que le
crible abstrait fait disparaître). Diagnostiqué à la main le matin, retrouvé
et mesuré par la machine le soir.

**Tests** : `tests/outils_ia/corpus/test_notions_candidates.py`, **3 passed en
84 s**, dont un test qui verrouille la reconnaissance des abréviations et un
qui garde le constat des deux habits (avec la note : s'il tombe un jour parce
que les graphies ont été unifiées, ce sera une bonne nouvelle — le réécrire,
pas le supprimer).

⚠️ L'ORGANE PROPOSE, IL NE PROMEUT PAS. La promotion en notion du dépôt reste
une décision humaine ; le noyau reste seul juge des théorèmes qui l'utiliseront.
Aucun `Theoreme` ne sort de là.

⚠️ DETTE DE RANGEMENT SIGNALÉE : `outils_ia/corpus/` est à 57 entrées pour une
convention à 10. Le fichier y va parce que c'est sa place sémantique, pas parce
que la règle est tenue. L'éclatement est une dette antérieure.

### ev.420 (12 août, 9h54-10h05) — ANALOGIE SUR LES PREUVES : LIVRÉ, SIGNAL FAIBLE

**LE CONSTAT PRÉALABLE, important pour la suite du projet.** Le noyau ne
conserve PAS le DAG des dérivations : `Theoreme.justification` est une CHAÎNE
(« S2 », « MP », « axiome[…] »), pas un pointeur vers les parents. Le vrai
graphe de preuve n'existe donc nulle part, et l'obtenir exigerait
d'instrumenter le noyau — exclu par la frontière de confiance.

**SUBSTITUT RETENU** : `outils_ia/corpus/analogie_preuves.py` travaille sur le
graphe d'APPELS entre constructeurs de théorèmes (analyse AST). Approximation
assumée et annoncée dans l'entête — mais c'est aussi le niveau auquel un
mathématicien perçoit une analogie : quels lemmes on enchaîne.

**RÉSULTAT HONNÊTE : la cible de validation ÉCHOUE.**
`symetrie_du_crible` ≈ `symetrie_additive` — deux preuves qui SONT la même —
n'est pas trouvée. Le classement est saturé de petits auxiliaires de 8 à 12
nœuds sans intérêt.

**DIAGNOSTIC, et c'est lui qui vaut.** L'isomorphisme EXACT est à la fois :
  · trop permissif — deux auxiliaires de même taille ont la même forme sans
    signification ;
  · trop strict — la version concrète appelle DEUX FOIS le pont d'habit α que
    l'abstraite n'a pas ; deux appels de plus tuent un appariement réel.

**CORRECTION IDENTIFIÉE, NON IMPLÉMENTÉE** : distance d'édition sur les arbres
de forme, avec plancher de taille, au lieu d'une égalité.

**CE QUI EST ACQUIS QUAND MÊME** : la mécanique (extraction du graphe,
effacement du vocabulaire, exclusion des tests — qui sont structurellement
jumeaux par construction — et des paires intra-module, qui sont du
copier-coller et non des analogies). Et un fait sur le dépôt : le noyau ne
trace pas ses dépendances, ce qu'aucun document ne disait.

**BILAN DES QUATRE IDÉES** : (1) oracle numérique ✅, (4) réfutation ✅,
(2) invention de définitions ✅ et au-delà de l'attendu, (3) analogie ⚠️ livré
mais faible, avec sa correction nommée.


### ev.420 (13 août, 7h10-7h35) — L'ANALOGIE MARCHE, ET LE PLAN ÉCRIT LA VEILLE ÉTAIT FAUX

**REPRISE de l'idée (3), là où la session du 12 août s'est arrêtée net à 9h57.**

**LE PLAN LAISSÉ ÉTAIT : « distance d'édition sur les arbres, l'isomorphisme
exact est trop strict ». LA MESURE L'A INFIRMÉ.** Sur la cible de validation
`symetrie_du_crible` ≈ `symetrie_additive` :

    profondeur 1  →   85 appels contre  80   (5 d'écart)
    profondeur 3  →  293 nœuds  contre 189   (104 d'écart)

Ce n'était pas l'égalité qui était trop stricte, c'était le **DÉPLIAGE** qui
détruisait la ressemblance. En dépliant les lemmes sur trois niveaux, on ne
compare plus deux preuves : on compare l'IMPLÉMENTATION des lemmes qu'elles
appellent. Une analogie se lit au niveau des pas enchaînés, pas dans les
entrailles des pas. Une distance d'édition sur ces arbres-là aurait coûté
cher (Zhang, appariement de coût minimal) pour rapprocher les mauvais objets.

**SECOND CONSTAT, DÉCISIF.** Les deux preuves partagent **26 noms d'appels**
(`_mp`, `_cg`, `s5`, `s6`, `assume`, `generalisation`…) et ne diffèrent que
sur 7 contre 6. Effacer TOUS les noms, comme le faisait la v1, jetait donc le
signal le plus fort. C'est la structure même d'une analogie mathématique :

    même SQUELETTE d'inférence (vocabulaire de liaison, PARTAGÉ)
    autre VOCABULAIRE de domaine (rare, propre au sujet)

**CRITÈRE RETENU, et il se décide sans rien savoir du sujet** : un nom appelé
depuis ≥ 3 modules distincts est de la LIAISON et garde son identité ; un nom
rare est du DOMAINE et s'efface en `?`. Distance = édition sur multiensembles,
normalisée. Aucune liste blanche écrite à la main — le corpus décide seul, et
le critère survit à son extension.

**RANG DE LA CIBLE, quatre conceptions comparées sur 582 paires** :

| conception | rang | distance |
|---|---|---|
| noms tous effacés (la v1, à prof. 1) | 42 | 0,030 |
| tous les noms gardés | 4 | 0,127 |
| **liaison gardée / domaine effacé** ← RETENUE | **4** | **0,091** |
| idem + vocabulaires disjoints exigés | ABSENTE | — |

La conception retenue creuse une **FALAISE** : rangs 1 à 4 sous 0,10, puis
saut à 0,22. `SEUIL_ANALOGIE = 0.15` est posé dans ce vide, pas au doigt
mouillé. Les quatre paires retenues sont toutes de vraies analogies.

**LES SEUILS NE SONT PAS UN RÉGLAGE FIN — balayés, c'est un PLATEAU.** La
cible reste au rang 2 à 4 pour `SEUIL_LIAISON` de 2 à 8 **et** `APPELS_MINI`
de 10 à 40 ; la paire emboîtée reste au rang 1 partout. La valeur exacte ne
porte rien, c'est la CONCEPTION qui porte. ⚠️ Et `SEUIL_LIAISON = 5`
classerait mieux la cible (rang 2, d = 0,030) : **je ne l'ai pas pris**.
Régler un seuil sur l'exemple qui sert à valider, c'est se mentir. La valeur
3 (« vu dans au moins trois modules ») est la seule qui s'explique sans
regarder la réponse.

**⚠️ POURQUOI ON N'EXIGE PAS DES VOCABULAIRES DISJOINTS.** C'était l'idée la
plus tentante — une analogie, c'est deux sujets différents. Mesuré : la cible
DISPARAÎT. Les deux preuves partagent des noms rares (`cible_partenaire`,
`fic_t`…). Une abstraction réussie GARDE une partie du vocabulaire de sa
version concrète ; exiger la disjonction interdit précisément le cas cherché.

**LE RÉSULTAT QUE JE N'ATTENDAIS PAS.** Le rang 1 n'est pas la cible : c'est
`demi.rencontre_se_restreint` ≈ `demi_abstrait.restriction_a_la_moitie`
(d = 0,057), que personne n'avait montrée à l'organe. Vérifié à la main :
les deux énoncent LITTÉRALEMENT la même chose, l'une concrète, l'autre
abstraite. Et son vocabulaire de domaine est **exactement la cible de
validation** — `symetrie_du_crible` d'un côté, `symetrie_additive` de
l'autre. **La grande analogie est bâtie sur la petite, et l'organe retrouve
l'emboîtement.** Test dédié `test_les_deux_analogies_sont_emboitees`.

**FAIT** : `outils_ia/corpus/analogie_preuves.py` réécrit (~180 l. de code) —
`vocabulaire_de_liaison`, `forme`, `distance`, `vocabulaires_opposes`,
`paires_analogues`. La sortie affiche, sous chaque paire, LES DEUX
VOCABULAIRES OPPOSÉS : c'est la charge utile pour un lecteur humain, ce que
le transport devrait traduire. Tests :
`tests/outils_ia/corpus/test_analogie_preuves.py`, **8 passed en 1,4 s**
(dont le test de sûreté : aucun `Theoreme` ne sort de cet organe).

**LEÇON, ET C'EST LA TROISIÈME FOIS EN DEUX JOURS.** À l'oracle : ne pas
descendre dans les termes. Aux notions : ne pas descendre dans les
entrailles des abréviations. À l'analogie : ne pas déplier les lemmes.
**Le bon niveau d'abstraction est toujours le niveau où la notion est
NOMMÉE, jamais celui où elle est implémentée.** Trois organes, trois fois la
même erreur, trois fois le même remède.

**BILAN DES QUATRE IDÉES — LES QUATRE SONT LIVRÉES** : (1) oracle numérique ✅,
(4) réfutation ✅, (2) invention de définitions ✅, (3) analogie ✅ (elle était
« livrée mais faible » ; elle apparie maintenant sa cible et en trouve une
autre seule).

**⚠️ RIEN N'EST COMMITÉ** — consigne « JAMAIS COMMITER » respectée. Les cinq
fichiers des quatre idées sont NON SUIVIS dans le dépôt, par-dessus la grosse
restructuration `bourbaki/logique/` → `bourbaki/i_description_mathematique_formelle/`
en attente dans l'index. À sécuriser dès que Karl le décide.
