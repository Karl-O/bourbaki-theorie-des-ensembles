# PLAN ETAPE C -- lot de cibles verifiees (audit fan-out w15tvt5e4, 2026-06-25)

Issu d'un audit 3 agents (Chap I/II/III) qui a **trie les « manquants » de COUVERTURE (2026-06-24)
contre le code ACTUEL + le PDF**. Bilan du tri : **13 faux-manquants** (deja faits depuis, ex-plans
B/v2/v3), **23 subsumes** reclasses non_applicable (criteres CS/CF/S, comparaison de theories, et
C43 = primitive S6), **11 cibles reelles closables** retenues ci-dessous.

Format : `## [ ] <nom>` -> cocher `## [x]` APRES commit verifie. Implementer UNE cible a la fois
(jamais pendant un fan-out d'audit), preuve CLOSE (primitives N.* only), `theorie==22`, enonce==livre,
test qui APPELLE le theoreme, verif (test + gate 0 erreur + conclusion==cible + hyps honnetes) AVANT commit.
Re-verifier l'absence (grep) au debut de chaque delegation (un import reussi ne prouve rien).

---

## [ ] appartenance_collectivisante  (faible/facile)  [secteur II.1.4]
- repere: E II.4 (n°4, Exemple 1) | PDF p.54-55
- statut: MANQUANT
- enonce: `{} |- Coll_x(x in y)` c.-a-d. `(existe Y)(pourtout x)((x in Y) <=> (x in y))` (la relation x∈y est collectivisante en x ; temoin = y).
- strategie: la plus simple. (1) `equivalence_reflexive(appartient(var x, var y))` -> `(x∈y)<=>(x∈y)`. (2) `generalisation('x', .)` -> `(pourtout x)((x∈y)<=>(x∈y))`. (3) corps de `coll('x', appartient(var x, var y))` instancie en Y:=y ; `N.s5(corps, var('y'), 'Y')` + modus_ponens -> `Coll_x(x∈y)`. Verifier fraicheur du lieur Y. Conclusion SANS hypothese => CLOSE. NON tautologique : le contenu est l'EXISTENCE d'un ensemble (Y=y), pas P=>P.
- lemmes: tactiques_prop.py (equivalence_reflexive L.78) ; formule.py (coll L.125) ; N.generalisation/s5/modus_ponens (usages s5 : cardinaux/arithmetique/iii_3_3_produit/ensembles_arith_cardinale.py L.468-472)
- fichier: bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_appartenance_coll.py

## [x] reticule_implique_filtrant_droite_gauche  (faible/facile)  [secteur III.1.11]  — FAIT (commit ci-dessous ; test 4 passed, theorie==22)
- repere: E III.13 (Remarque apres Def.8) | PDF p.116
- statut: MANQUANT (grep 'reticule.*filtrant' = 0)
- enonce: `{ est_reticule(G,E) } |- ( filtrant_droite_G(G,E) et filtrant_gauche_G(G,E) )`. Bourbaki : « Un ensemble ordonne reticule est evidemment filtrant a droite et a gauche. »
- strategie: est_reticule = est_ordre et (∀x∀y)((x∈E et y∈E)=>admet_borne_sup_inf), admet_borne_sup_inf=(∃s)(∃i)(borne_sup(G,{x,y},s,E) et borne_inf(...,i,E)). DROITE : instancie+MP, existe_elimination des temoins s,i ; de borne_sup extraire majorant (conj_elim_gauche)=(s∈E et (∀z)(z∈{x,y}=>(z,s)∈G)) ; x∈{x,y} via membre_paire_gauche, y∈{x,y} via membre_paire_droite => MP => (x,s)∈G et (y,s)∈G ; conjonction_intro = corps du temoin z:=s ; N.s5 reintroduit (∃z)(z∈E et (x,z)∈G et (y,z)∈G) ; loi_deduction + generalisation x,y = filtrant_droite. GAUCHE : dual (borne_inf/minorant). Calquer _filtrant_droite_G de ensembles_prop10_maximal_filtrant.py (copier le helper local).
- lemmes: ordre_treillis/ensembles_ordre_monotone.py (est_reticule, admet_borne_sup_inf) ; ensembles_ordre_relation.py (borne_superieure/inferieure, majorant, minorant) ; ii_2_couples_produit/ensembles_couples.py (membre_paire_gauche/droite) ; ensembles_abrege.py (est_filtrant_droite/gauche, paire) ; iii_1_8_filtrants/ensembles_prop10_maximal_filtrant.py (_filtrant_droite_G, existe_elimination)
- fichier: bourbaki/ordre/iii_1_relations_ordre/iii_1_11_reticules/ensembles_reticule_filtrant.py

## [ ] non_existence_ensemble_universel  (faible/moyen)  [secteur II.1.7]
- repere: E II.6 (n°7, Remarque) | PDF p.57
- statut: MANQUANT
- enonce: `{} |- non (existe X)(pourtout x)(x in X)` (pas d'ensemble dont tout objet est element).
- strategie: corollaire DIRECT du Russell deja formalise. Par l'absurde, H=(∃X)(∀x)(x∈X) ; temoin X0 via N.existe_temoin -> (∀x)(x∈X0) ; route close en calquant EXACTEMENT le squelette de `non_collectivisante_appartenance_propre` (reduction a l'absurde via helper `_non_equiv_negation` : |- non(P<=>non P)) ; decharger H par loi_deduction -> |- non H. Pas de tau residuel (X0 elimine) => CLOSE.
- lemmes: ii_1_axiomes_algebre/ensembles_theoremes.py (non_collectivisante_appartenance_propre L.256 ; _non_equiv_negation L.280) ; formule.py (coll, existe, pourtout, appartient) ; N.s5/N.existe_temoin
- fichier: bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_pas_ensemble_universel.py

## [x] galois_vuv_egale_v  (faible/moyen)  [secteur III.1.7]  — FAIT (test 7 passed + primal 5 vert, theorie==22)
- repere: E III.7-8 Prop.2 (2e egalite) | PDF p.110-111
- statut: PARTIEL (ensembles_prop2_galois.py n'a QUE la 1re egalite galois_uvu_egale_u)
- enonce: avec les hyps Galois (v decroissante, u(v(x'))>=x', v(u(x))>=x, nommage w=v∘u∘v, antisymetrie(G)) : `|- (∀x')(x'∈E' => w(x')=v(x'))`. Prop.2 seconde egalite v∘u∘v=v ; Bourbaki : « la seconde s'etablit de meme ».
- strategie: DUAL EXACT de galois_uvu_egale_u par echange u<->v, E<->E', G<->G'. (A) (v(u(v(x'))),v(x'))∈G de u(v(x'))>=x' + v decroissante ; (B) (v(x'),v(u(v(x'))))∈G de v(u(x))>=x en x:=v(x') ; (C) antisymetrie(G) sur (A)et(B) => v(u(v(x')))=v(x') ; (D) nommage w + composer_egalites. loi_deduction + generalisation(x'). Ici la decroissance de v est load-bearing. Reutiliser tous les helpers internes du fichier existant (_couple_dans/_val/_envoie_dans/_galois_vu/_galois_uv).
- lemmes: iii_1_5_applications_croissantes/ensembles_prop2_galois.py (galois_uvu_egale_u = patron miroir + helpers) ; ensembles_ordre_monotone.py (est_decroissante) ; ensembles_ordre_relation.py (antisymetrie) ; tactiques_abrege_egalite.py (composer_egalites)
- fichier: bourbaki/ordre/iii_1_relations_ordre/iii_1_5_applications_croissantes/ensembles_prop2_galois_dual.py

## [ ] ordre_applications_pointwise  (faible/moyen)  [secteur III.1.6]
- repere: E III.6 (Remarque, ordre sur F(E;F)) ; cf E III.13 Ex.4 | PDF p.109, p.116
- statut: MANQUANT (grep 0)
- enonce: definir `ordre_pointwise(GF,F,f,g,E) := (∀x)(x∈E => (f(x),g(x))∈GF)` PUIS prouver heritage REFLEXIVITE `{est_ordre(GF,F)} |- (∀f)((∀x)(x∈E=>f(x)∈F) => ordre_pointwise(GF,F,f,f,E))` et TRANSITIVITE `{est_ordre(GF,F)} |- (ordre_pointwise(f,g) et ordre_pointwise(g,h)) => ordre_pointwise(f,h)`. Bourbaki E III.6 : f<=g <=> (∀x∈E) f(x)<=g(x).
- strategie: REFL : extraire reflexivite_sur de est_ordre (conj_elim_gauche∘gauche) ; pour x∈E, f(x)∈F => (f(x),f(x))∈GF ; loi_deduction+generalisation. TRANS : extraire transitivite (conj_elim_droite) ; instancie ×3 + conjonction_intro + MP ; loi_deduction+generalisation. Calquer composee_croissantes_est_croissante (gestion _val(f,x) + instanciation transitivite). NE PAS affirmer l'antisymetrie globale (=extensionnalite des applications, plus lourd).
- lemmes: ensembles_ordre_relation.py (est_ordre, reflexivite_sur, transitivite) ; ensembles_ordre_monotone.py (composee_croissantes_est_croissante = patron _val/instanciation) ; ensembles_abrege.py (valeur)
- fichier: bourbaki/ordre/iii_1_relations_ordre/iii_1_6_ordre_produit/ensembles_ordre_applications.py

## [ ] monotonie_composee_graphes  (moyen)  [secteur II.3.3]
- repere: E II.13 (n°3, Remarque) | PDF p.64
- statut: MANQUANT
- enonce: `{G1 ⊂ G2, G1' ⊂ G2'} |- (G1'∘G1) ⊂ (G2'∘G2)` (monotonie de la composee de graphes).
- strategie: but = (∀w)(w∈G1'∘G1 => w∈G2'∘G2). Pour (x,z) : couple_composee(G1',G1,'x','z') deplie (x,z)∈G1'∘G1 <=> (∃y)((x,y)∈G1 et (y,z)∈G1'). Sous existe_elimination, (x,y)∈G1 + inclus(G1,G2) instancie en (x,y) => (x,y)∈G2 ; idem (y,z)∈G1'=>(y,z)∈G2' ; reconstruire (∃y)(...G2...G2') puis replier via equivalence_arriere(couple_composee(G2',G2,'x','z')). Decharger + generaliser w. Calquer image_composee (re-pliage existentiel).
- lemmes: fonctions/ii_3_3_composee_graphes/ensembles_composee.py (couple_composee L.35 ; image_composee L.68 patron) ; ensembles_abrege.py (composee, AXIOME_COMPOSEE, inclus) ; N.assume/instancie/loi_deduction/generalisation/existe_temoin
- fichier: bourbaki/ensembles/ii_3_correspondances/ii_3_reciproque_composee/ensembles_composee_monotone.py

## [BLOQUE] totalement_ordonne_implique_reticule  (moyen)  [secteur III.1.12]  — BLOQUE par bug capture est_reticule (cf. ANOMALIES 2026-06-25 ; corriger la def avant)
- repere: E III.14 (Remarque apres Ex. Def.9) | PDF p.117
- statut: MANQUANT (grep 0)
- enonce: `{ est_ordre(G,E), totalite(G,E) } |- est_reticule(G,E)`, totalite=(∀x∀y)((x∈E et y∈E)=>((x,y)∈G ou (y,x)∈G)). Bourbaki E III.14 : « Un ensemble totalement ordonne est reticule et a fortiori filtrant a droite et a gauche. »
- strategie: pour x,y∈E, cas (x,y)∈G OU (y,x)∈G (tactique cas/tiers_exclu). Branche (x,y)∈G : borne_sup temoin s:=y (majorant : (x,y)∈G par hyp, (y,y)∈G par reflexivite ; z∈{x,y} via _instance_paire => z=x ou z=y => Leibniz S6 ; plus petit majorant : tout majorant m verifie (y,m)∈G) et borne_inf temoin i:=x. Branche (y,x)∈G symetrique. Recoller par cas. Calquer maximal_est_plus_grand_si_total (combo totalite+antisym) + mecanique paire de reticule_implique_filtrant.
- lemmes: ensembles_ordre_monotone.py (est_reticule, admet_borne_sup_inf) ; ensembles_ordre_relation.py (borne_sup/inf, majorant/minorant) ; ensembles_couples.py (membre_paire_*, _instance_paire) ; ensembles_abrege.py (est_totalement_ordonne) ; iii_1_12_totalement_ordonnes/ensembles_prop12_sup_total.py (cas/tiers_exclu)
- fichier: bourbaki/ordre/iii_1_relations_ordre/iii_1_12_totalement_ordonnes/ensembles_total_implique_reticule.py

## [ ] c39_existe_typique  (faible/moyen)  [secteur I.4.4]
- repere: E I.37 L.18-26 | PDF p.37
- statut: MANQUANT
- enonce: `{ A=>(R=>S) } |- (E_A x)R => (E_A x)S` et `(A_A x)R => (A_A x)S`, ou (E_A x)R:=(∃x)(A et R), (A_A x)R:=non(∃x)(A et non R).
- strategie: layer Assemblage, calquer criteres_quantif2.py:c35. EXISTENTIEL : de A=>(R=>S) construire (A et R)=>(A et S) (assume, conj_elim, MP, conj_intro, loi_deduction) ; monotonie_existe(.,x) => (∃x)(A et R)=>(∃x)(A et S). UNIVERSEL : (A et non S)=>(A et non R) [contraposer via contraposition], monotonie_existe, puis c23_negation/contraposition. conjonction_intro des deux sens (ou deux def).
- lemmes: congruence_quantif.py (monotonie_existe L.29) ; criteres_C.py (c23_negation L.104) ; tactiques_prop.py (conjonction_intro L.58, contraposition) ; criteres_quantif2.py (c35 L.43, patron) ; assemblage.py (conjonction, existe, negation)
- fichier: bourbaki/logique/i_3_quantifies/criteres_typiques_c39_c42.py

## [ ] c40_existe_ou_typique  (moyen)  [secteur I.4.4]
- repere: E I.37 L.28-33 | PDF p.37
- statut: MANQUANT
- enonce: `|- (A_A x)(R et S) <=> ((A_A x)R et (A_A x)S)` et `|- (E_A x)(R ou S) <=> ((E_A x)R ou (E_A x)S)`.
- strategie: EXIST/OU : (E_A x)(R ou S)=(∃x)(A et (R ou S)). (1) congruence prop (A et (R ou S))<=>((A et R) ou (A et S)) [_et_ou_distrib patron]. (2) congruence_existe(.,x). (3) distribution (∃x)(P ou Q)<=>((∃x)P ou (∃x)Q) (=> par C18+monotonie_existe ; <= par monotonie_existe). Chainer c22_transitivite. UNIV/ET : via c35 + congruence_pour_tout + distribution (∀x)(P et Q).
- lemmes: congruence_quantif.py (congruence_existe L.50, congruence_pour_tout L.57, monotonie_existe L.29) ; criteres_quantif2.py (c35 L.43) ; criteres_C.py (c22_transitivite L.96, c18 L.79) ; tactiques_abrege2.py (_et_ou_distrib L.174)
- fichier: bourbaki/logique/i_3_quantifies/criteres_typiques_c39_c42.py

## [ ] c42_commute_typique  (moyen)  [secteur I.4.4]
- repere: E I.37 L.35-41 | PDF p.37
- statut: MANQUANT
- enonce: si x∉B et y∉A : `|- (A_A x)(A_B y)R <=> (A_B y)(A_A x)R` et `|- (E_A x)(E_B y)R <=> (E_B y)(E_A x)R`.
- strategie: reduire via C35 a la commutation deja prouvee C34. EXIST : (E_A x)(E_B y)R=(∃x)(A et (∃y)(B et R)) ; faire passer A,B a travers (∃x),(∃y) par et_existe_droite/gauche (x∉B, y∉A) => (∃x)(∃y)(A et B et R) ; existe_commute pour echanger ; remonter symetriquement. UNIV : via c35 puis c34_pour_tout + congruence_pour_tout. Chainages c22_transitivite + conjonction_intro.
- lemmes: criteres_quantif2.py (c34_pour_tout L.21, c34_existe L.34, c35 L.43) ; tactiques_abrege_quantif.py (existe_commute L.107, et_existe_droite L.75, et_existe_gauche L.91) ; congruence_quantif.py (congruence_pour_tout L.57, congruence_existe L.50) ; criteres_C.py (c22_transitivite L.96)
- fichier: bourbaki/logique/i_3_quantifies/criteres_typiques_c39_c42.py

## [ ] c45_univoque_avant  (moyen)  [secteur I.5.3]
- repere: E I.41 L.5-13 | PDF p.41
- statut: MANQUANT (ni def univoque ni c45)
- enonce: `relation_univoque_x(R) := (∀y)(∀z)(((y|x)R et (z|x)R) => (y=z))` (« il existe au plus un x tel que R », E I.40) PUIS sens direct C45 : `{ relation_univoque_x(R) } |- R => (x = tau_x(R))`. (Sens reciproque hors scope.)
- strategie: layer Assemblage (i_4_egalitaires). (1) constructeur relation_univoque_x(R,x,y,z) = pour_tout(y,pour_tout(z,implication(conjonction(subst(y,x,R),subst(z,x,R)),egalite(y,z)))), y,z frais. (2) C45-avant (calquer preuve livre E I.41 L.5-11) : assume(R) ; S5 sur R au terme tau_x(R) => (tau_x(R)|x)R ; conjonction_intro(R,(tau_x(R)|x)R) ; instancier univoque (C30/instanciation) en y:=x, z:=tau_x(R) => (R et (tau_x(R)|x)R)=>(x=tau_x(R)) ; MP ; loi_deduction sur R => {univoque} |- R=>(x=tau_x(R)).
- lemmes: tactiques_egalite.py (instanciation/C30 L.41, c44 patron L.94) ; assemblage.py (tau_x, existe L.172, egalite, conjonction, substitution_b_x_a) ; tactiques_prop.py (conjonction_intro L.58) ; noyau.py (s5)
- fichier: bourbaki/logique/i_4_egalitaires/relations_fonctionnelles_c45.py

---

## Subsumes par le noyau (reclasses non_applicable, NE PAS implementer)
Chap I : C2-C5 (theorie plus forte/equivalente), **C43 = primitive S6**, schemas CS/CF de formation/
substitution, meta-concepts « demonstration/theorie » (~12). Chap II : ~8 criteres de selection/
schemas subsumes. Chap III : ~3. Total ~23. Cf. audit w15tvt5e4.

## Faux-manquants (deja faits, COUVERTURE perimee) : ~13
Chap II : Russell (non_collectivisante_appartenance_propre), singleton (appartient_singleton),
{x}⊂X⇔x∈X (appartient_singleton_inclus), + plans v3 (produits, relation induite, image reciproque). Chap III : 4.
