# PLAN_ETAPE_B_v2 — file des resultats FAISABLES (fan-out wu9090em3, 6 secteurs)

Priorise: perf_risque faible + difficulte facile d abord. [ ] = a faire, [x] = fait.

## [x] theoreme1_b_section_valeur  (faible/facile)
- secteur: II.3 correspondances et foncti | §II.3.8, Théorème 1 b) — composition des sections : « si s, s' sont des sections associées à f et f', s∘s' est une section associée à f''=f'∘f »
- statut: MANQUANT — le module ensembles_retractions_props.py couvre Théorème 1 a) (theoreme1_a_retraction_valeur, composition des RÉTRACTIONS au niveau matriciel) et 1 d), mais le DUAL exact pour les SECTIONS 
- enonce: ⊢_{S section de F sur A, S' section de F' sur B, s'(z)∈B} (z∈C) ⇒ f'(f(s(s'(z)))) = z. Lu matriciellement (encodage Déf. 11 du projet, comme theoreme1_a_retraction_valeur) : « s∘s' est une section de f''=f'∘f » signifie (∀z∈C) (f'∘f)((s∘s')(z))=z, soit en dépliant f'(f(s(s'(z))))=z. Preuve de Bourba
- strategie:
  - Calquer EXACTEMENT theoreme1_a_retraction_valeur (lignes 200-241 de ensembles_retractions_props.py) en inversant le rôle composition gauche↔droite.
  - Poser vS,vSp,vF,vFp,vA,vB,vC ; vz=var('z') ; assumer z∈C (hxC).
  - Étape 1 : E.est_section(vF, ... ) — instancier est_section(S,F,A) au point s'(z) : besoin de s'(z)∈A. Bourbaki applique d'abord la section s' de f' : (4) f'(f(s(s'(z))))... NB l'ordre est f(s(...)) = s'(z) puis f'(s'(z))=z.
  - Étape 2 (f(s(t))=t avec t=s'(z)∈B) : instancier hsec_S = N.assume(E.est_section(vS,vF,?)) au point s'(z), décharger l'appartenance s'(z)∈B (hyp explicite, jamais postulée) → f(s(s'(z))) = s'(z).
  - Étape 3 (congruence sous f'(·)) : N.modus_ponens(eq_etape2, congruence_terme(f(s(s'(z))), s'(z), E.valeur(vFp, var('w')), 'w')) → f'(f(s(s'(z)))) = f'(s'(z)).
  - Étape 4 (f'(s'(z))=z) : instancier hsec_Sp = N.assume(E.est_section(vSp,vFp,vC)) au point z, décharger z∈C → f'(s'(z))=z.
  - Étape 5 : composer_egalites(etape3, etape4) → f'(f(s(s'(z))))=z ; conclure N.loi_deduction(appartient(vz,vC), eq).
  - Construire cible_theoreme1_b_section_valeur en miroir de cible_theoreme1_a_retraction_valeur (lignes 244-250). Ajouter au __all__ et 2 tests (conclusion==cible + ensemble exact des 3 hypothèses) sur le modèle test_theoreme1_a_retraction_valeur_hypotheses.
- lemmes: bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_section, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:valeur, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:composee, bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:congruence_terme, bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:composer_egalites, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:instancie, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:assume, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:modus_ponens
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_retractions_props.py (ajout d'1 fonction + 1 cible d

## [x] section_unique_par_image  (faible/facile)
- secteur: II.3 correspondances et foncti | §II.3.8, Déf. 11 (remarque finale) — « une section s est déterminée de manière unique par l'ensemble s(B) » : si s, s' sont deux sections de f surjective avec s(B)=s'(B), alors s=s'
- statut: MANQUANT — aucune fonction sur l'unicité de la section (Grep 'section_unique' → aucun résultat). C'est une propriété purement set/fonction-théorique (égalité de valeurs forcée par injectivité de la re
- enonce: Version VALEURS (faisable, fidèle au cœur de la remarque Déf. 11) : ⊢ [s, s' sections de f sur B] ⇒ (∀y)(y∈B ⇒ f(s(y))=f(s'(y))). En effet f(s(y))=y=f(s'(y)) pour tout y∈B (les deux sections vérifient f∘s=Id_B). C'est la brique d'unicité « au niveau des valeurs-images » : s(y) et s'(y) ont la même i
- strategie:
  - Assumer hsec=N.assume(E.est_section(vS,vF,vB)) et hsecp=N.assume(E.est_section(vSp,vF,vB)).
  - Instancier les deux au point y (instancie, comme section_implique_surjective_valeur lignes 86-97), décharger y∈B → f(s(y))=y et f(s'(y))=y.
  - Symétriser la 2e (symetrie) → y=f(s'(y)), puis composer_egalites → f(s(y))=f(s'(y)).
  - loi_deduction(y∈B, eq) ; generalisation('y', inner) → (∀y)(y∈B ⇒ f(s(y))=f(s'(y))).
  - VARIANTE forte (optionnelle, conditionnée) : ajouter l'hypothèse injective_dans(F, s(B)) + s(y)∈s(B), s'(y)∈s'(B)=s(B), puis modus_ponens sur l'injectivité → s(y)=s'(y) → (∀y∈B) s(y)=s'(y). Garder TOUTES ces hyps explicites.
  - Ajouter cible_section_unique_par_image et 2 tests (.est_clos + conclusion==cible) sur le modèle test_prop8_section_implique_surjective_valeur.
- lemmes: bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions_props:section_implique_surjective_valeur, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_section, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:injective_dans, bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:symetrie, bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:composer_egalites, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:instancie, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:assume, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:loi_deduction
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_retractions_props.py (ajout dans fichier existant ; 

## [x] image_difference_egal_si_injective — Corollaire de la Prop. 6 (image DIRECTE)  (faible/facile)
- secteur: II.4 réunion/intersection d'un | E.II.4.5 (Chap. II §4, sous-section 5, « Réunion et intersection de deux ensembles »), Corollaire de la Proposition 6 : f injection ⟹ f⟨A∖X⟩ = f⟨A⟩∖f⟨X⟩.
- statut: MANQUANT. Le DUAL réciproque est déjà CLOS (`image_reciproque_difference`, est_fonctionnel ⟹ f⁻¹⟨B∖Y⟩=f⁻¹⟨B⟩∖f⁻¹⟨Y⟩, fichier ii_4_image_famille/ensembles_image_algebre_binaire_ii4.py l.327). La versio
- enonce: ⊢ injective(f) ⇒ f⟨A∖X⟩ = f⟨A⟩∖f⟨X⟩, pour X ⊂ A. Énoncé Bourbaki verbatim : « Soit f une injection de A dans B ; pour toute partie X de A, on a f⟨A−X⟩ = f⟨A⟩ − f⟨X⟩ » (Texte.tex §5, Corollaire de la Prop. 6, lignes 91-100).
- strategie:
  - Cible : impl(injective(f), egal(E.image(f, E.difference(A, X)), E.difference(E.image(f, A), E.image(f, X)))).
  - Calculer les appartenances point par point via membre_image (AXIOME_IMAGE : a∈f⟨Z⟩ ⇔ (∃x)(x∈Z et (x,a)∈f)) sur les trois ensembles f⟨A∖X⟩, f⟨A⟩, f⟨X⟩ et _instance_diff sur A∖X et sur f⟨A⟩∖f⟨X⟩.
  - Sens ⊇ (a∈f⟨A⟩∖f⟨X⟩ ⇒ a∈f⟨A∖X⟩) : INCONDITIONNEL. Témoin x avec x∈A, (x,a)∈f ; montrer ¬x∈X par contraposition de « x∈X ⇒ a∈f⟨X⟩ » (témoin x), qui contredit ¬a∈f⟨X⟩ ; recoller via S5. Calque EXACT du bloc ⊇ de image_reciproque_difference (l.390-413), avec couples (x,a)∈f au lieu de (x,a)∈f⁻¹.
  - Sens ⊆ (a∈f⟨A∖X⟩ ⇒ a∈f⟨A⟩∖f⟨X⟩) : utilise l'INJECTIVITÉ. Témoin x∈A∖X, (x,a)∈f ; donc a∈f⟨A⟩ et x∈A, ¬x∈X. Pour ¬a∈f⟨X⟩ : sous-lemme « a∈f⟨X⟩ ⇒ x∈X » via un témoin x', (x',a)∈f, x'∈X, puis injective(f) instanciée donne x=x' (les deux couples (x,a),(x',a)∈f partagent la 2e coordonnée), Leibniz S6 transporte x'∈X en x∈X. Contraposition avec ¬x∈X. Calque du sous-lemme aY_implique_xinY (l.354-368) en remplaçant _univalence(f⁻¹) par instancie(injective(f),x,x',a).
  - Conclure par conjonction_intro des deux inclusions + extensionnalite_appliquee, puis loi_deduction sur injective(f).
- lemmes: ensembles_image_algebre_binaire_ii4:membre_image, ensembles_image_algebre_binaire_ii4:_instance_diff, ensembles_image_recip_famille_ii4:injective, ensembles_abrege:image, ensembles_abrege:difference, ensembles_theoremes:extensionnalite_appliquee, tactiques_abrege2:instancie, tactiques_abrege2:contraposition
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_image_famille/ensembles_image_difference_injective_

## [x] commutativite_reunion_binaire / commutativite_inter_binaire — corollaires nommés de la Prop. 1 + Cor.  (faible/facile)
- secteur: II.4 réunion/intersection d'un | E.II.4.5 (sous-section 5), formules A∪B = B∪A et A∩B = B∩A présentées comme « conséquences des prop. 1 et 2 » (Texte.tex §4.5 lignes 29-39).
- statut: PARTIEL. La commutativité ∪/∩ existe au niveau de l'algèbre booléenne profonde (ii_1_axiomes_algebre/ensembles_algebre_booleenne.py) mais N'EST PAS dérivée comme résultat de la SECTION II.4 à partir d
- enonce: ⊢ A∪B = B∪A et ⊢ A∩B = B∩A, dérivés directement de la caractérisation z∈A∪B ⇔ (z∈A ∨ z∈B) (AXIOME_REUNION) et de la commutativité du ∨ (C-critère), resp. z∈A∩B ⇔ (z∈A et z∈B) et commutativité du et. Énoncé Bourbaki : Texte.tex §4.5 lignes 31-33.
- strategie:
  - Cible commutativité ∪ : egal(E.reunion(A,B), E.reunion(B,A)).
  - Instancier AXIOME_REUNION sur (A,B,z) et sur (B,A,z) : _instance_reunion(A,B,z) donne z∈A∪B ⇔ (z∈A ∨ z∈B) ; _instance_reunion(B,A,z) donne z∈B∪A ⇔ (z∈B ∨ z∈A).
  - Pont : commutativité du ∨ — réutiliser la tactique `ou_commute`/`comm_ou` de tactiques_abrege2 (analogue à comm_et déjà utilisé l.108 de ensembles_image_algebre_binaire_ii4) pour (z∈A ∨ z∈B) ⇔ (z∈B ∨ z∈A).
  - Chaîner par equivalence_transitivite : (z∈A∪B) ⇔ (z∈A∨z∈B) ⇔ (z∈B∨z∈A) ⇔ (z∈B∪A). Généraliser sur z, appliquer egalite_par_extension. Symétrique pour ∩ avec comm_et et _instance_inter.
  - INCONDITIONNEL, 0 hypothèse, preuve courte (~15 lignes chacune).
- lemmes: ensembles_image_algebre_binaire_ii4:_instance_reunion, ensembles_image_algebre_binaire_ii4:_instance_inter, tactiques_abrege2:comm_et, tactiques_abrege2:equivalence_transitivite, ensembles_theoremes:egalite_par_extension, ensembles_abrege:reunion, ensembles_abrege:inter, noyau_abrege:generalisation
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_binaire_commut_ii4.

## [x] diagonale_injective — injectivité de l'application diagonale x ↦ x̃  (faible/facile)
- secteur: II.5 — Produit d'une famille d | E.II.5.3 (Définition du produit, paragraphe sur la diagonale Δ et l'application diagonale)
- statut: MANQUANT — explicitement REPORTÉ. La docstring de application_diagonale (ensembles_extension_canonique.py l.172-179) dit « Injection (Bourbaki) — l'injectivité est REPORTÉE (lemme dur) ». Le sous-doss
- enonce: Soit E un ensemble, I un ensemble d'indices. Pour x∈E, x̃ = graphe de la fonction constante ι↦x. L'application diagonale x↦x̃ de E dans E^I est une injection. Forme formalisable fidèle (sous hypothèse honnête I≠∅, requise car sur I=∅ tous les x̃ valent ∅) : ⊢ ( ¬(I=∅) et x∈E et y∈E et x̃ = ỹ ) ⇒ x =
- strategie:
  - Choisir un indice témoin α∈I (de l'hypothèse honnête : soit α donné par ¬(I=∅) via temoin/non_vide_ssi_element, soit α∈I posé en hypothèse directe — la 2e variante évite tout détour vide).
  - Évaluer x̃ en α : x̃ = famille_constante(I,x,iota) = graphe_terme(I, x, iota). Comme la valeur T=x ne contient pas le liant iota, subst_t(α,iota,x)=x. Donc graphe_terme_valeur(I, T=x, u=α, x=iota) donne {α∈I} ⊢ x̃(α) = x.
  - De même {α∈I} ⊢ ỹ(α) = y.
  - De l'hypothèse x̃ = ỹ, par Leibniz (S6/congruence_terme) sur la valeur en α : x̃(α) = ỹ(α).
  - Composer les trois égalités (composer_egalites/symetrie) : x = x̃(α) = ỹ(α) = y, d'où x = y.
  - Décharger les hypothèses par loi_deduction pour obtenir l'implication close.
- lemmes: bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor:graphe_terme_valeur — {u∈A} ⊢ F(u)=T[u] (le pivot ; déjà réexporté/utilisé par ensembles_produit_props_fonctoriel.py et ensembles_projections_terme.py — coût d'import module seulement, AUCUN calcul cardinal au runtime de la preuve), bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique:famille_constante / application_diagonale / diagonale_valeur (x̃ et sa caractérisation, déjà définis), bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:symetrie, composer_egalites, congruence_terme, bourbaki.logique.i_1_termes_relations.formule:subst_t (constate T[α]=x car liant iota absent de T=x), bourbaki.logique.i_2_criteres_C.noyau:noyau_abrege (assume, modus_ponens, loi_deduction, s6)
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_2_diagonale/ensembles_diagonale_injective.py (NOUVEAU fichier, co

## [x] C55 — caractérisation de la projection canonique : p(x)=p(y) ⇔ R{x,y}  (faible/facile)
- secteur: II.6 Relations d'équivalence ( | E.II.6.2 (Classes d'équivalence, ensemble quotient) — assemblage final p(x)=p(y) ⇔ R{x,y}
- statut: MANQUANT (assemblage). Les DEUX maillons sont déjà CLOS dans ensembles_quotient_props_graphe.py : projection_valeur_classe ⊢ (p(a)=p(b)) ⇔ (Cl(a)=Cl(b)) [mod. hyp. de valeur p(·)=Cl(·)] et relation_ss
- enonce: Soit R une relation d'équivalence dans E donnée par son graphe G, et p l'application canonique de E sur E/R (p(x)=Cl_R(x)). Sous {R réflexive dans E, R symétrique, R transitive, b∈E, p(a)=Cl_R(a), p(b)=Cl_R(b)} : ⊢ ( p(a)=p(b) ) ⇔ ( R{a,b} ). C'est le « C55 » socle de la décomposition canonique (deu
- strategie:
  - 1. eqv_p = projection_valeur_classe(g,e,a,b) ⊢ (p(a)=p(b)) ⇔ (Cl(a)=Cl(b)) [hyp. valeurs p(·)=Cl(·)].
  - 2. eqv_R = relation_ssi_classe_egale(g,a,b,e,x,z) ⊢ R{a,b} ⇔ (Cl(a)=Cl(b)) [hyp. réfl/sym/trans + b∈E].
  - 3. Recoller par equivalence_transitivite : eqv_p composée à equivalence_symetrie(eqv_R) donne (p(a)=p(b)) ⇔ R{a,b}. Aucune nouvelle hypothèse introduite : le séquent final est l'union des hypothèses déchargées dans les deux maillons (toutes laissées explicites, rien postulé).
  - 4. Vérifier theorie_ensembles() inchangée (22 axiomes) — aucun axiome neuf, pur recollage logique.
- lemmes: bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe:projection_valeur_classe, bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe:relation_ssi_classe_egale, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:equivalence_transitivite, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:equivalence_symetrie
- fichier: bourbaki/ensembles/ii_6_equivalence/ensembles_projection_c55.py (NOUVEAU fichier ; le dossier ii_6_equivalence a 7 .py + __init__ + __pycache__ = sous la limite de 10)

## [x] Proposition 4 — inf A ≤ sup A (cas A non vide)  (faible/facile)
- secteur: III.1 relations d'ordre (bourb | E.III.1.9, Borne supérieure, borne inférieure — Proposition 4
- statut: MANQUANT : aucune fonction dans bornes_sup/ ni ordre_treillis/ ne prouve inf A ≤ sup A. Les prédicats borne_inferieure / borne_superieure existent (ensembles_ordre_relation.py), mais le lien inf≤sup (
- enonce: Soient E un ensemble ordonné de graphe G, A une partie de E admettant à la fois une borne inférieure i = inf A et une borne supérieure s = sup A dans E. Si A ≠ ∅, alors inf A ≤ sup A, i.e. (i,s) ∈ G. Cible close : { transitivite_rel(G), ¬(A=∅) [sous forme (∃z)(z∈A)], borne_inferieure(G,A,i,E), borne
- strategie:
  - Prendre un témoin a∈A via l'hypothèse A≠∅ (assume (∃z)(z∈A), puis existe_elimination sur le corps z∈A — patron de majorant_de_sur_domine dans ensembles_sup_generiques_iii1.py).
  - De borne_inferieure(G,A,i,E) extraire minorant(G,A,i,E) (conjonction_elim_gauche), puis son corps (∀x)(x∈A⇒(i,x)∈G) ; instancier en a : (i,a)∈G.
  - De borne_superieure(G,A,s,E) extraire majorant(G,A,s,E) (conjonction_elim_gauche), puis son corps (∀x)(x∈A⇒(x,s)∈G) ; instancier en a : (a,s)∈G.
  - Appliquer transitivite_rel(G) instanciée en (i,a,s) : ((i,a)∈G et (a,s)∈G) ⇒ (i,s)∈G ; modus_ponens sur conjonction_intro((i,a)∈G,(a,s)∈G) → (i,s)∈G.
  - Décharger le témoin a par existe_elimination + modus_ponens sur (∃z)(z∈A) pour clore l'hypothèse A≠∅ ; vérifier 0 hypothèse non déchargée hors des 4 hypothèses honnêtes.
- lemmes: bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:borne_inferieure, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:borne_superieure, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:minorant, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:majorant, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:transitivite_rel, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_intro, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_gauche, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_droite
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_1_relations_ordre/bornes_sup/ensembles_inf_sup_prop4_iii1.py

## [ ] Proposition 10 — élément maximal d'un ensemble ordonné filtrant à droite = plus grand élément  (faible/facile)
- secteur: III.1 relations d'ordre (bourb | E.III.1.10, Ensembles filtrants — Proposition 10
- statut: MANQUANT et DOSSIER-TROU : le dossier iii_1_relations_ordre/iii_1_8_filtrants/ ne contient que __init__.py (TODO explicite « résultat du livre PAS ENCORE formalisé. À combler en ÉTAPE B »). Les prédic
- enonce: Dans un ensemble ordonné filtrant à droite E (graphe G), tout élément maximal a de E est le plus grand élément de E. Cible close : { est_ordre(G,E) [pour la réflexivité (a,a)∈G], filtrant_droite_G(G,E), element_maximal(G,E,a) } ⊢ plus_grand_element(G,E,a). Preuve Bourbaki : pour x∈E, il existe y∈E a
- strategie:
  - Définir le prédicat graphe-G filtrant_droite_G(G,E) := E.est_filtrant_droite(lambda u,v:(u,v)∈G, E) — réutiliser exactement le helper _filtrant_droite_G de ensembles_ordre_fini_iii4.py.
  - Extraire de element_maximal(G,E,a) : a∈E (conjonction_elim_gauche) et le corps (∀x)((x∈E et (a,x)∈G)⇒x=a) (conjonction_elim_droite).
  - Corps du « plus grand » à prouver : (∀x)(x∈E⇒(x,a)∈G). Sous Hx=assume(x∈E) : instancier filtrant en (x,a) (avec a∈E) ⇒ (∃z)(z∈E et (x,z)∈G et (a,z)∈G).
  - existe_elimination du témoin y : sous (y∈E et (x,y)∈G et (a,y)∈G), extraire (a,y)∈G ; instancier la maximalité de a en y avec (y∈E et (a,y)∈G) ⇒ y=a.
  - Transporter (x,y)∈G en (x,a)∈G par Leibniz S6 sur la 2e coordonnée avec l'égalité y=a (patron EXACT de maximal_est_plus_grand_si_total dans ensembles_ordre_relation.py, lignes 516-520).
  - Décharger le témoin (existe_elimination + modus_ponens), généraliser en x, conjonction_intro avec a∈E ⇒ plus_grand_element(G,E,a). 0 hypothèse résiduelle hors des 3 honnêtes.
- lemmes: bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:element_maximal, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:plus_grand_element, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation:est_ordre, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_filtrant_droite, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_intro, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_gauche, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_droite, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:instancie
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_1_relations_ordre/iii_1_8_filtrants/ensembles_filtrants_prop10.py

## [ ] segment_de_segment_est_segment (transitivité des segments, clôture Déf. 2)  (faible/facile)
- secteur: III.2 ensembles bien ordonnés  | §III.2.1, Définition 2 — phrase « en outre, tout segment de S est aussi un segment de E »
- statut: MANQUANT — grep "segment_de_segment / segment_transitif / tout segment de S" → 0 occurrence dans tout bourbaki/. Le module ensembles_bon_ordre.py couvre E, ∅, A∩B, A∪B segments, mais PAS la transitivi
- enonce: ⊢ ( est_segment(S, R, E)  et  est_segment(T, R, S) )  ⇒  est_segment(T, R, E).  Autrement dit : si S est un segment de E et T un segment de S (au sens de l'ordre induit), alors T est un segment de E. Énoncé manipulant uniquement ⊂ et l'implication de clôture-bas (∀x,y)((x∈T et y∈E et y≤x)⇒y∈T) — auc
- strategie:
  - Hypothèses : H1=est_segment(S,R,E) = (S⊂E et clos_S), H2=est_segment(T,R,S) = (T⊂S et clos_T) où clos_S/clos_T sont les clauses (∀x,y)((x∈·et y∈· et y≤x)⇒y∈·).
  - Composante 1 — T⊂E : par transitivité de l'inclusion (T⊂S et S⊂E ⇒ T⊂E) via la tactique existante inclusion_transitive (déjà importée dans ensembles_sous_bien_ordonne.py).
  - Composante 2 — clôture-bas de T dans E : assumer la prémisse (x∈T et y∈E et y≤x). But : y∈T. Étape (a) : de x∈T et T⊂S, instancier l'inclusion → x∈S. Étape (b) : appliquer clos_T à (x∈T, y∈S, y≤x) — mais il faut d'abord y∈S. Pour l'obtenir : de x∈S (étape a), y∈E, y≤x, appliquer clos_S → y∈S. Étape (c) : maintenant (x∈T et y∈S et y≤x) → clos_T donne y∈T.
  - Assembler conjonction_intro(T⊂E, clôture) ; décharger H1,H2 par loi_deduction. Réutiliser exactement le motif de _force_premisse / instancie(instancie(body,vx),vy) de ensembles_bon_ordre.py.
- lemmes: bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_segment (prédicat, ligne 711), bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:inclusion_transitive, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:instancie / conjonction_intro / conjonction_elim_gauche / conjonction_elim_droite, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:assume / loi_deduction / modus_ponens / generalisation, motif _force_premisse de bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_bon_ordre.py (à recopier en local)
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_segment_transitif.py (NOUVEAU 4e fichier du dossier ; le do

## [ ] element_hors_de_son_segment + seg_strict_propre (x∉S_x et x<y ⟹ S_x ⊊ S_y)  (faible/facile)
- secteur: III.2 ensembles bien ordonnés  | §III.2.1, Proposition 2 — « x<y entraîne S_x ⊊ S_y » (préliminaire de la bijection croissante x↦S_x)
- statut: PARTIEL — la monotonie NON STRICTE S_x⊂S_y est faite (seg_strict_monotone, ensembles_segments_construction.py). Le cœur de l'inclusion STRICTE (x∈S_y mais x∉S_x) est MANQUANT : grep "x_not_in_seg / x∉
- enonce: Deux lemmes : (L-a) ⊢ x∉seg(R,E,x), i.e. ¬( x ∈ S_x )  [INCONDITIONNEL, par l'axiome de segment : u∈S_x ⇔ ((u∈E et R{u,x}) et u≠x), donc x∈S_x forcerait x≠x]. (L-b) ⊢ { est_relation_ordre(R), x∈E, R{x,y}, x≠y } ⊢ ( x ∈ seg(R,E,y)  et  ¬(x ∈ seg(R,E,x)) ) — le témoin x certifie S_x ⊊ S_y (S_x⊂S_y déj
- strategie:
  - L-a (x∉S_x) : instancier membre_segment(R,E,x,x) → (x∈S_x ⇔ ((x∈E et R{x,x}) et x≠x)). Supposer x∈S_x ; sens avant → ((x∈E et R{x,x}) et x≠x) ; projeter x≠x. Avec N.reflexivite(x) (x=x) faire ex_falso → ¬(x∈S_x). Réutiliser les helpers locaux _ex_falso/_refute_self déjà présents (recopiés de ensembles_segments_construction.py).
  - L-b composante x∈S_y : il faut x∈E, R{x,y}, x≠y (hyps) → corps ((x∈E et R{x,y}) et x≠y) ; membre_segment(R,E,y,x) sens arrière (equivalence_arriere) → x∈seg(R,E,y).
  - L-b composante x∉S_x : c'est exactement L-a (inconditionnel).
  - Assembler conjonction_intro(x∈S_y, ¬(x∈S_x)). Optionnel : combiner avec seg_strict_monotone_de_bon_ordre (déjà clos, lemme_1_segments.py) pour exposer une cible « S_x⊂S_y et S_x≠S_y » via le témoin x (extensionnalité A1 contraposée : S_x=S_y ⇒ x∈S_x, absurde) — étape A1 facile et bornée.
- lemmes: bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction:membre_segment (axiome de segment instancié, ligne 106), bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction:seg (constructeur S_x, ligne 95), bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments:seg_strict_monotone_de_bon_ordre (S_x⊂S_y, clos), bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:reflexivite / s2 / s6 / loi_deduction / modus_ponens, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:equivalence_avant / equivalence_arriere / conjonction_intro / conjonction_elim_droite, helpers _ex_falso / _refute_self (motif présent dans ensembles_segments_construction.py / ensembles_trichotomie_prop1.py)
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_segment_strict_propre.py (NOUVEAU dans bon_ordre_segments ;

## [ ] theoreme1_e_surjective_valeur  (faible/moyen)
- secteur: II.3 correspondances et foncti | §II.3.8, Théorème 1 e) — « si f''=f'∘f est une injection et f' une injection, f est une surjection » (au niveau des valeurs : tout y antécédent de f' atteint via f)
- statut: PARTIEL/MANQUANT — Théorème 1 c) (f'' inj ⇒ f inj) et 1 d) (f'' surj ⇒ f' surj, niveau valeurs) sont clos, mais 1 e) n'existe pas. La preuve complète de Bourbaki pour e) utilise f' bijection + récipro
- enonce: Forme valeurs, inconditionnelle : ⊢ [(∀x)(∀x')(f'(f(x))=f'(f(x')) ⇒ f(x)=f(x'))] ⇐ [injective_dans(F', dom)] (congruence + injectivité de f' transportée). Plus précisément la brique exploitable : ⊢_{F' injective au sens valeurs} (f'(f(x))=f'(f(x'))) ⇒ (f(x)=f(x')) — i.e. l'injectivité de f' « descen
- strategie:
  - Modéliser comme theoreme1_d_surjective_valeur (lignes 254-282) qui élimine un ∃ et réintroduit un témoin via N.s5 + existe_elimination.
  - Assumer injective_dans(F', B) au niveau valeurs ; assumer f'(f(x))=f'(f(x')).
  - Instancier l'injectivité de F' aux points f(x), f(x') : décharger les gardes d'appartenance (f(x)∈B, f(x')∈B comme hyps explicites OU via happlique (∀v∈A) f(v)∈B, déjà utilisé dans _cv_point / theoreme1_c_injective lignes 109-129).
  - Modus_ponens → f(x)=f(x'). Loi_deduction pour refermer l'implication. Generalisation.
  - Pour la composante surjective duale (tout y∈f'(B) atteint comme f'(f(x))) : réutiliser le motif témoin de theoreme1_d_surjective_valeur (N.s5 témoin = f(x), existe_elimination 'x').
  - Garder les hypothèses C46 explicites (dom F'=B, f applique A dans B) JAMAIS postulées, exactement comme theoreme1_c_injective. Ajouter cible + 2 tests (conclusion exacte + hypothèses structurelles) en miroir.
- lemmes: bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions_props:_cv_point, bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions_props:theoreme1_c_injective, bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions_props:theoreme1_d_surjective_valeur, bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif:existe_elimination, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:s5, bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:congruence_terme, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:injective_dans
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_retractions_props.py (ajout dans fichier existant). 

## [ ] associativite_reunion_famille — Proposition 2 (réunion), partie INCONDITIONNELLE  (faible/moyen)
- secteur: II.4 réunion/intersection d'un | E.II.4.2 (Chap. II §4, sous-section 2, « Propriétés de la réunion et de l'intersection »), Proposition 2, première formule (« associativité » de la réunion).
- statut: MANQUANT. Le docstring de ensembles_familles.py (l.12-16) déclare explicitement « associativité … REPORTÉES ». grep `associativ` dans familles/ii_4 = 0 (seul ii_5 produit a une associativité, sans rap
- enonce: ⊢ ⋃_{λ∈L} X_λ = ⋃_{λ∈L} (⋃_{ι∈J_λ} X_ι), sous l'hypothèse « L = ⋃_{λ∈L} J_λ », formalisée fidèlement par les deux clauses : (a) couverture (∀ι)(ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ)) et (b) domaine (∀λ)(∀ι)(λ∈L et ι∈J_λ ⇒ ι∈L). Cette première formule est INCONDITIONNELLE (pas de J_λ≠∅ requis), contrairement à l'
- strategie:
  - Construire la famille interne G : λ ↦ ⋃_{ι∈J_λ} X_ι. Réutiliser le PATRON `famille_reparam`/`axiome_valeur_reparam` de ensembles_chap2_props_restantes.py (l.167-187) : définir un terme `famille_double_reunion(f, J)` dont la valeur en λ est reunion_famille(f, valeur_famille(J,λ)), caractérisé par un théorème de valeur (S6/Leibniz) — AUCUN axiome neuf, theorie_ensembles reste à 22.
  - Membre gauche : z∈⋃_{λ∈L}X_λ ⇔ (∃λ)(λ∈L et z∈X_λ) via _inst_reunion (réutilisé de ensembles_familles.py / ensembles_familles_algebre.py).
  - Membre droit : z∈⋃_{λ∈L}G_λ ⇔ (∃λ)(λ∈L et z∈G_λ) ⇔ (∃λ)(λ∈L et (∃ι)(ι∈J_λ et z∈X_ι)) via _inst_reunion sur G puis sur l'interne + le théorème de valeur de G.
  - Équivalence des deux corps : sens ⇒ : d'un témoin λ avec λ∈L, z∈X_λ, la couverture (a) donne λ'∈L avec λ∈J_λ' ; témoin (λ', λ) à droite. Sens ⇐ : d'un (λ,ι) à droite, le domaine (b) donne ι∈L ; témoin ι à gauche. Pur jeu de quantificateurs ∃ : existe_elimination + s5 (témoin) + congruence_existe.
  - Généraliser sur z et appliquer egalite_par_extension. Décharger l'hypothèse conjointe (a et b) par loi_deduction.
- lemmes: ensembles_familles_algebre:_inst_reunion, ensembles_chap2_props_restantes:famille_reparam, ensembles_chap2_props_restantes:axiome_valeur_reparam, ensembles_chap2_props_restantes:_membre_eq, ensembles_abrege:reunion_famille, ensembles_abrege:valeur_famille, ensembles_theoremes:egalite_par_extension, tactiques_abrege_quantif:congruence_existe
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_familles_assoc_reun

## [ ] diagonale_dans_exposant — x̃ ∈ E^I et Δ ⊂ E^I (la diagonale vit bien dans le produit E^I)  (faible/moyen)
- secteur: II.5 — Produit d'une famille d | E.II.5.3 (la diagonale Δ est « une partie du produit E^I »)
- statut: MANQUANT — le texte Bourbaki affirme « les graphes des applications constantes forment une partie Δ du produit E^I » mais aucun lemme ne certifie x̃∈E^I ni l'inclusion Δ⊂E^I. diagonale_produit (=image
- enonce: Soit E un ensemble, I un ensemble d'indices. (a) Pour tout x∈E, x̃ ∈ E^I (= exposant(I,E)). (b) Δ ⊂ E^I, où Δ = {x̃ | x∈E}. Formes : ⊢ (x∈E) ⇒ ( x̃ ∈ exposant(I,E) ) ; et ⊢ Δ ⊂ exposant(I,E).
- strategie:
  - Pour (a) : instancier axiome_exposant(I,E) en x̃ : x̃∈E^I ⇔ ( x̃⊂I×E et x̃ fonctionnel et dom x̃ = I ).
  - Prouver les trois conjoints du graphe-terme constant x̃ = graphe_terme(I,x,iota) : (i) fonctionnel via graphe_terme_fonctionnel ; (ii) dom x̃ = I via graphe_terme_domaine ; (iii) x̃⊂I×E : tout couple (ι,v)∈x̃ a v=T[ι]=x∈E et ι∈I (via graphe_terme_couple_dans / membre_graphe_terme + l'hypothèse x∈E), donc (ι,v)∈I×E.
  - Conjoindre (conjonction_intro) et conclure x̃∈E^I par equivalence_arriere de l'axiome instancié ; décharger x∈E.
  - Pour (b) : soit z∈Δ ; membre_diagonale donne (∃x)(x∈E et (x,z)∈graphe(diag)) ; le couple (x,z)∈graphe(diag) force z=x̃ (caractérisation diag_application_membre) ; sous x∈E, (a) donne z=x̃∈E^I ; généraliser et refermer en inclusion par def de inclus.
- lemmes: bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:exposant, axiome_exposant, theorie_exposant (caractérisation membership de E^I — théorie dédiée, hors des 22 axiomes ; motif déjà utilisé dans ensembles/fonctions/hors_ii_3/ii_5_produit_famille/ensembles_application_valeur.py l.84-85), bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme:graphe_terme_fonctionnel, membre_graphe_terme, bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_projections_terme:projection_premiere (=graphe_terme_domaine), graphe_terme_couple_dans, bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique:famille_constante, diagonale_produit, membre_diagonale, diag_application_membre, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:instancie, equivalence_avant, equivalence_arriere, conjonction_intro
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_2_diagonale/ensembles_diagonale_dans_exposant.py (NOUVEAU, même d

## [ ] Proposition 1 (réciproque) : a),b),c) ⇒ Γ équivalence dans X — symétrie & transitivité du graphe  (faible/moyen)
- secteur: II.6 Relations d'équivalence ( | E.II.6.1 (Définition d'une relation d'équivalence), Proposition 1 — caractérisation Γ=Γ⁻¹, Γ∘Γ=Γ
- statut: MANQUANT entièrement (aucune occurrence de Proposition 1 / Γ=Γ⁻¹ / Γ∘Γ=Γ dans ii_6_equivalence). On vise la moitié RÉCIPROQUE (sens b)⇒sym, c)⇒trans), la plus directement closeable. Les briques de mem
- enonce: Soit G le graphe d'une correspondance Γ entre X et X. (b) Si G = G⁻¹ alors R{x,y}:=(x,y)∈G est SYMÉTRIQUE. (c) Si G∘G ⊂ G alors R est TRANSITIVE. Donc sous {G=G⁻¹, G∘G⊂G}, ⊢ est_relation_equivalence(rel_graphe(G)) (symétrie ET transitivité), c'est-à-dire la condition logique de la réciproque de la P
- strategie:
  - SYMÉTRIE : assume G=G⁻¹. Pour x,y : assume (x,y)∈G. Par Leibniz S6 sur G=G⁻¹, réécrire (x,y)∈G en (x,y)∈G⁻¹ ; couple_reciproque(G,x,y) donne ((x,y)∈G⁻¹)⇔((y,x)∈G) ⇒ (y,x)∈G. loi_deduction + double generalisation ⇒ est_symetrique(rel_graphe G).
  - TRANSITIVITÉ : assume G∘G ⊂ G (inclusion). Pour x,y,z : assume (x,y)∈G et (y,z)∈G ; conjonction_intro + existe_temoin(y) ⇒ (∃y)((x,y)∈G et (y,z)∈G) ; equivalence_arriere(couple_composee(G,G,x,z)) ⇒ (x,z)∈G∘G ; instancier l'inclusion G∘G⊂G en (x,z) ⇒ (x,z)∈G. loi_deduction + triple generalisation ⇒ est_transitive(rel_graphe G).
  - ASSEMBLAGE : conjonction_intro(sym, trans) = est_relation_equivalence(rel_graphe G), littéralement la déf E.II.6.1. Hypothèses laissées explicites {G=G⁻¹, G∘G⊂G}, rien postulé, theorie inchangée (22).
  - OPTION (si rapide) : ajouter a)⇒ réflexivité via diagonale_membre (Δ_X⊂G) pour est_relation_equivalence_dans — sinon laisser en commentaire « reporté » pour rester faible-risque.
- lemmes: bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque:couple_reciproque, bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee:couple_composee, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:rel_graphe, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_symetrique, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_transitive, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_relation_equivalence, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_intro, equivalence_avant, equivalence_arriere, instancie (+ noyau_abrege.assume/modus_ponens/loi_deduction/generalisation/s6/s5)
- fichier: bourbaki/ensembles/ii_6_equivalence/ensembles_proposition1_gamma.py (NOUVEAU ; reste sous 10 entrées/dossier)

## [ ] segment_du_plus_petit_est_vide (S_α = ∅ pour α = min E)  (faible/moyen)
- secteur: III.2 ensembles bien ordonnés  | §III.2.1 — « si E est bien ordonné et n'est pas vide, il a un plus petit élément α, et par suite S_α est aussi l'intervalle semi-ouvert [α,α[ » (S_α = ∅)
- statut: MANQUANT — grep "seg_min_vide / segment_minimum / seg du min" → 0 occurrence. La Prop 1 (prop1_segment_propre, clos) traite le segment propre général mais PAS le cas dégénéré du minimum.
- enonce: ⊢ { est_bien_ordonne(R,E),  est_plus_petit_element(R,E,α) }  ⊢  seg(R,E,α) = ∅.  Le segment d'extrémité du plus petit élément est vide : aucun u ne peut vérifier (u∈E et R{u,α} et u≠α), car α minore E donne R{α,u}, et avec R{u,α} l'antisymétrie force u=α. Énoncé purement order/ensembliste (extension
- strategie:
  - Extraire de est_plus_petit_element(R,E,α) : α∈E et (∀x)(x∈E ⇒ R{α,x}) (conjonction_elim). Extraire de est_bien_ordonne l'antisymétrie (motif _proprietes_ordre_de_bon_ordre / _antisym_de_bo déjà écrit dans lemme4_segments).
  - Montrer ∀u ¬(u∈seg(R,E,α)) : supposer u∈seg(R,E,α) ; membre_segment sens avant → (u∈E et R{u,α}) et u≠α ; projeter u∈E, R{u,α}, u≠α. De α minore E et u∈E → R{α,u}. Antisymétrie instanciée (u,α) : (R{u,α} et R{α,u}) ⇒ u=α. Contradiction avec u≠α → ex_falso → ¬(u∈seg).
  - Passer de (∀u)¬(u∈S_α) à S_α=∅ : utiliser AXIOME_VIDE (∀z)¬(z∈∅) et l'extensionnalité A1 — montrer S_α⊂∅ (de ¬(u∈S_α) par S2/ex falso : u∈S_α⇒u∈∅) et ∅⊂S_α (ex falso depuis ¬(u∈∅), motif déjà dans vide_est_segment de ensembles_bon_ordre.py), puis A1 → S_α=∅. Tous ces sous-motifs (A1, AXIOME_VIDE, ⊂ vide) sont déjà présents et bornés dans ensembles_trichotomie_prop1.py (_diff_non_vide) et ensembles_bon_ordre.py.
  - Décharger les 2 hypothèses (bon ordre, plus petit élément) ou les garder ; fournir une fonction _cible miroir pour le test (motif systématique du projet).
- lemmes: bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_plus_petit_element (ligne 579) / est_bien_ordonne / segment_extremite / VIDE / A1 / AXIOME_VIDE, bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction:seg / membre_segment, bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_croissante:_antisym_de_bo (extraction antisymétrie de est_bien_ordonne), bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite:symetrie, bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege:axiome / instancie / s2 / loi_deduction / generalisation, motifs A1/⊂-vide/ex falso de bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_bon_ordre.py (vide_est_segment) et ensembles_trichotomie_prop1.py (_diff_non_vide)
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_segment_minimum.py (NOUVEAU dans bon_ordre_segments ; surve

## [ ] Saturé Ã = p⁻¹⟨p⟨A⟩⟩ : Ã est saturée pour R (clôture par R)  (faible/difficile)
- secteur: II.6 Relations d'équivalence ( | E.II.6.4 (Parties saturées) — « le saturé Ã est la plus petite partie saturée contenant A »
- statut: PARTIEL. La NOTION sature(a,p)=p⁻¹⟨p⟨A⟩⟩ existe (ensembles_abrege:sature) et UNE direction est close (saturee_implique_classe_incluse : A saturée ⇒ classe incluse). MANQUE le fait structurel que Ã lui
- enonce: Soit R d'équivalence dans E (graphe G, symétrique et transitive), p l'application canonique, A⊂E, et Ã := p⁻¹⟨p⟨A⟩⟩ (sature(A,p)). Alors Ã est saturée pour R : (∀x)(∀y)( (x∈Ã et R{x,y}) ⇒ y∈Ã ). Forme minimale closeable : sur l'écriture Ã = p⁻¹⟨B⟩ (image réciproque d'un B⊂E/R), tout sur-ensemble ima
- strategie:
  - Déplier est_saturee(Ã,G,Ã) = est_compatible(t↦t∈Ã, rel_graphe G) = (∀x)(∀y)((x∈Ã et (x,y)∈G)⇒y∈Ã), en réutilisant le squelette d'instanciation de saturee_implique_classe_incluse.
  - Coeur : sous x∈Ã et R{x,y}, montrer y∈Ã. Avec Ã=p⁻¹⟨B⟩, x∈Ã ⇔ p(x)∈B (image réciproque). R{x,y} ⇒ Cl(x)=Cl(y) (relation_implique_classe_egale, déjà clos) ⇒ p(x)=p(y) (projection_valeur_classe) ⇒ p(y)∈B (Leibniz S6) ⇒ y∈Ã.
  - Laisser explicites {R sym, R trans} (consommées par relation_implique_classe_egale) et les relations de valeur de p ; theorie inchangée (22).
  - Garde faible-risque : rester sur la forme « Ã = p⁻¹⟨B⟩ ⇒ Ã saturée » (image réciproque pure) plutôt que de déplier p⟨A⟩ ; aucun cardinal, uniquement membership image/réciproque + égalité de classes.
- lemmes: bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:sature, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_saturee, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege:est_compatible, bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_produit_restant:saturee_implique_classe_incluse, bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe:relation_implique_classe_egale, bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe:projection_valeur_classe, bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque:couple_reciproque
- fichier: bourbaki/ensembles/ii_6_equivalence/ensembles_sature_partie.py (NOUVEAU ; reste sous 10 entrées/dossier)

## [ ] produit_inclus_reciproque — Cor 3 (réciproque) : ∏X_ι ⊂ ∏Y_ι et X_ι≠∅ ⇒ X_ι ⊂ Y_ι  (moyen/moyen)
- secteur: II.5 — Produit d'une famille d | E.II.5.4, Corollaire 3 (réciproque de la monotonie du produit)
- statut: PARTIEL — le SENS DIRECT (Prop.10/Cor.3 : (∀ι)(X_ι⊂Y_ι) ⇒ ∏X⊂∏Y) est FAIT (produit_monotone dans ii_5_6_7_algebre_produit/ensembles_produit_monotone_ii5.py). La RÉCIPROQUE (∏X⊂∏Y et tous X_ι≠∅ ⇒ X_ι⊂Y
- enonce: Soient (X_ι), (Y_ι) deux familles sur I. Si ∏_{ι∈I}X_ι ⊂ ∏_{ι∈I}Y_ι et si X_ι≠∅ pour tout ι, alors X_ι⊂Y_ι pour tout ι. Forme conditionnelle fidèle (hypothèse = un témoin/élément du produit, exactement Cor.1) : ⊢ ( ∏X ⊂ ∏Y et α∈I et F∈∏X et a∈X_α ) ⇒ ( a ∈ Y_α ) — version pointwise ; plus la général
- strategie:
  - Réutiliser le « principe de choix »-τ déjà prouvé : facteur_temoin ⊢ ¬(X_ι=∅) ⇒ τ_w(w∈X_ι)∈X_ι, pour fabriquer (ou recevoir en hypothèse honnête) un F∈∏X dont la α-coordonnée est a (Cor.1 = pr_α surjective ; reçu en hypothèse, comme pr_J_surjective_via_prolongement reçoit le prolongement).
  - De l'inclusion ∏X⊂∏Y et F∈∏X, déduire F∈∏Y (def de inclus + modus_ponens).
  - Appliquer projection_dans_facteur à F∈∏Y : (α∈I) ⇒ F(α)∈Y_α.
  - Comme F(α)=a (la coordonnée α du témoin choisi vaut a, par construction/hypothèse), conclure a∈Y_α par Leibniz (S6).
  - Généraliser sur a∈X_α et refermer en X_α⊂Y_α ; décharger les hypothèses par loi_deduction. Marquer CONDITIONNEL : la prémisse « F∈∏X avec F(α)=a » EST la surjectivité de pr_α (Cor.1, reportée), pas postulée comme acquis.
- lemmes: bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille:projection_dans_facteur (F∈∏ ⇒ (α∈I ⇒ F(α)∈X_α)), membre_produit_famille, bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_4_projection_partielle.ensembles_produit_props_projection:facteur_temoin (choix-τ), facteur_non_vide_si_membre (déjà prouvés, même esprit de réduction conditionnelle), bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit.ensembles_produit_monotone_ii5:produit_monotone (le sens direct, pour assembler l'équivalence si désiré), bourbaki.logique.i_2_criteres_C.noyau:noyau_abrege (assume, modus_ponens, loi_deduction, s6, generalisation)
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_4_projection_partielle/ensembles_produit_inclus_reciproque.py (NO

## [ ] Proposition 13 — l'intersection de deux intervalles fermés est un intervalle  (moyen/moyen)
- secteur: III.1 relations d'ordre (bourb | E.III.1.13, Intervalles — Proposition 13 (cas de deux intervalles fermés)
- statut: PARTIEL : l'axiome de membership [a,b] est posé en théorie dédiée theorie_intervalle_ferme (ensembles_ordre_treillis_props.py : axiome_intervalle_ferme, x∈[a,b] ⇔ (x∈E et a≤x et x≤b)), avec intervalle
- enonce: Dans un ensemble ordonné E (graphe G), pour deux intervalles fermés [a,b] et [c,d], un x appartient à [a,b]∩[c,d] si et seulement si x∈E, a≤x, c≤x, x≤b et x≤d. Cible close (forme membership, sans treillis) : ⊢ (∀x)( x∈[a,b]∩[c,d] ⇔ (x∈E et (a,x)∈G et (c,x)∈G et (x,b)∈G et (x,d)∈G) ), l'axiome de mem
- strategie:
  - Travailler dans theorie_intervalle_ferme (réutiliser axiome_intervalle_ferme de ensembles_ordre_treillis_props.py), instancié pour [a,b] et pour [c,d].
  - Réutiliser le lemme de membership de l'intersection : x∈X∩Y ⇔ (x∈X et x∈Y) — chercher _instance_intersection / intersection_membre dans bourbaki/ensembles/ii_1_axiomes_algebre (analogue à _instance_reunion déjà utilisé dans ensembles_sup_generiques_iii1.py:majorant_reunion_iff).
  - Sens ⇒ : de x∈[a,b]∩[c,d], obtenir x∈[a,b] et x∈[c,d] (equivalence_avant du lemme intersection), puis par equivalence_avant de l'axiome [a,b] : (x∈E et a≤x et x≤b), et de même pour [c,d] : (x∈E et c≤x et x≤d) ; recombiner en conjonction (x∈E et a≤x et c≤x et x≤b et x≤d).
  - Sens ⇐ : de (x∈E et a≤x et c≤x et x≤b et x≤d), reconstruire (x∈E et a≤x et x≤b) ⇒ x∈[a,b] (equivalence_arriere axiome) et (x∈E et c≤x et x≤d) ⇒ x∈[c,d], puis equivalence_arriere du lemme intersection ⇒ x∈[a,b]∩[c,d].
  - Assembler les deux sens par conjonction_intro (équivalence) et généraliser en x. Garder le caractère « intervalle » au niveau membership ; ne PAS introduire sup/inf de paires (perf et machinery treillis) — c'est le résidu honnête documenté.
- lemmes: bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_treillis_props:axiome_intervalle_ferme, bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_treillis_props:theorie_intervalle_ferme, bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes:_instance_reunion (modèle ; chercher l'analogue _instance_intersection), bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:equivalence_avant, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:equivalence_arriere, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_intro, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_gauche, bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2:conjonction_elim_droite
- fichier: C:/Users/KARL/OneDrive/Bureau/Apprendre/Livre/Bourbakie/Theorie_des_ensembles/V9/bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_intervalles_prop13.py

