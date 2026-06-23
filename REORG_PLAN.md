# REORG_PLAN — arborescence cible (calquée sur le livre, ≤10 entrées/dossier)

> **PLAN — rien n'est déplacé.** À valider avant migration (par étapes, tests verts à chaque palier ; `tests/` calqué à l'identique).

**Totaux** : 401 fichiers · 399 déplacements · 16 dossiers-trous à créer · profondeur max 3 niveaux · validation ≤10 : **1 VIOLATIONS**.

---

## bourbaki/logique  (24 fichiers → 25 déplacements)

- **(racine du paquet)/** — _I (racine du paquet)_ (6)
    - __init__.py
- **i_1_termes_relations/** — _I.1_ (7)
    - __init__.py
    - formule.py
    - lecture.py
    - notation.py
    - propositions.py
    - criteres_CS.py
    - criteres_CF.py
- **i_2_criteres_C/** — _I.2_ (4)
    - __init__.py
  - **criteres/** — _I.2_ (4)
      - __init__.py
      - criteres_C.py
      - criteres_C_suite.py
      - criteres_C_suite2.py
  - **noyau/** — _I.2_ (3)
      - __init__.py
      - noyau.py
      - noyau_abrege.py
  - **tactiques/** — _I.2_ (5)
      - __init__.py
      - tactiques.py
      - tactiques_prop.py
      - tactiques_abrege.py
      - tactiques_abrege2.py
- **i_3_quantifies/** — _I.3_ (5)
    - __init__.py
    - congruence_quantif.py
    - criteres_quantif2.py
    - tactiques_abrege_quantif.py
    - ensembles_alpha_bridge.py
- **i_4_egalitaires/** — _I.4_ (3)
    - __init__.py
    - tactiques_egalite.py
    - tactiques_abrege_egalite.py
- **verification/** — _I (couche outillage)_ (2)
    - __init__.py
    - verificateur_preuve.py

## bourbaki/ensembles  (25 fichiers → 22 déplacements)

- **(racine du paquet)/** — _II_ (7)
    - __init__.py
- **ii_1_axiomes_algebre/** — _II.1_ (9)
    - __init__.py
    - ensembles_abrege.py
    - ensembles_theoremes.py
    - ensembles_algebre_booleenne.py
    - ensembles_inclusion_treillis.py
    - ensembles_vide.py
    - ensembles_vide_identites.py
    - ensembles_difference.py
    - ensembles_difference_identites.py
- **ii_2_couples_produit/** — _II.2_ (3)
    - __init__.py
    - ensembles_couples.py
    - ensembles_produit_distributif.py
- **ii_3_correspondances/** — _II.3_ (3)
    - __init__.py
    - ensembles_fondations_notions.py
    - ensembles_correspondances.py
- **ii_4_reunion_intersection/** — _II.4_ (2)
    - __init__.py
    - ensembles_chap2_props_restantes.py
- **ii_6_equivalence/** — _II.6_ (8)
    - __init__.py
    - ensembles_quotient_props_graphe.py
    - ensembles_quotient_produit_restant.py
    - ensembles_quotient_props.py
    - ensembles_quotient_complements.py
    - ensembles_quotient_c56_c57.py
    - ensembles_decomposition_quotient.py
    - ensembles_decomposition_effective.py
- **iii_3_ordre_cardinaux/** — _III.3_ (2)
    - __init__.py
    - ensembles_props_diverses.py

  **Trous du livre (dossiers vides à créer) :**
  - `ii_2_couples_produit/ii_2_5_graphe_produit` — _II.2.5_ : II.2 a une sous-section sur le graphe d'un produit / produit cartesien comme ensemble (egalites ensemblistes A x (B u C) = ...) non encore formalisee : seul le coeur appartenance-couple (produit_distributif) et l'injectivite des paires (couples) sont prouves ; l'egalite ensembliste pleine est reportee.
  - `ii_3_correspondances/ii_3_reciproque_composee` — _II.3.2-3.3_ : II.3 correspondance reciproque et composition des correspondances (graphes) ne sont pas couvertes dans ce paquet (dom/img/image directe seuls presents) ; les correspondances reciproque/composee relevent du sous-paquet fonctions (autre agent) mais le trou cote 'graphe de correspondance' reste visible ici.

## bourbaki/ensembles/fonctions  (30 fichiers → 30 déplacements)

- **(racine du paquet)/** — _II.3_ (10)
    - __init__.py
- **hors_ii_3/** — _II.2/II.5/III.3/IV_ (4)
  - **ii_2_projections/** — _II.2_ (1)
      - ensembles_projections.py
  - **ii_5_produit_famille/** — _II.5_ (3)
      - ensembles_application_valeur.py
      - ensembles_composee_triple_fonctionnelle.py
      - ensembles_currying_ii5.py
  - **iii_3_recollement/** — _III.3_ (3)
      - ensembles_recollement_bijection.py
      - ensembles_restriction_somme.py
      - ensembles_dom_image_reunion.py
  - **iv_structures/** — _IV.1/IV.2/IV.3_ (3)
      - ensembles_isomorphismes.py
      - ensembles_morphismes.py
      - ensembles_applications_universelles.py
- **ii_3_2_reciproque/** — _II.3.2_ (1)
    - ensembles_reciproque.py
- **ii_3_3_composee_graphes/** — _II.3.3_ (2)
    - ensembles_composee.py
    - ensembles_composee_reciproque.py
- **ii_3_4_fonctions_valeur/** — _II.3.4_ (3)
    - ensembles_fonctions.py
    - ensembles_valeur_codomaine.py
    - ensembles_composee_assoc.py
- **ii_3_5_restrictions_prolongements/** — _II.3.5_ (2)
    - ensembles_restrictions.py
    - ensembles_sous_famille.py
- **ii_3_6_fonction_terme/** — _II.3.6_ (3)
    - ensembles_fonction_terme.py
    - ensembles_fonctions_coordonnees.py
    - ensembles_projections_terme.py
- **ii_3_7_composee_fonctions/** — _II.3.7_ (1)
    - ensembles_fonctions_composee.py
- **ii_3_8_retractions_sections/** — _II.3.8_ (3)
    - ensembles_retractions.py
    - ensembles_retractions_props.py
    - ensembles_composee_valeurs.py
- **ii_3_general/** — _II.3_ (4)
    - ensembles_extensionnalite.py
    - ensembles_fonctions_complements.py
    - ensembles_fonctions_props2.py
    - ensembles_prop7_9_ii3.py

  **Trous du livre (dossiers vides à créer) :**
  - `ii_3_1_graphes` — _II.3.1_ : Sous-section II.3.1 (notion de graphe / correspondance) : aucun fichier dedie dans ce paquet (la composee/reciproque de graphes sont en II.3.2-II.3.3). Dossier vide pour rendre le trou visible.
  - `ii_3_9_fonctions_deux_variables` — _II.3.9_ : Sous-section II.3.9 (fonctions de deux variables / coupes partielles) : aucun fichier dans ce paquet. Dossier vide pour signaler le trou de couverture.

## bourbaki/ensembles/familles  (28 fichiers → 28 déplacements)

- **./** — _II.4 / II.5 (+ II.2, III.7 résidents)_ (5)
    - __init__.py
- **ii_2_produit_deux_ensembles/** — _II.2.2_ (1)
    - ensembles_produit.py
- **ii_4_reunion_intersection_familles/** — _II.4_ (4)
  - **ii_4_1_definitions_algebre/** — _II.4.1_ (5)
      - ensembles_familles.py
      - ensembles_familles_algebre.py
      - ensembles_reunion_sup_univ_ii4.py
      - ensembles_inter_inf_univ_ii4.py
      - ensembles_reparam_inter_ii4.py
  - **ii_4_demorgan/** — _II.4 (Prop. 5)_ (1)
      - ensembles_familles_demorgan.py
  - **ii_4_image_famille/** — _II.4 (E.II.25-27, Prop. 3/4/6)_ (3)
      - ensembles_image_recip_famille_ii4.py
      - ensembles_reciproque_reunion_binaire_ii4.py
      - ensembles_image_algebre_binaire_ii4.py
  - **ii_4_recollement_somme/** — _II.4.8 (Prop. 7-10, somme)_ (2)
      - ensembles_recollement_props.py
      - ensembles_somme_disjointe.py
- **ii_5_produit_famille/** — _II.5_ (4)
  - **ii_5_1_extension_canonique/** — _II.5.1 / II.5.7_ (3)
      - ensembles_extension_canonique.py
      - ensembles_produit_props.py
      - ensembles_produit_props_fonctoriel.py
  - **ii_5_4_projection_partielle/** — _II.5.4_ (1)
      - ensembles_produit_props_projection.py
  - **ii_5_6_7_algebre_produit/** — _II.5.4-5.7_ (4)
      - ensembles_produit_props2.py
      - ensembles_produit_monotone_ii5.py
      - ensembles_produit_egal_facteurs_ii5.py
      - ensembles_produit_inter_ii5.py
  - **ii_5_definitions/** — _II.5.1 / II.5.3_ (2)
      - ensembles_produit_famille.py
      - ensembles_extensionnalite_produit.py
- **iii_7_limites/** — _III.7_ (5)
    - ensembles_limites.py
    - ensembles_limites_iii7.py
    - ensembles_cone_unicite.py
    - ensembles_limites_prop2_3_iii7.py
    - ensembles_limites_prop4plus_iii7.py

  **Trous du livre (dossiers vides à créer) :**
  - `bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_2_diagonale` — _II.5.2-5.3_ : Application diagonale et diagonale Delta du produit E^I (mentionnees comme notions dans ensembles_extension_canonique mais pas de module/propositions propres deposes).

## bourbaki/ordre  (36 fichiers → 36 déplacements)

- **./** — _III.1-III.7_ (6)
    - __init__.py
- **iii_1_relations_ordre/** — _III.1_ (3)
  - **bornes_sup/** — _III.1.9-III.1.12 (Prop 5-9)_ (2)
      - ensembles_sup_generiques_iii1.py
      - ensembles_sup_prop7_8_iii1.py
  - **isomorphismes_ordre/** — _III.1.3 (iso d'ordre)_ (3)
      - ensembles_iso_ordre_canon.py
      - ensembles_valeur_bridge.py
      - ensembles_pont_binder.py
  - **ordre_treillis/** — _III.1.1-III.1.5/1.11_ (7)
      - ensembles_ordre.py
      - ensembles_ordre_relation.py
      - ensembles_ordre_vocab.py
      - ensembles_iii1_ordre_props.py
      - ensembles_ordre_produit_antisym.py
      - ensembles_ordre_monotone.py
      - ensembles_ordre_treillis_props.py
- **iii_2_bon_ordre/** — _III.2_ (3)
  - **bon_ordre_segments/** — _III.2.1 (bon ordre, segments)_ (2)
      - ensembles_bon_ordre.py
      - ensembles_sous_bien_ordonne.py
  - **recurrence_transfinie/** — _III.2 (C59 recurrence, C60 recursion)_ (8)
      - ensembles_recurrence_transfinie.py
      - ensembles_recursion_transfinie_existence.py
      - ensembles_c60_existence_close.py
      - ensembles_c60_realisation.py
      - ensembles_c60_clauses.py
      - ensembles_c60_coeur.py
      - ensembles_c60_final.py
      - ensembles_c60_pont.py
  - **zorn_zermelo/** — _III.2 (Th.1 Zermelo, Th.2 Zorn, Bourbaki-Witt)_ (5)
      - ensembles_zorn.py
      - ensembles_zorn_theoreme.py
      - ensembles_zermelo.py
      - ensembles_bourbaki_witt.py
      - ensembles_bourbaki_witt_chaine.py
- **iii_4_ensembles_finis/** — _III.4 (Prop 3, Th.1 Tukey)_ (3)
    - ensembles_tukey_iii4.py
    - ensembles_tukey_sous_lemme.py
    - ensembles_ordre_fini_iii4.py
- **iii_6_ordinaux/** — _III.6 (Exercices, ordinaux)_ (1)
    - ensembles_ordinaux.py
- **iii_7_limites/** — _III.7 (limites proj./induct.)_ (4)
    - ensembles_limites_canoniques.py
    - ensembles_cofinal.py
    - ensembles_limites_props.py
    - ensembles_limites_props2.py

  **Trous du livre (dossiers vides à créer) :**
  - `iii_1_relations_ordre/iii_1_8_filtrants` — _III.1.8_ : La notion d'ensemble filtrant / partie filtrante (E.III.1.8) du perimetre III.1 n'a pas de fichier dedie dans bourbaki/ordre : elle est couverte ailleurs (ensembles_abrege est_filtrant_*, et ensembles_cofinal cote III.7). Dossier vide pour rendre visible le trou de couverture propre a III.1.8 dans ce paquet.

## bourbaki/cardinaux  (140 fichiers → 139 déplacements)

- **(racine du paquet)/** — _III.2-III.6 (racine paquet)_ (8)
    - __init__.py
- **iii_2_trichotomie_ordinaux/** — _III.2_ (7)
  - **assemblage/** — _III.2 (Th.3, assemblage final)_ (8)
      - ensembles_trichotomie_assemble.py
      - ensembles_trichotomie_maillon_final.py
      - ensembles_trichotomie_pont_val.py
      - ensembles_trichotomie_residuals.py
      - ensembles_trichotomie_scaffold.py
      - ensembles_trichotomie_dom_segment.py
      - ensembles_trichotomie_temoin_adjonction.py
      - ensembles_maillon_coherences_prouvees.py
  - **coincidence_fusion/** — _III.2 (Lemme 1, coïncidence/fusion)_ (8)
      - ensembles_coincidence_decharge.py
      - ensembles_coincidence_geometrie.py
      - ensembles_coincidence_pont.py
      - ensembles_coincidence_univ.py
      - ensembles_coincidence_univ_app.py
      - ensembles_fusion_app.py
      - ensembles_fusion_assemblage.py
      - ensembles_fusion_depuis_coincidence_app.py
  - **h_coherences/** — _III.2 (Th.3, cohérences de h)_ (6)
      - ensembles_h_bien_defini.py
      - ensembles_h_est_graphe.py
      - ensembles_trichotomie_coherences.py
      - ensembles_trichotomie_h_iso.py
      - ensembles_trichotomie_hgraphe_pr2seg.py
      - ensembles_trichotomie_restriction.py
  - **iso_ordre/** — _III.2 (Cor.1 / III.1.3)_ (6)
      - ensembles_iso_ordre_composee.py
      - ensembles_iso_ordre_reciproque.py
      - ensembles_iso_unicite.py
      - ensembles_iso_unicite_finale.py
      - ensembles_iso_unicite_sous_domaine.py
      - ensembles_restriction_iso_pieces.py
  - **lemme4_segments/** — _III.2 (Lemme 4, segments)_ (8)
      - ensembles_lemme4_croissante.py
      - ensembles_lemme4_sous_domaine.py
      - ensembles_bien_ordonne_lemme_1_segments.py
      - ensembles_bien_ordonne_seg_iso.py
      - ensembles_bien_ordonne_total.py
      - ensembles_segments_construction.py
      - ensembles_segment_comparabilite_abstrait.py
      - ensembles_ordre_induit_sousensemble.py
  - **maximalite/** — _III.2 (Th.3, maximalité de h)_ (6)
      - ensembles_maximalite_adjoint_bridge.py
      - ensembles_maximalite_close.py
      - ensembles_maximalite_substantielle.py
      - ensembles_trichotomie_maximalite_preuve.py
      - ensembles_trichotomie_scaffold_maximalite.py
      - ensembles_trichotomie_extension_iso.py
  - **temoins_comparabilite/** — _III.2 (Lemme 1, témoins / Prop.1)_ (5)
      - ensembles_temoin_commun.py
      - ensembles_temoin_couvrant.py
      - ensembles_temoin_deux_couples.py
      - ensembles_trichotomie_prop1.py
      - ensembles_codomaine_reconciliation.py
- **iii_3_equipotence_cardinaux/** — _III.3_ (7)
  - **cantor/** — _III.3_ (1)
      - ensembles_cantor.py
  - **cantor_bernstein/** — _III.3.2_ (3)
      - ensembles_cantor_bernstein.py
      - ensembles_cantor_bernstein_bij.py
      - ensembles_cantor_bernstein_fin.py
  - **definitions_cardinaux/** — _III.3_ (3)
      - ensembles_cardinaux.py
      - ensembles_cardinaux_theoremes.py
      - ensembles_cardinaux_consequences.py
  - **equipotence/** — _III.3.1_ (6)
      - ensembles_equipotence.py
      - ensembles_equivalence.py
      - ensembles_bijection.py
      - ensembles_composee_bijection.py
      - ensembles_vide_singleton.py
      - ensembles_reunion_somme_bijection.py
  - **ordre_cardinaux/** — _III.3.2_ (9)
      - ensembles_cardinaux_ordre.py
      - ensembles_cardinaux_props_restantes_ordre.py
      - ensembles_cardinal_ordre_props.py
      - ensembles_comparabilite.py
      - ensembles_cardinaux_bornes.py
      - ensembles_cardinaux_un_borne.py
      - ensembles_ordre_strict_petits.py
      - ensembles_sup_cardinal.py
      - ensembles_cardinaux_borne_sup.py
  - **props_restantes/** — _III.3 / III.3.6_ (6)
      - ensembles_cardinaux_props_restantes.py
      - ensembles_cardinaux_props_restantes_prop7.py
      - ensembles_prop3_prop4cor_iii3.py
      - ensembles_prop13_complement.py
      - ensembles_prop13_full_iii3.py
      - ensembles_divisibilite_propre.py
  - **somme_produit_bornes/** — _III.3.2-3.5_ (5)
      - ensembles_cardinaux_bornes_somme.py
      - ensembles_bornes_exposant.py
      - ensembles_eq_exposant_invariant.py
      - ensembles_injectif_graphe_pont.py
      - ensembles_recollement_famille_injectif.py
- **iii_4_ordinal_cardinal/** — _III.4_ (4)
  - **bon_ordre_intervalle/** — _III.4 (gate ℕ, clause/bon-ordre)_ (9)
      - ensembles_bon_ordre_intervalle_ordinal.py
      - ensembles_clause_plus_petit.py
      - ensembles_clause_plus_petit_correspondance.py
      - ensembles_clause_plus_petit_monotonie.py
      - ensembles_bien_ordonne_lemme_0_ordre_total.py
      - ensembles_bien_ordonne_lemme_2_ordre_clause.py
      - ensembles_bien_ordonne_lemme_3_assemblage.py
      - ensembles_ordinal_cardinal_ordre.py
      - ensembles_ordinaux_bien_ordonnes.py
  - **equipotence_retrait/** — _III.4_ (1)
      - ensembles_equipotence_retrait.py
  - **ordinal_cardinal_correspondance/** — _III.4_ (5)
      - ensembles_ordinal_cardinal.py
      - ensembles_ordinal_cardinal_bon_ordre.py
      - ensembles_ordinal_cardinal_correspondance.py
      - ensembles_segments_ordinaux.py
      - ensembles_cardinal_pas_entre_univ.py
  - **realisation_segment/** — _III.4 (réalisation segment)_ (6)
      - ensembles_realisation_segment_close.py
      - ensembles_realisation_segment_preuve.py
      - ensembles_subset_realise_close.py
      - ensembles_transport_sous_ensemble.py
      - ensembles_hyp_transport_ordinal_preuve.py
      - ensembles_gate_onto_top.py
- **iii_5_entiers/** — _III.5_ (5)
    - ensembles_n_arith_iii5.py
    - ensembles_parite_iii5.py
    - ensembles_puissance_deux_trois_NN.py
    - ensembles_puissance_entiers_inconditionnel.py
    - ensembles_produit_union_carre.py
- **iii_6_infinis/** — _III.6_ (5)
  - **chaine_recollement/** — _III.6.3 (recollement de chaîne)_ (5)
      - ensembles_chaine_frame_membership.py
      - ensembles_chaine_surjective_frame.py
      - ensembles_chaine_temoin_abstrait.py
      - ensembles_union_chaine_bijection.py
      - ensembles_ponts_couple_valeur_surj.py
  - **denombrable/** — _III.6 (Lemme 2, dénombrable)_ (2)
      - ensembles_denombrable_carre_iii6.py
      - ensembles_denombrable_injection_iii6.py
  - **frame_zorn/** — _III.6.3 (poset 𝔉 de Zorn)_ (6)
      - ensembles_frame_a_maximal.py
      - ensembles_frame_extension_finale.py
      - ensembles_frame_inductif_assemblage.py
      - ensembles_frame_maximal_clos.py
      - ensembles_frame_ordre_axiome.py
      - ensembles_frame_ordre_est_ordre.py
  - **hessenberg/** — _III.6.3 (Th.2 Hessenberg)_ (2)
    - **assemblage_vrai/** — _III.6.3 (assemblage non-vacuous)_ (10)
        - ensembles_hessenberg_chaine_vraie.py
        - ensembles_hessenberg_stepb.py
        - ensembles_hessenberg_stepb2.py
        - ensembles_hessenberg_step_b_classify.py
        - ensembles_hessenberg_p5.py
        - ensembles_hessenberg_p5c.py
        - ensembles_hessenberg_vrai.py
        - ensembles_hessenberg_vrai_final.py
        - ensembles_hessenberg_vrai_haut.py
        - ensembles_hessenberg_recollement_final.py
    - **coeur/** — _III.6.3_ (9)
        - ensembles_hessenberg.py
        - ensembles_hessenberg_hard.py
        - ensembles_hessenberg_inductivite.py
        - ensembles_hessenberg_maximal_card.py
        - ensembles_hessenberg_extension.py
        - ensembles_hessenberg_2b3b.py
        - ensembles_hessenberg_structural_discharge.py
        - ensembles_cadre_plat.py
        - ensembles_descentes_inconditionnelles.py
  - **infinis_descentes/** — _III.6.1_ (1)
      - ensembles_fini_inf_egal_infini.py

  **Trous du livre (dossiers vides à créer) :**
  - `iii_3_equipotence_cardinaux/iii_3_3_definition_ordre` — _III.3.3_ : III.3.3 (≤ pour cardinaux, définition de l'ordre via injection) n'a pas de fichier dédié distinct — la matière est dispersée dans ordre_cardinaux ; dossier vide pour matérialiser la sous-section.
  - `iii_6_infinis/iii_6_1_definition_infini` — _III.6.1_ : III.6.1 (définition cardinal infini) : seul fini_inf_egal_infini touche la remarque Déf.1 ; aucun fichier ne couvre la définition propre de l'infini / ℵ0 — trou à rendre visible.
  - `iii_6_infinis/iii_6_2_proprietes_infinis` — _III.6.2_ : III.6.2 (propriétés des ensembles infinis, partie inférieure infinie) non couverte par un fichier dédié.
  - `iii_7_limites_proj_induct` — _III.7_ : III.7 (limites projectives et inductives) entièrement absente du paquet cardinaux — trou de couverture du livre.

## bourbaki/cardinaux/arithmetique  (42 fichiers → 46 déplacements)

- **(racine du paquet)/** — _III.3_ (7)
    - __init__.py
- **fondations/** — _II.3.1_ (1)
    - ensembles_graphe_de.py
- **iii_3_2_monotonie/** — _III.3.2_ (5)
    - ensembles_somme_monotone.py
    - ensembles_arith_cardinale_props_produit_monotone.py
    - ensembles_arith_cardinale_props_exposant_monotone.py
    - ensembles_exposant_monotone_exp_incond.py
    - ensembles_exposant_monotone_incond.py
- **iii_3_3_produit/** — _III.3.3_ (5)
    - ensembles_arith_cardinale.py
    - ensembles_produit_equipotence.py
    - ensembles_produit_commute.py
    - ensembles_produit_petits.py
    - ensembles_distributivite_cardinale.py
- **iii_3_3_somme/** — _III.3.3_ (5)
    - ensembles_arith_somme.py
    - ensembles_somme_equipotence.py
    - ensembles_somme_commute.py
    - ensembles_somme_associe.py
    - ensembles_somme_zero.py
- **iii_3_4_prop8_successeur/** — _III.3.4_ (8)
    - ensembles_prop8_successeur.py
    - ensembles_prop8_plus_point.py
    - ensembles_prop8_assemblage.py
    - ensembles_prop8_transposition.py
    - ensembles_prop8_fini2.py
    - ensembles_copie_marquee.py
- **iii_3_5_exposant/** — _III.3.5_ (4)
  - **definition/** — _III.3.5_ (4)
      - ensembles_exposant_cardinal.py
      - ensembles_exposant_un_base.py
      - ensembles_exposant_zero.py
  - **prop10_currying/** — _III.3.5_ (7)
      - ensembles_exposant_produit.py
      - ensembles_prop10_currying.py
      - ensembles_prop10_inj_curry.py
      - ensembles_prop10_inj_uncurry.py
      - ensembles_prop10_close.py
      - ensembles_prop10_final_close.py
      - ensembles_prop10cor2_iii3.py
  - **prop12_powerset/** — _III.3.5_ (5)
      - ensembles_powerset_exp.py
      - ensembles_powerset_deux.py
      - ensembles_prop12_powerset.py
      - ensembles_prop12_fin.py
  - **prop9_exp_somme/** — _III.3.5_ (6)
      - ensembles_exposant_somme.py
      - ensembles_prop9_exp_somme.py
      - ensembles_prop9_final.py
      - ensembles_prop9_final_close.py
      - ensembles_prop9_close.py
      - ensembles_prop9_cloture.py

  **Trous du livre (dossiers vides à créer) :**
  - `iii_3_5_exposant/prop11_petits_cas` — _III.3.5_ : Proposition 11 (1^a=1, 0^a=0, a^1=a, a^0=1) — actuellement absorbée dans definition/ ; un dossier dedie la rendrait visible comme sous-section distincte de la Definition 4. Optionnel : non cree ici car les 3 fichiers exposant_un_base/exposant_zero/exposant_un couvrent deja la matiere et tiennent dans definition/.
  - `iii_3_6_familles` — _III.3.6_ : Somme/produit d'une FAMILLE de cardinaux (∑_ι a_ι, ∏_ι a_ι, au-dela du cas binaire) — aucun fichier du paquet ne traite le cas indexe general ; trou de couverture a rendre visible.
  - `iii_3_7_inegalites` — _III.3.7_ : Inegalites sur somme/produit de familles et theoreme de Konig — aucun fichier present ; trou de couverture.

## bourbaki/entiers  (59 fichiers → 58 déplacements)

- **(racine du paquet)/** — _III.4-III.6_ (4)
    - __init__.py
- **iii_4_entiers_finis/** — _III.4_ (5)
  - **iii_4_1_definitions_premiers_entiers/** — _III.4.1_ (8)
      - ensembles_entiers.py
      - ensembles_zero_plus_un.py
      - ensembles_fini_successeur.py
      - ensembles_fini_zero.py
      - ensembles_fini_un.py
      - ensembles_fini_deux.py
      - ensembles_fini_trois_quatre.py
      - ensembles_entiers_theoremes.py
  - **iii_4_2_cor4_inj_surj_bij/** — _III.4.2_ (3)
      - ensembles_cor4_inj_surj_iii4.py
      - ensembles_cor4_surj_inj_iii4.py
      - ensembles_cor4_surj_inj_fin.py
  - **iii_4_2_finis_props/** — _III.4.2_ (3)
      - ensembles_finis_props.py
      - ensembles_finis_props2.py
      - ensembles_chap3_props_restantes.py
  - **iii_4_2_pigeonhole_surgery/** — _III.4.2_ (4)
      - ensembles_pigeonhole_sous_lemme.py
      - ensembles_partie_equipotente_finie.py
      - ensembles_retrait_point.py
      - ensembles_retrait_surgery.py
  - **iii_4_recurrence_c61_existence_n/** — _III.4.2_ (5)
      - ensembles_recurrence_C61.py
      - ensembles_principe_recurrence_preuve.py
      - ensembles_recurrence_vraie.py
      - ensembles_predecesseur_prop2.py
      - ensembles_cardinal_pas_entre.py
- **iii_5_calcul_entiers/** — _III.5_ (6)
  - **iii_5_1_somme_produit_entiers/** — _III.5.1_ (5)
      - ensembles_combinatoire_iii5.py
      - ensembles_prop3_produit_entier_iii5.py
      - ensembles_calcul_entiers_props.py
      - ensembles_simplification_additive.py
      - ensembles_recurrence_finie.py
  - **iii_5_2_inegalites_ordre_soustraction/** — _III.5.2_ (6)
      - ensembles_prop2_strict_iii5.py
      - ensembles_prop3_strict_mono_iii5.py
      - ensembles_successeur_ordre.py
      - ensembles_prop4_strict_iii5.py
      - ensembles_prop4_surj_iii5.py
      - ensembles_soustraction_iii5.py
  - **iii_5_5_caracteristique_combinatoire/** — _III.5.5_ (2)
      - ensembles_prop7_caracteristique_iii5.py
      - ensembles_prop9_bergers_iii5.py
  - **iii_5_8_factorielle/** — _III.5.8_ (4)
      - ensembles_factorielle_iii5.py
      - ensembles_factorielle_existence.py
      - ensembles_factorielle_existence_vrai.py
      - ensembles_factorielle_gluing_diag.py
  - **iii_5_intervalles_comptage/** — _III.5.3_ (6)
      - ensembles_prop5_intervalle.py
      - ensembles_prop5_prop4_iii5.py
      - ensembles_prop5_general_iii5.py
      - ensembles_prop6_bien_ordonne_iii5.py
      - ensembles_prop6_fini_interval_iii5.py
      - ensembles_prop6_iso_iii5.py
  - **iii_5_notions_complementaires/** — _III.5.4-III.5.7_ (2)
      - ensembles_entiers_notions_arith.py
      - ensembles_entiers_notions_suites.py
- **iii_6_infinis/** — _III.6_ (3)
  - **iii_6_1_n_objet_existence/** — _III.6.1_ (4)
      - ensembles_N_collectivise.py
      - ensembles_ensemble_NN.py
      - ensembles_n_bien_ordonne.py
      - ensembles_aleph0.py
  - **iii_6_2_recursion_c62/** — _III.6.2_ (2)
      - ensembles_c62_recursion.py
      - ensembles_recursion_hygienic.py
  - **iii_6_3_infinis_denombrables/** — _III.6_ (4)
      - ensembles_infinis.py
      - ensembles_infinis_iii6.py
      - ensembles_infinis_props.py
      - ensembles_infinis_theoremes.py

  **Trous du livre (dossiers vides à créer) :**
  - `iii_5_calcul_entiers/iii_5_6_divisibilite_division_euclidienne` — _III.5.6_ : Definition 1 de III.5.6 (multiple, diviseur, quotient a/b, division euclidienne) n'a aucun fichier dedie : les notions sont seulement esquissees dans ensembles_entiers_notions_arith (range en notions_complementaires) et dans ensembles_entiers.py. Aucune proposition propre a III.5.6 close. Dossier vide pour rendre visible le trou.
  - `iii_5_calcul_entiers/iii_5_7_developpement_base_b` — _III.5.7_ : Le developpement de base b (chiffre, symbole numerique) de III.5.7 n'a aucun module propre : seulement evoque dans ensembles_entiers_notions_arith. Aucune proposition close. Dossier vide pour signaler le trou de couverture.
  - `iii_6_infinis/iii_6_4_limites_proj_induct` — _III.7_ : Note : la limite projective/inductive est III.7 dans la table cible, hors perimetre entiers ; aucun fichier ici. Ce dossier vide n'est PROPOSE qu'a titre indicatif si l'on veut materialiser le voisinage III.7 sous le paquet ; sinon a ignorer. Aucun trou interne a III.4-III.6 n'existe par ailleurs.

## bourbaki/structures  (17 fichiers → 15 déplacements)

- **(racine du paquet)/** — _IV_ (4)
    - __init__.py
- **iv_1_structures_isomorphismes/** — _IV.1_ (5)
    - ensembles_especes_echelon.py
    - ensembles_especes_typification.py
    - ensembles_especes.py
    - ensembles_especes_deduction.py
    - ensembles_transport_iso_props.py
- **iv_2_morphismes_structures_derivees/** — _IV.2_ (6)
    - ensembles_universel_morphismes.py
    - ensembles_universel_finale.py
    - ensembles_structures_props.py
    - ensembles_structures_derivees_props.py
    - ensembles_structures_residus.py
  - **cst_criteres/** — _IV.1-IV.2_ (4)
      - ensembles_CST_criteres.py
      - ensembles_chap4_props_restantes.py
      - ensembles_cst_criteres_suite.py
      - ensembles_cst_produit_quotient.py
- **iv_3_applications_universelles/** — _IV.3_ (2)
    - ensembles_universel_applications.py
    - ensembles_structures_complements.py


---

# Annexe — liste complète des déplacements


### bourbaki/logique
```
bourbaki/logique/__init__.py
   -> bourbaki/logique/__init__.py
bourbaki/logique/formule.py
   -> bourbaki/logique/i_1_termes_relations/formule.py
bourbaki/logique/lecture.py
   -> bourbaki/logique/i_1_termes_relations/lecture.py
bourbaki/logique/notation.py
   -> bourbaki/logique/i_1_termes_relations/notation.py
bourbaki/logique/propositions.py
   -> bourbaki/logique/i_1_termes_relations/propositions.py
bourbaki/logique/criteres/criteres_CS.py
   -> bourbaki/logique/i_1_termes_relations/criteres_CS.py
bourbaki/logique/criteres/criteres_CF.py
   -> bourbaki/logique/i_1_termes_relations/criteres_CF.py
bourbaki/logique/noyau.py
   -> bourbaki/logique/i_2_criteres_C/noyau/noyau.py
bourbaki/logique/noyau_abrege.py
   -> bourbaki/logique/i_2_criteres_C/noyau/noyau_abrege.py
bourbaki/logique/criteres/criteres_C.py
   -> bourbaki/logique/i_2_criteres_C/criteres/criteres_C.py
bourbaki/logique/criteres/criteres_C_suite.py
   -> bourbaki/logique/i_2_criteres_C/criteres/criteres_C_suite.py
bourbaki/logique/criteres/criteres_C_suite2.py
   -> bourbaki/logique/i_2_criteres_C/criteres/criteres_C_suite2.py
bourbaki/logique/tactiques/tactiques.py
   -> bourbaki/logique/i_2_criteres_C/tactiques/tactiques.py
bourbaki/logique/tactiques/tactiques_prop.py
   -> bourbaki/logique/i_2_criteres_C/tactiques/tactiques_prop.py
bourbaki/logique/tactiques/tactiques_abrege.py
   -> bourbaki/logique/i_2_criteres_C/tactiques/tactiques_abrege.py
bourbaki/logique/tactiques/tactiques_abrege2.py
   -> bourbaki/logique/i_2_criteres_C/tactiques/tactiques_abrege2.py
bourbaki/logique/congruence_quantif.py
   -> bourbaki/logique/i_3_quantifies/congruence_quantif.py
bourbaki/logique/criteres/criteres_quantif2.py
   -> bourbaki/logique/i_3_quantifies/criteres_quantif2.py
bourbaki/logique/tactiques/tactiques_abrege_quantif.py
   -> bourbaki/logique/i_3_quantifies/tactiques_abrege_quantif.py
bourbaki/logique/tactiques/ensembles_alpha_bridge.py
   -> bourbaki/logique/i_3_quantifies/ensembles_alpha_bridge.py
bourbaki/logique/tactiques/tactiques_egalite.py
   -> bourbaki/logique/i_4_egalitaires/tactiques_egalite.py
bourbaki/logique/tactiques/tactiques_abrege_egalite.py
   -> bourbaki/logique/i_4_egalitaires/tactiques_abrege_egalite.py
bourbaki/logique/verificateur_preuve.py
   -> bourbaki/logique/verification/verificateur_preuve.py
bourbaki/logique/criteres/__init__.py
   -> bourbaki/logique/i_2_criteres_C/criteres/__init__.py
bourbaki/logique/tactiques/__init__.py
   -> bourbaki/logique/i_2_criteres_C/tactiques/__init__.py
```

### bourbaki/ensembles
```
bourbaki/ensembles/ensembles_abrege.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_abrege.py
bourbaki/ensembles/ensembles_theoremes.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_theoremes.py
bourbaki/ensembles/ensembles_algebre_booleenne.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_algebre_booleenne.py
bourbaki/ensembles/ensembles_inclusion_treillis.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_inclusion_treillis.py
bourbaki/ensembles/ensembles_vide_identites.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_vide_identites.py
bourbaki/ensembles/ensembles_difference_identites.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_difference_identites.py
bourbaki/ensembles/base/ensembles_vide.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_vide.py
bourbaki/ensembles/base/ensembles_difference.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_difference.py
bourbaki/ensembles/base/ensembles_couples.py
   -> bourbaki/ensembles/ii_2_couples_produit/ensembles_couples.py
bourbaki/ensembles/ensembles_produit_distributif.py
   -> bourbaki/ensembles/ii_2_couples_produit/ensembles_produit_distributif.py
bourbaki/ensembles/base/ensembles_fondations_notions.py
   -> bourbaki/ensembles/ii_3_correspondances/ensembles_fondations_notions.py
bourbaki/ensembles/base/ensembles_correspondances.py
   -> bourbaki/ensembles/ii_3_correspondances/ensembles_correspondances.py
bourbaki/ensembles/ensembles_chap2_props_restantes.py
   -> bourbaki/ensembles/ii_4_reunion_intersection/ensembles_chap2_props_restantes.py
bourbaki/ensembles/ensembles_quotient_props.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_quotient_props_graphe.py
bourbaki/ensembles/ensembles_quotient_produit_restant.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_quotient_produit_restant.py
bourbaki/ensembles/relations/ensembles_quotient_props.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_quotient_props.py
bourbaki/ensembles/relations/ensembles_quotient_complements.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_quotient_complements.py
bourbaki/ensembles/relations/ensembles_quotient_c56_c57.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_quotient_c56_c57.py
bourbaki/ensembles/relations/ensembles_decomposition_quotient.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_decomposition_quotient.py
bourbaki/ensembles/relations/ensembles_decomposition_effective.py
   -> bourbaki/ensembles/ii_6_equivalence/ensembles_decomposition_effective.py
bourbaki/ensembles/ensembles_props_diverses.py
   -> bourbaki/ensembles/iii_3_ordre_cardinaux/ensembles_props_diverses.py
bourbaki/ensembles/theorie_ensembles.py
   -> bourbaki/ensembles/ii_1_axiomes_algebre/theorie_ensembles.py
```

### bourbaki/ensembles/fonctions
```
bourbaki/ensembles/fonctions/ensembles_reciproque.py
   -> bourbaki/ensembles/fonctions/ii_3_2_reciproque/ensembles_reciproque.py
bourbaki/ensembles/fonctions/ensembles_composee.py
   -> bourbaki/ensembles/fonctions/ii_3_3_composee_graphes/ensembles_composee.py
bourbaki/ensembles/fonctions/ensembles_composee_reciproque.py
   -> bourbaki/ensembles/fonctions/ii_3_3_composee_graphes/ensembles_composee_reciproque.py
bourbaki/ensembles/fonctions/ensembles_fonctions.py
   -> bourbaki/ensembles/fonctions/ii_3_4_fonctions_valeur/ensembles_fonctions.py
bourbaki/ensembles/fonctions/ensembles_valeur_codomaine.py
   -> bourbaki/ensembles/fonctions/ii_3_4_fonctions_valeur/ensembles_valeur_codomaine.py
bourbaki/ensembles/fonctions/ensembles_composee_assoc.py
   -> bourbaki/ensembles/fonctions/ii_3_4_fonctions_valeur/ensembles_composee_assoc.py
bourbaki/ensembles/fonctions/ensembles_extensionnalite.py
   -> bourbaki/ensembles/fonctions/ii_3_general/ensembles_extensionnalite.py
bourbaki/ensembles/fonctions/ensembles_fonctions_complements.py
   -> bourbaki/ensembles/fonctions/ii_3_general/ensembles_fonctions_complements.py
bourbaki/ensembles/fonctions/ensembles_fonctions_props2.py
   -> bourbaki/ensembles/fonctions/ii_3_general/ensembles_fonctions_props2.py
bourbaki/ensembles/fonctions/ensembles_prop7_9_ii3.py
   -> bourbaki/ensembles/fonctions/ii_3_general/ensembles_prop7_9_ii3.py
bourbaki/ensembles/fonctions/ensembles_restrictions.py
   -> bourbaki/ensembles/fonctions/ii_3_5_restrictions_prolongements/ensembles_restrictions.py
bourbaki/ensembles/fonctions/ensembles_sous_famille.py
   -> bourbaki/ensembles/fonctions/ii_3_5_restrictions_prolongements/ensembles_sous_famille.py
bourbaki/ensembles/fonctions/ensembles_fonction_terme.py
   -> bourbaki/ensembles/fonctions/ii_3_6_fonction_terme/ensembles_fonction_terme.py
bourbaki/ensembles/fonctions/ensembles_fonctions_coordonnees.py
   -> bourbaki/ensembles/fonctions/ii_3_6_fonction_terme/ensembles_fonctions_coordonnees.py
bourbaki/ensembles/fonctions/ensembles_projections_terme.py
   -> bourbaki/ensembles/fonctions/ii_3_6_fonction_terme/ensembles_projections_terme.py
bourbaki/ensembles/fonctions/ensembles_fonctions_composee.py
   -> bourbaki/ensembles/fonctions/ii_3_7_composee_fonctions/ensembles_fonctions_composee.py
bourbaki/ensembles/fonctions/ensembles_retractions.py
   -> bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_retractions.py
bourbaki/ensembles/fonctions/ensembles_retractions_props.py
   -> bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_retractions_props.py
bourbaki/ensembles/fonctions/ensembles_composee_valeurs.py
   -> bourbaki/ensembles/fonctions/ii_3_8_retractions_sections/ensembles_composee_valeurs.py
bourbaki/ensembles/fonctions/ensembles_projections.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/ii_2_projections/ensembles_projections.py
bourbaki/ensembles/fonctions/ensembles_application_valeur.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/ii_5_produit_famille/ensembles_application_valeur.py
bourbaki/ensembles/fonctions/ensembles_composee_triple_fonctionnelle.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/ii_5_produit_famille/ensembles_composee_triple_fonctionnelle.py
bourbaki/ensembles/fonctions/ensembles_currying_ii5.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/ii_5_produit_famille/ensembles_currying_ii5.py
bourbaki/ensembles/fonctions/ensembles_recollement_bijection.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iii_3_recollement/ensembles_recollement_bijection.py
bourbaki/ensembles/fonctions/ensembles_restriction_somme.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iii_3_recollement/ensembles_restriction_somme.py
bourbaki/ensembles/fonctions/ensembles_dom_image_reunion.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iii_3_recollement/ensembles_dom_image_reunion.py
bourbaki/ensembles/fonctions/ensembles_isomorphismes.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iv_structures/ensembles_isomorphismes.py
bourbaki/ensembles/fonctions/ensembles_morphismes.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iv_structures/ensembles_morphismes.py
bourbaki/ensembles/fonctions/ensembles_applications_universelles.py
   -> bourbaki/ensembles/fonctions/hors_ii_3/iv_structures/ensembles_applications_universelles.py
bourbaki/ensembles/fonctions/__init__.py
   -> bourbaki/ensembles/fonctions/__init__.py
```

### bourbaki/ensembles/familles
```
bourbaki/ensembles/familles/ensembles_familles.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_familles.py
bourbaki/ensembles/familles/ensembles_familles_algebre.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_familles_algebre.py
bourbaki/ensembles/familles/ensembles_reunion_sup_univ_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_reunion_sup_univ_ii4.py
bourbaki/ensembles/familles/ensembles_inter_inf_univ_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_inter_inf_univ_ii4.py
bourbaki/ensembles/familles/ensembles_reparam_inter_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_1_definitions_algebre/ensembles_reparam_inter_ii4.py
bourbaki/ensembles/familles/ensembles_familles_demorgan.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_demorgan/ensembles_familles_demorgan.py
bourbaki/ensembles/familles/ensembles_image_recip_famille_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_image_famille/ensembles_image_recip_famille_ii4.py
bourbaki/ensembles/familles/ensembles_reciproque_reunion_binaire_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_image_famille/ensembles_reciproque_reunion_binaire_ii4.py
bourbaki/ensembles/familles/ensembles_image_algebre_binaire_ii4.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_image_famille/ensembles_image_algebre_binaire_ii4.py
bourbaki/ensembles/familles/ensembles_recollement_props.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_recollement_somme/ensembles_recollement_props.py
bourbaki/ensembles/familles/ensembles_somme_disjointe.py
   -> bourbaki/ensembles/familles/ii_4_reunion_intersection_familles/ii_4_recollement_somme/ensembles_somme_disjointe.py
bourbaki/ensembles/familles/ensembles_produit_famille.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_definitions/ensembles_produit_famille.py
bourbaki/ensembles/familles/ensembles_extensionnalite_produit.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_definitions/ensembles_extensionnalite_produit.py
bourbaki/ensembles/familles/ensembles_extension_canonique.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_1_extension_canonique/ensembles_extension_canonique.py
bourbaki/ensembles/familles/ensembles_produit_props.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_1_extension_canonique/ensembles_produit_props.py
bourbaki/ensembles/familles/ensembles_produit_props_fonctoriel.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_1_extension_canonique/ensembles_produit_props_fonctoriel.py
bourbaki/ensembles/familles/ensembles_produit_props_projection.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_4_projection_partielle/ensembles_produit_props_projection.py
bourbaki/ensembles/familles/ensembles_produit_props2.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_6_7_algebre_produit/ensembles_produit_props2.py
bourbaki/ensembles/familles/ensembles_produit_monotone_ii5.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_6_7_algebre_produit/ensembles_produit_monotone_ii5.py
bourbaki/ensembles/familles/ensembles_produit_egal_facteurs_ii5.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_6_7_algebre_produit/ensembles_produit_egal_facteurs_ii5.py
bourbaki/ensembles/familles/ensembles_produit_inter_ii5.py
   -> bourbaki/ensembles/familles/ii_5_produit_famille/ii_5_6_7_algebre_produit/ensembles_produit_inter_ii5.py
bourbaki/ensembles/familles/ensembles_produit.py
   -> bourbaki/ensembles/familles/ii_2_produit_deux_ensembles/ensembles_produit.py
bourbaki/ensembles/familles/ensembles_limites.py
   -> bourbaki/ensembles/familles/iii_7_limites/ensembles_limites.py
bourbaki/ensembles/familles/ensembles_limites_iii7.py
   -> bourbaki/ensembles/familles/iii_7_limites/ensembles_limites_iii7.py
bourbaki/ensembles/familles/ensembles_cone_unicite.py
   -> bourbaki/ensembles/familles/iii_7_limites/ensembles_cone_unicite.py
bourbaki/ensembles/familles/ensembles_limites_prop2_3_iii7.py
   -> bourbaki/ensembles/familles/iii_7_limites/ensembles_limites_prop2_3_iii7.py
bourbaki/ensembles/familles/ensembles_limites_prop4plus_iii7.py
   -> bourbaki/ensembles/familles/iii_7_limites/ensembles_limites_prop4plus_iii7.py
bourbaki/ensembles/familles/__init__.py
   -> bourbaki/ensembles/familles/__init__.py
```

### bourbaki/ordre
```
bourbaki/ordre/__init__.py
   -> bourbaki/ordre/__init__.py
bourbaki/ordre/ensembles_ordre.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre.py
bourbaki/ordre/ensembles_ordre_relation.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre_relation.py
bourbaki/ordre/ensembles_ordre_vocab.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre_vocab.py
bourbaki/ordre/ensembles_iii1_ordre_props.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_iii1_ordre_props.py
bourbaki/ordre/ensembles_ordre_produit_antisym.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre_produit_antisym.py
bourbaki/ordre/ensembles_ordre_monotone.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre_monotone.py
bourbaki/ordre/ensembles_ordre_treillis_props.py
   -> bourbaki/ordre/iii_1_relations_ordre/ordre_treillis/ensembles_ordre_treillis_props.py
bourbaki/ordre/ensembles_sup_generiques_iii1.py
   -> bourbaki/ordre/iii_1_relations_ordre/bornes_sup/ensembles_sup_generiques_iii1.py
bourbaki/ordre/ensembles_sup_prop7_8_iii1.py
   -> bourbaki/ordre/iii_1_relations_ordre/bornes_sup/ensembles_sup_prop7_8_iii1.py
bourbaki/ordre/ensembles_iso_ordre_canon.py
   -> bourbaki/ordre/iii_1_relations_ordre/isomorphismes_ordre/ensembles_iso_ordre_canon.py
bourbaki/ordre/ensembles_valeur_bridge.py
   -> bourbaki/ordre/iii_1_relations_ordre/isomorphismes_ordre/ensembles_valeur_bridge.py
bourbaki/ordre/ensembles_pont_binder.py
   -> bourbaki/ordre/iii_1_relations_ordre/isomorphismes_ordre/ensembles_pont_binder.py
bourbaki/ordre/ensembles_bon_ordre.py
   -> bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_bon_ordre.py
bourbaki/ordre/ensembles_sous_bien_ordonne.py
   -> bourbaki/ordre/iii_2_bon_ordre/bon_ordre_segments/ensembles_sous_bien_ordonne.py
bourbaki/ordre/ensembles_zorn.py
   -> bourbaki/ordre/iii_2_bon_ordre/zorn_zermelo/ensembles_zorn.py
bourbaki/ordre/ensembles_zorn_theoreme.py
   -> bourbaki/ordre/iii_2_bon_ordre/zorn_zermelo/ensembles_zorn_theoreme.py
bourbaki/ordre/ensembles_zermelo.py
   -> bourbaki/ordre/iii_2_bon_ordre/zorn_zermelo/ensembles_zermelo.py
bourbaki/ordre/ensembles_bourbaki_witt.py
   -> bourbaki/ordre/iii_2_bon_ordre/zorn_zermelo/ensembles_bourbaki_witt.py
bourbaki/ordre/ensembles_bourbaki_witt_chaine.py
   -> bourbaki/ordre/iii_2_bon_ordre/zorn_zermelo/ensembles_bourbaki_witt_chaine.py
bourbaki/ordre/ensembles_recurrence_transfinie.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_recurrence_transfinie.py
bourbaki/ordre/ensembles_recursion_transfinie_existence.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_recursion_transfinie_existence.py
bourbaki/ordre/ensembles_c60_existence_close.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_existence_close.py
bourbaki/ordre/ensembles_c60_realisation.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_realisation.py
bourbaki/ordre/ensembles_c60_clauses.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_clauses.py
bourbaki/ordre/ensembles_c60_coeur.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_coeur.py
bourbaki/ordre/ensembles_c60_final.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_final.py
bourbaki/ordre/ensembles_c60_pont.py
   -> bourbaki/ordre/iii_2_bon_ordre/recurrence_transfinie/ensembles_c60_pont.py
bourbaki/ordre/ensembles_tukey_iii4.py
   -> bourbaki/ordre/iii_4_ensembles_finis/ensembles_tukey_iii4.py
bourbaki/ordre/ensembles_tukey_sous_lemme.py
   -> bourbaki/ordre/iii_4_ensembles_finis/ensembles_tukey_sous_lemme.py
bourbaki/ordre/ensembles_ordre_fini_iii4.py
   -> bourbaki/ordre/iii_4_ensembles_finis/ensembles_ordre_fini_iii4.py
bourbaki/ordre/ensembles_ordinaux.py
   -> bourbaki/ordre/iii_6_ordinaux/ensembles_ordinaux.py
bourbaki/ordre/ensembles_limites_canoniques.py
   -> bourbaki/ordre/iii_7_limites/ensembles_limites_canoniques.py
bourbaki/ordre/ensembles_cofinal.py
   -> bourbaki/ordre/iii_7_limites/ensembles_cofinal.py
bourbaki/ordre/ensembles_limites_props.py
   -> bourbaki/ordre/iii_7_limites/ensembles_limites_props.py
bourbaki/ordre/ensembles_limites_props2.py
   -> bourbaki/ordre/iii_7_limites/ensembles_limites_props2.py
```

### bourbaki/cardinaux
```
bourbaki/cardinaux/ensembles_iso_ordre_composee.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_iso_ordre_composee.py
bourbaki/cardinaux/ensembles_iso_ordre_reciproque.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_iso_ordre_reciproque.py
bourbaki/cardinaux/ensembles_iso_unicite.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_iso_unicite.py
bourbaki/cardinaux/ensembles_iso_unicite_finale.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_iso_unicite_finale.py
bourbaki/cardinaux/ensembles_iso_unicite_sous_domaine.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_iso_unicite_sous_domaine.py
bourbaki/cardinaux/ensembles_restriction_iso_pieces.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/iso_ordre/ensembles_restriction_iso_pieces.py
bourbaki/cardinaux/ensembles_lemme4_croissante.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_lemme4_croissante.py
bourbaki/cardinaux/ensembles_lemme4_sous_domaine.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_lemme4_sous_domaine.py
bourbaki/cardinaux/ensembles_bien_ordonne_lemme_1_segments.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_bien_ordonne_lemme_1_segments.py
bourbaki/cardinaux/ensembles_bien_ordonne_seg_iso.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_bien_ordonne_seg_iso.py
bourbaki/cardinaux/ensembles_bien_ordonne_total.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_bien_ordonne_total.py
bourbaki/cardinaux/ensembles_segments_construction.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_segments_construction.py
bourbaki/cardinaux/ensembles_segment_comparabilite_abstrait.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_segment_comparabilite_abstrait.py
bourbaki/cardinaux/ensembles_ordre_induit_sousensemble.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/lemme4_segments/ensembles_ordre_induit_sousensemble.py
bourbaki/cardinaux/ensembles_temoin_commun.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/temoins_comparabilite/ensembles_temoin_commun.py
bourbaki/cardinaux/ensembles_temoin_couvrant.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/temoins_comparabilite/ensembles_temoin_couvrant.py
bourbaki/cardinaux/ensembles_temoin_deux_couples.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/temoins_comparabilite/ensembles_temoin_deux_couples.py
bourbaki/cardinaux/ensembles_trichotomie_prop1.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/temoins_comparabilite/ensembles_trichotomie_prop1.py
bourbaki/cardinaux/ensembles_codomaine_reconciliation.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/temoins_comparabilite/ensembles_codomaine_reconciliation.py
bourbaki/cardinaux/ensembles_coincidence_decharge.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_coincidence_decharge.py
bourbaki/cardinaux/ensembles_coincidence_geometrie.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_coincidence_geometrie.py
bourbaki/cardinaux/ensembles_coincidence_pont.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_coincidence_pont.py
bourbaki/cardinaux/ensembles_coincidence_univ.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_coincidence_univ.py
bourbaki/cardinaux/ensembles_coincidence_univ_app.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_coincidence_univ_app.py
bourbaki/cardinaux/ensembles_fusion_app.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_fusion_app.py
bourbaki/cardinaux/ensembles_fusion_assemblage.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_fusion_assemblage.py
bourbaki/cardinaux/ensembles_fusion_depuis_coincidence_app.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/coincidence_fusion/ensembles_fusion_depuis_coincidence_app.py
bourbaki/cardinaux/ensembles_h_bien_defini.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_h_bien_defini.py
bourbaki/cardinaux/ensembles_h_est_graphe.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_h_est_graphe.py
bourbaki/cardinaux/ensembles_trichotomie_coherences.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_trichotomie_coherences.py
bourbaki/cardinaux/ensembles_trichotomie_h_iso.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_trichotomie_h_iso.py
bourbaki/cardinaux/ensembles_trichotomie_hgraphe_pr2seg.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_trichotomie_hgraphe_pr2seg.py
bourbaki/cardinaux/ensembles_trichotomie_restriction.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/h_coherences/ensembles_trichotomie_restriction.py
bourbaki/cardinaux/ensembles_maximalite_adjoint_bridge.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_maximalite_adjoint_bridge.py
bourbaki/cardinaux/ensembles_maximalite_close.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_maximalite_close.py
bourbaki/cardinaux/ensembles_maximalite_substantielle.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_maximalite_substantielle.py
bourbaki/cardinaux/ensembles_trichotomie_maximalite_preuve.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_trichotomie_maximalite_preuve.py
bourbaki/cardinaux/ensembles_trichotomie_scaffold_maximalite.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_trichotomie_scaffold_maximalite.py
bourbaki/cardinaux/ensembles_trichotomie_extension_iso.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/maximalite/ensembles_trichotomie_extension_iso.py
bourbaki/cardinaux/ensembles_trichotomie_assemble.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_assemble.py
bourbaki/cardinaux/ensembles_trichotomie_maillon_final.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_maillon_final.py
bourbaki/cardinaux/ensembles_trichotomie_pont_val.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_pont_val.py
bourbaki/cardinaux/ensembles_trichotomie_residuals.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_residuals.py
bourbaki/cardinaux/ensembles_trichotomie_scaffold.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_scaffold.py
bourbaki/cardinaux/ensembles_trichotomie_dom_segment.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_dom_segment.py
bourbaki/cardinaux/ensembles_trichotomie_temoin_adjonction.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_trichotomie_temoin_adjonction.py
bourbaki/cardinaux/ensembles_maillon_coherences_prouvees.py
   -> bourbaki/cardinaux/iii_2_trichotomie_ordinaux/assemblage/ensembles_maillon_coherences_prouvees.py
bourbaki/cardinaux/ensembles_equipotence.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_equipotence.py
bourbaki/cardinaux/ensembles_equivalence.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_equivalence.py
bourbaki/cardinaux/ensembles_bijection.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_bijection.py
bourbaki/cardinaux/ensembles_composee_bijection.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_composee_bijection.py
bourbaki/cardinaux/ensembles_vide_singleton.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_vide_singleton.py
bourbaki/cardinaux/ensembles_reunion_somme_bijection.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/equipotence/ensembles_reunion_somme_bijection.py
bourbaki/cardinaux/ensembles_cantor.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/cantor/ensembles_cantor.py
bourbaki/cardinaux/ensembles_cantor_bernstein.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/cantor_bernstein/ensembles_cantor_bernstein.py
bourbaki/cardinaux/ensembles_cantor_bernstein_bij.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/cantor_bernstein/ensembles_cantor_bernstein_bij.py
bourbaki/cardinaux/ensembles_cantor_bernstein_fin.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/cantor_bernstein/ensembles_cantor_bernstein_fin.py
bourbaki/cardinaux/ensembles_cardinaux.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/definitions_cardinaux/ensembles_cardinaux.py
bourbaki/cardinaux/ensembles_cardinaux_theoremes.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/definitions_cardinaux/ensembles_cardinaux_theoremes.py
bourbaki/cardinaux/ensembles_cardinaux_consequences.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/definitions_cardinaux/ensembles_cardinaux_consequences.py
bourbaki/cardinaux/ensembles_cardinaux_ordre.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinaux_ordre.py
bourbaki/cardinaux/ensembles_cardinaux_props_restantes_ordre.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinaux_props_restantes_ordre.py
bourbaki/cardinaux/ensembles_cardinal_ordre_props.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinal_ordre_props.py
bourbaki/cardinaux/ensembles_comparabilite.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_comparabilite.py
bourbaki/cardinaux/ensembles_cardinaux_bornes.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinaux_bornes.py
bourbaki/cardinaux/ensembles_cardinaux_un_borne.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinaux_un_borne.py
bourbaki/cardinaux/ensembles_ordre_strict_petits.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_ordre_strict_petits.py
bourbaki/cardinaux/ensembles_sup_cardinal.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_sup_cardinal.py
bourbaki/cardinaux/ensembles_cardinaux_borne_sup.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/ordre_cardinaux/ensembles_cardinaux_borne_sup.py
bourbaki/cardinaux/ensembles_cardinaux_bornes_somme.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/somme_produit_bornes/ensembles_cardinaux_bornes_somme.py
bourbaki/cardinaux/ensembles_bornes_exposant.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/somme_produit_bornes/ensembles_bornes_exposant.py
bourbaki/cardinaux/ensembles_eq_exposant_invariant.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/somme_produit_bornes/ensembles_eq_exposant_invariant.py
bourbaki/cardinaux/ensembles_injectif_graphe_pont.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/somme_produit_bornes/ensembles_injectif_graphe_pont.py
bourbaki/cardinaux/ensembles_recollement_famille_injectif.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/somme_produit_bornes/ensembles_recollement_famille_injectif.py
bourbaki/cardinaux/ensembles_cardinaux_props_restantes.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_cardinaux_props_restantes.py
bourbaki/cardinaux/ensembles_cardinaux_props_restantes_prop7.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_cardinaux_props_restantes_prop7.py
bourbaki/cardinaux/ensembles_prop3_prop4cor_iii3.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_prop3_prop4cor_iii3.py
bourbaki/cardinaux/ensembles_prop13_complement.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_prop13_complement.py
bourbaki/cardinaux/ensembles_prop13_full_iii3.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_prop13_full_iii3.py
bourbaki/cardinaux/ensembles_divisibilite_propre.py
   -> bourbaki/cardinaux/iii_3_equipotence_cardinaux/props_restantes/ensembles_divisibilite_propre.py
bourbaki/cardinaux/ensembles_bon_ordre_intervalle_ordinal.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_bon_ordre_intervalle_ordinal.py
bourbaki/cardinaux/ensembles_clause_plus_petit.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_clause_plus_petit.py
bourbaki/cardinaux/ensembles_clause_plus_petit_correspondance.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_clause_plus_petit_correspondance.py
bourbaki/cardinaux/ensembles_clause_plus_petit_monotonie.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_clause_plus_petit_monotonie.py
bourbaki/cardinaux/ensembles_bien_ordonne_lemme_0_ordre_total.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_bien_ordonne_lemme_0_ordre_total.py
bourbaki/cardinaux/ensembles_bien_ordonne_lemme_2_ordre_clause.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_bien_ordonne_lemme_2_ordre_clause.py
bourbaki/cardinaux/ensembles_bien_ordonne_lemme_3_assemblage.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_bien_ordonne_lemme_3_assemblage.py
bourbaki/cardinaux/ensembles_ordinal_cardinal_ordre.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_ordinal_cardinal_ordre.py
bourbaki/cardinaux/ensembles_ordinaux_bien_ordonnes.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/bon_ordre_intervalle/ensembles_ordinaux_bien_ordonnes.py
bourbaki/cardinaux/ensembles_ordinal_cardinal.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/ordinal_cardinal_correspondance/ensembles_ordinal_cardinal.py
bourbaki/cardinaux/ensembles_ordinal_cardinal_bon_ordre.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/ordinal_cardinal_correspondance/ensembles_ordinal_cardinal_bon_ordre.py
bourbaki/cardinaux/ensembles_ordinal_cardinal_correspondance.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/ordinal_cardinal_correspondance/ensembles_ordinal_cardinal_correspondance.py
bourbaki/cardinaux/ensembles_segments_ordinaux.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/ordinal_cardinal_correspondance/ensembles_segments_ordinaux.py
bourbaki/cardinaux/ensembles_cardinal_pas_entre_univ.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/ordinal_cardinal_correspondance/ensembles_cardinal_pas_entre_univ.py
bourbaki/cardinaux/ensembles_realisation_segment_close.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_realisation_segment_close.py
bourbaki/cardinaux/ensembles_realisation_segment_preuve.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_realisation_segment_preuve.py
bourbaki/cardinaux/ensembles_subset_realise_close.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_subset_realise_close.py
bourbaki/cardinaux/ensembles_transport_sous_ensemble.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_transport_sous_ensemble.py
bourbaki/cardinaux/ensembles_hyp_transport_ordinal_preuve.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_hyp_transport_ordinal_preuve.py
bourbaki/cardinaux/ensembles_gate_onto_top.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/realisation_segment/ensembles_gate_onto_top.py
bourbaki/cardinaux/ensembles_equipotence_retrait.py
   -> bourbaki/cardinaux/iii_4_ordinal_cardinal/equipotence_retrait/ensembles_equipotence_retrait.py
bourbaki/cardinaux/ensembles_n_arith_iii5.py
   -> bourbaki/cardinaux/iii_5_entiers/ensembles_n_arith_iii5.py
bourbaki/cardinaux/ensembles_parite_iii5.py
   -> bourbaki/cardinaux/iii_5_entiers/ensembles_parite_iii5.py
bourbaki/cardinaux/ensembles_puissance_deux_trois_NN.py
   -> bourbaki/cardinaux/iii_5_entiers/ensembles_puissance_deux_trois_NN.py
bourbaki/cardinaux/ensembles_puissance_entiers_inconditionnel.py
   -> bourbaki/cardinaux/iii_5_entiers/ensembles_puissance_entiers_inconditionnel.py
bourbaki/cardinaux/ensembles_produit_union_carre.py
   -> bourbaki/cardinaux/iii_5_entiers/ensembles_produit_union_carre.py
bourbaki/cardinaux/ensembles_hessenberg.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg.py
bourbaki/cardinaux/ensembles_hessenberg_hard.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_hard.py
bourbaki/cardinaux/ensembles_hessenberg_inductivite.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_inductivite.py
bourbaki/cardinaux/ensembles_hessenberg_maximal_card.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_maximal_card.py
bourbaki/cardinaux/ensembles_hessenberg_extension.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_extension.py
bourbaki/cardinaux/ensembles_hessenberg_2b3b.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_2b3b.py
bourbaki/cardinaux/ensembles_hessenberg_structural_discharge.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_hessenberg_structural_discharge.py
bourbaki/cardinaux/ensembles_cadre_plat.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_cadre_plat.py
bourbaki/cardinaux/ensembles_descentes_inconditionnelles.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/coeur/ensembles_descentes_inconditionnelles.py
bourbaki/cardinaux/ensembles_hessenberg_chaine_vraie.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_chaine_vraie.py
bourbaki/cardinaux/ensembles_hessenberg_stepb.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_stepb.py
bourbaki/cardinaux/ensembles_hessenberg_stepb2.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_stepb2.py
bourbaki/cardinaux/ensembles_hessenberg_step_b_classify.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_step_b_classify.py
bourbaki/cardinaux/ensembles_hessenberg_p5.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_p5.py
bourbaki/cardinaux/ensembles_hessenberg_p5c.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_p5c.py
bourbaki/cardinaux/ensembles_hessenberg_vrai.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_vrai.py
bourbaki/cardinaux/ensembles_hessenberg_vrai_final.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_vrai_final.py
bourbaki/cardinaux/ensembles_hessenberg_vrai_haut.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_vrai_haut.py
bourbaki/cardinaux/ensembles_hessenberg_recollement_final.py
   -> bourbaki/cardinaux/iii_6_infinis/hessenberg/assemblage_vrai/ensembles_hessenberg_recollement_final.py
bourbaki/cardinaux/ensembles_frame_a_maximal.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_a_maximal.py
bourbaki/cardinaux/ensembles_frame_extension_finale.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_extension_finale.py
bourbaki/cardinaux/ensembles_frame_inductif_assemblage.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_inductif_assemblage.py
bourbaki/cardinaux/ensembles_frame_maximal_clos.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_maximal_clos.py
bourbaki/cardinaux/ensembles_frame_ordre_axiome.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_ordre_axiome.py
bourbaki/cardinaux/ensembles_frame_ordre_est_ordre.py
   -> bourbaki/cardinaux/iii_6_infinis/frame_zorn/ensembles_frame_ordre_est_ordre.py
bourbaki/cardinaux/ensembles_chaine_frame_membership.py
   -> bourbaki/cardinaux/iii_6_infinis/chaine_recollement/ensembles_chaine_frame_membership.py
bourbaki/cardinaux/ensembles_chaine_surjective_frame.py
   -> bourbaki/cardinaux/iii_6_infinis/chaine_recollement/ensembles_chaine_surjective_frame.py
bourbaki/cardinaux/ensembles_chaine_temoin_abstrait.py
   -> bourbaki/cardinaux/iii_6_infinis/chaine_recollement/ensembles_chaine_temoin_abstrait.py
bourbaki/cardinaux/ensembles_union_chaine_bijection.py
   -> bourbaki/cardinaux/iii_6_infinis/chaine_recollement/ensembles_union_chaine_bijection.py
bourbaki/cardinaux/ensembles_ponts_couple_valeur_surj.py
   -> bourbaki/cardinaux/iii_6_infinis/chaine_recollement/ensembles_ponts_couple_valeur_surj.py
bourbaki/cardinaux/ensembles_denombrable_carre_iii6.py
   -> bourbaki/cardinaux/iii_6_infinis/denombrable/ensembles_denombrable_carre_iii6.py
bourbaki/cardinaux/ensembles_denombrable_injection_iii6.py
   -> bourbaki/cardinaux/iii_6_infinis/denombrable/ensembles_denombrable_injection_iii6.py
bourbaki/cardinaux/ensembles_fini_inf_egal_infini.py
   -> bourbaki/cardinaux/iii_6_infinis/infinis_descentes/ensembles_fini_inf_egal_infini.py
```

### bourbaki/cardinaux/arithmetique
```
ensembles_graphe_de.py
   -> fondations/ensembles_graphe_de.py
ensembles_somme_monotone.py
   -> iii_3_2_monotonie/ensembles_somme_monotone.py
ensembles_arith_cardinale_props_produit_monotone.py
   -> iii_3_2_monotonie/ensembles_arith_cardinale_props_produit_monotone.py
ensembles_arith_cardinale_props_exposant_monotone.py
   -> iii_3_2_monotonie/ensembles_arith_cardinale_props_exposant_monotone.py
ensembles_exposant_monotone_exp_incond.py
   -> iii_3_2_monotonie/ensembles_exposant_monotone_exp_incond.py
ensembles_exposant_monotone_incond.py
   -> iii_3_2_monotonie/ensembles_exposant_monotone_incond.py
ensembles_arith_somme.py
   -> iii_3_3_somme/ensembles_arith_somme.py
ensembles_somme_equipotence.py
   -> iii_3_3_somme/ensembles_somme_equipotence.py
ensembles_somme_commute.py
   -> iii_3_3_somme/ensembles_somme_commute.py
ensembles_somme_associe.py
   -> iii_3_3_somme/ensembles_somme_associe.py
ensembles_somme_zero.py
   -> iii_3_3_somme/ensembles_somme_zero.py
ensembles_arith_cardinale.py
   -> iii_3_3_produit/ensembles_arith_cardinale.py
ensembles_produit_equipotence.py
   -> iii_3_3_produit/ensembles_produit_equipotence.py
ensembles_produit_commute.py
   -> iii_3_3_produit/ensembles_produit_commute.py
ensembles_produit_petits.py
   -> iii_3_3_produit/ensembles_produit_petits.py
ensembles_distributivite_cardinale.py
   -> iii_3_3_produit/ensembles_distributivite_cardinale.py
ensembles_prop8_successeur.py
   -> iii_3_4_prop8_successeur/ensembles_prop8_successeur.py
ensembles_prop8_plus_point.py
   -> iii_3_4_prop8_successeur/ensembles_prop8_plus_point.py
ensembles_prop8_assemblage.py
   -> iii_3_4_prop8_successeur/ensembles_prop8_assemblage.py
ensembles_prop8_transposition.py
   -> iii_3_4_prop8_successeur/ensembles_prop8_transposition.py
ensembles_prop8_fini2.py
   -> iii_3_4_prop8_successeur/ensembles_prop8_fini2.py
ensembles_copie_marquee.py
   -> iii_3_4_prop8_successeur/ensembles_copie_marquee.py
ensembles_prop8_coeur/
   -> iii_3_4_prop8_successeur/prop8_coeur/
ensembles_transposition/
   -> iii_3_4_prop8_successeur/transposition/
ensembles_exposant_cardinal.py
   -> iii_3_5_exposant/definition/ensembles_exposant_cardinal.py
ensembles_exposant_un_base.py
   -> iii_3_5_exposant/definition/ensembles_exposant_un_base.py
ensembles_exposant_zero.py
   -> iii_3_5_exposant/definition/ensembles_exposant_zero.py
ensembles_exposant_un/
   -> iii_3_5_exposant/definition/exposant_un/
ensembles_exposant_somme.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_exposant_somme.py
ensembles_prop9_exp_somme.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_prop9_exp_somme.py
ensembles_prop9_final.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_prop9_final.py
ensembles_prop9_final_close.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_prop9_final_close.py
ensembles_prop9_close.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_prop9_close.py
ensembles_prop9_cloture.py
   -> iii_3_5_exposant/prop9_exp_somme/ensembles_prop9_cloture.py
ensembles_exposant_produit.py
   -> iii_3_5_exposant/prop10_currying/ensembles_exposant_produit.py
ensembles_prop10_currying.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10_currying.py
ensembles_prop10_inj_curry.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10_inj_curry.py
ensembles_prop10_inj_uncurry.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10_inj_uncurry.py
ensembles_prop10_close.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10_close.py
ensembles_prop10_final_close.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10_final_close.py
ensembles_prop10cor2_iii3.py
   -> iii_3_5_exposant/prop10_currying/ensembles_prop10cor2_iii3.py
ensembles_powerset_exp.py
   -> iii_3_5_exposant/prop12_powerset/ensembles_powerset_exp.py
ensembles_powerset_deux.py
   -> iii_3_5_exposant/prop12_powerset/ensembles_powerset_deux.py
ensembles_prop12_powerset.py
   -> iii_3_5_exposant/prop12_powerset/ensembles_prop12_powerset.py
ensembles_prop12_fin.py
   -> iii_3_5_exposant/prop12_powerset/ensembles_prop12_fin.py
ensembles_prop12_card/
   -> iii_3_5_exposant/prop12_powerset/prop12_card/
```

### bourbaki/entiers
```
bourbaki/entiers/ensembles_entiers.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_entiers.py
bourbaki/entiers/ensembles_zero_plus_un.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_zero_plus_un.py
bourbaki/entiers/ensembles_fini_successeur.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_fini_successeur.py
bourbaki/entiers/ensembles_fini_zero.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_fini_zero.py
bourbaki/entiers/ensembles_fini_un.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_fini_un.py
bourbaki/entiers/ensembles_fini_deux.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_fini_deux.py
bourbaki/entiers/ensembles_fini_trois_quatre.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_fini_trois_quatre.py
bourbaki/entiers/ensembles_entiers_theoremes.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_entiers_theoremes.py
bourbaki/entiers/ensembles_recurrence_C61.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_recurrence_c61_existence_n/ensembles_recurrence_C61.py
bourbaki/entiers/ensembles_principe_recurrence_preuve.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_recurrence_c61_existence_n/ensembles_principe_recurrence_preuve.py
bourbaki/entiers/ensembles_recurrence_vraie.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_recurrence_c61_existence_n/ensembles_recurrence_vraie.py
bourbaki/entiers/ensembles_predecesseur_prop2.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_recurrence_c61_existence_n/ensembles_predecesseur_prop2.py
bourbaki/entiers/ensembles_cardinal_pas_entre.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_recurrence_c61_existence_n/ensembles_cardinal_pas_entre.py
bourbaki/entiers/ensembles_pigeonhole_sous_lemme.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_pigeonhole_surgery/ensembles_pigeonhole_sous_lemme.py
bourbaki/entiers/ensembles_partie_equipotente_finie.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_pigeonhole_surgery/ensembles_partie_equipotente_finie.py
bourbaki/entiers/ensembles_retrait_point.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_pigeonhole_surgery/ensembles_retrait_point.py
bourbaki/entiers/ensembles_retrait_surgery.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_pigeonhole_surgery/ensembles_retrait_surgery.py
bourbaki/entiers/ensembles_cor4_inj_surj_iii4.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_cor4_inj_surj_bij/ensembles_cor4_inj_surj_iii4.py
bourbaki/entiers/ensembles_cor4_surj_inj_iii4.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_cor4_inj_surj_bij/ensembles_cor4_surj_inj_iii4.py
bourbaki/entiers/ensembles_cor4_surj_inj_fin.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_cor4_inj_surj_bij/ensembles_cor4_surj_inj_fin.py
bourbaki/entiers/ensembles_finis_props.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_finis_props/ensembles_finis_props.py
bourbaki/entiers/ensembles_finis_props2.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_finis_props/ensembles_finis_props2.py
bourbaki/entiers/ensembles_chap3_props_restantes.py
   -> bourbaki/entiers/iii_4_entiers_finis/iii_4_2_finis_props/ensembles_chap3_props_restantes.py
bourbaki/entiers/ensembles_combinatoire_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_1_somme_produit_entiers/ensembles_combinatoire_iii5.py
bourbaki/entiers/ensembles_prop3_produit_entier_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_1_somme_produit_entiers/ensembles_prop3_produit_entier_iii5.py
bourbaki/entiers/ensembles_calcul_entiers_props.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_1_somme_produit_entiers/ensembles_calcul_entiers_props.py
bourbaki/entiers/ensembles_simplification_additive.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_1_somme_produit_entiers/ensembles_simplification_additive.py
bourbaki/entiers/ensembles_recurrence_finie.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_1_somme_produit_entiers/ensembles_recurrence_finie.py
bourbaki/entiers/ensembles_prop2_strict_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_prop2_strict_iii5.py
bourbaki/entiers/ensembles_prop3_strict_mono_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_prop3_strict_mono_iii5.py
bourbaki/entiers/ensembles_successeur_ordre.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_successeur_ordre.py
bourbaki/entiers/ensembles_prop4_strict_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_prop4_strict_iii5.py
bourbaki/entiers/ensembles_prop4_surj_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_prop4_surj_iii5.py
bourbaki/entiers/ensembles_soustraction_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_2_inegalites_ordre_soustraction/ensembles_soustraction_iii5.py
bourbaki/entiers/ensembles_prop5_intervalle.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop5_intervalle.py
bourbaki/entiers/ensembles_prop5_prop4_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop5_prop4_iii5.py
bourbaki/entiers/ensembles_prop5_general_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop5_general_iii5.py
bourbaki/entiers/ensembles_prop6_bien_ordonne_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop6_bien_ordonne_iii5.py
bourbaki/entiers/ensembles_prop6_fini_interval_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop6_fini_interval_iii5.py
bourbaki/entiers/ensembles_prop6_iso_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_intervalles_comptage/ensembles_prop6_iso_iii5.py
bourbaki/entiers/ensembles_prop7_caracteristique_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_5_caracteristique_combinatoire/ensembles_prop7_caracteristique_iii5.py
bourbaki/entiers/ensembles_prop9_bergers_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_5_caracteristique_combinatoire/ensembles_prop9_bergers_iii5.py
bourbaki/entiers/ensembles_factorielle_iii5.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_8_factorielle/ensembles_factorielle_iii5.py
bourbaki/entiers/ensembles_factorielle_existence.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_8_factorielle/ensembles_factorielle_existence.py
bourbaki/entiers/ensembles_factorielle_existence_vrai.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_8_factorielle/ensembles_factorielle_existence_vrai.py
bourbaki/entiers/ensembles_factorielle_gluing_diag.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_8_factorielle/ensembles_factorielle_gluing_diag.py
bourbaki/entiers/ensembles_entiers_notions_arith.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_notions_complementaires/ensembles_entiers_notions_arith.py
bourbaki/entiers/ensembles_entiers_notions_suites.py
   -> bourbaki/entiers/iii_5_calcul_entiers/iii_5_notions_complementaires/ensembles_entiers_notions_suites.py
bourbaki/entiers/ensembles_N_collectivise.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_1_n_objet_existence/ensembles_N_collectivise.py
bourbaki/entiers/ensembles_ensemble_NN.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_1_n_objet_existence/ensembles_ensemble_NN.py
bourbaki/entiers/ensembles_n_bien_ordonne.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_1_n_objet_existence/ensembles_n_bien_ordonne.py
bourbaki/entiers/ensembles_aleph0.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_1_n_objet_existence/ensembles_aleph0.py
bourbaki/entiers/ensembles_c62_recursion.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_2_recursion_c62/ensembles_c62_recursion.py
bourbaki/entiers/ensembles_recursion_hygienic.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_2_recursion_c62/ensembles_recursion_hygienic.py
bourbaki/entiers/ensembles_infinis.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_3_infinis_denombrables/ensembles_infinis.py
bourbaki/entiers/ensembles_infinis_iii6.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_3_infinis_denombrables/ensembles_infinis_iii6.py
bourbaki/entiers/ensembles_infinis_props.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_3_infinis_denombrables/ensembles_infinis_props.py
bourbaki/entiers/ensembles_infinis_theoremes.py
   -> bourbaki/entiers/iii_6_infinis/iii_6_3_infinis_denombrables/ensembles_infinis_theoremes.py
```

### bourbaki/structures
```
bourbaki/structures/ensembles_especes_echelon.py
   -> bourbaki/structures/iv_1_structures_isomorphismes/ensembles_especes_echelon.py
bourbaki/structures/ensembles_especes_typification.py
   -> bourbaki/structures/iv_1_structures_isomorphismes/ensembles_especes_typification.py
bourbaki/structures/ensembles_especes.py
   -> bourbaki/structures/iv_1_structures_isomorphismes/ensembles_especes.py
bourbaki/structures/ensembles_especes_deduction.py
   -> bourbaki/structures/iv_1_structures_isomorphismes/ensembles_especes_deduction.py
bourbaki/structures/ensembles_transport_iso_props.py
   -> bourbaki/structures/iv_1_structures_isomorphismes/ensembles_transport_iso_props.py
bourbaki/structures/ensembles_universel_morphismes.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_universel_morphismes.py
bourbaki/structures/ensembles_universel_finale.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_universel_finale.py
bourbaki/structures/ensembles_structures_props.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_structures_props.py
bourbaki/structures/ensembles_structures_derivees_props.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_structures_derivees_props.py
bourbaki/structures/ensembles_structures_residus.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_structures_residus.py
bourbaki/structures/ensembles_CST_criteres.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/cst_criteres/ensembles_CST_criteres.py
bourbaki/structures/ensembles_chap4_props_restantes.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/cst_criteres/ensembles_chap4_props_restantes.py
bourbaki/structures/ensembles_cst_criteres_suite.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/cst_criteres/ensembles_cst_criteres_suite.py
bourbaki/structures/ensembles_cst_produit_quotient.py
   -> bourbaki/structures/iv_2_morphismes_structures_derivees/cst_criteres/ensembles_cst_produit_quotient.py
bourbaki/structures/__init__.py
   -> bourbaki/structures/__init__.py
```
