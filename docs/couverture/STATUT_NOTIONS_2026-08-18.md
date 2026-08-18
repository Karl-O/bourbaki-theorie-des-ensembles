```
==============================================================================
 STATUT DES NOTIONS — ce que le dépôt DÉCLARE, ce que le NOYAU dit
==============================================================================
 notions marquées @livre et rattachées à une def : 1811
------------------------------------------------------------------------------
 (1) DÉCLARÉ — lu dans les docstrings, par chapitre

  chap |          CLOS   CLOS_MODULO       REPORTE          MUET     total
  I    |             8             0             0           234       242
  II   |            59            46            17           341       463
  III  |           111            91            59           620       881
  IV   |             6             4            31           134       175
  R    |             0            10             0            40        50
  TOUS |           184           151           107          1369      1811
------------------------------------------------------------------------------
 (2) NOYAU — 1811 notions évaluées

   FAIT                 591
   PARTIEL              504
   CONSTRUIT            275
   NON_EVALUABLE        441

   TYPES DÉMONTRABLES (Prop/Th/Cor/Crit/Lem/Demo/Sch/Ax) : 1142
     FAIT                 413
     PARTIEL              402
     CONSTRUIT             72
     NON_EVALUABLE        255
   → taux FAIT sur les DÉMONTRABLES tranchées : 50.7 % (413/815)
------------------------------------------------------------------------------
 (3) CROISEMENT — ce qu'aucun autre outil ne voit

   ACCORD                     588
   REPORT_PERIME               23
   DECLARATION_TROP_FORTE      92
   ACQUIS_NON_DECLARE         392
   NON_TRANCHE                716

   ── REPORT_PERIME ──
     application_identique_est_application  FAIT (0 hyp) ensembles_fondations_notions.py
     theoreme1_d_surjective_valeur          FAIT (0 hyp) ensembles_retractions_props.py
     surjective_image_donne_valeur          FAIT (0 hyp) ensembles_surjectivite_image_valeur.py
     ext_canonique_valeur                   FAIT (0 hyp) ensembles_extension_canonique.py
     facteur_inclus_si_produit_inclus       FAIT (0 hyp) ensembles_produit_inclus_reciproque.py
     pr_J_surjective_via_prolongement       FAIT (0 hyp) ensembles_produit_props_projection.py
     reparametrage_injectif                 FAIT (0 hyp) ensembles_produit_props2.py
     associativite_via_inverse              FAIT (0 hyp) ensembles_produit_props2.py
     h_maximal_preuve                       FAIT (0 hyp) ensembles_trichotomie_maximalite_preuve.py
     h_maximal_preuve                       FAIT (0 hyp) ensembles_trichotomie_maximalite_preuve.py
     reduction_back_and_forth               FAIT (0 hyp) ensembles_prop8_successeur.py
     curry_but_egale_via_eq                 FAIT (0 hyp) ensembles_exposant_produit.py
     cor2_via_eq                            FAIT (0 hyp) ensembles_prop10cor2_iii3.py
     prop13_forward_conditionnel            FAIT (0 hyp) ensembles_cardinaux_props_restantes.py
     cantor_strict_cardinal                 FAIT (0 hyp) ensembles_chap3_props_restantes.py
     cantor_strict_cardinal                 FAIT (0 hyp) ensembles_chap3_props_restantes.py
     cor1_partie_finie_est_finie_conditionn FAIT (0 hyp) ensembles_finis_props.py
     cor2_partie_stricte_card_strict_cond   FAIT (0 hyp) ensembles_finis_props2.py
     cor3_image_finie_cond                  FAIT (0 hyp) ensembles_finis_props2.py
     puissance_entiers_ferme                FAIT (0 hyp) ensembles_n_arith_iii5.py

   ── DECLARATION_TROP_FORTE ──
     projection_vide_implique_graphe_vide   PARTIEL (2 hyp) ensembles_graphe_inclus_produit.py
     fonctorialite_parties_termes           PARTIEL (1 hyp) ensembles_graphe_terme_egalite.py
     projection_c55                         PARTIEL (6 hyp) ensembles_projection_c55.py
     relation_induite_symetrique            PARTIEL (1 hyp) ensembles_quotient_complements.py
     image_reciproque_symetrique            PARTIEL (1 hyp) ensembles_quotient_complements.py
     image_reciproque_transitive            PARTIEL (1 hyp) ensembles_quotient_complements.py
     classe_objets_unicite                  PARTIEL (2 hyp) ensembles_quotient_complements.py
     appartient_classe                      PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     relation_implique_classe_egale         PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     classe_egale_implique_relation         PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     relation_ssi_classe_egale              PARTIEL (4 hyp) ensembles_quotient_props_graphe.py
     classes_se_rencontrent_egales          PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     projection_valeur_classe               PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     intersection_symetrique                PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     intersection_transitive                PARTIEL (2 hyp) ensembles_quotient_props_graphe.py
     intersection_relation_equivalence      PARTIEL (4 hyp) ensembles_quotient_props_graphe.py
     produit_symetrique                     PARTIEL (2 hyp) ensembles_quotient_produit_restant.py
     produit_transitive                     PARTIEL (2 hyp) ensembles_quotient_produit_restant.py
     produit_relation_equivalence           PARTIEL (4 hyp) ensembles_quotient_produit_restant.py
     induite_transitive                     PARTIEL (1 hyp) ensembles_quotient_produit_restant.py
==============================================================================
```

## Lecture (ajoutée à la main, 18 août)

**C'est la première réponse chiffrée à la question du projet** : « démontré
dans le livre » coïncide-t-il avec « vérifié par la machine » ? Sur les 1142
notions de type démontrable, 815 sont tranchées par le noyau : **50,7 % FAIT**
(0 hypothèse), 49,3 % PARTIEL. Les 255 NON_EVALUABLE restantes sont des
fonctions à paramètres non génériques (couche assemblage, prédicats) — le
repli ne les atteint pas, et il ne doit PAS deviner.

**Les 23 REPORT_PERIME sont la trouvaille actionnable** : des théorèmes que
le noyau rend CLOS et dont la docstring dit encore REPORTÉ. Chacun est un
acquis qu'une session future risquait de REFAIRE. ⚠️ À vérifier un par un
avant de nettoyer : une docstring peut dire « REPORTÉ » d'un ASPECT (la
généralisation, l'assemblage) tout en livrant un théorème clos d'un autre —
le croisement signale, il ne juge pas la nuance.

Les 92 DECLARATION_TROP_FORTE sont l'inverse : un « CLOS » que le noyau
contredit. Même consigne : vérifier la nuance avant de corriger la docstring.
