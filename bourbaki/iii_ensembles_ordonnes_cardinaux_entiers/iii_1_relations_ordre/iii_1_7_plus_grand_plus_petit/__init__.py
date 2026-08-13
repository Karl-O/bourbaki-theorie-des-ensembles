"""§III.1.7 — PLUS GRAND / PLUS PETIT élément (E.III.1.7, Définition 4 ; Remarque).

Sous-section dédiée aux résultats du §III.1.7 portant sur le plus grand et le
plus petit élément d'un ensemble ordonné (convention « graphe G » : x≤y signifie
(x,y)∈G).  Les prédicats `plus_grand_element`, `plus_petit_element`,
`element_maximal`, `element_minimal` sont définis dans
`ordre_treillis/ensembles_ordre_relation.py`.

Résultats formalisés (certifiés noyau LCF).  ⚠️ **Le statut est indiqué RÉSULTAT PAR
RÉSULTAT** : ce titre a dit « CLOS » pour tout le dossier, ce qui est devenu FAUX dès
l'ajout de `terme_plus_grand_vaut` (2 hypothèses résiduelles, `est_clos=False` — mesuré
le 27 juil. 2026).  Un en-tête de dossier qui promet un statut collectif se périme au
premier ajout : ne jamais en écrire, indiquer le statut sur chaque entrée.

  • `ensembles_plus_petit_unique_minimal.plus_petit_est_unique_minimal`
      REMARQUE (E.III.1.7) : si E admet un plus petit élément a, alors tout
      élément minimal m de E coïncide avec a (le plus petit élément est l'unique
      élément minimal).  Preuve order-théorique pure : l'antisymétrie n'est PAS
      requise (énoncé minimal honnête).

  • `ensembles_terme_plus_grand.terme_plus_grand` / `.terme_plus_grand_vaut`
      LE TERME « plus grand élément » :  M_R(A) := τ_m( plus grand élt de A ),
      explicitation du τ dont E III.46 (note 2) dit qu'il code la borne
      supérieure « même pour un ensemble non majoré ».  Théorème :
      { est_plus_grand_element(R,A,a), antisymetrie_sur(R,A) } ⊢ M_R(A) = a —
      le terme DÉNOTE dès qu'un plus grand élément existe.  Le prédicat existait
      (`ensembles_abrege.est_plus_grand_element`) ; le TERME manquait.
      Instance arithmétique M([0,n]) = n : `iii_5_calcul_entiers/
      iii_5_intervalles_comptage/ensembles_max_intervalle_iii5.py`.
"""
