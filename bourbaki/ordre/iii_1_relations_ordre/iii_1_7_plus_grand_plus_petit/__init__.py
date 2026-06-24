"""§III.1.7 — PLUS GRAND / PLUS PETIT élément (E.III.1.7, Définition 4 ; Remarque).

Sous-section dédiée aux résultats du §III.1.7 portant sur le plus grand et le
plus petit élément d'un ensemble ordonné (convention « graphe G » : x≤y signifie
(x,y)∈G).  Les prédicats `plus_grand_element`, `plus_petit_element`,
`element_maximal`, `element_minimal` sont définis dans
`ordre_treillis/ensembles_ordre_relation.py`.

Résultats formalisés (certifiés noyau LCF, CLOS) :

  • `ensembles_plus_petit_unique_minimal.plus_petit_est_unique_minimal`
      REMARQUE (E.III.1.7) : si E admet un plus petit élément a, alors tout
      élément minimal m de E coïncide avec a (le plus petit élément est l'unique
      élément minimal).  Preuve order-théorique pure : l'antisymétrie n'est PAS
      requise (énoncé minimal honnête).
"""
