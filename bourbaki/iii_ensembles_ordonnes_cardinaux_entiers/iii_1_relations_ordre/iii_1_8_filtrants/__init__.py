"""§III.1.10 — Ensembles ORDONNÉS FILTRANTS (E.III.1.10, Déf. 7 ; Proposition 10).

Sous-section dédiée aux ensembles ordonnés filtrants à droite/gauche du périmètre
III.1.  Le prédicat `est_filtrant_droite` est défini dans
`ensembles/ii_1_relations_collectivisantes/ensembles_abrege.py` ; on le réexpose ici en
convention « graphe G » (x≤y := (x,y)∈G) via `_filtrant_droite_G`.

Résultats formalisés (certifiés noyau LCF, CLOS) :

  • `ensembles_prop10_maximal_filtrant.maximal_filtrant_est_plus_grand`
      PROPOSITION 10 (E.III.1.10) : dans un ensemble ordonné filtrant à droite,
      tout élément maximal est le plus grand élément.

  • `ensembles_cofinale_plus_grand` — REMARQUE (E.III.1.8) « plus grand élément
      ⟺ partie cofinale réduite à un seul élément » : sens direct
      (`plus_grand_implique_cofinale_singleton`), réciproque
      (`cofinale_singleton_implique_plus_grand`) et ÉQUIVALENCE sous a∈E
      (`plus_grand_equivaut_cofinale_singleton`).
"""
