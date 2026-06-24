"""§II.6.6 — Relation d'équivalence induite R_A sur une partie A de E.

Sous-paquet dédié à la relation induite R_A{x,y} := (x∈A et y∈A et R{x,y})
(E.II.6.6, Déf.), introduite dans `..ensembles_quotient_complements`
(`relation_induite`, `relation_induite_implique`, `relation_induite_symetrique`).

Ce paquet COMPLÈTE la chaîne de propriétés héritées de R par R_A en démontrant,
dans le noyau LCF (primitives N.* seules ; theorie_ensembles INCHANGÉE = 22) :

  • `relation_induite_transitive`           {R transitive} ⊢ R_A transitive ;
  • `relation_induite_relation_equivalence` {R sym., R trans.} ⊢ R_A relation
        d'équivalence  (= R_A symétrique ET transitive ; assemble la symétrie
        EXISTANTE `relation_induite_symetrique` et la transitivité ci-dessus).

Conclusion VERBATIM : `est_transitive(R_A)` resp. `est_relation_equivalence(R_A)`
au sens d'`ensembles_abrege` (liants x, y, z par défaut).  Aucune réflexivité
n'est requise (R_A est une relation d'équivalence au sens symétrie+transitivité,
E.II.6.1).
"""
