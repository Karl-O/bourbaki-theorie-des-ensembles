"""§II.4.2 — Propriétés de monotonie EN L'ENSEMBLE D'INDICES.

Sous-section dédiée aux variations de ⋃_{ι∈J} X_ι et ⋂_{ι∈J} X_ι quand on fait
varier l'ensemble d'indices J (à famille f FIXÉE), conformément à E.II.4.2.

  • DÉCROISSANCE de l'intersection (`inter_incluse_sous_indices`) :
        ⊢ (J ⊂ I) ⇒ ( (∃i)(i∈J) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι )
    L'intersection sur le PLUS GROS ensemble d'indices est la PLUS PETITE — DUAL
    universel (∀) de la croissance de la réunion `reunion_incluse_sous_indices`
    (déjà certifiée dans `ii_4_1_definitions_algebre/ensembles_familles_algebre`).
    L'hypothèse « J ≠ ∅ » est celle que Bourbaki écrit noir sur blanc (E II.24 :
    « Si J ⊂ I, on a ⋃_{ι∈J} X_ι ⊂ ⋃_{ι∈I} X_ι, et (si J ≠ ∅) ⋂_{ι∈J} X_ι ⊃
    ⋂_{ι∈I} X_ι ») ; elle est INDISPENSABLE depuis la réparation de la Déf. 2 par
    SÉLECTION (⋂_{ι∈∅} X_ι = ∅ ⇒ énoncé faux pour J = ∅).  La forme SANS cette
    hypothèse, affichée ici jusqu'au 2026-07-26, n'était démontrable que par
    l'ancien AXIOME_INTER_FAM contradictoire.  Voir l'en-tête du module.

Aucun axiome neuf : on n'utilise que les primitives N.* et l'axiome caractérisant
⋂ (AXIOME_INTER_FAM) ; theorie_ensembles() reste à 22 axiomes.
"""
