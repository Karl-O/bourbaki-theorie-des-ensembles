"""§II.4.1 Déf. 2 — FONDATION de l'intersection d'une famille : ⋂ = sélection dans ⋃.

RAISON D'ÊTRE.  `AXIOME_INTER_FAM` (ensembles_abrege.py) pose l'intersection SANS
la restriction « I ≠ ∅ » que la Déf. 2 EXIGE (E II.22, PDF p.73 : « Soit (X_ι)_{ι∈I}
une famille d'ensembles dont l'ensemble d'indices I n'est pas vide »).  Pour I = ∅ le
membre droit (∀ι)((ι∈I) ⇒ (x∈X_ι)) est vide-vrai pour TOUT x, donc ⋂_{ι∈∅} X_ι
contient tout objet — un ensemble universel.  Bourbaki annonce lui-même la panne dans
la note en petits caractères de la Déf. 2 (« … car ce serait l'ensemble de tous les
objets »), et le corpus prouve le contraire, CLOS (`ensembles_pas_ensemble_universel`).
`outils_ia/audit/preuve_incoherence_inter_vide.py` en dérive A et non-A.

LA RÉPARATION (route Grimm B5, `@source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7` :
« Taking for E the union of the family solves the problem »).  L'intersection cesse
d'être un postulat inconditionnel : elle devient une SÉLECTION dans la réunion,

    (∀f)(∀I)(∀z)( z ∈ ⋂_{ι∈I} X_ι  ⇔  ( z ∈ ⋃_{ι∈I} X_ι
                                          ∧ (∀i)((i∈I) ⇒ (z ∈ X_i)) ) )

légitimée par S8 (sélection dans l'ensemble EXISTANT ⋃_{ι∈I} X_ι) + A1 (unicité) —
exactement comme AXIOME_QUOTIENT (sélection dans P(E)) ou AXIOME_PRODUIT_FAM
(sélection dans P(I×A)).  Pour I = ∅ la réunion est vide, donc l'intersection est
vide : la pathologie MEURT sans qu'on ait à porter « I ≠ ∅ » dans la formule.

CONTENU
  • `ensembles_inter_selection_ii4` — l'axiome, sa théorie dédiée, et les trois
    résultats de base : élimination (⋂ ⊂ chaque X_ι), ⋂ ⊂ ⋃, introduction sous
    témoin d'indice.
  • `ensembles_inter_migration_ii4` — le pont de migration : l'ANCIEN énoncé
    récupéré sous « (∃i)(i∈I) » (resp. « I ≠ ∅ »), et la mort de la pathologie
    (⋂_{ι∈∅} X_ι = ∅).

INVARIANTS.  Rien n'est postulé au-delà de l'axiome ci-dessus, porté par une THÉORIE
DÉDIÉE `theorie_inter_selection()` (motif `theorie_russell_dans` /
`theorie_diagonale_cantor`) : `theorie_ensembles()` reste EXACTEMENT à 22 axiomes et
AUCUN fichier existant n'est modifié.  Les preuves combinent librement des théorèmes
de `theorie_ensembles()` (AXIOME_REUNION_FAM, AXIOME_VIDE) et de
`theorie_inter_selection()` — motif standard du projet.
"""
