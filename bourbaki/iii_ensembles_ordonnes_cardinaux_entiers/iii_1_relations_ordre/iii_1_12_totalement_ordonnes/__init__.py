"""§III.1 n°12 — Ensembles TOTALEMENT ORDONNÉS (E.III.1.14, Proposition 12).

Sous-section dédiée au n°12 « Ensembles totalement ordonnés » du §III.1.  Le
prédicat `totalement_ordonne` (graphe G, x≤y := (x,y)∈G) est défini dans
`ensembles_ordre_relation.py` ; on en tire ici le critère de borne supérieure
spécifique aux ordres TOTAUX.

Résultats formalisés (certifiés noyau LCF, CLOS sous hypothèses honnêtes) :

  • `ensembles_prop12_sup_total.borne_sup_critere_total`
      PROPOSITION 12 (E.III.1.14) : dans un ensemble TOTALEMENT ordonné, un élément
      b est borne supérieure de X ssi (1°) b majore X et (2°) tout c < b est
      dépassé dans X (∃x∈X, c < x ≤ b).
"""
