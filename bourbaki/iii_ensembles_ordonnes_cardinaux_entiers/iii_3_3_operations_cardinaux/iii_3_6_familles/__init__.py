"""III.3.6 — Somme/produit d'une FAMILLE de cardinaux (∑_ι a_ι, ∏_ι a_ι).

Contenu :
  ensembles_famille_successeurs.py     : la famille (i+1)_{i<n} + terme n! (Déf. 2 §III.5.8)
  ensembles_seg_successeur.py          : seg(n+1) = seg(n) ∪ {n} (support)
  ensembles_prop4_famille_cardinaux.py : Prop. 4 (familles de cardinaux)
  ensembles_produit_adjonction.py      : T1b-(2) — le graphe d'ADJONCTION Φ : F↦(F|I,F(j)),
      hypothèses honnêtes, membership I∪{j}, paliers P1-P3 (§II.5.5 Rem.1)
  ensembles_produit_adjonction_briques.py : restriction/réunion/prolongement-singleton
  ensembles_produit_adjonction_bij.py     : P4-P7 — bijection, Eq(∏_{I∪{j}}, ∏_I×u_j),
      Card(∏_{I∪{j}}) = produit_cardinal_binaire(∏_I, u_j)

Reste (ÉTAPE B) : la récursion du produit fini indexé (T1b-(3)) qui chaîne
l'adjonction sur seg(n+1)=seg(n)∪{n} — puis la convergence n! C62 / Déf. 2.
"""
