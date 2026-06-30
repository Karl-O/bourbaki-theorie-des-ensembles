# Stats du corpus — calibration du générateur (pas 4)

Mesures via `stats_corpus.py` sur `corpus_sample.jsonl` (22 théorèmes tracés, Ch II) +
export large `logique`+`ensembles` (282 théorèmes, 97 modules). Régénérable.

## Chiffres clés

**[1] Trajectoires (pas primitifs N.*).** min **48** | médiane **5 402** | max **30 207** |
total **205 861** sur 22 théorèmes. → Les preuves, au niveau primitif, sont **très
longues** (jusqu'à 30k pas). Le budget T d'une diffusion sur le DAG primitif serait énorme.

**[2] Espace d'actions PRIMITIF = petit et très déséquilibré (14 règles).**
`modus_ponens` 41 % · `assume` 18 % · `loi_deduction` 18 % · `s3` 15 % → **92 % à 4 règles**.
Le reste (s4, s2, s5, s6, reflexivite, axiome, s1, existe_temoin, generalisation, s7) < 8 %.
→ Au niveau primitif, le choix d'action est trivial ; la difficulté est **combinatoire**
(QUELS théorèmes combiner), pas le choix de règle.

**[3] Bibliothèque de fait (briques tactiques réutilisées).** `conjonction_intro` (20/22),
`equivalence_avant` (13), `conjonction_elim_gauche` (10), `existe_elimination`, `symetrie`,
`extensionnalite_appliquee`, `equivalence_transitivite`, `congruence_existe`, … → vocabulaire
**riche et signifiant** (des dizaines de tactiques), bien plus informatif que les 14 primitives.

## Implication de design (importante)

**Le générateur doit opérer au niveau TACTIQUE, pas au niveau primitif brut.**
- niveau primitif : 30k pas, 14 actions ultra-déséquilibrées → mauvais espace pour diffusion/GFlowNet ;
- niveau tactique (la bibliothèque [3]) : trajectoires courtes (l'ordre des `proof_src` :
  dizaines de pas), espace d'actions riche = les tactiques/lemmes réutilisés.
→ La paire **(but → programme-preuve)** de `proof_src` est la BONNE granularité (confirmé
par les données). La trace primitive sert de **vérification dense** (chaque tactique se
déplie en primitives kernel-vérifiées) et d'oracle, pas d'espace de génération.
→ Piste : GFlowNet/diffusion sur le DAG de **tactiques**, action = appliquer une brique de
la bibliothèque, récompense = but fermé (kernel), library-learning pour étendre la bibliothèque.

## Prochaines passes
- export large AVEC trace (échantillonné) pour distribution `trace_len` toutes-sections ;
- graphe de dépendance lemmes (qui-appelle-qui) complet = la vraie « bibliothèque » à apprendre ;
- premier proto generate-and-verify : muter un `proof_src` (échanger/insérer une tactique),
  ré-exécuter, vérifier au kernel — le plus petit « pas de marche + filtre ».
