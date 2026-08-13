# Traces de recherche — schéma v1 (étage 2 de la théorie de la trace)

Fichier de données : `events.jsonl` (une ligne JSON par événement, append-only).
Design complet : `../ameliorations/THEORIE_TRACE.md`. Hiérarchie de confiance :
tout champ `loi`/`stat` est EMPIRIQUE (≠ prouvé) ; les théorèmes restent au noyau.

## Types d'événements (champ "type")

- **PERCEE**   {item, cible, nb_strategies, briques_construites[], hyps_residuelles[],
                fichier, date, session}
- **VERROU**   {classe, symptome, contexte, fichier, date}
- **REMEDE**   {motif, classe_verrou, succes: true|false, note, date,
                *(v2)* etat?: "but/contexte au moment du choix",
                tentative_annulee?: "ce qui a échoué À CE MÊME ÉTAT",
                tentative_finale?: "ce qui a marché"}
  ⚠️ **v2 (26 juil., justifié par REPLica)** : l'unité de donnée exploitable n'est pas
  le remède seul mais le **COUPLE (annulé → final) À ÉTAT CONSTANT** — c'est ainsi que
  Ringer et al. classent 96 réparations (`@source ../../sources/traces_et_erreurs/REPLica_Ringer_CPP2020.pdf`
  p.6 §4.3). Remplir `etat`/`tentative_annulee`/`tentative_finale` dès que possible ;
  les événements v1 (motif seul) restent valides mais moins exploitables.
- **MUR**      {item, brique_manquante, ou_elle_devrait_vivre, date}
- **BLOQUE_FAUX** {item, raison_documentee, preuve_du_deblocage, date}
- **TENTATIVE** {cible, strategie, resultat: "OK"|"ECHEC", symptome?, cout?, date}
- **INCOHERENCE** {axiome, theorie, hypothese_perdue, source_fautive, source_correcte,
                   preuve_machine, portee, correctif, date}
  ⚠️ **Nouveau le 26 juil., créé par le cas `AXIOME_INTER_FAM`.** `BLOQUE_FAUX` enregistre
  « déclaré bloqué alors que ça passait » ; il manquait le **symétrique et bien plus grave** :
  « déclaré prouvé alors que la théorie était contradictoire ». Le noyau garantit la *soundness*
  (aucun pas de déduction faux) mais **PAS la fidélité** : un axiome infidèle est accepté sans
  broncher et empoisonne tout ce qui en descend, en restant vert aux tests. C'est le seul mode
  de défaillance qui ne se voit ni au noyau ni à la suite de tests — d'où un type dédié.
  - `preuve_machine` = chemin d'un script qui DÉRIVE l'absurdité et tourne. Sans lui, ce n'est
    pas une incohérence, c'est une inquiétude : utiliser `TENTATIVE` à la place.
  - `source_fautive` / `source_correcte` = les deux marqueurs `@livre`. Le cas fondateur donne
    la loi empirique : **un `@livre Ch.R` (Résumé) sur un AXIOME est un défaut de fidélité par
    construction** — un résumé condense et suppose le contexte acquis. Sur une notation pure
    (couple, pr₁, produit) `Ch.R` reste légitime.
  - `portee` = nombre de fichiers descendants dont la certification est suspendue.

Classes de verrous connues (vocabulaire contrôlé, étendre si besoin) :
`collision-nom-argument` · `alpha-variant-formule` · `alpha-variant-terme-tau` ·
`liant-tau-lettre-simple` · `garde-trop-large` · `brique-manquante` ·
`renommage-gratuit-subst` (ÉTEINTE par le fix du 24 juil) · `capture-liant-epine`.

## Protocole (à partir du 25 juil. 2026 au soir)
1. Chaque agent build REND ses événements en fin de rapport (section EVENTS, JSON).
2. Le tick de clôture les appende à events.jsonl.
3. Rétro-remplissage des campagnes 24-25 juil : fait à la création (voir events.jsonl).
4. Étages 1 (DAG/M1) et 3 (stats) : sessions dédiées ultérieures — rien d'irréversible.
