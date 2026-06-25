# Couverture CHAP_IV -- audit page-par-page du texte principal (2026-06-24)

Chaque notion du livre (texte principal) confrontee au code V9. Source = PDF lu page par page.

## Synthese (112 notions recensees)

**Statut code** : clos 42 | partiel 57 | **manquant 11** | n/a 2

**Fidelite** : fidele 73 | ecart mineur 26 | **ecart majeur 0** | non-verif 13

## Ecarts MAJEURS (enonce formalise != Bourbaki) -- priorite

_Aucun._

## Notions MANQUANTES (dans le livre, pas closes dans le code)

### IV.1a Structures: échelons, extensions canoniques, relations
- [definition] Ensemble des éléments V de S(E₁,…,Eₙ,A₁,…,A_m) vérifiant R (ensemble des structu (E IV.4) -- Bourbaki (E IV.4) définit l'ensemble des structures d'espèce Σ sur E₁,…,Eₙ comme l'ensemble des V de S(E₁,…,Eₙ,A₁,…,A_m) vérifiant R (un sou

### IV.1b Structures: isomorphismes, transport, déduction, espèc
- [remarque] Les automorphismes de E₁,…,Eₙ forment un groupe (A, I, §4, n°1) (E IV.6) -- Bourbaki mentionne que les automorphismes forment un groupe (référence à A, I, §4). Aucun symbole correspondant trouvé dans le code (ni grou
- [remarque] Espèce Θ moins riche que Σ / Σ plus riche que Θ (symétrie de la relation) (E IV.9) -- Bourbaki parle de Σ 'plus riche' et Θ 'moins riche'. La direction Θ moins riche que Σ n'est pas formalisée séparément dans le code.

### IV.3a — Applications universelles : ensembles/applications u
- [remarque] Exemple IV : Extension de l'anneau d'opérateurs d'un module (B-module universel  (E IV.26) -- Aucun symbole correspondant trouvé dans le code. Non mentionné dans les __all__ ni dans les docstrings des fichiers structures/.
- [remarque] Exemple V : Complétion d'un espace uniforme séparé (Σ = espaces uniformes séparé (E IV.26) -- Aucun symbole trouvé dans le code structures/. Non couvert (topologie, hors fragment ensembliste).
- [remarque] Exemple VII : Groupe topologique libre engendré par un espace complètement régul (E IV.26) -- Aucun symbole trouvé dans le code. Non couvert (topologie algébrique, hors fragment ensembliste).

### IV.3b — Applications universelles : exemples (E IV.25–IV.27,
- [remarque] Exemple IV — Extension de l'anneau d'opérateurs d'un module (A-module universel  (E IV.26) -- Aucune fonction ou terme nommé pour cet exemple (Σ=A-modules, α=applications B-linéaires, F_E=extension à A de l'anneau d'opérateurs B de E)
- [remarque] Exemple V — Séparé complété d'un espace uniforme (complétification uniforme) (E IV.26) -- Pas de terme ni fonction dédiée pour cet exemple. La notion de séparé complété (Σ=espaces uniformes séparés et complets, α=applications unif
- [remarque] Exemple VII — Groupe topologique libre engendré par l'espace E (E IV.26–IV.27) -- Aucun terme ou fonction dédiée pour cet exemple (Σ=groupes topologiques séparés, morphismes=homomorphismes continus, α=applications continue
- [remarque] Exemple VIII — Groupe compact associé à E et fonctions presque périodiques (E IV.27) -- Aucun terme, fonction ni symbole pour cet exemple (Σ=groupes compacts, α=homomorphismes continus). La notion de 'groupe compact associé à E'
- [remarque] Exemple IX — Variété d'Albanese de E (E IV.27) -- Aucun terme ni fonction pour cet exemple (Σ=variétés abéliennes sur le même corps de base que E, α=applications rationnelles, CU_I non vérif

## Detail complet par section

### IV.1a Structures: échelons, extensions canoniques, relations transportables, espèces (E IV.1–E IV.4, pages physiques 204–207)
_pages : 203 (E III.99 — bibliographie chap. III, hors périmètre), 204 (E IV.1 — titre ch_  (21 notions, 0 manquantes)

> La section IV.1a couvre pages physiques 204–207 (E IV.1–E IV.4). Page 203 est la bibliographie de chap. III, hors périmètre. Les notions de §1 (schéma d'échelon, construction, notation S(E₁,…,Eₙ)), §2 (extension canonique ⟨f⟩^S, CST1–CST3), §3 (typification, relation transportable) et §4 (espèce de structure, théorie T_Σ, structure générique) sont toutes PRÉSENTES dans le code iv_1_structures_isomorphismes, principalement dans ensembles_especes_echelon.py, ensembles_especes_typification.py et ensembles_especes.py. Toutes les définitions sont fidèlement représentées au niveau représentationnel (objets Python/Termes du fragment objet) avec justification méta honnête. CST1 et CST2 sont documentés comme REPORTÉS (récurrence méta sur le schéma non close) et fournis comme hypothèses explicites dans les théorèmes qui les utilisent (ensembles_transport_iso_props.py). CST3 est également en hypothèse explicite. La notation S(E₁,…,Eₙ) est introduite dans ensembles_especes_echelon.py (fonction `echelon`). La notation ⟨f₁,…,fₙ⟩^S est introduite dans `extension_canonique`. L'ensemble des structures d'espèce Σ sur E₁,…,Eₙ (l'ensemble des V de S(…) vérifiant R) n'est pas explicitement formalisé comme ensemble objet séparé. Couverture globale : définitions ~90 % clos/représentationnel, CST1/CST2/CST3 partiels (hypothèses non closes), notion « ensemble des structures d'espèce » manquante.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Schéma de construction d'échelon | definition | E IV.1 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Schéma de construction d'échelon sur n termes | definition | E IV.1 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Construction d'échelon de schéma S sur E₁,…,Eₙ | definition | E IV.1 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Échelon S(E₁,…,Eₙ) — notation et définition | notation | E IV.2 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Extension canonique ⟨f₁,…,fₙ⟩^S des applications | definition | E IV.2 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| Notation ⟨f₁,…,fₙ⟩^S | notation | E IV.2 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| CST1 — fonctorialité de l'extension canonique: ⟨f₁'∘f₁, | critere | E IV.2 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| CST2 — injective/surjective préservée par extension can | critere | E IV.2 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| CST3 — réciproque de la bijection étendue: ⟨f₁⁻¹,…,fₙ⁻¹ | critere | E IV.3 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| Typification des lettres s₁,…,s_p | definition | E IV.3 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Relation transportable (dans T) pour la typification T | definition | E IV.3 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| Notation s_j' = ⟨f₁,…,fₙ,Id₁,…,Id_m⟩^{S_j}(s_j) (relati | notation | E IV.3 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Espèce de structure Σ | definition | E IV.4 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Caractérisation typique de Σ | definition | E IV.4 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Axiome de l'espèce Σ (la relation R transportable) | definition | E IV.4 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Théorie de l'espèce de structure Σ (théorie T_Σ) | definition | E IV.4 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| U est une structure d'espèce Σ sur E₁,…,Eₙ (dans T') | definition | E IV.4 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Structure générique d'espèce Σ (la constante s dans T_Σ | definition | E IV.4 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| Ensembles de base principaux E₁,…,Eₙ munis de la struct | definition | E IV.4 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Ensemble des éléments V de S(E₁,…,Eₙ,A₁,…,A_m) vérifian | definition | E IV.4 | manquant | non_verifiable |  |
| Exemples de schémas d'échelon (𝔓(𝔓(E))×𝔓(F), schémas po | remarque | E IV.2 | clos | fidele | bourbaki/structures/iv_1_structures_isom |

### IV.1b Structures: isomorphismes, transport, déduction, espèces équivalentes
_pages : 208–212 (E IV.5–E IV.9)_  (21 notions, 0 manquantes)

> Pages 208–212 couvrent : la fin des exemples d'espèces (§4, p. 208), la section 5 « Isomorphismes et transport de structures » (pp. 209–210) introduisant la définition d'isomorphisme (relation (4)), le transport de structure, la réciproque d'un isomorphisme, la notion « sont isomorphes », l'automorphisme, l'espèce univalente, CST4 (composition d'isomorphismes), CST5 (unicité du transport) ; la section 6 « Déduction de structures » (pp. 210–212) introduisant le terme intrinsèque, le procédé de déduction, la structure déduite/sous-jacente, l'espèce plus riche, et le critère CST6 (fonctorialité de la déduction) ; et la section 7 « Espèces de structure équivalentes » (p. 212) introduisant la notion d'espèces équivalentes par l'intermédiaire de procédés P et Q, et le critère CST7 (isomorphisme Σ ⟺ isomorphisme Θ pour espèces équivalentes). La couverture du code est très bonne pour les définitions et partielle/manquante pour les énoncés les plus fins (groupe des automorphismes, univalence, espèce plus riche comme définition complète).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition d'isomorphisme (f₁,…,fₙ) de (E,U) sur (E',U' | definition | E IV.5 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Transport de structure U' = ⟨f₁,…,fₙ,Id₁,…,Id_m⟩^S(U) | definition | E IV.5 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Isomorphismes réciproques l'un de l'autre | definition | E IV.6 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Définition : (E₁,…,Eₙ) munis de U sont isomorphes à (E₁ | definition | E IV.6 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| « Sont isomorphes » est réflexive — tout ensemble struc | proposition | E IV.6 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| Automorphisme de E₁,…,Eₙ (isomorphisme de E sur E pour  | definition | E IV.6 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| L'identité Δ_E est un automorphisme | proposition | E IV.6 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| Les automorphismes de E₁,…,Eₙ forment un groupe (A, I,  | remarque | E IV.6 | manquant | non_verifiable |  |
| Espèce de structure univalente (deux structures quelcon | definition | E IV.6 | partiel | ecart_mineur | bourbaki/structures/iv_1_structures_isom |
| CST4 — Composition d'isomorphismes est un isomorphisme  | critere | E IV.6 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST5 — Unicité de la structure transportée (une seule s | critere | E IV.7 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| Terme intrinsèque pour s, de type T (conditions 1° et 2 | definition | E IV.7 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| Procédé de déduction d'une structure d'espèce Θ à parti | definition | E IV.7 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| Structure déduite ou subordonnée à 𝒮 par le procédé P | definition | E IV.8 | clos | fidele | bourbaki/structures/iv_1_structures_isom |
| Structure d'espèce Θ sous-jacente à 𝒮 (U_j = certaines  | definition | E IV.8 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| CST6 — Fonctorialité de la déduction : (h) isomorphisme | critere | E IV.7 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Espèce Σ plus riche que l'espèce Θ (§6 Exemple 3, mêmes | definition | E IV.9 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| Espèce Θ moins riche que Σ / Σ plus riche que Θ (symétr | remarque | E IV.9 | manquant | non_verifiable |  |
| Espèces de structure équivalentes par l'intermédiaire d | definition | E IV.9 | partiel | fidele | bourbaki/structures/iv_1_structures_isom |
| CST7 — Pour Σ,Θ équivalentes : (f) iso pour Σ ⟺ (f) iso | critere | E IV.9 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Transport donne un isomorphisme — le transport fait de  | proposition | E IV.5 | clos | fidele | bourbaki/structures/iv_1_structures_isom |

### IV.2a Morphismes, structures plus fines, structures initiales (pages 213–217)
_pages : p-213 (E IV.10), p-214 (E IV.11), p-215 (E IV.12), p-216 (E IV.13), p-217 (E IV._  (19 notions, 0 manquantes)

> Les pages 213–217 couvrent la fin du §1 (CST7, p.213) puis l'intégralité du §2 dans ses trois premiers numéros : §2.1 Morphismes (conditions MO_I/MO_II/MO_III et définition du σ-morphisme, CST8 caractérisation des isomorphismes), §2.2 Structures plus fines (définition « plus fine / moins fine », relation d'ordre sur les structures, exemples ordre/algèbre/topologie), §2.3 Structures initiales (propriété (IN), CST9 unicité et « moins fine », début CST10). La formalisation est très avancée : les définitions clés (σ-morphisme, plus/moins fine, comparables, strictement plus fine, image réciproque, structure induite, structure produit, structure initiale) et les théorèmes logiquement directs (CST8 via factorisation_unique_des_solutions, CST9 via cst9_unicite_initiale, réflexivité et transitivité de « plus fine ») sont certifiés au noyau LCF. Les lacunes réelles sont : (a) les axiomes-schémas MO_I/MO_II/MO_III en tant qu'axiomes du fragment objet (assumés comme prémisses explicites, non postulés — choix architectural délibéré) ; (b) CST8 au sens strict de MO_III-caractérisation (le sens bijection⟺(morph f ∧ morph f⁻¹) est laissé partiel : est_iso_morph est défini mais la vraie équivalence MO_III entre est_isomorphisme(Σ,…) et la définition par morphismes croisés n'est pas close) ; (c) l'existence des structures initiales (CST9 existence) reste reportée (seule l'unicité est certifiée).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| CST7 — isomorphisme pour Σ ⟺ isomorphisme pour Θ (espèc | critere | E IV.10 | partiel | ecart_mineur | bourbaki/structures/iv_2_morphismes_stru |
| (MO_I) — σ{x,y,s,t} ⊂ F(x;y) (le terme des morphismes e | axiome | E IV.11 | partiel | ecart_mineur | bourbaki/structures/iv_2_morphismes_stru |
| (MO_II) — la composée de deux σ-morphismes est un σ-mor | axiome | E IV.11 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| (MO_III) — pour qu'une bijection f soit un isomorphisme | axiome | E IV.11 | partiel | ecart_mineur | bourbaki/structures/iv_2_morphismes_stru |
| σ-morphisme (définition) — f est un σ-morphisme de x mu | definition | E IV.11 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Composée de deux σ-morphismes est un σ-morphisme (propo | proposition | E IV.11 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST8 — unicité à isomorphisme unique près de la solutio | critere | E IV.12 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Remarque — la notion de morphisme n'implique pas la not | remarque | E IV.12 | non_applicable | non_verifiable |  |
| Structure plus fine / moins fine (définition) — 𝒮₁ plus | definition | E IV.13 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Structures comparables (définition) — l'une est plus fi | definition | E IV.13 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Structure strictement plus fine (définition) | definition | E IV.13 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| « moins fine » est une relation d'ordre (réflexive d'ap | proposition | E IV.13 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Deux structures comparables d'espèce Σ sur E sont ident | remarque | E IV.13 | partiel | ecart_mineur | bourbaki/structures/iv_2_morphismes_stru |
| Propriété (IN) — condition caractéristique de la struct | definition | E IV.14 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Structure initiale (définition) — structure vérifiant ( | definition | E IV.14 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST9 — si elle existe, la structure initiale est la moi | critere | E IV.14 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST10 — critère de transitivité des structures initiale | critere | E IV.14 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Image réciproque d'une structure (cas I singleton — str | definition | E IV.14 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Structure produit (structure initiale pour les projecti | definition | E IV.14 | clos | fidele | bourbaki/structures/iv_2_morphismes_stru |

### IV.2b — Structures finales, produit, quotient (§4 Exemples de structures initiales + §5 Structures finales)
_pages : 218–223 (E IV.15–E IV.20)_  (15 notions, 0 manquantes)

> Les 6 pages couvrent deux sous-sections : §4 "Exemples de structures initiales" (image réciproque, structure induite, structure produit, CST11–CST17) et §5 "Structures finales" (propriété (FI), image directe, structure quotient, CST18–CST19). La couverture est très bonne pour les définitions et pour la plupart des critères. Les définitions (image réciproque, induite, produit, finale, image directe, quotient) sont toutes formalisées dans ensembles_universel_morphismes.py et ensembles_universel_finale.py. CST11, CST12, CST13, CST14, CST15, CST16, CST17, CST18, CST19 sont tous présents dans le sous-dossier cst_criteres/. Tous ces critères sont toutefois PARTIELS : on certifie uniquement le palier d'unicité/égalité (« entraînent que S=S' ») ou le palier conditionnel, mais l'équivalence d'existence a)⟺b) est explicitement reportée (CST22 non construit). La remarque (Bourbaki p.221) sur les conditions nécessaires de CST16 est non formalisée. La continuation de la preuve de la proposition d'existence de la structure initiale (partie b, p.218) n'est pas une notion nommée autonome mais fait partie de la preuve de la prop. de §3 déjà auditée.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition — image réciproque par f de la structure S ( | definition | E IV.15 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Définition — structure induite par S sur B via l'inject | definition | E IV.16 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST11 — transitivité des structures induites (B⊂A, C⊂B  | critere | E IV.16 | partiel | ecart_mineur | bourbaki/structures/iv_2_morphismes_stru |
| CST12 — restriction d'un morphisme aux sous-structures  | critere | E IV.16 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Définition — structure produit des S_ι sur E = ∏A_ι (Ex | definition | E IV.16 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST13 — associativité de la structure produit (partitio | critere | E IV.17 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST14 — compatibilité produit/sous-structure (B=∏B_ι⊂∏A | critere | E IV.17 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST15 — lien image réciproque/produit (l'imrec du produ | critere | E IV.17 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST16 — famille de morphismes f_ι:E'→A_ι définit un mor | critere | E IV.17 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST17 — un morphisme est caractérisé par son graphe (pr | critere | E IV.18 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Définition — structure finale pour la famille (A_ι,S_ι, | definition | E IV.19 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Définition — image directe par f de la structure S (cas | definition | E IV.19 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| Définition — structure quotient de S par R (image direc | definition | E IV.19 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST18 — la structure finale est la plus fine parmi cell | critere | E IV.19 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |
| CST19 — transitivité des structures finales (deux famil | critere | E IV.20 | partiel | fidele | bourbaki/structures/iv_2_morphismes_stru |

### IV.3a — Applications universelles : ensembles/applications universels, existence (E IV.22–E IV.26, pages physiques 225–229)
_pages : 224–229 (E IV.21–E IV.26) ; §3 commence p. 225 (E IV.22). La p. 224 (E IV.21) es_  (26 notions, 0 manquantes)

> Le §3 « Applications universelles » (E IV.22–E IV.26) introduit sept catégories de notions : (1) les données du problème (Σ-ensemble, σ-morphisme, terme α{x,s}, axiomes QM_I/QM_II, α-application) ; (2) la solution (condition AU, reformulation AU_I'/AU_II', équivalence AU ⟺ AU_I'+AU_II') ; (3) l'existence (partie Σ-permise, conditions CU_I/CU_II/CU_III, cardinal à possibilité Σ-permise, critère CST22) ; (4) l'injectivité de φ_E (critère CST23) ; (5) sept exemples illustratifs. La couverture V9 est BONNE sur les définitions et formules de premier ordre : les fichiers ensembles_universel_applications.py et ensembles_structures_complements.py couvrent toutes les définitions et les lemmes logiques directs (AU ⟺ AU_I'+AU_II' par projections, extraction des CU_k). En revanche : (a) l'équivalence (AU) ⟺ (AU_I')+(AU_II') n'est certifiée que dans un sens facile (projection), pas comme biconditional clos quantifié sur tous (F,S,φ) ; (b) CST22 est ÉNONCÉ (forme conditionnelle) mais sa PREUVE (construction de F_E par quotient du libre) est honnêtement reportée — donc partiel ; (c) CST23 est formalisé uniquement pour le sens logique de la contraposition ponctuelle, pas avec le contenu existentiel (∃ α-application séparante) du critère de Bourbaki — partiel ; (d) les exemples algébriques (corps des fractions, produit tensoriel, groupes libres, Stone-Čech, complétion uniforme) sont des termes opaques illustratifs, non formalisés comme théorèmes ; (e) il n'y a pas de dossier iv_3 distinct : tout est dans la racine structures/ — écart structurel mineur.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Σ-ensemble (ensemble muni d'une structure d'espèce Σ) | definition | E IV.22 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| σ-morphisme (notion de morphisme pour l'espèce Σ) | definition | E IV.22 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Terme α{x,s} définissant les α-applications (données du | notation | E IV.22 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| (QM_I) : α{x,s} ⊂ 𝓕(E;x) est vraie dans 𝒯_Σ | axiome | E IV.22 | partiel | fidele | bourbaki/structures/ensembles_universel_ |
| (QM_II) : f morphisme ⇒ φ ∈ α[F,S] entraîne f∘φ ∈ α[F', | axiome | E IV.22 | partiel | fidele | bourbaki/structures/ensembles_universel_ |
| α-application de E dans x (muni de s) : φ ∈ α{x,s} | definition | E IV.22 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| Σ-ensemble universel F_E et α-application universelle φ | definition | E IV.22–E IV.23 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| Solution du problème d'application universelle pour E : | notation | E IV.23 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| Unicité à un isomorphisme unique près de la solution (C | remarque | E IV.23 | partiel | fidele | bourbaki/structures/ensembles_structures |
| (AU_I') : pour tout Σ-ensemble F et toute α-application | critere | E IV.23 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| (AU_II') : pour tout Σ-ensemble F, deux morphismes de F | critere | E IV.23 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| Théorème : (AU) ⟺ (AU_I') et (AU_II') | proposition | E IV.23 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| §3 n°2 — Partie Σ-permise d'un Σ-ensemble F (G ⊂ F avec | definition | E IV.24 | clos | fidele | bourbaki/structures/ensembles_structures |
| (CU_I) : sur tout produit d'une famille de Σ-ensembles, | critere | E IV.23 | clos | fidele | bourbaki/structures/ensembles_structures |
| (CU_II) : l'application (φ_ι)_{ι∈I} dans le produit est | critere | E IV.23 | clos | fidele | bourbaki/structures/ensembles_structures |
| (CU_III) : existence d'un cardinal 𝔞 à possibilité Σ-pe | critere | E IV.23–E IV.24 | clos | fidele | bourbaki/structures/ensembles_structures |
| Cardinal 𝔞 à possibilité Σ-permise (témoin de CU_III) | notation | E IV.23–E IV.24 | clos | fidele | bourbaki/structures/ensembles_structures |
| CST22 : si (CU_I) à (CU_III) sont vérifiées, le problèm | critere | E IV.24 | partiel | fidele | bourbaki/structures/ensembles_structures |
| CST23 : (F_E, φ_E) solution ⇒ (φ_E injection ⟺ les α-ap | critere | E IV.25 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Σ-ensemble libre engendré par E (α = 𝓕(E;x), morphismes | definition | E IV.25 | clos | fidele | bourbaki/structures/ensembles_universel_ |
| Exemple II : Corps des fractions d'un anneau intègre (Σ | remarque | E IV.25–E IV.26 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple III : Produit tensoriel A ⊗_C B (Σ = C-modules, | remarque | E IV.26 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple IV : Extension de l'anneau d'opérateurs d'un mo | remarque | E IV.26 | manquant | non_verifiable |  |
| Exemple V : Complétion d'un espace uniforme séparé (Σ = | remarque | E IV.26 | manquant | non_verifiable |  |
| Exemple VI : Compactification de Stone-Čech d'un espace | remarque | E IV.26 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple VII : Groupe topologique libre engendré par un  | remarque | E IV.26 | manquant | non_verifiable |  |

### IV.3b — Applications universelles : exemples (E IV.25–IV.27, p. 228–230) + Exercices §1–§3 (p. 231–234)
_pages : p-228.png (E IV.25), p-229.png (E IV.25–IV.26), p-230.png (E IV.26–IV.27), p-231_  (10 notions, 0 manquantes)

> La section §IV.3b (p. 228–230, E IV.25–IV.27) est intitulée « 3. Exemples d'applications universelles » et présente neuf exemples numérotés I à IX illustrant le problème d'application universelle défini au §IV.3.1. Ces exemples ne constituent pas des définitions, théorèmes ou propositions formellement nommés au sens Bourbaki : ils sont présentés comme des exemples (les astérisques signalent ceux traités en détail dans la suite). Chaque exemple introduit une terminologie spécifique (Σ-ensemble libre, corps des fractions, produit tensoriel, anneau d'opérateurs étendu, séparé complété, compactifié de Stone-Čech, groupe topologique libre, groupe compact associé, fonction presque périodique, variété d'Albanese). Ces termes sont de nature terminologique, non de nature déductive ; ils ne donnent pas lieu à un critère CS ou CF ni à un théorème numéroté. Les pages 231–234 sont entièrement consacrées aux Exercices des §1, §2 et §3 du chapitre IV ; elles ne contiennent aucune notion formelle Bourbaki à formaliser. Dans le code, le module ensembles_universel_applications.py couvre partiellement ces exemples via des termes opaques illustratifs (corps_des_fractions, produit_tensoriel, compactifie_stone_cech, alpha_libre / est_libre_engendre). Les exemples relevant d'autres branches (topologie, algèbre, géométrie algébrique) sont documentés comme REPORTÉS et hors du fragment ensembliste, ce qui est honnête. Aucune notion formelle manquante n'est identifiée dans ce segment purement exemplatif.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Exemple I — Σ-ensemble libre engendré par E (structures | remarque | E IV.25 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple II — Corps des fractions d'un anneau (anneau co | remarque | E IV.25 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple III — Produit tensoriel A⊗_C B de deux C-module | remarque | E IV.25–IV.26 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple IV — Extension de l'anneau d'opérateurs d'un mo | remarque | E IV.26 | manquant | non_verifiable |  |
| Exemple V — Séparé complété d'un espace uniforme (compl | remarque | E IV.26 | manquant | non_verifiable |  |
| Exemple VI — Compactifié de Stone-Čech d'un espace comp | remarque | E IV.26 | partiel | ecart_mineur | bourbaki/structures/ensembles_universel_ |
| Exemple VII — Groupe topologique libre engendré par l'e | remarque | E IV.26–IV.27 | manquant | non_verifiable |  |
| Exemple VIII — Groupe compact associé à E et fonctions  | remarque | E IV.27 | manquant | non_verifiable |  |
| Exemple IX — Variété d'Albanese de E | remarque | E IV.27 | manquant | non_verifiable |  |
| Exercices §1–§3 du chapitre IV (p. 231–234) | remarque | E IV.28–IV.31 | non_applicable | non_verifiable |  |
