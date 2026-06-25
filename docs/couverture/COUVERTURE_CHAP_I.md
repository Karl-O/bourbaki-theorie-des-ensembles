# Couverture CHAP_I -- audit page-par-page du texte principal (2026-06-24)

Chaque notion du livre (texte principal) confrontee au code V9. Source = PDF lu page par page.

## Synthese (136 notions recensees)

**Statut code** : clos 58 | partiel 11 | **manquant 20** | n/a 47

**Fidelite** : fidele 69 | ecart mineur 13 | **ecart majeur 0** | non-verif 54

## Ecarts MAJEURS (enonce formalise != Bourbaki) -- priorite

_Aucun._

## Notions MANQUANTES (dans le livre, pas closes dans le code)

### I.2 Théorèmes (axiomes, démonstrations, substitutions, compa
- [critere] C2 : A thm de T, T terme de T, x lettre ⟹ (T|x)A thm de (T|x)T (E I.23) -- Explicitement signalé comme non couvert dans criteres_C.py ligne 9 : «Non couverts (métathéorèmes hors fragment objet) : C2–C5». Aucun symbo
- [critere] C3 : A thm de T, T terme de T, x lettre pas constante de T ⟹ (T|x)A thm de T (E I.23) -- Explicitement signalé comme non couvert dans criteres_C.py ligne 9 : «Non couverts (métathéorèmes hors fragment objet) : C2–C5». Aucun symbo
- [definition] Théorie plus forte (définition) (E I.24) -- Bourbaki : T' est plus forte que T si tout signe de T est signe de T', tout axiome explicite de T est théorème de T', et tout schéma de T es
- [critere] C4 : T' plus forte que T ⟹ tout théorème de T est théorème de T' (E I.24) -- Explicitement signalé comme non couvert dans criteres_C.py ligne 9 : «Non couverts (métathéorèmes hors fragment objet) : C2–C5». Aucun symbo
- [definition] Théories équivalentes (définition) (E I.24) -- Bourbaki : T et T' sont équivalentes si chacune est plus forte que l'autre. Aucun objet ou fonction correspondant trouvé dans le code.
- [critere] C5 : si dans T' les (T_1|a_1)...(T_h|a_h)A_i sont des théorèmes et les signes/sc (E I.24) -- Explicitement signalé comme non couvert dans criteres_C.py ligne 9 : «Non couverts (métathéorèmes hors fragment objet) : C2–C5». Aucun symbo
- [remarque] Remarque : sous hypothèses C5, si T contradictoire alors T' contradictoire (E I.24) -- Remarque finale de la section, conséquence de C5 : si T est contradictoire (A et non A sont des théorèmes), alors T' l'est aussi. Aucune for

### I.3 Théories logiques (axiomes S1-S4, critères C6-C21, métho
- [definition] Définition : théorie logique (E I.25) -- La définition 'toute théorie T dans laquelle S1-S4 fournissent des axiomes implicites' n'est pas formalisée comme objet autonome. Le noyau i
- [theoreme] Théorème : théorie logique contradictoire ⇒ toute relation est théorème (E I.25) -- La preuve narrative (via S2, C1, C1 à nouveau) n'est pas formalisée comme Theoreme clos. Aucun fichier ni symbole correspondant trouvé.

### I.4 Théories quantifiées
- [critere] C26 : (∀x)R et (τ_x(¬R)|x)R sont équivalentes dans T (théorie logique) (E I.32) -- C26 est mentionné dans les commentaires de noyau.py comme étape dans la justification de C27, mais aucune fonction def c26 ou symbole c26 n'
- [critere] C39 : A⇒(R⇒S) théorème ⟹ (∃_A x)R⇒(∃_A x)S et (∀_A x)R⇒(∀_A x)S (monotonie des q (E I.37) -- C39 n'a pas de symbole dans le code. Déclaré 'C32, C33, C39–C42 restent workflow-vérifiés (lock-in à finir)' dans criteres_quantif2.py.
- [critere] C40 : (∀_A x)(R et S) ⇔ ((∀_A x)R et (∀_A x)S) et (∃_A x)(R ou S) ⇔ ((∃_A x)R ou (E I.37) -- C40 absent du code. Déclaré 'workflow-vérifiés, lock-in à finir' dans criteres_quantif2.py.
- [critere] C41 : (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S) et (∃_A x)(R et S) ⇔ (R et (∃_A x)S) qua (E I.37) -- C41 absent du code. Déclaré 'workflow-vérifiés, lock-in à finir' dans criteres_quantif2.py.
- [critere] C42 : (∀_A x)(∀_B y)R ⇔ (∀_B y)(∀_A x)R et (∃_A x)(∃_B y)R ⇔ (∃_B y)(∃_A x)R et  (E I.37) -- C42 absent du code. Déclaré 'workflow-vérifiés, lock-in à finir' dans criteres_quantif2.py.

### I.5 Théories égalitaires
- [definition] Définition : théorie égalitaire (E I.38) -- Le concept est réalisé structurellement (egalite() dans assemblage.py, S6/S7 dans le noyau, S1-S5 dans noyau.py), mais il n'existe aucun obj
- [critere] Critère C43 — (T=U et R{T}) équivalent (T=U et R{U}) (E I.39) -- C43 est mentionné dans un commentaire de congruence_quantif.py (contexte C32-C42 workflow) et utilisé informellement dans ensembles_correspo
- [definition] Notion : équation (T=U), solution en x, solution complète/générale (E I.40) -- Ces notions (équation, solution d'une équation en x comme terme V tel que (V|x)(T=U) soit théorème, solution complète) sont des définitions 
- [definition] Définition : relation univoque en x (au plus un x vérifiant R) (E I.40) -- Ni la définition de 'relation univoque en x' ni le terme est_univoque n'existent dans i_4_egalitaires ni dans le reste de bourbaki/. La noti
- [critere] Critère C45 — R univoque en x dans T ⟺ R ⇒ (x = τx(R)) (E I.41) -- Aucune fonction nommée c45, univoque, ou portant cet énoncé (R ⇒ x=τx(R)) n'est présente dans le code certifié. C45 est mentionné commentair
- [definition] Définition : relation fonctionnelle en x (∃x.R et univoque en x) (E I.41) -- La définition de 'relation fonctionnelle en x dans T' au sens §I.5 (conjonction ∃x.R et unicité) n'est pas formalisée dans i_4_egalitaires. 

## Detail complet par section

### I.1 Termes et relations
_pages : p-014 à p-020 (E I.14 – E I.20)_  (28 notions, 0 manquantes)

> La section §I.1 pose les fondations syntaxiques : signes (logiques, lettres, spécifiques), assemblages avec liens, opérateurs de substitution (B|x)A et τ_x(A), puis la notion de théorie mathématique (termes/relations/théorèmes). Les critères de substitution CS1–CS5 sont des méta-identités sur (B|x) et τ. Les constructions formatives (conditions a–e, notion de poids, espèces) définissent inductivement termes et relations. Les critères formatifs CF1–CF8 en déduisent les propriétés de clôture. Le code couvre très bien la couche assemblage (assemblage.py) et les critères CS/CF (criteres_CS.py, criteres_CF.py, lecture.py). Les définitions fondamentales (signes, assemblage, substitution, τ) sont fidèlement réalisées dans assemblage.py. CS1–CS5 et CF1–CF8 sont présents comme vérificateurs méta (fonctions booléennes) — c'est le statut correct (non_applicable au sens LCF, ou partiel au sens où ce ne sont pas des Theoreme noyau). Les notions «poids», «première/deuxième espèce», «construction formative» sont subsumées structurellement par la couche lecture (grammar en notation préfixe de Łukasiewicz). CF6 dans le code (préservation d'espèce pour un seul assemblage avec y∉A) est plus faible que l'énoncé Bourbaki (préservation d'une construction formative entière) — écart mineur car le corollaire utile (CF7) est bien présent. La notion «théorie mathématique» elle-même n'a pas d'objet Python dédié à I.1 (elle est réalisée implicitement par le noyau + signature).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Signes logiques : □, τ, ∨, ¬ | definition | E I.14 | clos | fidele | bourbaki/assemblage/assemblage.py:SIGNES |
| Lettres (latines, avec accents/primes) | definition | E I.14 | clos | fidele | bourbaki/assemblage/assemblage.py:est_le |
| Signes spécifiques (=, ∈ pour la théorie des ensembles) | definition | E I.14 | clos | fidele | bourbaki/logique/i_1_termes_relations/le |
| Assemblage (succession de signes avec liens τ–□) | definition | E I.14-15 | clos | fidele | bourbaki/assemblage/assemblage.py:Assemb |
| Notation AB (concaténation d'assemblages) | notation | E I.15 | clos | fidele | bourbaki/assemblage/assemblage.py:concat |
| Notation ∨ A ¬ B (assemblage disjonction) | notation | E I.15 | clos | fidele | bourbaki/assemblage/assemblage.py:disjon |
| Opérateur τ_x(A) (lien τ–□, suppression de x) | notation | E I.15-16 | clos | fidele | bourbaki/assemblage/assemblage.py:tau_x |
| Substitution (B/x)A | notation | E I.16 | clos | fidele | bourbaki/assemblage/assemblage.py:substi |
| Théorie mathématique (termes, relations, théorèmes) | definition | E I.15 | non_applicable | non_verifiable |  |
| CS1 : x'∉A ⟹ (B/x')(x'/x)A = (B/x)A | critere | E I.17 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CS2 : x≠y, y∉B ⟹ (B/x)(C/y)A = ((B/x)C/y)(B/x)A | critere | E I.17 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CS3 : x'∉A ⟹ τ_x(A) = τ_x'((x'/x)A) | critere | E I.17 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CS4 : x∉B, x≠y ⟹ (B/y)τ_x(A) = τ_x((B/y)A) | critere | E I.17 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CS5 : (C/x) est homomorphisme pour ¬, ∨, ⇒, s (signe sp | critere | E I.17 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| Poids d'un signe spécifique | definition | E I.17 | partiel | ecart_mineur | bourbaki/logique/i_1_termes_relations/le |
| Assemblage de première espèce (commence par τ ou se réd | definition | E I.17-18 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/le |
| Assemblage de deuxième espèce (commence par ∨, ¬ ou sig | definition | E I.17-18 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/le |
| Construction formative (suite d'assemblages vérifiant l | definition | E I.17-18 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/le |
| Terme (assemblage de 1ère espèce figurant dans une cons | definition | E I.18 | clos | fidele | bourbaki/logique/i_1_termes_relations/le |
| Relation (assemblage de 2ème espèce figurant dans une c | definition | E I.18 | clos | fidele | bourbaki/logique/i_1_termes_relations/le |
| CF1 : A,B relations ⟹ (A∨B) relation | critere | E I.19 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CF2 : A relation ⟹ (¬A) relation | critere | E I.19 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CF3 : A relation, x lettre ⟹ τ_x(A) terme | critere | E I.19 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CF4 : A₁,...,Aₙ termes, s signe spécifique de poids n ⟹ | critere | E I.19 | non_applicable | ecart_mineur | bourbaki/logique/i_1_termes_relations/cr |
| CF5 : A,B relations ⟹ (A⇒B) relation (déduit de CF1+CF2 | critere | E I.19 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CF6 : y∉Aᵢ ⟹ (y/x)A₁,...,(y/x)Aₙ est une construction f | critere | E I.19 | non_applicable | ecart_mineur | bourbaki/logique/i_1_termes_relations/cr |
| CF7 : (y/x)A garde l'espèce de A (y lettre quelconque) | critere | E I.20 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CF8 : T terme ⟹ (T/x)A garde l'espèce de A | critere | E I.20 | non_applicable | fidele | bourbaki/logique/i_1_termes_relations/cr |

### I.2 Théorèmes (axiomes, démonstrations, substitutions, comparaison des théories)
_pages : p-021.png (E I.21), p-022.png (E I.22), p-023.png (E I.23), p-024.png (E I.24)_  (19 notions, 0 manquantes)

> La section §2 (pages E I.21–24) introduit la structure d'une théorie formelle (axiomes explicites, constantes, schémas, axiomes implicites), puis la démonstration et le théorème, puis le critère fondamental C1 (syllogisme/modus ponens), les critères de substitution C2–C3, et enfin la comparaison des théories (plus forte, équivalente) avec les critères C4–C5, plus une remarque sur la contradiction. Le code V9 implémente solidement C1 comme primitive du noyau (modus_ponens) et la classe Theorie avec axiomes explicites/implicites/schémas. Les notions métamathématiques (démonstration, théorème-comme-concept, texte démonstratif, relation vraie/fausse, théorie contradictoire) sont subsumées structurellement par le noyau LCF. C2–C5 sont explicitement signalés comme non couverts dans criteres_C.py (commentaire ligne 9 : «Non couverts (métathéorèmes hors fragment objet) : C2–C5»), et aucun symbole C2/C3/C4/C5 ni de notion «théorie plus forte» ou «équivalente» n'a été trouvé dans le code.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Notations non(A), (A) ou (B), (A)⇒(B) | notation | E I.21 | clos | fidele | bourbaki/assemblage/assemblage.py:negati |
| Axiomes explicites d'une théorie | definition | E I.21 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| Constantes d'une théorie | definition | E I.21 | partiel | ecart_mineur | bourbaki/logique/i_2_criteres_C/noyau/no |
| Schémas d'une théorie | definition | E I.21 | partiel | ecart_mineur | bourbaki/logique/i_2_criteres_C/noyau/no |
| Axiomes implicites d'une théorie | definition | E I.22 | non_applicable | non_verifiable | bourbaki/logique/i_2_criteres_C/noyau/no |
| Texte démonstratif (construction formative auxiliaire + | definition | E I.22 | non_applicable | non_verifiable | bourbaki/logique/i_2_criteres_C/noyau/no |
| Démonstration d'une théorie T | definition | E I.22 | non_applicable | non_verifiable | bourbaki/logique/i_2_criteres_C/noyau/no |
| Théorème d'une théorie T (relation figurant dans une dé | definition | E I.22 | non_applicable | non_verifiable | bourbaki/logique/i_2_criteres_C/noyau/no |
| Relation vraie dans T / T vérifie R en x / solution de  | definition | E I.22 | non_applicable | non_verifiable | bourbaki/assemblage/assemblage.py:substi |
| Relation fausse dans T / théorie contradictoire | definition | E I.22 | non_applicable | non_verifiable |  |
| C1 (syllogisme) : A thm, A⇒B thm ⟹ B thm | critere | E I.23 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| Substitution dans une théorie : définition de (T/x)T (t | definition | E I.23 | partiel | ecart_mineur | bourbaki/assemblage/assemblage.py:substi |
| C2 : A thm de T, T terme de T, x lettre ⟹ (T/x)A thm de | critere | E I.23 | manquant | non_verifiable |  |
| C3 : A thm de T, T terme de T, x lettre pas constante d | critere | E I.23 | manquant | non_verifiable |  |
| Théorie plus forte (définition) | definition | E I.24 | manquant | non_verifiable |  |
| C4 : T' plus forte que T ⟹ tout théorème de T est théor | critere | E I.24 | manquant | non_verifiable |  |
| Théories équivalentes (définition) | definition | E I.24 | manquant | non_verifiable |  |
| C5 : si dans T' les (T_1/a_1)...(T_h/a_h)A_i sont des t | critere | E I.24 | manquant | non_verifiable |  |
| Remarque : sous hypothèses C5, si T contradictoire alor | remarque | E I.24 | manquant | non_verifiable |  |

### I.3 Théories logiques (axiomes S1-S4, critères C6-C21, méthodes de démonstration, conjonction, équivalence)
_pages : p-025 (E I.25) à p-030 (E I.30)_  (28 notions, 0 manquantes)

> Le §3 introduit la notion de théorie logique (S1-S4 comme axiomes implicites), 16 critères nommés (C6-C21), 3 méthodes de démonstration (C14, C15, C18/C19), la conjonction (§3.4) et l'équivalence (§3.5) avec leurs critères formatifs et de substitution (CS6, CS7, CF9, CF10). Le noyau LCF (noyau.py) implémente directement S1-S4 comme règles primitives closes et C6 (loi_deduction) comme règle primitive de confiance. Les critères C6-C18 et C20-C21 sont tous présents dans le code (criteres_C.py et tactiques_prop.py) sous forme de fonctions vérifiées. Manquent en tant qu'objets autonomes : la définition formelle de « théorie logique », le théorème sur les théories contradictoires, et C19 (méthode de la constante auxiliaire, métathéorème explicitement écarté dans le code). CS6 et CS7 sont métamathématiquement subsumés par CS5 déjà vérifié. CF9 et CF10 sont présents et clos dans criteres_CF.py. L'arbre de dossiers ne possède pas encore de sous-dossier i_3_theories_logiques : les résultats sont répartis dans i_2_criteres_C (critères C) et i_1_termes_relations (CF/CS).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition : théorie logique | definition | E I.25 | manquant | non_verifiable |  |
| S1 : (A ou A) ⇒ A est un axiome | axiome | E I.25 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| S2 : A ⇒ (A ou B) est un axiome | axiome | E I.25 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| S3 : (A ou B) ⇒ (B ou A) est un axiome | axiome | E I.25 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| S4 : (A ⇒ B) ⇒ ((C ou A) ⇒ (C ou B)) est un axiome | axiome | E I.25 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| Théorème : théorie logique contradictoire ⇒ toute relat | theoreme | E I.25 | manquant | non_verifiable |  |
| C6 : critère de la déduction (A⊢B ⟹ ⊢A⇒B) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| C7 : B ⇒ (A ou B) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C8 : A ⇒ A | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/tactique |
| C9 : ⊢B et ⊢A⇒B ⟹ ⊢A (Modus Ponens / affaiblissement) | critere | E I.26 | clos | ecart_mineur | bourbaki/logique/i_2_criteres_C/criteres |
| C10 : A ou (non A) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C11 : A ⇒ (non non A) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C12 : (A⇒B) ⇒ ((non B)⇒(non A)) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C13 : ⊢A⇒B ⟹ ⊢(B⇒C)⇒(A⇒C) | critere | E I.26 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C14 : critère de la déduction / méthode de l'hypothèse  | critere | E I.27 | non_applicable | non_verifiable | bourbaki/logique/i_2_criteres_C/criteres |
| C15 : réduction à l'absurde ((non A)⊢contradiction ⟹ ⊢A | critere | E I.27 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C16 : (non non A) ⇒ A | critere | E I.28 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C17 : ((non B)⇒(non A)) ⇒ (A⇒B) | critere | E I.28 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C18 : disjonction des cas (⊢A∨B, ⊢A⇒C, ⊢B⇒C ⟹ ⊢C) | critere | E I.28 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C19 : méthode de la constante auxiliaire | critere | E I.28 | non_applicable | non_verifiable |  |
| Notation : A et B := non((non A) ou (non B)) | notation | E I.29 | clos | fidele | bourbaki/assemblage/assemblage.py:conjon |
| CS6 : (T/x)(A et B) identique à ((T/x)A et (T/x)B) | critere | E I.29 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/cr |
| CF9 : A,B relations ⟹ (A et B) relation | critere | E I.29 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| C20 : ⊢A et ⊢B ⟹ ⊢(A et B) | critere | E I.29 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C21 : (A et B)⇒A et (A et B)⇒B | critere | E I.29 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| Notation : A ⟺ B := (A⇒B) et (B⇒A) | notation | E I.30 | clos | fidele | bourbaki/assemblage/assemblage.py:equiva |
| CS7 : (T/x)(A⟺B) identique à ((T/x)A ⟺ (T/x)B) | critere | E I.30 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/cr |
| CF10 : A,B relations ⟹ (A⟺B) relation | critere | E I.30 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |

### I.4 Théories quantifiées
_pages : p-031 à p-037 (E I.31–E I.37)_  (31 notions, 0 manquantes)

> La section §I.4 couvre : (1) la définition des quantificateurs ∃ et ∀ comme abréviations via τ (§I.4.1) ; (2) le schéma axiomatique S5 qui fonde la théorie quantifiée (§I.4.2) ; (3) les propriétés des quantificateurs C26–C34 (§I.4.3) ; (4) la définition et les propriétés des quantificateurs typiques ∃_A, ∀_A avec C35–C42 (§I.4.4). Les critères de substitution CS8–CS11 et les critères formatifs CF11–CF12 sont également introduits ici.\n\nCouverture V9 : les définitions de ∃ et ∀ sont formalisées fidèlement dans assemblage.py. S5 est une primitive du noyau. C27 (généralisation) est une primitive du noyau. C28, C29, C30, C31 (monotonies/congruences), C32–C35 et une partie de C38 sont couverts avec divers degrés. C26 n'a pas de symbole autonome. C32, C33, C39–C42 sont décrits comme « workflow-vérifiés » (lock-in à finir), donc partiels. C36, C37 sont des métathéorèmes explicitement exclus par le code. CS8–CS11 sont absents du code en tant que critères nommés (statut non_applicable : identités d'assemblages réalisées structurellement). CF11 et CF12 sont présents comme fonctions booléennes dans criteres_CF.py.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition : quantificateur existentiel (∃x)R = (τ_x(R) | definition | E I.32 | clos | fidele | bourbaki/assemblage/assemblage.py:existe |
| Définition : quantificateur universel (∀x)R = ¬(∃x)(¬R) | definition | E I.32 | clos | fidele | bourbaki/assemblage/assemblage.py:pour_t |
| Notation : symboles abréviatifs ∃ (quantificateur exist | notation | E I.32 | clos | fidele | bourbaki/assemblage/assemblage.py:existe |
| CS8 : x' ∉ R ⟹ (∃x)R ≡ (∃x')R' et (∀x)R ≡ (∀x')R' où R' | critere | E I.32 | non_applicable | non_verifiable |  |
| CS9 : x ∉ U, y distinct ⟹ (U/y)(∃x)R ≡ (∃x)R' et (U/y)( | critere | E I.32 | non_applicable | non_verifiable |  |
| CF11 : R relation, x lettre ⟹ (∃x)R et (∀x)R sont des r | critere | E I.32 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| Définition : théorie quantifiée (possède S1–S5 comme ax | definition | E I.33 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| S5 : (T/x)R ⇒ (∃x)R  (schéma axiomatique) | axiome | E I.33 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| C26 : (∀x)R et (τ_x(¬R)/x)R sont équivalentes dans T (t | critere | E I.32 | manquant | non_verifiable |  |
| C27 : de Γ⊢R (x non libre dans Γ), déduire Γ⊢(∀x)R  (gé | critere | E I.32 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| C28 : ¬(∀x)R ⇔ (∃x)(¬R)  (négation du universel) | critere | E I.33 | clos | fidele | bourbaki/logique/i_2_criteres_C/criteres |
| C29 : ¬(∃x)R ⇔ (∀x)(¬R)  (négation de l'existentiel) | critere | E I.33-34 | clos | fidele | bourbaki/logique/i_3_quantifies/congruen |
| C30 : (∀x)R ⇒ (T/x)R  (instanciation universelle) | critere | E I.34 | clos | fidele | bourbaki/logique/i_4_egalitaires/tactiqu |
| C31 : R⇒S théorème ⟹ (∀x)R⇒(∀x)S et (∃x)R⇒(∃x)S (monoto | critere | E I.34 | clos | fidele | bourbaki/logique/i_3_quantifies/congruen |
| C32 : R⇔S théorème ⟹ (∀x)R⇔(∀x)S et (∃x)R⇔(∃x)S (congru | critere | E I.34 | partiel | ecart_mineur | bourbaki/logique/i_3_quantifies/congruen |
| C33 : (∀x)(R et S) ⇔ ((∀x)R et (∀x)S) et (∃x)(R ou S) ⇔ | critere | E I.34 | partiel | ecart_mineur | bourbaki/logique/i_3_quantifies/tactique |
| C34 : (∀x)(∀y)R ⇔ (∀y)(∀x)R et (∃x)(∃y)R ⇔ (∃y)(∃x)R et | critere | E I.35 | clos | fidele | bourbaki/logique/i_3_quantifies/criteres |
| Définition : quantificateur typique ∃_A (existentiel bo | definition | E I.35-36 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| Définition : quantificateur typique ∀_A (universel born | definition | E I.35-36 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| Notation : symboles abréviatifs ∃_A et ∀_A (quantificat | notation | E I.36 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| CS10 : x' ∉ R, x' ∉ A ⟹ (∃_A x)R ≡ (∃_A x')R' et (∀_A x | critere | E I.36 | non_applicable | non_verifiable |  |
| CS11 : x ∉ U, y distinct ⟹ (U/y)(∃_A x)R ≡ (∃_A x)R' et | critere | E I.36 | non_applicable | non_verifiable |  |
| CF12 : A, R relations, x lettre ⟹ (∃_A x)R et (∀_A x)R  | critere | E I.36 | clos | fidele | bourbaki/logique/i_1_termes_relations/cr |
| C35 : (∀_A x)R ⇔ (∀x)(A ⇒ R) | critere | E I.36 | clos | fidele | bourbaki/logique/i_3_quantifies/criteres |
| C36 : méta-théorème — si A⊢R dans T'=T+A et x non const | critere | E I.36 | non_applicable | non_verifiable |  |
| C37 : méta-théorème — si A, non R ⊢ contradiction dans  | critere | E I.37 | non_applicable | non_verifiable |  |
| C38 : ¬(∀_A x)R ⇔ (∃_A x)(¬R)  (négation du universel t | critere | E I.37 | partiel | ecart_mineur | bourbaki/logique/i_3_quantifies/criteres |
| C39 : A⇒(R⇒S) théorème ⟹ (∃_A x)R⇒(∃_A x)S et (∀_A x)R⇒ | critere | E I.37 | manquant | non_verifiable |  |
| C40 : (∀_A x)(R et S) ⇔ ((∀_A x)R et (∀_A x)S) et (∃_A  | critere | E I.37 | manquant | non_verifiable |  |
| C41 : (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S) et (∃_A x)(R et | critere | E I.37 | manquant | non_verifiable |  |
| C42 : (∀_A x)(∀_B y)R ⇔ (∀_B y)(∀_A x)R et (∃_A x)(∃_B  | critere | E I.37 | manquant | non_verifiable |  |

### I.5 Théories égalitaires
_pages : p-038, p-039, p-040, p-041 (pages physiques 38–41 du PDF, en-têtes E I.38–E I.41_  (15 notions, 0 manquantes)

> La section §I.5 couvre les deux axiomes S6/S7, la définition de théorie égalitaire, la notation T≠U, le critère C43 (Leibniz pour relations), les trois théorèmes de base (réflexivité, symétrie, transitivité), le critère C44 (substitutivité pour termes), puis les notions de relation univoque (C45), fonctionnelle (C46) et symbole fonctionnel. Les points forts du code : S6 et S7 sont des primitives noyau complètes et fidèles ; Th1/Th2/Th3 et C44 sont clos dans i_4_egalitaires. Les lacunes : C43 est absent de i_4_egalitaires (mentionné seulement dans des commentaires du contexte §I.4) ; C45 (univoque) est entièrement absent ; la notion de théorie égalitaire n'est pas formalisée comme définition nommée ; équation/solution sont des notions méta non formalisées ; C46 (fonctionnelle) est formalisé mais uniquement dans le registre ensembles (§II.3), pas dans §I.5 logique.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition : théorie égalitaire | definition | E I.38 | manquant | non_verifiable |  |
| Notation T=U et T≠U (relation d'égalité) | notation | E I.38 | partiel | fidele | bourbaki/assemblage/assemblage.py:egalit |
| Axiome S6 | axiome | E I.38 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| Axiome S7 | axiome | E I.38 | clos | fidele | bourbaki/logique/i_2_criteres_C/noyau/no |
| Critère C43 — (T=U et R{T}) équivalent (T=U et R{U}) | critere | E I.39 | manquant | non_verifiable |  |
| Théorème 1 — x = x (réflexivité de l'égalité) | theoreme | E I.39 | clos | fidele | bourbaki/logique/i_4_egalitaires/tactiqu |
| Théorème 2 — (x=y) ⇔ (y=x) (symétrie) | theoreme | E I.39 | clos | fidele | bourbaki/logique/i_4_egalitaires/tactiqu |
| Théorème 3 — ((x=y) et (y=z)) ⇒ (x=z) (transitivité) | theoreme | E I.40 | clos | fidele | bourbaki/logique/i_4_egalitaires/tactiqu |
| Critère C44 — (T=U) ⇒ (V{T} = V{U}) (substitutivité de  | critere | E I.40 | clos | fidele | bourbaki/logique/i_4_egalitaires/tactiqu |
| Notion : équation (T=U), solution en x, solution complè | definition | E I.40 | manquant | non_verifiable |  |
| Définition : relation univoque en x (au plus un x vérif | definition | E I.40 | manquant | non_verifiable |  |
| Critère C45 — R univoque en x dans T ⟺ R ⇒ (x = τx(R)) | critere | E I.41 | manquant | non_verifiable |  |
| Définition : relation fonctionnelle en x (∃x.R et univo | definition | E I.41 | manquant | non_verifiable |  |
| Critère C46 — R fonctionnelle en x ⟺ R ⇔ (x = τx(R)) | critere | E I.41 | partiel | ecart_mineur | bourbaki/ensembles/fonctions/ii_3_4_fonc |
| Définition : symbole fonctionnel Σ (abréviation pour τx | notation | E I.41 | non_applicable | non_verifiable | bourbaki/assemblage/assemblage.py:tau_x  |

### I.Appendice — Caractérisation des termes et des relations
_pages : 42–48 (physiques) = E I.42–E I.48_  (15 notions, 0 manquantes)

> L'Appendice développe une métamathématique des mots sur un alphabet muni de poids : il construit le monoïde libre L₀(S), définit les suites significatives et les mots équilibrés, prouve leur équivalence (Prop. 2 = unicité de lecture à la Łukasiewicz), puis applique ce résultat aux assemblages de la théorie T pour obtenir deux critères algorithmiques (Critère 1 et Critère 2) permettant de reconnaître termes et relations. Dans V9, l'essentiel de ce programme est réalisé FONCTIONNELLEMENT par le module `lecture.py` (parseur récursif descendant, prédicats est_terme/est_relation/est_significatif, round-trip vers_assemblage). Aucun objet `Theoreme` LCF nommé ne correspond aux propositions, lemmes ou corollaires de l'Appendice : la mécanique est incorporée dans le parseur lui-même plutôt que certifiée par le noyau. Les notions purement métamathématiques (monoïde libre, poids, longueur, suite significative, mots équilibrés en tant que schéma général, Lemmes 1-2, Critère 1) sont subsumées structurellement : les former comme des Theoreme séparés n'aurait pas de sens dans le cadre LCF maison. Critère 2 est présent comme prédicat vérifié mais pas comme Theoreme clos.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Monoïde libre L₀(S) sur un ensemble de signes S — mots, | definition | E I.42–43 | non_applicable | non_verifiable | bourbaki/assemblage/assemblage.py:Assemb |
| Segment d'un mot (propre, initial, final) ; segments di | definition | E I.43 | non_applicable | non_verifiable |  |
| Suite significative — propriété inductive sur une suite | definition | E I.43 | non_applicable | non_verifiable |  |
| Mot significatif — mot figurant dans une suite signific | definition | E I.43 | partiel | ecart_mineur | bourbaki/logique/i_1_termes_relations/le |
| Proposition 1 — si A₁,…,Aₚ sont p mots significatifs et | proposition | E I.43 | non_applicable | non_verifiable |  |
| Mot équilibré — l(A)=n(A)+1 et tout segment initial pro | definition | E I.43 | non_applicable | non_verifiable |  |
| Proposition 2 — un mot est significatif si et seulement | proposition | E I.43–44 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/le |
| Lemme 1 — mot équilibré A, 0≤k<l(A) : ∃! segment équili | proposition | E I.44 | non_applicable | non_verifiable |  |
| Lemme 2 — tout mot équilibré A s'écrit fA₁…Aₚ de façon  | proposition | E I.44 | non_applicable | non_verifiable |  |
| Corollaire 1 — mot significatif A, 0≤k<l(A) : ∃! segmen | corollaire | E I.44 | non_applicable | non_verifiable |  |
| Corollaire 2 — tout mot significatif A se met d'une man | corollaire | E I.45 | non_applicable | non_verifiable | bourbaki/logique/i_1_termes_relations/le |
| Assemblage équilibré d'une théorie T — assemblage dont  | definition | E I.45 | non_applicable | non_verifiable |  |
| Critère 1 — si A est un terme ou une relation de T, alo | critere | E I.45 | non_applicable | non_verifiable |  |
| Critère 2 — conditions nécessaires et suffisantes (en t | critere | E I.45–46 | partiel | ecart_mineur | bourbaki/logique/i_1_termes_relations/le |
| Remarque — absence de procédé général pour décider si u | remarque | E I.46 | non_applicable | non_verifiable |  |
