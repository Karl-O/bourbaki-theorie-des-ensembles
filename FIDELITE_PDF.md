# Audit de FIDÉLITÉ au PDF Bourbaki — Résumé des résultats (2026-06-24)

Comparaison notion-par-notion : texte du livre (Résumé des résultats, PDF) ↔ formalisation V9.
⚠ Source = Résumé (énoncés condensés, SANS preuves, OMET le Chap. I) ; à compléter par le texte principal.

## Synthèse globale (128 notions auditées)

**Fidélité** : fidèle 65 · écart mineur 28 · **écart majeur 4** · non vérifiable 31

**Statut code** : clos 56 · partiel 42 · **manquant 24** · n/a 6

## ⚠ Écarts MAJEURS (énoncé formalisé ≠ Bourbaki) — à corriger en priorité

- **§2 FONCTIONS — Résumé des résultats (E.R** — n°7 — (14) f⁻¹(X∩Y)=f⁻¹(X)∩f⁻¹(Y) et (15) f⁻¹(∁X)=∁f⁻¹(X) (E.R.8 n°7 b) formules (14)(15)) : ÉCART MAJEUR de portée : dans le Résumé (E.R.8 n°7), f est UNE APPLICATION et (14)/(15) sont INCONDITIONNELLES (Bourbaki note explicitement que (14) « ne serait pas vraie » pour une extension réciproque QUELCONQUE). Le code formalise image_reciproque_inter_binaire (14) et image_reciproque_difference (15, sous forme différence B∖Y) avec l'HYPOTHÈSE est_fonctionnel(f) en prémisse (ensembles_image_algebre_binaire_ii4.py:160,327). Or pour f⁻¹ d'une application, fonctionnel(f) EST acquis : l'hypothèse est honnête mais l'énoncé livré reste conditionnel (⇒), donc PARTIEL vs l'énoncé inconditionnel du Résumé. (15) est aussi formulée comme différence binaire et non comme complément ∁X au sens strict du livre.
- **§3 « Produit de plusieurs ensembles » — ** — Item 3d — formule (23) : (X×Y)∩(X'×Y')=(X∩X')×(Y∩Y') (E.R.12 (23) (p.315)) : couple_dans_intersection_produits (ensembles_produit_distributif.py:125) prouve (u,v)∈(A×B)∩(C×D) ⇔ (u,v)∈(A∩C)×(B∩D) — exactement la formule (23) — mais SEULEMENT au niveau APPARTENANCE D'UN COUPLE, PAS l'égalité ensembliste pleine ∀z. Écart MAJEUR de portée explicitement assumé dans le docstring (égalité ensembliste « REPORTÉE », l.17). L'énoncé Bourbaki (23) est une égalité d'ensembles ; le formalisé est l'équivalence d'appartenance d'un couple. Fidèle en contenu mais pas en portée.
- **§II.4-II.5 — Réunion, intersection, prod** — N6/Déf.2 — Intersection ∩_{ι∈J} X_ι = {x : (∀ι)(ι∈J ⇒ x∈X_ι)} (I≠∅) ; formule (4 (E.R.18-19, item 6 + formules (39)(40)) : AXIOME_INTER_FAM (ensembles_abrege.py L985) encode {x:(∀i)(i∈I⇒x∈X_i)} SANS la clause z∈E. ÉCART : le Résumé (E.R.18) restreint Déf.2 à I≠∅ et pose explicitement (40) ∩_∅ X_ι = E (l'ensemble ambiant). Le code, pour I=∅, donne la classe universelle (∀i∈∅ vacuously true), PAS E ; et (40) n'est PAS formalisée. L'écart est explicitement reconnu dans la docstring de ensembles_familles_demorgan.py (« avec l'axiome ⋂ sans la clause z∈E (Déf.2), le sens ⇐ tombe en défaut pour I=∅ ; Déf.3 du livre inclut z∈E »). Pour I≠∅ l'encodage coïncide avec Bourbaki. À remonter : la formalisation s'écarte de la convention ∩_∅=E du Résumé.
- **E.R. §7 — Puissances. Ensembles dénombra** — Item 7 (suite), propriétés des infinis : tout infini a une partition d'infinis d (E.R.33 item 7 (bas)) : E×E≃E (Théorème 2, a²=a) : hessenberg_a_carre_egal_a_inconditionnel (hessenberg/.../recollement_final.py) est CONDITIONNEL — conclut « est_infini(Card E) ⇒ Card E·Card E = Card E » SOUS des hypothèses honnêtes non déchargées (𝔟≤a, Card(S₀×S₀)=Card S₀, hyps géométriques de negation_b_inf_strict_a). ÉCART MAJEUR vs item 7 : l'énoncé Bourbaki est INCONDITIONNEL (a²=a pour tout a infini) alors que le formalisé garde des résidus. N×N≃N (denombrable_carre, iii_6/denombrable) est aussi CONDITIONNEL (résidu ℕ×ℕ≤ℕ, direction dyadique non close). Partition d'infinis, E×N≃E, parties finies≃E : MANQUANTS.

## Notions MANQUANTES (dans le livre, pas dans le code)

### §1 — Éléments et parties d'un ensemble (Fascicule de résultats, E.R.1–E.R.4)
- Item 11 : critère d'égalité x=y ⇔ (∀X)(x∈X ⇒ y∈X) (pour X∈P(E)) (E.R.3, item 11 (p.306)) — Aucun théorème encodant 'x=y ⇔ pour tout X tel que x∈X on a y∈X'. (L'égalité Leibniz du noyau s6/s7 couvre le contenu logique, mais l'énoncé ENSEMBLISTE quantif
- Item 14a : ∅=∁E et E=∁∅ (E.R.4, item 14 a) (p.307)) — Pas de théorème ∅=E∖E ni E=E∖∅. (difference_self A∖A=∅ existe mais paramétrée en A quelconque, pas appliquée/nommée pour ∅=∁E ; E=∁∅ absent.)
- Item 14 b)(1) : ∁(∁X)=X (involution du complémentaire) (E.R.4, item 14 b)(1) (p.307)) — Aucun théorème E∖(E∖X)=X (involution). Grep 'involut'/'complement' : absent de ii_1_axiomes_algebre.
- Item 14 b)(3) : X∪(∁X)=E et X∩(∁X)=∅ (complément) (E.R.4, item 14 b)(3) (p.307)) — Aucun théorème X∪(E∖X)=E ni X∩(E∖X)=∅. Absent (ces deux lois fondamentales du complément ne sont pas formalisées).
- Item 14 e) : équivalence X∩Y=∅, X⊂∁Y, Y⊂∁X (disjonction) (E.R.4, item 14 e) (p.307)) — Aucun théorème reliant X∩Y=∅ à X⊂E∖Y ou Y⊂E∖X. Absent.
- Item 14 f) : équivalence X∪Y=E, ∁X⊂Y, ∁Y⊂X (recouvrement) (E.R.4, item 14 f) (p.307)) — Aucun théorème reliant X∪Y=E à E∖X⊂Y ou E∖Y⊂X. Absent (fait intervenir l'ambiant E).

### §2 FONCTIONS — Résumé des résultats (E.R.6 à E.R.10), Théorie des ensembles, Bourbaki
- n°9 — Permutation de E (bijection E→E) ; application involutive (g=g⁻¹) ; correspondance b (E.R.9 n°9) — Aucun prédicat dédié « permutation », « involutive » ou « correspondance biunivoque » trouvé dans bourbaki/ensembles/fonctions (grep négatif). Notions présentes
- n°10 — (17) f⁻¹(Y)=f⁻¹(Y∩f(E)), (18) X⊂f⁻¹(f(X)), (19) f(f⁻¹(Y))⊂Y ; b/c/d caractérisation (E.R.9 n°10 formules (17)(18)(19)) — Aucun énoncé dédié trouvé pour (17) f⁻¹(Y)=f⁻¹(Y∩f(E)), (18) X⊂f⁻¹(f(X)), (19) f(f⁻¹(Y))⊂Y, ni pour les caractérisations b) f(f⁻¹(Y))=Y⇔surjective, c) f⁻¹(f(X))

### §3 « Produit de plusieurs ensembles » — Résumé des résultats (E.R.11 à E.R.15, items 1-12)
- Item 3c — formule (22) : (X×Y)∪(X'×Y)=(X∪X')×Y (E.R.12 (22) (p.315)) — Cette égalité précise (réunion sur le 1er facteur, facteur Y commun) N'EST PAS formalisée. Le module distributif couvre A×(B∪C)=(A×B)∪(A×C) (réunion sur le 2e f
- Item 3e — formule (24) : pr₁⁻¹(X)=X×F, pr₂⁻¹(Y)=E×Y (E.R.12 (24) (p.315)) — Images réciproques des projections par X (resp Y) ; non formalisées dans la zone II.2 (exigent pr⁻¹ comme correspondance, II.3). Absent.
- Item 3f — formule (25) : si Y≠∅, pr₁(X×Y)=X (E.R.12 (25) (p.315)) — Image directe d'un produit par pr₁ ; non formalisée (le code a produit_projections : z∈A×B ⇒ pr₁z∈A et pr₂z∈B, ensembles_produit.py:118, mais pas l'égalité d'im
- Item 3g — formule (26) : Z⊂pr₁(Z)×pr₂(Z) (E.R.12 (26) (p.315)) — Non formalisée. Absent dans la zone produit.
- Item 3h — application (a,y)↦y de {a}×F sur F (restriction de pr₂) est bijective (E.R.12 item 3h (p.315)) — Bijection {a}×F → F non formalisée (notion d'application bijective sur une coupe ; relève de II.3). Absent.
- Item 4 — application canonique (x,y)↦(y,x) bijective de E×F sur F×E ; symétrie canonique ( (E.R.12-13 item 4 (p.315-316)) — L'application canonique d'échange (x,y)↦(y,x) et la symétrie canonique involutive NE SONT PAS formalisées (grep : aucun swap/échange de couple). La diagonale Δ 
- Item 12 — produit de trois ensembles E×F×G : triplets (x,y,z) ; (x,y,z)=(x',y',z') ⇔ x=x'  (E.R.15 item 12 (p.318)) — Le produit de TROIS ensembles, les triplets, leurs projections et les bijections canoniques associatives N'EXISTENT PAS dans le code (grep produit_trois/triplet

### §5 — Relations d'équivalence ; ensemble quotient (Résumé des résultats, E.R.22-24, items 1-7)
- Item 2 — La relation d'égalité x=y est une relation d'équivalence ; l'application canoniqu (E.R.23 item 2 (fin)) — Cas particulier 'égalité = équivalence' et 'p:E→E/(=) , x↦{x} bijective' non trouvés dans ii_6_equivalence (aucun lemme dédié à R{x,y}:=x=y comme équivalence ni
- Item 3 — Dans E×F, 'pr₁(z)=pr₁(z')' est une relation d'équivalence et (E×F)/R se met en co (E.R.23 item 3) — Aucune formalisation de la relation 'pr₁(z)=pr₁(z')' sur E×F ni de la bijection (E×F)/R ↔ E (grep pr1/pr_1/produit×quotient ne renvoie que le produit de relatio

### §6 « Ensembles ordonnés » — Résumé des résultats (E.R.25–E.R.31), items 1–14
- Item 7 — Application majorée/minorée/bornée ; borne supérieure d'une application sup_{x∈A} (E.R.28 (item 7, p.331)) — Aucun prédicat « f majorée/minorée/bornée » ni « borne supérieure de f (= sup de f(A)) » n'est formalisé dans bourbaki/ordre. Notion absente du code (cf. grep a
- Item 12 — Famille croissante/décroissante (X_ι)_{ι∈I} de parties : ι↦X_ι croissante de I d (E.R.29 (item 12, p.332)) — La notion de FAMILLE de parties croissante/décroissante (application I→𝔓(E) monotone pour ⊂) n'est pas formalisée comme prédicat dédié. Notion absente.

### E.R. §7 — Puissances. Ensembles dénombrables (Résumé des résultats, items 1-8)
- Item 1, propriété : « Si E et F sont équipotents, P(E) et P(F) sont équipotents » ; et sta (E.R.32 item 1) — Pas de théorème « Eq(E,F) ⇒ Eq(P(E),P(F)) » ni « Eq composante à composante ⇒ Eq des produits » trouvé (grep parties/produit equipotence). Le produit binaire E×
- Item 3 (E.R.33 haut), propriété : « l'ensemble des puissances des parties d'un ensemble E  (E.R.33 (suite item 3)) — Pas de théorème « l'ensemble des puissances/cardinaux ≤Card(P(E)) est bien ordonné ». CLAUDE.md liste « bon ordre des cardinaux (III.3) » comme gros chantier ou
- Item 6, propriété : « N (entiers positifs) = ensemble des puissances des parties finies d' (E.R.33 item 6) — N est codé NN=app('N') comme TERME OPAQUE (ensembles_infinis.py) ; sa caractérisation « ensemble des puissances des parties finies d'un infini » N'est PAS forma

### §8 « Échelles d'ensembles et structures » (Résumé des résultats, E.R.34–37) — audit de fidélité contre la formalisation V9 (bourbaki/structures, IV.1–IV.3)
- §8.2 — Exemple : structure d'ensemble ordonné = élément C de 𝔓(E×E) tel que a) C∘C⊂C et b) (E.R.35, §8 item 2 (exemple)) — L'instance concrète « espèce ensemble ordonné » avec axiomes C∘C⊂C et C∩C̄⁻¹=Δ n'est PAS construite comme un objet Espece dans bourbaki/structures (la machineri
- §8.6 — Axiomes contradictoires : un système d'axiomes définissant T est contradictoire si  (E.R.37, §8 item 6 (= IV.1.4 fin)) — Aucun prédicat « espèce contradictoire / T=∅ » dans bourbaki/structures. Notion simple (vacuité de l'espèce) non encore introduite. Pas d'écart d'énoncé à signa

## Détail complet par section

### §1 — Éléments et parties d'un ensemble (Fascicule de résultats, E.R.1–E.R.4)
_pages lues : PDF physiques 304-307 (E.R.1 à E.R.4 / §1.13) rendus en PNG (outils_ia/pdf_pages/aud_s1-304..307.png) et lus intégralement_

> Les DÉFINITIONS de la section (inclusion item 12, complémentaire/différence item 7, vide ∅ item 8, singleton item 9, ensemble des parties P(E) item 10, réunion/intersection item 13) sont toutes formalisées et CLOSES, et FIDÈLES à Bourbaki : en particulier inclus := (∀z)(z∈t⇒z∈u) est verbatim, et les axiomes de membership (AXIOME_DIFF/VIDE/PARTIES/REUNION/INTER) reproduisent exactement les caractérisations du livre. Aucun écart MAJEUR (énoncé formalisé contredisant le livre) n'a été détecté ; le seul écart de présentation est l'absence de terme UNAIRE ∁X (le code rend l'ambiant E explicite via difference(E,X), même contenu — écart mineur). Les TROUS de couverture portent sur l'item 11 (critère d'égalité via les parties) et plusieurs identités de l'item 14 qui font intervenir un univers/ambiant E fixe (14a ∅=∁E, 14b1 involution ∁(∁X)=X, 14b3 X∪∁X=E / X∩∁X=∅, 14d maillon ∁X⊃∁Y, 14e, 14f, et X∩E=X / X∪E=E) — non formalisées, l'algèbre booléenne présente couvrant en revanche commutativité, associativité, idempotence, absorption, distributivité, De Morgan et les ∅-identités, toutes closes et fidèles.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| Item 1-2 : un ensemble est formé d'éléments ; ensembles/éléments désig | E.R.2, items 1-2 (p.304-305) | non_applicable | non_verifiable |
| Item 3-5 : identité, R entraîne S, R et S équivalentes ; quantificateu | E.R.2, items 3-5 (p.305) | formalise_clos | fidele |
| Item 6 : relation d'égalité x=y (mêmes symboles) et négation x≠y | E.R.3, item 6 (p.306) | formalise_clos | fidele |
| Item 7 : DÉFINITION de partie/sous-ensemble (éléments possédant une pr | E.R.3, item 7 (p.306) | formalise_clos | ecart_mineur |
| Item 8 : DÉFINITION de la partie vide ∅ (propriété fausse pour aucun é | E.R.3, item 8 (p.306) | formalise_clos | fidele |
| Item 9 : DÉFINITION de la partie réduite à un seul élément {a} (propri | E.R.3, item 9 (p.306) | formalise_clos | fidele |
| Item 10 : DÉFINITION de l'ensemble des parties P(E) (éléments = partie | E.R.3, item 10 (p.306) | formalise_clos | fidele |
| Item 11 : critère d'égalité x=y ⇔ (∀X)(x∈X ⇒ y∈X) (pour X∈P(E)) | E.R.3, item 11 (p.306) | manquant | non_verifiable |
| Item 12 : DÉFINITION de l'inclusion X⊂Y (x∈X entraîne x∈Y) ; ∅⊂X, X⊂E  | E.R.3, item 12 (p.306) | formalise_clos | fidele |
| Item 13 : DÉFINITION réunion X∪Y (x∈X ou x∈Y) et intersection X∩Y (x∈X | E.R.4, item 13 (p.307) | formalise_clos | fidele |
| Item 14a : ∅=∁E et E=∁∅ | E.R.4, item 14 a) (p.307) | manquant | non_verifiable |
| Item 14 b)(1) : ∁(∁X)=X (involution du complémentaire) | E.R.4, item 14 b)(1) (p.307) | manquant | non_verifiable |
| Item 14 b)(2) : X∪X=X et X∩X=X (idempotence) | E.R.4, item 14 b)(2) (p.307) | formalise_clos | fidele |
| Item 14 b)(3) : X∪(∁X)=E et X∩(∁X)=∅ (complément) | E.R.4, item 14 b)(3) (p.307) | manquant | non_verifiable |
| Item 14 b)(4)-(5) : X∪∅=X, X∩E=X, X∪E=E, X∩∅=∅ | E.R.4, item 14 b)(4)-(5) (p.307) | formalise_partiel | fidele |
| Item 14 c)(6) : commutativité X∪Y=Y∪X, X∩Y=Y∩X | E.R.4, item 14 c)(6) (p.307) | formalise_clos | fidele |
| Item 14 c)(7) : X⊂X∪Y et X∩Y⊂X | E.R.4, item 14 c)(7) (p.307) | formalise_clos | fidele |
| Item 14 c)(8) : De Morgan ∁(X∪Y)=(∁X)∩(∁Y), ∁(X∩Y)=(∁X)∪(∁Y) | E.R.4, item 14 c)(8) (p.307) | formalise_clos | fidele |
| Item 14 d) : équivalence des relations X⊂Y, ∁X⊃∁Y, X∪Y=Y, X∩Y=X | E.R.4, item 14 d) (p.307) | formalise_partiel | fidele |
| Item 14 e) : équivalence X∩Y=∅, X⊂∁Y, Y⊂∁X (disjonction) | E.R.4, item 14 e) (p.307) | manquant | non_verifiable |
| Item 14 f) : équivalence X∪Y=E, ∁X⊂Y, ∁Y⊂X (recouvrement) | E.R.4, item 14 f) (p.307) | manquant | non_verifiable |

### §2 FONCTIONS — Résumé des résultats (E.R.6 à E.R.10), Théorie des ensembles, Bourbaki
_pages lues : PDF physiques 308-313 (= E.R.5 fin §1 / E.R.6 à E.R.10) rendus en PNG (outils_ia/pdf_pages/aud_s2-308..313.png) et lus intégralement ; notions numérotées 1 à 12 de la section « Fonctions »._

> La section « Fonctions » du Résumé (notions 1 à 12) est bien couverte pour les DÉFINITIONS de base (fonction/application, valeur, 𝓕(E;F), identité, image directe/réciproque, surjection/injection/bijection, composée, rétraction/section) qui sont fidèles au livre, et pour les formules-clés inconditionnelles (11) f(X∪Y), (13) f⁻¹(X∪Y), (20)/(21), Prop. 2 et Prop. 6/7, toutes CLOSES. Deux écarts notables à remonter : (1) ÉCART MAJEUR de portée pour les formules (14) f⁻¹(X∩Y) et (15) f⁻¹(∁X) — le Résumé les donne INCONDITIONNELLES pour une application, le code les livre sous prémisse est_fonctionnel(f) (honnête mais conditionnelle), et (15) est codée comme différence binaire B∖Y et non comme complément strict ; (2) plusieurs notions/énoncés du Résumé sont MANQUANTS : permutation/involution/correspondance biunivoque (n°9), les formules (17)(18)(19) et les caractérisations b/c/d (n°10), les itérées f^n (n°11), et le volet section f∘f⁻¹=Id_F (n°12, explicitement reporté). Écarts mineurs de présentation sur constante (n°3) et injection (n°8, déf. par caractérisation f(u)=f(u')⇒u=u' au lieu de « f⁻¹({y}) vide ou singleton »).

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| n°1 — Fonction / application : relation fonctionnelle en y, valeur f(x | E.R.6 n°1 | formalise_clos | fidele |
| n°2 — Ensemble des applications 𝓕(E;F), notation f(x)/f_x, égalité f=g | E.R.6 n°2 | formalise_clos | fidele |
| n°3 — Fonction constante (même valeur a pour tout x), déterminée par y | E.R.6 n°3 | formalise_clos | ecart_mineur |
| Application identique Id_E : x↦x (y=x) ; application canonique de A da | E.R.7 (suite n°3) | formalise_clos | fidele |
| Élément invariant par f (f(x)=x) ; x invariant par un ensemble d'appli | E.R.7 (suite n°3) | formalise_partiel | fidele |
| n°4 — Image directe f⟨X⟩ (ensemble des valeurs prises par f sur X) ; e | E.R.7 n°4 | formalise_clos | fidele |
| n°4 — f(∅)=∅ et f({x})={f(x)} ; surjection (f(E)=F) ; partie stable (f | E.R.7 n°4 | formalise_partiel | fidele |
| n°5 — Propositions image directe : a) X⊂Y ⇒ f(X)⊂f(Y) ; b) X≠∅ ⇔ f(X)≠ | E.R.8 n°5 a) b) | formalise_partiel | fidele |
| n°5 c) — (11) f(X∪Y)=f(X)∪f(Y) et (12) f(X∩Y)⊂f(X)∩f(Y) | E.R.8 n°5 c) formules (11)(12) | formalise_clos | fidele |
| n°6 — Image réciproque f⁻¹⟨Y⟩ (extension réciproque aux ensembles de p | E.R.8 n°6 | formalise_clos | fidele |
| n°7 — Image réciproque : a) X⊂Y ⇒ f⁻¹(X)⊂f⁻¹(Y) ; (13) f⁻¹(X∪Y)=f⁻¹(X) | E.R.8 n°7 a) formule (13) | formalise_clos | fidele |
| n°7 — (14) f⁻¹(X∩Y)=f⁻¹(X)∩f⁻¹(Y) et (15) f⁻¹(∁X)=∁f⁻¹(X) | E.R.8 n°7 b) formules (14)(15) | formalise_partiel | ecart_majeur |
| n°8 — Injection (f⁻¹({y}) vide ou réduit à un élément) ; (16) f(X∩Y)=f | E.R.9 n°8 formule (16) | formalise_clos | ecart_mineur |
| n°9 — Bijection (f⁻¹({y}) réduit à un élément ; = surjective ET inject | E.R.9 n°9 | formalise_clos | fidele |
| n°9 — Permutation de E (bijection E→E) ; application involutive (g=g⁻¹ | E.R.9 n°9 | manquant | non_verifiable |
| n°10 — (17) f⁻¹(Y)=f⁻¹(Y∩f(E)), (18) X⊂f⁻¹(f(X)), (19) f(f⁻¹(Y))⊂Y ; b | E.R.9 n°10 formules (17)(18)(19) | manquant | non_verifiable |
| n°11 — Application composée g∘f (valeur g(f(x))) ; factorisation h=g∘f | E.R.10 n°11 formules (20)(21) | formalise_clos | fidele |
| n°11 — composée de bijections est bijective ; associativité h∘(g∘f)=(h | E.R.10 n°11 | formalise_partiel | fidele |
| n°12 — f⁻¹∘f, f∘f⁻¹ et identités Id_E/Id_F pour f bijective ; réciproq | E.R.10 n°12 | formalise_partiel | ecart_mineur |

### §3 « Produit de plusieurs ensembles » — Résumé des résultats (E.R.11 à E.R.15, items 1-12)
_pages lues : PDF pages physiques 314-318 (E.R.11-15) rendues en PNG (outils_ia/pdf_pages/aud_s3-314..318.png) et lues. Code lu : bourbaki/ensembles/ii_1_axiomes_algebre/ensembles_abrege.py (défs couple/pr1/pr2/produit/est_un_couple/diagonale), ensembles_theoremes.py (sens facile Prop1), ii_2_couples_produit/ensembles_couples.py (Prop1 sens dur), ii_2_couples_produit/ensembles_produit_distributif.py, familles/ii_2_produit_deux_ensembles/ensembles_produit.py, fonctions/hors_ii_3/ii_2_projections/ensembles_projections.py ; tests test_produit.py, test_produit_distributif.py._

> Le cœur binaire de la section (couple {{x},{x,y}}, équivalence (x,y)=(x',y') de la Prop 1, produit E×F, projections pr₁/pr₂ avec pr₁((u,v))=u, Prop 2 monotonie+réciproques sous garde de non-vacuité, Prop 3 X×Y=∅⇔X=∅ ou Y=∅) est formalisé CLOS et FIDÈLE au livre — défs et énoncés coïncident, gardes de non-vacuité correctement reproduites. Deux écarts à remonter : (1) ÉCART MAJEUR DE PORTÉE — les formules ensemblistes (23) et la distributivité (22-type) sont prouvées seulement au niveau « appartenance d'un couple » et non comme égalités d'ensembles ∀z (report explicite, honnête, dans les docstrings) ; (2) TROUS structurels — le produit de TROIS ensembles / triplets et les bijections canoniques (item 12, qui donne son titre à la section), l'application canonique d'échange (x,y)↦(y,x) et l'application diagonale x↦(x,x) (item 4), ainsi que les formules (24)(25)(26) et l'item 3h, ne sont pas formalisés ; le dossier ii_2_5_graphe_produit est d'ailleurs explicitement marqué TODO. Les items 5-11 du Résumé relèvent des correspondances (II.3) et sortent du périmètre produit.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| Item 1 — Ensemble produit E×F : les couples (x,y), x∈E, y∈F, forment u | E.R.11 item 1 (p.314) | formalise_clos | fidele |
| Item 1 (suite) — première coordonnée / première projection pr₁ : appli | E.R.11 item 1 (p.314-315) | formalise_partiel | ecart_mineur |
| Item 1 (suite) — seconde coordonnée / seconde projection pr₂ : applica | E.R.12 item 1 (p.315) | formalise_partiel | ecart_mineur |
| Item 1 (suite) — extension de pr₁/pr₂ aux ensembles de parties (premiè | E.R.12 item 1 (p.315) | non_applicable | non_verifiable |
| Item 2 — Graphe d'une relation R(x,y) : partie de E×F ; réciproquement | E.R.12 item 2 (p.315) | formalise_partiel | ecart_mineur |
| Item 3a — « X×Y=∅ » équivalent à « X=∅ ou Y=∅ » | E.R.12 item 3a (p.315) | formalise_clos | fidele |
| Item 3b — Si X×Y≠∅, « X×Y⊂X'×Y' » équivalent à « X⊂X' et Y⊂Y' » (Propo | E.R.12 item 3b (p.315) | formalise_clos | fidele |
| Item 3c — formule (22) : (X×Y)∪(X'×Y)=(X∪X')×Y | E.R.12 (22) (p.315) | manquant | non_verifiable |
| Item 3d — formule (23) : (X×Y)∩(X'×Y')=(X∩X')×(Y∩Y') | E.R.12 (23) (p.315) | formalise_partiel | ecart_majeur |
| Item 3e — formule (24) : pr₁⁻¹(X)=X×F, pr₂⁻¹(Y)=E×Y | E.R.12 (24) (p.315) | manquant | non_verifiable |
| Item 3f — formule (25) : si Y≠∅, pr₁(X×Y)=X | E.R.12 (25) (p.315) | manquant | non_verifiable |
| Item 3g — formule (26) : Z⊂pr₁(Z)×pr₂(Z) | E.R.12 (26) (p.315) | manquant | non_verifiable |
| Item 3h — application (a,y)↦y de {a}×F sur F (restriction de pr₂) est  | E.R.12 item 3h (p.315) | manquant | non_verifiable |
| Item 4 — application canonique (x,y)↦(y,x) bijective de E×F sur F×E ;  | E.R.12-13 item 4 (p.315-316) | manquant | non_verifiable |
| Items 5-9 — graphe d'une fonction ; ensemble des applications ↔ partie | E.R.13-14 items 5-9 (p.316-317) | non_applicable | non_verifiable |
| Item 10-11 — ensemble composé B∘A de parties de produits ; associativi | E.R.14-15 items 10-11 (p.317-318) | non_applicable | non_verifiable |
| Item 12 — produit de trois ensembles E×F×G : triplets (x,y,z) ; (x,y,z | E.R.15 item 12 (p.318) | manquant | non_verifiable |

### §II.4-II.5 — Réunion, intersection, produit d'une famille (Résumé des résultats, E.R.16-21)
_pages lues : PDF physiques 319-324 (= E.R.16 à E.R.21), rendus en PNG via pdftoppm puis lus image par image. Section « §4. Réunion, intersection, produit d'une famille d'ensembles », items numérotés 1 à 12 + formules (33)-(48)._

> Couverture forte des DÉFINITIONS du §4 : réunion (Déf.1), intersection (Déf.2), produit ∏ (Déf.1), parties P(X), exposant E^I, recouvrement/partition/disjoints/somme (Déf.5-8) sont tous formalisés avec axiomes caractérisants fidèles au Résumé, testés (statut clos). L'ÉCART MAJEUR à remonter concerne l'INTERSECTION sur ensemble d'indices vide : le code (AXIOME_INTER_FAM) encode {x:(∀ι∈J)(x∈X_ι)} sans la clause « x∈E », donc pour J=∅ il donne la classe universelle au lieu de E ; la formule (40) ∩_∅ X_ι = E du Résumé n'est pas formalisée et la Déf.2 du code diffère de la Déf.3 « avec z∈E » de Bourbaki — écart déjà reconnu en commentaire (docstring De Morgan), avec impact sur les lois de De Morgan/dualité restreintes à I≠∅. Écarts de COUVERTURE (non-fidélité, mais énoncés absents) : formules (37)(38)(41)(42)(43)(44) à double famille indexée I×K, l'axiome de choix N10 comme énoncé du §4 (présent seulement via τ et via Zermelo ailleurs), et les formules (47)(48) ∏X_ι=∩pr_ι⁻¹(X_ι) / pr_κ(∏X_ι)=X_κ. Les propositions profondes (assoc, pr_J surjective, monotonie produit) sont formalisées mais CONDITIONNELLES (hypothèses honnêtes ou cas binaire), conformément à la politique du projet.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| N1 — Famille (X_ι)_{ι∈I} de parties de E, ensemble d'indices I quelcon | E.R.16-17, item 1 | formalise_clos | fidele |
| N2/Déf.1 — Réunion ∪_{ι∈J} X_ι = {x : (∃ι)(ι∈J et x∈X_ι)} ; formule (3 | E.R.17, item 2 + formule (33) | formalise_clos | fidele |
| N6/Déf.2 — Intersection ∩_{ι∈J} X_ι = {x : (∀ι)(ι∈J ⇒ x∈X_ι)} (I≠∅) ;  | E.R.18-19, item 6 + formules (39)(40) | formalise_partiel | ecart_majeur |
| N3 — Monotonie de ∪ en l'indice (J⊂I ⇒ ∪_J⊂∪_I) et en la famille (X_ι⊂ | E.R.17, item 3 + formules (34)(35) | formalise_partiel | ecart_mineur |
| N4 — Recouvrement (A⊂∪X_ι), partition (recouvrement + X_ι∩X_κ=∅ pour ι | E.R.18, item 4 + formules (36)(37)(38) | formalise_partiel | ecart_mineur |
| N5/Déf.8 — Somme ∑_{ι∈I} X_ι = ∪_{ι∈I}(X_ι×{ι}) = ∪ X'_ι avec X'_ι={ι} | E.R.18, item 5 | formalise_partiel | ecart_mineur |
| N7 — Règle de dualité : C(∪X_ι)=∩(CX_ι) (39) ; échange ∪↔∩, C, sur fam | E.R.19, item 7 + formule (39) | formalise_partiel | ecart_mineur |
| N8 — Monotonie de ∩ (J⊂I ⇒ ∩_I⊂∩_J ; X_ι⊂Y_ι ⇒ ∩X⊂∩Y) ; formules (41)  | E.R.19-20, item 8 + formules (41)-(46) | formalise_partiel | ecart_mineur |
| N9 — Exponentiation E^I (familles d'éléments de E à indices I, ≅ appli | E.R.20, item 9 | formalise_clos | fidele |
| N10 — Axiome de choix (Zermelo) : équivalence « (∀x)(∃y)R(x,y) ⟺ (∃f a | E.R.20-21, item 10 | formalise_partiel | non_verifiable |
| N11 — Projection pr_J : ∏_I→∏_J (restriction (x_ι)_I↦(x_ι)_J) ; coordo | E.R.21, item 11 | formalise_partiel | ecart_mineur |
| N12 — Propositions sur ∏ de parties (X_ι⊂A_ι) : a) (∏X_ι≠∅) ⇒ (∏X_ι⊂∏Y | E.R.21, item 12 + formules (47)(48) | formalise_partiel | ecart_mineur |

### §5 — Relations d'équivalence ; ensemble quotient (Résumé des résultats, E.R.22-24, items 1-7)
_pages lues : PDF physiques 325-327 (= E.R.22, E.R.23, E.R.24) rendues en PNG (outils_ia/pdf_pages/aud_s5-325..327.png) et lues. Couvre l'item 1 (bas de E.R.22) à l'item 7 (E.R.24) ; l'item 8 amorcé en bas de E.R.24 hors périmètre._

> La section 5 du Résumé est couverte de façon SOLIDE sur les DÉFINITIONS (équivalence sym/trans, réflexivité dans E, classe, quotient, application canonique, R_f, R_A, saturée/saturé, compatibilité, relation quotient P') — toutes fidèles au PDF, dans ii_6_equivalence (ensembles_abrege.py + modules), avec 100/100 tests verts. Les THÉORÈMES nommés sont surtout 'clos modulo hypothèses honnêtes' : item 4 (R⇔Cl égales) pleinement clos, item 1 (graphe→sym/trans), item 6 (p⁻¹⟨B⟩ saturée), item 7 (C56) clos mod. hyp. Aucun ÉCART MAJEUR détecté (pas d'énoncé formalisé contredisant Bourbaki). Les écarts sont des MANQUES de couverture : item 1a (Δ⊂C⇔réflexivité) et C∘C=C absents ; item 2 'égalité=équivalence/x↦{x} bijective' et l'énoncé global '𝔉 partition' non assemblés ; item 3 (E×F)/R↔E et la bijection f(E)↔E/R absents (décomposition canonique définie mais factorisation effective de graphes reportée) ; item 5 correspondance f(A)↔A/R_A absente ; item 7 limité à P{x} mono-argument (vs P{x,y,z} multi-argument du Résumé). Risque #1 (énoncé infidèle) : NÉANT ; le point de vigilance est la modélisation de la 'réflexivité' de l'item 1 par est_reflexive_dans (texte principal E.II) plutôt que par le 'R{x,x} identité' du Résumé — écart de présentation, même contenu.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| Item 1 (déf. relation R d'une partition + propriétés a) réflexivité 'R | E.R.22 item 1 | formalise_partiel | ecart_mineur |
| Item 1 — équivalences avec conditions sur le graphe C : a') Δ⊂C, b') C | E.R.22 item 1 (fin) / E.R.23 haut | formalise_partiel | fidele |
| Item 2 — réciproque : R réflexive/symétrique/transitive ⇒ l'image 𝔉 de | E.R.23 item 2 | formalise_partiel | ecart_mineur |
| Item 2 — Définitions : relation d'équivalence dans E, ensemble quotien | E.R.23 item 2 | formalise_clos | fidele |
| Item 2 — La relation d'égalité x=y est une relation d'équivalence ; l' | E.R.23 item 2 (fin) | manquant | non_verifiable |
| Item 3 — Dans E×F, 'pr₁(z)=pr₁(z')' est une relation d'équivalence et  | E.R.23 item 3 | manquant | non_verifiable |
| Item 3 — f:E→F, 'f(x)=f(y)' est une relation d'équivalence R ; z↦f⁻¹(z | E.R.23 item 3 | formalise_partiel | fidele |
| Item 3 — Décomposition (factorisation) canonique de f : f = injection  | E.R.23 item 3 (fin) | formalise_partiel | fidele |
| Item 4 — Toute relation d'équivalence R dans E est définissable via un | E.R.24 item 4 | formalise_clos | ecart_mineur |
| Item 5 — Relation induite R_A par R sur une partie A ; correspondance  | E.R.24 item 5 | formalise_partiel | fidele |
| Item 6 — Partie A saturée pour R ; le saturé de A est Ã = f⁻¹(f(A)) (p | E.R.24 item 6 | formalise_partiel | fidele |
| Item 7 — Relation P{x,y,z} compatible (en x) avec R ; relation P' dédu | E.R.24 item 7 | formalise_partiel | ecart_mineur |

### §6 « Ensembles ordonnés » — Résumé des résultats (E.R.25–E.R.31), items 1–14
_pages lues : PDF physiques 328-334 rendus en PNG (outils_ia/pdf_pages/aud_s6-328..334.png) et lus un à un. Cœur du §6 (items 1-12) sur E.R.25–29 (p.328-332) ; items 13-14 (limites inductives/projectives) sur E.R.29-31 (p.332-334) relèvent de III.7 et sont signalés non_applicable à cette section._

> Couverture EXCELLENTE des DÉFINITIONS du §6 : quasiment toutes les notions du Résumé (relation d'ordre/préordre, ordre induit/opposé, total, intervalles, plus grand-petit, maximal-minimal, majorant-minorant, borne sup-inf, cofinal-coinitial, filtrant, réticulé, croissante-décroissante, inductif) sont formalisées fidèlement, principalement dans ensembles_abrege.py (R=fonction Python) et ensembles_ordre_relation.py (graphe G), avec de nombreux théorèmes directs clos (unicité plus grand élt/borne sup, plus grand⇒maximal⇒majorant⇒borne sup, ordre induit, total partie, Zorn inconditionnel). Deux ÉCARTS MINEURS notables : (1) est_reticule (item 8) encode « toute PAIRE {x,y} a sup/inf » au lieu de « toute partie FINIE non vide » de Bourbaki (équivalent par récurrence, présentation différente) ; (2) zorn_theoreme (item 10) ajoute l'hypothèse E≠∅ que Bourbaki n'écrit pas (justifié : inductif force E≠∅ via ∅ totalement ordonnée). MANQUES : les notions « application majorée/minorée/bornée » et « borne supérieure d'une application sup_{x∈A} f(x) » (fin item 7), ainsi que le prédicat ensembliste « partie majorée/minorée/bornée », ne sont PAS formalisés comme prédicats nommés (seuls majorant/minorant le sont). Aucun ÉCART MAJEUR de fidélité détecté sur les énoncés formalisés.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| Item 1 — Relation d'ordre : ω{x,y} ordre ssi (a) transitive et (b) (ω{ | E.R.25-26 (item 1, p.328-329) | formalise_clos | fidele |
| Item 1 — Ensemble ordonné / structure d'ordre ; relations d'ordre oppo | E.R.26 (item 1, p.329) | formalise_clos | fidele |
| Item 1 — Relation de préordre (réflexive+transitive), ensemble préordo | E.R.26 (item 1, p.329) | formalise_partiel | ecart_mineur |
| Item 2 — Exemples d'ordres : inclusion ⊂ sur 𝔓(E) ; ordre « g prolonge | E.R.26 (item 2, p.329) | formalise_partiel | fidele |
| Item 3 — Notations x≤y, y≥x ; relations strictes x<y, x>y := (x≤y et x | E.R.26 (item 3, p.329) | formalise_partiel | fidele |
| Item 4 — Partie totalement ordonnée : (∀x,y∈X) x≤y ou y≤x ; toute part | E.R.26-27 (item 4, p.329-330) | formalise_clos | fidele |
| Item 4 — Intervalles : fermé [a,b], semi-ouverts [a,b[ et ]a,b], ouver | E.R.27 (item 4, p.330) | formalise_clos | fidele |
| Item 5 — Plus petit élément (a∈X, ∀x∈X a≤x) et plus grand élément (b∈X | E.R.27 (item 5, p.330) | formalise_clos | fidele |
| Item 5 — Ensemble bien ordonné : toute partie non vide admet un plus p | E.R.27 (item 5, p.330) | formalise_clos | fidele |
| Item 6 — Élément minimal (aucun z<x dans X) / maximal (aucun z>x) ; si | E.R.28 (item 6, p.331) | formalise_clos | fidele |
| Item 7 — Majorant (x majore X : ∀z∈X z≤x) / minorant ; ensemble des ma | E.R.28 (item 7, p.331) | formalise_partiel | fidele |
| Item 7 — Borne supérieure (plus petit majorant) / borne inférieure (pl | E.R.28 (item 7, p.331) | formalise_clos | fidele |
| Item 7 — Application majorée/minorée/bornée ; borne supérieure d'une a | E.R.28 (item 7, p.331) | manquant | non_verifiable |
| Item 8 — Ensemble filtrant à droite/gauche : toute partie finie non vi | E.R.28 (item 8, p.331) | formalise_clos | ecart_mineur |
| Item 8 — Ensemble réticulé / réseau ordonné / lattis : toute partie fi | E.R.28 (item 8, p.331) | formalise_partiel | ecart_mineur |
| Item 9 — Ensemble inductif : toute partie totalement ordonnée possède  | E.R.28-29 (item 9, p.331-332) | formalise_clos | fidele |
| Item 10 — Théorème de Zorn : tout ensemble ordonné inductif possède au | E.R.29 (item 10, p.332) | formalise_clos | ecart_mineur |
| Item 11 — Application de Zorn à 𝔓(E) ; ensemble de parties de caractèr | E.R.29 (item 11, p.332) | formalise_partiel | fidele |
| Item 12 — Application croissante/décroissante (x≤y ⇒ f(x)≤f(y) / ≥) ;  | E.R.29 (item 12, p.332) | formalise_clos | fidele |
| Item 12 — Famille croissante/décroissante (X_ι)_{ι∈I} de parties : ι↦X | E.R.29 (item 12, p.332) | manquant | non_verifiable |
| Items 13-14 — Limite inductive / système inductif d'ensembles et d'app | E.R.29-31 (items 13-14, p.332-334) | non_applicable | non_verifiable |

### E.R. §7 — Puissances. Ensembles dénombrables (Résumé des résultats, items 1-8)
_pages lues : PDF physiques 335-336 (E.R.32 et E.R.33), rendus en PNG via pdftoppm puis lus (outils_ia/pdf_pages/aud_s7-335.png, aud_s7-336.png)_

> Couverture solide des DÉFINITIONS de §7 (équipotence, cardinal, ordre ≤, dénombrable, suite — toutes formalisées, plusieurs verbatim) et des deux théorèmes-phares CLOS et FIDÈLES : Cantor (X<P(X), item 4) et Cantor-Bernstein (antisymétrie de ≤, item 3). L'écart MAJEUR à remonter est l'item 7 « E×E équipotent à E » : le Théorème 2 de Hessenberg (a²=a) n'est formalisé que CONDITIONNELLEMENT (résidus honnêtes non déchargés : 𝔟≤a, carré maximal, hyps géométriques), de même que N×N≃N (denombrable_carre garde le résidu ℕ×ℕ≤ℕ) — l'énoncé Bourbaki, lui, est inconditionnel. Écarts mineurs récurrents : N reste un terme OPAQUE (item 6 « N = puissances des parties finies » manquant, Théorème 1 reporté) et les propriétés de l'item 7 (partition d'infinis, E×N≃E, parties finies≃E, infini⇒puissance>N) sont absentes ou reportées ; le transport P(E)≃P(F) (item 1) et le bon ordre des puissances via Zorn (item 3, E.R.33) sont manquants. Incohérence documentaire mineure : ordre_cardinaux/ensembles_cardinaux_ordre.py déclare Cantor-Bernstein « REPORTÉ » alors qu'il est clos dans ensembles_cantor_bernstein_final.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| Item 1, Déf. équipotents : « Deux ensembles E, F sont dits équipotents | E.R.32 item 1 | formalise_clos | ecart_mineur |
| Item 1, propriété : « Deux ensembles équipotents à un même troisième s | E.R.32 item 1 | formalise_clos | fidele |
| Item 1, propriété : « Si E et F sont équipotents, P(E) et P(F) sont éq | E.R.32 item 1 | manquant | non_verifiable |
| Item 2, Déf. puissance / cardinal : « la relation X et Y équipotents e | E.R.32 item 2 + note¹ | formalise_partiel | ecart_mineur |
| Item 3, Déf. ordre des puissances : « a inférieure à b s'il existe une | E.R.32 item 3 | formalise_clos | ecart_mineur |
| Item 3, propriété (Cantor-Bernstein) : « si a est à la fois supérieure | E.R.32 item 3 | formalise_clos | fidele |
| Item 3 (E.R.33 haut), propriété : « l'ensemble des puissances des part | E.R.33 (suite item 3) | manquant | non_verifiable |
| Item 4, théorème de Cantor : « La puissance d'un ensemble E est strict | E.R.33 item 4 | formalise_clos | fidele |
| Item 4 (2e §), propriété : « la puissance de l'image f(X) d'une partie | E.R.33 item 4 | formalise_partiel | ecart_mineur |
| Item 5, propriété : familles (X_ι) disjointes, (Y_ι), Card(Y_ι)≤Card(X | E.R.33 item 5 | formalise_partiel | ecart_mineur |
| Item 5 (suite), propriété : familles X_ι, Y_ι équipotentes terme à ter | E.R.33 item 5 | formalise_partiel | non_verifiable |
| Item 6, propriété : « N (entiers positifs) = ensemble des puissances d | E.R.33 item 6 | manquant | non_verifiable |
| Item 7, Déf. dénombrable : « un ensemble est dénombrable s'il est équi | E.R.33 item 7 | formalise_partiel | fidele |
| Item 7 (suite), propriétés des infinis : tout infini a une partition d | E.R.33 item 7 (bas) | formalise_partiel | ecart_majeur |
| Item 8, Déf. suite d'éléments : « une suite d'éléments de E est une fa | E.R.33 item 8 (début, suite p. E.R.34) | formalise_clos | fidele |

### §8 « Échelles d'ensembles et structures » (Résumé des résultats, E.R.34–37) — audit de fidélité contre la formalisation V9 (bourbaki/structures, IV.1–IV.3)
_pages lues : PDF physiques 337-340 = E.R.34, E.R.35, E.R.36, E.R.37 (rendus outils_ia/pdf_pages/aud_s8-337..340.png, lus). §8 complet (items 1 à 7, fin « multivalente »). Le §8 du Résumé condense le chap. IV du livre ; la formalisation est calée sur le chap. IV détaillé (IV.1.1–IV.1.7, IV.2, IV.3), que j'audite comme source des énoncés._

> Couverture très forte et fidèle du §8 : la machinerie générique du chapitre IV (échelon/schéma IV.1.1, extension canonique IV.1.2, typification/transportabilité IV.1.3, espèce de structure IV.1.4, isomorphisme/transport/automorphisme IV.1.5, termes intrinsèques/espèce plus riche IV.1.6, espèces équivalentes IV.1.7) est formalisée au niveau objet, VERBATIM des énoncés Bourbaki, avec 51 tests verts dans iv_1 et plusieurs propriétés CLOSES (réciproque d'iso, unicité du transport, identité-automorphisme, iso⇒égalité (4)). Définitions jugées fidèles ; écarts uniquement mineurs et DOCUMENTÉS (extensions ext_parties/produit_applications opaques au niveau objet ; « f bijection » explicitée dans l'iso ; espèce plus riche encodée par implication d'axiomes plutôt que par inclusion U⊂T). Aucun écart MAJEUR (aucun énoncé formalisé ne contredit le livre). Trois trous, sans risque de faux énoncé : (1) l'EXEMPLE concret « structure d'ensemble ordonné » (C∘C⊂C, C∩C̄⁻¹=Δ) et « totalement ordonné » (C∪C̄⁻¹=E×E) ne sont pas instanciés comme objets Espece (les relations d'ordre concrètes restent au chap. III) ; (2) « axiomes contradictoires » (T=∅) non introduit ; (3) « univalente/multivalente » (item 7) seulement représentationnel (marqueur documenté, non un prédicat-formule) car quantification méta sur toutes structures — partiel assumé, la conséquence « E,F équipotents » n'est pas formalisée.

| notion | E.R. | statut | fidélité |
|---|---|---|---|
| §8.1 — Échelle d'ensembles ayant pour base E,F,G : ensembles obtenus d | E.R.34–35, §8 item 1 (= IV.1.1 schéma/échelon) | formalise_clos | fidele |
| §8.1 — Une relation/une application/un couple revient à un seul élémen | E.R.35 (haut), §8 item 1 | non_applicable | fidele |
| §8.2 — Structure d'espèce T : T = intersection des parties d'un ensemb | E.R.35, §8 item 2 (= IV.1.4 espèce de structure) | formalise_clos | fidele |
| §8.2 — Exemple : structure d'ensemble ordonné = élément C de 𝔓(E×E) te | E.R.35, §8 item 2 (exemple) | manquant | non_verifiable |
| §8.2 — Une espèce dont les axiomes s'énoncent pour un E quelconque déf | E.R.35–36, §8 item 2 (fin) + IV.1.6 | formalise_clos | fidele |
| §8.3 — Espèce plus riche : ajout de nouveaux axiomes ⟹ partie U⊂T ; le | E.R.36, §8 item 3 (= IV.1.6 Exemple 3) | formalise_clos | fidele |
| §8.4 — Systèmes d'axiomes équivalents : application bijective de T sur | E.R.36, §8 item 4 (= IV.1.7 espèces équivalentes) | formalise_clos | fidele |
| §8.5 — Transport de structure : applications bijectives E→E', F→F', G→ | E.R.36, §8 item 5 (= IV.1.2 extension canonique + IV.1.5 transport) | formalise_clos | fidele |
| §8.5–6 (E.R.36) — Isomorphes / isomorphie / isomorphisme : σ' sur E',F | E.R.36 (haut) + E.R.37, §8 items 5–6 (= IV.1.5) | formalise_clos | fidele |
| §8.6 — Axiomes contradictoires : un système d'axiomes définissant T es | E.R.37, §8 item 6 (= IV.1.4 fin) | manquant | non_verifiable |
| §8.7 — Théorie univalente / multivalente : si deux structures satisfai | E.R.37, §8 item 7 (= IV.1.5 univalence) | formalise_partiel | ecart_mineur |
