# Couverture CHAP_II -- audit page-par-page du texte principal (2026-06-24)

Chaque notion du livre (texte principal) confrontee au code V9. Source = PDF lu page par page.

## Synthese (222 notions recensees)

**Statut code** : clos 107 | partiel 56 | **manquant 52** | n/a 7

**Fidelite** : fidele 114 | ecart mineur 38 | **ecart majeur 10** | non-verif 60

## Ecarts MAJEURS (enonce formalise != Bourbaki) -- priorite

- **II.2 Couples — texte principal** -- Caracterisation : la relation z=(pr1z,pr2z) ⇔ « z est un couple » (E II.7 (§2.1, juste avant le passage sur R{x,y})) : Bourbaki : « z=(pr1z,pr2z) est equivalente a : z est un couple ». Le code prouve seulement (z∈X×Y) ⇒ z=(pr1z,pr2z) : l'hypothese est l'appartenance a un PRODUIT donne, pas « z est un couple », et c'es
- **II.3 — Correspondances et fonc** -- Prop. 7 — f application : f⁻¹ fonction ⟺ f bijective ; application réc (E II.17) : SEUL le cœur graphe « F⁻¹ fonctionnel ⟺ F injectif » est CLOS (reciproque_fonctionnel_ssi_injectif). L'énoncé COMPLET de Bourbaki (f⁻¹ fonction ⟺ f BIJECTIVE, qui inclut la surjectivité via dom f⁻¹=f(
- **II.3 — Correspondances et fonc** -- Théorème 1 a–f — composition d'injections/surjections/rétractions/sect (E II.19) : a (inj) + b (surj) CLOS via composee_injective/composee_surjections ; composee_bijectives CLOS. Mais a/b (rétraction r∘r' / section s∘s'), c, d, e, f livrés au NIVEAU VALEURS et en FORME DÉPLIÉE (r(r'
- **II.3 — Correspondances et fonc** -- Corollaire §8 — g∘f=Id_A, f∘g=Id_B ⇒ f,g bijectives et g=f⁻¹ (E II.18) : corollaire_f_injective/corollaire_g_injective (parties injectivité) CLOS. L'identification g=f⁻¹ EXPLICITEMENT REPORTÉE dans le code (commentaire : exige pont valeurs↔graphe) — donc le corollaire comp
- **II.3 — Correspondances et fonc** -- Prop. 9 a/b — factorisation f=h∘g (g surj) / f=g∘h (g inj) ; h unique (E II.20) : prop9a/b_factorisation_valeur livrent le SENS RÉCIPROQUE CONSTRUCTIF au niveau VALEURS (f(s(u))=f(x) ; g(r(f(x)))=f(x)) sous hyps honnêtes. MANQUANT : la condition n.&s. complète (∃h ⟺ compatibilité /
- **II.5 — Produit d'une famille d** -- Proposition 2 — u surj & v inj ⇒ f↦v∘f∘u injective ; u inj & v surj ⇒  (E II.31 (§5.2, p82)) : ÉCART : seul le CŒUR est clos — (F,G,H fonctionnels)⇒(H∘(G∘F) fonctionnel), c-à-d la bien-définition de v∘f∘u. L'injectivité/surjectivité de f↦v∘f∘u (l'énoncé réel de la Prop 2) est explicitement REPO
- **II.5 — Produit d'une famille d** -- Proposition 4 — reparamétrage : u bijection K→I ⇒ F↦F∘U bijective ∏_{ι (E II.33 (§5.3, p84)) : ÉCART : seule la MOITIÉ injective est formalisée, et CONDITIONNELLE : (F,F'∈∏ ∧ (F∘U)∘V=F ∧ (F'∘U)∘V=F' ∧ F∘U=F'∘U)⇒F=F' sous hyp 'u admet inverse-graphe V'. La bijectivité (surjectivité + le bon but 
- **II.5 — Produit d'une famille d** -- Proposition 7 — (J_λ) partition de I ⇒ F↦(pr_{J_λ}F)_λ bijective ∏_{ι∈ (E II.34–35 (§5.5, p85–86)) : ÉCART : seule la SURJECTIVITÉ est formalisée, et CONDITIONNELLE : (F∈∏_I ∧ assoc(F)∈∏∏ ∧ recoller(assoc(F))=F)⇒(∃H)(H∈∏∏ ∧ recoller(H)=F), sous hyp inverse-recollement (=Prop 6 sur la partition). La b
- **II.5 — Produit d'une famille d** -- Proposition 10 — ⋂_{κ∈K}(∏_{ι∈I}X_{ι,κ})=∏_{ι∈I}(⋂_{κ∈K}X_{ι,κ}) (K≠∅) (E II.37 (§5.6, p88)) : ÉCART : la formule Prop 10 (commutation produit/⋂ indexée par K) n'est formalisée que (a) en demi-implication membership conditionnelle (G∈∏(⋂X_{ι,κ}))⇒(κ₀∈K⇒G∈∏X_{·,κ₀}), et (b) en version BINAIRE cl
- **II.6 — Relations d'équivalence** -- Proposition 1 — caractérisation d'une équivalence par a) X=ens. déf. Γ (E II.41 (p.92)) : Bourbaki: Γ équivalence dans X ⟺ (a)∧(b)∧(c). Le code ne prouve QUE le sens RÉCIPROQUE {G=G⁻¹, G∘G⊂G} ⊢ est_relation_equivalence(rel_graphe G), et SEULEMENT pour (b) symétrie + (c) transitivité. MANQU

## Notions MANQUANTES (dans le livre, pas closes dans le code)

### II.1 — Relations collectivisantes (Chapitre II « Théorie des
- [critere] CS12 — (V|x)(T⊂U) identique à (V|x)T ⊂ (V|x)U (stabilité par substitution) (E II.2 (nº2, p.53)) -- Critère métamathématique de substitution dans ⊂. Non formalisé : la substitution est gérée au niveau noyau (substituer) mais ce critère nomm
- [critere] CF13 — si T,U termes, T⊂U est une relation (critère formatif) (E II.2 (nº2, p.53)) -- Critère formatif (bonne formation de T⊂U). Garanti implicitement par le typage (inclus renvoie une Formule) mais aucun objet/théorème nommé.
- [remarque] Exemple 1 (nº4) — la relation x∈y est collectivisante en x (E II.4 (nº4, p.54)) -- Aucun théorème ⊢ Coll_x(x∈y). Non formalisé comme résultat nommé. ou_dans_code: "".
- [remarque] Exemple 2 (nº4) — x∉x n'est PAS collectivisante en x ; non Coll_x(x∉x) est un th (E II.4 (nº4, p.54)) -- ⊢ non Coll_x(x∉x) ABSENT du code. Recherche x∉x / Russell / non_collectivisante : aucun résultat. Manquant.
- [critere] C49 — si R collectivisante en x, (∀x)((x∈y)⇔R) est fonctionnelle en y (E II.3-4 (nº4, C49, p.54-55)) -- Critère (existence+unicité ⇒ symbole fonctionnel {x|R}) non formalisé comme objet nommé. ou_dans_code: "".
- [critere] C50 — pour R,S collectivisantes en x : (∀x)(R⇒S) ⇔ {x|R}⊂{x|S} ; (∀x)(R⇔S) ⇔ {x| (E II.4 (nº4, C50, p.55)) -- Critère reliant ⇒/⇔ des relations à ⊂/= des ensembles. Le PRINCIPE est utilisé partout via egalite_par_extension (ensembles_theoremes.py:71)
- [axiome] Schéma S8 — sélection et réunion : (∀y)(∃X)(∀x)(R⇒(x∈X)) ⇒ (∀Y)Coll_x((∃y)((y∈Y) (E II.4 (nº6, S8, p.55-56)) -- Le schéma S8 N'EST PAS formalisé comme schéma/axiome du noyau. Il sert uniquement de JUSTIFICATION méta dans les commentaires (« existence p
- [critere] C51 — pour P relation, A ensemble, x∉A : « P et x∈A » est collectivisante en x (E II.5 (nº6, C51, p.56)) -- Critère de sélection (séparation) : toute partie définie par P dans un ensemble A existe. Non formalisé comme théorème ; sa conséquence prat
- [critere] C52 — si R⇒(x∈A) est un théorème (A ensemble, x∉A), alors R est collectivisante  (E II.5 (nº6, C52, p.56)) -- Corollaire de C51. Non formalisé comme critère nommé. ou_dans_code: "".
- [remarque] Remarque (nº6) — si R collectivisante en x et (∀x)(S⇒R) théorème, alors S collec (E II.5 (nº6, p.56)) -- Remarque nommée (héritée de C52+C50). Non formalisée. ou_dans_code: "".
- [proposition] A⊂B ⇔ ∁_X B ⊂ ∁_X A (antitonie du complément) (E II.6 (nº7, p.57)) -- L'équivalence A⊂B ⇔ ∁B⊂∁A n'est pas formalisée comme théorème nommé. (Les caractérisations treillis A⊂B⇔A∩B=A / A∪B=B existent, inclusion_tr
- [theoreme] Théorème 1 — la relation (∀x)(x∉X) est fonctionnelle en X (justifie le symbole f (E II.6 (nº7, Th.1, p.57)) -- Le THÉORÈME 1 (univocité+existence de la relation (∀x)(x∉X), d'où ∅=τX((∀x)(x∉X))) n'est PAS formalisé. ∅ est posé DIRECTEMENT comme terme V
- [remarque] Remarque (nº7) — il n'existe pas d'ensemble dont tous les objets soient éléments (E II.6 (nº7, p.57)) -- Le théorème de non-existence d'un ensemble universel n'est PAS formalisé (recherche ensemble universel/non(∃X)(∀x)(x∈X) : aucun résultat). M

### II.2 Couples — texte principal, pages physiques 58-59 (E II.
- [remarque] Remarque : si z est un couple, (∃y)(z=(x,y)) et (∃x)(z=(x,y)) sont fonctionnelle (E II.7 (§2.1)) -- Justification (par Prop.1) du caractere fonctionnel des relations definissant pr1/pr2 ; condition de legitimite des termes τ. Non formalisee
- [remarque] Caracterisation : si z est un couple, (∃y)(z=(x,y)) ⇔ x=pr1z et (∃x)(z=(x,y)) ⇔  (E II.7 (§2.1)) -- Equivalences x=pr1z ⇔ (∃y)(z=(x,y)) (et duale pour pr2) sous « z couple ». Non formalisees comme theoremes nommes. Le code prouve pr1((x,y))
- [proposition] Caracterisation : la relation z=(x,y) ⇔ « z est un couple et x=pr1z et y=pr2z » (E II.7 (§2.1)) -- Resultat-cle de §2.1 (z=(x,y) ⇔ (z couple et x=pr1z et y=pr2z)), prouve dans le livre via Prop.1 + C33 + C47. Aucun theoreme du depot ne l'e
- [remarque] Interpretation : pour R{x,y} (x,y distinctes, dans R) et z lettre fraiche, S{z}  (E II.7-8 (§2.1, fin)) -- Remarque conceptuelle (et son corollaire encadre : « on peut interpreter une relation entre objets x,y comme une propriete du couple »). Con

### II.3 — Correspondances et fonctions (texte principal, E II.9
- [proposition] Prop. 1 — existence de A=pr₁G,B=pr₂G avec (∃y)(x,y)∈G⇔x∈A et (∃x)(x,y)∈G⇔y∈B (E II.9) -- AXIOME_DOM/AXIOME_IMG donnent les deux équivalences POINT À POINT, mais la Prop.1 (existence+unicité par A1 des ensembles pr₁G,pr₂G) n'est p
- [proposition] G⊂pr₁G×pr₂G ; tout ens. de couples est partie d'un produit ; pr₁G ou pr₂G vide ⇒ (E II.10) -- Conséquence de Prop.1 non isolée en théorème nommé dans le code.
- [corollaire] Corollaire — A⊃pr₁G ⇒ G⟨A⟩=pr₂G (E II.11) -- Corollaire de Prop.2 non formalisé.
- [definition] Graphe symétrique : G⁻¹=G (E II.11) -- Déf. « G symétrique := G⁻¹=G » (E II.11) ABSENTE. est_symetrique de ensembles_abrege.py code la symétrie d'une RELATION R{x,y} (E II.6.1), n
- [remarque] pr₁(G'∘G)=G⁻¹⟨pr₁G'⟩, pr₂(G'∘G)=G'⟨pr₂G⟩, X⊂pr₁G ⇒ X=G⁻¹⟨G⟨X⟩⟩ (E II.12) -- Sous-résultats de la preuve de Prop.5 non isolés ; X⊂f⁻¹⟨f⟨X⟩⟩ partiellement couvert par inclus_image_reciproque_image (sous H_app).
- [remarque] G1⊂G2 & G1'⊂G2' ⇒ G1'∘G1⊂G2'∘G2 (monotonie composée) (E II.13) -- Monotonie de la composée non isolée.

### II.4 — Réunion et intersection d'une famille d'ensembles (E 
- [definition] Déf. 3 — Intersection d'une famille de parties de E (⋂ inclut « x∈E », vaut E si (E II.23 (n°1, Déf. 3)) -- Bourbaki : pour une famille de parties de E, ⋂ = {x | x∈E et (∀ι)(ι∈I⇒x∈X_ι)}, qui pour I=∅ donne ⋂=E. Cette VARIANTE (clause z∈E) n'est PAS
- [definition] Déf. 4 — Réunion/intersection des ensembles d'un ensemble d'ensembles 𝔉 (⋃_{X∈𝔉} (E II.23–24 (n°1, Déf. 4)) -- Réunion/intersection des éléments d'un ENSEMBLE d'ensembles 𝔉 (= famille définie par id_𝔉). Notation ⋃_{X∈𝔉}X, ⋂_{X∈𝔉}X non formalisée comme
- [notation] Trace de X sur A (X∩A) ; trace d'une famille 𝔉 sur A (E II.27 (n°5)) -- Notation « trace de X sur A » = X∩A, et trace d'une famille sur A. Pure terminologie ; X∩A existe (intersection) mais le terme/notion nommé 
- [remarque] Recouvrement par un ensemble d'ensembles ℜ (E⊂⋃_{X∈ℜ}X) (E II.27 (n°6)) -- Variante de la Déf. 5 pour un ensemble d'ensembles ℜ (via id_ℜ). Pas formalisée distinctement (cf. Déf. 4 manquante).
- [remarque] Transitivité de « plus fin » ; sous-recouvrement (J⊂I) plus fin ; intersection d (E II.28 (n°6)) -- Série de remarques nommées sur les recouvrements (ℜ''plus fin que ℜ par transitivité ; (X_ι∩Y_κ) recouvrement le plus fin commun ; image f⟨X
- [remarque] Préimage d'une famille disjointe par f est disjointe (f⁻¹⟨Y_ι⟩) ; remarque sur f (E II.29 (n°7)) -- Remarque : si (Y_ι) mutuellement disjointes, (f⁻¹⟨Y_ι⟩) le sont aussi (par Prop. 4) ; l'image directe ne l'est pas en général. Non formalisé
- [remarque] Exemple — ({x})_{x∈A} est une partition de A (A non vide) (E II.29 (n°7, Exemple)) -- Exemple nommé : la famille des singletons est une partition. Non formalisé comme théorème. Manquant (faisable, illustratif).
- [remarque] Bijection ι↦X_ι d'une partition en parties non vides sur l'ensemble des éléments (E II.29 (n°7)) -- Remarque : une partition en ensembles non vides définit une bijection entre l'ensemble d'indices et l'ensemble 𝔉 des éléments de la partitio
- [notation] Adjonction (somme de X et {a}) (E II.30 (n°8)) -- Terminologie : un ensemble somme de X et {a} est obtenu par « adjonction de a à X ». Notation non formalisée. Impact nul.

### II.5 — Produit d'une famille d'ensembles (E II.30–II.38, tex
- [remarque] Remarque — adjonction de a à X (somme de X et {a}) (E II.30 (haut p81)) -- Notion §II.4. « ensemble somme d'un X et d'un {a} = adjonction de a à X ». Aucun grep 'adjonction' ne trouve de prédicat. Hors périmètre II.
- [notation] Bijection canonique G↦(G,E,F) de F^E sur 𝓕(E;F) (E II.31 (§5.2, p82)) -- « Bijection dite canonique de F^E sur 𝓕(E;F) ». Aucune formalisation de cette bijection précise (grep négatif). Notion de traduction, non im
- [corollaire] Corollaire (de Prop 2) — u,v bijections ⇒ f↦v∘f∘u bijective (E II.31 (§5.2, p82)) -- Corollaire de la Prop 2. Non formalisé (dépend de la Prop 2 reportée).
- [remarque] Cas I=∅ : ∏_{ι∈I}X_ι réduit au seul élément ∅ (E II.32 (§5.3, p83)) -- « Si I=∅, le produit n'a qu'un seul élément, l'ensemble vide. » Aucun théorème ∏(f,∅)={∅} formalisé (grep négatif).
- [remarque] Cas facteurs constants : ∏_{ι∈I}X_ι = E^I quand tous X_ι=E ; ∏X_ι⊂E^I si ⋃X_ι⊂E (E II.32 (§5.3, p83)) -- Égalité ∏X_ι=E^I (facteurs égaux à E) et inclusion ∏X_ι⊂E^I. Non formalisée comme théorème (grep négatif). Les références E^I servent ailleu
- [remarque] Cas I={α} : ∏X_ι=X_α^{(α)}, bijection canonique F↦F(α), ∏→X_α (E II.32–33 (§5.3, p83–84)) -- Produit à un seul indice = bijection canonique sur X_α. Non formalisé (grep négatif). Utilisé par Bourbaki dans la preuve du Cor 1 de Prop 6
- [remarque] Cas X_ι={a_ι} singletons : ∏X_ι réduit à l'unique élément (a_ι) (E II.33 (§5.3, p84)) -- Produit de singletons = singleton. Non formalisé (grep négatif).
- [corollaire] Corollaire 1 (de Prop 6) — X_ι≠∅ ∀ι ⇒ pr_α surjection de ∏ sur X_α (E II.34 (§5.4, p85)) -- pr_α surjective (cas J={α} de Prop 5 + bijection ∏=X_α^{(α)}). Pas de théorème dédié ; la surjectivité de pr_α est utilisée comme hypothèse-
- [remarque] Remarque 1 (§5.5) — bijection canonique ∏X_ι ≅ (∏_{J_α}X_ι)×(∏_{J_β}X_ι) pour pa (E II.35 (§5.5, p86)) -- Cas partition en deux blocs : bijection produit ≅ produit×produit. Non formalisé (grep négatif).
- [remarque] Remarque 2 (§5.5) — bijection canonique ∏_{ι∈{α,β,γ}}X_ι ≅ A×B×C et permutations (E II.35 (§5.5, p86)) -- Identification du produit à 3 indices avec A×B×C et toutes ses permutations. Non formalisé (grep négatif).
- [proposition] Proposition 8 — distributivité ⋃/⋂ : ⋃_λ⋂_{ι∈J_λ}X_{λ,ι}=⋂_{f∈I}⋃_λ X_{λ,f(λ)} e (E II.35–36 (§5.6, p86–87)) -- Les deux formules de distributivité ⋃/⋂ (avec I=∏J_λ, f fonction de choix). NON formalisées (grep négatif : seulement mentionnées en comment
- [corollaire] Corollaire (de Prop 8) — (⋂X_ι)∪(⋂Y_κ)=⋂_{I×K}(X_ι∪Y_κ) et (⋃X_ι)∩(⋃Y_κ)=⋃_{I×K} (E II.36 (§5.6, p87)) -- Version binaire des distributivités ⋃/⋂ indexée par I×K. Non formalisée (grep négatif).
- [proposition] Proposition 9 — distributivité du produit : ∏_λ(⋃_{ι∈J_λ}X_{λ,ι})=⋃_{f∈I}∏_λ X_{ (E II.36–37 (§5.6, p87–88)) -- Les deux formules de distributivité du produit sur ⋃ et ⋂. NON formalisées (grep négatif : seulement mentionnées). Manque majeur du §5.6.
- [corollaire] Corollaire 1 (de Prop 9) — (X_{λ,ι})_ι partition de X_λ ⇒ (∏_λ X_{λ,f(λ)})_f par (E II.37 (§5.6, p88)) -- Le produit d'une famille de partitions est une partition du produit. Non formalisé (grep négatif).
- [corollaire] Corollaire 2 (de Prop 9) — (⋃X_ι)×(⋃Y_κ)=⋃_{I×K}(X_ι×Y_κ) et (⋂X_ι)×(⋂Y_κ)=⋂_{I× (E II.37 (§5.6, p88)) -- Distributivité du produit binaire ×  sur ⋃/⋂ de familles. Non formalisée (grep négatif).

### II.6 — Relations d'équivalence (texte principal, E II.39–II.
- [remarque] Stabilité saturation par réunion/intersection/complémentaire (E II.43-44 (p.94-95)) -- Bourbaki: si (X_ι) saturées, ∪X_ι et ∩X_ι saturées (II.25 prop 3,4) ; ∁_E A saturée ; saturé de ∪X_ι = ∪(saturés). Aucun de ces résultats n'
- [proposition] Les classes de R×R' sont les produits de classes ; canonicité (E×E')/(R×R')↔(E/R (E II.46-47 (p.97-98)) -- Bourbaki: toute classe de R×R' = produit d'une classe de R et d'une classe de R' ; f×f' donne bijection canonique (E×E')/(R×R')→(E/R)×(E'/R'
- [remarque] Remarque — Q{u} compatible avec R×R' ⟺ P{x,x'} compatible avec R et R' (E II.47 (p.98)) -- Bourbaki (Remarque, p.98): P compatible avec R et R' ⟺ Q{u}:=∃x∃x'(u=(x,x') et P{x,x'}) compatible avec R×R'. Non formalisé. MANQUANT.
- [critere] Condition (1) ⟹ relation ∃x(R{x,x} et z=θ{x}) collectivisante en z (E II.48 (p.99)) -- Bourbaki: si (∀y)(R{y,y}⇒∃x(x∈T et R{x,y})) alors (∃x)(R{x,x} et z=θ{x}) est collectivisante en z (preuve par remplacement de T par {x∈T|R{x
- [proposition] Bijection Θ→F/R justifiant la terminologie (R équivalence DANS un ensemble F) (E II.48 (p.99)) -- Bourbaki: si R équivalence dans F, prendre A{x}=Cl(x) ⟹ f:θ{x}↦A{θ{x}} bijection de Θ sur F/R (justifie d'appeler Θ ensemble des classes). N

## Detail complet par section

### II.1 — Relations collectivisantes (Chapitre II « Théorie des ensembles »), E II.1 à E II.6, nº 1 à 7
_pages : Pages physiques 52-57 du PDF (= E II.1 à E II.6), rendues en PNG à 150 dpi (outi_  (35 notions, 12 manquantes)

> Section II.1 (E II.1-II.6, pages 52-57) entièrement épluchée page par page. La COUVERTURE DE BASE est solide et fidèle pour les briques fondamentales : ∈ et ⊂ (Déf.1) fidèles ; axiomes A1 (extensionnalité) et A2 (paire) verbatim et membres de theorie_ensembles() (22 axiomes) ; constructeur coll(x,f) de Coll_x R fidèle ; termes {x,y} (Déf.2), {x}, ∅ caractérisés par axiomes de membership (AXIOME_PAIRE, AXIOME_VIDE) avec théorèmes clos (commutativite_paire, vide_sans_element, vide_ssi_sans_element). Les Propositions 1 (x⊂x) et 2 (transitivité) sont CLOSES mais DÉPLACÉES hors zone II.1 (rangées dans ordre/iii_1, via inclusion_reflexive/inclusion_transitive) — écart structurel par rapport au plan « arbre calqué sur la table des matières ». Le complémentaire (Déf.3) est réalisé par la différence E∖X (AXIOME_DIFF) avec lois closes (X∖X=∅, X∩∁X=∅) et lois gardées honnêtes (∁∁X=X, X∪∁X=E sous X⊂E). Les théorèmes du vide du nº7 (x∉∅, ∁_X X=∅, ∁_X ∅=X) sont présents et clos ; ∅⊂X n'existe que comme helper privé.

MANQUES MAJEURS (priorité). 1) Le SCHÉMA S8 (sélection et réunion), pilier collectivisant de tout le chapitre, n'est PAS formalisé : il sert uniquement de justification méta en commentaire, et l'existence de chaque ensemble par compréhension est ADMISE par un axiome de membership ad hoc (AXIOME_PRODUIT, theorie_graphe_terme, diagonale_cantor, etc.) — fondement jamais dérivé de S8. 2) AUCUN des critères C48, C49, C50, C51, C52, C53 n'est formalisé comme objet nommé (seul leur ESPRIT survit via egalite_par_extension/unicite_par_extension et les termes par sélection). 3) Le THÉORÈME 1 du nº7 (la relation (∀x)(x∉X) est fonctionnelle en X, qui FONDE le symbole ∅) est absent : ∅ est posé directement par axiome, sans établir univocité/fonctionnalité. 4) Les deux exemples-clés du nº4 (x∈y collectivisante ; surtout « x∉x NON collectivisante » = non-existence de l'ensemble de Russell) ne sont pas prouvés. 5) La Remarque finale « non(∃X)(∀x)(x∈X) » (pas d'ensemble universel) est absente. 6) Notations génériques {x|R} et {x∈A|P} non disponibles comme abréviateurs uniques (réalisées au cas par cas). Soundness garantie par le noyau LCF ; la fidélité d'énoncé est bonne là où c'est implémenté, mais la section a un déficit structurel : son armature métamathématique (S8 + critères C48-C53) est contournée plutôt que formalisée.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Théorie des ensembles (signes ∈, =, schémas S1-S8, axio | definition | E II.1 (nº1, p.52) | partiel | ecart_mineur |  |
| Relation d'appartenance ∈ TU (T appartient à U) ; notat | notation | E II.1 (nº1, p.52) | clos | fidele |  |
| Définition 1 — relation d'inclusion x⊂y := (∀z)((z∈x)⇒( | definition | E II.2 (nº2, Déf.1, p.53) | clos | fidele |  |
| CS12 — (V/x)(T⊂U) identique à (V/x)T ⊂ (V/x)U (stabilit | critere | E II.2 (nº2, p.53) | manquant | non_verifiable |  |
| CF13 — si T,U termes, T⊂U est une relation (critère for | critere | E II.2 (nº2, p.53) | manquant | non_verifiable |  |
| Proposition 1 — x⊂x (réflexivité ; x est la « partie pl | proposition | E II.2 (nº2, Prop.1, p.53) | clos | fidele |  |
| Proposition 2 — (x⊂y et y⊂z) ⇒ x⊂z (transitivité de ⊂) | proposition | E II.2 (nº2, Prop.2, p.53) | clos | fidele |  |
| Axiome A1 — extensionnalité : (∀x)(∀y)((x⊂y et y⊂x)⇒(x= | axiome | E II.3 (nº3, A1, p.54) | clos | fidele |  |
| C48 — pour R relation, x lettre, y∉R : la relation (∀x) | critere | E II.3 (nº3, C48, p.54) | partiel | ecart_mineur |  |
| Définition (nº4) — Coll_x R := (∃y)(∀x)((x∈y)⇔R) (R col | definition | E II.4 (nº4, p.54) | clos | fidele |  |
| Exemple 1 (nº4) — la relation x∈y est collectivisante e | remarque | E II.4 (nº4, p.54) | manquant | non_verifiable |  |
| Exemple 2 (nº4) — x∉x n'est PAS collectivisante en x ;  | remarque | E II.4 (nº4, p.54) | manquant | non_verifiable |  |
| C49 — si R collectivisante en x, (∀x)((x∈y)⇔R) est fonc | critere | E II.3-4 (nº4, C49, p.54-55) | manquant | non_verifiable |  |
| Notation {x/R} — l'ensemble des x tels que R ; τy((∀x)( | notation | E II.4 (nº4, p.55) | partiel | ecart_mineur |  |
| C50 — pour R,S collectivisantes en x : (∀x)(R⇒S) ⇔ {x/R | critere | E II.4 (nº4, C50, p.55) | manquant | non_verifiable |  |
| Axiome A2 — paire : (∀x)(∀y)Coll_z(z=x ou z=y) | axiome | E II.4 (nº5, A2, p.55) | clos | fidele |  |
| Définition 2 — {x,y} : l'ensemble {z / z=x ou z=y} ; {y | definition | E II.4 (nº5, Déf.2, p.55) | clos | fidele |  |
| Singleton {x} := {x,x} ; z∈{x}⇔z=x ; x∈X ⇔ {x}⊂X | definition | E II.4 (nº5, p.55) | partiel | ecart_mineur |  |
| Schéma S8 — sélection et réunion : (∀y)(∃X)(∀x)(R⇒(x∈X) | axiome | E II.4 (nº6, S8, p.55-56) | manquant | non_verifiable |  |
| C51 — pour P relation, A ensemble, x∉A : « P et x∈A » e | critere | E II.5 (nº6, C51, p.56) | manquant | non_verifiable |  |
| Notation {x∈A / P} — l'ensemble des x∈A tels que P | notation | E II.5 (nº6, p.56) | partiel | ecart_mineur |  |
| C52 — si R⇒(x∈A) est un théorème (A ensemble, x∉A), alo | critere | E II.5 (nº6, C52, p.56) | manquant | non_verifiable |  |
| Remarque (nº6) — si R collectivisante en x et (∀x)(S⇒R) | remarque | E II.5 (nº6, p.56) | manquant | non_verifiable |  |
| C53 — pour T terme, A ensemble : (∃x)(y=T et x∈A) est c | critere | E II.5-6 (nº6, C53, p.56-57) | partiel | ecart_mineur |  |
| Définition 3 — complémentaire ∁_X A = X − A := {x / x∉A | definition | E II.6 (nº7, Déf.3, p.57) | clos | ecart_mineur |  |
| A=∁_X(∁_X A) (involution du complément, A partie de X) | proposition | E II.6 (nº7, p.57) | partiel | fidele |  |
| A⊂B ⇔ ∁_X B ⊂ ∁_X A (antitonie du complément) | proposition | E II.6 (nº7, p.57) | manquant | non_verifiable |  |
| Théorème 1 — la relation (∀x)(x∉X) est fonctionnelle en | theoreme | E II.6 (nº7, Th.1, p.57) | manquant | non_verifiable |  |
| Définition de l'ensemble vide ∅ := τ_X((∀x)(x∈X)... soi | definition | E II.6 (nº7, p.57) | clos | ecart_mineur |  |
| Théorème — x∉∅ (∅ n'a pas d'élément) | theoreme | E II.6 (nº7, p.57) | clos | fidele |  |
| Théorème — ∅⊂X (le vide est inclus dans tout ensemble) | theoreme | E II.6 (nº7, p.57) | partiel | fidele |  |
| Théorème — ∁_X X = ∅ (complémentaire de X dans X est vi | theoreme | E II.6 (nº7, p.57) | clos | fidele |  |
| Théorème — ∁_X ∅ = X (complémentaire du vide dans X est | theoreme | E II.6 (nº7, p.57) | clos | fidele |  |
| Théorème — X⊂∅ ⇔ X=∅ | theoreme | E II.6 (nº7, p.57) | partiel | ecart_mineur |  |
| Critère — (∀x)((x∈∅)⇒R{x}) est vraie (ex falso sur ∅) | critere | E II.6 (nº7, p.57) | partiel | fidele |  |
| Remarque (nº7) — il n'existe pas d'ensemble dont tous l | remarque | E II.6 (nº7, p.57) | manquant | non_verifiable |  |

### II.2 Couples — texte principal, pages physiques 58-59 (E II.7 fin de §1, §2.1 Definition des couples ; E II.8 §2.2 Produit de deux ensembles)
_pages : 58 (E II.7), 59 (E II.8)_  (17 notions, 4 manquantes)

> Audit du texte principal de §II.2 « Couples », pages physiques 58-59 (E II.7 fin de §1 + §2.1 Definition des couples ; E II.8 §2.2 Produit de deux ensembles ; la preuve de Prop.3 deborde sur la p.60 non rendue). 17 notions recensees (dont 1 remarque de cloture de §1 et 1 terminologie, hors decompte de manques).

CŒUR BIEN COUVERT ET FIDELE : la Definition du couple (E.couple={{x},{x,y}}), la Proposition 1 ((x,y)=(x',y') ⇔ x=x' et y=y', proposition_1, equivalence complete, hyp=0), la definition « z est un couple » (est_un_couple), les definitions des projections pr1/pr2 comme termes τ (E.pr1/E.pr2), l'identite pr1(x,y)=x / pr2(x,y)=y (projection_premiere/seconde, clos), la Definition 1 du produit X×Y (E.produit + AXIOME_PRODUIT), et la Proposition 3 (produit_vide, equivalence complete, hyp=0). Tous ces resultats sont clos (0 hypothese) et leurs enonces coincident avec Bourbaki.

MANQUANTS (4, hors §1/terminologie) — tous dans §2.1, autour de la caracterisation des couples par leurs projections :
 (a) z=(x,y) ⇔ « z couple et x=pr1z et y=pr2z » : resultat central de §2.1, AUCUN theoreme du depot ne l'enonce ;
 (b) x=pr1z ⇔ (∃y)(z=(x,y)) (et duale) sous « z couple » : equivalences generales absentes (seul le cas applique pr1((x,y))=x est prouve) ;
 (c) le caractere fonctionnel des relations definissant pr1/pr2 (justification par Prop.1) non formalise (meta-justification, mineur) ;
 (d) l'interpretation S{z}=(∃x)(∃y)(z=(x,y) et R{x,y}) et les equivalences R{x,y} ⇔ S{(x,y)} ⇔ (∃z)(z=(x,y) et S{z}) (transformation relation↔propriete du couple, C47) : entierement absente.

ECARTS MAJEURS (1) : z=(pr1z,pr2z) ⇔ « z est un couple » est implemente (couple_decomposition) UNIQUEMENT comme implication restreinte (z∈X×Y) ⇒ z=(pr1z,pr2z) — hypothese « appartenance a un produit donne » au lieu de « z couple », et sens unique au lieu de l'equivalence : ecart de portee assume comme brique technique d'extensionnalite.

ECARTS MINEURS / POINT DE STATUT NOTABLE : le THEOREME 1 (collectivisante en z, donc EXISTENCE du produit) est POSTULE comme AXIOME_PRODUIT et non derive (la demonstration Bourbaki via C53/S8 n'est pas reproduite) — l'enonce d'appartenance est fidele mais le theoreme d'existence reste axiomatise (partiel). z∈X×Y ⇔ (z couple et pr1z∈X et pr2z∈Y) et la Proposition 2 sont couverts fidelement au contenu mais decoupes en briques (couple_dans_produit_ssi, produit_projections ; produit_inclusion_facile + deux reciproques) sans reassemblage en l'equivalence-z / l'equivalence globale unique de Bourbaki.

Bilan : tronc definitionnel et propositions 1 et 3 fideles et clos ; trou structurel concentre sur la caracterisation generale des couples par projections (z=(x,y)/z=(pr1z,pr2z) au niveau z arbitraire) et l'interpretation relation-comme-propriete-du-couple ; Theoreme 1 axiomatise plutot que prouve.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Remarque de cloture de §1 : « toute relation serait col | remarque | E II.7 (haut, fin de §1) | non_applicable | non_verifiable |  |
| Definition du couple (x,y) := {{x},{x,y}} | definition | E II.7 (§2.1, suite de Prop.1) | clos | fidele | ensembles_abrege.couple(t,u) = paire(sin |
| Proposition 1 : {{x},{x,y}}={{x'},{x',y'}} ⇔ (x=x' et y | proposition | E II.7 (§2.1, Prop.1) | clos | fidele | ensembles_couples.proposition_1 (sens du |
| Notation/Definition : « z est un couple » := (∃x)(∃y)(z | definition | E II.7 (§2.1) / E II.31 cite par le code | clos | fidele | ensembles_abrege.est_un_couple(z) = (∃x) |
| Remarque : si z est un couple, (∃y)(z=(x,y)) et (∃x)(z= | remarque | E II.7 (§2.1) | manquant | non_verifiable |  |
| Definition des projections : pr1z := τx((∃y)(z=(x,y))), | definition | E II.7 (§2.1) / E II.31 (cite par le code) ; renvoi I p.41 | clos | fidele | ensembles_abrege.pr1(z)=tau(x,(∃y)(z=(x, |
| Caracterisation : si z est un couple, (∃y)(z=(x,y)) ⇔ x | remarque | E II.7 (§2.1) | manquant | non_verifiable |  |
| Caracterisation : la relation z=(x,y) ⇔ « z est un coup | proposition | E II.7 (§2.1) | manquant | non_verifiable |  |
| « On a evidemment pr1(x,y)=x et pr2(x,y)=y » | proposition | E II.7 (§2.1) | clos | fidele | ensembles_projections.projection_premier |
| Caracterisation : la relation z=(pr1z,pr2z) ⇔ « z est u | proposition | E II.7 (§2.1, juste avant le passage sur R{x,y}) | partiel | ecart_majeur | ensembles_produit_extensionnalite.couple |
| Interpretation : pour R{x,y} (x,y distinctes, dans R) e | remarque | E II.7-8 (§2.1, fin) | manquant | non_verifiable |  |
| Theoreme 1 : (∀X)(∀Y)(∃Z)(∀z)(z∈Z ⇔ (∃x)(∃y)(z=(x,y) et | theoreme | E II.8 (§2.2, Th.1) | partiel | ecart_mineur | ensembles_abrege.AXIOME_PRODUIT (posee c |
| Definition 1 : X×Y := {z / (∃x)(∃y)(z=(x,y) et x∈X et y | definition | E II.8 (§2.2, Def.1) | clos | fidele | ensembles_abrege.produit(t,u) (terme pri |
| Caracterisation : z∈X×Y ⇔ « z est un couple et pr1z∈X e | remarque | E II.8 (§2.2, apres Def.1) | partiel | ecart_mineur | ensembles_produit.couple_dans_produit_ss |
| Terminologie : X, Y appeles premier et second ensemble  | notation | E II.8 (§2.2) | non_applicable | non_verifiable |  |
| Proposition 2 : si A',B' non vides, (A'×B' ⊂ A×B) ⇔ (A' | proposition | E II.8 (§2.2, Prop.2) | clos | ecart_mineur | ensembles_produit.produit_inclusion_faci |
| Proposition 3 : A×B=∅ ⇔ (A=∅ ou B=∅) | proposition | E II.8 (§2.2, Prop.3) ; preuve debordant sur p.60 | clos | fidele | ensembles_produit.produit_vide (= conjon |

### II.3 — Correspondances et fonctions (texte principal, E II.9–E II.21)
_pages : PNG physiques 60–72 (= E II.9 à E II.21 ; p.60 fin de II.2 sur le triplet, puis _  (46 notions, 11 manquantes)

> Couverture EXCELLENTE et globalement très fidèle. Le texte principal de II.3 (Déf. 1–11, Prop. 1–9, Th. 1 a–f, Cor., C54, plus les remarques/notations nommées) est presque intégralement formalisé, avec un module par sous-section calqué sur la table des matières et un test par résultat (statut « clos » bien étayé). Les TERMES/PRÉDICATS de base (graphe, dom/img/image, réciproque, composée, restriction, graphe_terme/fonction_terme, est_fonctionnel, valeur f(x), injection/surjection/bijection, diagonale/Id, rétraction/section) sont présents dans ensembles_abrege.py et caractérisés par 8 axiomes de définition (DOM, IMG, IMAGE, RECIP, COMPOSEE, RESTRICTION, DIAGONALE, graphe_terme) — théorie à 22 axiomes inchangée. Les graphe-théorèmes inconditionnels sont CLOS et FIDÈLES : couple_reciproque (Déf.5), pr1/pr2 réciproque, (X×Y)⁻¹=Y×X, couple_composee+image_composee=Prop.5, reciproque_composee=Prop.3, composee_associative=Prop.4, image_croissante=Prop.2, coupe_membre (Déf.4), valeur_caracterisation=C46, graphe_terme_fonctionnel=C54, composee_fonctionnelle=Prop.6, reciproque_fonctionnel_ssi_injectif=cœur Prop.7, retraction_implique_injective + section_construite_par_tau=Prop.8. 

ÉCARTS / FAIBLESSES (à signaler) : (1) Le Théorème 1 (a–f) et la Prop. 9 sont formalisés au NIVEAU DES VALEURS et en FORME DÉPLIÉE (r(r'(f'(f(x))))=x au lieu de (r∘r')∘(f'∘f)=Id, etc.), avec hypothèses C46 honnêtes mais sans la forme « repliée » r∘r' rétraction de f''=f'∘f — écart de présentation assumé (verrou τ-capture). Plusieurs volets de e)/f) ne livrent qu'une BRIQUE de la preuve, pas l'énoncé complet (e) « f surjective » entier reporté). (2) Prop. 7 SENS COMPLET (f⁻¹ fonction ⟺ f bijective, au niveau application+but) reporté : seul le cœur graphe « F⁻¹ fonctionnel ⟺ F injectif » est clos. (3) Prop. 8 sens réciproque INJECTIF (existence d'une rétraction r si f injective et A≠∅, construction par τ) MANQUANT (seul le cas surjectif=section est construit). (4) Plusieurs notions sont des DÉFINITIONS nommées sans propriété (correspondance_reciproque/composee de triples, application partielle, permutation) — correct mais « niveau définition ». 

MANQUANTS véritables (notions du livre absentes) : Prop. 1 (existence de A=pr₁G, B=pr₂G avec les deux équivalences) et G⊂pr₁G×pr₂G non isolés en théorème nommé ; Déf. 8 « Γ∘Id_A=Id_B∘Γ=Γ » et « Id_A est sa propre réciproque » non prouvés ; « réciproque de G⁻¹ est G » / « réciproque de Γ'∘Γ = Γ⁻¹∘Γ'⁻¹ au niveau correspondances » non isolés ; Prop. 7 « f⁻¹ involutive », « permutation involutive » (Déf., E II.18) absent ; Th.1 Corollaire « g=f⁻¹ » explicitement REPORTÉ (noté dans le code) ; et le DERNIER paragraphe de §9 (extension canonique / produit u×v de deux applications, (u'×v')∘(u×v)=(u'∘u)×(v'∘v), u×v injective/surjective/bijective) appartient au texte de E II.21 mais n'est traité que partiellement en II.5 (extension_produit introduit, propriétés reportées). La « fonction de deux arguments » (Déf. §9) et l'« application partielle » sont bien présentes (fonctions_complements + valeur_deux_arguments).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Triplet (A×B)×C=A×B×C | notation | E II.9 | non_applicable | non_verifiable |  |
| Déf. 1 — Graphe (tout élément est un couple) | definition | E II.9 | clos | fidele | ensembles_abrege.est_un_graphe |
| R admet un graphe / graphe d'une relation | definition | E II.9 | clos | fidele | ensembles_abrege.graphe_terme + axiome_g |
| Prop. 1 — existence de A=pr₁G,B=pr₂G avec (∃y)(x,y)∈G⇔x | proposition | E II.9 | manquant | non_verifiable |  |
| pr₁G / pr₂G — première/seconde projection (domaine, ens | definition | E II.9 | clos | fidele | ensembles_abrege.dom, .img + AXIOME_DOM, |
| G⊂pr₁G×pr₂G ; tout ens. de couples est partie d'un prod | proposition | E II.10 | manquant | non_verifiable |  |
| Remarque — x=y n'admet pas de graphe | remarque | E II.10 | non_applicable | non_verifiable |  |
| Déf. 2 — Correspondance Γ=(G,A,B), G⊂A×B ; départ/arriv | definition | E II.10 | clos | fidele | ensembles_fondations_notions.est_une_cor |
| Déf. 3 — Image directe G⟨X⟩ ; Γ⟨X⟩ | definition | E II.10 | clos | fidele | ensembles_abrege.image + AXIOME_IMAGE |
| G⟨pr₁G⟩=pr₂G, G⟨∅⟩=∅, X⊂pr₁G & X≠∅ ⇒ G⟨X⟩≠∅, G⟨X⟩⊂pr₂G | remarque | E II.10 | partiel | fidele | ensembles_correspondances.image_vide, .i |
| Prop. 2 — X⊂Y ⇒ G⟨X⟩⊂G⟨Y⟩ | proposition | E II.10 | clos | fidele | ensembles_correspondances.image_croissan |
| Corollaire — A⊃pr₁G ⇒ G⟨A⟩=pr₂G | corollaire | E II.11 | manquant | non_verifiable |  |
| Déf. 4 — Coupe de G suivant x : G⟨{x}⟩ ; Γ⟨{x}⟩ | definition | E II.11 | clos | fidele | ensembles_fonctions_complements.coupe ;  |
| Déf. 5 — Graphe réciproque G⁻¹ ; image réciproque G⁻¹⟨X | definition | E II.11 | clos | fidele | ensembles_abrege.reciproque ; ensembles_ |
| Réciproque de G⁻¹ est G ; pr₁G⁻¹=pr₂G, pr₂G⁻¹=pr₁G | remarque | E II.11 | partiel | fidele | ensembles_reciproque.pr1_reciproque, .pr |
| (X×Y)⁻¹=Y×X | remarque | E II.11 | clos | fidele | ensembles_reciproque.reciproque_produit |
| Graphe symétrique : G⁻¹=G | definition | E II.11 | manquant | non_verifiable |  |
| Correspondance réciproque Γ⁻¹=(G⁻¹,B,A) ; image récipro | definition | E II.11 | partiel | fidele | ensembles_fonctions_complements.correspo |
| Déf. 6 — Composé de graphes G'∘G | definition | E II.11 | clos | fidele | ensembles_abrege.composee ; ensembles_co |
| Prop. 3 — (G'∘G)⁻¹=G⁻¹∘G'⁻¹ | proposition | E II.12 | clos | fidele | ensembles_composee_reciproque.reciproque |
| Prop. 4 — associativité (G3∘G2)∘G1=G3∘(G2∘G1) | proposition | E II.12 | clos | fidele | ensembles_composee_assoc.composee_associ |
| Prop. 5 — (G'∘G)⟨A⟩=G'⟨G⟨A⟩⟩ | proposition | E II.12 | clos | fidele | ensembles_composee.image_composee ; ense |
| pr₁(G'∘G)=G⁻¹⟨pr₁G'⟩, pr₂(G'∘G)=G'⟨pr₂G⟩, X⊂pr₁G ⇒ X=G⁻ | remarque | E II.12 | manquant | non_verifiable |  |
| G1⊂G2 & G1'⊂G2' ⇒ G1'∘G1⊂G2'∘G2 (monotonie composée) | remarque | E II.13 | manquant | non_verifiable |  |
| Déf. 7 — Composée de correspondances Γ'∘Γ=(G'∘G,A,C) ;  | definition | E II.13 | partiel | fidele | ensembles_fonctions_complements.correspo |
| Déf. 8 — Diagonale Δ_A ; correspondance identique Id_A= | definition | E II.13 | partiel | fidele |  |
| Déf. 9 — Graphe fonctionnel ; fonction f=(F,A,B) ; vale | definition | E II.13 | clos | fidele | ensembles_abrege.est_fonctionnel, .valeu |
| Application f de A dans B (départ=définition=A, arrivée | definition | E II.14 | clos | fidele | ensembles_fondations_notions.est_applica |
| Famille / ens. d'indices / ens. des éléments ; famille  | notation | E II.14 | clos | fidele | ensembles_abrege.valeur_famille |
| Ex. fonctions — fonction vide (∅,∅,∅) ; application ide | definition | E II.14 | clos | fidele | ensembles_abrege.application_vide ; ense |
| Fonction constante ; élément invariant (f(x)=x) | definition | E II.15 | clos | fidele | ensembles_abrege.est_constante, .est_inv |
| §5 — Coïncidence de f,g dans E ; prolongement (F⊂G) ; s | definition | E II.15 | clos | fidele | ensembles_abrege.coincident,.prolonge,.r |
| f/X=(F∩(X×B),X,B) ; déduite par passage au sous-ensembl | remarque | E II.15 | partiel | ecart_mineur | ensembles_abrege.restriction |
| C54 — Déf. d'une fonction par un terme x↦T ; F(x)=T ; p | critere | E II.15 | clos | fidele | ensembles_fonction_terme ; ensembles_pro |
| Notation x↦T (x∈A,T∈C) ; « la fonction x³ » | notation | E II.16 | clos | fidele | ensembles_abrege.fonction_terme |
| Ex. 2 §6 — première/seconde fonction coordonnée z↦pr₁z, | definition | E II.16 | clos | fidele | ensembles_fonctions_coordonnees |
| Prop. 6 — f:A→B, g:B→C ⇒ g∘f:A→C (application) | proposition | E II.16 | clos | fidele | ensembles_fonctions_composee.composee_fo |
| Déf. 10 — injection / surjection / bijection (biunivoqu | definition | E II.16 | clos | fidele | ensembles_abrege.est_injective, .injecti |
| Ex. §7 — injection/application/diagonale canonique ; pe | definition | E II.17 | partiel | fidele | ensembles_fonctions_complements.est_perm |
| Prop. 7 — f application : f⁻¹ fonction ⟺ f bijective ;  | proposition | E II.17 | partiel | ecart_majeur | ensembles_prop7_9_ii3.reciproque_fonctio |
| Remarque §8 — X⊂f⁻¹⟨f⟨X⟩⟩, f⟨f⁻¹⟨Y⟩⟩⊂Y, égalités si f i | remarque | E II.18 | partiel | fidele | ensembles_image_reciproque_props |
| Prop. 8 — rétraction⇒injective, section⇒surjective ; ré | proposition | E II.18 | partiel | ecart_mineur | ensembles_retractions ; ensembles_retrac |
| Déf. 11 — rétraction/section (inverse à gauche/droite)  | definition | E II.18 | clos | fidele | ensembles_abrege.est_retraction,.est_sec |
| Théorème 1 a–f — composition d'injections/surjections/r | theoreme | E II.19 | partiel | ecart_majeur | ensembles_retractions_props ; ensembles_ |
| Corollaire §8 — g∘f=Id_A, f∘g=Id_B ⇒ f,g bijectives et  | corollaire | E II.18 | partiel | ecart_majeur | ensembles_retractions_props.corollaire_f |
| Prop. 9 a/b — factorisation f=h∘g (g surj) / f=g∘h (g i | proposition | E II.20 | partiel | ecart_majeur |  |
| §9 — Fonction de deux arguments f(x,y) ; application pa | definition | E II.21 | clos | fidele | ensembles_fonctions_complements ; ensemb |
| §9 — Extension canonique (produit) u×v de deux applicat | definition | E II.21 | partiel | ecart_mineur | ensembles_extension_canonique (ii_5_1) |

### II.4 — Réunion et intersection d'une famille d'ensembles (E II.22–30, §4 n°1–8)
_pages : PDF physiques 73–81 (= E II.22 à E II.30), texte principal intégral du §4 n°1 à _  (42 notions, 11 manquantes)

> AUDIT D'EXHAUSTIVITÉ — §II.4 (E II.22–30), texte principal intégral lu page par page (PDF physiques 73–81).

COUVERTURE GLOBALE. Le noyau opératoire du §II.4 est SOLIDEMENT formalisé et TESTÉ (81 tests verts, theorie_ensembles à 22 axiomes préservée) : Déf. 1/2 (réunion/intersection de famille via AXIOME_REUNION_FAM/INTER_FAM, légitimés par S8), Prop. 1 (réindexation surjective, réunion + dual intersection), son Corollaire (famille constante), Prop. 2 (associativité ⋃ et ⋂), Prop. 3 (image directe ⋃/⋂), Prop. 4 (image réciproque ⋂ + réunion), Cor. Prop. 4 (injection), Prop. 5 (De Morgan des familles, 2 directions), Prop. 6 + Cor. (image réciproque/directe d'une différence), toute l'algèbre BINAIRE (commutativité, associativité, distributivité, De Morgan, complément, images directe/réciproque de ∪/∩/−), et les DÉFINITIONS de recouvrement (Déf. 5), plus fin, disjoints/mutuellement disjoints (Déf. 6), partition (Déf. 7), somme (Déf. 8). Fidélité globalement FIDÈLE ou ÉCART MINEUR ; aucun écart MAJEUR (aucun énoncé formalisé ne contredit Bourbaki).

ÉCART STRUCTUREL PRINCIPAL (récurrent, honnête). L'axiome d'intersection encode la Déf. 2 (z∈⋂ ⇔ (∀ι)(ι∈I⇒z∈X_ι)) SANS la clause « z∈E » de la Déf. 3. La DÉF. 3 (intersection d'une famille de parties de E, qui vaut E pour I=∅) est donc une notion DISTINCTE du livre ABSENTE du code. Conséquence en cascade : Prop. 4, son Cor. et Prop. 5-direction-A reçoivent une hypothèse supplémentaire I≠∅ (via α∈I ou (∃ι)(ι∈I)) que Bourbaki n'a pas besoin de poser dans le cadre Déf. 3. Ces hypothèses sont fidèlement déchargées et jamais postulées — écart mineur, contenu mathématique préservé.

POINTS PARTIELS (cas binaire seul, famille générale reportée). Prop. 7 (recollement sur recouvrement) : cœur-valeur clos et fidèle, mais existence/unicité de la fonction recollée seulement au rang |I|=2. Prop. 8, 9, 10 et la Déf. 8 (somme) : machinerie BINAIRE complète et testée, mais la quantification sur une famille (X_ι)_{ι∈I} quelconque (recollement indexé, ⋃ disjointe à I indices, ⋃≃somme générale) est REPORTÉE faute d'infra de récursion/recollement indexé. Le terme somme_famille existe mais sans axiome caractérisant (non exploité). La Prop. 10 binaire reste conditionnée à une hypothèse de bijection non encore prouvée inconditionnellement.

MANQUANTS (notions/remarques nommées du livre absentes). Déf. 3 (intersection de parties, cf. ci-dessus) ; Déf. 4 (⋃/⋂ d'un ensemble d'ensembles 𝔉) ; recouvrement par un ensemble d'ensembles ℜ ; les remarques nommées du n°6 (transitivité de « plus fin », sous-recouvrement, intersection/produit/image/image réciproque de recouvrements) ; remarque préimage-disjointe du n°7 ; Exemple des singletons et bijection partition↔𝔉 ; notations « trace de X sur A » et « adjonction ». La plupart sont faisables et de faible portée mathématique (réductibles aux briques existantes), sauf la Déf. 3 qui est conceptuellement importante (variante d'axiome).

VERDICT. §II.4 = formalisation de très bonne facture pour son cœur algébrique (Prop. 1–6 + algèbre binaire : CLOS, fidèle), avec deux fronts ouverts clairement assumés : (1) la Déf. 3 et son cadre « parties de E » non implémentés (origine des hyp I≠∅ surnuméraires), (2) le passage du rang binaire au rang famille pour le bloc recollement/somme (Prop. 7.2–10). Aucun ÉCART MAJEUR détecté.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Famille d'ensembles / famille de parties (X_ι)_{ι∈I} | definition | E II.22 (n°1) | clos | fidele | ensembles_abrege.valeur_famille |
| Déf. 1 — Réunion d'une famille ⋃_{ι∈I} X_ι | definition | E II.22 (n°1, Déf. 1) | clos | fidele | ensembles_abrege.reunion_famille / AXIOM |
| ⋃_{ι∈∅} X_ι = ∅ (note de la Déf. 1) | remarque | E II.22 (n°1) | clos | fidele | ensembles_familles.reunion_famille_vide |
| Déf. 2 — Intersection d'une famille ⋂_{ι∈I} X_ι (I≠∅) | definition | E II.23 (n°1, Déf. 2) | clos | fidele | ensembles_abrege.inter_famille / AXIOME_ |
| Déf. 3 — Intersection d'une famille de parties de E (⋂  | definition | E II.23 (n°1, Déf. 3) | manquant | non_verifiable |  |
| Prop. 1 — Réindexation par surjection : ⋃_{κ∈K} X_{f(κ) | proposition | E II.23 (n°1, Prop. 1) | clos | fidele | ensembles_chap2_props_restantes.reparam_ |
| Corollaire (Prop. 1) — famille constante X_ι=X_κ : ⋃=X_ | corollaire | E II.23 (n°1, Cor.) | clos | fidele | ensembles_chap2_props_restantes.reunion_ |
| Déf. 4 — Réunion/intersection des ensembles d'un ensemb | definition | E II.23–24 (n°1, Déf. 4) | manquant | non_verifiable |  |
| Monotonie en les termes : (∀ι)(Y_ι⊂X_ι) ⇒ ⋃Y⊂⋃X et (I≠∅ | proposition | E II.24 (n°2) | clos | fidele | ensembles_familles.monotonie_reunion_fam |
| Sous-famille / monotonie en l'indice : J⊂I ⇒ ⋃_{J}⊂⋃_{I | remarque | E II.24 (n°2) | clos | fidele | ensembles_familles_algebre.reunion_inclu |
| Bornes fondamentales ⋂⊂X_α⊂⋃ (propriété de borne sup/in | remarque | E II.22–24 (n°1, propriété fondamentale) | clos | fidele | ensembles_familles_algebre.inter_incluse |
| Prop. 2 — Associativité : I=⋃_λ J_λ ⇒ ⋃_{ι∈I}X_ι = ⋃_{λ | proposition | E II.24 (n°2, Prop. 2) | clos | ecart_mineur | ensembles_familles_assoc_reunion.associa |
| Prop. 3 — Image directe : Γ⟨⋃X_ι⟩=⋃Γ⟨X_ι⟩ et Γ⟨⋂X_ι⟩⊂⋂Γ | proposition | E II.25 (n°3, Prop. 3) | clos | fidele | ensembles_image_recip_famille_ii4.image_ |
| Prop. 4 — Image réciproque d'une intersection : f⁻¹⟨⋂Y_ | proposition | E II.25 (n°3, Prop. 4) | clos | ecart_mineur | ensembles_image_recip_famille_ii4.image_ |
| Corollaire (Prop. 4) — f injection ⇒ f⟨⋂X_ι⟩=⋂f⟨X_ι⟩ | corollaire | E II.25 (n°3, Cor.) | clos | ecart_mineur | ensembles_image_recip_famille_ii4.image_ |
| Prop. 5 — Complémentaire : ∁_E(⋃X_ι)=⋂(∁_E X_ι) et ∁_E( | proposition | E II.26 (n°4, Prop. 5) | clos | ecart_mineur | ensembles_familles_demorgan.de_morgan_in |
| Formules binaires du complémentaire : ∁_E(A∪B)=∁A∩∁B, ∁ | corollaire | E II.27 (n°5) | clos | fidele | ensembles_algebre_booleenne.de_morgan_co |
| Image directe binaire : Γ⟨A∪B⟩=Γ⟨A⟩∪Γ⟨B⟩, Γ⟨A∩B⟩⊂Γ⟨A⟩∩Γ | corollaire | E II.27 (n°5, conséquence Prop. 3) | clos | fidele | ensembles_image_algebre_binaire_ii4.imag |
| Image réciproque binaire : f⁻¹⟨A∪B⟩=f⁻¹⟨A⟩∪f⁻¹⟨B⟩, f⁻¹⟨ | corollaire | E II.27 (n°5, conséquence Prop. 4) | clos | fidele | ensembles_reciproque_reunion_binaire_ii4 |
| Prop. 6 — Image réciproque d'une différence : f⁻¹⟨B−Y⟩= | proposition | E II.27 (n°5, Prop. 6) | clos | fidele | ensembles_image_recip_famille_ii4.image_ |
| Corollaire (Prop. 6) — f injection ⇒ f⟨A−X⟩=f⟨A⟩−f⟨X⟩ | corollaire | E II.27 (n°5, Cor.) | clos | fidele | ensembles_image_difference_injective.ima |
| Trace de X sur A (X∩A) ; trace d'une famille 𝔉 sur A | notation | E II.27 (n°5) | manquant | non_verifiable |  |
| Réunion/intersection binaires A∪B, A∩B (et {x,y,z}, {x, | definition | E II.26 (n°5) | clos | fidele | ensembles_abrege.reunion / intersection  |
| Commutativité binaire A∪B=B∪A, A∩B=B∩A | proposition | E II.26 (n°5) | clos | fidele | ensembles_binaire_commut_ii4.commutativi |
| Associativité binaire A∪(B∪C)=(A∪B)∪C, A∩(B∩C)=(A∩B)∩C | proposition | E II.26 (n°5) | clos | fidele | ensembles_algebre_booleenne.associativit |
| Distributivité binaire A∪(B∩C)=(A∪B)∩(A∪C), A∩(B∪C)=(A∩ | proposition | E II.26 (n°5) | clos | fidele | ensembles_algebre_booleenne.distributivi |
| Déf. 5 — Recouvrement d'un ensemble E ; recouvrement pl | definition | E II.27 (n°6, Déf. 5) | clos | fidele | ensembles_abrege.est_recouvrement / plus |
| Recouvrement par un ensemble d'ensembles ℜ (E⊂⋃_{X∈ℜ}X) | remarque | E II.27 (n°6) | manquant | non_verifiable |  |
| Transitivité de « plus fin » ; sous-recouvrement (J⊂I)  | remarque | E II.28 (n°6) | manquant | non_verifiable |  |
| Prop. 7 — Recollement de fonctions coïncidant sur un re | proposition | E II.28 (n°6, Prop. 7) | partiel | ecart_mineur | ensembles_recollement_props.recollement_ |
| Déf. 6 — Ensembles disjoints (A∩B=∅) ; famille mutuelle | definition | E II.29 (n°7, Déf. 6) | clos | fidele | ensembles_abrege.sont_disjoints / famill |
| Préimage d'une famille disjointe par f est disjointe (f | remarque | E II.29 (n°7) | manquant | non_verifiable |  |
| Prop. 8 — Recollement sur une famille mutuellement disj | proposition | E II.29 (n°7, Prop. 8) | partiel | ecart_mineur | ensembles_recollement_props.recollement_ |
| Déf. 7 — Partition d'un ensemble E (famille de parties  | definition | E II.29 (n°7, Déf. 7) | clos | fidele | ensembles_abrege.est_partition |
| Exemple — ({x})_{x∈A} est une partition de A (A non vid | remarque | E II.29 (n°7, Exemple) | manquant | non_verifiable |  |
| Bijection ι↦X_ι d'une partition en parties non vides su | remarque | E II.29 (n°7) | manquant | non_verifiable |  |
| Prop. 9 — Existence d'une réunion disjointe : tout (X_ι | proposition | E II.29–30 (n°8, Prop. 9) | partiel | ecart_mineur | ensembles_recollement_props.reunion_disj |
| Déf. 8 — Somme d'une famille ∑_{ι∈I} X_ι = ⋃_{ι∈I}(X_ι× | definition | E II.30 (n°8, Déf. 8) | partiel | ecart_mineur | ensembles_abrege.somme_famille (terme) ; |
| Prop. 10 — Réunion d'une famille disjointe ≃ sa somme ( | proposition | E II.30 (n°8, Prop. 10) | partiel | ecart_mineur | ensembles_recollement_props.bijection_ca |
| Adjonction (somme de X et {a}) | notation | E II.30 (n°8) | manquant | non_verifiable |  |

### II.5 — Produit d'une famille d'ensembles (E II.30–II.38, texte principal, scan pages physiques 81–89)
_pages : 81-89 (rendus PNG outils_ia/pdf_pages/ch2_5-0NN.png, r=150, lus un par un). Page_  (44 notions, 15 manquantes)

> Section II.5 (E II.30–38) couvre 7 sous-sections : (1) axiome A3 / P(X) / extension canonique aux parties ; (2) ensemble des applications F^E, 𝓕(E;F), currying ; (3) Déf 1 produit ∏X_ι, projections, diagonale ; (4) produits partiels, pr_J, Prop 5–6 et Cor 1–3 ; (5) associativité (Prop 7) ; (6) distributivité (Prop 8, 9, 10 + corollaires) ; (7) extension aux produits (Déf 2, Prop 11).\n\nÉTAT DU CODE — module bourbaki/ensembles/familles/ii_5_produit_famille (+ ensembles/fonctions/hors_ii_3/ii_5_produit_famille), 90 tests VERTS, theorie_ensembles=22 (invariant respecté). Les DÉFINITIONS et NOTATIONS structurantes sont remarquablement complètes et FIDÈLES : P(X)/A3, F^E/𝓕(E;F), Déf 1 produit, pr_ι, diagonale x̃/Δ, produit partiel/pr_J, Déf 2 extension aux produits — toutes présentes, encodées par axiomes de membership (A3 et AXIOME_PRODUIT_FAM dans les 22 ; le reste dans des théories dédiées hors-22). Théorèmes CLOS et fidèles : monotonie P, membre/projection produit, diagonale⊂E^I, sens direct du Cor 3 (monotonie produit), facteur_temoin (principe de choix τ), Prop 3 currying (équipotence), ∏=∅ si facteur vide.\n\nMANQUANTS (priorité haute) — la sous-section 6 (DISTRIBUTIVITÉ) est le grand trou : Proposition 8 (distributivité ⋃/⋂), Proposition 9 (distributivité du produit sur ⋃/⋂), leurs Corollaires, et la moitié K-indexée générale de la Proposition 10 sont SEULEMENT MENTIONNÉS en commentaire, jamais formalisés (la fonction de choix f∈∏J_λ exigée n'est pas montée). Manquent aussi : bijection canonique F^E≅𝓕(E;F) (§2), Cor de Prop 2, Cor 1 de Prop 6 (pr_α surjective), les remarques de cas particuliers du produit (I=∅, ∏=E^I, I singleton, singletons), et les Remarques 1–2 d'associativité.\n\nÉCARTS MAJEURS (énoncé formalisé ≠ Bourbaki) : Prop 2 (seul le cœur 'composée triple fonctionnelle' est clos, PAS l'injectivité/surjectivité de f↦v∘f∘u) ; Prop 4 (seule la demi-injectivité conditionnelle, pas la bijection ni le bon but ∏X_{u(κ)}) ; Prop 7 associativité (seule la surjectivité conditionnelle) ; Prop 10 (seulement demi-implication conditionnelle + version binaire). Plusieurs Propositions 'présentes' (1, 5, 6, 11) sont en réalité CONDITIONNELLES : leur contenu dur est reçu en hypothèse honnête (rétraction/section ensembliste, prolongement, recollement, composition fonctionnelle) et explicitement REPORTÉ — corrects en logique mais non clos au sens Bourbaki.\n\nNB technique : le fichier ensembles_prop10_inter_produit_ii5.py et son test n'existent plus qu'en .pyc (pycache) — source supprimée, pycache périmé à nettoyer.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Définition 8 — somme d'une famille d'ensembles ∑X_ι = ⋃ | definition | E II.30 (fin §II.4, haut p81) | clos | fidele | ensembles_abrege.somme_famille(f,i) := a |
| Proposition 10 (§II.4) — famille disjointe : bijection  | proposition | E II.30 (fin §II.4, haut p81) | partiel | non_verifiable | ii_4_recollement_somme/ensembles_somme_d |
| Remarque — adjonction de a à X (somme de X et {a}) | remarque | E II.30 (haut p81) | manquant | non_verifiable |  |
| Axiome A3 — (∀X) Coll_Y(Y⊂X) : ensemble des parties P(X | axiome | E II.30 (§5.1, p81) | clos | fidele | ensembles_abrege.AXIOME_PARTIES + partie |
| Monotonie de P : X⊂X' ⇒ P(X)⊂P(X') | remarque | E II.30 (§5.1, p81) | clos | fidele | parties_croissante (ii_5_definitions/ens |
| Extension canonique Γ̂ d'une correspondance aux ensembl | definition | E II.30 (§5.1, p81) | clos | fidele | extension_canonique / graphe_extension_c |
| Proposition 1 — f surjection ⇒ f̂ surjection de P(E) su | proposition | E II.30 (§5.1, p81) | partiel | ecart_mineur | ext_canonique_injective / ext_canonique_ |
| Ensemble des applications : F^E = {G∈P(E×F) / G graphe  | definition | E II.31 (§5.2, p82) | clos | fidele | ensembles_abrege.exposant(e,f) ; applica |
| Bijection canonique G↦(G,E,F) de F^E sur 𝓕(E;F) | notation | E II.31 (§5.2, p82) | manquant | non_verifiable |  |
| Proposition 2 — u surj & v inj ⇒ f↦v∘f∘u injective ; u  | proposition | E II.31 (§5.2, p82) | partiel | ecart_majeur | ensembles_composee_triple_fonctionnelle. |
| Corollaire (de Prop 2) — u,v bijections ⇒ f↦v∘f∘u bijec | corollaire | E II.31 (§5.2, p82) | manquant | non_verifiable |  |
| Proposition 3 — currying : f↦f̃ bijection canonique de  | proposition | E II.31–32 (§5.2, p82–83) | clos | fidele | prop3_currying_bijection (ensembles_curr |
| Bijections canoniques A^(B×C) ≅ (A^B)^C et (A^C)^B (cor | corollaire | E II.32 (§5.2, haut p83) | partiel | ecart_mineur | cardinaux/.../iii_3_5_exposant/prop10_cu |
| Définition 1 — produit ∏_{ι∈I}X_ι = {F fonctionnel / do | definition | E II.32 (§5.3, p83) | clos | fidele | ensembles_abrege.produit_famille(f,i) +  |
| Fonction coordonnée (projection) pr_ι : F↦F(ι), ∏→X_ι | definition | E II.32 (§5.3, p83) | clos | fidele | ensembles_abrege.projection_indice(f,i): |
| Remarque — A ⊂ ∏_{ι∈I} pr_ι⟨A⟩ pour toute partie A du p | remarque | E II.32 (§5.3, p83) | partiel | ecart_mineur | produit_inclus_projections (ii_5_4_proje |
| Notation (x_ι)_{ι∈I} pour les éléments du produit | notation | E II.32 (§5.3, p83) | non_applicable | non_verifiable |  |
| Cas I=∅ : ∏_{ι∈I}X_ι réduit au seul élément ∅ | remarque | E II.32 (§5.3, p83) | manquant | non_verifiable |  |
| Cas facteurs constants : ∏_{ι∈I}X_ι = E^I quand tous X_ | remarque | E II.32 (§5.3, p83) | manquant | non_verifiable |  |
| Cas I={α} : ∏X_ι=X_α^{(α)}, bijection canonique F↦F(α), | remarque | E II.32–33 (§5.3, p83–84) | manquant | non_verifiable |  |
| Cas X_ι={a_ι} singletons : ∏X_ι réduit à l'unique éléme | remarque | E II.33 (§5.3, p84) | manquant | non_verifiable |  |
| Application diagonale x↦x̃ : E→E^I (injection) et diago | definition | E II.33 (§5.3, p84) | clos | fidele | famille_constante / application_diagonal |
| Injectivité de l'application diagonale x↦x̃ | proposition | E II.33 (§5.3, p84) | partiel | ecart_mineur | diagonale_injective (ii_5_2_diagonale/en |
| Proposition 4 — reparamétrage : u bijection K→I ⇒ F↦F∘U | proposition | E II.33 (§5.3, p84) | partiel | ecart_majeur | reparametrage_injectif (ii_5_6_7_algebre |
| Produit partiel ∏_{ι∈J}X_ι (J⊂I) ; projection pr_J(F)=F | definition | E II.33 (§5.4, p84) | clos | fidele | produit_partiel(f,j) / projection_J(ff,j |
| Proposition 5 — X_ι≠∅ ∀ι ⇒ pr_J surjection de ∏_{ι∈I}X_ | proposition | E II.33–34 (§5.4, p84–85) | partiel | ecart_mineur | pr_J_surjective_via_prolongement (ii_5_4 |
| Proposition 6 — X_ι≠∅ ∀ι ; g:J→A avec g(ι)∈X_ι ⇒ prolon | proposition | E II.34 (§5.4, haut p85) | partiel | ecart_mineur | facteur_temoin (ii_5_4_projection_partie |
| Corollaire 1 (de Prop 6) — X_ι≠∅ ∀ι ⇒ pr_α surjection d | corollaire | E II.34 (§5.4, p85) | manquant | non_verifiable |  |
| Corollaire 2 (de Prop 6) — ∏_{ι∈I}X_ι=∅ ⟺ (∃ι)X_ι=∅ | corollaire | E II.34 (§5.4, p85) | partiel | ecart_mineur | produit_vide_si_facteur_vide (ii_5_4_pro |
| Corollaire 3 (de Prop 6) — X_ι⊂Y_ι ∀ι ⇒ ∏X_ι⊂∏Y_ι ; réc | corollaire | E II.34 (§5.4, p85) | partiel | ecart_mineur | produit_monotone_facteurs / facteurs_ega |
| Remarque — 'principe de choix' via τ légitimant 'prenon | remarque | E II.34 (§5.4, p85) | clos | fidele | facteur_temoin (ensembles_produit_props_ |
| Proposition 7 — (J_λ) partition de I ⇒ F↦(pr_{J_λ}F)_λ  | proposition | E II.34–35 (§5.5, p85–86) | partiel | ecart_majeur | associativite_via_inverse (ensembles_pro |
| Remarque 1 (§5.5) — bijection canonique ∏X_ι ≅ (∏_{J_α} | remarque | E II.35 (§5.5, p86) | manquant | non_verifiable |  |
| Remarque 2 (§5.5) — bijection canonique ∏_{ι∈{α,β,γ}}X_ | remarque | E II.35 (§5.5, p86) | manquant | non_verifiable |  |
| Proposition 8 — distributivité ⋃/⋂ : ⋃_λ⋂_{ι∈J_λ}X_{λ,ι | proposition | E II.35–36 (§5.6, p86–87) | manquant | non_verifiable |  |
| Corollaire (de Prop 8) — (⋂X_ι)∪(⋂Y_κ)=⋂_{I×K}(X_ι∪Y_κ) | corollaire | E II.36 (§5.6, p87) | manquant | non_verifiable |  |
| Proposition 9 — distributivité du produit : ∏_λ(⋃_{ι∈J_ | proposition | E II.36–37 (§5.6, p87–88) | manquant | non_verifiable |  |
| Corollaire 1 (de Prop 9) — (X_{λ,ι})_ι partition de X_λ | corollaire | E II.37 (§5.6, p88) | manquant | non_verifiable |  |
| Corollaire 2 (de Prop 9) — (⋃X_ι)×(⋃Y_κ)=⋃_{I×K}(X_ι×Y_ | corollaire | E II.37 (§5.6, p88) | manquant | non_verifiable |  |
| Proposition 10 — ⋂_{κ∈K}(∏_{ι∈I}X_{ι,κ})=∏_{ι∈I}(⋂_{κ∈K | proposition | E II.37 (§5.6, p88) | partiel | ecart_majeur | produit_distrib_inter_membre (ensembles_ |
| Corollaire (de Prop 10) — (∏X_ι)∩(∏Y_ι)=∏(X_ι∩Y_ι) et ( | corollaire | E II.38 (§5.6, p89) | partiel | ecart_mineur | produit_inter_ii5.py (produit_inter, pre |
| Définition 2 — extension canonique aux produits ∏g_ι :  | definition | E II.37–38 (§5.7, p88–89) | clos | fidele | extension_produit / valeur_image_produit |
| Proposition 11 — fonctorialité : ∏(g'_ι∘g_ι)=(∏g'_ι)∘(∏ | proposition | E II.38 (§5.7, p89) | partiel | ecart_mineur | coord_fonctorialite / coord_identite (en |
| Corollaire (de Prop 11) — débute bas p89 | corollaire | E II.38 (§5.7, p89, déborde p90) | non_applicable | non_verifiable |  |

### II.6 — Relations d'équivalence (texte principal, E II.39–II.48)
_pages : PDF physiques 90–99 (= E II.39 à E II.48) ; rendus outils_ia/pdf_pages/ch2_6-090_  (38 notions, 5 manquantes)

> Audit page-par-page de §II.6 (pp. 90-99 = E.II.39-48) confronté au code V9 sous bourbaki/ensembles/ii_6_equivalence/ (+ defs dans ensembles_abrege.py). 100 tests ii_6 passent (0.76s) → tous les théorèmes recensés sont effectivement clos modulo leurs hypothèses. Couverture EXCELLENTE des définitions (symétrique, transitive, équivalence, réflexive-dans, classe Cl_R, quotient, application canonique, compatible, relation déduite/quotient, saturée, saturé, compatible-application, R_f, R_A, image réciproque S∘φ, plus fine, R×R', R/S, θ{x}, E_R) : toutes présentes et FIDÈLES à l'énoncé Bourbaki. Les critères C55, C56, C57 sont formalisés fidèlement (clos mod. hypothèses honnêtes). MANQUES principaux : (1) Proposition 1 (E.II.41) n'est formalisée QUE dans le sens RÉCIPROQUE et seulement pour (b) symétrie + (c) transitivité ; le sens DIRECT (Γ équivalence ⟹ a,b,c) et le volet (a) réflexivité Δ⊂G ⟺ R réflexive sont ABSENTS — donc l'équivalence « Γ équivalence ⟺ a∧b∧c » n'est PAS établie. (2) Le terme `quotient(g,e)`=E/R et `application_canonique(g,e)`=p sont des TERMES OPAQUES (app(...) sans axiome de membership clos) : E/R n'a pas d'axiome de membership prouvant C=Cl_R(x), p n'est utilisé qu'à travers AXIOME_APPCANON ; la décomposition canonique f=i∘b∘p reste un PRÉDICAT (factorisation effective reportée, seule l'injectivité de b au niveau valeurs est prouvée). (3) Plusieurs résultats du texte sont des REMARQUES/EXEMPLES non nommés (partition E/R, système de représentants effectif S↔E/R, traces de R_A, exemple espaces vectoriels §6.9) : NOTIONS définies mais THÉORÈMES durs reportés. Aucun ÉCART MAJEUR de fidélité détecté : tous les énoncés formalisés coïncident avec Bourbaki ; les écarts sont des manques (sens non couverts) ou des présentations (graphe vs relation, hypothèses honnêtes laissées explicites), jamais un énoncé déformé. theorie_ensembles reste à 22 axiomes.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Relation symétrique (par rapport à x,y) | definition | E II.39 (p.90) | clos | fidele | ensembles_abrege.est_symetrique |
| Relation transitive (par rapport à x,y) | definition | E II.39 (p.90) | clos | fidele | ensembles_abrege.est_transitive |
| Relation d'équivalence (symétrique et transitive) | definition | E II.40 (p.91) | clos | fidele | ensembles_abrege.est_relation_equivalenc |
| Relation réflexive dans E ; relation d'équivalence dans | definition | E II.40 (p.91) | clos | fidele | ensembles_abrege.est_reflexive_dans / es |
| Équivalence (correspondance) admettant un graphe | definition | E II.40 (p.91) | partiel | ecart_mineur | ensembles_abrege.rel_graphe (relation as |
| Exemples de relations d'équivalence (x=y ; x=y et x∈E ; | remarque | E II.40-41 (p.91-92) | non_applicable | non_verifiable |  |
| Proposition 1 — caractérisation d'une équivalence par a | proposition | E II.41 (p.92) | partiel | ecart_majeur | ii_6_equivalence.ensembles_proposition1_ |
| Relation d'équivalence associée à une fonction f (R_f : | definition | E II.41 (p.92) | clos | fidele | ensembles_abrege.relation_associee_fonct |
| Classe d'équivalence Cl_R(x)=G⟨{x}⟩ ; représentant | definition | E II.41 (p.92) | clos | fidele | ensembles_abrege.classe ; ii_6_equivalen |
| Ensemble quotient E/R ; application canonique p:E→E/R | definition | E II.41 (p.92) | partiel | ecart_mineur | ensembles_abrege.quotient (app 'quotient |
| Critère C55 — p(x)=p(y) ⟺ R{x,y} | critere | E II.41-42 (p.92-93) | clos | fidele | ii_6_equivalence.ensembles_projection_c5 |
| Section de E pour R (section associée à l'application c | definition | E II.42 (p.93) | partiel | ecart_mineur | ii_6_equivalence.ensembles_quotient_comp |
| Partition de E ; les classes partitionnent E (égales ou | proposition | E II.42 (p.93) | clos | fidele | ii_6_equivalence.ensembles_quotient_prop |
| Système de représentants des classes suivant R | definition | E II.42 (p.93) | partiel | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Relation P{x} compatible avec une relation d'équivalenc | definition | E II.42 (p.93) | clos | fidele | ensembles_abrege.est_compatible |
| Relation P'{t} déduite de P par passage au quotient (t∈ | definition | E II.43 (p.94) | clos | fidele | ensembles_abrege.relation_quotient |
| Critère C56 — (∃x)(x∈t et P{x}) ⟺ (∀x)((x∈t)⇒P{x}) sous | critere | E II.43 (p.94) | clos | fidele | ii_6_equivalence.ensembles_quotient_c56_ |
| Partie A saturée pour R | definition | E II.43 (p.94) | clos | fidele | ensembles_abrege.est_saturee ; ii_6_4_sa |
| Saturé Ã = p⁻¹⟨p⟨A⟩⟩ ; toute image réciproque p⁻¹⟨B⟩ es | proposition | E II.43-44 (p.94-95) | clos | fidele | ensembles_abrege.sature ; ii_6_4_saturee |
| Stabilité saturation par réunion/intersection/complémen | remarque | E II.43-44 (p.94-95) | manquant | non_verifiable |  |
| Application f compatible avec une relation d'équivalenc | definition | E II.44 (p.95) | clos | fidele | ensembles_abrege.est_compatible_applicat |
| Critère C57 — f compatible ⟺ f=h∘g ; h uniquement déter | critere | E II.44 (p.95) | partiel | fidele | ii_6_equivalence.ensembles_quotient_c56_ |
| Application h déduite de f par passage au quotient (h=f | definition | E II.44 (p.95) | clos | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Décomposition canonique f = j∘k∘g (i∘b∘p) | definition | E II.44 (p.95) | partiel | fidele | ii_6_5_decomposition.ensembles_decomposi |
| Application f compatible avec R et S (x≡x'(R)⇒f(x)≡f(x' | definition | E II.44-45 (p.95-96) | clos | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Application h déduite de f par passage aux quotients su | definition | E II.45 (p.96) | clos | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Image réciproque S∘φ d'une relation d'équivalence par u | definition | E II.45 (p.96) | clos | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Relation induite R_A par R sur une partie A (note R_A) | definition | E II.45 (p.96) | clos | fidele | ii_6_equivalence.ensembles_quotient_comp |
| Relation plus fine / moins fine (S plus fine que R := S | definition | E II.46 (p.97) | clos | fidele | ensembles_abrege.plus_fine ; ii_6_4_satu |
| Quotient R/S de deux relations d'équivalence (S plus fi | definition | E II.46 (p.97) | partiel | fidele | ii_6_5_decomposition.ensembles_decomposi |
| Produit R×R' de deux relations d'équivalence | definition | E II.46 (p.97) | clos | fidele | ensembles_abrege.relation_produit ; ii_6 |
| Les classes de R×R' sont les produits de classes ; cano | proposition | E II.46-47 (p.97-98) | manquant | non_verifiable |  |
| Remarque — Q{u} compatible avec R×R' ⟺ P{x,x'} compatib | remarque | E II.47 (p.98) | manquant | non_verifiable |  |
| Classe d'objets équivalents θ{x}=τ_y(R{x,y}) (R sans gr | definition | E II.47 (p.98) | clos | fidele | ensembles_abrege.classe_objets ; ii_6_eq |
| Ensemble Θ (E_R) des classes d'objets équivalents (sous | definition | E II.47-48 (p.98-99) | partiel | ecart_mineur | ii_6_equivalence.ensembles_quotient_comp |
| Condition (1) ⟹ relation ∃x(R{x,x} et z=θ{x}) collectiv | critere | E II.48 (p.99) | manquant | non_verifiable |  |
| Bijection Θ→F/R justifiant la terminologie (R équivalen | proposition | E II.48 (p.99) | manquant | non_verifiable |  |
