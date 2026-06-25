# Couverture CHAP_III -- audit page-par-page du texte principal (2026-06-24)

Chaque notion du livre (texte principal) confrontee au code V9. Source = PDF lu page par page.

## Synthese (237 notions recensees)

**Statut code** : clos 98 | partiel 72 | **manquant 60** | n/a 7

**Fidelite** : fidele 93 | ecart mineur 46 | **ecart majeur 31** | non-verif 67

## Ecarts MAJEURS (enonce formalise != Bourbaki) -- priorite

- **Chapitre III, §1 — Relations d** -- Proposition 7 — sup par recouvrement (J_λ) : sup_I = sup_λ(sup_{J_λ}) (E III.1.11) : Seul le CŒUR binaire (m majore A∪B ⟺ majore A et majore B) est certifié ; le cas général à recouvrement quelconque (J_λ)_{λ∈L} n'est pas prouvé.
- **Chapitre III, §1 — Relations d** -- Proposition 8 — sup dans un produit : sup A = (sup A_ι)_ι (E III.1.11-12) : Cœur 'majorant pointwise' traité ; résidu explicite signalé dans le docstring — énoncé complet sup A=(sup pr_ι A) non clos.
- **III.2 Ensembles bien ordonnés ** -- Proposition 2 — E* (segments de E) bien ordonné par inclusion ; x↦S_x  (E III.16) : Bourbaki : x↦S_x est un ISOMORPHISME de E sur l'ensemble des segments propres, et E* est bien ordonné par ⊂. Le dépôt prouve la brique cruciale (monotonie stricte + réciproque = bijection croissante s
- **III.2 Ensembles bien ordonnés ** -- Proposition 3 — Famille (X_ι) où chaque paire X_ι,X_κ : l'un segment d (E III.16) : Bourbaki donne l'existence/unicité d'un ordre sur la réunion d'une famille de bons ordres emboîtés en segments + bon ordre de la réunion + structure des segments. Le dépôt couvre la fusion de DEUX bon
- **III.2 Ensembles bien ordonnés ** -- Lemme 1 — Famille filtrante (X_α,⊂) à ordres induits cohérents ⇒ ordre (E III.17) : Lemme général de recollement d'ordres sur une réunion filtrante (G=⋃G_α). Le dépôt l'utilise sous forme binaire/abstraite (fusion_hyp, témoin commun) pour la trichotomie ; le lemme indexé général n'es
- **III.2 Ensembles bien ordonnés ** -- Théorème 1 (Zermelo) — Sur tout ensemble E il existe un bon ordre (E III.20) : ÉNONCÉ fidèle (« tout ensemble admet un bon ordre »). Mais PREUVE non fidèle au livre : Bourbaki déduit Th1 de Lemme 3 avec p(X)=τ_x(x∈E∖X) ; le dépôt le dérive de Zorn/Bourbaki–Witt par le poset des 
- **III.2 Ensembles bien ordonnés ** -- Théorème 2 — Tout ensemble ordonné inductif possède un élément maximal (E III.20) : Énoncé : (est_ordre ∧ est_inductif ∧ E≠∅) ⇒ ∃m maximal. NB Bourbaki Th2 ne suppose pas E≠∅ explicitement (un inductif est non vide car ∅ totalement ordonné a un majorant) — léger écart d'hypothèse. Pr
- **III.3 — Ensembles équipotents.** -- Définition 3 — produit cardinal ∏a_ι et somme cardinale ∑a_ι (cardinal (E III.25 (§III.3.3)) : Bourbaki définit la somme/produit d'une FAMILLE indexée (a_ι)_{ι∈I}. Le code ne formalise QUE le cas BINAIRE (a·b=Card(a×b), a+b=Card(a⊔b)). Le cas famille générale ∑_ι/∏_ι manque entièrement (dossier
- **III.3 — Ensembles équipotents.** -- Proposition 4 — Card(produit)=produit cardinal, Card(somme)=somme card (E III.26 (§III.3.3)) : Bourbaki : Card(P)=∏a_ι, Card(S)=∑a_ι pour une famille. Au niveau binaire c'est la définition même (Card(a⊔b)=a+b). Le cas famille manque. Écart majeur (familles).
- **III.3 — Ensembles équipotents.** -- Proposition 5 — a) invariance par bijection d'indices ; b) associativi (E III.26 (§III.3.3)) : Bourbaki 5a/5b/5c portent sur des FAMILLES (réindexation, partition, distributivité indexée). Le code prouve UNIQUEMENT les cas binaires/ternaires : (A⊔B)⊔C≅A⊔(B⊔C), A×(B⊔C)≅(A×B)⊔(A×C), commutativité
- **III.3 — Ensembles équipotents.** -- Proposition 6 — a_ι=0 hors J ⇒ ∑=∑_J ; a_ι=1 hors K ⇒ ∏=∏_K (éliminati (E III.27 (§III.3.4)) : Bourbaki : version FAMILLE (somme/produit insensibles aux termes 0/1). Code : seulement cas binaires Card(∅⊔B)=Card B et Card(A×{∅})=Card A. Cas famille manque. Écart majeur.
- **III.3 — Ensembles équipotents.** -- Proposition 7 — ∏a_ι ≠ 0 ⟺ a_ι≠0 pour tout ι (E III.28 (§III.3.4)) : Code prouve la forme BINAIRE inconditionnelle : a·b=0 ⟺ (a=0 ou b=0), via produit_vide (E.II.34). Fidèle pour 2 indices, mais Prop.7 Bourbaki est sur une famille quelconque. Écart majeur (familles).
- **III.3 — Ensembles équipotents.** -- Proposition 10 — Card(I)=b, a_ι=a ⇒ a^b = ∏_{ι∈I} a_ι (E III.28 (§III.3.5)) : Énoncé exact Bourbaki (a^b = produit d'une famille constante indexée par I, Card I=b) : NON formalisé tel quel (produit de famille manquant). Le dossier prop10_currying traite surtout le Cor.3 (curryi
- **III.3 — Ensembles équipotents.** -- Corollaire 1 (de Prop.10) — a^(∑b_ι) = ∏ a^{b_ι} (E III.28 (§III.3.5)) : Cas BINAIRE a^(b+c)=a^b·a^c CLOS (prop9_close). Cas famille a^(∑b_ι)=∏a^{b_ι} manquant. Écart majeur (familles).
- **III.3 — Ensembles équipotents.** -- Corollaire 2 (de Prop.10) — (∏a_ι)^b = ∏ a_ι^b (E III.29 (§III.3.5)) : Forme ensembliste 𝓕(B;∏A_ι)≅∏𝓕(B;A_ι) visée via familles indexées + paramétrage opaque valeur_famille ; CRUX (bijection) reporté/conditionnel. Énoncé famille non clos. Écart majeur.
- **III.3 — Ensembles équipotents.** -- Corollaire 3 (de Prop.10) — a^(bc) = (a^b)^c (currying) (E III.29 (§III.3.5)) : Bourbaki : a^(bc)=(a^b)^c. Code : les deux termes Card(𝓕(B×C;A)) et Card(𝓕(C;𝓕(B;A))) construits, mais la bijection de CURRYING est explicitement REPORTÉE NON RÉSOLUE (verrou double niveau de fonction
- **III.3 — Ensembles équipotents.** -- Proposition 14 — a_ι≤b_ι pour tout ι ⇒ ∑a_ι≤∑b_ι et ∏a_ι≤∏b_ι (monoton (E III.30 (§III.3.6)) : Code : monotonie BINAIRE close (A≤A₁ et B≤B₁ ⇒ A⊔B≤A₁⊔B₁, A×B≤A₁×B₁ ; versions Card aussi). Bourbaki Prop.14 porte sur des FAMILLES de même I. Cas famille manquant. Écart majeur (binaire seulement).
- **III.3 — Ensembles équipotents.** -- Corollaire 1 (de Prop.14) — ∑_J a_ι≤∑a_ι ; et ∏_J≤∏ si a_ι≠0 hors J (E III.30 (§III.3.6)) : Code : bornes BINAIRES (A≤A⊔B, B≤A⊔B, A≤A×B si B≠∅). C'est le cas à 2 indices du Cor.1 (monotonie par restriction de partie J). Cas famille manquant. Écart majeur.
- **III.5 — Calcul sur les entiers** -- Proposition 1 — Pour une famille finie d'entiers (a_i), les cardinaux  (E III.35 / E III.36) : Bourbaki : somme ET produit d'une famille FINIE INDEXÉE d'entiers sont des entiers (récurrence sur Card I, base Σ sur partition Prop5). Code : seul le cas BINAIRE clos (a+b entier, a·b entier via récu
- **III.5 — Calcul sur les entiers** -- Proposition 3 — a_i≤b_i et a_j<b_j pour un j ⇒ Σa_i<Σb_i ; si b_i>0 al (E III.36) : Bourbaki : monotonie STRICTE pour familles FINIES INDEXÉES. Code : versions binaires (somme/produit strict monotone à deux termes). La forme famille n'est pas formalisée. Écart majeur (binaire seul).
- **III.5 — Calcul sur les entiers** -- Théorème 1 (division euclidienne) — b>0 ⇒ existence et unicité de q,r  (E III.39) : Th.1 NON PROUVÉ. Seuls des termes opaques (quotient_division, reste_division, couple divmod) et la FORMULE condition a=bq+r ∧ r<b (avec b·q+r codé app opaque 'plus_ent'/'prod_ent'). Existence/unicité 
- **III.5 — Calcul sur les entiers** -- Proposition 9 (principe des bergers) — f surjection E→F à fibres de mê (E III.41) : Forme PLEINE non formalisée (manque somme cardinale famille indexée, Prop5b partition, Prop6 Cor2, recollement E≅⊔fibres). Seul le CŒUR BINAIRE clos : Card(E0⊔E1)=a+a (deux fibres). Même la liaison a+
- **III.6 Ensembles infinis (texte** -- Theoreme 2 (Hessenberg) — pour tout cardinal infini a, a^2 = a (E III.48) : GROS CHANTIER (CLAUDE.md). Assemblages multiples : hessenberg_vrai monte a2=a NON-vacuousement mais SOUS l'hypothese-carre Card(S0xS0)=Card S0 non dechargee + deux residus de Zorn ; hessenberg_a_carre
- **III.6 Ensembles infinis (texte** -- Lemme 1 — tout ensemble infini E contient un ensemble equipotent a N (E III.47) : Aucun fichier prouvant Lemme 1 a 0 hyp ; cite comme RESIDU non decharge bloquant inductivite et frame-membership de Th.2. Implementation manquante en tant que theoreme clos. PARTIEL / ecart majeur (no
- **III.6 Ensembles infinis (texte** -- Corollaire 1 — si a cardinal infini, a^n = a pour tout entier n>=1 (E III.49) : « evident par recurrence sur n » a partir de Th.2. Th.2 non clos inconditionnellement et recurrence Prop.1 III.5 manque => a^n=a non prouve. Seule la brique a^(n+1)=a^n.a est close. PARTIEL/ecart maje
- **III.6 Ensembles infinis (texte** -- Proposition 1 — partie / produit fini / reunion d'une suite d'ensemble (E III.49) : Trois assertions : (i) partie d'un denombrable « evidente », formalisee conditionnellement (transport REPORTE en hyp) ; (ii) produit fini et (iii) reunion d'une suite — Bourbaki les fait resulter des 
- **III.6 Ensembles infinis (texte** -- Proposition 2 — tout ensemble infini denombrable E est equipotent a N (E III.49) : Preuve Bourbaki : Card E<=Card N (definition) et Card N<=Card E car E infini (Lemme 1, p.48) -> Cantor-Bernstein. Depend du Lemme 1 (non clos). Aucun theoreme nomme prouvant Eq(E,N) a 0 hyp. PARTIEL/e
- **III.7 Limites projectives et l** -- Corollaire 1 de la Prop. 1 : système projectif d'applications (u_α:E_α (E III.53) : Définition du système d'applications + terme lim_proj_applications introduits. EXISTENCE/UNICITÉ de u=lim← u_α (cœur du Cor.1) REPORTÉE ; seul le sens facile/diagramme pointwise prouvé.
- **III.7 Limites projectives et l** -- Proposition 3 : J cofinale filtrante ⇒ application canonique g:E→E' BI (E III.55-56) : INJECTIVITÉ de g prouvée POINTWISE sous témoin cofinal (pr_λ x=pr_λ x' pour λ≤α∈J), et g bien définie (sens facile). BIJECTIVITÉ complète (généralisation ∀λ + SURJECTIVITÉ) REPORTÉE. Cas ω (lim←=E_ω) 
- **III.7 Limites projectives et l** -- Double limite projective : système relatif à I×L, formules (11)-(15),  (E III.56-57) : Prouvé le PAS-CLÉ pointwise : (14)+(15) ⇒ condition (1) du système I×L (recollement via f_λμ_αβ=f_λ_αβ∘h_λμ_β, hyp (11) portée). La BIJECTION CANONIQUE (16) lim←_{α,λ}=lim←_λ lim←_α elle-même REPORTÉE
- **III.7 Limites projectives et l** -- Corollaire 1 Prop. 6 : système inductif d'applications (u_α:E_α→F_α) ⇒ (E III.63) : Définition + terme lim_ind_applications introduits ; diagramme propagé pointwise. EXISTENCE/UNICITÉ de u REPORTÉE.

## Notions MANQUANTES (dans le livre, pas closes dans le code)

### Chapitre III, §1 — Relations d'ordre, ensembles ordonnés (E 
- [proposition] Proposition 1 (Γ ordre ⟺ G∘G=G et G∩G⁻¹=Δ) (E III.1.2) -- Caractérisation du graphe d'un ordre par G∘G=G et G∩G⁻¹=Δ. Non formalisée (le projet utilise la définition par prédicats réflexif/antisym/tr
- [proposition] Relation d'ordre associée à un préordre (passage au quotient R'{X,Y}) (E III.1.3) -- Construction E/S et ordre associé sur le quotient. Non formalisée.
- [remarque] Ordre sur F^E / F(E;F) : f≤g ⟺ (∀x)f(x)≤g(x) (E III.1.6) -- Ordre point-par-point sur les applications E→F (cas particulier de l'ordre produit). Pas de formalisation dédiée nommée.
- [definition] Famille de parties croissante/décroissante (ι↦X_ι croissante dans P(E)) (E III.1.7) -- Notion de famille de parties monotone indexée par I ordonné. Non formalisée explicitement.
- [proposition] Proposition 2 (u,v décroissantes, v(u(x))≥x, u(v(x'))≥x' ⇒ u∘v∘u=u, v∘u∘v=v) (E III.1.7-8) -- Identités de type connexion de Galois. NON formalisée — manque réel.
- [definition] Partie minorée / majorée / bornée ; application minorée/majorée/bornée (E III.1.9-10) -- Les prédicats 'X minorée/majorée/bornée' (ensemble des minorants/majorants non vide) et l'extension aux applications f(A) ne sont PAS défini
- [proposition] X admet plus petit élément ⟺ ∃ minorant de X appartenant à X (E III.1.10) -- Caractérisation (minorant ∈ X) non formalisée comme théorème nommé.
- [corollaire] Corollaire (Prop 7) — sup famille double sup_{(λ,μ)} = sup_μ(sup_λ) (E III.1.11) -- Forme double indices non formalisée.
- [remarque] Remarque — réticulé ⇒ filtrant à droite et à gauche (E III.1.13) -- Implication réticulé⇒filtrant non prouvée comme théorème nommé.
- [remarque] Remarque — totalement ordonné ⇒ réticulé, a fortiori filtrant des deux côtés (E III.1.14) -- Non formalisée.
- [proposition] Proposition 12 — caractérisation de sup X dans un ensemble totalement ordonné (b (E III.1.14) -- NON formalisée — manque réel.

### III.2 Ensembles bien ordonnés (E III.14–E III.21)
- [remarque] Toute partie majorée d'un bien ordonné admet une borne supérieure (E III.15) -- Remarque non numérotée après Déf 1 (« toute partie A majorée admet une borne sup »). Pas de théorème dédié repéré dans iii_2_bon_ordre.
- [remarque] Réunion des S_x = E (si pas de plus grand élt) ou E∖{b} (E III.16) -- Remarque préparatoire à Prop 2. Pas de théorème dédié repéré.
- [proposition] Lemme 3 — ∃ partie M et bon ordre Γ avec S_x∈𝔖, p(S_x)=x, M∉𝔖 (p:𝔖→E, p(X)∉X) (E III.19) -- Lemme-clé de la preuve Bourbaki de Zermelo/Th2 (construction de M par p(X)∉X). NON implémenté : le dépôt prouve Zermelo et Zorn via Bourbaki
- [proposition] Proposition 4 — E ordonné dont toute partie bien ordonnée est majorée ⇒ E admet  (E III.20) -- Le résultat général dont Th2 est cas particulier (via majorant strict p(S) et Lemme 3). Décrit dans la narration de zorn.py mais NON prouvé 
- [corollaire] Corollaire 1 — E inductif, a∈E ⇒ ∃ maximal m≥a (E III.21) -- Mentionné dans la docstring narrative de zorn.py mais pas de théorème clos (l'ensemble F des x≥a est inductif, maximal de F = maximal de E).
- [corollaire] Corollaire 2 — 𝔉 ensemble de parties fermé par réunion (resp. intersection) de s (E III.21) -- Forme usuelle de Zorn pour ensembles de parties. Mentionné en narration, non formalisé comme théorème clos.

### III.3 — Ensembles équipotents. Cardinaux (E III.22–29, sous-
- [corollaire] Corollaire 2 (de Prop.6) — I équipotent à b ⇒ ab=∑_I a et b=∑_I 1 (E III.27 (§III.3.4)) -- « ab = ∑_{ι∈I} a (a_ι=a) et b = ∑_{ι∈I} 1 (c_ι=1) ». Repose sur la somme d'une FAMILLE constante = produit ; pas trouvé dans le code (cas fa

### III.4 — Entiers naturels, ensembles finis (E III.30 à E III.
- [proposition] Proposition 2 (suite) — a<n ⇔ a≤m (où n=m+1) (E III.31) -- L'équivalence a<n ⇔ a≤m (n=m+1) n'est PAS formalisée comme théorème. Énoncé composite de Prop.2 non assemblé intégralement. À AJOUTER pour f
- [corollaire] Corollaire 2 — X⊂E, X≠E, E fini ⇒ Card X < Card E (E III.31) -- Seul l'ÉNONCÉ-cible (cor2_partie_stricte_card_strict) et la moitié asymétrie (inf_strict_exclut_reciproque, a<b⇒¬b≤a, CLOS) sont là. La stri
- [remarque] Remarque E III.33 — variantes de récurrence : (1) forte S{n}=(∀p<n)R{p}; (2) à p (E III.33) -- AUCUNE des 4 variantes (récurrence forte, à partir de k, limitée à un intervalle a≤n≤b, descendante) n'est formalisée. Seule la récurrence d

### III.5 — Calcul sur les entiers (E III.35–E III.43)
- [corollaire] Corollaire 1 (Prop1) — La réunion d'une famille finie d'ensembles finis est un e (E III.36) -- Aucun théorème dédié 'réunion famille finie d'ensembles finis ⇒ fini'. Seule la somme disjointe binaire est close. Manquant.
- [corollaire] Corollaire 2 (Prop1) — Le produit d'une famille finie d'ensembles finis est un e (E III.36) -- Pas de résultat 'produit d'une famille finie d'ensembles finis est fini'. Manquant.
- [corollaire] Corollaire 4 (Prop1) — L'ensemble des parties d'un ensemble fini est fini (card  (E III.36) -- Pas trouvé dans iii_5. Note : 2^Card existe côté cardinaux (prop12_powerset) mais le Cor.4 'P(E) fini pour E fini' n'est pas assemblé dans i
- [corollaire] Corollaire 1 (Prop3) — a<a' et b>0 ⇒ a^b<a'^b (E III.37) -- Monotonie stricte de la base de l'exponentielle entière non trouvée dans iii_5. (NB côté cardinaux il existe exposant_monotone conditionnels
- [corollaire] Corollaire 2 (Prop3) — a>1 et b<b' ⇒ a^b<a^{b'} (E III.37) -- Monotonie stricte de l'exposant non assemblée pour les entiers dans iii_5. Manquant.
- [theoreme] Théorème 1 (division euclidienne) — b>0 ⇒ existence et unicité de q,r avec a=bq+ (E III.39) -- Th.1 NON PROUVÉ. Seuls des termes opaques (quotient_division, reste_division, couple divmod) et la FORMULE condition a=bq+r ∧ r<b (avec b·q+
- [proposition] Proposition 8 — f_k(r)=Σ r_h b^{k-h-1} est un isomorphisme de E_k (produit lexic (E III.40) -- NON formalisée (récurrence sur k, produit lexicographique). Trou structurel : dossier dédié vide. Manquant.
- [proposition] Proposition 10 — n!/(n−m)! est le nombre des applications injectives d'un ensemb (E III.41 / E III.42) -- Non formalisée (récurrence sur m, principe des bergers). Aucun module. Manquant.
- [corollaire] Corollaire (Prop10) — Le nombre de permutations d'un ensemble fini à n éléments  (E III.42) -- Non formalisé. Manquant.
- [proposition] Proposition 11 — nombre de recouvrements partitionnés (X_i) avec Card X_i=p_i es (E III.42) -- Non formalisée (Prop10 + principe des bergers). Manquant.
- [corollaire] Corollaire 2 (Prop11) — nombre d'applications strictement croissantes de E (p él (E III.43) -- Non formalisé. Manquant.
- [proposition] Proposition 12 — Σ_p C(n,p) = 2^n (E III.43) -- Non formalisée pour les entiers (relation binomiale). NB : 2^Card=Card P(E) existe côté cardinaux (prop12_powerset) mais la somme Σ C(n,p)=2
- [proposition] Proposition 13 (formule de Pascal) — C(n+1,p+1)=C(n,p+1)+C(n,p) (E III.43) -- Non formalisée. Manquant (explicitement reporté dans le docstring de coefficient_binomial).
- [proposition] Proposition 14 — nombre a_n de couples (i,j) avec 1≤i≤j≤n est n(n+1)/2 ; b_n ave (E III.43) -- Non formalisée (énoncé entamé en bas de p.146, preuve hors plage lue). Manquant.

### III.6 Ensembles infinis (texte principal, E III.45-49 ; sous
- [definition] Sous-famille extraite d'une suite (« suite extraite ») (E III.46) -- « Toute sous-famille d'une suite est une suite, dite extraite. » Aucune definition est_suite_extraite. Trou mineur (notion derivee).
- [definition] Suites ne differant que par l'ordre des termes (permutation des indices) (E III.46) -- « (x_n),(y_n) de meme ensemble d'indices ne different que par l'ordre des termes s'il existe une permutation f telle que x_{f(n)}=y_n ». Non
- [definition] Suite multiple (p-uple, double, triple) ; suite rangee dans l'ordre defini par f (E III.46) -- « suite multiple = famille indexee par une partie d'un produit N^p » ; « ranger dans l'ordre defini par f via une bijection f:N->I ». Aucune
- [remarque] Exemple 1 — recurrence f(0)=a, f(n+1)=g(f(n)) (g:E->E) (E III.47) -- Application de C63 a S{u}=g(u). Pas d'instance close nommee. Trou mineur (exemple).
- [remarque] Exemple 2 — n-eme iteree f^n d'une application (f^0=e, f^{n+1}=f o f^n) (E III.47) -- Iteree n-eme via C63 (S{u}=f o u). Non formalisee comme objet nomme. Trou mineur (exemple).
- [remarque] Exemple 3 — iteration P^n(E) de l'ensemble des parties (E III.47) -- P^0(E)=E, P^{n+1}(E)=P(P^n(E)) via C63. Non formalise. Trou mineur (exemple).
- [remarque] Remarque — recurrence limitee (f definie seulement sur [0,p+1]) (E III.47) -- Cas g:A->E partielle ; p plus grand entier tel que f([0,p]) inclus A. Non formalise. Trou mineur.
- [corollaire] Corollaire 2 — produit d'une famille finie de cardinaux non nuls dont le plus gr (E III.49) -- Repose sur Cor.1 (b<=a^n=a) et b>=a. Aucun fichier dedie ; depend de Cor.1 non clos. MANQUANT.
- [corollaire] Corollaire 3 — somme d'une famille (a_i) de cardinaux <=a indexee par I de cardi (E III.49) -- Somme_i a_i <= a.b <= a^2 = a (depend Th.2). Aucun fichier dedie. MANQUANT.
- [corollaire] Corollaire 4 — a, b non nuls dont l'un infini : a.b = a + b = sup(a,b) (E III.49) -- Resulte de Cor.2 et Cor.3. Aucun fichier dedie. MANQUANT.

### III.7 Limites projectives et limites inductives (E III.51–II
- [remarque] Exemple 2 : I filtrant, E_α=F, f_αβ=Id ⇒ lim← = diagonale Δ de F^I (E III.52) -- Aucune trace de l'identification lim←=diagonale dans les modules III.7.
- [proposition] Proposition 2 : (u_α) sys. proj. d'applications ⇒ u⁻¹(x')=lim← u_α⁻¹(x'_α) (E III.54) -- L'identité d'ensembles u⁻¹(x')=lim← u_α⁻¹(x'_α) REPORTÉE (image réciproque effective absente). Seules les NOTIONS de fibres/système image-ré
- [remarque] Relation (9) u(E)⊂lim← u_α(E_α) (images forment un système projectif de parties, (E III.55) -- Inclusion (9) non formalisée.
- [remarque] Remarques 1-3 §III.7.3 : E'_α=f_α(E) système de parties avec lim← E'_α=E, formul (E III.55-56) -- Formule (10) E'_α=f_α(E)⊂∩_{β≥α} f_αβ(E_β) et Remarques non formalisées.
- [corollaire] Corollaire 1 Prop. 4 : (17) lim←_{α,λ} u_α^λ=lim←_λ(lim←_α u_α^λ) (E III.57) -- Non formalisé (« vérification analogue » à Prop.4 ; même obstacle bijection canonique).
- [corollaire] Corollaire 2 Prop. 4 : (18) lim←_α ∏_λ E_α^λ=∏_λ(lim←_α E_α^λ) (commutation lim← (E III.57) -- Non formalisé.
- [proposition] Proposition 5 : I filtrant + partie cofinale dénombrable + f_αβ surjectives ⇒ f_ (E III.58) -- REPORTÉ (récurrence sur partie cofinale dénombrable + relèvement). Seule l'hypothèse « système projectif filtrant » nommée.
- [definition] Conditions (i)(ii)(ii') sur les ensembles S_α de parties (intersection stable ;  (E III.58) -- Conditions (i),(ii),(ii') du Théorème 1 non formalisées comme prédicats.
- [theoreme] Théorème 1 : I filtrant, S_α (i)(ii), (iii)(iv) ⇒ a) f_α(E)=∩_{β≥α} f_αβ(E_β) ;  (E III.58-60) -- Le théorème central de non-vacuité (E III.58, formules (19)(20)(21)) entièrement REPORTÉ (propriété d'intersection finie, Σ inductif/Zorn). 
- [remarque] Exemples §III.7.5 (germes d'applications V_α→B ; E_α=F, g_βα=Id ⇒ bijection lim→ (E III.61-62) -- Exemples non formalisés.
- [proposition] Lemme 1 : tout système fini d'éléments de E=lim→ se relève dans un E_α ; séparat (E III.62) -- Lemme de relèvement fini (cœur de la théorie inductive) REPORTÉ ; nécessite le quotient G/R effectif.
- [proposition] Proposition 6 (propriété universelle de lim→) : u_α∘... compatible (23) ⇒ ∃! u:E (E III.62-63) -- Propriété universelle inductive entièrement REPORTÉE (quotient effectif + compatibilité avec R absent). Seul sens facile critère cité dans p
- [proposition] Proposition 7 : (u_α) sys. ind. d'applications, u=lim→ u_α ; u_α injectives ⇒ u  (E III.64) -- REPORTÉ (repose sur Lemme 1 + quotient G/R). Aucune preuve.
- [corollaire] Corollaire Prop. 7 : (i) lim→ u_α(M_α)=u(lim→ M_α) formule (26) ; (ii) u_α⁻¹(a'_ (E III.65) -- Formules (26)(27) (images/préimages directes des systèmes inductifs) non formalisées.
- [remarque] Remarque 2 §III.7.6 + restriction inductive à J filtrante ; application canoniqu (E III.65) -- Restriction d'un système inductif à une partie J filtrante et sa canonique non formalisées (la restriction projective à J l'est, pas l'induc

## Detail complet par section

### Chapitre III, §1 — Relations d'ordre, ensembles ordonnés (E III.2 à E III.15, pages physiques 104-118 du PDF)
_pages : 103-118 (texte principal §1 : 104-118 ; p.103 = exercices §6 chap.II hors périmè_  (49 notions, 13 manquantes)

> Couverture §III.1 globalement FORTE sur les définitions (~95% closes et fidèles) : ordre, ordre dans E, opposé, préordre, ordre induit/produit, isomorphisme, croissante/décroissante/monotone (Déf.1-2), maximal/minimal (Déf.3), plus grand/petit (Déf.4), majorant/minorant (Déf.5), cofinale/coinitiale, borne sup/inf (Déf.6), filtrant (Déf.7), réticulé (Déf.8), comparable/totalement ordonné (Déf.9), tous les intervalles (Déf.13) — tous présents, énoncés conformes au PDF. Théorèmes nommés également bien couverts : unicités, plus grand⇒maximal, Prop.4 (inf≤sup), Prop.5+Cor, Prop.6, Prop.10 (maximal filtrant), Prop.11 (injectivité), Prop.13 (intersection intervalles, forme membership). PRINCIPAUX MANQUES / ÉCARTS MAJEURS à prioriser : (1) Prop.2 (identités de Galois u∘v∘u=u) MANQUANTE ; (2) Prop.12 (caractérisation de sup dans un totalement ordonné) MANQUANTE ; (3) Prop.1 (caractérisation graphe G∘G=G, G∩G⁻¹=Δ) MANQUANTE ; (4) ordre associé à un préordre par passage au quotient MANQUANT ; (5) Prop.7 et Prop.8 seulement PARTIELLES (cœur binaire/pointwise certifié, cas général à recouvrement/produit quelconque non clos) — écart majeur ; (6) prédicats 'majorée/minorée/bornée' (Déf.5 fin) non définis nommément ; (7) remarques d'implication (réticulé⇒filtrant, totalement ordonné⇒réticulé) non formalisées ; (8) ordre point-par-point sur F^E et famille de parties monotone non formalisés ; (9) seconde assertion de Prop.11 (str.croissante⇒iso sur f(E)) et première inégalité de Prop.9 (sup_E≤sup_F) non closes. Aucune anomalie de fidélité grave détectée sur les définitions auditées.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Relation d'ordre (transitive, antisymétrique, R{x,y}⇒(R | definition | E III.1.1 | clos | fidele | ensembles/ii_1_axiomes_algebre/ensembles |
| Relation d'ordre DANS un ensemble E (réflexive dans E) | definition | E III.1.1 | clos | fidele | ensembles_abrege.py:est_relation_ordre_d |
| Relation d'ordre opposée R{y,x} | definition | E III.1.1 Ex.3 | clos | fidele | ensembles_abrege.py:ordre_oppose ; ordre |
| Exemples relation d'ordre (égalité, inclusion ⊂) | remarque | E III.1.1 | clos | fidele | ensembles_ordre_relation.py:diagonale_es |
| Ordre comme correspondance Γ=(G,E,E) / graphe d'ordre s | definition | E III.1.1 | clos | fidele | ensembles_ordre_relation.py:est_ordre(G, |
| Proposition 1 (Γ ordre ⟺ G∘G=G et G∩G⁻¹=Δ) | proposition | E III.1.2 | manquant | non_verifiable |  |
| Relation de préordre (transitive, R{x,y}⇒(R{x,x} et R{y | definition | E III.1.2 | clos | fidele | ensembles_abrege.py:est_relation_preordr |
| Relation d'ordre associée à un préordre (passage au quo | proposition | E III.1.3 | manquant | non_verifiable |  |
| Préordre sur E comme correspondance ; Δ⊂G et G∘G⊂G | definition | E III.1.4 | partiel | ecart_mineur | ensembles_abrege.py:est_relation_preordr |
| Conditions (RO_I)-(RO_IV) pour la notation x≤y | axiome | E III.1.4 | clos | ecart_mineur | ensembles_abrege.py (transitif/antisym/r |
| Critère C58 (x≤y ⟺ (x<y ou x=y) ; x<y et y≤z ⇒ x<z) | critere | E III.1.5 | partiel | ecart_mineur | ensembles_abrege.py:relation_stricte ; e |
| Ensemble ordonné/préordonné par Γ ; x≤y := y∈Γ⟨x⟩ | definition | E III.1.5 | clos | fidele | ensembles_ordre_relation.py / ensembles_ |
| Isomorphisme d'ensembles ordonnés (f bijective, x≤y ⟺ f | definition | E III.1.5 | clos | fidele | ordre_treillis/ensembles_ordre_vocab.py: |
| Sous-ensemble ordonné / ordre induit G∩(A×A) | definition | E III.1.5-6 | clos | fidele | ensembles_abrege.py:ordre_induit ; ensem |
| Produit d'ensembles ordonnés / ordre produit ((∀ι)pr_ι  | definition | E III.1.6 | clos | fidele | ensembles_ordre_vocab.py:ordre_produit ; |
| Ordre sur F^E / F(E;F) : f≤g ⟺ (∀x)f(x)≤g(x) | remarque | E III.1.6 | manquant | non_verifiable |  |
| Définition 1 — application croissante / décroissante /  | definition | E III.1.7 | clos | fidele | ordre_treillis/ensembles_ordre_monotone. |
| Définition 2 — strictement croissante / décroissante /  | definition | E III.1.7 | clos | fidele | ensembles_ordre_monotone.py:est_strictem |
| Famille de parties croissante/décroissante (ι↦X_ι crois | definition | E III.1.7 | manquant | non_verifiable |  |
| f bijective isomorphisme ⟺ f et f⁻¹ croissantes | proposition | E III.1.7 | partiel | ecart_mineur | ordre_treillis/ensembles_ordre_treillis_ |
| Proposition 2 (u,v décroissantes, v(u(x))≥x, u(v(x'))≥x | proposition | E III.1.7-8 | manquant | non_verifiable |  |
| Définition 3 — élément maximal / minimal (x≤a ⇒ x=a) | definition | E III.1.8 | clos | fidele | ensembles_abrege.py:est_element_minimal/ |
| Plus petit / plus grand élément (Déf. 4) + unicité | definition | E III.1.8-9 | clos | fidele | ensembles_abrege.py:est_plus_petit/grand |
| Plus petit élément ⇒ unique élément minimal ; plus gran | proposition | E III.1.8-9 | clos | fidele | iii_1_7_plus_grand_plus_petit/ensembles_ |
| Proposition 3 — adjonction d'un plus grand élément a à  | proposition | E III.1.9 | partiel | ecart_mineur | ensembles_ordre_vocab.py:est_adjonction_ |
| Partie cofinale / coinitiale | definition | E III.1.9 | clos | fidele | ensembles_abrege.py:est_cofinale, est_co |
| Définition 5 — majorant / minorant (a majore/minore X) | definition | E III.1.9 | clos | fidele | ensembles_abrege.py:majore, minore ; ens |
| Partie minorée / majorée / bornée ; application minorée | definition | E III.1.9-10 | manquant | non_verifiable |  |
| X admet plus petit élément ⟺ ∃ minorant de X appartenan | proposition | E III.1.10 | manquant | non_verifiable |  |
| Définition 6 — borne inférieure / supérieure (plus gran | definition | E III.1.10 | clos | fidele | ensembles_ordre_relation.py:borne_superi |
| sup X admet plus grand élément a ⇒ a=sup X ; borne sup  | remarque | E III.1.10 | clos | fidele | ensembles_ordre_relation.py:plus_grand_e |
| Proposition 4 — inf A ≤ sup A (A≠∅) ; A=∅ ⇒ sup A plus  | proposition | E III.1.10 | clos | fidele | bornes_sup/ensembles_inf_sup_prop4_iii1. |
| Proposition 5 — A,B sup ; A⊂B ⇒ sup A ≤ sup B (mono inc | proposition | E III.1.11 | clos | fidele | bornes_sup/ensembles_sup_generiques_iii1 |
| Corollaire (Prop 5) — J⊂I ⇒ sup_J x_ι ≤ sup_I x_ι | corollaire | E III.1.11 | clos | fidele | ensembles_sup_generiques_iii1.py:sup_sou |
| Proposition 6 — x_ι≤y_ι ⇒ sup x_ι ≤ sup y_ι | proposition | E III.1.11 | clos | fidele | ensembles_sup_generiques_iii1.py (Prop6, |
| Proposition 7 — sup par recouvrement (J_λ) : sup_I = su | proposition | E III.1.11 | partiel | ecart_majeur | bornes_sup/ensembles_sup_prop7_8_iii1.py |
| Corollaire (Prop 7) — sup famille double sup_{(λ,μ)} =  | corollaire | E III.1.11 | manquant | non_verifiable |  |
| Proposition 8 — sup dans un produit : sup A = (sup A_ι) | proposition | E III.1.11-12 | partiel | ecart_majeur | bornes_sup/ensembles_sup_prop7_8_iii1.py |
| Proposition 9 — sup_E A ≤ sup_F A ; si sup_E A∈F alors  | proposition | E III.1.12 | partiel | ecart_mineur | bornes_sup/ensembles_sup_generiques_iii1 |
| Définition 7 — ensemble filtrant à droite / à gauche | definition | E III.1.12 | clos | fidele | ensembles_abrege.py:est_filtrant_droite, |
| Proposition 10 — dans un filtrant à droite, élément max | proposition | E III.1.13 | clos | fidele | iii_1_8_filtrants/ensembles_prop10_maxim |
| Définition 8 — ensemble réticulé (treillis/lattis) | definition | E III.1.13 | clos | fidele | ordre_treillis/ensembles_ordre_monotone. |
| Remarque — réticulé ⇒ filtrant à droite et à gauche | remarque | E III.1.13 | manquant | non_verifiable |  |
| Définition 9 — éléments comparables ; ensemble totaleme | definition | E III.1.13-14 | clos | fidele | ensembles_abrege.py:sont_comparables, es |
| Remarque — totalement ordonné ⇒ réticulé, a fortiori fi | remarque | E III.1.14 | manquant | non_verifiable |  |
| Proposition 11 — application strictement monotone d'un  | proposition | E III.1.14 | partiel | ecart_mineur | ordre_treillis/ensembles_ordre_treillis_ |
| Proposition 12 — caractérisation de sup X dans un ensem | proposition | E III.1.14 | manquant | non_verifiable |  |
| Définition 13 — intervalles fermé [a,b], semi-ouverts [ | definition | E III.1.14-15 | clos | fidele | ensembles_abrege.py:intervalle_ferme, in |
| Intervalles illimités ]←,a], ]←,a[, [a,→[, ]a,→[, ]←,→[ | definition | E III.1.15 | clos | fidele | ensembles_abrege.py:intervalle_illimite_ |
| Remarque — [a,a]={a}≠∅ ; ]a,a[, [a,a[, ]a,a] vides | remarque | E III.1.15 | partiel | ecart_mineur | ordre_treillis/ensembles_ordre_treillis_ |
| Proposition 13 — dans un réticulé, l'intersection de de | proposition | E III.1.15 | clos | ecart_mineur | ordre_treillis/ensembles_intervalles_pro |

### III.2 Ensembles bien ordonnés (E III.14–E III.21)
_pages : PDF physiques 117-124 (117 = fin III.1 §13 Intervalles ; III.2 débute p.118/E II_  (26 notions, 7 manquantes)

> III.2 (E III.14–21) lue page par page (PDF 117-124 ; 117 = fin de III.1). La couverture est RÉELLE et substantielle sur le socle : Déf 1 (bon ordre), Déf 2 (segment), Déf 3 (inductif) sont closes et fidèles ; les remarques élémentaires sur les segments (réunion/intersection/transitivité, E et ∅) sont des théorèmes directs ; C59 (récurrence transfinie) est clos et fidèle (preuve par plus-petit-contre-exemple, équivalente à la méthode du livre) ; Th1 (Zermelo) et Th2 (Zorn) sont clos avec énoncés fidèles. L'unicité de l'iso (composante de Th3) est close.

ÉCARTS MAJEURS DE FIDÉLITÉ (énoncé correct, mais formalisation/preuve divergente) : (1) Le CHEMIN DE PREUVE de Th1/Th2 NE SUIT PAS le livre — Bourbaki passe par Lemme 3 (p(X)∉X) et Prop 4 (parties bien ordonnées majorées) ; le dépôt dérive tout de Bourbaki–Witt / point fixe sur le poset des chaînes/bons-ordres-partiels. Soundness garantie par le noyau, mais Lemme 3, Prop 4, Cor 1, Cor 2 ne sont PAS formalisés comme théorèmes (seulement évoqués en narration dans zorn.py). (2) Th2 ajoute E≠∅ en hypothèse là où Bourbaki ne l'exige pas (écart mineur d'hypothèse).

PARTIELS notables : Prop 1 (segment propre = ]←,a[) explicitement « REPORTÉ » dans ensembles_bon_ordre.py ; Prop 2 (E* bien ordonné par ⊂, iso E≅S(E)) seulement la brique de monotonie stricte ; Prop 3 et Lemme 1 (recollement d'une FAMILLE indexée de bons ordres emboîtés) traités uniquement en CAS BINAIRE au service de la trichotomie ; C60 (existence/unicité de l'application récursive) prouvé surtout au NIVEAU VALEUR avec verrous honnêtes signalés ; Th3 (trichotomie) bâti par une longue chaîne mais l'assemblage final RAPPORTE un résidu structurel irréductible (non clos à 0 hypothèse).

MANQUANTS : Lemme 3, Prop 4, Cor 1, Cor 2, ainsi que deux remarques préparatoires (borne sup d'une partie majorée ; ⋃S_x = E ou E∖{b}).

Priorité de comblement recommandée : Prop 1 et Prop 2 (briques manquantes pour une couverture honnête de la structure des segments), puis Prop 4/Cor 1/Cor 2 si l'on veut la fidélité au schéma de preuve du livre. Aucun écart de SOUNDNESS détecté ; les écarts sont de FIDÉLITÉ (chemin de preuve) et de COMPLÉTUDE (généralité famille vs binaire, niveau valeur vs graphe).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Relation de bon ordre entre x et y | definition | E III.15 | clos | fidele | bourbaki/ordre/iii_2_bon_ordre/bon_ordre |
| Définition 1 — Ensemble bien ordonné | definition | E III.15 | clos | fidele | bon_ordre_segments/ensembles_bon_ordre.p |
| E bien ordonné ⇒ E totalement ordonné | proposition | E III.15 | clos | fidele | bon_ordre_segments/ensembles_bon_ordre_t |
| Toute partie d'un bien ordonné est bien ordonnée par l' | remarque | E III.15 (Exemple 2) | clos | fidele | bon_ordre_segments/ensembles_sous_bien_o |
| Toute partie majorée d'un bien ordonné admet une borne  | remarque | E III.15 | manquant | non_verifiable |  |
| Définition 2 — Segment de E | definition | E III.16 | clos | fidele | bon_ordre_segments/ (est_segment) ; segm |
| Intersection / réunion de segments est un segment ; E e | remarque | E III.16 | clos | fidele | bon_ordre_segments/ensembles_bon_ordre.p |
| Proposition 1 — Tout segment de E distinct de E est un  | proposition | E III.16 | partiel | ecart_mineur | lemme4_segments/ensembles_bien_ordonne_l |
| Segment d'extrémité x : S_x = ]←,x[ | notation | E III.16 | clos | fidele | lemme4_segments/ensembles_segments_const |
| Réunion des S_x = E (si pas de plus grand élt) ou E∖{b} | remarque | E III.16 | manquant | non_verifiable |  |
| Proposition 2 — E* (segments de E) bien ordonné par inc | proposition | E III.16 | partiel | ecart_majeur | bon_ordre_segments/ensembles_segment_str |
| Proposition 3 — Famille (X_ι) où chaque paire X_ι,X_κ : | proposition | E III.16 | partiel | ecart_majeur | cardinaux/iii_2_trichotomie_ordinaux/lem |
| Lemme 1 — Famille filtrante (X_α,⊂) à ordres induits co | proposition | E III.17 | partiel | ecart_majeur | cardinaux/iii_2_trichotomie_ordinaux/lem |
| Lemme 2 — Critère d'induction sur les segments (réunion | proposition | E III.17 | clos | ecart_mineur | recurrence_transfinie/ (sous-jacent à re |
| C59 — Principe de récurrence transfinie | critere | E III.18 | clos | fidele | recurrence_transfinie/ensembles_recurren |
| Notation g^(x) (restriction d'une application de segmen | notation | E III.18 | clos | fidele | recurrence_transfinie/ensembles_c60_coeu |
| C60 — Définition d'une application par récurrence trans | critere | E III.18 | partiel | ecart_mineur | recurrence_transfinie/ensembles_c60_fina |
| Cas particulier de C60 : T{h}∈F pour toute h ⇒ U partie | remarque | E III.19 | non_applicable | non_verifiable |  |
| Lemme 3 — ∃ partie M et bon ordre Γ avec S_x∈𝔖, p(S_x)= | proposition | E III.19 | manquant | non_verifiable |  |
| Théorème 1 (Zermelo) — Sur tout ensemble E il existe un | theoreme | E III.20 | clos | ecart_majeur | zorn_zermelo/ensembles_zermelo.py (theor |
| Définition 3 — Ensemble inductif | definition | E III.20 | clos | fidele | ensembles_abrege.py (est_inductif, l.738 |
| Exemples d'inductifs (𝔉 fermé par réunion de chaînes ;  | remarque | E III.20 | non_applicable | non_verifiable |  |
| Théorème 2 — Tout ensemble ordonné inductif possède un  | theoreme | E III.20 | clos | ecart_majeur | zorn_zermelo/ensembles_zorn_theoreme.py  |
| Proposition 4 — E ordonné dont toute partie bien ordonn | proposition | E III.20 | manquant | non_verifiable |  |
| Corollaire 1 — E inductif, a∈E ⇒ ∃ maximal m≥a | corollaire | E III.21 | manquant | non_verifiable |  |
| Corollaire 2 — 𝔉 ensemble de parties fermé par réunion  | corollaire | E III.21 | manquant | non_verifiable |  |
| Théorème 3 — E,F bien ordonnés : il existe un iso uniqu | theoreme | E III.21 | partiel | ecart_mineur | cardinaux/iii_2_trichotomie_ordinaux/ass |
| Unicité de l'isomorphisme (de E sur un segment de F) | proposition | E III.21 | clos | fidele | cardinaux/iii_2_trichotomie_ordinaux/iso |

### III.3 — Ensembles équipotents. Cardinaux (E III.22–29, sous-sections 1–6 + Cantor/Th.2)
_pages : PDF physiques 125-134 (E III.22-31) rendus en PNG (150 dpi) et lus un par un ; l_  (38 notions, 1 manquantes)

> Audit du texte principal §III.3 (E III.22-30) page par page (PDF scan rendu 125-134) vs zone code bourbaki/cardinaux. INVENTAIRE : 4 définitions (Eq, Card, ≤, exponentiation) + Déf.3 somme/produit, Th.1 (bon ordre), Th.2 (Cantor), Prop.1-14, ~12 corollaires, plusieurs remarques. COUVERTURE — Solide (clos, fidèle) : Déf.1/2/4, Prop.1, équivalence Eq, ≤ (def+transitivité+Eq⇒≤), comparabilité (Cor.1 Th.1 via Zorn), Cantor–Bernstein (Cor.2 Th.1), Prop.3, Prop.8 (successeur injectif), Prop.12 (𝔓(X)=2^a), Prop.13 (a≥b⟺∃c a=b+c, les deux sens), Th.2 Cantor 2^a>a + corollaire, identités binaires a+b=b+a/ab=ba/associativité/distributivité, a+0=a/a·1=a, a^0=1/a^1=a, 0<1/1<2, bornes 0≤a/1≤a. PRINCIPAL ÉCART STRUCTUREL (récurrent, ecart_majeur) : tout ce qui concerne les FAMILLES INDEXÉES de cardinaux n'existe qu'au cas BINAIRE/ternaire — Déf.3 (∑_ι/∏_ι), Prop.4, Prop.5 (5a réindexation, 5b associativité-partition, 5c distributivité indexée), Prop.6, Prop.7, Prop.10 (a^b=∏ famille constante), Cor.1/Cor.2 de Prop.10, Prop.14 et ses Cor.1. Les dossiers iii_3_6_familles et iii_3_7_inegalites sont des TODO VIDES (trous de couverture visibles structurellement). MANQUANT net : Cor.2 de Prop.6 (ab=∑_I a, b=∑_I 1). REPORTS HONNÊTES non clos : currying a^(bc)=(a^b)^c (Cor.3 Prop.10, verrou bijection double-niveau), monotonie exponentielle Cor.2 Prop.14 (conditionnelle), caractère collectivisant 'ensemble des cardinaux ≤a' (axiome définitionnel). Th.1 'R{x,y} bon ordre' est fonctionnellement présent (réflexif+transitif+antisym+total+bon-ordre exploité dans sup_cardinal) mais pas unifié en un énoncé-théorème calqué sur la preuve Bourbaki (segments φ(x)). Prop.2 (sup d'une famille) dérivée mais formulée sur un ensemble borné de cardinaux, pas une famille indexée (écart mineur). Aucune INFIDÉLITÉ de définition détectée sur les notions closes ; le noyau garantit la soundness (theorie=22 partout affirmé). Le gros chantier ouvert reste la GÉNÉRALISATION FAMILLE des opérations cardinales et le currying exponentiel.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Produit lexicographique d'une famille d'ensembles ordon | definition | E III.22-23 (§III.2.6) | non_applicable | non_verifiable |  |
| Définition 1 — Équipotence Eq(X,Y) | definition | E III.23 (§III.3.1) | clos | fidele | iii_3_equipotence_cardinaux/definitions_ |
| Eq est une relation d'équivalence (symétrique, réflexiv | proposition | E III.23 (§III.3.1) | clos | fidele | equipotence/ensembles_equipotence.py + e |
| Axiome de congruence de τ_Z sous équivalence universell | axiome | E III.23 (§III.3.1) | clos | fidele | definitions_cardinaux/ensembles_cardinau |
| Définition 2 — Cardinal Card(X) := τ_Z(Eq(X,Z)) | definition | E III.23 (§III.3.1) | clos | fidele | definitions_cardinaux/ensembles_cardinau |
| Proposition 1 — Eq(X,Y) ⟺ Card X = Card Y | proposition | E III.23 (§III.3.1) | clos | fidele | definitions_cardinaux/ensembles_cardinau |
| Exemple 1 — 0 = Card(∅) = ∅ | definition | E III.23 (§III.3.1) | clos | fidele | equipotence/ensembles_vide_singleton.py  |
| Exemple 2 — 1 = Card({∅}) | definition | E III.24 (§III.3.1) | clos | fidele | définitions entiers : 1=Card({∅}) utilis |
| Exemple 3 — 2 = Card({∅,{∅}}) | definition | E III.24 (§III.3.1) | clos | fidele | prop12_powerset (2={∅,{∅}}=paire) ; ordr |
| Théorème 1 — la relation R{x,y} « x,y cardinaux et x éq | theoreme | E III.24 (§III.3.2) | partiel | ecart_mineur | ordre_cardinaux/ensembles_comparabilite. |
| Définition de ≤ entre cardinaux (x≤y ⟺ ∃ injection x→y  | definition | E III.24 (§III.3.2) | clos | fidele | definitions_cardinaux/ensembles_cardinau |
| Eq(X,Y) ⇒ X≤Y | proposition | E III.24 (§III.3.2) | clos | fidele | ordre_cardinaux/ensembles_cardinaux_ordr |
| Transitivité de ≤ : (X≤Y et Y≤Z) ⇒ X≤Z | proposition | E III.24 (§III.3.2) | clos | fidele | ordre_cardinaux/ensembles_cardinaux_ordr |
| Remarque — 0≤x pour tout cardinal x, et 1≤x pour tout x | remarque | E III.25 (§III.3.2) | clos | fidele | ordre_cardinaux/ensembles_cardinaux_born |
| Corollaire 1 (de Th.1) — étant donnés deux ensembles, l | corollaire | E III.25 (§III.3.2) | clos | fidele | ordre_cardinaux/ensembles_comparabilite. |
| Corollaire 2 (de Th.1) — deux ensembles chacun équipote | corollaire | E III.25 (§III.3.2) | clos | fidele | ensembles_cantor_bernstein_final/_recoll |
| Remarque — ensemble des cardinaux ≤ a (collectivisante  | remarque | E III.25 (§III.3.2) | partiel | ecart_mineur | ordre_cardinaux/ensembles_cardinaux_born |
| Proposition 2 — toute famille de cardinaux admet une bo | proposition | E III.25 (§III.3.2) | partiel | ecart_mineur | ordre_cardinaux/ensembles_sup_cardinal.p |
| Proposition 3 — surjection f:X→Y ⇒ Card Y ≤ Card X | proposition | E III.25 (§III.3.2) | clos | fidele | props_restantes/ensembles_prop3_prop4cor |
| Définition 3 — produit cardinal ∏a_ι et somme cardinale | definition | E III.25 (§III.3.3) | partiel | ecart_majeur | arithmetique/iii_3_3_produit/ensembles_a |
| Proposition 4 — Card(produit)=produit cardinal, Card(so | proposition | E III.26 (§III.3.3) | partiel | ecart_majeur | binaire seulement : somme_cardinale (=Ca |
| Corollaire (de Prop.4) — Card(⋃E_ι) ≤ ∑Card(E_ι) | corollaire | E III.26 (§III.3.3) | partiel | ecart_mineur | props_restantes/ensembles_prop3_prop4cor |
| Proposition 5 — a) invariance par bijection d'indices ; | proposition | E III.26 (§III.3.3) | partiel | ecart_majeur | iii_3_3_somme/ensembles_somme_associe.py |
| Commutativité/associativité binaires : a+b=b+a, ab=ba,  | corollaire | E III.27 (§III.3.3) | clos | fidele | somme_commute, somme_associe, produit_co |
| Proposition 6 — a_ι=0 hors J ⇒ ∑=∑_J ; a_ι=1 hors K ⇒ ∏ | proposition | E III.27 (§III.3.4) | partiel | ecart_majeur | iii_3_3_somme/ensembles_somme_zero.py (0 |
| Corollaire 1 (de Prop.6) — a+0 = a·1 = a | corollaire | E III.27 (§III.3.4) | clos | fidele | somme_zero (card_somme_zero_neutre) ; pr |
| Corollaire 2 (de Prop.6) — I équipotent à b ⇒ ab=∑_I a  | corollaire | E III.27 (§III.3.4) | manquant | non_verifiable |  |
| Proposition 7 — ∏a_ι ≠ 0 ⟺ a_ι≠0 pour tout ι | proposition | E III.28 (§III.3.4) | partiel | ecart_majeur | props_restantes/ensembles_cardinaux_prop |
| Proposition 8 — a+1=b+1 ⇒ a=b (successeur cardinal inje | proposition | E III.28 (§III.3.4) | clos | fidele | arithmetique/iii_3_4_prop8_successeur/ ( |
| Remarque — a+m=b+m n'entraîne pas a=b en général (vrai  | remarque | E III.28 (§III.3.4) | non_applicable | non_verifiable |  |
| Définition 4 — exponentiation a^b := Card(ensemble des  | definition | E III.28 (§III.3.5) | clos | fidele | arithmetique/iii_3_5_exposant/definition |
| Proposition 9 — Card(X^Y) = a^b (a=Card X, b=Card Y) | proposition | E III.28 (§III.3.5) | clos | ecart_mineur | prop9_exp_somme/* (et invariance de a^b  |
| Proposition 10 — Card(I)=b, a_ι=a ⇒ a^b = ∏_{ι∈I} a_ι | proposition | E III.28 (§III.3.5) | partiel | ecart_majeur | prop10_currying/* (currying ; sert au Co |
| Corollaire 1 (de Prop.10) — a^(∑b_ι) = ∏ a^{b_ι} | corollaire | E III.28 (§III.3.5) | partiel | ecart_majeur | prop9_exp_somme/* (cas binaire a^(b+c)=a |
| Corollaire 2 (de Prop.10) — (∏a_ι)^b = ∏ a_ι^b | corollaire | E III.29 (§III.3.5) | partiel | ecart_majeur | prop10_currying/ensembles_prop10cor2_iii |
| Corollaire 3 (de Prop.10) — a^(bc) = (a^b)^c (currying) | corollaire | E III.29 (§III.3.5) | partiel | ecart_majeur | prop10_currying/ensembles_exposant_produ |
| Proposition 11 — a^0=1, a^1=a, 1^a=1, 0^a=0 (a≠0), 0^0= | proposition | E III.29 (§III.3.5) | clos | ecart_mineur | iii_3_5_exposant/definition/ : exposant_ |
| Proposition 12 — Card(𝔓(X)) = 2^a | proposition | E III.29 (§III.3.5) | clos | fidele | prop12_powerset/* (ensembles_prop12_powe |
| Proposition 13 — a≥b ⟺ ∃c a=b+c | proposition | E III.29 (§III.3.6) | clos | fidele | props_restantes/ensembles_prop13_complem |
| Remarque §III.3.6 — pas de différence a−b en général (p | remarque | E III.30 (§III.3.6) | non_applicable | non_verifiable |  |
| Proposition 14 — a_ι≤b_ι pour tout ι ⇒ ∑a_ι≤∑b_ι et ∏a_ | proposition | E III.30 (§III.3.6) | partiel | ecart_majeur | arithmetique/iii_3_2_monotonie/ensembles |
| Corollaire 1 (de Prop.14) — ∑_J a_ι≤∑a_ι ; et ∏_J≤∏ si  | corollaire | E III.30 (§III.3.6) | partiel | ecart_majeur | somme_produit_bornes/ensembles_cardinaux |
| Corollaire 2 (de Prop.14) — a≤a', b≤b', a'>0 ⇒ a^b ≤ a' | corollaire | E III.30 (§III.3.6) | partiel | ecart_mineur | iii_3_2_monotonie/ensembles_arith_cardin |
| Théorème 2 (Cantor) — pour tout cardinal a, 2^a > a | theoreme | E III.30 (§III.3.6) | clos | fidele | iii_3_equipotence_cardinaux/cantor/ensem |
| Corollaire (de Th.2 Cantor) — il n'existe pas d'ensembl | corollaire | E III.30 (§III.3.6) | clos | ecart_mineur | consequences/ensembles_cardinaux_consequ |

### III.4 — Entiers naturels, ensembles finis (E III.30 à E III.33)
_pages : PDF physiques 132-136 rendus à 150 dpi (E III.29 fin de §3 ; E III.30-33 = §4 nº_  (14 notions, 5 manquantes)

> Couverture EXCELLENTE du noyau de §4. Déf. 1 (cardinal fini = entier naturel ; ensemble/famille finie ; nombre d'éléments) est formalisée fidèlement dans bourbaki/entiers/iii_4_entiers_finis/iii_4_1_definitions_premiers_entiers/ensembles_entiers.py (est_fini, est_entier, est_fini_ensemble, nombre_d_elements, famille_finie). Les premiers entiers 0,1,2,3,4 sont construits et leur finitude PROUVÉE (CLOS) via Prop. 8. Prop. 1 (a fini ⇔ a+1 fini) est CLOSE (fini_ssi_fini_successeur). Le fait remarquable : C61 (principe de récurrence) est désormais PROUVÉ constructivement par plus-petit-contre-exemple (ensembles_principe_recurrence_preuve.principe_recurrence_preuve), avec cardinaux_bien_ordonnes_close (CLOS) et le prédécesseur Prop. 2 fermé (predecesseur_fini_universel_preuve, CLOS) ; il en résulte que ℕ existe inconditionnellement (N_existe, CLOS) et que fini_downward (« tout a≤n est entier ») est dérivable. Cor. 4 inj⇒surj est CLOS ; Cor. 4 surj⇒inj est PARTIEL (deux maillons reportés : section d'une surjection est injective + g=f⁻¹). ÉCARTS/MANQUES principaux : (a) Prop. 2 n'est formalisée que par MORCEAUX (existence/unicité du prédécesseur n=m+1 close, « tout a≤n entier » dérivable, mais l'énoncé COMPOSITE complet incluant « a<n ⇔ a≤m » n'est pas assemblé en un seul théorème) ; (b) Cor. 1 « toute partie d'un fini est finie » est CONDITIONNEL (déchargé sur fini_downward, désormais dérivable mais pas branché) ; (c) Cor. 2 (Card X < Card E pour partie stricte) RAPPORTÉ (énoncé seul, surgery non close) ; (d) Cor. 3 (image d'un fini est finie) CONDITIONNEL/PARTIEL ; (e) la Remarque E III.33 (variantes de récurrence : forte S{n}, à partir de k, limitée à un intervalle [a,b], descendante — points 1 à 4) est ENTIÈREMENT MANQUANTE ; (f) Déf. 2 « caractère fini » (E III.4.5, hors de la plage page lue mais référencée dans le module) présente seulement la formule, pas de théorème.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Déf. 1 — cardinal fini / entier naturel : Fini(a) :⇔ a  | definition | E III.30 | clos | fidele | entiers/iii_4_entiers_finis/iii_4_1_defi |
| Déf. 1 (suite) — ensemble E fini = Card(E) cardinal fin | definition | E III.30-31 | clos | fidele | ensembles_entiers.py:est_fini_ensemble,n |
| Déf. 1 (suite) — famille finie = ensemble d'indices fin | definition | E III.31 | clos | fidele | ensembles_entiers.py:famille_finie |
| Premiers entiers 0,1,2,3,4 (0=Card∅, 1=0+1, 2=1+1, 3,4) | definition | E III.31 | clos | fidele | iii_4_1_definitions_premiers_entiers/ens |
| Proposition 1 — a fini ⇔ a+1 fini | proposition | E III.31 | clos | fidele | ensembles_fini_successeur.py:fini_ssi_fi |
| Proposition 2 — existence/unicité du prédécesseur (n≠0  | proposition | E III.31 | clos | ecart_mineur | ensembles_predecesseur_prop2.py:predeces |
| Proposition 2 (suite) — tout cardinal a≤n est un entier | proposition | E III.31 | clos | fidele | ensembles_recurrence_C61.py:fini_downwar |
| Proposition 2 (suite) — a<n ⇔ a≤m (où n=m+1) | proposition | E III.31 | manquant | non_verifiable |  |
| Corollaire 1 — toute partie d'un ensemble fini est fini | corollaire | E III.31 | partiel | ecart_mineur | finis_props.py:cor1_partie_finie_est_fin |
| Corollaire 2 — X⊂E, X≠E, E fini ⇒ Card X < Card E | corollaire | E III.31 | manquant | non_verifiable | finis_props.py:cor2_partie_stricte_card_ |
| Corollaire 3 — f:E→F, E fini ⇒ f(E) partie finie de F | corollaire | E III.32 | partiel | ecart_mineur | finis_props2.py:cor3_image_finie_cond |
| Corollaire 4 — E,F finis même cardinal, f:E→F ⇒ (inj ⇔  | corollaire | E III.32 | partiel | ecart_mineur | iii_4_2_cor4_inj_surj_bij/ensembles_cor4 |
| C61 — principe de récurrence (métathéorème) : R{0} et ( | critere | E III.32 | clos | fidele | ensembles_principe_recurrence_preuve.py: |
| Remarque E III.33 — variantes de récurrence : (1) forte | remarque | E III.33 | manquant | non_verifiable |  |

### III.5 — Calcul sur les entiers (E III.35–E III.43)
_pages : PDF physiques 137-146 rendus à 150 dpi (ch3_5-137…146.png) puis lus un par un. §_  (38 notions, 14 manquantes)

> §III.5 « Calcul sur les entiers » (E III.35–E III.43) compte ~38 notions nommées. La couverture est TRÈS contrastée. SOLIDE et CLOS/FIDÈLE : Prop2 (a<b ⟺ ∃c>0, b=a+c, équivalence complète), Cor4 (existence+unicité de la différence), Prop4 (translation iso d'ordre [0,b]→[a,a+b]), Prop5 (Card[a,b]=(b−a)+1), et les synonymies de la Déf1 divisibilité (multiple/diviseur/divise, théorèmes-identités clos). PARTIELS notables : Prop1 (somme/produit d'entiers) close en BINAIRE seulement, pas en famille indexée ; Cor3 a^b entier CONDITIONNEL au keystone eq_exposant_invariant non déchargé ; Prop3 monotonie stricte binaire seule ; Prop7 fonctions caractéristiques prouvée sous hypothèses honnêtes (φ opaque) ; factorielle close comme 'n! est un entier' sous les deux prémisses récursives mais le terme factorielle reste opaque ; Prop6 iso E→[1,n] assemblé avec hypothèses résiduelles à vérifier ; notions développement base b / chiffre / coefficient binomial posées fidèlement mais en termes opaques sans propriétés.

TROUS MAJEURS (priorité) : (1) Théorème 1 DIVISION EUCLIDIENNE — non prouvé, dossier iii_5_6 VIDE, seuls des termes opaques + la formule a=bq+r∧r<b ; (2) Proposition 8 DÉVELOPPEMENT DE BASE b (iso f_k sur [0,b^k−1]) — non formalisée, dossier iii_5_7 VIDE ; (3) toute l'ANALYSE COMBINATOIRE Prop10–14 et corollaires (injections n!/(n−m)!, permutations=n!, recouvrements, parties à p élts=C(n,p), Σ C(n,p)=2^n, Pascal, couples n(n+1)/2) — AUCUN théorème, seulement le terme opaque coefficient_binomial ; (4) Prop9 principe des bergers — forme pleine manquante, seul le cœur binaire à deux fibres (somme) clos ; (5) Cor1/Cor2/Cor4 de Prop1 (réunion/produit/parties d'ensembles finis = fini) non assemblés dans iii_5.

Les trous sont VISIBLES STRUCTURELLEMENT (dossiers iii_5_6 et iii_5_7 vides), conformément à la convention du projet. Aucun faux théorème détecté (les conditionnels sont honnêtement exposés comme hypothèses non circulaires). Lecture seule : rendus PNG + Read + Grep uniquement, aucun code écrit/commité.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Proposition 1 — Pour une famille finie d'entiers (a_i), | proposition | E III.35 / E III.36 | partiel | ecart_majeur | entiers/iii_5_calcul_entiers/iii_5_1_som |
| Corollaire 1 (Prop1) — La réunion d'une famille finie d | corollaire | E III.36 | manquant | non_verifiable |  |
| Corollaire 2 (Prop1) — Le produit d'une famille finie d | corollaire | E III.36 | manquant | non_verifiable |  |
| Corollaire 3 (Prop1) — Si a et b sont des entiers, a^b  | corollaire | E III.36 | partiel | ecart_mineur | cardinaux/iii_5_entiers/ensembles_n_arit |
| Corollaire 4 (Prop1) — L'ensemble des parties d'un ense | corollaire | E III.36 | manquant | non_verifiable |  |
| Proposition 2 — a<b ⟺ il existe un entier c>0 tel que b | proposition | E III.36 | clos | fidele | entiers/iii_5_calcul_entiers/iii_5_2_ine |
| Proposition 3 — a_i≤b_i et a_j<b_j pour un j ⇒ Σa_i<Σb_ | proposition | E III.36 | partiel | ecart_majeur | entiers/iii_5_calcul_entiers/iii_5_2_ine |
| Corollaire 1 (Prop3) — a<a' et b>0 ⇒ a^b<a'^b | corollaire | E III.37 | manquant | non_verifiable |  |
| Corollaire 2 (Prop3) — a>1 et b<b' ⇒ a^b<a^{b'} | corollaire | E III.37 | manquant | non_verifiable |  |
| Corollaire 3 (Prop3) — a+b=a+b' ⟺ b=b' (resp. ab=ab' ⟺  | corollaire | E III.37 | partiel | ecart_mineur | entiers/iii_5_calcul_entiers/iii_5_1_som |
| Corollaire 4 (Prop3) — Si a≤b il existe un unique entie | corollaire | E III.37 | clos | fidele | entiers/iii_5_calcul_entiers/iii_5_2_ine |
| Définition (différence) — l'entier c tel que b=a+c se n | definition | E III.37 | partiel | ecart_mineur | difference_entiers (ensembles_entiers.py |
| Intervalle d'entiers [0,a] — {x : x cardinal et x≤a} es | notation | E III.37 | clos | fidele | intervalle_entiers, corps_intervalle_ent |
| Proposition 4 — x↦a+x est un isomorphisme strictement c | proposition | E III.37 | clos | fidele | entiers/iii_5_calcul_entiers/iii_5_2_ine |
| Proposition 5 — Si a≤b, [a,b] est fini de nombre d'élém | proposition | E III.38 | clos | fidele | entiers/iii_5_calcul_entiers/iii_5_inter |
| Proposition 6 — Tout ensemble fini totalement ordonné à | proposition | E III.38 | partiel | ecart_mineur | entiers/iii_5_calcul_entiers/iii_5_inter |
| Suite finie — famille dont l'ensemble d'indices est un  | definition | E III.38 | clos | fidele | est_suite_finie, longueur_suite (ensembl |
| Numérotation/k-ième, premier, dernier terme d'une suite | definition | E III.38 | partiel | fidele | entiers/iii_5_calcul_entiers/iii_5_notio |
| Notation (t_i)_{P{i}} et Π_{i=a}^{b}, notations indexée | notation | E III.38 | non_applicable | non_verifiable |  |
| Définition (fonction caractéristique) — φ_A:E→{0,1}, φ_ | definition | E III.38 / E III.39 | partiel | ecart_mineur | fonction_caracteristique (ensembles_enti |
| Proposition 7 — φ_{E−A}=1−φ_A ; φ_{A∩B}=φ_A·φ_B ; φ_{A∪ | proposition | E III.39 | partiel | fidele | entiers/iii_5_calcul_entiers/iii_5_5_car |
| Théorème 1 (division euclidienne) — b>0 ⇒ existence et  | theoreme | E III.39 | manquant | ecart_majeur | condition_division_euclidienne, division |
| Définition 1 — reste r ; multiple, divisible, diviseur, | definition | E III.39 | clos | fidele | entiers/iii_5_calcul_entiers/iii_5_notio |
| Identités de divisibilité — (c+d)/b=c/b+d/b, (c−d)/b=c/ | remarque | E III.39 | partiel | ecart_mineur | est_pair, est_impair (ensembles_entiers. |
| Proposition 8 — f_k(r)=Σ r_h b^{k-h-1} est un isomorphi | proposition | E III.40 | manquant | non_verifiable | dossier iii_5_7_developpement_base_b/ VI |
| Développement de base b — existence d'une suite (r_h) a | definition | E III.40 / E III.41 | partiel | fidele | entiers/iii_5_calcul_entiers/iii_5_notio |
| Système de numération / chiffre / symbole numérique / s | definition | E III.41 | partiel | fidele | est_chiffre, symbole_numerique (ensemble |
| Proposition 9 (principe des bergers) — f surjection E→F | proposition | E III.41 | partiel | ecart_majeur | entiers/iii_5_calcul_entiers/iii_5_5_car |
| Définition 2 (factorielle) — n!=Π_{i<n}(i+1) ; 0!=1, (n | definition | E III.41 | partiel | ecart_mineur | factorielle (ensembles_entiers.py, opaqu |
| Proposition 10 — n!/(n−m)! est le nombre des applicatio | proposition | E III.41 / E III.42 | manquant | non_verifiable |  |
| Corollaire (Prop10) — Le nombre de permutations d'un en | corollaire | E III.42 | manquant | non_verifiable |  |
| Proposition 11 — nombre de recouvrements partitionnés ( | proposition | E III.42 | manquant | non_verifiable |  |
| Corollaire 1 (Prop11) — nombre de parties à p éléments  | corollaire | E III.42 | partiel | ecart_mineur | coefficient_binomial (ensembles_entiers. |
| Convention C(n,p)=0 si p>n ; C(n,p)=C(n,n−p) | definition | E III.42 / E III.43 | partiel | fidele | coefficient_binomial (ensembles_entiers. |
| Corollaire 2 (Prop11) — nombre d'applications stricteme | corollaire | E III.43 | manquant | non_verifiable |  |
| Proposition 12 — Σ_p C(n,p) = 2^n | proposition | E III.43 | manquant | non_verifiable |  |
| Proposition 13 (formule de Pascal) — C(n+1,p+1)=C(n,p+1 | proposition | E III.43 | manquant | non_verifiable |  |
| Proposition 14 — nombre a_n de couples (i,j) avec 1≤i≤j | proposition | E III.43 | manquant | non_verifiable |  |

### III.6 Ensembles infinis (texte principal, E III.45-49 ; sous-sections III.6.1 L'ensemble des entiers naturels, III.6.2 Definition d'applications par recurrence, III.6.3 Calcul sur les cardinaux infinis, III.6.4 Ensembles denombrables — debut)
_pages : PDF physiques 147-152 (= queue de III.5 en p.147 : Prop.15+Cor. ; III.6 demarre _  (24 notions, 8 manquantes)

> Audit du TEXTE PRINCIPAL de III.6 sur les pages PDF 147-152 (E III.45-49 ; p.147 est encore III.5 Prop.15+Cor., ecartee). 24 notions recensees : III.6.1 (Defs 1-2, Remarque, A4, Th.1, N, aleph0, vocabulaire des suites), III.6.2 (C62/C63 + 4 exemples/remarque), III.6.3 (Th.2 Hessenberg + Lemmes 1-2 + Cor.1-4), III.6.4 debut (Def.3, Prop.1-2).

POINTS FORTS (clos & fideles) : Def.1 (infini), Def.2 (suite), Def.3 (denombrable, verbatim), N, aleph0, Theoreme 1 (collectivisation prouvee a partir de A4). A4 present et bien isole (hors invariant 22 axiomes, porte par theorie_infini()) mais sous forme cardinale (ecart mineur).

ECARTS MAJEURS / TROUS PRIORITAIRES :
- Theoreme 2 (a^2=a, Hessenberg) : PARTIEL ; un assemblage porte AVERTISSEMENT VACUITE (audit 2026-06-22), l'autre reste sous l'hypothese-carre Card(S0xS0)=Card S0 non dechargee + deux residus de Zorn. Pas de a^2=a a 0 hypothese. Gros chantier annonce dans CLAUDE.md.
- Lemme 1 (tout infini contient un ~N) : non prouve, residu bloquant Th.2 ET Prop.2.
- Lemme 2 (NxN~N) : moitie close (N<=NxN), autre reportee (injection dyadique, depend recurrence III.5).
- Corollaires : Cor.1 (a^n=a) PARTIEL (seule brique a^(n+1)=a^n.a) ; Cor.2,3,4 MANQUANTS (aucun fichier).
- Prop.1, Prop.2 (denombrables) : PARTIELS, dependent des corollaires du Th.2 non clos.

TROUS MINEURS (vocabulaire/exemples) : suite extraite, suites differant par l'ordre, suite multiple/p-uple, ranger dans l'ordre defini par f ; Exemples 1-3 de recurrence et remarque « recurrence limitee ». C62/C63 presents mais PARTIELS : existence conditionnelle (N lu (N,<=)) et UNICITE de (U,f) non etablie alors que Bourbaki l'affirme.

Note structurelle : deux dossiers explicitement TODO (iii_6_1_definition_infini, iii_6_2_proprietes_infinis) sont des trous-dossier ; la matiere reelle de III.6.1 vit sous bourbaki/entiers/iii_6_infinis/. Bilan : socle definitionnel solide et fidele, mais tout le bloc arithmetique des cardinaux infinis (Th.2 + Cor.1-4 + Prop.1-2 + Lemmes 1-2) est partiel/conditionnel ou manquant. Tests lourds non lances (lecture seule respectee).

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Definition 1 — ensemble infini / cardinal infini | definition | E III.45 | clos | fidele | bourbaki/entiers/iii_6_infinis/iii_6_3_i |
| Remarque — « x est un entier » collectivisante ssi il e | remarque | E III.45 | partiel | ecart_mineur | bourbaki/entiers/iii_6_infinis/iii_6_1_n |
| A4 — axiome de l'infini : « Il existe un ensemble infin | axiome | E III.45 | clos | ecart_mineur | bourbaki/entiers/iii_6_infinis/iii_6_3_i |
| Theoreme 1 — « x est un entier » est collectivisante (e | theoreme | E III.45 | clos | fidele | bourbaki/entiers/iii_6_infinis/iii_6_1_n |
| N — ensemble des entiers naturels (notation, ordre usue | notation | E III.45 | clos | fidele | ensembles_ensemble_NN.py:NN (tau du corp |
| aleph_0 := Card(N) | notation | E III.45 | clos | fidele | ensembles_aleph0.py:aleph_0() (TERME CLO |
| Definition 2 — suite ; suite d'elements de E ; suite in | definition | E III.45/46 | clos | fidele | ensembles_infinis.py : est_suite(f,I):=( |
| Sous-famille extraite d'une suite (« suite extraite ») | definition | E III.46 | manquant | non_verifiable |  |
| Suites ne differant que par l'ordre des termes (permuta | definition | E III.46 | manquant | non_verifiable |  |
| Suite multiple (p-uple, double, triple) ; suite rangee  | definition | E III.46 | manquant | non_verifiable |  |
| C62 — definition d'applications par recurrence (forme g | critere | E III.46 | partiel | ecart_mineur | bourbaki/entiers/iii_6_infinis/iii_6_2_r |
| C63 — recurrence forme « iteration » : f(0)=a, f(n)=S{f | critere | E III.46 | partiel | ecart_mineur | ensembles_c62_recursion.py:regle_iterati |
| Exemple 1 — recurrence f(0)=a, f(n+1)=g(f(n)) (g:E->E) | remarque | E III.47 | manquant | non_verifiable |  |
| Exemple 2 — n-eme iteree f^n d'une application (f^0=e,  | remarque | E III.47 | manquant | non_verifiable |  |
| Exemple 3 — iteration P^n(E) de l'ensemble des parties | remarque | E III.47 | manquant | non_verifiable |  |
| Remarque — recurrence limitee (f definie seulement sur  | remarque | E III.47 | manquant | non_verifiable |  |
| Theoreme 2 (Hessenberg) — pour tout cardinal infini a,  | theoreme | E III.48 | partiel | ecart_majeur | bourbaki/cardinaux/iii_6_infinis/hessenb |
| Lemme 1 — tout ensemble infini E contient un ensemble e | proposition | E III.47 | partiel | ecart_majeur | references dans frame_zorn/ensembles_fra |
| Lemme 2 — N x N est equipotent a N | proposition | E III.48 | partiel | ecart_mineur | bourbaki/cardinaux/iii_6_infinis/denombr |
| Corollaire 1 — si a cardinal infini, a^n = a pour tout  | corollaire | E III.49 | partiel | ecart_majeur | brique puissance_succ_eq_incond (denombr |
| Corollaire 2 — produit d'une famille finie de cardinaux | corollaire | E III.49 | manquant | non_verifiable |  |
| Corollaire 3 — somme d'une famille (a_i) de cardinaux < | corollaire | E III.49 | manquant | non_verifiable |  |
| Corollaire 4 — a, b non nuls dont l'un infini : a.b = a | corollaire | E III.49 | manquant | non_verifiable |  |
| Definition 3 — ensemble denombrable | definition | E III.49 | clos | fidele | ensembles_infinis.py : est_denombrable(E |
| Proposition 1 — partie / produit fini / reunion d'une s | proposition | E III.49 | partiel | ecart_majeur | ensembles_infinis_props.py : sous_ensemb |
| Proposition 2 — tout ensemble infini denombrable E est  | proposition | E III.49 | partiel | ecart_majeur | forme cardinale dans ensembles_infinis.p |

### III.7 Limites projectives et limites inductives (E III.51–III.65)
_pages : PDF physiques 153–168 (= E III.50–III.65). p.153 = fin III.6 (Prop. 3–5, Cor., D_  (33 notions, 14 manquantes)

> COUVERTURE §III.7 (pages 153-168). Les DÉFINITIONS et le SOCLE sont solidement et fidèlement formalisés : systèmes projectif/inductif (LP/LI, cocycle+identité, lus aussi au niveau des valeurs et certifiés noyau), terme lim_proj + axiome (1), lim_ind=G/R, applications canoniques f_α (proj : pr_α restreint ; ind : Cl_R) avec leurs axiomes définitionnels (S8+A1, theorie==22 préservé), restriction projective à J + axiome (3), systèmes de parties et d'applications (proj/ind) comme prédicats. Plusieurs CŒURS de propositions sont prouvés POINTWISE de façon honnête et non-vide : Prop. 1 existence du cône (+ unicité via extensionnalité dans ensembles_cone_unicite), Cor. Prop. 2 injectivité de u=lim← u_α, Prop. 3 injectivité pointwise sous témoin cofinal, formule (4) coordonnée par coordonnée, Prop. 4 pas-clé du recollement (14)+(15)⇒(1), fonctorialité Cor.2 (proj & ind) au niveau des valeurs.

MANQUES / ÉCARTS MAJEURS (priorité). Côté projectif : les ÉGALITÉS d'ensembles/d'applications globales restent ouvertes là où seul le pointwise est prouvé — (4) g''=g'∘g, (7)/(25) fonctorialité, (8) lim← M_α, (10), bijectivité complète de g (Prop.3), bijection canonique des doubles limites (16)(17)(18). Le THÉORÈME 1 §III.7.4 (non-vacuité, a) f_α(E)=∩f_αβ(E_β), b) E non vide) et la PROPOSITION 5 (surjectivité sous cofinale dénombrable) sont entièrement REPORTÉS, ainsi que les conditions (i)(ii)(ii')(iii)(iv). Côté inductif, le manque est plus profond : R relation d'ÉQUIVALENCE (transitivité) non prouvée, LEMME 1 (relèvement fini) REPORTÉ, donc PROPOSITION 6 (propriété universelle inductive, critères 2°/3°) et PROPOSITION 7 (lim→ injective/surjective) entièrement absentes ; les formules (26)(27) et l'identification des systèmes de parties inductifs non formalisées. Plusieurs EXEMPLES et REMARQUES (Ex.1/2 §III.7.1, diagonale, germes, cas ω lim←=E_ω) ne sont pas formalisés ; exemple_ordre_egalite_produit cité en docstring mais absent du code lu (à vérifier). Globalement : structure et définitions ~clos ; propriétés universelles et théorème de non-vacuité = chantier ouvert, surtout côté inductif.

| notion | type | ref | statut | fidelite | ou |
|---|---|---|---|---|---|
| Conditions (LP_I) (LP_II) d'un système projectif (cocyc | axiome | E III.51 | clos | fidele | ensembles/familles/iii_7_limites/ensembl |
| Limite projective E=lim← E_α : partie de ∏E_α par condi | definition | E III.52 | clos | fidele | ensembles_limites.py: lim_proj, axiome_l |
| Application canonique f_α=restriction de pr_α ; relatio | definition | E III.52 | clos | fidele | ordre/iii_7_limites/ensembles_limites_ca |
| Exemple 1 : préordre=égalité ⇒ lim← = ∏ E_α | remarque | E III.52 | partiel | non_verifiable | ensembles_limites.py (docstring mentionn |
| Exemple 2 : I filtrant, E_α=F, f_αβ=Id ⇒ lim← = diagona | remarque | E III.52 | manquant | non_verifiable |  |
| Application canonique g:E→E' de la restriction de l'ens | definition | E III.52 | clos | fidele | ensembles_limites_canoniques.py: restric |
| Transitivité (4) g''=g'∘g des canoniques de restriction | proposition | E III.52 | partiel | ecart_mineur | ensembles/familles/iii_7_limites/ensembl |
| Proposition 1 (propriété universelle de lim←) : ∃! u:F→ | proposition | E III.53 | partiel | ecart_mineur | ensembles/familles/iii_7_limites/ensembl |
| Corollaire 1 de la Prop. 1 : système projectif d'applic | corollaire | E III.53 | partiel | ecart_majeur | ensembles_limites_canoniques.py: est_sys |
| Corollaire 2 de la Prop. 1 : fonctorialité lim←(v_α∘u_α | corollaire | E III.54 | partiel | ecart_mineur | ensembles_limites_props.py: composition_ |
| Système projectif de parties (M_α⊂E_α, f_αβ⟨M_β⟩⊂M_α) ; | definition | E III.54 | partiel | ecart_mineur | ensembles_limites_canoniques.py: est_sys |
| Proposition 2 : (u_α) sys. proj. d'applications ⇒ u⁻¹(x | proposition | E III.54 | manquant | non_verifiable | ensembles_cofinal.py (notions image_reci |
| Corollaire de la Prop. 2 : u_α injective (resp. bijecti | corollaire | E III.54 | partiel | ecart_mineur | ensembles/familles/iii_7_limites/ensembl |
| Relation (9) u(E)⊂lim← u_α(E_α) (images forment un syst | remarque | E III.55 | manquant | non_verifiable |  |
| Proposition 3 : J cofinale filtrante ⇒ application cano | proposition | E III.55-56 | partiel | ecart_majeur | ensembles_limites_prop2_3_iii7.py: prop3 |
| Remarques 1-3 §III.7.3 : E'_α=f_α(E) système de parties | remarque | E III.55-56 | manquant | non_verifiable |  |
| Double limite projective : système relatif à I×L, formu | proposition | E III.56-57 | partiel | ecart_majeur | ensembles_limites_prop4plus_iii7.py: pro |
| Corollaire 1 Prop. 4 : (17) lim←_{α,λ} u_α^λ=lim←_λ(lim | corollaire | E III.57 | manquant | non_verifiable |  |
| Corollaire 2 Prop. 4 : (18) lim←_α ∏_λ E_α^λ=∏_λ(lim←_α | corollaire | E III.57 | manquant | non_verifiable |  |
| Proposition 5 : I filtrant + partie cofinale dénombrabl | proposition | E III.58 | manquant | non_verifiable | ensembles_cofinal.py (est_systeme_projec |
| Conditions (i)(ii)(ii') sur les ensembles S_α de partie | definition | E III.58 | manquant | non_verifiable |  |
| Théorème 1 : I filtrant, S_α (i)(ii), (iii)(iv) ⇒ a) f_ | theoreme | E III.58-60 | manquant | non_verifiable |  |
| Exemples Th.1 (I : E_α finis / S_α toutes parties ; II  | remarque | E III.60 | non_applicable | non_verifiable |  |
| Conditions (LI_I) (LI_II) d'un système inductif (cocycl | axiome | E III.60-61 | clos | fidele | ensembles_limites.py: cocycle_inductif,  |
| Relation de cohérence R{x,y} sur la somme G=∑E_α ; limi | definition | E III.61 | partiel | ecart_mineur | ensembles_limites_canoniques.py: lambda_ |
| Application canonique inductive f_α:E_α→E (restriction  | definition | E III.61 | clos | fidele | ensembles_limites_canoniques.py: f_canon |
| Exemples §III.7.5 (germes d'applications V_α→B ; E_α=F, | remarque | E III.61-62 | manquant | non_verifiable |  |
| Lemme 1 : tout système fini d'éléments de E=lim→ se rel | proposition | E III.62 | manquant | non_verifiable |  |
| Proposition 6 (propriété universelle de lim→) : u_α∘... | proposition | E III.62-63 | manquant | non_verifiable |  |
| Corollaire 1 Prop. 6 : système inductif d'applications  | corollaire | E III.63 | partiel | ecart_majeur | ensembles_limites_canoniques.py: est_sys |
| Corollaire 2 Prop. 6 : fonctorialité inductive (25) lim | corollaire | E III.64 | partiel | ecart_mineur | ensembles_limites_props.py: composition_ |
| Proposition 7 : (u_α) sys. ind. d'applications, u=lim→  | proposition | E III.64 | manquant | non_verifiable |  |
| Système inductif de parties (M_α⊂E_α, f_βα⟨M_α⟩⊂M_β) ;  | definition | E III.64-65 | partiel | ecart_mineur | ensembles_limites_canoniques.py: est_sys |
| Corollaire Prop. 7 : (i) lim→ u_α(M_α)=u(lim→ M_α) form | corollaire | E III.65 | manquant | non_verifiable |  |
| Remarque 2 §III.7.6 + restriction inductive à J filtran | remarque | E III.65 | manquant | non_verifiable |  |
