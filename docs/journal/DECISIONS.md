

## 2026-08-21 (22h40) — Cantor (iv) : design arrêté — bijection vers les TRIPLES

(iii) CLOSE (bd808a2). Cible fidèle de (v) : 2^a = Card(F(a;2)) — TRIPLES
(Déf. 4, exposant_cardinal_binaire lu). Bijection (iv) : Y ↦ chi_appli(Y) =
((χ_Y, X), 2), graphe B := graphe_terme(parties(X), chi_appli(·)) :
  (a) fonctionnel / dom : lemmes graphe_terme_* (signature T[u] à vérifier) ;
  (b) INJECTIF : 2× couple_egal_implique_composantes (ii_2_1 l.112) ⇒
      χ_Y=χ_{Y'} ⇒ Y=Pre(χ_Y)=Pre(χ_{Y'})=Y' (rho_chi + congruence Pre) ;
  (c) IMAGE = F(X;2) : ⊂ chi_dans_applications (membre_parties : Y∈P(X) ⇒
      Y⊂X) ; ⊇ : t=((G,X),2), G∈2^X (axiome_applications élim ∃) ⇒
      t = chi_appli(Pre(G)) (chi_rho_identite + congruences couple),
      Pre(G)∈P(X) (preimage_inclus + membre_parties ⊇) ;
  (d) Eq(P(X), F(X;2)) par S5.
POINT CLÉ pour (v) : le Th.2 porte sur « tout cardinal a » — PRENDRE
X := a dès le départ : F(a;2) est alors LITTÉRALEMENT le support de 2^a,
zéro pont d'équipotence en (v). (v) = Prop.1 direct sur Eq(P(a), F(a;2)).
NB : le commit b49a90d annonçait cette note mais un caractère astral l'avait
fait échouer — la voici réellement.

## 2026-08-21 23h20 — CIBLE 1 ATTEINTE : Théorème 2 de Cantor LITTÉRAL clos
La file Cantor est TERMINÉE en une soirée : (iii) chi_rho_identite (bd808a2),
(iv) bijection (a) fcd496c + (b) injectif 7db51c9 + (c) image c7a2ac5 +
(d) Eq(P(A),F(A;2)) c078923, puis DÉCOUVERTE : prop12_card était DÉJÀ VERT
(13 passed — card_parties_egale_deux_exp = Prop.12, cantor_deux_exp =
Card X < 2^Card X). Le doc de cantor_strict_cardinal (« cantor_deux_exp lève
NotImplementedError ») était PÉRIMÉ. (v)+(vi) se sont réduits au restatement
littéral theoreme_deux_cantor (e8948ed) : est_cardinal(a) ⇒ a < 2^a, X:=a
(2^a littéral, zéro pont), cardinal_de_cardinal + S6 gauche. @livre Ch.III
§3.6 Th.2 | E III.30 L.20-21 | PDF p.133.
LEÇONS : (1) mes briques (iii)/(iv) dupliquaient en partie prop12_card/_crux
et _bijection — TOUJOURS tester les chantiers voisins avant d'ouvrir une file
(le grep NotImplementedError sur le chantier AVANT de planifier) ; (2) trois
sous-lemmes verts DU PREMIER COUP aujourd'hui : le patron « lire les formes
exactes en code avant d'écrire » paie.
PROCHAIN : CIBLE 2 Hessenberg a²=a (III.6).

## 2026-08-21 23h59 — CIBLE 2 Hessenberg : CARTE COMPLÈTE de la frontière
Suite complète hessenberg/ : 99 passed en 41 min (rien de rouge). La pointe
est `hessenberg_a_carre_egal_a_0hyp(E)` (frame_maximal_clos) : conclusion
enonce_hessenberg(E), E-seule, tous témoins éliminés, lock absent, sous
EXACTEMENT 2 résidus Zorn E-niveau :
  H1 = 𝔉(E)≠∅ (l'amorçage) ; H2 = m_dans_frame_universel (frame-inductivité
  du recollement de chaîne).
Les DEUX butent sur les Lemmes 1-2 de Bourbaki E.III.48, ABSENTS du dépôt :
  L1 « a infini ⇒ ℵ₀ ≤ a » — REPORTÉ (infinis_props l.301 :
     aleph0_inf_egal_cardinal_infini_enonce) ; exige la collectivisation de ℕ
     + la récurrence « n ≤ a pour tout entier n ».
  L2 « ℕ×ℕ ≃ ℕ » — chantier denombrable/ensembles_denombrable_carre_iii6 :
     direction A (ℕ ≤ ℕ×ℕ) CLOSE ; direction B (ℕ×ℕ ≤ ℕ) ⛔ bloquée sur
     l'ARITHMÉTIQUE MULTIPLICATIVE de ℕ : a^b∈ℕ (Cor.3 §III.5.1, récurrence
     Prop.1 §III.5), puis unicité de factorisation OU 2-valuation, d'où
     l'injectivité du pairing (m,n)↦2^m·3^n ; Cantor-Bernstein est déjà là.
ROUTE DE LA CIBLE 2 (ordre d'attaque, du plus élémentaire au sommet) :
  (1) §III.5 arithmétique : a^b∈ℕ par récurrence (le socle C61/Prop.1 existe,
      la division euclidienne d'aujourd'hui en est la preuve de maturité) ;
  (2) le pairing 2^m·3^n injectif (2-valuation OU factorisation minimale —
      décider en lisant ce que le livre fait au juste, E III.48 Lemme 2 :
      développement dyadique — lire PDF p.151 avant de choisir) ;
  (3) L2 par Cantor-Bernstein (direction A déjà close) ;
  (4) L1 (collectivisation ℕ + récurrence n≤a) ;
  (5) décharge H1 (𝔉∋(D,ψ₀) avec D dénombrable ⊂ E par L1, ψ₀ par L2) et
      H2 (le recollement de chaîne, « bute sur Lemme 1 » dixit frame_zorn) ;
  (6) a²=a 0-hyp par hessenberg_a_carre_egal_a_0hyp.
C'est le vrai chantier mathématique (semaines) — exactement l'objectif validé
par Karl (cibles-qui-commandent). Dette signalée : cadre_plat.py 748 l.

## 2026-08-22 00h06 — Lecture PDF p.150-151 (E III.47-48) : Lemmes 1-2 EXACTS
En-têtes vérifiés (E III.47 / E III.48). Th.2 : « Pour tout cardinal infini a,
on a a² = a » (§6.3) — le restatement final devra être littéral-cardinal comme
Cantor (est_cardinal(a) ∧ est_infini(a) ⇒ a·a = a), en plus de la forme
E-niveau du dépôt.
L1 (E III.47) : « Tout ensemble infini E contient un ensemble équipotent à N. »
Démo livre : bon ordre sur E (Zermelo III p.20 th.1) ; E bien ordonné non
isomorphe à un segment propre de N (segment (0,n) fini, III p.16 prop.1 +
p.38 prop.5) ; donc N isomorphe à un segment de E (comparaison III p.21 th.3).
L2 (E III.48) : « L'ensemble N×N est équipotent à N. » Démo livre : ≤ facile
par {0}×N ; injection f par ENTRELACEMENT des développements dyadiques
(φ : N → I^N, I={0,1}, via n = Σ ε_k 2^(r-k-1) (III p.41) ; φ injective par
prop.8 III p.40 ; f(n,n') = l'entier s dont la suite dyadique entrelace
w_2m=u_m, w_2m+1=v_m) ; conclut par antisymétrie de ≤ (Cantor-Bernstein).
CHOIX DE ROUTE pour L2-direction-B (à confirmer après audit iii_5_7) :
  Option F (fidèle) : formaliser §III.5.7 (développement base b, existence+
  unicité) + entrelacement. Le chantier iii_5_7_developpement_base_b EXISTE —
  auditer son état au prochain tick.
  Option V (variante courte) : pairing (m,n) ↦ 2^m(2n+1), unicité par
  2-valuation (division euclidienne par 2 itérée — Th.1 §III.5.6 clos hier).
  Si retenue : écart de DÉMO (énoncé identique) à consigner dans ANOMALIES.
Vu aussi : puissance_entiers_ferme (Fini a^b) existe (n_arith_iii5) sous
prémisses B0(a)/(∀m)B(a,m) à examiner ; iii_5_1 récurrence C61 outillée.

## 2026-08-22 00h15 — ROUTE L2 TRANCHÉE : continuer le chantier 2^m·3^n du dépôt
AUDIT : iii_5_7 (base b) = énoncés seuls, termes opaques (Option F trop
chère) ; MAIS le dépôt a DÉJÀ choisi et fondé la route 2^m·3^n :
  • puissance_deux_trois_NN : Fini n ⇒ Fini 2^n / Fini 3^n — CLOS ;
  • puissance_entiers_inconditionnel (Cor.3 §III.5.1) — CLOS (B0/B déchargés
    par eq_exposant_invariant) ;
  • parite_iii5 : division_par_deux, impair_decompose, un_impair,
    deux_k_plus_un_impair, impair_fois_impair, successeur injectif (Prop.8)
    — « fondation ℵ₀·ℵ₀=ℵ₀ » explicite ;
  • produits_disjoints / produit_union_carre (support cadre-réunion) — clos.
L'injectivité du pairing N'EST PAS commencée. Écart de DÉMO vs livre
(entrelacement dyadique, E III.48) : à consigner dans ANOMALIES quand L2
sera clos — l'ÉNONCÉ Eq(N×N, N) reste identique.
PLAN DE BRIQUES W (un commit testé chacune) :
  W1 trois_puissance_impair : ¬(2 | 3^n) — récurrence (3^0=1 un_impair ;
     3^(n+1)=3^n·3 impair_fois_impair).
  W2 simplification par b>0 : (b·a = b·a') ⇒ a=a' pour entiers — via
     l'unicité du quotient de la division euclidienne §III.5.6 (quotient_de_
     produit : (a=b·q)⇒(q=a/b) + congruence) ; instances b=2, b=3.
  W3 2-valuation : 2^m·u = 2^m'·u' (u,u' impairs) ⇒ m=m' et u=u' —
     récurrence sur m, base par pair_neq_impair, pas par W2(b=2).
  W4 3-injectivité : 3^n = 3^n' ⇒ n=n' — récurrence + W2(b=3) + 1≠3·3^k
     (pair_neq_impair ne suffit pas : 1 impair, 3^k impair — utiliser plutôt
     1 < 3·3^k par monotonie, OU l'unicité W3-analogue en base 3 : à décider
     en écrivant, la division par 3 donne le même patron que la parité).
  W5 injectivité pairing : 2^m·3^n = 2^m'·3^n' ⇒ m=m' ∧ n=n' = W1+W3+W4.
  W6 graphe F = graphe_terme(N×N, 2^(pr1 z)·3^(pr2 z)) : fonctionnel/domaine
     (C54), injectif sur N×N (W5 + couples), image ⊂ N → est_injection_de →
     Card(N×N) ≤ Card N. (Reprendre la représentation de N de la direction A
     NN_inf_egal_NN_carre ; vérifier pr1/pr2 comme termes du dépôt.)
  W7 L2 : Eq(N×N, N) par cantor_bernstein + direction A (close).
Ensuite : L1 (route livre : Zermelo + comparaison th.3 §III.2 — auditer ce
qui existe côté iii_2_bien_ordonnes), puis décharge H1/H2, puis a²=a 0-hyp
+ restatement littéral-cardinal (comme Cantor).

## 2026-08-22 03h20 — L2 : W3 CLOS, W4-W5 écrits (nuit de l'arithmétique)
W3 deux_valuation_unique CLOS (0e0e4a8, 38 min de C61) : l'unicité 2-adique
SANS report — la route « écart d=m'−m » butait sur fini_downward (REPORTÉ,
bon ordre des cardinaux) ; la récurrence C61 patron pair_neq_impair l'évite
(le prédécesseur s'applique à mp, FINI PAR HYPOTHÈSE du corps ∀-imbriqué).
Briques neuves en route : exposant_somme_pont (base^(m+d)=base^m·base^d,
Cor.1 §III.3.5 aux opérations), puissance_non_nulle (base^n≠0, C61),
ops_produit_commutatif/associatif (ponts Card intercalés), exposant_zero_un,
ops_produit_un_droite (neutre x·1=x).
W4 trois_puiss_injectif écrit (en test) : C61, cœur absurde 1=3^(succ j) par
produit/somme_succ_distribue + Prop.8 + successeur_non_nul — PAS d'ordre.
W5 pairing_injectif écrit : assemblage pur W1+W3+W4.
LEÇONS de capture (cumul de la nuit) :
  8. congruence_terme(t,u,v,w='w') : trou EXPLICITE si le template n'use pas w.
  9. lieur d'un ∃ à éliminer ≠ tout témoin reçu de l'appelant (kpred vs kpred2
     dans un helper appelé SOUS un autre prédécesseur).
  10. les keystones-à-noms se ∀-closent sur LEURS noms puis s'instancient aux
     termes ; ne jamais gen sur Z (τ de cardinal), F/G (∃ bij), w (trou).
RESTE pour L2 : W6 graphe est_injection_de(F, N×N, N) (lire la repr. N de la
direction A + pr1/pr2 + pont ∈N/Fini), W7 Eq par Cantor-Bernstein.

## 2026-08-22 08h30 — 🎉🎉🎉 LEMME 2 CLOS : Eq(ℕ×ℕ, ℕ) (3 passed, 2 h 53)
La route L2 est TERMINÉE : W1-W7 tous clos. Chronologie des validations :
W1+W2 (44 min), W3a (7 s), W3b (3 min), ops commut/assoc (4 s),
W3 deux_valuation_unique (38 min), W4 trois_puiss_injectif (34 min),
W5 pairing_injectif (1 h 30), W6+W7 graphe+Cantor-Bernstein (2 h 53).
Leçons 11/11bis/12 (capture C54) : la variable du terme C54 doit être
FRAÎCHE si le terme contient des τ à lieurs x/y (pr1/pr2) ; y reste au
DÉFAUT (valeur_caracterisation le code en dur) ; graphe_terme_domaine
patché (α-récupération du lieur si l'axiome DOM renomme — additif,
non-régression cantor 14 passed).
RESTE pour CIBLE 2 : L1 (tout infini ⊃ dénombrable), décharge H1/H2 Zorn,
a²=a 0-hyp + littéral.

## 2026-08-22 08h35 — Cahier des charges décharge H1/H2 (lecture des formes)
residu_H1 = (∃x)(x ∈ 𝔉(E)) ; residu_H2 = (∀C)((⋃S(C),⋃φ(C)) ∈ 𝔉(E)).
𝔉(E) = {p | ∃S∃φ(p=(S,φ) ∧ S⊂E ∧ S INFINI ∧ φ bij S×S→S)} (axiome_frame).
⚠️ DIAGNOSTIC H2 : le ∀C est NU — pour C:=∅ le recollement est (∅,∅) et
« ∅ infini » est FAUX : H2 semble INSATISFIABLE telle quelle. La décharge
exigera de REFORMULER l'inductivité (frame_inductif_assemblage /
enonce_chaine_majoree_preuve) : cas C=∅ majoré par le témoin de H1, garde
« C ≠ ∅ » (ou « C chaîne de 𝔉 ») sur le résidu de recollement. À VÉRIFIER
finement (union_premiere(∅) = ∅ ?) avant de restructurer — si confirmé,
consigner aussi dans ANOMALIES (le résidu du chantier Zorn était trop fort).
PLAN : (1) H1 D'ABORD — témoin (D,ψ) : L1 donne D⊂E, Eq(D,ℕ) ; D infini
via Card D = ℵ₀ (aleph0/est_infini_ensemble, brique-surensemble p5c l.154) ;
ψ par élim ∃ de Eq(D×D,D) = transport de L2 (Eq(D,ℕ) + eq_produit_invariant
+ transitivité/symétrie + lemme_deux_NN) ; S5 ×2 vers le corps ∃S∃φ.
(2) L1 : audit iii_2_bien_ordonnes (Zermelo/th.3/segments) vs route ÉTAPE C
de N_collectivise (n≤a). (3) H2 ensuite (restructuration + recollement).

## 2026-08-22 09h35 — AUDIT iii_2 : 621 passed (47 min) — ROUTE-LIVRE L1 retenue
TOUT iii_2_bien_ordonnes est VERT. ZERMELO EST CLOS ET INCONDITIONNEL :
⊢ (∃R) est_bien_ordonne(R_R, X) (zermelo.py l.2594, via Zorn sur le poset
des bons ordres partiels en end-extension). La trichotomie des ordinaux
(comparaison th.3) est le 2e pilier — conclusions exactes à relire au
prochain tick (trichotomie_ordinaux/assemblage : « DEUX VERSIONS LIVRÉES »).
DÉCISION : route-livre pour L1 (E III.47 Lemme 1) — bon ordre sur E
(Zermelo) + comparaison (E,R) vs (ℕ,≤) + « segment propre de ℕ ⇒ fini »
(realisation_segment/intervalles §III.4) ; la route-cardinale reste bloquée
par le passage sup (∀n n≤a → ℵ₀≤a, arithmétique infinie absente).
CIBLE MINIMALE pour H1 (suffit) : {est_infini(Card E)} ⊢ (∃D)(D⊂E ∧ Eq(D,ℕ))
— H1 se décharge SOUS Inf par restructuration légale (assume Inf ; L1 ; cut ;
loi_deduction), donc L1 conditionnel à l'infinité suffit.

## 2026-08-22 09h40 — Trichotomie (th.3) : SOUS RÉSIDU residu_univ_app
Précision d'audit : la trichotomie des bons ordres n'est PROUVÉE que sous
{bo(R,E), bo(Rp,F), residu_univ_app} (trichotomie_ordinaux_canon_prouve,
assemblage l.185). Le résidu structurel est PRÉCISÉMENT rapporté :
  #8  est_segment(image(φ_grand, S_petit), R', F) — « l'image d'un segment
      par un isomorphisme est un segment » ;
  #13 une inclusion de graphe du chevauchement des isos (Lemme 1 §III.2).
Ces deux briques MANQUENT (pas d'impossibilité structurelle — des lemmes
segment/iso à construire). ROUTE L1 ACTUALISÉE : attaquer #8 puis #13 pour
clore la trichotomie, PUIS L1a-d (Zermelo clos + comparaison + segments).
Alternative en réserve : construction directe de D par itération C63
(E III.47 Exemple 1 — vérifier l'état de C63 dans le dépôt si #8/#13
résistent).

## 2026-08-22 09h45 — L1 : ROUTE DEDEKIND retenue (trichotomie : résidu quadruple)
Lecture complète du résidu trichotomie : R1 (#8 image-segment + #13
resserrage), R2 (val_dans_F), R3 (h_graphe_hyp — BLOQUÉ par l'axiome opaque
de h qui ne caractérise que les couples : restructuration d'axiome), R4
(segment pr₂h). R3 rend la clôture de la trichotomie un chantier lourd.
ROUTE DEDEKIND pour L1 (écart de démo vs livre, énoncé identique, à
consigner dans ANOMALIES quand clos) :
  D1 Dedekind : est_infini(a) ⇒ a = a+1 — dedekind_cardinal INCONDITIONNEL ✓
     (infinis_props l.150) ; pour a := Card E : Eq(E, E⊔{∅})-transport →
     une bijection g̃ : E⊔{∅} → E ; g := restriction de g̃ à E (injection
     E→E) et e₀ := g̃((∅,1)) ∉ image(g) (l'injectivité sépare les images).
  D2 l'itération : f(n) = gⁿ(e₀) — C62/C63 existent (regle_iteration,
     iii_1_7/terme_plus_grand + recursion_hygienic §6.2) ; caveat (O1) :
     C63 ne livre pas f assemblée mais une conclusion quantifiée — lire la
     forme exacte et éliminer les ∃.
  D3 injectivité de n ↦ gⁿ(e₀) : récurrence C61 (patron W3/W4 de la nuit) —
     gⁿ(e₀)=gᵐ(e₀) ∧ n<m → simplifier par g (injective) → e₀ = g^(m-n)(e₀)
     ∈ im(g), contredit e₀ ∉ im(g).
  D4 D := image de f ; Eq(ℕ, D) (graphe injectif → bijection sur image,
     patron W6/bijection_injective) ; D ⊂ E ; sym → cible L1 minimale
     {est_infini(Card E)} ⊢ (∃D)(D⊂E ∧ Eq(D,ℕ)).
PROCHAIN : lire regle_iteration/C63 (factorielle_existence l.26-60 +
recursion_hygienic) — la forme exacte de ce que C63 conclut.

## 2026-08-22 09h50 — D2 VIABLE : les obstructions C63 sont levées
Lecture factorielle_existence : (O1) RÉFUTÉ (la fonction assemblée existe
depuis le 25 juil. — chantier iii_6_2_recursion_c62 : fonction_globale/
existence/unicite/domaine/restriction) ; (O3) RÉFUTÉ (le « renommage gratuit »
de subst corrigé par court-circuit CS) ; (O2) vrai mais SANS OBJET pour D2
(l'itération gⁿ(e₀) est index-INdépendante — exactement la forme C63
regle_iteration(S, a) : T{u} = τ_y((u=∅ ∧ y=a) ∨ (u≠∅ ∧ y=S{u(M(Du))})),
c62_recursion l.171 ; S := valeur(g, ·), a := e₀).
PROCHAIN : lire la conclusion EXACTE du capstone (c62_fonction_globale +
c62_recursion_sur_N l.106 : signature (vh, e=Enat, G=Gle, V=Uval...) — vh ?
sous quelles hypothèses ; puis tests miroir iii_6_2 pour l'état vert).
Ensuite D1 (bijection Dedekind → g, e₀), D3 (injectivité C61), D4 (image).

## 2026-08-22 09h55 — PANORAMA L1 (honnête) : trois routes, trois chantiers
C62 est VERT (39 passed) et conclut fonction_recursion_c62 :
{bo, ebf, rc} ⊢ (∃f)(fonctionnel ∧ dom=E ∧ ∀z(z∈E ⇒ f(z)=T(z))) — MAIS
l'équation est au niveau VALEUR-RÈGLE (T appliquée au POINT z), pas encore
f(z)=T{f|seg(z)} : le PONT-RESTRICTION est « le chantier suivant » (docstring
fonction_existence). L'itération D2 (f(n+1)=S{f(n)}) en dépend. De plus 3
résidus C62 {bo, ebf, rc} à identifier/décharger pour E=ℕ.
ROUTES L1 : (1) trichotomie — résidus R1-R4, R3 bloqué (axiome opaque de h) ;
(2) Dedekind — pont-restriction C62 + 3 résidus ; (3) cardinale — sup absent.
DÉCISION : continuer (2) — l'infrastructure essais/famille est VERTE et le
pont-restriction est un chantier LOCALISÉ (l'équation d'essai contient déjà
la lecture de la restriction : il s'agit de la faire remonter à f=⋃𝔇).
PROCHAIN : lire les 3 résidus {bo, ebf, rc} (fonction_domaine) + l'équation
d'essai (est_essai) + évaluer le pont pour la FORME ITÉRATION précisément
(pour regle_iteration, T(z) au point vs T{restriction} : la règle τ lit
u(M(Du)) — au point z, T(z) est... relire la définition exacte).
NOTE session : la CIBLE 2 complète (a²=a 0-hyp) reste un chantier de
plusieurs jours ; les jalons de session (Cantor, L2, Prop.2) sont déjà
poussables — PUSH JALON dès que Karl est là.

## 2026-08-22 10h00 — DIAGNOSTIC FINAL front L1 : la récursion réelle manque
est_essai (c60_existence_close l.337) : l'équation est valeur(p,z) = vh(z)
avec vh : Terme→Terme appliquée AU POINT z — vh ne reçoit JAMAIS p. C'est
une TABULATION (f = graphe de vh), pas l'équation de récursion
f(z)=T{f|seg(z)} : le chantier C60/C62 « hygienic » a dérivé l'existence
d'une fonction tabulée, l'équation récursive est l'« écart de fidélité »
avoué de fonction_existence. La route D2 (itération gⁿ(e₀)) attend donc une
REFONTE de l'équation d'essai (profonde : C59/C60/C62 re-dérivés avec
vh(restriction(p, seg(z)))).
FRONT L1 (résumé pour Karl) — trois routes, trois murs :
  (1) trichotomie th.3 : résidus R1-R4, R3 sur axiome opaque (refonte h) ;
  (2) Dedekind/itération : équation de récursion absente (refonte C60+) ;
  (3) cardinale : passage sup (∀n n≤a → ℵ₀≤a) absent.
Le mur (2) est le plus « rentable » (débloque récursion partout : factorielle
index-dépendante incluse) mais c'est une refonte multi-jours. PIVOT du matin :
rapport V9 (documenter Prop.12+Th.2 Cantor + Lemme 2 — livrable en attente),
en laissant le choix du mur à discuter avec Karl (stratégie cibles).

## 2026-08-22 10h05 — Proposition à Karl : rafraîchir CLAUDE.md §Suivi de couverture
Le paragraphe « Gros chantiers ouverts » de CLAUDE.md est périmé : Cantor
2^a>a est FAIT (CIBLE 1), la division euclidienne est FAITE (Th.1 complet).
Restent réellement : Hessenberg a²=a (frontière = L1 + H2, cartographiée),
bon ordre des cardinaux (III.3), limites (III.7), CST1/CST2 (IV). À valider
par Karl avant toute édition de CLAUDE.md (consigne utilisateur).

## 2026-08-22 10h10 — DESIGN R' (refonte C60-récursion, mur 2) — à valider avec Karl
La nouvelle équation d'essai : p(z) = vh(restriction(p, seg(R,E,z))) — la
règle lit LA RESTRICTION (vraie récursion), au lieu de vh(z)-au-point
(tabulation actuelle). Chantier C60 existant : 8 modules (clauses, coeur,
existence_close, final, pont, realisation, recurrence_transfinie,
recursion_transfinie_existence), extension_un_pas en 3 variantes,
heredite_couverture_realisee (final l.646). Briques du design :
  R1' est_essai_rec : le prédicat avec l'équation-restriction (± 0,5 j).
  R2' UNICITÉ des essais-rec (deux essais en x coïncident sur seg∪{x}) —
      induction C59 sur « coïncide sous z » ; LE morceau dur : remplace
      l'épinglage-tabulation dans la coïncidence de famille (± 2-3 j).
  R3' hérédité : extension d'un cran p' = p ∪ {(x, vh(p|seg(x)))} — les
      extension_un_pas_* se réutilisent (fonctionnalité/domaines), la
      valeur au nouveau point est bien définie par construction (± 1-2 j).
  R4' couverture C59 → (∀x∈E)(∃p essai-rec) (± 1 j, calque de l'existant).
  R5' bien-formés/codomain pour la règle concrète (± 0,5 j).
  R6' famille 𝔇_tot + union + capstone : la coïncidence de famille passe
      par R2' (± 1-2 j).
  R7' spécialisation ℕ (bo_graphe_NN clos) (± 0,5 j).
  R8' itération : dériver f(0)=a ∧ f(succ n)=S(f(n)) de l'équation-
      restriction — DEUX évaluations du τ de regle_iteration (branche u=∅ ;
      branche u≠∅ avec M(D(u))=n) : ⚠️ INCONNUE-CLÉ : l'évaluation du τ
      exige soit les tactiques τ existantes (existe_temoin/S7, patron
      chi/_fonct_un_zero), soit un axiome-définition dédié (motif
      diff/preimage). À VÉRIFIER avant tout engagement (± 1-3 j selon).
TOTAL estimé : 7 à 13 jours de ticks. GAIN : la récursion réelle pour tout
le dépôt (L1-Dedekind, factorielle index-dépendante via C62-rec, suites).
ALTERNATIVES : mur 1 (trichotomie R1-R4, R3 = refonte d'axiome opaque de h,
estimé comparable, gain limité au th.3) ; mur 3 (sup cardinal, non exploré).
DÉCISION EN ATTENTE DE KARL. En attendant : vérifier l'inconnue-clé R8'.

## 2026-08-22 10h12 — R8' : l'inconnue-clé est LEVÉE (patron t_fac_en_non_vide)
L'évaluation du τ-disjonctif de regle_iteration a son patron COMPLET dans
factorielle_succ.t_fac_en_non_vide : sous Γ ⊢ ¬(u=∅), la garde-disjonction
(_garde_disjonction + _ou_commute_gd) réduit le corps à (y=Sval), puis S7
(τ-extensionnalité) et S5+existe_temoin évaluent τ(y=Sval)=Sval — asserts
d'hygiène inclus (hypothèses conservées). Le cas u=∅ est symétrique.
⇒ R8' ≈ 1 jour. DESIGN R' CONSOLIDÉ : 7-9 jours estimés au total.
Recommandation ferme à Karl : mur 2 (refonte C60-récursion, R1'-R8') —
débloque L1-Dedekind, la factorielle index-dépendante, et toute suite
récurrente à venir. Prêt à commencer R1' sur son accord.

## 2026-08-22 10h20 — R' RÉVISION MAJEURE : le pont-restriction a déjà son CŒUR
c62_fonction_restriction (jamais cité par fonction_existence !) contient :
  restriction_egale_essai_seg {p∈𝔇_tot, est_essai(p,x)} ⊢ f|seg(x) = p|seg(x)
— la cohérence des essais au niveau graphe (sens dur par l'épinglage). DONC
la stratégie du dépôt était probablement : équation-au-point f(z)=vh(z) PLUS
le pont f|seg=p|seg, et la forme fidèle f(z)=T{f|seg(z)} se DÉRIVE si vh(z)
est définie comme T{essai-canonique(z)|seg(z)} (τ-sélection indépendante de
p). HYPOTHÈSE À VÉRIFIER au prochain tick : lire les USAGES de vh (qui
choisit la règle dans les théories dédiées theorie_Dtot/theorie C60 — la
règle est un callable ambiant : l'instancier en (z ↦ T{restriction(f, seg z)})
est-il LÉGAL (f = le terme-union, indépendant de p ✓ !) — ALORS l'équation
f(z) = T{f|seg(z)} sort DIRECTEMENT de fonction_recursion_c62 avec CE vh,
sans AUCUNE refonte : vh(z) := T(restriction(Dtot-union, seg(z))) est un
Terme→Terme parfaitement valide !!). Si ça tient : R' se réduit à R5'+R8'
(bien-formés/codomain pour cette règle + évaluation τ) ≈ 2-3 jours.

## 2026-08-22 10h25 — CLEF vh* REJETÉE (soundness) : imprédicativité de l'axiome
Vérification code : Dtot(e,V) = app("c62_Dtot", E, V) — le terme est vh-libre
✓. MAIS l'axiome de sélection de theorie_Dtot(vh*) aurait son SÉLECTEUR
mentionnant restriction(union(Dtot(E,V)), ...) — c'est-à-dire LE TERME QUE
L'AXIOME DÉFINIT, dans son propre membre droit : un POINT FIXE imprédicatif,
PAS une instance de S8 (dont le prédicat doit être donné avant l'ensemble).
Un tel axiome pourrait encoder p∈D ⇔ p∉D : INTERDIT par la frontière de
confiance. La clef-raccourci est morte ; en revanche le prédicat
est_essai_rec (R1') est S8-LÉGAL (l'équation mentionne p lui-même — une
formule en p, aucune référence au terme défini). RETOUR AU PLAN R'
(R2'-R8', 7-9 j), avec la bonne nouvelle intacte : le patron du pont
(c62_fonction_restriction) et t_fac_en_non_vide se réutilisent comme
PATRONS de preuves dans la refonte.

## 2026-08-22 10h28 — DESIGN FIN R2' (unicité des essais-rec)
Squelette : couverture_transfinie(P, e, G, ...) : {bo, heredite_couverture(P)}
⊢ (∀x)(x∈E ⇒ P(x)) — le C59 du dépôt (recursion_transfinie_existence l.250,
utilisé par couverture_essais_via_c59). Pour l'unicité, P est paramétré par
DEUX essais-rec p (en xp) et q (en xq) :
    P(z) := (z ∈ dom p ∧ z ∈ dom q) ⇒ valeur(p,z) = valeur(q,z).
Hérédité sous HR = (∀y∈seg z)P(y) et z∈les deux doms :
  R2'a — ÉGALITÉ DES RESTRICTIONS : p|seg(z) = q|seg(z).
    Sous-briques : (i) dom(p|seg z) = dom p ∩ seg z (lemme restriction-dom —
    chercher/écrire) ; (ii) seg z ⊂ dom p et ⊂ dom q (z ∈ seg(xp)∪{xp} et
    l'ordre est transitif : y<z ≤ xp ⇒ y ∈ seg(xp) — brique
    segment-transitivité, chercher dans segment_extremite-lemmes) ; donc les
    deux restrictions ont LE MÊME domaine seg z ; (iii) valeurs égales sur ce
    domaine (HR instanciée) ; (iv) extensionnalité des graphes fonctionnels
    (patron graphe_egal_par_valeurs, prop12) → égalité.
  R2'b — CONGRUENCE DE LA RÈGLE : (A=B) ⇒ vh(A)=vh(B) par
    congruence_terme(A, B, vh(var("wrec")), "wrec") (vh accepte var ✓) ;
    avec les équations d'essai instanciées en z : p(z) = vh(p|seg z)
    = vh(q|seg z) = q(z). ✓
Écriture : R2'a d'abord (fichier rec_veritable/ensembles_restrictions_egales.py,
briques (i)-(iv)), puis R2'b+induction (ensembles_unicite_essai_rec.py).

## 2026-08-22 10h30 — R2'a : AXIOME_RESTRICTION est z-ARBITRAIRE (bonne nouvelle)
(∀F)(∀X)(∀z)(z∈f|X ⇔ (∃p)(∃q)(z=(p,q) ∧ p∈X ∧ (p,q)∈F)) — l'axiome (l.970
abrege, dans les 22) caractérise un z arbitraire, PAS seulement les couples
(contrairement à l'axiome de h qui bloque la trichotomie, R3). Liants p/q.
Toutes les briques R2'a en découlent : (i) dom(f|X) = dom f ∩ X (par AXIOME_
DOM + l'axiome ci-dessus), (ii) l'inclusion f|X ⊂ produit (idem), (iii) les
valeurs (valeur_caracterisation), (iv) graphe_egal_par_valeurs. Écriture de
rec_veritable/ensembles_restrictions_egales.py au prochain tick.

## 2026-08-22 10h35 — R2'a : brique (i) DÉJÀ CLOSE + inventaire
restriction_dom_sous_inclusion (cantor_bernstein_bij l.150) : ⊢ (X ⊂ dom F)
⇒ dom(f|X) = X — exactement la forme utile (X := seg z, avec (ii)
seg z ⊂ dom p). restriction_domaine_piece (iso_ordre) = la version
à-hypothèse. RESTE pour R2'a : (ii) seg-transitivité (chercher dans
segment_extremite-lemmes/bon_ordre : « z∈dom_essai(x) ⇒ seg z ⊂ dom_essai(x) »
— découle de la transitivité de l'ordre + structure seg(x)∪{x}) ; (iii)
valeur de la restriction ((p|X)(u)=p(u) pour u∈X∩dom — chercher
restriction_valeur / _restriction_valeurs_coincident (prop9_close l.559) /
dans cantor_bernstein_bij ; sinon dériver de AXIOME_RESTRICTION +
valeur_caracterisation) ; (iv) graphe_egal_par_valeurs (patron prop12).

## 2026-08-22 10h45 — R2'a : briques (ii) CLOSE et (iii) DÉJÀ CLOSE
(ii) ÉCRITE ET VERTE (rec_veritable/ensembles_seg_transitif.py, commit 4762f29,
2 passed 0.08 s) : seg_transitif_strict {bo} ⊢ (z∈seg x ∧ u∈seg z) ⇒ u∈seg x
(transitivité + antisymétrie extraites de est_bien_ordonne, patron CASE A/B
factorisé de couverture_segment_realise) ; seg_inclus_dom_essai {bo} ⊢
z∈dom_essai(x) ⇒ seg z ⊂ dom_essai(x) (cas z∈seg x / z=x par S6, puis
S2+axiome-réunion). UNE hypothèse honnête chacun (le bon ordre).
(iii) DÉJÀ CLOSE, rien à écrire : restriction_valeur (cantor_bernstein_bij
l.206) {F fonct, u∈X, u∈dom F} ⊢ (f|X)(u)=F(u) — accepte des TERMES (_t),
donc directement applicable à p|seg(z). En bonus pour (iv) :
_restriction_fonctionnelle_terme ⊢ func(F) ⇒ func(f|X) (implication CLOSE)
et _restriction_incluse_terme ⊢ f|X ⊂ F, mêmes signatures-termes.
RESTE R2'a : (iv) seule — assembler graphe_egal_par_valeurs (patron prop12)
sur p|seg z et q|seg z : fonctionnelles (✓ _restriction_fonctionnelle_terme),
incluses dans un produit (via f|X ⊂ F + F ⊂ E×V hypothèse honnête de R2'),
doms égaux ((i)+(ii) : les deux valent seg z), valeurs égales (HR + (iii)).
Leçon : les deux ticks de recherche ont évité ~150 lignes de redérivation.

## 2026-08-22 10h58 — R2'a COMPLET : brique (iv) restrictions_egales CLOSE
rec_veritable/ensembles_restrictions_egales.py (1 passed 0.28 s) :
restrictions_egales {bo, func p, func q, dom p=dom_essai(x), dom q=dom_essai(x),
z∈dom_essai(x), HR:(∀u)(u∈seg z ⇒ p(u)=q(u))} ⊢ p|seg z = q|seg z.
Assemblage exactement comme conçu : graphe_egal_par_valeurs à 6 prémisses
gauche-associées ((((func∧func)∧gr)∧gr)∧dom)∧val, lieur « x » imposé par
egalite_valeurs (aucune capture : mes noms pre/qre/Gsr/Esr/xsr/zsr/ure).
hypothese_recurrence(p,q,G,e,z) exporté = la forme EXACTE que l'induction
C59 devra fournir (interface R2'a↔R2'b propre).
PLAN R2'b (prochain fichier rec_veritable/ensembles_unicite_essai_rec.py) :
sous les hyps est_essai_rec(p,x) ∧ est_essai_rec(q,x) déplier les deux
équations en z (instancie à vz + mp z∈dom p), congruence_terme(p|seg z,
q|seg z, vh(var("wrec")), "wrec") sur restrictions_egales → vh(p|seg z)=
vh(q|seg z), composer p(z)=vh(p|seg z)=vh(q|seg z)=q(z) ; PUIS l'induction
C59 (couverture_transfinie {bo, heredite}) sur P(z) := z∈dom_essai(x) ⇒
p(z)=q(z) pour décharger l'HR — ATTENTION : l'HR de couverture_transfinie
porte sur TOUT z∈E (vérifier la forme exacte de heredite_couverture(P)).

## 2026-08-22 11h12 — 🏆 R2' CLOS EN 6 TICKS : l'unicité de la vraie récursion
unicite_essai_rec {bo, essai p, essai q, x∈E, graphe p, graphe q} ⊢ p=q
(commit 675ae56, 9 passed, fichier 279 l.). Chaîne complète :
R2'a (i) restriction_dom_sous_inclusion [déjà close] + (ii) seg_transitif
[4762f29] + (iii) restriction_valeur [déjà close] + (iv) restrictions_egales
[36124c2] → unicite_au_point [2052054] → couverture_unicite C59 [9ac1825]
→ dom_essai_inclus_E + graphe_egal_par_valeurs → p=q [675ae56].
TECHNIQUES-CLÉS consignées : prédicat C59 GARDÉ par le domaine (le dégardage
par seg_inclus_dom_essai) ; affaiblissement loi_deduction (hyps-{a}, a absent
OK) pour le conjoint x∈E de l'hérédité ; liants x0tf/ytf imposés par
couverture_transfinie ; l'appel unicite_au_point(z="x0tf") DIRECTEMENT au nom
du liant avant generalisation (pas de α-détour).
PROCHAIN — R3' (hérédité-EXISTENCE de la couverture couvert_essai_rec) :
l'essai étendu p' := p ∪ {(x, vh(p|seg x))} pour x non couvert ; chercher
extension_un_pas / prolongement dans c60 (grep extension\|prolonge dans
recurrence_transfinie + c60_final l.646 heredite_couverture_realisee comme
patron structurel) ; les briques recollement (reunion_essais_fonctionnelle,
valeur_essai_reunion) sont DÉJÀ closes au niveau binaire — le pas p∪{(x,v)}
est EXACTEMENT ce niveau binaire (singleton = essai trivial ? NON : le
singleton {(x,v)} est fonctionnel/dom={x} — briques singleton à chercher).

## 2026-08-22 11h18 — R3' : DESIGN ARBITRÉ (route B binaire) + carte de réutilisation
DÉCISION : R3'-binaire d'abord (l'extension p' := p∪{(x, vh(p|seg x))} pour p
« essai-sur-seg(x) » : func p, dom p=seg(x), équation-restriction sur dom p),
la famille/recollement (route A, analogue Dfam avec P2-coïncidence PAR R2'-
unicité au lieu de valeurs-épinglées) viendra pour le cas limite en R4'.
CARTE DE RÉUTILISATION (vérifiée en code ce tick) :
- func(p∪S) : extension_un_pas_fonctionnelle (c60_existence_close l.290,
  {func p, dom p=seg}) — DIRECTEMENT réutilisable ✓
- (p∪S)(x)=v : valeur_reunion_point(g,j,x) (produit_adjonction_briques,
  {func(G∪S)} ⊢ (G∪{(j,x)})(j)=x, TERMES génériques) ✓
- (p∪S)(z)=p(z) sur dom p : valeur_reunion_gauche(g,h,t) (idem, TERMES —
  PAS la version famille de c60_final) ✓
- dom(p∪S) : dom_reunion_graphes (restriction_somme l.187, CLOS) + dom du
  singleton (chercher E2 dans c60_existence_close) → dom p'=seg∪{x}=dom_essai ✓
- helper _dech(thm,*preuves) (adjonction_briques) = multi-coupure ✓
- patron témoins ∃p∃q de AXIOME_RESTRICTION : restriction_est_graphe
  (adjonction_briques l.93 : subst_f+S5 re-liage, existe_elimination ×2) ✓
BRIQUE NOUVELLE UNIQUE : restriction_reunion_singleton_hors {¬(x∈X)} ⊢
(p∪{(x,v)})|X = p|X — double inclusion par AXIOME_RESTRICTION, cas (pb,qb)∈S
absurde (pb=x∈X par couple_egal_implique_composantes+S6, contredit x∉X,
ex falso via patron s2-encodage) ; puis x∉seg x vient de l'axiome-segment
(conjoint y≠x avec y:=x : x∈seg x ⇒ x≠x ⇒ absurde avec reflexivite).
ASSEMBLAGE FINAL extension_essai_rec : équation en z∈dom p' par cas
(z∈dom p : valeur_reunion_gauche + équation-p + p'|seg z=p|seg z [la brique
nouvelle, x∉seg z car seg z⊂seg x∌x… NON : x∉seg z car z∈seg x → seg z⊂seg x
(seg_transitif !) et x∉seg x] ; z=x : valeur_reunion_point + p'|seg x=p|seg x
= p [restriction pleine : dom p=seg x → p|dom p=p — chercher
restriction_identite/restriction_totale, sinon dériver] + v:=vh(p) donc
vh(p'|seg x)=vh(p)=v par congruence).
⚠️ MANQUE ENCORE : p|dom p = p (restriction identité) — grep au prochain tick.

## 2026-08-22 11h34 — 🏆 R3' CLOS : le prolongement d'un pas (extension_essai_rec)
{bo, func p, dom p=seg(x), graphe p, éq-seg} ⊢ est_essai_rec(p∪{(x,vh(p))}, x)
(dc4b2ab, 5 hyps, 13 tests rec_veritable verts). Clé conceptuelle : v := vh(p)
— la règle appliquée à p ENTIER, qui EST p'|seg(x) après effacement (brique 1)
et restriction pleine. Le pas de la vraie récursion tient en ~90 l. grâce à la
carte de réutilisation (extension_un_pas_fonctionnelle, valeur_reunion_*, doms).
ÉTAT DU CHANTIER R' : R1' (prédicat) ✓ R2' (unicité) ✓ R3' (pas) ✓.
RESTE POUR LA COUVERTURE (R4', le morceau famille/limite) : pour x∈E avec
(∀y<x) couvert_essai_rec(y), construire l'essai-SUR-SEG p_seg (recollement
⋃D des essais des y<x) puis R3' conclut couvert_essai_rec(x). Structure =
couverture_segment_realise/Dfam_real de C60 déposé MAIS : (P2-coïncidence)
vient de R2'-unicité (les valeurs d'essais récursifs distincts coïncident où
les deux sont définis — ATTENTION R2' unifie des essais AU MÊME point x ; pour
y≠y' il faut « l'essai de y restreint à seg(y'')∩… coïncide » — le VRAI
argument : deux essais récursifs p_y, p_y' avec y'≤y : p_y|dom_essai(y') est
un essai récursif en y' (LEMME R4'a À ÉCRIRE : la restriction d'un essai
récursif à un dom_essai inférieur est un essai récursif — équation par
restriction-de-restriction : (p|A)|seg z = p|seg z si seg z ⊂ A… composition
de restrictions À CHERCHER) puis R2'-unicité en y' donne p_y|… = p_y' ✓) ;
(P3-domaine) = réunion des dom_essai(y) pour y∈seg x = seg x (chaque y∈seg x
est dans son propre dom_essai ⊂ seg x quand y<x : dom_essai(y)⊂dom_essai(x)
par seg_inclus + {y}⊂seg x) ; (P4-équation sur la réunion) = valeur_union +
équation des membres. GROS MORCEAU (S8-collectivisation de la famille D :=
{p ∈ 𝔓(E×V) | ∃y∈seg x, est_essai_rec(p,y)} — vérifier le patron
Dfam_real/_inst_Dfam_real de c60_realisation, S8-légal).
PROCHAIN TICK : lire c60_realisation (Dfam_real, l'axiome S8, ambiant) +
chercher composition de restrictions ((p|A)|B = p|B si B⊂A ou p|A∩B).

## 2026-08-22 11h45 — R4' COMPLET + design R5'-coïncidence SANS wlog
R4'b composition_restrictions (207d435) + R4'a restriction_essai_rec/
dom_essai_monotone (d1a06cc) : 19 tests rec_veritable verts, tout premier-coup.
DESIGN R5'-COÏNCIDENCE (l'écueil wlog résolu) : pour p essai-en-y, q essai-en-
y', a∈dom p∩dom q : descendre LES DEUX au point commun — a∈dom p=dom_essai(y)
donc restriction_essai_rec donne p|dom_essai(a) essai-EN-a (idem q) ; R2'-
unicité (unicite_essai_rec) au point a donne p|dom_essai(a) = q|dom_essai(a) ;
puis p(a) = (p|dom_essai(a))(a) [restriction_valeur, a∈dom_essai(a) car
a∈{a}⊂dom_essai(a) — PETIT LEMME point_dans_dom_essai à écrire : S2+réunion]
= (q|…)(a) = q(a). Besoins R2' : a∈E (de a∈dom_essai(y)⊂E, dom_essai_inclus_E
sous y∈E — y∈seg(x)⊂E dans la famille ✓) + graphes des restrictions
(restriction_est_graphe CLOS ✓). AUCUNE trichotomie, AUCUN wlog.
PROCHAIN TICK — R5'a : (1) point_dans_dom_essai ⊢CLOS x∈dom_essai(G,e,x)
(reflexivite+singleton_membre arriere+S2/S3+_instance_reunion arriere) ;
(2) coincidence_essais_rec {bo, essai p en y, essai q en y', a∈dom p… reformulé
a∈dom_essai(y), a∈dom_essai(y'), y∈E?…} ⊢ p(a)=q(a) — assembler descente ×2 +
R2' + valeur ×2. PUIS R5'b la famille S8 (patron axiome_Dfam_real/theorie_
Dfam_real de c60_realisation À LIRE avant), P3-domaine, P4-équation, ⋃D
essai-sur-seg, R3' → hérédité de couvert_essai_rec ; R6' couverture totale
(couverture_transfinie) ; R7' capstone ∃!f.

## 2026-08-22 12h35 — 🏆🏆 R5'-FINAL + R6' CLOS : LA COUVERTURE TOTALE
heredite_rec + couverture_totale_rec {bo, regle_dans_V} ⊢ (∀x∈E)(∃p ambiant)
est_essai_rec(p,x) — 29 tests rec_veritable verts, TOUT premier-coup sauf
U4 (leçon 13). Le chantier vraie-récursion aura pris ~20 ticks : R1' prédicat,
R2' unicité (6 ticks), R3' extension (3), R4' descente (2), R5' famille/
réunion (5), hérédité+couverture (2). Techniques nouvelles consignées :
garde-domaine C59, descente bilatérale sans wlog, terme-porteur-du-graphe,
α-pont ytf/yaa entre l'HR C59 et l'antécédent des U-lemmes, règle bornée
regle_dans_V instanciée au terme ⋃D.
RESTE R7' (capstone ∃!f global) : famille GLOBALE Dglob:={p∈𝔓(E×V)|∃y∈E
essai_rec(p,y)} (S8 analogue à Dfam_rec avec E au lieu de seg x — écrire
famille_globale_rec), f:=⋃Dglob ; dom f=E (⊆ : dom p=dom_essai(y)⊂E
[dom_essai_inclus_E {y∈E}] ; ⊇ : couverture_totale_rec fournit l'essai de
chaque x, x∈dom_essai(x) [point_dans]) ; compat globale (coincidence_essais_rec
— a∈E direct cette fois) ; équation de f (analogue U4 : f(z)=paa(z)=
vh(paa|seg z)=vh(f|seg z), la restriction-coïncidence avec seg z⊂dom f=E par
seg⊂E [axiome-segment]) ; UNICITÉ de f (analogue R2'-sur-E : deux solutions
globales coïncident par C59 sur P(z):=f(z)=g(z) SANS garde — les doms sont E) ;
puis (∃!f) formulé. ~3-4 ticks. PUIS R8' ℕ-itération → K6-K7 → D1 → L1 → H1
→ H2 → a²=a 🏆 CIBLE 2.

## 2026-08-22 13h00 — 🏆🏆🏆 R7' CLOS : LE CRITÈRE C60 VÉRITABLE (chantier R' TERMINÉ)
existence_solution {bo, regle_dans_V} ⊢ (∃g)(sol(g)) + unicite_globale
{bo, sol g, sol h, graphes} ⊢ g=h — LE critère C60 de Bourbaki avec la vraie
équation f(x)=T(f|seg x), certifié noyau, 37 tests verts. LE CHANTIER R'
COMPLET EN UNE JOURNÉE (~25 ticks) : R1' prédicat → R2' unicité locale →
R3' prolongement → R4' descente/composition → R5' famille/recollement →
R6' couverture totale → R7' capstone global (famille Dglob, dom f=E,
équation partout, unicité C59 sans garde, ∃ par S5-témoin-f).
L'ANCIEN point dur (« recollement/collectivisation des essais — REPORTÉ »
de C60-déposé) est LEVÉ : la sélection S8 sur 𝔓(E×V) + la coïncidence par
unicité remplacent les résidus honnêtes. Écart avec le livre : notre V est
DONNÉ avec la règle bornée (∀p)(vh(p)∈V) — c'est la donnée de Bourbaki
(« T à valeurs dans V », E III.18) rendue explicite en hypothèse.
PROCHAIN — R8' L'ITÉRATION SUR ℕ : spécialiser le critère à (ℕ, bo_graphe_NN
[vérifier son nom/état exact : grep bo_graphe_NN\|bien_ordonne.*NN]) avec la
règle d'itération T(p) := « S(p(dernier)) si p≠∅ sinon e0 » — τ-évaluation
patron t_fac_en_non_vide (garde-disjonction) OU la forme Bourbaki §III.6.1
(l'itération = C60 appliqué : LIRE V7 Texte.tex §III.6.1 + iii_6 code
existant c62 pour la CIBLE exacte f(0)=e0 ∧ f(succ n)=S(f(n))). Le C62
déposé (tabulation) a déjà une cible-itération — la NÔTRE la remplace avec
la vraie équation. PUIS K6 (injectivité de l'itérée de succ), K7 (D:=im f,
Eq(ℕ,D)), D1-Dedekind, L1 {Inf(Card E)}⊢∃D⊂E Eq(D,ℕ), H1, H2, a²=a 🏆.

## 2026-08-22 13h05 — R8' RECONNAISSANCE : l'itération ℕ a un TERRAIN DÉJÀ RICHE
Vérifié en code : bo_graphe_NN ⊢CLOS est_bien_ordonne(≤_G, ℕ) (iii_6_1) ;
segment_zero_NN_est_vide ⊢CLOS seg(≤,ℕ,0)=∅ ; restriction_vide_est_vide(F)
(factorielle_zero l.108 : F|∅=∅) ; h2_seg_succ_intervalle (donnees_ordre_NN) ;
h1_succ_dans_NN. La CIBLE C63 existe (c62_recursion l.210) MAIS sur la
TABULATION, et sa regle_iteration(S,a) = τ_y((u=∅∧y=a)∨(u≠∅∧y=S(u(M(Du)))))
a un FALLBACK LOUCHE : M=sup_borne ABSENT d'abrege → M:=dom(u) (terme bien
formé mais sémantiquement faux — l'équation au succ vaudrait S(u(dom u))).
DÉCOUVERTE : le chantier factorielle (iii_5_8) a DÉJÀ construit
factorielle_fonction_existe (3 hyps) et factorielle_equation_restriction
(4 hyps, LA FORME DU LIVRE f(n)=T_fac(f|seg n)) via C60-déposé+gluing
déverrouillé, avec les τ-évaluations en 0 (factorielle_zero) et succ
(factorielle_succ, t_fac_en_non_vide). DEUX ROUTES pour R8' :
(A) NOTRE capstone C60-vrai + regle_iteration RÉPARÉE : définir le max d'un
segment ℕ par un vrai terme (τ du plus grand élément : plus_grand_element
existe-t-il en abrege ? grep au prochain tick) puis DEUX τ-évaluations
(patrons factorielle_zero/succ) → f(0)=a ∧ f(succ n)=S(f(n)) DÉRIVÉES de
l'équation-restriction de est_solution_rec — PROPRE, réutilise R7'.
(B) recopier le montage factorielle en généralisant T_fac → T_{S,a} —
plus long, doublonne. DÉCISION : route (A), en volant les τ-patrons de
factorielle_zero/succ (lire T_fac exact d'abord : comment il récupère la
« dernière valeur » sans sup ? — si T_fac contourne le max par la forme
u((n-1)-du-POINT)… non, T ne voit pas le point : LIRE factorielle_succ
au prochain tick AVANT d'écrire).

## 2026-08-22 13h10 — R8' DESIGN FINALISÉ : tout l'outillage existe
regle_factorielle (factorielle_existence l.126) montre LA solution au max :
prev = u(terme_plus_grand(inf_egal_card, dom u, "m", "x")) — le τ-terme du
plus grand élément (§III.1.7, E III.46 note 2), liants m/x HORS des liants
cardinaux (piège du 27 juil. payé) ; max_intervalle_vaut_n_entier
(ensembles_max_intervalle_iii5) évalue M([0,n-1])=n-1. Et t_fac_en_non_vide
(factorielle_succ l.56) est GÉNÉRIQUE : (T, u, thm_nonvide) → Γ⊢T(u)=Sval
pour TOUTE règle de la forme τ_y((u=∅∧y=a)∨(u≠∅∧y=Sval)).
PLAN R8' (3-4 ticks) — rec_veritable/couverture_rec/capstone/ est PLEIN ?
(6 modules ✓ marge) — nouveau ensembles_iteration_N.py :
(1) regle_iteration_vraie(S, a) := τ_y((u=∅∧y=a)∨(u≠∅∧y=S(u(M(Du)))))
    avec M = terme_plus_grand(inf_egal_card, ·, "m", "x") — copie de
    regle_factorielle en remplaçant n·prev par S(prev) ;
(2) iteration_N_vrai := existence_solution(T_{S,a}, G_ordre_NN(),
    ensemble_NN(), V) + coupure bo par bo_graphe_NN → {regle_dans_V(T)}
    ⊢ (∃f)(sol(f)) — UNE hypothèse honnête ;
(3) éval-0 : sol(f) donne f(0)=T(f|seg 0) ; segment_zero_NN_est_vide +
    Leibniz + restriction_vide_est_vide (factorielle_zero) → T(∅) ;
    t-en-vide (patron factorielle_zero, adapter à S-générique) → =a ;
(4) éval-succ : (n, f(n))∈f|seg(succ n) (n<succ n → n∈seg succ n) → ≠∅ ;
    t_fac_en_non_vide GÉNÉRIQUE → T(…)=S(valeur(f|seg succ n, M(D…))) ;
    D(f|seg succ n)=seg succ n (restriction_dom_sous_inclusion) ;
    M(seg succ n)=n (max_intervalle_vaut_n_entier + h2_seg_succ_intervalle
    — VÉRIFIER les formes exactes au moment d'écrire) ; valeur-restriction
    → =S(f(n)) ; CIBLE C63-VRAIE : (∃f)(f(0)=a ∧ (∀n∈ℕ)(f(succ n)=S(f(n))))
    + unicité (déjà unicite_globale) — @livre Ch.III §6.2 Crit.C63
    E III.46 L.21-24 PDF p.149.

## 2026-08-22 15h42 — ÉVAL-SUCC : plan précis aux VRAIS noms (tout existe)
Briques vérifiées : h4_n_dans_seg ⊢CLOS (∀n)(Fini n ⇒ n∈seg(ℕ,succ n))
(donnees_ordre_NN l.165) ; h2_seg_succ_intervalle ⊢CLOS (∀n)(Fini n ⇒
seg(ℕ,succ n)=[0,n]) (l.114 ; version {n∈ℕ} : segment_succ_est_intervalle,
pont_segment_iii5 l.163 ; termes segment_succ_NN(k)/intervalle_zero(n)) ;
max_intervalle_vaut_n_entier {est_entier n} ⊢ M([0,n])=n (max_intervalle_iii5
l.262 — vérifier que son M est le même terme_plus_grand(inf_egal_card,·,
"m","x") que ma règle) ; h1_succ_dans_NN (succ n∈ℕ sous Fini) ; les gardes
Fini se dérivent de n∈ℕ par appartenance_NN avant. NON-VIDE : pas de lemme
membre⇒non-vide générique trouvé → dériver inline (~8 l.) : assume u=∅,
S6 réécrit (n,g(n))∈u → ∈∅, AXIOME_VIDE instancié réfute, patron
ex-falso-∨+S1 → ¬(u=∅).
PREUVE valeur_succ_iteration {sol(g), n∈ℕ} ⊢ g(succ n)=S(g(n)) :
Fini n [appartenance_NN] → succ n∈ℕ [h1] → ∈dom g [Leibniz] → éq instanciée
→ g(succ n)=T(u), u:=g|seg(succ n) ; n∈seg(succ n) [h4+Fini] ; (n,g(n))∈g
[valeur_dans_graphe coupures] → ∈u [_couple_restriction arriere] → u≠∅
[inline] ; t_fac_en_non_vide(T,u,nonvide) → T(u)=S(valeur(u, M(dom u))) ;
dom u=seg succ n [restriction_dom_sous_inclusion {seg⊂ℕ=dom g :
seg_inclus_E+Leibniz}] ; M(dom u)=M(seg succ n)=M([0,n])=n [congruences sur
le trou DANS S(valeur(u,·)) + h2/segment_succ_est_intervalle +
max_intervalle_vaut_n_entier{est_entier n : pont Fini→est_entier à vérifier}] ;
valeur(u,n)=g(n) [restriction_valeur coupures] ; réécritures congruence_terme
trou wits dans S(valeur(u, ·)) puis S(·) → chaîne → g(succ n)=S(g(n)).
