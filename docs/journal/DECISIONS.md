

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
