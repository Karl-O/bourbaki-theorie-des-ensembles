

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
