

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
