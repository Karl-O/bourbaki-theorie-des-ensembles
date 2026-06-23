"""§III.5 — CALCUL SUR LES ENTIERS : PROPOSITIONS atteignables (salvage gradué).

Ce module SALVAGE, de manière GRADUÉE et INCONDITIONNELLE quand c'est possible, les
énoncés de E.III.5 (« Calcul sur les entiers ») qui se déduisent DIRECTEMENT des
résultats DÉJÀ prouvés du projet :

  • ORDRE TOTAL des cardinaux (comparabilité, transitivité, antisymétrie, trichotomie
    — cf. ensembles_finis_props, NON dupliqués ici) ;
  • ARITHMÉTIQUE CARDINALE BINAIRE (somme a+b := Card(A⊔B), produit a·b := Card(A×B)
    — bien-définie, commutative, associative, distributive — DÉJÀ prouvée) ;
  • MONOTONIE de la somme disjointe pour ≤ : inf_egal_somme_invariant
        (A≤B et C≤D) ⇒ (A⊔C ≤ B⊔D)   [ensembles_somme_monotone] ;
  • BORNES : a ≤ a+b, b ≤ a+b, a ≤ a·b (b≠0)   [ensembles_cardinaux_bornes_somme] ;
  • Proposition 1 §III.3 (sens direct, version terme) Eq(U,V) ⇒ Card U = Card V.

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉS DE BOURBAKI VISÉS (E.III.5) :

  Prop. 1 (§5.1) : Σ_{ι∈I} a_ι et ∏_{ι∈I} a_ι d'une famille FINIE d'entiers sont des
      entiers.  ⚠ exige la RÉCURRENCE C61 (sur Card I) → REPORTÉ ; toutefois les CAS
      BINAIRES « a+b entier » / « a·b entier » se ramènent à fini_downward via les
      bornes — fournis sous report explicite (jamais postulés).
  Prop. 2 (§5.2) : a < b ⇔ (∃c>0)(b = a+c).  Le sens (⇐) « b = a+c ⇒ a ≤ b » est
      INCONDITIONNEL (substitution dans a ≤ a+c) ; le sens (⇒) exige la différence
      (Cor. 4 / récurrence) → REPORTÉ.
  Prop. 3 (§5.2) : MONOTONIE STRICTE de Σ et ∏ pour des familles finies.  Le cas
      BINAIRE de la monotonie LARGE — (a≤b et c≤d) ⇒ a+c ≤ b+d — est INCONDITIONNEL
      (via inf_egal_somme_invariant + le pont ensembles→cardinaux).  La version
      STRICTE et le cas FAMILLE exigent la récurrence → REPORTÉS/conditionnés.
  Cor. 4 (§5.2) — différence : a ≤ b ⇒ (∃! c)(b = a+c).  L'UNICITÉ et l'EXISTENCE de
      la différence exigent le bon ordre de ℕ → REPORTÉES (énoncés-cibles fournis).

────────────────────────────────────────────────────────────────────────────────
SALVAGE — état des paliers (cf. __all__) :

  ✅ INCONDITIONNEL (rien postulé, theorie_ensembles()=22), sur les TERMES de la
     somme/du produit cardinal BINAIRE (a+b, a·b) :
       • somme_binaire_monotone(a,b,c,d)        — (a≤b et c≤d) ⇒ a+c ≤ b+d  [Prop. 3] ;
       • somme_binaire_monotone_gauche(a,b,c)   — (a≤b) ⇒ a+c ≤ b+c ;
       • somme_binaire_monotone_droite(a,b,c)   — (a≤b) ⇒ c+a ≤ c+b ;
       • inf_egal_somme_gauche_binaire(a,b)     — a ≤ a+b   [borne, Prop. 2 ⇐ socle] ;
       • inf_egal_somme_droite_binaire(a,b)     — b ≤ a+b ;
       • prop2_somme_implique_inf_egal(a,b,c)   — (b = a+c) ⇒ a ≤ b   [Prop. 2, ⇐] ;
       • inf_egal_produit_binaire(a,b)          — (b ≠ ∅) ⇒ a ≤ a·b  [borne produit].

  ⚠️ REPORTÉS — ÉNONCÉS-CIBLES (formules retournées, JAMAIS prouvées ni postulées ;
     dépendent de la RÉCURRENCE C61 / du bon ordre de ℕ / de la différence) :
       • somme_binaire_entier_cible(a,b)        — (Fini a et Fini b) ⇒ Fini(a+b)  [Prop. 1
         cas binaire ; récurrence sur b] ; la version FAMILLE reste reportée (réc. Card I) ;
       • produit_binaire_entier_cible(a,b)      — (Fini a et Fini b) ⇒ Fini(a·b) ;
       • prop3_somme_stricte_cible(a,b,c,d)     — monotonie STRICTE de + ;
       • cor4_difference_existe_unique_cible(a,b) — existence de c tq b = a+c (diff. b − a ;
         existence ET unicité reportées, formule-cible = existence).

INVARIANT : aucun N.axiome ajouté à theorie_ensembles() (= 22).  Les seuls givens sont
des HYPOTHÈSES explicites (a≤b, b=a+c, b≠∅, fini_downward), déchargées par
loi_deduction.  Anti-tautologie/anti-affaibli strict : chaque énoncé inconditionnel a
un CONTENU non trivial (monotonie, borne) certifié par le noyau.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, impl, existe)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_son_cardinal, inf_egal_reflexif,
)
from bourbaki.cardinaux.ensembles_cardinaux_ordre import (
    equipotence_implique_inf_egal,
)
from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_somme_monotone import (
    inf_egal_somme_invariant,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  PONT  (X ≤ Y)  ⇒  (Card X ≤ Card Y)   [INCONDITIONNEL, public theorems seuls]
#
#  Card X ≤ X  (Eq(X,Card X) symétrique ⇒ Eq(Card X,X) ⇒ Card X ≤ X) ;
#  X ≤ Y (hyp) ; Y ≤ Card Y (Eq(Y,Card Y) ⇒ Y ≤ Card Y).
#  Transitivité ×2 : Card X ≤ X ≤ Y ≤ Card Y.
# ════════════════════════════════════════════════════════════════════════════
def _eq_son_cardinal_t(tX):
    """⊢ Eq(X, Card X) pour un TERME X (généralise equipotent_son_cardinal aux termes)."""
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), tX)


def _trans_le(tA, tB, tC):
    """⊢ (A ≤ B et B ≤ C) ⇒ (A ≤ C)  pour des TERMES (transitivité de ≤, version terme).

    inf_egal_transitive(F,G,X,Y,Z) généralisée en X,Y,Z puis instanciée aux termes."""
    from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
    trans = inf_egal_transitive("F", "G", "X", "Y", "Z")
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z", trans)))
    return instancie(instancie(instancie(gen, tA), tB), tC)


def le_ens_implique_le_card(tX, tY):
    """⊢ ( X ≤ Y ) ⇒ ( Card X ≤ Card Y ).   (le ≤ entre ENSEMBLES passe aux CARDINAUX.)

    Card X ≤ X (Eq(X,Card X) symétrique ⇒ Card X ≤ X) ; X ≤ Y (hyp) ; Y ≤ Card Y.
    Transitivité ×2 : Card X ≤ X ≤ Y ≤ Card Y.  Tout INCONDITIONNEL (réflexivité/
    transitivité de ≤ + Prop. 1 §III.3).  Sert de pont pour pousser la monotonie de la
    somme disjointe (sur ENSEMBLES) vers la somme cardinale binaire (sur CARDINAUX)."""
    vX, vY = _t(tX), _t(tY)
    cX, cY = cardinal(vX), cardinal(vY)
    sym_all = N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y")))                  # (∀X)(∀Y)(Eq(X,Y)⇒Eq(Y,X))
    eqle_all = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))           # (∀X)(∀Y)(Eq(X,Y)⇒X≤Y)
    # Card X ≤ X
    eq_X_cX = _eq_son_cardinal_t(vX)                             # Eq(X, Card X)
    eq_cX_X = N.modus_ponens(eq_X_cX, instancie(instancie(sym_all, vX), cX))   # Eq(Card X, X)
    le_cX_X = N.modus_ponens(eq_cX_X, instancie(instancie(eqle_all, cX), vX))  # Card X ≤ X
    # Y ≤ Card Y
    eq_Y_cY = _eq_son_cardinal_t(vY)                             # Eq(Y, Card Y)
    le_Y_cY = N.modus_ponens(eq_Y_cY, instancie(instancie(eqle_all, vY), cY))  # Y ≤ Card Y
    # sous X ≤ Y : Card X ≤ X ≤ Y ≤ Card Y
    h_le_XY = N.assume(inf_egal_card(vX, vY))                    # X ≤ Y
    le_cX_Y = N.modus_ponens(conjonction_intro(le_cX_X, h_le_XY),
                             _trans_le(cX, vX, vY))              # Card X ≤ Y
    le_cX_cY = N.modus_ponens(conjonction_intro(le_cX_Y, le_Y_cY),
                              _trans_le(cX, vY, cY))             # Card X ≤ Card Y
    return N.loi_deduction(inf_egal_card(vX, vY), le_cX_cY)      # (X≤Y) ⇒ (Card X ≤ Card Y)


# ════════════════════════════════════════════════════════════════════════════
#  (1) MONOTONIE de la SOMME cardinale binaire   (Proposition 3, cas binaire LARGE)
#
#  a + b := Card(A ⊔ B).  De (A≤B₁ et C≤D) on tire A⊔C ≤ B₁⊔D (inf_egal_somme_invariant),
#  puis Card(A⊔C) ≤ Card(B₁⊔D) (pont).  C'est EXACTEMENT a+c ≤ b+d, où le « + » est la
#  somme cardinale binaire somme_cardinale_binaire = Card(·⊔·).
# ════════════════════════════════════════════════════════════════════════════
def somme_binaire_monotone(a="a", b="b", c="c", d="d"):
    """⊢ ( a ≤ b et c ≤ d ) ⇒ ( a+c ≤ b+d ).   (MONOTONIE de + ; Prop. 3 cas binaire ; INCONDITIONNEL.)

    où a+c := somme_cardinale_binaire(a,c) = Card(a⊔c), b+d := Card(b⊔d).
    inf_egal_somme_invariant(F,G,a,c,b,d) : (a≤b et c≤d) ⇒ (a⊔c ≤ b⊔d) ;
    le_ens_implique_le_card(a⊔c, b⊔d) : (a⊔c ≤ b⊔d) ⇒ (Card(a⊔c) ≤ Card(b⊔d)).
    Composition : (a≤b et c≤d) ⇒ a+c ≤ b+d.  « La somme d'entiers croît avec chaque
    terme » (E.III.5.2, Prop. 3, version LARGE binaire) — INCONDITIONNEL, contenu non
    trivial (distinct de toute tautologie)."""
    va, vb, vc, vd = _t(a), _t(b), _t(c), _t(d)
    ac = somme_disjointe(va, vc)
    bd = somme_disjointe(vb, vd)
    ante = et(inf_egal_card(va, vb), inf_egal_card(vc, vd))
    h = N.assume(ante)
    # a⊔c ≤ b⊔d.  inf_egal_somme_invariant utilise des liants INTERNES a, b, k, t, u…
    # dans ses projections : passer var("a")/… comme paramètres-ensembles y provoquerait
    # une capture.  On construit donc l'invariant avec des PLACEHOLDERS sûrs (A0,C0,B0,D0)
    # puis on GÉNÉRALISE et INSTANCIE aux termes réels va, vc, vb, vd (renommage sûr).
    inv0 = inf_egal_somme_invariant("F", "G", "A0", "C0", "B0", "D0")
    # conclusion : (A0≤B0 et C0≤D0) ⇒ (A0⊔C0 ≤ B0⊔D0)
    inv_gen = N.generalisation("A0", N.generalisation("C0",
              N.generalisation("B0", N.generalisation("D0", inv0))))
    inv = instancie(instancie(instancie(instancie(inv_gen, va), vc), vb), vd)
    le_ens = N.modus_ponens(h, inv)                             # a⊔c ≤ b⊔d
    # Card(a⊔c) ≤ Card(b⊔d)  =  a+c ≤ b+d
    le_card = N.modus_ponens(le_ens, le_ens_implique_le_card(ac, bd))   # Card(a⊔c) ≤ Card(b⊔d)
    return N.loi_deduction(ante, le_card)                       # (a≤b et c≤d) ⇒ a+c ≤ b+d


def somme_binaire_monotone_gauche(a="a", b="b", c="c"):
    """⊢ ( a ≤ b ) ⇒ ( a+c ≤ b+c ).   (MONOTONIE de + en l'argument GAUCHE ; INCONDITIONNEL.)

    Cas particulier de somme_binaire_monotone avec d := c et c ≤ c (réflexivité de ≤,
    inf_egal_reflexif au terme c) : de a≤b on tire a+c ≤ b+c.  « Ajouter une même
    quantité préserve l'ordre » (E.III.5.2)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    h_ab = N.assume(inf_egal_card(va, vb))                      # a ≤ b
    refl_c = instancie(N.generalisation("X", inf_egal_reflexif("X")), vc)   # c ≤ c
    mono = somme_binaire_monotone(va, vb, vc, vc)               # (a≤b et c≤c) ⇒ a+c ≤ b+c
    le = N.modus_ponens(conjonction_intro(h_ab, refl_c), mono)  # a+c ≤ b+c   [sous a≤b]
    return N.loi_deduction(inf_egal_card(va, vb), le)


def somme_binaire_monotone_droite(a="a", b="b", c="c"):
    """⊢ ( a ≤ b ) ⇒ ( c+a ≤ c+b ).   (MONOTONIE de + en l'argument DROIT ; INCONDITIONNEL.)

    Cas particulier de somme_binaire_monotone avec premier argument c ≤ c (réflexivité)
    et deuxième a ≤ b : de a≤b on tire c+a ≤ c+b."""
    va, vb, vc = _t(a), _t(b), _t(c)
    h_ab = N.assume(inf_egal_card(va, vb))                      # a ≤ b
    refl_c = instancie(N.generalisation("X", inf_egal_reflexif("X")), vc)   # c ≤ c
    mono = somme_binaire_monotone(vc, vc, va, vb)               # (c≤c et a≤b) ⇒ c+a ≤ c+b
    le = N.modus_ponens(conjonction_intro(refl_c, h_ab), mono)  # c+a ≤ c+b   [sous a≤b]
    return N.loi_deduction(inf_egal_card(va, vb), le)


# ════════════════════════════════════════════════════════════════════════════
#  (2) BORNES de la SOMME cardinale binaire :  a ≤ a+b,  b ≤ a+b   (INCONDITIONNEL)
#
#  a ≤ a+b est le SOCLE du sens (⇐) de la Prop. 2 (a<b ⇔ (∃c>0)(b=a+c)).  On le prouve
#  sur le TERME a+b := Card(a⊔b) : Card a ≤ Card(a⊔b) via a ≤ a⊔b (injection gauche
#  u↦(u,0)) puis le pont.  Reste à identifier Card a = a quand a est un cardinal — on
#  reste GÉNÉRAL : la borne s'énonce « Card a ≤ a+b », et sous est_cardinal a c'est a ≤ a+b.
# ════════════════════════════════════════════════════════════════════════════
def inf_egal_somme_gauche_binaire(a="a", b="b"):
    """⊢ Card(a) ≤ ( a+b ).   (BORNE GAUCHE « a ≤ a+b » ; E.III.5.2 ; INCONDITIONNEL.)

    où a+b := somme_cardinale_binaire(a,b) = Card(a⊔b).  a ≤ a⊔b (injection gauche
    u↦(u,0), inf_egal_somme_gauche) ; le pont le_ens_implique_le_card donne
    Card a ≤ Card(a⊔b) = a+b.  Sous est_cardinal a (Card a = a) c'est « a ≤ a+b ».
    SOCLE du sens (⇐) de la Proposition 2 (b = a+c ⇒ a ≤ b)."""
    from bourbaki.cardinaux.ensembles_cardinaux_bornes_somme import inf_egal_somme_gauche
    va, vb = _t(a), _t(b)
    ab = somme_disjointe(va, vb)
    le_ens = inf_egal_somme_gauche(va, vb)                      # a ≤ a⊔b   (clos)
    return N.modus_ponens(le_ens, le_ens_implique_le_card(va, ab))   # Card a ≤ Card(a⊔b) = a+b


def inf_egal_somme_droite_binaire(a="a", b="b"):
    """⊢ Card(b) ≤ ( a+b ).   (BORNE DROITE « b ≤ a+b » ; E.III.5.2 ; INCONDITIONNEL.)

    b ≤ a⊔b (injection droite v↦(v,1), inf_egal_somme_droite) ; le pont donne
    Card b ≤ Card(a⊔b) = a+b.  Sous est_cardinal b c'est « b ≤ a+b »."""
    from bourbaki.cardinaux.ensembles_cardinaux_bornes_somme import inf_egal_somme_droite
    va, vb = _t(a), _t(b)
    ab = somme_disjointe(va, vb)
    le_ens = inf_egal_somme_droite(va, vb)                      # b ≤ a⊔b   (clos)
    return N.modus_ponens(le_ens, le_ens_implique_le_card(vb, ab))   # Card b ≤ Card(a⊔b) = a+b


def prop2_somme_implique_inf_egal(a="a", b="b", c="c"):
    """⊢ ( est_cardinal(a) et b = a+c ) ⇒ ( a ≤ b ).   (Proposition 2, sens ⇐ ; INCONDITIONNEL.)

    PROPOSITION 2 §III.5.2, sens (⇐) : « s'il existe c tel que b = a+c, alors a ≤ b ».
    a ≤ a+c (inf_egal_somme_gauche_binaire, sous Card a = a) ; b = a+c (hyp) donne, par
    réécriture S6 du majorant a+c ↦ b, a ≤ b.  La partie « c > 0 ⇒ a < b » (stricte) et
    la réciproque (⇒) exigent la différence (Cor. 4 / récurrence) → REPORTÉES.
    Hypothèse est_cardinal a : pour identifier Card a = a (sinon on aurait Card a ≤ b)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
    va, vb, vc = _t(a), _t(b), _t(c)
    ac = somme_cardinale_binaire(va, vc)                        # a+c = Card(a⊔c)
    h_ca = N.assume(est_cardinal(va))                           # est_cardinal a
    h_eq = N.assume(egal(vb, ac))                               # b = a+c
    # Card a ≤ a+c
    le_cardA_ac = inf_egal_somme_gauche_binaire(va, vc)         # Card a ≤ a+c
    # Card a = a  (sous est_cardinal a) → a ≤ a+c
    cardA_eq_a = N.modus_ponens(h_ca, cardinal_de_cardinal(va)) # Card a = a
    a_le_ac = N.modus_ponens(le_cardA_ac, equivalence_avant_S6_card(va, ac, cardA_eq_a))
    # a ≤ a+c et b = a+c → a ≤ b  (réécrire a+c ↦ b via b = a+c, i.e. S6 sur le majorant)
    # b = a+c  ⇒ ( a ≤ a+c ⇔ a ≤ b )   (S6, sujet du 2ᵉ argument)
    leib = N.s6(ac, vb, "w", inf_egal_card(va, var("w")))       # (a+c = b) ⇒ (a≤a+c ⇔ a≤b)
    eq_ac_b = N.modus_ponens(h_eq, symetrie(vb, ac))           # a+c = b
    equiv = N.modus_ponens(eq_ac_b, leib)                      # (a≤a+c) ⇔ (a≤b)
    a_le_b = N.modus_ponens(a_le_ac, _eqv_avant(equiv))        # a ≤ b
    inner = N.loi_deduction(egal(vb, ac), a_le_b)              # (b=a+c) ⇒ a≤b   [card a]
    return N.loi_deduction(est_cardinal(va), inner)            # (est_card a) ⇒ ((b=a+c) ⇒ a≤b)


def _eqv_avant(equiv_thm):
    """⊢ A ⇔ B ⟹ ⊢ A ⇒ B   (sens AVANT d'une équivalence, raccourci local)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    return equivalence_avant(equiv_thm)


def equivalence_avant_S6_card(tA, tMaj, eq_thm):
    """{Card A = A} ⊢ ( Card A ≤ M ) ⇒ ( A ≤ M ).   (réécriture du sujet Card A ↦ A.)

    De Card A = A (preuve eq_thm), S6 donne (Card A ≤ M ⇔ A ≤ M) ; on renvoie le sens
    AVANT comme IMPLICATION close (eq_thm est déjà une preuve, donc l'implication est
    sans hypothèse résiduelle au-delà de celles de eq_thm)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    cA = cardinal(_t(tA))
    leib = N.s6(cA, _t(tA), "w", inf_egal_card(var("w"), _t(tMaj)))   # (Card A = A) ⇒ (CardA≤M ⇔ A≤M)
    equiv = N.modus_ponens(eq_thm, leib)                        # (Card A ≤ M) ⇔ (A ≤ M)
    return equivalence_avant(equiv)                             # (Card A ≤ M) ⇒ (A ≤ M)


# ════════════════════════════════════════════════════════════════════════════
#  (3) BORNE du PRODUIT cardinal binaire :  b ≠ ∅ ⇒ a ≤ a·b   (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def inf_egal_produit_binaire(a="a", b="b"):
    """⊢ ( b ≠ ∅ ) ⇒ ( Card(a) ≤ a·b ).   (BORNE PRODUIT « a ≤ a·b si b≠0 » ; INCONDITIONNEL.)

    où a·b := produit_cardinal_binaire(a,b) = Card(a×b).  Ré-exposition directe de
    cardinal_inf_egal_produit (ensembles_cardinaux_bornes_somme) : pour b ≠ ∅, x↦(x,e)
    (e ∈ b témoin) injecte a dans a×b, donc Card a ≤ Card(a×b) = a·b.  Sous est_cardinal a
    (Card a = a) c'est « a ≤ a·b » (E.III.5.2).  Le cas b = ∅ donne a·b = 0 (0^a-type)."""
    va, vb = _t(a), _t(b)
    # cardinal_inf_egal_produit(A,B) : ¬(B=∅) ⇒ (Card A ≤ Card(A)×B) ; on l'instancie en
    # termes a, b — mais sa conclusion vise Card(A)×B, pas a×b.  On reconstruit donc
    # proprement via la version ENSEMBLE inf_egal_produit + le pont.
    from bourbaki.cardinaux.ensembles_cardinaux_bornes_somme import inf_egal_produit
    ab = E.produit(va, vb)
    h_ne = N.assume(non(egal(vb, E.VIDE)))                      # b ≠ ∅
    le_ens = N.modus_ponens(h_ne, inf_egal_produit(va, vb))     # a ≤ a×b   [sous b≠∅]
    le_card = N.modus_ponens(le_ens, le_ens_implique_le_card(va, ab))   # Card a ≤ Card(a×b) = a·b
    return N.loi_deduction(non(egal(vb, E.VIDE)), le_card)      # (b≠∅) ⇒ Card a ≤ a·b


# ════════════════════════════════════════════════════════════════════════════
#  (4) PROPOSITION 1 §III.5.1 (cas binaire) — CONDITIONNEL sur la récurrence C61
#
#  « La somme/le produit d'une famille FINIE d'entiers est un entier. »  La version
#  FAMILLE exige une récurrence sur Card I (REPORTÉE).  Le cas BINAIRE « a, b entiers ⇒
#  a+b entier » se ramène à fini_downward : a+b = Card(a⊔b) ; il faudrait Fini(a+b),
#  ce qui suit de Fini(a)+Fini(b) PAR récurrence (C61) → on le pose en HYPOTHÈSE.
# ════════════════════════════════════════════════════════════════════════════
def somme_binaire_entier_cible(a="a", b="b"):
    """ÉNONCÉ (formule-cible, NON théorème) du cas BINAIRE de la Proposition 1 §III.5.1 :
        ( Fini a et Fini b ) ⇒ Fini( a+b ).

    « La somme de DEUX entiers est un entier. »  ⚠ REPORTÉ : la finitude de a+b à partir
    de celle de a et b passe par la RÉCURRENCE C61 (récurrence sur b : Fini(a+0)=Fini a ;
    Fini(a+b) ⇒ Fini(a+(b+1)) via Prop. 1 §III.4.1 « Fini 𝔠 ⇔ Fini 𝔠+1 »).  Énoncé
    fourni comme cible — JAMAIS postulé."""
    va, vb = _t(a), _t(b)
    return impl(et(est_fini(va), est_fini(vb)), est_fini(somme_cardinale_binaire(va, vb)))


def produit_binaire_entier_cible(a="a", b="b"):
    """ÉNONCÉ (formule-cible, NON théorème) du cas BINAIRE de la Proposition 1 §III.5.1 :
        ( Fini a et Fini b ) ⇒ Fini( a·b ).

    « Le produit de DEUX entiers est un entier. »  ⚠ REPORTÉ (récurrence C61 sur b :
    a·0 = 0 fini ; a·(b+1) = a·b + a fini par le cas somme).  Énoncé-cible, jamais postulé."""
    va, vb = _t(a), _t(b)
    return impl(et(est_fini(va), est_fini(vb)), est_fini(produit_cardinal_binaire(va, vb)))


# ════════════════════════════════════════════════════════════════════════════
#  (5) ÉNONCÉS REPORTÉS — formules-cibles (Prop. 3 stricte, Cor. 4 différence)
# ════════════════════════════════════════════════════════════════════════════
def prop3_somme_stricte_cible(a="a", b="b", c="c", d="d"):
    """ÉNONCÉ (formule-cible) de la Proposition 3 §III.5.2 (cas binaire STRICT) :
        ( a ≤ b et c < d ) ⇒ ( a+c < b+d ).

    « Si l'un des termes croît STRICTEMENT (et les autres au moins largement), la somme
    croît strictement. »  ⚠ REPORTÉ : la stricte monotonie exige le lemme
    cardinal_pas_entre (rien entre c et c+1) et/ou la différence → REPORTÉE.  Énoncé-cible."""
    va, vb, vc, vd = _t(a), _t(b), _t(c), _t(d)
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    ac = somme_cardinale_binaire(va, vc)
    bd = somme_cardinale_binaire(vb, vd)
    return impl(et(inf_egal_card(va, vb), inf_strict_card(vc, vd)), inf_strict_card(ac, bd))


def cor4_difference_existe_unique_cible(a="a", b="b", c="c"):
    """ÉNONCÉ (formule-cible) du Corollaire 4 §III.5.2 (DIFFÉRENCE) :
        ( a ≤ b ) ⇒ ( ∃c )( est_cardinal c et b = a+c ).

    « Si a ≤ b, il existe un entier c tel que b = a+c (la différence b − a). »
    ⚠ REPORTÉ : l'EXISTENCE de la différence (et son UNICITÉ) exige le bon ordre de ℕ
    et l'arithmétique cardinale infinie → REPORTÉE.  Énoncé-cible, jamais postulé.
    (Le SENS (⇐) « b = a+c ⇒ a ≤ b » est, lui, prouvé par prop2_somme_implique_inf_egal.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return impl(inf_egal_card(va, vb),
                existe("c", et(est_cardinal(var("c")), egal(vb, somme_cardinale_binaire(va, var("c"))))))


__all__ = [
    # PONT (infra réutilisable)
    "le_ens_implique_le_card",
    # ✅ INCONDITIONNELS — monotonie de la somme cardinale binaire (Prop. 3 large)
    "somme_binaire_monotone",
    "somme_binaire_monotone_gauche",
    "somme_binaire_monotone_droite",
    # ✅ INCONDITIONNELS — bornes (socle Prop. 2 ⇐)
    "inf_egal_somme_gauche_binaire",
    "inf_egal_somme_droite_binaire",
    "prop2_somme_implique_inf_egal",
    "inf_egal_produit_binaire",
    # ⚠️ ÉNONCÉS-CIBLES REPORTÉS / CONDITIONNELS (jamais postulés comme théorèmes)
    "somme_binaire_entier_cible",
    "produit_binaire_entier_cible",
    "prop3_somme_stricte_cible",
    "cor4_difference_existe_unique_cible",
]
