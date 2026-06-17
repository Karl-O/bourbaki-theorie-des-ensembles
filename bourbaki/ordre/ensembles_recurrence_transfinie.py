"""§III.2 — RÉCURRENCE TRANSFINIE (Critère C59) : PREUVE par PLUS-PETIT-CONTRE-EXEMPLE.

OBJECTIF : prouver, comme MÉTATHÉORÈME paramétré par un prédicat P (fonction Python
Terme→Formule), le PRINCIPE DE RÉCURRENCE TRANSFINIE (Critère C59, E.III.2) sur un
ensemble BIEN ORDONNÉ (E, R) :

    recurrence_transfinie(P, E, R) :=
        est_bien_ordonne(R,E)  ⇒
          (  (∀x)( x∈E ⇒ [ (∀y)( y∈seg(R,E,x) ⇒ P[y] )  ⇒  P[x] ] )
             ⇒
             (∀x)( x∈E ⇒ P[x] )  )

« Pour démontrer qu'une propriété P[x] est vraie pour tout x d'un ensemble bien
ordonné E, il suffit de montrer que, pour tout x∈E, si P[y] est vraie pour tout y
strictement plus petit que x [c.-à-d. y∈seg(R,E,x) = ]←,x[], alors P[x] est vraie. »

────────────────────────────────────────────────────────────────────────────────
PREUVE (plus-petit-contre-exemple — c'est la justification même de C59 par Bourbaki).

  Hypothèses :  W := est_bien_ordonne(R,E)  (le bon ordre)
                Hyp := (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ P[y]) ⇒ P[x] ) )  (hér. transf.)
  Cible :  (∀x)( x∈E ⇒ P[x] ).  On fixe x0, on assume x0∈E, et on prouve P[x0] par
  l'absurde : on assume ¬P[x0] et on dérive une contradiction.

  1. SÉPARATION S8 :  A := { x ∈ E | ¬P[x] }   (axiome DÉDIÉ ⇒ theorie reste 22).
     A ⊂ E (projection du corps : x∈A ⇒ x∈E).  x0 ∈ A (x0∈E, ¬P[x0]), donc A ≠ ∅.

  2. BON ORDRE :  W projette la clause « toute partie non vide a un plus petit
     élément », instanciée à X:=A.  Comme A⊂E et A≠∅, il existe un ≤-MIN m :
         m ∈ A   et   (∀w)( w∈A ⇒ m ≤ w ).
     m∈A : m∈E et ¬P[m].

  3. P[y] pour tout y < m :  soit y∈seg(R,E,m) = { y∈E | y≤m et y≠m }.  Alors y∈E,
     y≤m, y≠m.  Si ¬P[y] alors y∈A, donc m≤y (m est ≤-min) ; avec y≤m, l'ANTI-
     SYMÉTRIE de R (issue de W : est_relation_ordre_dans ⇒ ordre antisymétrique)
     donne y=m, contredisant y≠m.  Donc ¬¬P[y], d'où P[y] (DNE).  Universellement :
         (∀y)( y∈seg(R,E,m) ⇒ P[y] ).

  4. PAS D'HÉRÉDITÉ :  Hyp instanciée à m (m∈E) donne
         (∀y)(y∈seg(R,E,m) ⇒ P[y])  ⇒  P[m].
     Avec l'étape 3 : P[m].  Mais m∈A ⇒ ¬P[m].  CONTRADICTION.

  5. Donc sous { x0∈E, ¬P[x0], W, Hyp } : ⊥.  D'où ¬P[x0]⇒¬¬P[x0] (consequentia
     mirabilis) ⇒ ¬¬P[x0] ⇒ P[x0] (DNE), SOUS { x0∈E, W, Hyp }.  Décharge x0∈E,
     généralise (∀x0), décharge Hyp puis W ⇒ recurrence_transfinie(P,E,R).

────────────────────────────────────────────────────────────────────────────────
STATUT — CLOS, 0 HYPOTHÈSE RÉSIDUELLE  (≠ C61 sur ℕ).

Contrairement à `principe_recurrence_preuve` (§III.4, qui traînait DEUX résidus :
predecesseur_fini_universel [Prop.2 §III.5, gap maths] et bon_ordre_min_universel
[blocage NOYAU sur le τ-binder ZERO de [0,n0]]), la récurrence transfinie est
PLEINEMENT close :
  • le ≤-min vient DIRECTEMENT de l'hypothèse `est_bien_ordonne(R,E)` (W EST le bon
    ordre) — AUCUN report `cardinaux_bien_ordonnes` n'est nécessaire ;
  • E = var('E') ne contient AUCUN τ-binder interne (≠ le ZERO de [0,n0]) ⇒ la
    séparation A⊂E se prouve au binder canonique 'z' SANS renommage '@0' ⇒ AUCUN
    blocage noyau (le verrou du résidu #2 de C61 n'existe pas ici) ;
  • aucun « prédécesseur » : on raisonne sur le SEGMENT seg(R,E,m), pas sur m−1.

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  La séparation S8 de A est un
axiome DÉDIÉ (théorie isolée, motif `_theorie_A` de C61) ; l'axiome de seg(R,E,x)
est `axiome_segment_extremite` dans sa THÉORIE DÉDIÉE (theorie_segment_extremite).
RIEN n'est postulé ; tout est DÉRIVÉ.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, contraposition, equivalence_avant, equivalence_arriere, dne, dni,
    antecedent_consequent,
)
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ────────────────────────────────────────────────────────────────────────────
#  helpers logiques (motif identique à ensembles_principe_recurrence_preuve)
# ────────────────────────────────────────────────────────────────────────────
def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible  (ex falso quodlibet)."""
    a = thm_a.conclusion
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))   # ¬A ∨ cible = (A ⇒ cible)
    return N.modus_ponens(thm_a, imp)                    # cible


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) = (¬P∨¬P) → ¬P par S1.)"""
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)   # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))            # (¬P∨¬P)⇒¬P


def _graphe_R(G):
    """Relation ≤ portée par le graphe G : a≤b := (a,b)∈G  (convention par défaut)."""
    vG = _t(G)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vG)


# ════════════════════════════════════════════════════════════════════════════
#  SÉPARATION S8 DÉDIÉE — A := { x ∈ E | ¬P[x] }.
#  Terme opaque + axiome DÉFINITIONNEL (motif _A de C61) — theorie reste 22.
# ════════════════════════════════════════════════════════════════════════════
def _A(P, e):
    """A := { x ∈ E | ¬P[x] }  (terme opaque, paramétré par E)."""
    return app("A_contre_ex_transfinie", _t(e))


def _A_corps(P, e, x):
    """Corps caractérisant x ∈ A :  x∈E  et  ¬P[x]."""
    vx = _t(x)
    return et(appartient(vx, _t(e)), non(P(vx)))


def _axiome_A(P, e="Eax", x="xAax"):
    """⊢-schéma  (∀E)(∀x)( x ∈ A(E) ⇔ (x∈E et ¬P[x]) )   (séparation S8 dans E).

    ⚠️ E et x sont des NOMS de liants (str) — JAMAIS var() sur un Terme."""
    en = e if isinstance(e, str) else e.nom
    xn = x if isinstance(x, str) else x.nom
    ve, vx = var(en), var(xn)
    return pourtout(en, pourtout(xn,
        equiv(appartient(vx, _A(P, ve)), _A_corps(P, ve, vx))))


def _theorie_A(P, e="Eax", x="xAax"):
    """Théorie DÉDIÉE ne contenant que l'axiome de A (motif theorie_segment_extremite /
    _theorie_A de C61).  N'altère PAS theorie_ensembles() (= 22)."""
    return N.Theorie("A-contre-exemple-recurrence-transfinie", [_axiome_A(P, e, x)])


def _A_membre(P, e, x, ebind="Eax", xbind="xAax"):
    """⊢ ( x ∈ A(E) ⇔ (x∈E et ¬P[x]) )   (axiome instancié aux TERMES E, x)."""
    ax = N.axiome(_theorie_A(P, ebind, xbind), _axiome_A(P, ebind, xbind))
    return instancie(instancie(ax, _t(e)), _t(x))


def _A_inclus_E(P, e, ebind="Eax", xbind="xAax", z="z"):
    """⊢ inclus(A(E), E)  = (∀z)( z∈A ⇒ z∈E )   (CLOS, 0 hyp).

    PREUVE que A ⊂ E : z∈A ⇒ (z∈E et ¬P[z]) ⇒ z∈E (projection gauche du corps).
    E = var('E') ne contient AUCUN τ-binder interne (≠ ZERO de [0,n0] dans C61), donc
    le binder 'z' de `inclus` n'est PAS renommé '@0' : la forme RAW canonique
    `inclus(A,E)` (celle qu'attend la clause de bon ordre) est produite EXACTEMENT,
    SANS pont α.  C'est ce qui rend la récurrence transfinie close, là où C61 butait."""
    ve, vz = _t(e), var(z)
    A = _A(P, ve)
    h = N.assume(appartient(vz, A))
    corps = N.modus_ponens(h, equivalence_avant(_A_membre(P, ve, vz, ebind, xbind)))
    z_in = conjonction_elim_gauche(corps)                # z ∈ E
    res = N.generalisation(z, N.loi_deduction(appartient(vz, A), z_in))  # inclus(A,E)
    assert res.conclusion == inclus(A, ve, z), "A_inclus_E ≠ inclus(A,E)"
    assert res.est_clos, "A_inclus_E non clos"
    return res


def _A_non_vide(P, e, x0_in_A):
    """⊢ ¬( A(E) = ∅ )   depuis une preuve `x0_in_A` de  x0 ∈ A(E)  (témoin non-vacuité).

    Motif `_A_non_vide` de C61 : S5 (témoin x0) ⇒ (∃z)(z∈A) ; puis sens ARRIÈRE de
    `non_vide_ssi_element(A)` : ¬(A=∅) ⇔ (∃z)(z∈A)."""
    A = _A(P, _t(e))
    ex_z = N.modus_ponens(x0_in_A, N.s5(appartient(var("z"), A), x0_in_A.conclusion.termes[0], "z"))
    res = N.modus_ponens(ex_z, equivalence_arriere(non_vide_ssi_element(A)))    # ¬(A=∅)
    assert res.conclusion == non(egal(A, E.VIDE)), "A_non_vide mal formé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  AXIOME DE SEGMENT  seg(R,E,x) = ]←,x[ = { y∈E | y≤x et y≠x }  (E.III.2.1).
#  Instance de axiome_segment_extremite dans sa THÉORIE DÉDIÉE — theorie reste 22.
# ════════════════════════════════════════════════════════════════════════════
def _seg_membre(R, e, x, y):
    """⊢ ( y ∈ seg(R,E,x) ) ⇔ ( (y∈E et y≤x) et y≠x )   (axiome instancié aux TERMES E,x,y)."""
    th = E.theorie_segment_extremite(R)
    ax = N.axiome(th, E.axiome_segment_extremite(R))     # (∀E)(∀x)(∀y)( y∈S_x ⇔ ((y∈E et y≤x) et y≠x) )
    return instancie(instancie(instancie(ax, _t(e)), _t(x)), _t(y))


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS (formules-cible) — récurrence transfinie C59.
# ════════════════════════════════════════════════════════════════════════════
def heredite_transfinie(P, R, e, x="x", y="y"):
    """(∀x)( x∈E ⇒ ( (∀y)( y∈seg(R,E,x) ⇒ P[y] )  ⇒  P[x] ) )   (HÉRÉDITÉ transfinie).

    « Pour tout x∈E, si P vaut sur tout le segment initial ]←,x[, alors P[x]. »"""
    vx, vy = var(x), var(y)
    seg_x = E.segment_extremite(R, _t(e), vx)
    devant = pourtout(y, impl(appartient(vy, seg_x), P(vy)))      # P sur seg(R,E,x)
    return pourtout(x, impl(appartient(vx, _t(e)), impl(devant, P(vx))))


def conclusion_transfinie(P, e, x="x"):
    """(∀x)( x∈E ⇒ P[x] )   (CONCLUSION : P vaut partout sur E)."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _t(e)), P(vx)))


def recurrence_transfinie(P, R, e, x="x", y="y"):
    """Énoncé du PRINCIPE DE RÉCURRENCE TRANSFINIE (Critère C59, E.III.2) :

        est_bien_ordonne(R,E)  ⇒  ( heredite_transfinie(P,R,E) ⇒ conclusion_transfinie(P,E) ).
    """
    return impl(E.est_bien_ordonne(R, _t(e)),
                impl(heredite_transfinie(P, R, e, x, y), conclusion_transfinie(P, e, x)))


# ════════════════════════════════════════════════════════════════════════════
#  PREUVE GÉNÉRIQUE — recurrence_transfinie(P, E, R) par plus-petit-contre-exemple.
# ════════════════════════════════════════════════════════════════════════════
def recurrence_transfinie_preuve(P, e="E", G="G", x0="x0tf", y="ytf",
                                 ebind="Eax", xbind="xAax"):
    """⊢ recurrence_transfinie(P, R, E)   — CLOS, 0 hypothèse résiduelle.

    PREUVE GÉNÉRIQUE (vaut pour TOUTE fonction P : Terme→Formule) par plus-petit-
    contre-exemple.  R = relation portée par le graphe G (a≤b := (a,b)∈G), comme
    partout dans le package ordre.  La séparation S8 de A = {x∈E | ¬P[x]} est un
    axiome DÉDIÉ (theorie reste 22) ; le ≤-min vient de l'hypothèse de bon ordre.

    Binders DISTINCTS pour éviter toute capture avec les binders internes de P :
    contre-exemple x0='x0tf', segment y='ytf', séparation E='Eax'/x='xAax'."""
    ve = _t(e)
    R = _graphe_R(G)

    # ── hypothèses globales ──────────────────────────────────────────────────
    W = E.est_bien_ordonne(R, ve)                         # le bon ordre
    hW = N.assume(W)
    Hyp = heredite_transfinie(P, R, ve, x0, y)            # hérédité transfinie (binder x0)
    hHyp = N.assume(Hyp)

    # ── briques tirées de W ──────────────────────────────────────────────────
    ord_clause = conjonction_elim_gauche(hW)             # est_relation_ordre_dans(R,E)
    rel_ordre = conjonction_elim_gauche(ord_clause)      # est_relation_ordre(R)
    antisym = conjonction_elim_droite(conjonction_elim_gauche(rel_ordre))  # ordre_antisymetrique(R)
    least_clause = conjonction_elim_droite(hW)           # (∀X)((X⊂E et X≠∅) ⇒ (∃a)min)

    A = _A(P, ve)

    # ════════════════════════════════════════════════════════════════════════
    #  On fixe x0 ; sous { x0∈E, ¬P[x0] } on dérive une CONTRADICTION.
    # ════════════════════════════════════════════════════════════════════════
    vx0 = var(x0)
    h_x0_in_E = N.assume(appartient(vx0, ve))            # x0 ∈ E
    h_nP_x0 = N.assume(non(P(vx0)))                      # ¬P[x0]

    # ── x0 ∈ A  (x0∈E ; ¬P[x0]) — TÉMOIGNE A≠∅
    corps_A_x0 = conjonction_intro(h_x0_in_E, h_nP_x0)
    x0_in_A = N.modus_ponens(corps_A_x0,
        equivalence_arriere(_A_membre(P, ve, vx0, ebind, xbind)))     # x0 ∈ A

    # ── BON ORDRE : ≤-MIN de A.  W projette la clause de bon ordre, X:=A.
    A_sub = _A_inclus_E(P, ve, ebind, xbind)            # inclus(A,E)        [CLOS]
    A_ne = _A_non_vide(P, ve, x0_in_A)                  # ¬(A=∅)            [x0∈E, ¬P[x0]]
    least_A = instancie(least_clause, A)               # (A⊂E et A≠∅) ⇒ (∃a)min
    ante = conjonction_intro(A_sub, A_ne)              # A⊂E et A≠∅
    ex_min = N.modus_ponens(ante, least_A)             # (∃a)( a∈A et (∀w)(w∈A ⇒ a≤w) )

    # ── ouvrir le ∃a : binders de la clause de bon ordre (a='a', w='w')
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    amin, wcmp = "a", "w"
    vmin, vw = var(amin), var(wcmp)
    corps_min = et(appartient(vmin, A),
        pourtout(wcmp, impl(appartient(vw, A), R(vmin, vw))))
    hMin = N.assume(corps_min)
    min_in_A = conjonction_elim_gauche(hMin)           # m ∈ A
    min_le_all = conjonction_elim_droite(hMin)         # (∀w)(w∈A ⇒ m≤w)

    min_corps = N.modus_ponens(min_in_A,
        equivalence_avant(_A_membre(P, ve, vmin, ebind, xbind)))      # m∈E et ¬P[m]
    min_in_E = conjonction_elim_gauche(min_corps)      # m ∈ E
    nP_min = conjonction_elim_droite(min_corps)        # ¬P[m]

    # ════════════════════════════════════════════════════════════════════════
    #  P[y] pour tout y ∈ seg(R,E,m).  Fixe y, assume y∈seg(R,E,m), prouve P[y].
    # ════════════════════════════════════════════════════════════════════════
    vy = var(y)
    seg_m = E.segment_extremite(R, ve, vmin)
    h_y_in_seg = N.assume(appartient(vy, seg_m))        # y ∈ seg(R,E,m)
    seg_corps = N.modus_ponens(h_y_in_seg,
        equivalence_avant(_seg_membre(R, ve, vmin, vy)))             # (y∈E et y≤m) et y≠m
    y_le_min = conjonction_elim_droite(conjonction_elim_gauche(seg_corps))  # y ≤ m
    y_ne_min = conjonction_elim_droite(seg_corps)       # y ≠ m

    # ── P[y] par l'absurde : assume ¬P[y] ⇒ y∈A ⇒ m≤y ; antisym (y≤m, m≤y) ⇒ y=m ⊥
    h_nP_y = N.assume(non(P(vy)))                       # ¬P[y]  (réfutation)
    y_in_E = conjonction_elim_gauche(conjonction_elim_gauche(seg_corps))    # y ∈ E
    corps_y_in_A = conjonction_intro(y_in_E, h_nP_y)
    y_in_A = N.modus_ponens(corps_y_in_A,
        equivalence_arriere(_A_membre(P, ve, vy, ebind, xbind)))     # y ∈ A
    min_le_y = N.modus_ponens(y_in_A, instancie(min_le_all, vy))     # m ≤ y
    # antisym instancié à (y, m) :  (y≤m et m≤y) ⇒ y=m
    antisym_ym = instancie(instancie(antisym, vy), vmin)            # (y≤m et m≤y) ⇒ y=m
    y_eq_min = N.modus_ponens(conjonction_intro(y_le_min, min_le_y), antisym_ym)  # y = m
    # contradiction y=m ∧ y≠m  ⇒  ¬¬P[y]  (consequentia mirabilis) ⇒ P[y]
    nn_P_y = _refute_self(N.loi_deduction(non(P(vy)),
        _ex_falso(y_eq_min, y_ne_min, non(non(P(vy))))))            # ¬¬P[y]
    P_y = N.modus_ponens(nn_P_y, dne(P(vy)))           # P[y]        [y∈seg(R,E,m), corps_min, ...]

    # ── (∀y)( y∈seg(R,E,m) ⇒ P[y] )
    P_on_seg = N.generalisation(y, N.loi_deduction(appartient(vy, seg_m), P_y))

    # ════════════════════════════════════════════════════════════════════════
    #  HÉRÉDITÉ : Hyp instanciée à m (m∈E) ⇒ P[m].  Contredit ¬P[m].
    # ════════════════════════════════════════════════════════════════════════
    Hyp_m = instancie(hHyp, vmin)                      # m∈E ⇒ ((∀y)(y∈seg(R,E,m)⇒P[y]) ⇒ P[m])
    Hyp_m_dev = N.modus_ponens(min_in_E, Hyp_m)        # (∀y)(y∈seg(R,E,m)⇒P[y]) ⇒ P[m]
    P_min = N.modus_ponens(P_on_seg, Hyp_m_dev)        # P[m]
    # contradiction P[m] ∧ ¬P[m]  →  P[x0]  (ex falso ; cible P[x0]).  Sous corps_min.
    P_x0_fromMin = _ex_falso(P_min, nP_min, P(vx0))    # P[x0]   [corps_min, ..., x0∈E, ¬P[x0]]

    # ── refermer le ∃a (existe_elimination sur 'a')
    P_x0_underNeg = N.modus_ponens(ex_min,
        existe_elimination(N.loi_deduction(corps_min, P_x0_fromMin), amin))  # P[x0] [x0∈E,¬P[x0],W,Hyp]

    # ── ¬P[x0] ⇒ ¬¬P[x0]  (dni) ⇒ ¬¬P[x0]  (consequentia mirabilis) ⇒ P[x0]
    neg_imp_dneg = N.loi_deduction(non(P(vx0)),
        N.modus_ponens(P_x0_underNeg, dni(P(vx0))))    # ¬P[x0] ⇒ ¬¬P[x0]
    nn_P_x0 = _refute_self(neg_imp_dneg)               # ¬¬P[x0]   [x0∈E, W, Hyp]
    P_x0 = N.modus_ponens(nn_P_x0, dne(P(vx0)))        # P[x0]     [x0∈E, W, Hyp]

    # ════════════════════════════════════════════════════════════════════════
    #  Assemblage : (x0∈E ⇒ P[x0]), généralise (∀x0), décharge Hyp puis W.
    # ════════════════════════════════════════════════════════════════════════
    corps_concl = N.loi_deduction(appartient(vx0, ve), P_x0)   # (x0∈E ⇒ P[x0])   [W, Hyp]
    concl_all = N.generalisation(x0, corps_concl)              # (∀x0)(x0∈E ⇒ P[x0])  [W, Hyp]

    cible_concl = conclusion_transfinie(P, ve, x0)
    assert concl_all.conclusion == cible_concl, "conclusion ≠ conclusion_transfinie(P,E)"

    res_inner = N.loi_deduction(Hyp, concl_all)        # Hyp ⇒ conclusion        [W]
    res = N.loi_deduction(W, res_inner)                # W ⇒ (Hyp ⇒ conclusion)  [CLOS]

    # binders effectifs : contre-exemple/conclusion 'x0tf', segment 'ytf'
    assert res.conclusion == recurrence_transfinie(P, R, ve, x0, y), \
        "conclusion ≠ recurrence_transfinie(P,R,E)"
    return res


__all__ = [
    "heredite_transfinie", "conclusion_transfinie", "recurrence_transfinie",
    "recurrence_transfinie_preuve",
]
