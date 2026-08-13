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

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, non, impl, equiv, appartient, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere, dne, dni,
    antecedent_consequent,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element


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
def _seg_membre(G, e, x, y):
    """⊢ ( y ∈ seg(G,E,x) ) ⇔ ( (y∈E et y≤x) et y≠x )   (axiome instancié aux TERMES G,E,x,y).

    L'axiome est CLOS (∀G∀E∀x∀y) depuis la migration seg_ext : on l'instancie
    D'ABORD sur le graphe G, puis sur E, x, y."""
    th = E.theorie_segment_extremite()
    ax = N.axiome(th, E.axiome_segment_extremite())      # (∀G)(∀E)(∀x)(∀y)( y∈S_x ⇔ ((y∈E et (y,x)∈G) et y≠x) )
    return instancie(instancie(instancie(instancie(ax, _t(G)), _t(e)), _t(x)), _t(y))


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS (formules-cible) — récurrence transfinie C59.
# ════════════════════════════════════════════════════════════════════════════
def heredite_transfinie(P, G, e, x="x", y="y"):
    """(∀x)( x∈E ⇒ ( (∀y)( y∈seg(G,E,x) ⇒ P[y] )  ⇒  P[x] ) )   (HÉRÉDITÉ transfinie).

    « Pour tout x∈E, si P vaut sur tout le segment initial ]←,x[, alors P[x]. »
    ⚠️ MIGRÉ : 2ᵉ argument = le GRAPHE de l'ordre (terme), plus une relation callable."""
    vx, vy = var(x), var(y)
    seg_x = E.segment_extremite(_t(G), _t(e), vx)
    devant = pourtout(y, impl(appartient(vy, seg_x), P(vy)))      # P sur seg(R,E,x)
    return pourtout(x, impl(appartient(vx, _t(e)), impl(devant, P(vx))))


def conclusion_transfinie(P, e, x="x"):
    """(∀x)( x∈E ⇒ P[x] )   (CONCLUSION : P vaut partout sur E)."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _t(e)), P(vx)))


# @livre Ch.III §2.2 Def.- | E III.17 L.33-33 | PDF p.120  (titre « 2. Le principe de récurrence transfinie »)
# @livre Ch.III §2.2 Lem.2 | E III.17 L.34-38 | PDF p.120
#   (Lemme 2 : 𝔖 ensemble de segments stable par réunion et par S_x ∪ {x} ⇒
#    tout segment de E est dans 𝔖 — c'est le SQUELETTE de l'induction sur les
#    segments que réalise la preuve par plus-petit-contre-exemple de ce module
#    et le gluing C60 voisin ; la démo du livre continue en E III.18, annotée)
# @livre Ch.III §2.2 Crit.59 | E III.18 L.5-9 | PDF p.121
def recurrence_transfinie(P, G, e, x="x", y="y"):
    """Énoncé du PRINCIPE DE RÉCURRENCE TRANSFINIE (Critère C59, E.III.2) :

        est_bien_ordonne(R,E)  ⇒  ( heredite_transfinie(P,G,E) ⇒ conclusion_transfinie(P,E) ).

    ⚠️ MIGRÉ : 2ᵉ argument = le GRAPHE G (terme) ; la relation ≤ qu'il porte
    (a≤b := (a,b)∈G) est reconstruite ici pour `est_bien_ordonne`."""
    return impl(E.est_bien_ordonne(_graphe_R(G), _t(e)),
                impl(heredite_transfinie(P, G, e, x, y), conclusion_transfinie(P, e, x)))


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
    Hyp = heredite_transfinie(P, G, ve, x0, y)            # hérédité transfinie (binder x0)
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
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
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
    seg_m = E.segment_extremite(_t(G), ve, vmin)
    h_y_in_seg = N.assume(appartient(vy, seg_m))        # y ∈ seg(R,E,m)
    seg_corps = N.modus_ponens(h_y_in_seg,
        equivalence_avant(_seg_membre(G, ve, vmin, vy)))             # (y∈E et y≤m) et y≠m
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
    assert res.conclusion == recurrence_transfinie(P, G, ve, x0, y), \
        "conclusion ≠ recurrence_transfinie(P,G,E)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  C60 — DÉFINITION PAR RÉCURRENCE TRANSFINIE : énoncés + UNICITÉ (corollaire C59).
#
#  Bourbaki, E.III.2 Critère C60 : sur un ensemble bien ordonné (E,R), une « règle »
#  qui à chaque x associe une valeur dépendant de la restriction de f au segment
#  seg(R,E,x) DÉTERMINE une UNIQUE fonction f vérifiant l'équation de récursion
#       f(x) = (règle appliquée à f|seg(R,E,x))    pour tout x∈E.
#
#  EXISTENCE (la moitié dure : f = réunion des fonctions partielles sur les segments,
#  via la machinerie de recollement) → REPORTÉE honnêtement (gros chantier ; cf.
#  l'infra `ensembles_recollement_bijection`).  UNICITÉ → CONSÉQUENCE DIRECTE de C59
#  (induction transfinie) ci-dessous : deux solutions coïncident PONCTUELLEMENT.
#
#  On représente une « solution candidate » par sa fonction-VALEUR  vf : Terme→Terme
#  (vf(x) = la valeur de la candidate en x, p.ex. E.valeur(graphe_de(f),x)).  Le
#  prédicat d'induction est  P[x] := ( vf(x) = vg(x) ).
# ════════════════════════════════════════════════════════════════════════════
def _P_egal_valeurs(vf, vg):
    """Prédicat d'induction P[x] := ( vf(x) = vg(x) )  (fonction Terme→Formule)."""
    return lambda x: egal(vf(_t(x)), vg(_t(x)))


def regle_coherente_sur_segments(vf, vg, G, e, x="x", y="y"):
    """HÉRÉDITÉ de l'unicité = « la règle respecte la coïncidence sur les segments » :

        (∀x)( x∈E ⇒ ( (∀y)( y∈seg(R,E,x) ⇒ vf(y)=vg(y) )  ⇒  vf(x)=vg(x) ) ).

    C'est EXACTEMENT `heredite_transfinie(P,R,E)` pour P[x] := vf(x)=vg(x).  Sa vérité
    EST le contenu de l'équation de récursion C60 : si vf=((règle)|f) et vg=((règle)|g)
    et que f,g coïncident sur seg(R,E,x), alors la règle — qui ne dépend de f QUE via
    f|seg(R,E,x) — rend la même valeur, donc vf(x)=vg(x).  HYPOTHÈSE HONNÊTE, INTENTION-
    NELLE (l'unicité C60 N'est PAS inconditionnelle : elle suppose que les deux solutions
    obéissent à la MÊME règle de récursion ; cette coïncidence-sur-segments en est la
    traduction fidèle)."""
    P = _P_egal_valeurs(vf, vg)
    return heredite_transfinie(P, G, e, x, y)


def coincidence_solutions(vf, vg, e, x="x"):
    """CONCLUSION d'unicité (PONCTUELLE) :  (∀x)( x∈E ⇒ vf(x)=vg(x) )."""
    P = _P_egal_valeurs(vf, vg)
    return conclusion_transfinie(P, e, x)


# @livre Ch.III §2.2 Crit.60 | E III.18 L.20-24 | PDF p.121
def recursion_transfinie_unicite(vf, vg, e="E", G="G", x0="x0tf", y="ytf",
                                 ebind="Eax", xbind="xAax"):
    """⊢ { est_bien_ordonne(R,E),  regle_coherente_sur_segments(vf,vg,R,E) } ⊢
         (∀x)( x∈E ⇒ vf(x)=vg(x) )                            [ UNICITÉ C60 ].

    MOITIÉ UNICITÉ du Critère C60 (définition par récursion transfinie), DÉRIVÉE du
    métathéorème C59 `recurrence_transfinie_preuve` appliqué à P[x] := vf(x)=vg(x).
    Deux solutions d'une même règle de récursion (toutes deux cohérentes sur les
    segments) COÏNCIDENT en tout point de E.

    ⚠️ DEUX HYPOTHÈSES HONNÊTES, INTENTIONNELLES, déchargées par loi_deduction
    (JAMAIS postulées ; theorie=22) :
      • est_bien_ordonne(R,E)            — (E,R) est bien ordonné (hypothèse de C60) ;
      • regle_coherente_sur_segments(…)  — l'équation de récursion C60 elle-même
        (la règle ne dépend de la solution que via sa restriction au segment).
    L'EXISTENCE d'une solution reste REPORTÉE (moitié dure, recollement).

    vf, vg : fonctions Python Terme→Terme (les fonctions-VALEUR des deux candidates).
    R = relation portée par le graphe G (a≤b := (a,b)∈G)."""
    ve = _t(e)
    R = _graphe_R(G)
    P = _P_egal_valeurs(vf, vg)

    c59 = recurrence_transfinie_preuve(P, e, G, x0, y, ebind, xbind)  # W⇒(héréd⇒concl) [CLOS]

    W = E.est_bien_ordonne(R, ve)
    her = regle_coherente_sur_segments(vf, vg, G, ve, x0, y)          # = heredite_transfinie(P)
    inner = N.modus_ponens(N.assume(W), c59)                          # héréd ⇒ concl   [W]
    concl = N.modus_ponens(N.assume(her), inner)                      # concl  [W, héréd]

    cible = coincidence_solutions(vf, vg, ve, x0)
    assert concl.conclusion == cible, "conclusion ≠ coincidence_solutions(vf,vg,E)"
    assert W in concl.hypotheses and her in concl.hypotheses, "hyps inattendues"
    assert len(concl.hypotheses) == 2, "hypothèses résiduelles inattendues (≠ 2)"
    return concl


__all__ = [
    # C59 — induction transfinie (CLOS, 0 hyp)
    "heredite_transfinie", "conclusion_transfinie", "recurrence_transfinie",
    "recurrence_transfinie_preuve",
    # C60 — définition par récursion transfinie : UNICITÉ (corollaire C59, 2 hyps honnêtes)
    "regle_coherente_sur_segments", "coincidence_solutions",
    "recursion_transfinie_unicite",
]
