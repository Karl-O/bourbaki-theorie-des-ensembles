"""§III.2 — ORDRE INDUIT sur un SOUS-ENSEMBLE : `graphe_induit(Ro,B)` et le THÉORÈME
de TRANSPORT du BON ORDRE  `bo(Ro,a) ∧ B⊆a  ⊢  bo(graphe_induit(Ro,B), B)`.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Pour appliquer la machinerie de la trichotomie (Th3 §III.2) à un couple
« (B, ordre induit) vs (a, Ro) », il faut que l'ordre induit sur B soit porté par
un GRAPHE (terme ensembliste), et NON par une simple λ-relation `ordre_induit` :
`_R_de(graphe)` interroge l'appartenance du COUPLE `(u,v)∈graphe`, donc l'ordre
induit doit être COLLECTIVISÉ.

On pose le GRAPHE INDUIT (sélection S8 dans Ro, motif `axiome_pullback` /
`diagonale_cantor` / `axiome_W`) caractérisé — DANS UNE THÉORIE DÉDIÉE, donc
theorie_ensembles() reste 22 — par sa membership de COUPLE (forme couple-only,
exactement comme l'axiome de h) :

    (∀u)(∀v)( (u,v) ∈ graphe_induit(Ro,B)  ⇔  ( (u,v)∈Ro  et  ( u∈B et v∈B ) ) ).

C'est la collectivisation S8 du prédicat « (u,v)∈Ro et u,v∈B » : le sous-graphe de
Ro restreint aux couples d'éléments de B = l'ordre INDUIT de Ro sur B (E.III.1.1,
Exemple 2).  La relation portée est donc

    R_ind{u,v} := (u,v) ∈ graphe_induit(Ro,B)  ⇔  ( Ro{u,v} et u∈B et v∈B )

soit EXACTEMENT `ordre_induit(_R_de(Ro), B)` au niveau de la relation.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie_ensembles=22, rien postulé du but) :

  ✅ `graphe_induit(Ro,B)` : le terme du sous-graphe induit (app).
  ✅ `axiome_graphe_induit` / `theorie_graphe_induit` / `membre_graphe_induit` :
     la membership de COUPLE, forme SET-couple instanciée.
  ✅ `Rind` : la relation portée `_R_de(graphe_induit(Ro,B))` (= ordre induit).
  🎯🎯 `bo_induit_B(Ro,a,B)` :
        { bo(_R_de(Ro),a),  B⊆a }  ⊢  bo( _R_de(graphe_induit(Ro,B)) , B ).
     LE TRANSPORT DU BON ORDRE à un sous-ensemble : tout sous-ensemble B d'un
     ensemble bien ordonné (a,Ro) est bien ordonné par l'ordre induit.  (E.III.2.1,
     « tout sous-ensemble d'un ensemble bien ordonné est bien ordonné ».)

     PREUVE.
       • est_relation_ordre_dans(R_ind, B) : transitif/antisym/reflexif-implicite
         de R_ind se DÉRIVENT de ceux de Ro + le filtre « u,v∈B » ; la réflexivité-
         DANS-B (R_ind{x,x} ⇔ x∈B) : (⇒) projection ; (⇐) x∈B⊆a ⇒ x∈a ⇒ Ro{x,x}
         (Ro réflexif-dans-a) ⇒ R_ind{x,x}.
       • CLAUSE de plus petit : X⊆B non vide ⇒ X⊆a non vide (B⊆a) ⇒ (bon ordre de a)
         plus petit m∈X pour Ro ; pour w∈X⊆B, Ro{m,w} et m,w∈B ⇒ R_ind{m,w}.

⚠️ La bare restriction `bo(_R_de(Ro), B)` (MÊME graphe Ro, ensemble B) est FAUSSE
(la réflexivité-DANS-B exigerait Ro{x,x} ⇔ x∈B, or Ro{x,x} ⇔ x∈a) : c'est pourquoi
l'ordre induit doit être le GRAPHE COLLECTIVISÉ, pas Ro restreint.

INVARIANT : theorie_ensembles() = 22 (le seul axiome neuf, axiome_graphe_induit, vit
dans theorie_graphe_induit, JAMAIS dans theorie_ensembles).  RIEN POSTULÉ du but : le
bon ordre induit DÉRIVE du bon ordre de a + B⊆a.  NON vacueux.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_segments_construction import _R_de


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_HOLE = "hole_ordind"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  Le GRAPHE INDUIT comme ENSEMBLE : axiome DÉFINITIONNEL de membre (couple, S8).
# ════════════════════════════════════════════════════════════════════════════
def graphe_induit(Ro, B):
    """graphe_induit(Ro,B) := { (u,v)∈Ro | u∈B et v∈B }  (sous-graphe induit, E.III.1.1).

    Terme collectivisant (sélection S8 dans Ro) ; caractérisé par
    AXIOME_GRAPHE_INDUIT (forme couple-only), DANS UNE THÉORIE DÉDIÉE."""
    return E.app("graphe_induit", _t(Ro), _t(B))


def Rind(Ro, B):
    """La RELATION portée par le graphe induit :  R_ind{u,v} := (u,v)∈graphe_induit(Ro,B).

    == _R_de(graphe_induit(Ro,B)).  Au niveau de l'équivalence (membre_graphe_induit) :
    R_ind{u,v} ⇔ ( Ro{u,v} et u∈B et v∈B ) = ordre_induit(_R_de(Ro),B)."""
    return _R_de(graphe_induit(Ro, B))


def _corps_couple(Ro, B, u, v):
    """Le corps de la sélection au COUPLE (u,v) :  ( (u,v)∈Ro  et  ( u∈B et v∈B ) )."""
    Rof = _R_de(Ro)
    vu, vv = _t(u), _t(v)
    return et(Rof(vu, vv), et(appartient(vu, _t(B)), appartient(vv, _t(B))))


def axiome_graphe_induit(Ro="Ro", B="B", u="ui", v="vi"):
    """⊢-schéma  (∀u)(∀v)( (u,v) ∈ graphe_induit(Ro,B)  ⇔  ( (u,v)∈Ro et (u∈B et v∈B) ) ).

    Axiome DÉFINITIONNEL du graphe induit (sélection S8 du prédicat « (u,v)∈Ro et
    u∈B et v∈B », unicité A1 ; motif axiome_pullback).  Forme COUPLE-ONLY (comme
    l'axiome de h) : suffisante car _R_de n'interroge que la membership de couple.
    N'ALTÈRE PAS theorie_ensembles()."""
    vu, vv = var(u), var(v)
    cpl = E.couple(vu, vv)
    return pourtout(u, pourtout(v,
        equiv(appartient(cpl, graphe_induit(Ro, B)),
              _corps_couple(Ro, B, vu, vv))))


def theorie_graphe_induit(Ro="Ro", B="B", u="ui", v="vi"):
    """Théorie DÉDIÉE ne contenant que l'axiome de sélection du graphe induit.
    theorie_ensembles() reste = 22 ; le graphe induit est introduit hors d'elle."""
    return N.Theorie("Graphe-induit-sous-ensemble",
                     [axiome_graphe_induit(Ro, B, u, v)])


def membre_graphe_induit(Ro="Ro", B="B", u="ui", v="vi"):
    """⊢ ( (u,v) ∈ graphe_induit(Ro,B) )  ⇔  ( (u,v)∈Ro et (u∈B et v∈B) ).

    L'axiome de sélection instancié aux TERMES u,v."""
    ax = N.axiome(theorie_graphe_induit(Ro, B, u, v),
                  axiome_graphe_induit(Ro, B, u, v))
    return instancie(instancie(ax, _t(u)), _t(v))


def _Rind_avant(Ro, B, u, v, h_in):
    """De ⊢ R_ind{u,v} déduit ⊢ ( Ro{u,v} et (u∈B et v∈B) )."""
    return N.modus_ponens(h_in, equivalence_avant(membre_graphe_induit(Ro, B, u, v)))


def _Rind_arriere(Ro, B, u, v, h_corps):
    """De ⊢ ( Ro{u,v} et (u∈B et v∈B) ) déduit ⊢ R_ind{u,v}."""
    return N.modus_ponens(h_corps, equivalence_arriere(membre_graphe_induit(Ro, B, u, v)))


# ════════════════════════════════════════════════════════════════════════════
#  Extraction des propriétés d'ordre de Ro depuis bo(Ro,a).
# ════════════════════════════════════════════════════════════════════════════
def _proprietes_Ro(Ro, a):
    """De ⊢ est_bien_ordonne(_R_de(Ro),a) [assumé] renvoie le n-uplet
    ( Hbo, h_trans, h_anti, h_refl_impl, h_refl_dans, clause_pp )."""
    Rof = _R_de(Ro)
    va = _t(a)
    Hbo = N.assume(E.est_bien_ordonne(Rof, va))
    ord_dans = conjonction_elim_gauche(Hbo)              # est_relation_ordre_dans(Ro,a)
    clause = conjonction_elim_droite(Hbo)                # clause plus petit (∀X)
    rel_ordre = conjonction_elim_gauche(ord_dans)        # est_relation_ordre(Ro)
    h_refl_dans = conjonction_elim_droite(ord_dans)      # est_reflexive_dans_ordre(Ro,a)
    trans_anti = conjonction_elim_gauche(rel_ordre)      # transitif et antisym
    h_refl_impl = conjonction_elim_droite(rel_ordre)     # ordre_reflexif_implicite(Ro)
    h_trans = conjonction_elim_gauche(trans_anti)        # ordre_transitif(Ro)
    h_anti = conjonction_elim_droite(trans_anti)         # ordre_antisymetrique(Ro)
    return Hbo, h_trans, h_anti, h_refl_impl, h_refl_dans, clause


# ════════════════════════════════════════════════════════════════════════════
#  est_relation_ordre_dans(R_ind, B)  — transitif, antisym, reflexif-impl, reflexif-dans-B.
# ════════════════════════════════════════════════════════════════════════════
def _transitif_induit(Ro, a, B, h_trans):
    """⊢ ordre_transitif(R_ind)  (depuis ordre_transitif(Ro))."""
    vx, vy, vz = var("x"), var("y"), var("z")
    Rind_f = Rind(Ro, B)
    # (R_ind{x,y} et R_ind{y,z}) ⇒ R_ind{x,z}
    Hpre = N.assume(et(Rind_f(vx, vy), Rind_f(vy, vz)))
    rxy = conjonction_elim_gauche(Hpre)
    ryz = conjonction_elim_droite(Hpre)
    cxy = _Rind_avant(Ro, B, vx, vy, rxy)               # Ro{x,y} et (x∈B et y∈B)
    cyz = _Rind_avant(Ro, B, vy, vz, ryz)               # Ro{y,z} et (y∈B et z∈B)
    Roxy = conjonction_elim_gauche(cxy)
    Royz = conjonction_elim_gauche(cyz)
    x_in_B = conjonction_elim_gauche(conjonction_elim_droite(cxy))   # x∈B
    z_in_B = conjonction_elim_droite(conjonction_elim_droite(cyz))   # z∈B
    Rof = _R_de(Ro)
    trans = instancie(instancie(instancie(h_trans, vx), vy), vz)     # (Ro{x,y} et Ro{y,z})⇒Ro{x,z}
    Roxz = N.modus_ponens(conjonction_intro(Roxy, Royz), trans)      # Ro{x,z}
    corps = conjonction_intro(Roxz, conjonction_intro(x_in_B, z_in_B))
    Rind_xz = _Rind_arriere(Ro, B, vx, vz, corps)                    # R_ind{x,z}
    body = N.loi_deduction(et(Rind_f(vx, vy), Rind_f(vy, vz)), Rind_xz)
    res = N.generalisation("x", N.generalisation("y", N.generalisation("z", body)))
    assert res.conclusion == E.ordre_transitif(Rind_f), "transitif induit mal formé"
    return res


def _antisym_induit(Ro, a, B, h_anti):
    """⊢ ordre_antisymetrique(R_ind)  (depuis ordre_antisymetrique(Ro))."""
    vx, vy = var("x"), var("y")
    Rind_f = Rind(Ro, B)
    Hpre = N.assume(et(Rind_f(vx, vy), Rind_f(vy, vx)))
    rxy = conjonction_elim_gauche(Hpre)
    ryx = conjonction_elim_droite(Hpre)
    cxy = _Rind_avant(Ro, B, vx, vy, rxy)
    cyx = _Rind_avant(Ro, B, vy, vx, ryx)
    Roxy = conjonction_elim_gauche(cxy)
    Royx = conjonction_elim_gauche(cyx)
    anti = instancie(instancie(h_anti, vx), vy)          # (Ro{x,y} et Ro{y,x}) ⇒ x=y
    x_eq_y = N.modus_ponens(conjonction_intro(Roxy, Royx), anti)
    body = N.loi_deduction(et(Rind_f(vx, vy), Rind_f(vy, vx)), x_eq_y)
    res = N.generalisation("x", N.generalisation("y", body))
    assert res.conclusion == E.ordre_antisymetrique(Rind_f), "antisym induit mal formé"
    return res


def _refl_impl_induit(Ro, a, B, h_refl_impl):
    """⊢ ordre_reflexif_implicite(R_ind) :  R_ind{x,y} ⇒ (R_ind{x,x} et R_ind{y,y})."""
    vx, vy = var("x"), var("y")
    Rind_f = Rind(Ro, B)
    Rof = _R_de(Ro)
    Hxy = N.assume(Rind_f(vx, vy))                        # R_ind{x,y}
    cxy = _Rind_avant(Ro, B, vx, vy, Hxy)                # Ro{x,y} et (x∈B et y∈B)
    Roxy = conjonction_elim_gauche(cxy)
    x_in_B = conjonction_elim_gauche(conjonction_elim_droite(cxy))
    y_in_B = conjonction_elim_droite(conjonction_elim_droite(cxy))
    # Ro réflexif implicite : Ro{x,y} ⇒ (Ro{x,x} et Ro{y,y})
    ri = instancie(instancie(h_refl_impl, vx), vy)
    Roxx_Royy = N.modus_ponens(Roxy, ri)
    Roxx = conjonction_elim_gauche(Roxx_Royy)
    Royy = conjonction_elim_droite(Roxx_Royy)
    # R_ind{x,x} et R_ind{y,y}
    Rind_xx = _Rind_arriere(Ro, B, vx, vx, conjonction_intro(Roxx, conjonction_intro(x_in_B, x_in_B)))
    Rind_yy = _Rind_arriere(Ro, B, vy, vy, conjonction_intro(Royy, conjonction_intro(y_in_B, y_in_B)))
    concl = conjonction_intro(Rind_xx, Rind_yy)
    body = N.loi_deduction(Rind_f(vx, vy), concl)
    res = N.generalisation("x", N.generalisation("y", body))
    assert res.conclusion == E.ordre_reflexif_implicite(Rind_f), "refl impl induit mal formé"
    return res


def _refl_dans_induit(Ro, a, B, h_refl_dans, h_B_sub_a):
    """⊢ est_reflexive_dans_ordre(R_ind, B) :  (∀x)( R_ind{x,x} ⇔ x∈B ).

    (⇒) R_ind{x,x} ⇒ x∈B (projection) ; (⇐) x∈B ⇒ x∈a (B⊆a) ⇒ Ro{x,x} (Ro réflexif-
    dans-a) ⇒ R_ind{x,x}."""
    vx = var("x")
    Rind_f = Rind(Ro, B)
    Rof = _R_de(Ro)
    va, vB = _t(a), _t(B)
    # (⇒) R_ind{x,x} ⇒ x∈B
    Hxx = N.assume(Rind_f(vx, vx))
    cxx = _Rind_avant(Ro, B, vx, vx, Hxx)
    x_in_B_fwd = conjonction_elim_gauche(conjonction_elim_droite(cxx))   # x∈B
    fwd = N.loi_deduction(Rind_f(vx, vx), x_in_B_fwd)
    # (⇐) x∈B ⇒ R_ind{x,x}
    HxB = N.assume(appartient(vx, vB))
    x_in_a = N.modus_ponens(HxB, instancie(h_B_sub_a, vx))   # x∈a
    refl_x = instancie(h_refl_dans, vx)                       # Ro{x,x} ⇔ x∈a
    Roxx = N.modus_ponens(x_in_a, equivalence_arriere(refl_x))   # Ro{x,x}
    corps = conjonction_intro(Roxx, conjonction_intro(HxB, HxB))
    Rind_xx = _Rind_arriere(Ro, B, vx, vx, corps)
    bwd = N.loi_deduction(appartient(vx, vB), Rind_xx)
    eqv = conjonction_intro(fwd, bwd)                         # R_ind{x,x} ⇔ x∈B
    res = N.generalisation("x", eqv)
    assert res.conclusion == E.est_reflexive_dans_ordre(Rind_f, vB), "refl dans B mal formé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CLAUSE de plus petit élément pour R_ind : X⊆B non vide ⇒ ∃ R_ind-min.
# ════════════════════════════════════════════════════════════════════════════
def _clause_induite(Ro, a, B, clause_Ro, h_B_sub_a, X="X", m="a", w="w"):
    """⊢ (∀X)( (X⊆B et X≠∅) ⇒ (∃m)( m∈X et (∀w)(w∈X ⇒ R_ind{m,w}) ) ).

    X⊆B⊆a non vide ⇒ (bon ordre de a, clause_Ro) plus petit m∈X pour Ro ; pour w∈X⊆B,
    Ro{m,w} et m,w∈B ⇒ R_ind{m,w}."""
    Rof, Rind_f = _R_de(Ro), Rind(Ro, B)
    va, vB = _t(a), _t(B)
    vX = var(X)
    vm, vw = var(m), var(w)
    # X⊆B ⇒ X⊆a  (transitivité de ⊂ via B⊆a)
    HX = N.assume(et(inclus(vX, vB), non(egal(vX, E.VIDE))))
    X_sub_B = conjonction_elim_gauche(HX)
    X_ne = conjonction_elim_droite(HX)
    # X⊆a : pour z∈X, z∈B (X⊆B) puis z∈a (B⊆a) — binder « z » canonique de inclus
    vz = var("z")
    Hz = N.assume(appartient(vz, vX))
    z_in_B = N.modus_ponens(Hz, instancie(X_sub_B, vz))
    z_in_a = N.modus_ponens(z_in_B, instancie(h_B_sub_a, vz))
    X_sub_a = N.generalisation("z", N.loi_deduction(appartient(vz, vX), z_in_a))
    assert X_sub_a.conclusion == inclus(vX, va), "X⊆a binder mismatch"
    # clause de Ro instanciée à X : (X⊆a et X≠∅) ⇒ (∃m)(m∈X et (∀w)(w∈X⇒Ro{m,w}))
    clause_X = instancie(clause_Ro, vX)
    pp = N.modus_ponens(conjonction_intro(X_sub_a, X_ne), clause_X)   # (∃m)(...)
    # per-témoin m : (m∈X et (∀w)(w∈X⇒Ro{m,w})) ⊢ (m∈X et (∀w)(w∈X⇒R_ind{m,w}))
    corps_Ro = et(appartient(vm, vX),
                  pourtout(w, impl(appartient(vw, vX), Rof(vm, vw))))
    Hm = N.assume(corps_Ro)
    m_in_X = conjonction_elim_gauche(Hm)
    body_Ro = conjonction_elim_droite(Hm)
    m_in_B = N.modus_ponens(m_in_X, instancie(X_sub_B, vm))   # m∈B
    # per-w : w∈X ⊢ R_ind{m,w}
    Hw = N.assume(appartient(vw, vX))
    w_in_B = N.modus_ponens(Hw, instancie(X_sub_B, vw))       # w∈B
    Romw = N.modus_ponens(Hw, instancie(body_Ro, vw))         # Ro{m,w}
    corps_couple = conjonction_intro(Romw, conjonction_intro(m_in_B, w_in_B))
    Rind_mw = _Rind_arriere(Ro, B, vm, vw, corps_couple)      # R_ind{m,w}
    body_w = N.generalisation(w, N.loi_deduction(appartient(vw, vX), Rind_mw))
    corps_induit = conjonction_intro(m_in_X, body_w)          # m∈X et (∀w∈X)R_ind{m,w}
    # introduire (∃m)
    body_ex = et(appartient(vm, vX),
                 pourtout(w, impl(appartient(vw, vX), Rind_f(vm, vw))))
    ex = N.modus_ponens(corps_induit, N.s5(body_ex, vm, m))
    wit_imp = N.loi_deduction(corps_Ro, ex)
    ex_imp = existe_elimination(wit_imp, m)
    pp_induit = N.modus_ponens(pp, ex_imp)                    # (∃m)(...induit)
    body_imp = N.loi_deduction(et(inclus(vX, vB), non(egal(vX, E.VIDE))), pp_induit)
    return N.generalisation(X, body_imp)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LE TRANSPORT DU BON ORDRE — bo(R_ind, B) sous { bo(Ro,a), B⊆a }.
# ════════════════════════════════════════════════════════════════════════════
def bo_induit_B(Ro="Ro", a="a", B="B"):
    """⊢ { bo(_R_de(Ro),a),  B⊆a }  ⊢  bo( _R_de(graphe_induit(Ro,B)) , B ).

    🎯🎯 TOUT SOUS-ENSEMBLE D'UN ENSEMBLE BIEN ORDONNÉ EST BIEN ORDONNÉ par l'ordre
    induit (E.III.2.1).  La structure d'ordre induit R_ind{u,v} = ((u,v)∈Ro et u,v∈B)
    HÉRITE transitivité/antisymétrie/réflexivité-implicite de Ro (avec le filtre B), la
    réflexivité-DANS-B vient de B⊆a + Ro réflexif-dans-a, et la clause de plus petit
    élément vient de celle de a (X⊆B⊆a).

    HYPOTHÈSES HONNÊTES : { bo(_R_de(Ro),a), B⊆a }.  theorie_ensembles()=22, rien
    postulé du but.  NON vacueux : la conclusion bo(R_ind,B) n'est aucune hypothèse."""
    Rof, Rind_f = _R_de(Ro), Rind(Ro, B)
    va, vB = _t(a), _t(B)
    Hbo, h_trans, h_anti, h_refl_impl, h_refl_dans, clause = _proprietes_Ro(Ro, a)
    h_B_sub_a = N.assume(inclus(vB, va))                      # B⊆a

    # ── est_relation_ordre_dans(R_ind, B) ──────────────────────────────────────
    trans = _transitif_induit(Ro, a, B, h_trans)
    anti = _antisym_induit(Ro, a, B, h_anti)
    refl_impl = _refl_impl_induit(Ro, a, B, h_refl_impl)
    refl_dans = _refl_dans_induit(Ro, a, B, h_refl_dans, h_B_sub_a)
    rel_ordre = conjonction_intro(conjonction_intro(trans, anti), refl_impl)
    assert rel_ordre.conclusion == E.est_relation_ordre(Rind_f), "est_relation_ordre induit mal formé"
    ord_dans = conjonction_intro(rel_ordre, refl_dans)
    assert ord_dans.conclusion == E.est_relation_ordre_dans(Rind_f, vB), \
        "est_relation_ordre_dans induit mal formé"

    # ── clause de plus petit ───────────────────────────────────────────────────
    clause_ind = _clause_induite(Ro, a, B, clause, h_B_sub_a)

    res = conjonction_intro(ord_dans, clause_ind)
    assert res.conclusion == E.est_bien_ordonne(Rind_f, vB), \
        "conclusion ≠ bo(R_ind,B)"
    return res


def bo_induit_B_cible(Ro="Ro", a="a", B="B"):
    """ÉNONCÉ-cible (test miroir) : bo( _R_de(graphe_induit(Ro,B)) , B )."""
    return E.est_bien_ordonne(Rind(Ro, B), _t(B))


def bo_induit_B_hypotheses(Ro="Ro", a="a", B="B"):
    """Les 2 HYPOTHÈSES SURVIVANTES ATTENDUES : { bo(_R_de(Ro),a), B⊆a }."""
    return {E.est_bien_ordonne(_R_de(Ro), _t(a)), inclus(_t(B), _t(a))}


__all__ = [
    "graphe_induit", "Rind",
    "axiome_graphe_induit", "theorie_graphe_induit", "membre_graphe_induit",
    "bo_induit_B", "bo_induit_B_cible", "bo_induit_B_hypotheses",
]
