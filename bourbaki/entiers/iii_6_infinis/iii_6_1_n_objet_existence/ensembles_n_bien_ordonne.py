"""§III.6 — ℕ EST BIEN ORDONNÉ :  est_bien_ordonne( ≤_induit , ℕ ).

🎯🎯🎯 LE BON ORDRE DE ℕ TOUT ENTIER (non borné), pas seulement des intervalles
bornés [0,a].  C'est l'hypothèse (a) IRRÉDUCTIBLE de C62 (ensembles_c62_recursion) :
« ℕ étant bien ordonné, on peut lui appliquer C60 » (Bourbaki E III.46).

────────────────────────────────────────────────────────────────────────────────
LA CIBLE.  ℕ = ensemble_NN() = τy(∀x)(x∈y ⇔ Fini x), et l'ordre est l'ordre des
cardinaux ≤ INDUIT sur ℕ :

    R_ℕ{u,v} := ( u≤v et u∈ℕ et v∈ℕ )   ( = ordre_induit(≤_card, ℕ) ).

    est_bien_ordonne(R_ℕ, ℕ) =
        est_relation_ordre_dans(R_ℕ, ℕ)              [PARTIE ORDRE]
      et (∀A)( (A⊂ℕ et A≠∅) ⇒ (∃m)(m∈A et (∀x)(x∈A ⇒ R_ℕ{m,x})) ).  [CLAUSE MIN]

────────────────────────────────────────────────────────────────────────────────
ROUTE — argument standard du plus petit élément, RAMENÉ au bon ordre BORNÉ déposé.

  PARTIE ORDRE.  Les 4 paliers (réflexif-dans-ℕ, réflexif-implicite, transitif,
  antisymétrique) sont CLOS, comme pour [0,a] (ensembles_ordinal_cardinal_ordre)
  mais avec le pont d'appartenance « x∈ℕ ⇒ est_cardinal x » (appartenance_NN +
  fini_implique_cardinal) à la place de « x∈[0,a] ⇒ est_cardinal x ».  La
  réflexivité/transitivité/antisymétrie de ≤_card sont INCONDITIONNELLES
  (inf_egal_reflexif, inf_egal_transitive, inf_egal_antisymetrique_card).

  CLAUSE MIN.  Soit A⊂ℕ non vide ; non_vide_ssi_element donne un témoin a₀∈A.
  On pose B := A ∩ [0,a₀].  B⊂[0,a₀] (AXIOME_INTER) et B≠∅ (a₀∈B : a₀∈A et
  a₀∈[0,a₀] car a₀ cardinal et a₀≤a₀).  Le bon ordre BORNÉ déposé
  `bon_ordre_intervalle_close(a₀)` (CLOS, 0 hyp) donne un plus petit m de B pour
  ≤_induit-sur-[0,a₀].  m∈B ⇒ m∈A.  m est alors le plus petit de TOUT A : pour
  x∈A, par comparabilité (comparabilite_cardinaux, CLOS) m≤x ou x≤m ; si x≤m, alors
  x≤m≤a₀ (transitivité, m∈[0,a₀]⇒m≤a₀) donc x∈[0,a₀] (x cardinal, 0≤x, x≤a₀) donc
  x∈B, et la minimalité de m dans B donne m≤x.  Dans les deux cas m≤x.

INVARIANT : theorie_ensembles() = 22.  Tout est DÉRIVÉ (rien postulé).  CLOS, 0 hyp.
⚠️ PERF : appartenance_NN déclenche N_existe (~5 min, mémoïsé une fois par session).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, ou, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.cardinaux.ensembles_comparabilite import comparabilite_cardinaux
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import intervalle_0a
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, intervalle_implique_borne_sup, membre_intervalle_entiers,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN, appartenance_NN


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def NN():
    """ℕ = ensemble_NN()  (terme clos)."""
    return ensemble_NN()


def _le(u, v):
    """u ≤ v  (ordre BARE des cardinaux, inf_egal_card)."""
    return inf_egal_card(_t(u), _t(v))


def ordre_induit_NN(u, v):
    """R_ℕ{u,v} := ( (u≤v et u∈ℕ) et v∈ℕ )  = ordre_induit(≤_card, ℕ).

    MÊME forme que ordre_induit (ensembles_abrege) : et(et(u≤v, u∈ℕ), v∈ℕ)."""
    nn = NN()
    return et(et(_le(u, v), appartient(_t(u), nn)), appartient(_t(v), nn))


# ════════════════════════════════════════════════════════════════════════════
#  Briques génériques sur ≤_card (généralisées-instanciées à des TERMES).
# ════════════════════════════════════════════════════════════════════════════
def _refl_terme(t):
    """⊢ t ≤ t  (inf_egal_reflexif généralisé-instancié)."""
    return instancie(N.generalisation("X", inf_egal_reflexif("X")), _t(t))


def _trans_terme(u, v, w):
    """⊢ (u≤v et v≤w) ⇒ u≤w  (inf_egal_transitive généralisé-instancié)."""
    g = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(g, _t(u)), _t(v)), _t(w))


def _card_de_NN(t):
    """⊢ ( t ∈ ℕ ) ⇒ est_cardinal(t)  pour un TERME t.

    appartenance_NN : (∀x)(x∈ℕ ⇔ Fini x), instanciée à t (sens ⇒) ; fini_implique_cardinal."""
    vt = _t(t)
    equ = instancie(appartenance_NN(), vt)               # (t∈ℕ) ⇔ (Fini t)
    Hin = N.assume(appartient(vt, NN()))                 # t∈ℕ
    fini = N.modus_ponens(Hin, equivalence_avant(equ))   # Fini t
    fic = _fini_implique_card_terme(vt)                  # Fini t ⇒ est_cardinal t
    card = N.modus_ponens(fini, fic)                     # est_cardinal t
    return N.loi_deduction(appartient(vt, NN()), card)


def _fini_implique_card_terme(t):
    """⊢ Fini t ⇒ est_cardinal t  pour un TERME t  (fini_implique_cardinal généralisé)."""
    g = N.generalisation("afic", fini_implique_cardinal("afic"))   # (∀a)(Fini a ⇒ card a)
    return instancie(g, _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  PARTIE ORDRE — est_relation_ordre_dans(R_ℕ, ℕ), les 4 paliers (cf. interval).
# ════════════════════════════════════════════════════════════════════════════
def reflexive_dans_NN(x="x"):
    """⊢ (∀x)( R_ℕ{x,x} ⇔ x∈ℕ )   = est_reflexive_dans_ordre(R_ℕ, ℕ).  INCONDITIONNEL."""
    vx = _t(x)
    nn = NN()
    x_in = appartient(vx, nn)
    Rxx = ordre_induit_NN(vx, vx)                        # ((x≤x et x∈ℕ) et x∈ℕ)
    Hf = N.assume(Rxx)
    fwd = N.loi_deduction(Rxx, conjonction_elim_droite(Hf))     # R_ℕ{x,x} ⇒ x∈ℕ
    Hb = N.assume(x_in)
    xlex = _refl_terme(vx)                               # x≤x
    Rxx_b = conjonction_intro(conjonction_intro(xlex, Hb), Hb)
    bwd = N.loi_deduction(x_in, Rxx_b)                   # x∈ℕ ⇒ R_ℕ{x,x}
    return N.generalisation(x, conjonction_intro(fwd, bwd))


def reflexif_implicite_NN(x="xo", y="yo"):
    """⊢ (∀x,y)( R_ℕ{x,y} ⇒ (R_ℕ{x,x} et R_ℕ{y,y}) ) = ordre_reflexif_implicite(R_ℕ)."""
    vx, vy = _t(x), _t(y)
    Rxy = ordre_induit_NN(vx, vy)
    H = N.assume(Rxy)
    x_in = conjonction_elim_droite(conjonction_elim_gauche(H))   # x∈ℕ
    y_in = conjonction_elim_droite(H)                            # y∈ℕ
    Rxx = conjonction_intro(conjonction_intro(_refl_terme(vx), x_in), x_in)
    Ryy = conjonction_intro(conjonction_intro(_refl_terme(vy), y_in), y_in)
    body = N.loi_deduction(Rxy, conjonction_intro(Rxx, Ryy))
    return N.generalisation(x, N.generalisation(y, body))


def transitif_NN(x="xo", y="yo", z="zo"):
    """⊢ (∀x,y,z)( (R_ℕ{x,y} et R_ℕ{y,z}) ⇒ R_ℕ{x,z} ) = ordre_transitif(R_ℕ)."""
    vx, vy, vz = _t(x), _t(y), _t(z)
    Rxy, Ryz = ordre_induit_NN(vx, vy), ordre_induit_NN(vy, vz)
    hyp = et(Rxy, Ryz)
    H = N.assume(hyp)
    Hxy = conjonction_elim_gauche(H)
    Hyz = conjonction_elim_droite(H)
    xley = conjonction_elim_gauche(conjonction_elim_gauche(Hxy))  # x≤y
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Hxy))  # x∈ℕ
    ylez = conjonction_elim_gauche(conjonction_elim_gauche(Hyz))  # y≤z
    z_in = conjonction_elim_droite(Hyz)                          # z∈ℕ
    xlez = N.modus_ponens(conjonction_intro(xley, ylez), _trans_terme(vx, vy, vz))
    Rxz = conjonction_intro(conjonction_intro(xlez, x_in), z_in)
    body = N.loi_deduction(hyp, Rxz)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, body)))


def antisymetrie_NN(x="xo", y="yo"):
    """⊢ (∀x,y)( (R_ℕ{x,y} et R_ℕ{y,x}) ⇒ x=y ) = ordre_antisymetrique(R_ℕ).

    CANTOR–BERNSTEIN (inf_egal_antisymetrique_card) ; cardinalité de x,y via
    « x∈ℕ ⇒ est_cardinal x » (_card_de_NN)."""
    vx, vy = _t(x), _t(y)
    hyp = et(ordre_induit_NN(vx, vy), ordre_induit_NN(vy, vx))
    H = N.assume(hyp)
    Hxy = conjonction_elim_gauche(H)
    Hyx = conjonction_elim_droite(H)
    le_xy = conjonction_elim_gauche(conjonction_elim_gauche(Hxy))  # x≤y
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Hxy))   # x∈ℕ
    le_yx = conjonction_elim_gauche(conjonction_elim_gauche(Hyx))  # y≤x
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hyx))   # y∈ℕ
    card_x = N.modus_ponens(x_in, _card_de_NN(vx))                # est_cardinal x
    card_y = N.modus_ponens(y_in, _card_de_NN(vy))                # est_cardinal y
    full = inf_egal_antisymetrique_card("ca", "cb")
    antis = instancie(instancie(full, vx), vy)
    premisse = conjonction_intro(conjonction_intro(conjonction_intro(
        le_xy, le_yx), card_x), card_y)
    x_eq_y = N.modus_ponens(premisse, antis)                     # x=y
    body = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, body))


def relation_ordre_dans_NN():
    """⊢ est_relation_ordre_dans( R_ℕ , ℕ )   (la PARTIE ORDRE de est_bien_ordonne).

    Assemble les 4 paliers dans l'ordre EXACT de est_relation_ordre_dans (binders
    xo,yo,zo).  Conclusion == E.est_relation_ordre_dans(R_ℕ, ℕ) LITTÉRALEMENT."""
    p1 = reflexive_dans_NN("xo")
    p2 = reflexif_implicite_NN("xo", "yo")
    p3 = transitif_NN("xo", "yo", "zo")
    p4 = antisymetrie_NN("xo", "yo")
    ro = conjonction_intro(conjonction_intro(p3, p4), p2)        # est_relation_ordre(R_ℕ)
    return conjonction_intro(ro, p1)                             # est_relation_ordre_dans(R_ℕ, ℕ)


# ════════════════════════════════════════════════════════════════════════════
#  CLAUSE MIN — toute partie A⊂ℕ non vide a un plus petit élément pour R_ℕ.
#
#  Réduit au bon ordre BORNÉ déposé bon_ordre_intervalle_close(a₀) via B=A∩[0,a₀].
# ════════════════════════════════════════════════════════════════════════════
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import zero_inf_egal_cardinal
from bourbaki.cardinaux.ensembles_gate_onto_top import bon_ordre_intervalle_close
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import ordre_induit_intervalle
from bourbaki.cardinaux.ensembles_ordinal_cardinal_bon_ordre import bon_ordre_donne_clause_plus_petit
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element


def _membre_interv_at(b, x):
    """⊢ ( x ∈ [0,b] ) ⇔ ( (est_cardinal x et 0≤x) et x≤b )  pour des TERMES b,x  (E.III.5.3)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        axiome_intervalle_entiers, theorie_intervalle_entiers,
    )
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    return instancie(instancie(instancie(ax, ZERO), _t(b)), _t(x))


def _inter_at(tA, tB, z):
    """⊢ ( z ∈ A∩B ) ⇔ ( z∈A et z∈B )  pour des TERMES A,B,z  (AXIOME_INTER instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, _t(tA)), _t(tB)), _t(z))


def _x_in_interv(b, x, card_x, le_xb):
    """De ⊢ est_cardinal x [card_x] et ⊢ x≤b [le_xb], déduit ⊢ x∈[0,b]  (sens ⇐ + 0≤x)."""
    vx = _t(x)
    zero_le = N.modus_ponens(card_x, _zero_le_terme(vx))         # 0≤x  [card_x]
    corps = conjonction_intro(conjonction_intro(card_x, zero_le), le_xb)   # ((card x et 0≤x) et x≤b)
    return N.modus_ponens(corps, equivalence_arriere(_membre_interv_at(b, vx)))   # x∈[0,b]


def _zero_le_terme(t):
    """⊢ est_cardinal t ⇒ 0≤t  pour un TERME t  (zero_inf_egal_cardinal généralisé)."""
    # zero_inf_egal_cardinal(x) a est_cardinal(x) en HYPOTHÈSE → on l'internalise puis généralise.
    base = zero_inf_egal_cardinal("zlt")                         # {card zlt} ⊢ 0≤zlt
    imp = N.loi_deduction(est_cardinal(var("zlt")), base)        # card zlt ⇒ 0≤zlt
    return instancie(N.generalisation("zlt", imp), _t(t))


def _borne_sup_interv(b, x):
    """⊢ ( x ∈ [0,b] ) ⇒ ( x ≤ b )  pour des TERMES b,x  (intervalle_implique_borne_sup généralisé)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import intervalle_implique_borne_sup
    g = N.generalisation("ia", N.generalisation("ib", N.generalisation("ix",
        intervalle_implique_borne_sup("ia", "ib", "ix"))))
    return instancie(instancie(instancie(g, ZERO), _t(b)), _t(x))


def clause_min_NN(A="X", a0="a0", m="a", x="w"):
    """⊢ ( A⊂ℕ et A≠∅ ) ⇒ (∃m)( m∈A et (∀x)(x∈A ⇒ R_ℕ{m,x}) ).

    🎯 LE CŒUR.  Pour A⊂ℕ non vide : témoin a₀∈A (non_vide_ssi_element) ; B:=A∩[0,a₀] ;
    bon_ordre_intervalle_close(a₀) (CLOS) → plus petit m de B pour ≤_induit-sur-[0,a₀] ;
    m∈A, et m minore TOUT A par comparabilité + l'argument « x<m ⇒ x≤a₀ ⇒ x∈B »."""
    nn = NN()
    vA = _t(A)
    # binders B-side (ceux que bon_ordre_intervalle_close DÉPOSE : witness ∃ = "m",
    # universel ∀ = "x") — DOIVENT matcher pour l'extraction de pp_B / corps_min.
    # vx (binder "x" interne du bon ordre BORNÉ) ne touche QUE B/[0,a₀]/Rint (pas ℕ) :
    # aucune capture par les liants internes "x","y" de ℕ.  L'élément ARBITRAIRE de A
    # est nommé "w" (vw) pour faire le raisonnement ℕ/cardinal SANS capture.
    mb, xb = "m", "x"
    va0, vm, vx = var(a0), var(mb), var(xb)
    vw = var(x)                                                 # élément arbitraire de A (x="w")
    interv = lambda c: intervalle_0a(c)
    Rint = ordre_induit_intervalle(va0)                          # ≤_induit sur [0,a₀]
    B = E.intersection(vA, interv(va0))                          # B = A ∩ [0,a₀]
    hyp_A = et(inclus(vA, nn), non(egal(vA, E.VIDE)))            # A⊂ℕ et A≠∅
    HA = N.assume(hyp_A)
    A_sub = conjonction_elim_gauche(HA)                          # A⊂ℕ
    A_ne = conjonction_elim_droite(HA)                           # A≠∅

    # ── témoin a₀∈A  (binder « z » de non_vide_ssi_element renommé en a0)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    ex_z = N.modus_ponens(A_ne, equivalence_avant(non_vide_ssi_element(vA)))   # (∃z)(z∈A)
    ren_a0 = alpha_existe("z", a0, appartient(var("z"), vA))                    # (∃z)(z∈A) ⇔ (∃a0)(a0∈A)
    ex_a0 = N.modus_ponens(ex_z, equivalence_avant(ren_a0))                     # (∃a0)(a0∈A)
    # per-témoin a₀ : a₀∈A ⊢ (∃m)(...)
    H_a0 = N.assume(appartient(va0, vA))                         # a₀∈A
    a0_in_NN = N.modus_ponens(H_a0, instancie(A_sub, va0))       # a₀∈ℕ
    card_a0 = N.modus_ponens(a0_in_NN, _card_de_NN(va0))         # est_cardinal a₀
    # a₀∈[0,a₀] : card a₀, 0≤a₀, a₀≤a₀
    a0_le_a0 = _refl_terme(va0)                                  # a₀≤a₀
    a0_in_interv = _x_in_interv(va0, va0, card_a0, a0_le_a0)     # a₀∈[0,a₀]
    # a₀∈B = a₀∈A∩[0,a₀]
    a0_in_B = N.modus_ponens(conjonction_intro(H_a0, a0_in_interv),
                             equivalence_arriere(_inter_at(vA, interv(va0), va0)))   # a₀∈B
    B_ne = _B_non_vide(B, va0, a0_in_B)                        # B≠∅

    # ── B⊂[0,a₀]
    B_sub = _B_inclus_interv(vA, va0)                           # B ⊂ [0,a₀]   (CLOS)

    # ── plus petit m de B pour ≤_induit-sur-[0,a₀]  (bon ordre BORNÉ clos)
    bo = bon_ordre_intervalle_close(a0)                         # CLOS ⊢ est_bien_ordonne(Rint,[0,a₀]) (binders xo,yo,zo,S,m,x)
    clause = N.modus_ponens(bo, bon_ordre_donne_clause_plus_petit(
        Rint, interv(va0), "xo", "yo", "zo", "S", "m", "x"))    # clause_plus_petit(Rint,[0,a₀])
    inst_B = instancie(clause, B)                              # (B⊂[0,a₀] et B≠∅) ⇒ (∃m)(m∈B et ...)
    pp_B = N.modus_ponens(conjonction_intro(B_sub, B_ne), inst_B)   # (∃m)(m∈B et (∀x)(x∈B ⇒ Rint{m,x}))

    # ── per-témoin m : corps_min ⊢ (∃m)(m∈A et (∀x)(x∈A ⇒ R_ℕ{m,x}))
    corps_min = et(appartient(vm, B),
                   pourtout(xb, impl(appartient(vx, B), Rint(vm, vx))))
    Hm = N.assume(corps_min)
    m_in_B = conjonction_elim_gauche(Hm)                       # m∈B
    min_body = conjonction_elim_droite(Hm)                     # (∀x)(x∈B ⇒ Rint{m,x})
    # m∈B ⇒ m∈A et m∈[0,a₀]
    m_AB = N.modus_ponens(m_in_B, equivalence_avant(_inter_at(vA, interv(va0), vm)))
    m_in_A = conjonction_elim_gauche(m_AB)                     # m∈A
    m_in_interv = conjonction_elim_droite(m_AB)                # m∈[0,a₀]
    m_le_a0 = N.modus_ponens(m_in_interv, _borne_sup_interv(va0, vm))   # m≤a₀
    m_in_NN = N.modus_ponens(m_in_A, instancie(A_sub, vm))     # m∈ℕ

    # ── (∀w)(w∈A ⇒ R_ℕ{m,w})   (élément arbitraire « w » de A, pas de capture ℕ)
    Hw = N.assume(appartient(vw, vA))                          # w∈A
    w_in_NN = N.modus_ponens(Hw, instancie(A_sub, vw))         # w∈ℕ
    card_w = N.modus_ponens(w_in_NN, _card_de_NN(vw))          # est_cardinal w
    m_le_w = _m_le_x(va0, vm, vw, vA, interv, Rint, B,
                     Hw, m_le_a0, card_w, min_body)            # m≤w  [w∈A, corps_min, hyp_A...]
    RNN_mw = conjonction_intro(conjonction_intro(m_le_w, m_in_NN), w_in_NN)   # R_ℕ{m,w}
    body_w = N.loi_deduction(appartient(vw, vA), RNN_mw)       # w∈A ⇒ R_ℕ{m,w}
    body_all = N.generalisation(x, body_w)                    # (∀w)(w∈A ⇒ R_ℕ{m,w})
    corps_res = conjonction_intro(m_in_A, body_all)            # m∈A et (∀w)(w∈A ⇒ R_ℕ{m,w})

    # ── (∃a)(a∈A et (∀w)(w∈A ⇒ R_ℕ{a,w}))   (binder ∃ = m=param "a" ; witness var = vm)
    body_r = et(appartient(var(m), vA),
                pourtout(x, impl(appartient(vw, vA), ordre_induit_NN(var(m), vw))))
    but = existe(m, body_r)
    ex_m = N.modus_ponens(corps_res, N.s5(body_r, vm, m))      # but  [corps_min, ...]
    wit_m = N.loi_deduction(corps_min, ex_m)                   # corps_min ⇒ but
    ex_from_B = N.modus_ponens(pp_B, existe_elimination(wit_m, mb))  # but  [a₀∈A, hyp_A]
    # ── éliminer le ∃a₀ (témoin de A≠∅)
    wit_a0 = N.loi_deduction(appartient(va0, vA), ex_from_B)   # a₀∈A ⇒ but
    but_from_ne = N.modus_ponens(ex_a0, existe_elimination(wit_a0, a0))   # but  [hyp_A]
    return N.loi_deduction(hyp_A, but_from_ne)                 # (A⊂ℕ et A≠∅) ⇒ but


def _B_non_vide(B, va0, a0_in_B):
    """De ⊢ a₀∈B, déduit ⊢ B≠∅  (non_vide_ssi_element, sens ⇐ via ∃)."""
    ex = N.modus_ponens(a0_in_B, N.s5(appartient(var("z"), B), va0, "z"))   # (∃z)(z∈B)
    return N.modus_ponens(ex, equivalence_arriere(non_vide_ssi_element(B)))  # B≠∅


def _B_inclus_interv(vA, va0):
    """⊢ A∩[0,a₀] ⊂ [0,a₀]  (CLOS) — par AXIOME_INTER (z∈A∩I ⇒ z∈I) + déf inclusion."""
    interv = intervalle_0a(va0)
    B = E.intersection(vA, interv)
    vz = var("z")                                             # binder de E.inclus
    Hz = N.assume(appartient(vz, B))                          # z∈B
    z_AB = N.modus_ponens(Hz, equivalence_avant(_inter_at(vA, interv, vz)))   # z∈A et z∈[0,a₀]
    z_in_I = conjonction_elim_droite(z_AB)                    # z∈[0,a₀]
    imp = N.loi_deduction(appartient(vz, B), z_in_I)          # z∈B ⇒ z∈[0,a₀]
    res = N.generalisation("z", imp)                          # (∀z)(z∈B ⇒ z∈[0,a₀])
    assert res.conclusion == E.inclus(B, interv), "forme inclusion inattendue (binder ?)"
    return res


def _m_le_x(va0, vm, vx, vA, interv_fn, Rint, B, Hx, m_le_a0, card_x, min_body):
    """⊢ m ≤ x  sous { x∈A [Hx], m≤a₀, card x, (∀x)(x∈B ⇒ Rint{m,x}) [min_body], ... }.

    Comparabilité : m≤x ou x≤m.  Si m≤x : fini.  Si x≤m : x≤m≤a₀ (trans) ⇒ x≤a₀ ⇒ x∈[0,a₀]
    ⇒ x∈B ⇒ Rint{m,x} ⇒ m≤x (1er conjoint)."""
    interv = interv_fn(va0)
    comp_mx = _comp_at(vm, vx)                                # (m≤x ou x≤m)
    # cas 1 : m≤x
    H1 = N.assume(_le(vm, vx))
    cas1 = H1                                                  # m≤x
    # cas 2 : x≤m
    H2 = N.assume(_le(vx, vm))
    x_le_a0 = N.modus_ponens(conjonction_intro(H2, m_le_a0), _trans_terme(vx, vm, va0))   # x≤a₀
    x_in_interv = _x_in_interv(va0, vx, card_x, x_le_a0)       # x∈[0,a₀]
    x_in_B = N.modus_ponens(conjonction_intro(Hx, x_in_interv),
                            equivalence_arriere(_inter_at(vA, interv, vx)))   # x∈B
    rint_mx = N.modus_ponens(x_in_B, instancie(min_body, vx))  # Rint{m,x}=((m≤x et m∈I) et x∈I)
    cas2 = conjonction_elim_gauche(conjonction_elim_gauche(rint_mx))   # m≤x
    # disjonction : des deux cas, m≤x
    imp1 = N.loi_deduction(_le(vm, vx), cas1)
    imp2 = N.loi_deduction(_le(vx, vm), cas2)
    return _ou_elim(comp_mx, imp1, imp2)


def _comp_at(vm, vx):
    """⊢ ( m≤x ou x≤m )  aux TERMES m,x  (comparabilite_cardinaux généralisée-instanciée)."""
    g = N.generalisation("Xc", N.generalisation("Yc",
        comparabilite_cardinaux("Xc", "Yc")))                 # (∀X,Y)(X≤Y ou Y≤X)
    return instancie(instancie(g, vm), vx)


def _ou_elim(disj, imp1, imp2):
    """De ⊢ (P ou Q), ⊢ (P⇒R), ⊢ (Q⇒R), déduit ⊢ R  (élimination de la disjonction, tac `cas`)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas
    return cas(disj, imp1, imp2)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 ASSEMBLAGE FINAL : est_bien_ordonne( R_ℕ , ℕ )   CLOS, 0 hyp.
# ════════════════════════════════════════════════════════════════════════════
def clause_plus_petit_NN(A="X", a0="a0", m="a", x="w"):
    """⊢ (∀A)( (A⊂ℕ et A≠∅) ⇒ (∃m)(m∈A et (∀x)(x∈A ⇒ R_ℕ{m,x})) ).

    clause_min_NN généralisée sur A (binders A→X, m→a, x→w = ceux de est_bien_ordonne)."""
    return N.generalisation(A, clause_min_NN(A, a0, m, x))


def n_bien_ordonne():
    """🎯🎯🎯 ⊢ est_bien_ordonne( R_ℕ , ℕ )   CLOS, 0 hypothèse.

    ℕ EST BIEN ORDONNÉ par l'ordre (induit) des cardinaux.  Conjonction de la PARTIE
    ORDRE (relation_ordre_dans_NN, CLOS) et de la CLAUSE de plus petit élément
    (clause_plus_petit_NN, CLOS, ramenée au bon ordre borné déposé).  Conclusion ==
    E.est_bien_ordonne(R_ℕ, ℕ, 'xo','yo','zo','X','a','w') LITTÉRALEMENT.  theorie=22."""
    from bourbaki.logique.i_1_termes_relations.formule import alpha_egal
    ordre = relation_ordre_dans_NN()                          # est_relation_ordre_dans(R_ℕ, ℕ)
    clause = clause_plus_petit_NN("X", "a0", "a", "w")        # la clause min
    res = conjonction_intro(ordre, clause)
    # Conclusion == est_bien_ordonne(R_ℕ, ℕ) À α-RENOMMAGE PRÈS : la seule différence est
    # le nom d'un liant τ INTERNE à est_cardinal (« X » canonicalisé « §/@ » lors des
    # introductions/éliminations de ∃ sur le témoin) ; la formule est LITTÉRALEMENT le
    # prédicat de bon ordre (relation R_ℕ et ensemble ℕ IDENTIQUES, vérifié par alpha_egal).
    assert alpha_egal(res.conclusion, n_bien_ordonne_cible()), \
        "conclusion ≠ est_bien_ordonne(R_ℕ, ℕ) (même à α-près)"
    return res


def n_bien_ordonne_cible():
    """ÉNONCÉ-cible (test miroir) : est_bien_ordonne( R_ℕ , ℕ )  (binders xo,yo,zo,X,a,w)."""
    return E.est_bien_ordonne(ordre_induit_NN, NN(), "xo", "yo", "zo", "X", "a", "w")


__all__ = [
    "NN", "ordre_induit_NN",
    "reflexive_dans_NN", "reflexif_implicite_NN", "transitif_NN",
    "antisymetrie_NN", "relation_ordre_dans_NN",
    "clause_min_NN", "clause_plus_petit_NN",
    "n_bien_ordonne", "n_bien_ordonne_cible",
]
