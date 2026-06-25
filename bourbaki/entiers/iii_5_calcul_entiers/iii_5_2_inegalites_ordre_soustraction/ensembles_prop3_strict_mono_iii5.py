"""§III.5.2 — PROPOSITION 3 (cas BINAIRE, MONOTONIE STRICTE) : a<b ⇒ a+c<b+c et a·c<b·c.

🎯 Le cas BINAIRE de la PROPOSITION 3 §III.5.2 (E III.36, LUE au PDF source) :

    « PROPOSITION 3. — Soient (a_ι) et (b_ι) deux familles finies d'entiers telles
      que a_ι ≤ b_ι pour tout ι et a_ι < b_ι pour un indice au moins.  On a alors
      ∑ a_ι < ∑ b_ι.  Si l'on suppose de plus b_ι > 0 pour tout ι, on a ∏ a_ι < ∏ b_ι. »

La preuve bourbakiste isole l'indice j où a_j<b_j, pose b_j = a_j + c_j avec c_j>0
(Prop. 2), et obtient ∑b_ι = c_j + ∑a_ι (donc ∑a_ι < ∑b_ι par Prop. 2), et de même
∏b_ι = (a_j+c_j)∏_J b_ι ⩾ a_j∏_J b_ι + c_j∏_J b_ι avec c_j·∏b_ι ≠ 0 (Prop. 7).  Le
CŒUR de cet argument est exactement le cas BINAIRE prouvé ici :

    somme_strict_monotone(a,b,c) :
        ⊢ ( est_entier a et est_entier b et est_entier c et a < b ) ⇒ a+c < b+c.

    produit_strict_monotone(a,b,c) :
        ⊢ ( est_entier a et est_entier b et est_entier c et c≠0 et a < b ) ⇒ a·c < b·c.

────────────────────────────────────────────────────────────────────────────────
ROUTE (sur prop2_strict_equivalence §III.5.2, déjà CLOSE) :

SOMME.  a<b ⇒ (Prop. 2 ⇒) ∃d( entier d, d≠0, b=a+d ).  Pour ce témoin d :
    b+c = (a+d)+c = (a+c)+d           [réarrangement cardinal : assoc + commut]
  avec d entier ≠0, et a+c, b+c entiers (somme_binaire_entier).  Prop. 2 (⇐) donne
  a+c < b+c.

PRODUIT.  a<b ⇒ ∃d( entier d, d≠0, b=a+d ).  Pour ce témoin d :
    b·c = (a+d)·c = a·c + d·c          [distributivité cardinale]
  avec d·c ≠ 0 (Prop. 7 : d≠0 et c≠0 ⇒ d·c≠0) et d·c entier (produit_binaire_entier),
  a·c, b·c entiers.  Prop. 2 (⇐) (avec témoin d·c) donne a·c < b·c.

⚠️ INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ : tout DÉRIVE de théorèmes
   CLOS (prop2_strict_equivalence, somme_cardinale_associative/commutative,
   distributivite_cardinale, prop7_produit_non_nul, somme_binaire_entier,
   produit_binaire_entier).  Gardes HONNÊTES = l'énoncé bourbakiste.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, non, et, impl, existe,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_arriere,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_strict_card,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative, somme_cardinale_associative,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_distributivite_cardinale import (
    distributivite_cardinale,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_entier, ZERO
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    _sdc, somme_binaire_entier,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_binaire_entier,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes_prop7 import (
    prop7_produit_non_nul,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop2_strict_iii5 import (
    prop2_strict_forward, prop2_strict_backward, _rhs,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _card_de_card_t(tx):
    """⊢ est_cardinal(x) ⇒ Card x = x  pour un TERME x (capture-safe)."""
    gen = N.generalisation("xccd3", cardinal_de_cardinal("xccd3"))
    return instancie(gen, _t(tx))


def _assoc_t(tx, ty, tz):
    """somme_cardinale_associative version TERME capture-safe (généralise+instancie).

    ⊢ Card((x⊔y)⊔z) = Card(x⊔(y⊔z))  pour TERMES x,y,z — contourne la capture des
    liants internes (u,up,A,B,…) du graphe de réassociation quand x/y/z sont composés."""
    g = somme_cardinale_associative("Xast3", "Yast3", "Zast3")
    gen = N.generalisation("Xast3", N.generalisation("Yast3",
          N.generalisation("Zast3", g)))
    return instancie(instancie(instancie(gen, _t(tx)), _t(ty)), _t(tz))


# ══════════════════════════════════════════════════════════════════════════════
#  RÉARRANGEMENT CARDINAL :  (x+y)+z = x+(y+z)   (associativité binaire des cardinaux)
# ══════════════════════════════════════════════════════════════════════════════
def _plus_assoc(x, y, z):
    """⊢ (est_cardinal x et est_cardinal y et est_cardinal z) ⇒ (x+y)+z = x+(y+z).

    Réarrangement au niveau des CARDINAUX (et non des ensembles), via le pont _sdc :
        (x+y)+z = Card((x⊔y)⊔z)        [sdc(x⊔y, z, x+y, z) ; Card(x⊔y)=x+y déf, Card z=z]
                = Card(x⊔(y⊔z))        [somme_cardinale_associative, déf des +]
                = x+(y+z)              [sdc(x, y⊔z, x, y+z) ; Card x=x, Card(y⊔z)=y+z déf].
    (x+y := Card(x⊔y) par DÉFINITION de somme_cardinale_binaire.)"""
    vx, vy, vz = _t(x), _t(y), _t(z)
    xy = somme_disjointe(vx, vy)            # x⊔y
    yz = somme_disjointe(vy, vz)            # y⊔z
    sum_xy = somme_cardinale_binaire(vx, vy)   # x+y = Card(x⊔y)  (déf)
    sum_yz = somme_cardinale_binaire(vy, vz)   # y+z = Card(y⊔z)  (déf)

    h = N.assume(et(est_cardinal(vx), et(est_cardinal(vy), est_cardinal(vz))))
    cx = conjonction_elim_gauche(h)
    cy = conjonction_elim_gauche(conjonction_elim_droite(h))
    cz = conjonction_elim_droite(conjonction_elim_droite(h))

    card_x = N.modus_ponens(cx, _card_de_card_t(vx))   # Card x = x
    card_z = N.modus_ponens(cz, _card_de_card_t(vz))   # Card z = z

    # Card(x⊔y) = x+y  est RÉFLEXIF (sum_xy == Card(x⊔y))
    refl_xy = N.reflexivite(sum_xy)                    # Card(x⊔y) = x+y
    refl_yz = N.reflexivite(sum_yz)                    # Card(y⊔z) = y+z

    # ── (A)  (x+y)+z = Card((x⊔y)⊔z) ───────────────────────────────────────────
    sdc_A = _sdc(xy, vz, sum_xy, vz)
    lhs = somme_cardinale_binaire(sum_xy, vz)          # (x+y)+z
    Card_xy_z = cardinal(somme_disjointe(xy, vz))
    eqA = N.modus_ponens(conjonction_intro(refl_xy, card_z), sdc_A)  # Card((x⊔y)⊔z) = (x+y)+z
    lhs_eq_card = N.modus_ponens(eqA, symetrie(Card_xy_z, lhs))      # (x+y)+z = Card((x⊔y)⊔z)

    # ── (B)  Card((x⊔y)⊔z) = Card(x⊔(y⊔z)) ─────────────────────────────────────
    assoc = _assoc_t(vx, vy, vz)                       # Card((x⊔y)⊔z) = Card(x⊔(y⊔z))

    # ── (C)  Card(x⊔(y⊔z)) = x+(y+z) ───────────────────────────────────────────
    sdc_C = _sdc(vx, yz, vx, sum_yz)
    rhs = somme_cardinale_binaire(vx, sum_yz)          # x+(y+z)
    Card_x_yz = cardinal(somme_disjointe(vx, yz))
    eqC = N.modus_ponens(conjonction_intro(card_x, refl_yz), sdc_C)  # Card(x⊔(y⊔z)) = x+(y+z)

    # ── ASSEMBLAGE ──────────────────────────────────────────────────────────────
    chain1 = composer_egalites(lhs_eq_card, assoc)     # (x+y)+z = Card(x⊔(y⊔z))
    final = composer_egalites(chain1, eqC)             # (x+y)+z = x+(y+z)
    out = N.loi_deduction(et(est_cardinal(vx), et(est_cardinal(vy), est_cardinal(vz))), final)
    cible = impl(et(est_cardinal(vx), et(est_cardinal(vy), est_cardinal(vz))),
                 egal(lhs, rhs))
    assert out.conclusion == cible, "_plus_assoc : conclusion inattendue"
    return out


def _plus_commute_t(x, y):
    """⊢ x+y = y+x  (INCONDITIONNEL : x+y := Card(x⊔y), commutativité = Card(x⊔y)=Card(y⊔x))."""
    vx, vy = _t(x), _t(y)
    gen = N.generalisation("Xcom3", N.generalisation("Ycom3",
          somme_cardinale_commutative("Xcom3", "Ycom3")))
    eq = instancie(instancie(gen, vx), vy)             # Card(x⊔y) = Card(y⊔x) = x+y = y+x
    cible = egal(somme_cardinale_binaire(vx, vy), somme_cardinale_binaire(vy, vx))
    assert eq.conclusion == cible, "_plus_commute_t : conclusion inattendue"
    return eq


def _rearrange_adc(a, d, c):
    """⊢ (est_cardinal a et est_cardinal d et est_cardinal c) ⇒ (a+d)+c = (a+c)+d.

    (a+d)+c = a+(d+c)   [_plus_assoc(a,d,c)]
            = a+(c+d)   [congruence sur a+·, _plus_commute(d,c)]
            = (a+c)+d   [_plus_assoc(a,c,d) symétrisé]."""
    va, vd, vc = _t(a), _t(d), _t(c)
    ante = et(est_cardinal(va), et(est_cardinal(vd), est_cardinal(vc)))
    h = N.assume(ante)
    ca = conjonction_elim_gauche(h)
    cd = conjonction_elim_gauche(conjonction_elim_droite(h))
    cc = conjonction_elim_droite(conjonction_elim_droite(h))

    # (a+d)+c = a+(d+c)
    assoc1 = N.modus_ponens(conjonction_intro(ca, conjonction_intro(cd, cc)),
                            _plus_assoc(va, vd, vc))    # (a+d)+c = a+(d+c)
    # a+(d+c) = a+(c+d)  via congruence_terme sur V=a+w, (d+c)=(c+d)
    commute_dc = _plus_commute_t(vd, vc)                # d+c = c+d
    V = somme_cardinale_binaire(va, var("wrac"))        # a + w
    cong = N.modus_ponens(commute_dc,
                          congruence_terme(somme_cardinale_binaire(vd, vc),
                                           somme_cardinale_binaire(vc, vd),
                                           V, w="wrac"))  # a+(d+c) = a+(c+d)
    chain1 = composer_egalites(assoc1, cong)            # (a+d)+c = a+(c+d)
    # a+(c+d) = (a+c)+d  : symétrie de _plus_assoc(a,c,d) : (a+c)+d = a+(c+d)
    assoc2 = N.modus_ponens(conjonction_intro(ca, conjonction_intro(cc, cd)),
                            _plus_assoc(va, vc, vd))    # (a+c)+d = a+(c+d)
    acd = somme_cardinale_binaire(somme_cardinale_binaire(va, vc), vd)  # (a+c)+d
    a_cd = somme_cardinale_binaire(va, somme_cardinale_binaire(vc, vd))  # a+(c+d)
    assoc2_sym = N.modus_ponens(assoc2, symetrie(acd, a_cd))   # a+(c+d) = (a+c)+d
    final = composer_egalites(chain1, assoc2_sym)       # (a+d)+c = (a+c)+d
    return N.loi_deduction(ante, final)


# ══════════════════════════════════════════════════════════════════════════════
#  briques term-safe : entier du produit / de la somme, Prop 7
# ══════════════════════════════════════════════════════════════════════════════
def _est_card_t(tx, name="xecu3"):
    """⊢ est_cardinal(Card X) pour X = terme  (card_est_un_cardinal instancié)."""
    return card_est_un_cardinal(_t(tx), name)


def _somme_binaire_entier_t(x, y):
    """⊢ (Fini x et Fini y) ⇒ Fini(x+y), version TERME (généralise+instancie)."""
    gen = N.generalisation("xsbe3", N.generalisation("ysbe3",
            somme_binaire_entier("xsbe3", "ysbe3")))
    return instancie(instancie(gen, _t(x)), _t(y))


def _produit_binaire_entier_t(x, y):
    """⊢ (Fini x et Fini y) ⇒ Fini(x·y), version TERME (généralise+instancie)."""
    gen = N.generalisation("xpbe3", N.generalisation("ypbe3",
            produit_binaire_entier("xpbe3", "ypbe3")))
    return instancie(instancie(gen, _t(x)), _t(y))


# ── prop2_strict_backward version TERME capture-safe ────────────────────────────
#   prop2_strict_backward(a,b,c) appelle en interne somme_zero_neutre_droite(a) et
#   somme_cardinale_commutative(a,·), NON capture-safe quand a/b sont des TERMES
#   composés (a+c, a·c).  On prouve sur 2 NOMS FRAIS « A2bw », « B2bw » puis on
#   généralise+instancie aux TERMES (la variable existentielle ename reste fixe).
_A2BW, _B2BW = "A2bw", "B2bw"


def _prop2_backward_t(tA, tB, ename):
    """⊢ (entier A et entier B) ⇒ ( ∃ename(entier ename, ename≠0, B=A+ename) ⇒ A<B ),
    pour TERMES A,B quelconques (capture-safe)."""
    g = prop2_strict_backward(_A2BW, _B2BW, ename)   # sur noms frais
    gen = N.generalisation(_A2BW, N.generalisation(_B2BW, g))
    return instancie(instancie(gen, _t(tA)), _t(tB))


# ══════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS
# ══════════════════════════════════════════════════════════════════════════════
def somme_strict_monotone_enonce(a="aP3", b="bP3", c="cP3"):
    va, vb, vc = _t(a), _t(b), _t(c)
    ac = somme_cardinale_binaire(va, vc)
    bc = somme_cardinale_binaire(vb, vc)
    return impl(et(est_entier(va), et(est_entier(vb),
                  et(est_entier(vc), inf_strict_card(va, vb)))),
                inf_strict_card(ac, bc))


def produit_strict_monotone_enonce(a="aP3", b="bP3", c="cP3"):
    va, vb, vc = _t(a), _t(b), _t(c)
    ac = produit_cardinal_binaire(va, vc)
    bc = produit_cardinal_binaire(vb, vc)
    return impl(et(est_entier(va), et(est_entier(vb),
                  et(est_entier(vc), et(non(egal(vc, ZERO)), inf_strict_card(va, vb))))),
                inf_strict_card(ac, bc))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 SOMME : a < b ⇒ a+c < b+c
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.2 Prop.3 | E III.36 L.39-46 | PDF p.139
def somme_strict_monotone(a="aP3", b="bP3", c="cP3", d="dP3"):
    """🎯 ⊢ ( est_entier a et est_entier b et est_entier c et a<b ) ⇒ a+c < b+c.   (CLOS.)

    PROPOSITION 3 §III.5.2, cas BINAIRE — somme."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dname = d if isinstance(d, str) else d.nom
    vd = var(dname)
    ad = somme_cardinale_binaire(va, vd)           # a+d
    ac = somme_cardinale_binaire(va, vc)           # a+c
    bc = somme_cardinale_binaire(vb, vc)           # b+c

    ante = et(est_entier(va), et(est_entier(vb),
              et(est_entier(vc), inf_strict_card(va, vb))))
    h = N.assume(ante)
    h_ent_a = conjonction_elim_gauche(h)
    h_ent_b = conjonction_elim_gauche(conjonction_elim_droite(h))
    h_ent_c = conjonction_elim_gauche(conjonction_elim_droite(conjonction_elim_droite(h)))
    h_lt = conjonction_elim_droite(conjonction_elim_droite(conjonction_elim_droite(h)))
    ca = conjonction_elim_gauche(h_ent_a)          # est_cardinal a
    cc = conjonction_elim_gauche(h_ent_c)          # est_cardinal c

    # Prop. 2 ⇒ : ∃d( entier d, d≠0, b=a+d )
    ab_ent = conjonction_intro(h_ent_a, h_ent_b)
    fwd = N.modus_ponens(ab_ent, prop2_strict_forward(a, b, d))   # (a<b) ⇒ rhs
    ex_d = N.modus_ponens(h_lt, fwd)                              # ∃d(...)

    # per-témoin d : entier d, d≠0, b=a+d  ⊢  a+c < b+c
    body = et(est_entier(vd), et(non(egal(vd, ZERO)), egal(vb, ad)))
    hbody = N.assume(body)
    h_ent_d = conjonction_elim_gauche(hbody)       # entier d
    h_rest = conjonction_elim_droite(hbody)
    h_d_ne0 = conjonction_elim_gauche(h_rest)      # d ≠ 0
    h_b_eq_ad = conjonction_elim_droite(h_rest)    # b = a+d
    cd = conjonction_elim_gauche(h_ent_d)          # est_cardinal d

    # b+c = (a+d)+c   (congruence sur w+c, à partir de b=a+d)
    Vbc = somme_cardinale_binaire(var("wsbc"), vc)     # w + c
    bc_eq_adc = N.modus_ponens(h_b_eq_ad,
                   congruence_terme(vb, ad, Vbc, w="wsbc"))   # b+c = (a+d)+c
    # (a+d)+c = (a+c)+d
    rear = N.modus_ponens(conjonction_intro(ca, conjonction_intro(cd, cc)),
                          _rearrange_adc(va, vd, vc))         # (a+d)+c = (a+c)+d
    bc_eq_acd = composer_egalites(bc_eq_adc, rear)            # b+c = (a+c)+d

    # entiers : a+c, b+c
    ent_ac = N.modus_ponens(conjonction_intro(h_ent_a, h_ent_c), _somme_binaire_entier_t(va, vc))  # Fini(a+c)
    ent_bc = N.modus_ponens(conjonction_intro(h_ent_b, h_ent_c), _somme_binaire_entier_t(vb, vc))  # Fini(b+c)

    # Prop. 2 ⇐ sur (a+c, b+c), témoin d : ( ∃e( entier e, e≠0, b+c=(a+c)+e ) ) ⇒ (a+c < b+c)
    bwd = N.modus_ponens(conjonction_intro(ent_ac, ent_bc),
                         _prop2_backward_t(ac, bc, d))       # rhs(ac,bc,d) ⇒ (a+c<b+c)
    # construire le témoin d pour rhs(ac, bc, d) : entier d et d≠0 et b+c=(a+c)+d
    body_tgt = et(est_entier(vd), et(non(egal(vd, ZERO)), egal(bc, somme_cardinale_binaire(ac, vd))))
    conj = conjonction_intro(h_ent_d, conjonction_intro(h_d_ne0, bc_eq_acd))
    assert conj.conclusion == body_tgt, "somme : corps témoin mal formé"
    rhs_acbc = _rhs(ac, bc, d)
    ex_tgt = N.modus_ponens(conj, N.s5(body_tgt, vd, dname))   # rhs(ac,bc,d)
    lt = N.modus_ponens(ex_tgt, bwd)                          # a+c < b+c

    imp_body = N.loi_deduction(body, lt)                      # body ⇒ (a+c<b+c)
    res = N.modus_ponens(ex_d, existe_elimination(imp_body, dname))   # a+c < b+c
    out = N.loi_deduction(ante, res)
    assert out.conclusion == somme_strict_monotone_enonce(a, b, c), \
        "somme_strict_monotone : conclusion ≠ énoncé attendu"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 PRODUIT : (c≠0 et a<b) ⇒ a·c < b·c
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.2 Prop.3 | E III.36 L.39-46 | PDF p.139
def produit_strict_monotone(a="aP3", b="bP3", c="cP3", d="dP3"):
    """🎯 ⊢ ( est_entier a et est_entier b et est_entier c et c≠0 et a<b ) ⇒ a·c < b·c.  (CLOS.)

    PROPOSITION 3 §III.5.2, cas BINAIRE — produit."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dname = d if isinstance(d, str) else d.nom
    vd = var(dname)
    ad = somme_cardinale_binaire(va, vd)           # a+d
    ac = produit_cardinal_binaire(va, vc)          # a·c = Card(a×c)
    bc = produit_cardinal_binaire(vb, vc)          # b·c = Card(b×c)
    dc = produit_cardinal_binaire(vd, vc)          # d·c = Card(d×c)

    ante = et(est_entier(va), et(est_entier(vb),
              et(est_entier(vc), et(non(egal(vc, ZERO)), inf_strict_card(va, vb)))))
    h = N.assume(ante)
    h_ent_a = conjonction_elim_gauche(h)
    h_ent_b = conjonction_elim_gauche(conjonction_elim_droite(h))
    r2 = conjonction_elim_droite(conjonction_elim_droite(h))
    h_ent_c = conjonction_elim_gauche(r2)
    r3 = conjonction_elim_droite(r2)
    h_c_ne0 = conjonction_elim_gauche(r3)          # c ≠ 0
    h_lt = conjonction_elim_droite(r3)             # a < b

    # Prop. 2 ⇒ : ∃d( entier d, d≠0, b=a+d )
    ab_ent = conjonction_intro(h_ent_a, h_ent_b)
    fwd = N.modus_ponens(ab_ent, prop2_strict_forward(a, b, d))
    ex_d = N.modus_ponens(h_lt, fwd)

    body = et(est_entier(vd), et(non(egal(vd, ZERO)), egal(vb, ad)))
    hbody = N.assume(body)
    h_ent_d = conjonction_elim_gauche(hbody)
    h_rest = conjonction_elim_droite(hbody)
    h_d_ne0 = conjonction_elim_gauche(h_rest)      # d ≠ 0
    h_b_eq_ad = conjonction_elim_droite(h_rest)    # b = a+d

    # b·c = (a+d)·c   (congruence sur w·c, à partir de b=a+d)
    Vbc = produit_cardinal_binaire(var("wpbc"), vc)    # w · c
    bc_eq_adc = N.modus_ponens(h_b_eq_ad,
                   congruence_terme(vb, ad, Vbc, w="wpbc"))   # b·c = (a+d)·c

    # (a+d)·c = a·c + d·c   via distributivité cardinale.
    #   distributivite_cardinale(c, a, d) : Card(c×(a⊔d)) = Card((c×a)⊔(c×d)).
    # On veut plutôt la forme (a⊔d)×c.  On utilise distributivite_cardinale avec
    #   (a+d)·c = Card((a+d)×c) ; (a+d) = Card(a⊔d) (déf de +) → réécriture difficile.
    # Route directe : on prouve l'égalité (a+d)·c = a·c + d·c à part (voir helper).
    distrib = _distrib_droite(va, vd, vc, conjonction_elim_gauche(h_ent_a),
                              conjonction_elim_gauche(h_ent_d),
                              conjonction_elim_gauche(h_ent_c))   # (a+d)·c = a·c + d·c
    bc_eq_acdc = composer_egalites(bc_eq_adc, distrib)            # b·c = a·c + (d·c)

    # d·c ≠ 0  via Prop. 7 (d≠0 et c≠0 ⇒ d·c≠0)
    # prop7_produit_non_nul(d,c) : ¬(Card(d×c)=Card∅) ⟺ (¬(Card d=Card∅) et ¬(Card c=Card∅))
    _p7g = N.generalisation("Ap7m", N.generalisation("Bp7m",
            prop7_produit_non_nul("Ap7m", "Bp7m")))
    p7 = instancie(instancie(_p7g, vd), vc)
    # ¬(Card d=Card∅) = (d≠0) ; ¬(Card c=Card∅) = (c≠0)  — d, c sont des cardinaux.
    cd = conjonction_elim_gauche(h_ent_d)          # est_cardinal d
    cc = conjonction_elim_gauche(h_ent_c)          # est_cardinal c
    # Card d = d, Card c = c → réécrire d≠0,c≠0 en ¬(Card d=Card∅),¬(Card c=Card∅)
    d_ne0_card = _ne0_vers_card(vd, h_d_ne0, cd)   # ¬(Card d = Card∅)
    c_ne0_card = _ne0_vers_card(vc, h_c_ne0, cc)   # ¬(Card c = Card∅)
    dc_ne0_card = N.modus_ponens(conjonction_intro(d_ne0_card, c_ne0_card),
                                 equivalence_arriere(p7))   # ¬(Card(d×c)=Card∅)
    dc_ne0 = _card_ne0_vers_dc(vd, vc, dc_ne0_card)   # d·c ≠ 0  (= ¬(Card(d×c)=ZERO))

    # entiers : a·c, b·c, d·c
    ent_ac = N.modus_ponens(conjonction_intro(h_ent_a, h_ent_c), _produit_binaire_entier_t(va, vc))
    ent_bc = N.modus_ponens(conjonction_intro(h_ent_b, h_ent_c), _produit_binaire_entier_t(vb, vc))
    ent_dc = N.modus_ponens(conjonction_intro(h_ent_d, h_ent_c), _produit_binaire_entier_t(vd, vc))

    # Prop. 2 ⇐ sur (a·c, b·c), variable existentielle FRAÎCHE ename, témoin = TERME d·c.
    ename = _fresh_dc_name(dc)                                # "edc3"  (binder frais)
    ve = var(ename)
    bwd = N.modus_ponens(conjonction_intro(ent_ac, ent_bc),
                         _prop2_backward_t(ac, bc, ename))   # _rhs(ac,bc,ename) ⇒ (a·c<b·c)
    # corps du ∃ instancié au témoin dc : entier dc et dc≠0 et b·c = a·c + dc
    body_tgt = et(est_entier(dc), et(non(egal(dc, ZERO)), egal(bc, somme_cardinale_binaire(ac, dc))))
    # corps GÉNÉRIQUE (en ename) attendu par _rhs(ac,bc,ename)
    body_gen = et(est_entier(ve), et(non(egal(ve, ZERO)), egal(bc, somme_cardinale_binaire(ac, ve))))
    conj = conjonction_intro(ent_dc, conjonction_intro(dc_ne0, bc_eq_acdc))
    assert conj.conclusion == body_tgt, "produit : corps témoin mal formé"
    ex_tgt = N.modus_ponens(conj, N.s5(body_gen, dc, ename))   # _rhs(ac,bc,ename)
    lt = N.modus_ponens(ex_tgt, bwd)                          # a·c < b·c

    imp_body = N.loi_deduction(body, lt)
    res = N.modus_ponens(ex_d, existe_elimination(imp_body, dname))
    out = N.loi_deduction(ante, res)
    assert out.conclusion == produit_strict_monotone_enonce(a, b, c), \
        "produit_strict_monotone : conclusion ≠ énoncé attendu"
    return out


# ── helpers produit ────────────────────────────────────────────────────────────
def _fresh_dc_name(dc_term):
    """nom de variable frais pour le ∃ (le terme d·c n'est pas une variable)."""
    return "edc3"


def _ne0_vers_card(x, x_ne0, hcard_x):
    """De ¬(x = 0) [= ¬(x = ZERO) = ¬(x = Card∅)] et est_cardinal(x), déduit
    ¬(Card x = Card∅).  (Card x = x ; réécriture du membre gauche.)

    ZERO == Card∅ (déf).  x_ne0 : ¬(x = Card∅).  On veut ¬(Card x = Card∅)."""
    vx = _t(x)
    card_x = N.modus_ponens(hcard_x, _card_de_card_t(vx))   # Card x = x
    # ¬(x=Card∅)  ⇒  ¬(Card x = Card∅)  via congruence : remplacer x par Card x
    #   on a Card x = x ; cible : (Card x = Card∅) ⇒ (x = Card∅) puis contraposée.
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
    cardvide = cardinal(E.VIDE)
    # (Card x = x) ⇒ ( (Card x = Card∅) ⇒ (x = Card∅) ) : congruence_terme sur w=Card∅ ? non.
    # Plus simple : V{w} := (w = Card∅) ; congruence_terme(Card x, x, ?) ne donne pas une impl.
    # On utilise S6 : (Card x = x) ⇒ ((Card x = Card∅) ⇔ (x = Card∅)).
    w = "wnv3"
    R = egal(var(w), cardvide)                              # (Card x|w)R=(Card x=Card∅), (x|w)R=(x=Card∅)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_avant
    eq = N.modus_ponens(card_x, N.s6(cardinal(vx), vx, w, R))   # (Card x=Card∅) ⇔ (x=Card∅)
    imp = equivalence_avant(eq)                             # (Card x=Card∅) ⇒ (x=Card∅)
    # contraposée : ¬(x=Card∅) ⇒ ¬(Card x=Card∅)
    return N.modus_ponens(x_ne0, contraposition(imp))


def _card_ne0_vers_dc(d, c, card_ne0):
    """De ¬(Card(d×c) = Card∅), déduit d·c ≠ 0  (= ¬(Card(d×c) = ZERO)).

    d·c := Card(d×c) (déf produit_cardinal_binaire), ZERO == Card∅ (déf).  IDENTIQUE."""
    vd, vc = _t(d), _t(c)
    cible = non(egal(produit_cardinal_binaire(vd, vc), ZERO))
    assert card_ne0.conclusion == cible, \
        "_card_ne0_vers_dc : d·c≠0 non identique à ¬(Card(d×c)=Card∅)"
    return card_ne0


def _distrib_droite(a, d, c, ca, cd, cc):
    """⊢ (a+d)·c = a·c + d·c   sous est_cardinal(a),est_cardinal(d),est_cardinal(c) [preuves ca,cd,cc].

    distributivite_cardinale(c, a, d) : Card(c×(a⊔d)) = Card((c×a)⊔(c×d))  [c·(a+d)=c·a+c·d].
    On passe à la forme DROITE par commutativité du produit cardinal :
        (a+d)·c = c·(a+d)              [produit_cardinal_commutatif]
                = c·a + c·d            [distributivité, via pont sdc Card↦+]
                = a·c + d·c            [commutativité produit × 2, commutativité somme]
    On expose plutôt la chaîne au niveau des CARDINAUX, pont sdc."""
    va, vd, vc = _t(a), _t(d), _t(c)
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_commutatif,
    )

    def _comm_t(tx, ty):
        g = produit_cardinal_commutatif("Xcmp3", "Ycmp3")
        gen = N.generalisation("Xcmp3", N.generalisation("Ycmp3", g))
        return instancie(instancie(gen, _t(tx)), _t(ty))

    def _dist_t(tx, ty, tz):
        g = distributivite_cardinale("Xdst3", "Ydst3", "Zdst3")
        gen = N.generalisation("Xdst3", N.generalisation("Ydst3",
              N.generalisation("Zdst3", g)))
        return instancie(instancie(instancie(gen, _t(tx)), _t(ty)), _t(tz))

    ad = somme_cardinale_binaire(va, vd)           # a+d = Card(a⊔d)
    # (a+d)·c = Card((a+d)×c)   (déf) ; (a+d)×c avec (a+d)=Card(a⊔d).
    # distributivite_cardinale(c, a, d) :
    #   Card(c×(a⊔d)) = Card((c×a)⊔(c×d))
    dist = _dist_t(vc, va, vd)    # Card(c×(a⊔d)) = Card((c×a)⊔(c×d))
    c_ad = E.produit(vc, somme_disjointe(va, vd))  # c×(a⊔d)
    ca_set = E.produit(vc, va)                     # c×a
    cd_set = E.produit(vc, vd)                     # c×d
    # (1) Card((c×a)⊔(c×d)) = Card(c×a) + Card(c×d)   via _sdc, réflexifs
    refl_ca = N.reflexivite(cardinal(ca_set))
    refl_cd = N.reflexivite(cardinal(cd_set))
    sdc1 = _sdc(ca_set, cd_set, cardinal(ca_set), cardinal(cd_set))
    Card_union = cardinal(somme_disjointe(ca_set, cd_set))
    eq1 = N.modus_ponens(conjonction_intro(refl_ca, refl_cd), sdc1)   # Card((c×a)⊔(c×d)) = Card(c×a)+Card(c×d)
    # chaîne : Card(c×(a⊔d)) = Card(c×a)+Card(c×d)
    lhs_dist = composer_egalites(dist, eq1)        # Card(c×(a⊔d)) = c·a + c·d  [Card(c×a)=c·a déf]

    # (2) (a+d)·c = Card(c×(a⊔d))
    #   (a+d)·c = Card((a+d)×c) = Card(c×(a+d))  [commut produit]  ; (a+d)=Card(a⊔d).
    #   On veut Card(c×(a⊔d)).  Or (a+d) = Card(a⊔d), donc c×(a+d) ≠ c×(a⊔d) littéralement.
    #   Pont : invariance — trop coûteux.  Alternative : prouver (a+d)·c = c·(a+d) [commut],
    #   puis c·(a+d) = Card(c×(a⊔d)) exige a+d=Card(a⊔d) DANS le produit → réécriture par
    #   congruence_terme avec l'égalité (a+d)=Card(a⊔d) [RÉFLEXIVE !].
    adc = produit_cardinal_binaire(ad, vc)         # (a+d)·c = Card((a+d)×c)
    comm1 = _comm_t(ad, vc)    # Card((a+d)×c) = Card(c×(a+d))   [c×(a+d) = c×Card(a⊔d)]
    # PONT D'INVARIANCE : Card(c×(a+d)) = Card(c×(a⊔d)).  (a+d) = Card(a⊔d) est un
    #   CARDINAL, ≠ le SET (a⊔d) ; produit_cardinal_bien_defini(c, a⊔d, c, a+d) sous
    #   (Card c=c et Card(a⊔d)=a+d réflexif) donne Card(c×(a⊔d)) = c·(a+d) = Card(c×(a+d)).
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import _pcbd_t
    a_disj_d = somme_disjointe(va, vd)             # a⊔d  (SET)
    card_c = N.modus_ponens(cc, _card_de_card_t(vc))   # Card c = c
    refl_ad = N.reflexivite(ad)                    # Card(a⊔d) = a+d  (ad == Card(a⊔d))
    bd = _pcbd_t(vc, a_disj_d, vc, ad)             # (Card c=c et Card(a⊔d)=a+d) ⇒ Card(c×(a⊔d))=c·(a+d)
    c_times_ad_card = produit_cardinal_binaire(vc, ad)   # c·(a+d) = Card(c×(a+d))
    eq_cad = N.modus_ponens(conjonction_intro(card_c, refl_ad), bd)  # Card(c×(a⊔d)) = Card(c×(a+d))
    Card_c_disj = cardinal(E.produit(vc, a_disj_d))
    eq_cad_sym = N.modus_ponens(eq_cad, symetrie(Card_c_disj, c_times_ad_card))  # Card(c×(a+d)) = Card(c×(a⊔d))
    chain_pont = composer_egalites(comm1, eq_cad_sym)   # Card((a+d)×c) = Card(c×(a⊔d))
    chain_left = composer_egalites(chain_pont, lhs_dist)   # Card((a+d)×c) = c·a + c·d
    # (3) c·a = a·c, c·d = d·c  (commut produit) puis a·c + d·c
    comm_ca = _comm_t(vc, va)  # Card(c×a) = Card(a×c)  = c·a = a·c
    comm_cd = _comm_t(vc, vd)  # Card(c×d) = Card(d×c)  = c·d = d·c
    # c·a + c·d = a·c + d·c : congruence sur les deux arguments de +
    ca_card = produit_cardinal_binaire(vc, va)     # c·a
    cd_card = produit_cardinal_binaire(vc, vd)     # c·d
    acard = produit_cardinal_binaire(va, vc)       # a·c
    dcard = produit_cardinal_binaire(vd, vc)       # d·c
    # remplacer c·a -> a·c dans (w + c·d)
    Vleft = somme_cardinale_binaire(var("wdl3"), cd_card)
    step_a = N.modus_ponens(comm_ca, congruence_terme(ca_card, acard, Vleft, w="wdl3"))  # c·a+c·d = a·c+c·d
    # remplacer c·d -> d·c dans (a·c + w)
    Vright = somme_cardinale_binaire(acard, var("wdr3"))
    step_d = N.modus_ponens(comm_cd, congruence_terme(cd_card, dcard, Vright, w="wdr3"))  # a·c+c·d = a·c+d·c
    cacd_eq = composer_egalites(step_a, step_d)    # c·a+c·d = a·c+d·c
    final = composer_egalites(chain_left, cacd_eq) # Card((a+d)×c) = a·c+d·c, i.e. (a+d)·c = a·c+d·c
    return final


__all__ = [
    "somme_strict_monotone", "somme_strict_monotone_enonce",
    "produit_strict_monotone", "produit_strict_monotone_enonce",
]
