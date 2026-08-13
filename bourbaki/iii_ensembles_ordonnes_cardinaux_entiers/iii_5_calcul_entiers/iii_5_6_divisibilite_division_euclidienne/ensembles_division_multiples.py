# -*- coding: utf-8 -*-
"""§III.5.6 — STABILITÉ DES MULTIPLES (E III.39, alinéa après la Déf. 1).  CLOS.

Bourbaki (E III.39 L.27-31, PDF p.142, vérifié en PNG) :
  « Tout multiple a′ d'un multiple a de b est multiple de b » (L.27-28) ;
  « si c et d sont des multiples de b, c + d, et c − d (lorsque d ≤ c) sont des
    multiples de b » (L.29-31).

THÉORÈMES PROUVÉS (CLOS, 0 hypothèse ; theorie_ensembles INCHANGÉE = 22) :

  • `multiple_de_multiple`  ⊢ (a′ multiple de a  et  a multiple de b) ⇒ a′ multiple de b.
        Témoin : a′ = a·q₂ = (b·q₁)·q₂ = b·(q₁·q₂)  (associativité du produit
        cardinal) ; Fini(q₁·q₂) par la Prop. 1 §III.5.1 (produit_binaire_entier).

  • `somme_multiples`       ⊢ (c multiple de b  et  d multiple de b) ⇒ (c+d) multiple de b.
        Témoin : c+d = b·q₁ + b·q₂ = b·(q₁+q₂)  (distributivité du produit sur la
        somme) ; Fini(q₁+q₂) par la Prop. 1 §III.5.1 (somme_binaire_entier).

Le prédicat est CELUI de la Déf. 1 (`est_multiple_cardinal`/`divise_cardinal`,
liant ∃ « qd », arithmétique cardinale RÉELLE a·q = Card(a×q)).  Chaîne de calcul au
niveau Card (motif exact de `ensembles_division_successeur`) : congruence (réécriture
des hypothèses a=b·q dans le terme), bien-définition/invariance (Eq(Card X, X) pour
dénicher les Card imbriqués), loi structurale au niveau ensembles (associativité resp.
distributivité), ré-encapsulation Card.  Les lemmes ∀-clos sont instanciés par
`_wrap4` (noms symboliques « Xw »… puis instancie — collision « q » de la machinerie
produit évitée, piège documenté).  Les DEUX hypothèses existentielles (∃qd) sont
consommées par élimination sur points EXOTIQUES qm1/qm2 puis recollées au liant du
livre par α-pont (`alpha_existe`).

RESTE (hors périmètre, honnête) : le cas c − d (exige la soustraction, Cor. 4
§III.5.2 non construit) ; les identités de quotients a′/b = (a′/a)(a/b) et
(c±d)/b = c/b ± d/b ; l'équivalence « a = bq ⇔ q = a/b » (exigent l'unicité τ du
quotient : chantier quotient_cardinal).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    _prop1_direct_tt)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.equipotence_retrait.ensembles_equipotence_retrait import (
    equipotence_reflexive_pour)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_associatif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_cardinale import (
    distributivite_cardinale)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    somme_cardinale_bien_definie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_binaire_entier)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_binaire_entier)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_definitions import (
    divise_cardinal, est_multiple_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_successeur import (
    _wrap4, _esc_t, _sym_eq)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _corps_divise(vb, va, q):
    """Corps du ∃ de divise_cardinal(b, a) écrit au nom q : Fini(q) et a = b·q."""
    return et(est_fini(var(q)), egal(va, produit_cardinal_binaire(vb, var(q))))


def _eq_refl(t):
    """⊢ Eq(T, T)  (réflexivité de l'équipotence, version terme)."""
    return equipotence_reflexive_pour(_t(t))


def _fermeture_existentielle(Cn, B1, B2, corps1_qd, corps2_qd):
    """Décharge les deux corps existentiels B1 (var qm1), B2 (var qm2) de Cn et
    recolle chacun au liant « qd » du livre (α-pont) :

        {B1, B2} ⊢ C   ⟼   ⊢ (∃qd)corps1 ⇒ ((∃qd)corps2 ⇒ C).
    """
    i2 = existe_elimination(N.loi_deduction(B2, Cn), "qm2")     # (∃qm2)B2 ⇒ C   [B1]
    a2 = alpha_existe("qd", "qm2", corps2_qd)                   # (∃qd)c2 ⇔ (∃qm2)B2
    i2b = syllogisme(equivalence_avant(a2), i2)                 # (∃qd)c2 ⇒ C    [B1]
    i1 = existe_elimination(N.loi_deduction(B1, i2b), "qm1")    # (∃qm1)B1 ⇒ ((∃qd)c2 ⇒ C)
    a1 = alpha_existe("qd", "qm1", corps1_qd)
    return syllogisme(equivalence_avant(a1), i1)                # (∃qd)c1 ⇒ ((∃qd)c2 ⇒ C)


def _forme_conjonctive(imp_curry, ante_g, ante_d):
    """⊢ A ⇒ (B ⇒ C)  ⟼  ⊢ (A et B) ⇒ C   (forme conjonctive du livre)."""
    ante = et(ante_g, ante_d)
    h = N.assume(ante)
    c = N.modus_ponens(conjonction_elim_droite(h),
                       N.modus_ponens(conjonction_elim_gauche(h), imp_curry))
    return N.loi_deduction(ante, c)


# ── Cibles (reconstruction des conclusions attendues, pour vérification ==) ────
def multiple_de_multiple_cible(ap="ap", a="a", b="b"):
    """(a′ multiple de a  et  a multiple de b) ⇒ a′ multiple de b."""
    vap, va, vb = _t(ap), _t(a), _t(b)
    return impl(et(est_multiple_cardinal(vap, va), est_multiple_cardinal(va, vb)),
                est_multiple_cardinal(vap, vb))


def somme_multiples_cible(c="c", d="d", b="b"):
    """(c multiple de b  et  d multiple de b) ⇒ (c+d) multiple de b."""
    vc, vd, vb = _t(c), _t(d), _t(b)
    return impl(et(est_multiple_cardinal(vc, vb), est_multiple_cardinal(vd, vb)),
                est_multiple_cardinal(somme_cardinale_binaire(vc, vd), vb))


# ═══════════════════════════════════════════════════════════════════════════════
# 1.  « Tout multiple a′ d'un multiple a de b est multiple de b »
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.6 Prop.- | E III.39 L.27-28 | PDF p.142
def multiple_de_multiple(ap="ap", a="a", b="b"):
    """🎯 ⊢ (a′ multiple de a  et  a multiple de b) ⇒ a′ multiple de b.   (CLOS.)

    Sous les corps existentiels (points exotiques qm1, qm2) : a = b·q₁, a′ = a·q₂.
    Chaîne :  a′ = Card(a×q₂)               [hyp]
                 = Card((b·q₁)×q₂)          [congruence : réécrit a]
                 = Card((b×q₁)×q₂)          [invariance : Eq(b·q₁, b×q₁)]
                 = Card(b×(q₁×q₂))          [associativité du produit, niveau ensembles]
                 = Card(b×(q₁·q₂)) = b·(q₁·q₂)   [invariance : Eq(q₁×q₂, q₁·q₂)].
    Témoin q₁·q₂, fini par produit_binaire_entier (Prop. 1 §III.5.1).  Rien postulé."""
    vap, va, vb = _t(ap), _t(a), _t(b)
    vq1, vq2 = var("qm1"), var("qm2")
    P1 = produit_cardinal_binaire(vb, vq1)          # b·q₁ = Card(b×q₁)
    W = produit_cardinal_binaire(vq1, vq2)          # q₁·q₂ = Card(q₁×q₂), le témoin
    BQ1 = E.produit(vb, vq1)
    Q12 = E.produit(vq1, vq2)

    B1 = _corps_divise(vb, va, "qm1")               # Fini q₁ et a = b·q₁
    B2 = _corps_divise(va, vap, "qm2")              # Fini q₂ et a′ = a·q₂
    h1, h2 = N.assume(B1), N.assume(B2)
    f1, e1 = conjonction_elim_gauche(h1), conjonction_elim_droite(h1)
    f2, e2 = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)

    # (0) a′ = Card(a×q₂) = Card((b·q₁)×q₂)   (réécriture de a par e1, trou « wdm »)
    V0 = cardinal(E.produit(var("wdm"), vq2))
    c0 = N.modus_ponens(e1, congruence_terme(va, P1, V0, "wdm"))
    ch = composer_egalites(e2, c0)                  # a′ = Card(P1×q₂)

    # (1) Card(P1×q₂) = Card((b×q₁)×q₂)   (invariance ; Eq(P1, b×q₁), Eq(q₂,q₂))
    inv_v = eq_produit_invariant("F", "G", "Xw", "Yw", "X1w", "Y1w")
    conj1 = conjonction_intro(_sym_eq(_esc_t(BQ1), BQ1, P1), _eq_refl(vq2))
    inv1 = N.modus_ponens(conj1, _wrap4(inv_v, ["Xw", "Yw", "X1w", "Y1w"],
                                        [P1, vq2, BQ1, vq2]))
    c1 = N.modus_ponens(inv1, _prop1_direct_tt(E.produit(P1, vq2), E.produit(BQ1, vq2)))

    # (2) Card((b×q₁)×q₂) = Card(b×(q₁×q₂))   (associativité, niveau ensembles)
    c2 = _wrap4(produit_cardinal_associatif("Xw", "Yw", "Zw"), ["Xw", "Yw", "Zw"],
                [vb, vq1, vq2])

    # (3) Card(b×(q₁×q₂)) = Card(b×(q₁·q₂)) = b·(q₁·q₂)   (invariance ; Eq(q₁×q₂, W))
    conj3 = conjonction_intro(_eq_refl(vb), _esc_t(Q12))
    inv3 = N.modus_ponens(conj3, _wrap4(inv_v, ["Xw", "Yw", "X1w", "Y1w"],
                                        [vb, Q12, vb, W]))
    c3 = N.modus_ponens(inv3, _prop1_direct_tt(E.produit(vb, Q12), E.produit(vb, W)))

    chaine = composer_egalites(composer_egalites(composer_egalites(ch, c1), c2), c3)
    # chaine : a′ = b·(q₁·q₂)   [B1, B2]

    # Fini(q₁·q₂)  (Prop. 1 §III.5.1, cas binaire produit)
    fin_v = _wrap4(produit_binaire_entier("Xw", "Yw"), ["Xw", "Yw"], [vq1, vq2])
    fW = N.modus_ponens(conjonction_intro(f1, f2), fin_v)       # Fini W   [B1, B2]

    # ∃-intro au liant du livre « qd » : divise_cardinal(b, a′)
    corps = _corps_divise(vb, vap, "qd")
    temoin = conjonction_intro(fW, chaine)                      # Fini W et a′ = b·W
    assert temoin.conclusion == subst_f(W, "qd", corps), "témoin ≠ (W|qd)corps"
    Cn = N.modus_ponens(temoin, N.s5(corps, W, "qd"))           # b | a′   [B1, B2]
    assert Cn.conclusion == est_multiple_cardinal(vap, vb), "∃-intro : cible"

    curry = _fermeture_existentielle(Cn, B1, B2,
                                     _corps_divise(vb, va, "qd"),
                                     _corps_divise(va, vap, "qd"))
    # curry : (a multiple de b) ⇒ ((a′ multiple de a) ⇒ (a′ multiple de b)), clos ;
    # l'ordre du livre (« multiple d'un multiple ») met a′|a en tête : on échange.
    res = _forme_conjonctive(_swap_curry(curry),
                             est_multiple_cardinal(vap, va),
                             est_multiple_cardinal(va, vb))
    assert res.conclusion == multiple_de_multiple_cible(vap, va, vb), "conclusion inattendue"
    assert res.est_clos, "multiple_de_multiple : non clos"
    return res


def _swap_curry(imp_curry):
    """⊢ A ⇒ (B ⇒ C)  ⟼  ⊢ B ⇒ (A ⇒ C)   (échange des deux antécédents)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
    a, bc = antecedent_consequent(imp_curry.conclusion)
    b, _ = antecedent_consequent(bc)
    ha, hb = N.assume(a), N.assume(b)
    c = N.modus_ponens(hb, N.modus_ponens(ha, imp_curry))
    return N.loi_deduction(b, N.loi_deduction(a, c))


# ═══════════════════════════════════════════════════════════════════════════════
# 2.  « Si c et d sont des multiples de b, c + d est multiple de b »
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.6 Prop.- | E III.39 L.29-31 | PDF p.142
def somme_multiples(c="c", d="d", b="b"):
    """🎯 ⊢ (c multiple de b  et  d multiple de b) ⇒ (c+d) multiple de b.   (CLOS.)

    Sous les corps existentiels (points exotiques qm1, qm2) : c = b·q₁, d = b·q₂.
    Chaîne :  c+d = Card(c⊔d) = Card((b·q₁)⊔(b·q₂))   [congruence ×2 : réécrit c puis d]
                  = Card((b×q₁)⊔(b×q₂))               [bien-définition de la somme]
                  = Card(b×(q₁⊔q₂))                   [distributivité, symétrisée]
                  = Card(b×(q₁+q₂)) = b·(q₁+q₂)       [invariance : Eq(q₁⊔q₂, q₁+q₂)].
    Témoin q₁+q₂, fini par somme_binaire_entier (Prop. 1 §III.5.1).  Rien postulé.
    (Le cas c−d du livre exige la soustraction : REPORTÉ, cf. docstring module.)"""
    vc, vd, vb = _t(c), _t(d), _t(b)
    vq1, vq2 = var("qm1"), var("qm2")
    P1 = produit_cardinal_binaire(vb, vq1)          # b·q₁
    P2 = produit_cardinal_binaire(vb, vq2)          # b·q₂
    W = somme_cardinale_binaire(vq1, vq2)           # q₁+q₂ = Card(q₁⊔q₂), le témoin
    BQ1, BQ2 = E.produit(vb, vq1), E.produit(vb, vq2)
    S = somme_disjointe(vq1, vq2)

    B1 = _corps_divise(vb, vc, "qm1")               # Fini q₁ et c = b·q₁
    B2 = _corps_divise(vb, vd, "qm2")               # Fini q₂ et d = b·q₂
    h1, h2 = N.assume(B1), N.assume(B2)
    f1, e1 = conjonction_elim_gauche(h1), conjonction_elim_droite(h1)
    f2, e2 = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)

    # (0) c+d = Card(c⊔d) = Card((b·q₁)⊔d) = Card((b·q₁)⊔(b·q₂))   (congruence ×2)
    V1 = cardinal(somme_disjointe(var("wdm"), vd))
    c0a = N.modus_ponens(e1, congruence_terme(vc, P1, V1, "wdm"))
    V2 = cardinal(somme_disjointe(P1, var("wdm")))
    c0b = N.modus_ponens(e2, congruence_terme(vd, P2, V2, "wdm"))
    c0 = composer_egalites(c0a, c0b)                # Card(c⊔d) = Card(P1⊔P2)

    # (1) Card(P1⊔P2) = Card((b×q₁)⊔(b×q₂))   (bien-définition ; Eq(P1,b×q₁), Eq(P2,b×q₂))
    conj1 = conjonction_intro(_sym_eq(_esc_t(BQ1), BQ1, P1),
                              _sym_eq(_esc_t(BQ2), BQ2, P2))
    bd_v = somme_cardinale_bien_definie("Aw", "Bw", "A1w", "B1w")
    c1 = N.modus_ponens(conj1, _wrap4(bd_v, ["Aw", "Bw", "A1w", "B1w"],
                                      [P1, P2, BQ1, BQ2]))

    # (2) Card((b×q₁)⊔(b×q₂)) = Card(b×(q₁⊔q₂))   (distributivité, symétrisée)
    dist = _wrap4(distributivite_cardinale("Aw", "Bw", "Cw"), ["Aw", "Bw", "Cw"],
                  [vb, vq1, vq2])                   # Card(b×(q₁⊔q₂)) = Card((b×q₁)⊔(b×q₂))
    c2 = N.modus_ponens(dist, symetrie(cardinal(E.produit(vb, S)),
                                       cardinal(somme_disjointe(BQ1, BQ2))))

    # (3) Card(b×(q₁⊔q₂)) = Card(b×(q₁+q₂)) = b·(q₁+q₂)   (invariance ; Eq(q₁⊔q₂, W))
    inv_v = eq_produit_invariant("F", "G", "Xw", "Yw", "X1w", "Y1w")
    conj3 = conjonction_intro(_eq_refl(vb), _esc_t(S))
    inv3 = N.modus_ponens(conj3, _wrap4(inv_v, ["Xw", "Yw", "X1w", "Y1w"],
                                        [vb, S, vb, W]))
    c3 = N.modus_ponens(inv3, _prop1_direct_tt(E.produit(vb, S), E.produit(vb, W)))

    chaine = composer_egalites(composer_egalites(composer_egalites(c0, c1), c2), c3)
    # chaine : c+d = b·(q₁+q₂)   [B1, B2]

    # Fini(q₁+q₂)  (Prop. 1 §III.5.1, cas binaire somme)
    fin_v = _wrap4(somme_binaire_entier("Xw", "Yw"), ["Xw", "Yw"], [vq1, vq2])
    fW = N.modus_ponens(conjonction_intro(f1, f2), fin_v)       # Fini W   [B1, B2]

    # ∃-intro au liant du livre « qd » : divise_cardinal(b, c+d)
    corps = _corps_divise(vb, somme_cardinale_binaire(vc, vd), "qd")
    temoin = conjonction_intro(fW, chaine)
    assert temoin.conclusion == subst_f(W, "qd", corps), "témoin ≠ (W|qd)corps"
    Cn = N.modus_ponens(temoin, N.s5(corps, W, "qd"))           # b | c+d   [B1, B2]
    assert Cn.conclusion == est_multiple_cardinal(somme_cardinale_binaire(vc, vd), vb)

    curry = _fermeture_existentielle(Cn, B1, B2,
                                     _corps_divise(vb, vc, "qd"),
                                     _corps_divise(vb, vd, "qd"))
    # curry : (c multiple de b) ⇒ ((d multiple de b) ⇒ (c+d multiple de b)), clos
    res = _forme_conjonctive(curry, est_multiple_cardinal(vc, vb),
                             est_multiple_cardinal(vd, vb))
    assert res.conclusion == somme_multiples_cible(vc, vd, vb), "conclusion inattendue"
    assert res.est_clos, "somme_multiples : non clos"
    return res


__all__ = ["multiple_de_multiple", "multiple_de_multiple_cible",
           "somme_multiples", "somme_multiples_cible"]
