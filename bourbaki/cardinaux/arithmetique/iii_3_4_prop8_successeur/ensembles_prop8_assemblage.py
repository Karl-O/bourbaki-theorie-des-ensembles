"""§III.3.4 — Proposition 8 : ASSEMBLAGE du cœur back-and-forth par ANALYSE DE CAS.

Ce module RECOLLE les deux cas de la preuve back-and-forth de la Proposition 8
(« si a + 1 = b + 1, alors a = b ») au-dessus de la copie de gauche.  Le CAS 1
(le marqueur * = (∅,1) est FIXÉ par la bijection h : A⊔{∅} → B⊔{∅}) est DÉJÀ
CERTIFIÉ et CLOS dans le sous-package ensembles_prop8_coeur (eq_copies_cas_fixe :
bij(h) ⇒ (h(*)=* ⇒ Eq(A×{0}, B×{0}))).  Le CAS 2 (h(*) ∈ B×{0}, échange ponctuel
a₀↦b₀ au niveau du graphe) est la partie DURE, REPORTÉE — surgery de graphe sur un
témoin abstrait h, de la même catégorie de difficulté que les bijections
somme/produit (~1 round complet).

Le recollement, lui, est ÉLÉMENTAIRE et est CERTIFIÉ ici : une bijection
h : A⊔{∅} → B⊔{∅} envoie le marqueur * quelque part dans B⊔{∅} = (B×{0}) ⊎ {*}
(somme_un_plus_point), donc on a la DISJONCTION  h(*) ∈ B×{0}  ∨  h(*) = *  ;
`cas` réunit alors le CAS 1 (branche h(*)=*) et le CAS 2 (branche h(*)∈B×{0}).

──────────────────────────────────────────────────────────────────────────────
On formalise le CAS 2 comme l'HYPOTHÈSE UNIVERSELLE (sur la bijection h)

    H2(A,B) := (∀h)((bij(h, A⊔{∅}, B⊔{∅}) et h(*) ∈ B×{0}) ⇒ Eq(A×{0}, B×{0})),

exactement comme reduction_back_and_forth réduit la Proposition 8 à l'unique
lemme back-and-forth.  On obtient alors, par recollement certifié :

  • eq_copies_par_cas(A,B)        — {H2(A,B)} ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A×{0},B×{0})
        (la disjonction sur h(*) recolle CAS 1 (clos) et CAS 2 (= H2)) ;
  • eq_somme_un_implique_eq_mod_cas2(A,B)  — ⊢ H2(A,B) ⇒
        (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B))     [compose avec eq_copies_gauches_implique_eq] ;
  • prop8_successeur_injectif_mod_cas2(A,B) — ⊢ H2(A,B) ⇒
        ((successeur(A)=successeur(B)) ⇒ (Card A = Card B))   [Proposition 8 modulo CAS 2].

Ainsi finir la Proposition 8 INCONDITIONNELLEMENT ne demande plus QUE de prouver
H2 = le CAS 2 (échange a₀↦b₀).  Théorèmes CLOS (l'hypothèse H2 est déchargée par
loi_deduction), CONDITIONNELS au seul CAS 2.

THÉORÈMES CERTIFIÉS (chacun testé, cf. test_prop8_assemblage.py) :
  • cas2_hypothese(A,B)               (formule : énoncé exact de H2) ;
  • hstar_dans_BS(A,B)   {dom h=A⊔{∅}, image h=B⊔{∅}} ⊢ h(*) ∈ B⊔{∅}  (clos sous hyps) ;
  • eq_copies_par_cas(A,B)            {H2} ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A×{0},B×{0}) ;
  • eq_somme_un_implique_eq_mod_cas2(A,B)  ⊢ H2 ⇒ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)) ;
  • prop8_successeur_injectif_mod_cas2(A,B) ⊢ H2 ⇒ (succ(A)=succ(B) ⇒ Card A=Card B).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, impl, appartient,
                                       existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (cas, instancie,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (existe_elimination,
                                                                  alpha_existe)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN, somme_disjointe
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_copie_marquee import eq_copies_gauches_implique_eq
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.prop8_coeur import eq_copies_cas_fixe
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.prop8_coeur._marqueurs import m_dans_AS
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_plus_point import somme_un_plus_point
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_successeur import reduction_back_and_forth


def _t(v):
    return v if isinstance(v, Terme) else var(v)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)
_H = "h"


def _A0(a):
    return E.produit(_t(a), E.singleton(ZERO))


def _B0(b):
    return E.produit(_t(b), E.singleton(ZERO))


def _AS(a):
    return somme_disjointe(_t(a), E.singleton(E.VIDE))


# ═══════════════════════════════════════════════════════════════════════════════
# CAS 2, formulé comme HYPOTHÈSE UNIVERSELLE  H2(A,B)   (le lemme REPORTÉ)
# ═══════════════════════════════════════════════════════════════════════════════
def cas2_hypothese(a="A", b="B", h=_H):
    """La formule H2(A,B) := (∀h)((bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})).

    C'est l'ÉNONCÉ EXACT du CAS 2 de la preuve back-and-forth : quand la bijection
    h n'envoie PAS le marqueur sur le marqueur mais dans la copie de gauche de
    droite B×{0}, on réussit quand même à fabriquer une équipotence des copies de
    gauche (par échange ponctuel a₀↦b₀).  Universel en h car h sera le témoin de
    l'équipotence Eq(A⊔{∅},B⊔{∅}) — un graphe arbitraire."""
    vh = _t(h)
    AS, BS = _AS(a), _AS(b)
    B0 = _B0(b)
    hstar = E.valeur(vh, _STAR)                       # h(*)
    body = impl(et(est_bijection_de(vh, AS, BS), appartient(hstar, B0)),
                equipotent(_A0(a), B0))
    return pourtout(h, body)


# ═══════════════════════════════════════════════════════════════════════════════
# h(*) ∈ B⊔{∅}   (le marqueur est envoyé dans l'ensemble augmenté de droite)
# ═══════════════════════════════════════════════════════════════════════════════
def hstar_dans_BS(a="A", b="B", h=_H):
    """{dom h = A⊔{∅}, image h = B⊔{∅}} ⊢ h(*) ∈ B⊔{∅}.

    Le marqueur * ∈ A⊔{∅} = dom h, donc (*, h(*)) ∈ h (valeur_dans_graphe), donc
    h(*) ∈ image(h, A⊔{∅}) = B⊔{∅} (AXIOME_IMAGE ⇐ puis réécriture image h=B⊔{∅}).
    Brique indispensable pour appliquer somme_un_plus_point à h(*)."""
    vh = _t(h)
    AS, BS = _AS(a), _AS(b)
    hstar = E.valeur(vh, _STAR)
    # *∈dom h  (de dom h=A⊔{∅} et *∈A⊔{∅})
    hdom = N.assume(egal(E.dom(vh), AS))
    m_inAS = m_dans_AS(a)                             # *∈A⊔{∅}  (clos)
    eq_dom = N.modus_ponens(hdom, symetrie(E.dom(vh), AS))   # A⊔{∅} = dom h
    m_in_dom = N.modus_ponens(m_inAS, equivalence_avant(N.modus_ponens(
        eq_dom, N.s6(AS, E.dom(vh), "w", appartient(_STAR, var("w"))))))   # *∈dom h
    # (*, h(*)) ∈ h  (témoin)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vh), _STAR)     # *∈dom h ⇔ (∃y)((*,y)∈h)
    exy = N.modus_ponens(m_in_dom, equivalence_avant(car))   # (∃y)((*,y)∈h)
    star_hstar = N.modus_ponens(exy, N.existe_temoin(
        appartient(E.couple(_STAR, var("y")), vh), "y"))      # (*, h(*)) ∈ h
    # h(*) ∈ image(h, A⊔{∅})  (AXIOME_IMAGE ⇐, témoin x:=*)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car = instancie(instancie(instancie(ax_img, vh), AS), hstar)
    ex = N.modus_ponens(conjonction_intro(m_inAS, star_hstar),
        N.s5(et(appartient(var("x"), AS), appartient(E.couple(var("x"), hstar), vh)),
             _STAR, "x"))                              # (∃x)(x∈A⊔{∅} et (x,h(*))∈h)
    hstar_in_img = N.modus_ponens(ex, equivalence_arriere(img_car))   # h(*)∈image(h,A⊔{∅})
    # réécriture image h = B⊔{∅}
    himg = N.assume(egal(E.image(vh, AS), BS))
    return N.modus_ponens(hstar_in_img, equivalence_avant(N.modus_ponens(
        himg, N.s6(E.image(vh, AS), BS, "w", appartient(hstar, var("w"))))))   # h(*)∈B⊔{∅}


# ═══════════════════════════════════════════════════════════════════════════════
# RECOLLEMENT par cas :  {H2} ⊢ Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A×{0}, B×{0})
# ═══════════════════════════════════════════════════════════════════════════════
def eq_copies_par_cas(a="A", b="B", h=_H):
    """{H2(A,B)} ⊢ Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A×{0}, B×{0}).

    RECOLLEMENT certifié des deux cas.  De Eq(A⊔{∅},B⊔{∅}) = (∃h)bij(h), on prend
    le témoin h ; bij(h) donne (via h(*)∈B⊔{∅}, hstar_dans_BS, puis
    somme_un_plus_point) la disjonction  h(*)∈B×{0}  ∨  h(*)=*  ; `cas` réunit :
      • branche h(*)=*       : CAS 1 (eq_copies_cas_fixe, CLOS) ⇒ Eq(A×{0},B×{0}) ;
      • branche h(*)∈B×{0}   : H2 instancié en h ⇒ Eq(A×{0},B×{0}).
    Le résultat ne dépend QUE de H2 (h, lié par ∃, est éliminé : ni dans H2 ni dans
    la conclusion Eq(A×{0},B×{0}))."""
    vh = _t(h)
    AS, BS = _AS(a), _AS(b)
    A0, B0 = _A0(a), _B0(b)
    hstar = E.valeur(vh, _STAR)
    bij_f = est_bijection_de(vh, AS, BS)

    # Sous le témoin h : bij(h)  ⊢  Eq(A×{0}, B×{0})
    bij = N.assume(bij_f)
    domh = conjonction_elim_droite(conjonction_elim_gauche(bij))   # dom h = A⊔{∅}
    img = conjonction_elim_droite(conjonction_elim_droite(bij))    # image h = B⊔{∅}

    # h(*) ∈ B⊔{∅}  (décharge ses 2 hypothèses dom/img par bij)
    hbs = hstar_dans_BS(a, b, h)
    hbs = N.modus_ponens(domh, N.loi_deduction(egal(E.dom(vh), AS), hbs))
    hbs = N.modus_ponens(img, N.loi_deduction(egal(E.image(vh, AS), BS), hbs))

    # disjonction  h(*)∈B×{0}  ∨  h(*)=*
    sup = somme_un_plus_point(b, hstar)               # h(*)∈B⊔{∅} ⇔ (h(*)∈B×{0} ∨ h(*)=*)
    disj = N.modus_ponens(hbs, equivalence_avant(sup))   # (h(*)∈B×{0}) ∨ (h(*)=*)

    # branche A : h(*)∈B×{0}  ⇒  Eq(A×{0},B×{0})   (via H2)
    H2 = N.assume(cas2_hypothese(a, b, h))
    H2_inst = instancie(H2, vh)                       # (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0)
    hbranchA = N.assume(appartient(hstar, B0))        # h(*)∈B×{0}
    eqA = N.modus_ponens(conjonction_intro(bij, hbranchA), H2_inst)   # Eq(A0,B0)
    impA = N.loi_deduction(appartient(hstar, B0), eqA)   # h(*)∈B0 ⇒ Eq(A0,B0)

    # branche B : h(*)=*  ⇒  Eq(A×{0},B×{0})   (via CAS 1, CLOS)
    cas1 = eq_copies_cas_fixe(a, b, h)                # bij(h) ⇒ (h(*)=* ⇒ Eq(A0,B0))
    impB = N.modus_ponens(bij, cas1)                  # h(*)=* ⇒ Eq(A0,B0)

    eq_copies = cas(disj, impA, impB)                 # Eq(A0,B0)   [hyps : bij(h), H2]
    inner = N.loi_deduction(bij_f, eq_copies)         # H2 ⊢ bij(h) ⇒ Eq(A0,B0)
    # éliminer le ∃h : (∃h)bij(h) ⇒ Eq(A0,B0)   (h non libre dans H2 ni dans Eq(A0,B0))
    elim = existe_elimination(inner, h)               # (∃h)bij(h,A⊔{∅},B⊔{∅}) ⇒ Eq(A0,B0)
    # α-renommer (∃h)bij(h,·) en (∃F)bij(F,·) = Eq(A⊔{∅},B⊔{∅})  (la déf. de equipotent)
    al = alpha_existe(h, "F", est_bijection_de(vh, AS, BS))   # (∃h)bij(h,·) ⇔ (∃F)bij(F,·)
    return syllogisme(equivalence_arriere(al), elim)  # Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A0,B0)   [hyp H2]


# ═══════════════════════════════════════════════════════════════════════════════
# Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)   MODULO CAS 2   (le cœur back-and-forth conditionnel)
# ═══════════════════════════════════════════════════════════════════════════════
def eq_somme_un_implique_eq_mod_cas2(a="A", b="B", h=_H):
    """⊢ H2(A,B) ⇒ (Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B)).

    Le CŒUR back-and-forth de la Proposition 8, MODULO le seul CAS 2 (H2).  On
    compose le recollement eq_copies_par_cas (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A×{0},B×{0}),
    sous H2) avec le transport déjà certifié eq_copies_gauches_implique_eq
    (Eq(A×{0},B×{0}) ⇒ Eq(A,B)) ; puis on décharge H2.  CLOS, conditionnel au CAS 2."""
    H2_f = cas2_hypothese(a, b, h)
    par_cas = eq_copies_par_cas(a, b, h)              # H2 ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A0,B0)
    transport = eq_copies_gauches_implique_eq(a, b)   # Eq(A0,B0) ⇒ Eq(A,B)
    chain = syllogisme(par_cas, transport)            # H2 ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)
    return N.loi_deduction(H2_f, chain)               # ⊢ H2 ⇒ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B))


# ═══════════════════════════════════════════════════════════════════════════════
# PROPOSITION 8 (forme successeur), MODULO CAS 2
# ═══════════════════════════════════════════════════════════════════════════════
def prop8_successeur_injectif_mod_cas2(a="A", b="B", h=_H):
    """⊢ H2(A,B) ⇒ ((successeur(A) = successeur(B)) ⇒ (Card A = Card B)).

    La PROPOSITION 8 (« le successeur cardinal est injectif »), ASSEMBLÉE modulo le
    seul CAS 2.  Sous H2, eq_somme_un_implique_eq_mod_cas2 fournit le cœur
    back-and-forth H := (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)), que reduction_back_and_forth
    (déjà clos) transforme en (succ(A)=succ(B) ⇒ Card A=Card B).  Finir la
    Proposition 8 inconditionnellement ne demande donc plus QUE le CAS 2."""
    H2_f = cas2_hypothese(a, b, h)
    coeur = eq_somme_un_implique_eq_mod_cas2(a, b, h)   # ⊢ H2 ⇒ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B))
    H2 = N.assume(H2_f)
    hard = N.modus_ponens(H2, coeur)                    # H2 ⊢ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B))
    assemble = reduction_back_and_forth(a, b)           # (Eq(A⊔{∅},B⊔{∅})⇒Eq(A,B)) ⇒ (succ=succ ⇒ Card=Card)
    prop8 = N.modus_ponens(hard, assemble)              # H2 ⊢ succ(A)=succ(B) ⇒ Card A=Card B
    return N.loi_deduction(H2_f, prop8)                 # ⊢ H2 ⇒ (succ=succ ⇒ Card A=Card B)


__all__ = ["cas2_hypothese", "hstar_dans_BS", "eq_copies_par_cas",
           "eq_somme_un_implique_eq_mod_cas2", "prop8_successeur_injectif_mod_cas2"]
