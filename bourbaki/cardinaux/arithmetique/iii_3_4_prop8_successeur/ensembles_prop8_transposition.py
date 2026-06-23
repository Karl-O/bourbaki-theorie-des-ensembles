"""§III.3.4 — Proposition 8 : CAS 2 par TRANSPOSITION + COMPOSITION (route élégante).

Ce module FERME le CAS 2 de la preuve back-and-forth de la Proposition 8 (« si
a + 1 = b + 1, alors a = b ») MODULO une seule brique CONCRÈTE et LOCALE : la
TRANSPOSITION τ de B⊔{∅} échangeant le marqueur * = (∅,1) et le point c₀ = h(*).

────────────────────────────────────────────────────────────────────────────────
IDÉE (route de la tâche, qui ramène le CAS 2 au CAS 1 déjà clos).  Sous une
bijection h : A⊔{∅} → B⊔{∅} avec h(*) ∈ B×{0} (CAS 2), on dispose d'une
TRANSPOSITION τ : B⊔{∅} → B⊔{∅} (involution) telle que τ(h(*)) = *.  Alors

        h₂ := τ ∘ h : A⊔{∅} → B⊔{∅}

est encore une bijection (composee_bijection, tâche A), et elle FIXE le marqueur :

        h₂(*) = (τ∘h)(*) = τ(h(*)) = *.

Donc h₂ est en CAS 1, et eq_cas_fixe_implique_eq(h₂) (CAS 1 CLOS) conclut Eq(A,B).
Le CAS 2 est ainsi RAMENÉ au CAS 1 par composition avec τ — c'est l'astuce
« réparer la bijection en ramenant le marqueur sur le marqueur ».

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE CERTIFIE (tout CLOS, conditionnel à la SEULE existence de τ) :

On formule la brique transposition comme l'HYPOTHÈSE EXISTENTIELLE LOCALE, en c₀ :

    HT(B, c₀) := (∃τ)( est_bijection_de(τ, B⊔{∅}, B⊔{∅})  et  τ(c₀) = * ).

C'est EXACTEMENT « il existe une transposition de B⊔{∅} qui ramène c₀ sur * ».
Elle est purement CONCRÈTE (un échange ponctuel dans un ensemble augmenté), sans
aucun témoin abstrait — sa construction (graphe_terme + sélecteur 3-cas, fonctionnel
GRATUIT par graphe_terme_fonctionnel, involution ⇒ bijectivité) est la SEULE chose
qui reste pour la Proposition 8 inconditionnelle.  On l'isole ici proprement.

  • h2_fixe_le_marqueur(A,B,h,τ)  —
        {bij(h,A⊔{∅},B⊔{∅}), bij(τ,B⊔{∅},B⊔{∅}), τ(h(*))=*} ⊢ (τ∘h)(*) = * ;
  • h2_cas1_eq(A,B,h,τ)           —
        {bij(h,·), h(*)∈B×{0}, bij(τ,·), τ(h(*))=*} ⊢ Eq(A,B)
        (composee_bijection donne bij(τ∘h), puis CAS 1 via h₂(*)=*) ;
  • cas2_via_transposition(A,B,h) —
        {HT(B,h(*))} ⊢ (bij(h,·) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})
        (le CŒUR du CAS 2 : Eq(A,B) ⇒ Eq(A×{0},B×{0}) par eq_copies_gauches, sens
         facile) — l'unique forme « copies de gauche » exigée par H2 ;
  • h2_hypothese(A,B)             — la formule HT2(A,B) := (∀h)(HT(B,h(*)) ⇒ …) ;
  • prop8_via_transposition_mod_HT(A,B) — ⊢ HT2(A,B) ⇒
        ((successeur(A)=successeur(B)) ⇒ (Card A = Card B))  (Prop. 8 modulo HT2).

Ainsi la Proposition 8 ne dépend PLUS QUE de la construction concrète de la
transposition τ (existence de τ : B⊔{∅}→B⊔{∅} bijective avec τ(c₀)=* pour tout
c₀∈B×{0}).  Aucun théorème de Bourbaki n'est postulé : HT est une PROPRIÉTÉ
CONCRÈTE déchargée par loi_deduction, à fournir par construction.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, appartient,
                                       existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN, somme_disjointe
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.cardinaux.ensembles_composee_bijection import composee_bijection
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_composee_valeurs import composition_valeur_t
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.prop8_coeur import eq_cas_fixe_implique_eq
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.prop8_coeur._marqueurs import m_dans_AS
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_copie_marquee import (
    eq_copie_marquee, _eq_sym_t, _eq_trans_t)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)
_H = "h"
_TAU = "tau"


def _A0(a):
    return E.produit(_t(a), E.singleton(ZERO))


def _B0(b):
    return E.produit(_t(b), E.singleton(ZERO))


def _AS(a):
    return somme_disjointe(_t(a), E.singleton(E.VIDE))


def _BS(b):
    return somme_disjointe(_t(b), E.singleton(E.VIDE))


def _composee_bijection_t(f, g, tX, tY, tZ):
    """⊢ (bij(F,X,Y) et bij(G,Y,Z)) ⇒ bij(G∘F, X, Z)  pour des TERMES X, Y, Z.

    composee_bijection n'accepte que des NOMS pour X, Y, Z (usage interne de
    vX.nom, var(y) avec liants fixes) ; on la généralise en X, Y, Z puis on
    instancie aux termes (renommage déterministe), comme _prop1_direct_t.  f, g
    restent des noms de graphe-lettre (F, G)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        composee_bijection(f, g, "X", "Y", "Z"))))   # (∀X)(∀Y)(∀Z)((bij(F,X,Y)et bij(G,Y,Z))⇒bij(G∘F,X,Z))
    return instancie(instancie(instancie(gen, _t(tX)), _t(tY)), _t(tZ))


def _cas1_t(a, b, tH):
    """⊢ est_bijection_de(H, A⊔{∅}, B⊔{∅}) ⇒ ((H(*)=*) ⇒ Eq(A,B))  pour un TERME H.

    Version TERME du CAS 1 (eq_cas_fixe_implique_eq n'accepte qu'un NOM de graphe) :
    on généralise sur le graphe « h » puis on instancie au terme H = τ∘h (sûr : les
    liants internes u,v,z,w,F,y de l'énoncé ne figurent pas dans τ∘h, qui ne
    contient que tau, h libres)."""
    gen = N.generalisation("h", eq_cas_fixe_implique_eq(a, b, "h"))   # (∀h)(bij(h,·)⇒(h(*)=*⇒Eq(A,B)))
    return instancie(gen, _t(tH))


def _eq_implique_eq_copies_gauches(a, b):
    """⊢ Eq(A, B) ⇒ Eq(A×{0}, B×{0}).   (sens FACILE, marqueur 0 ; clos localement.)

    Eq(A×{0}, A) ∘ Eq(A, B) ∘ Eq(B, B×{0}) ⟹ Eq(A×{0}, B×{0}) — deux transitivités,
    avec Eq(A×{0},A) = symétrie de Eq(A, A×{0}) (eq_copie_marquee, marqueur 0).
    Réciproque exacte de eq_copies_gauches_implique_eq."""
    va, vb = _t(a), _t(b)
    A0, B0 = _A0(a), _B0(b)
    h = N.assume(equipotent(va, vb))                  # Eq(A, B)   [hyp]
    eq_A_A0 = eq_copie_marquee(a, ZERO)               # Eq(A, A×{0})
    eq_B_B0 = eq_copie_marquee(b, ZERO)               # Eq(B, B×{0})
    eq_A0_A = N.modus_ponens(eq_A_A0, _eq_sym_t(va, A0))   # Eq(A×{0}, A)
    # Eq(A×{0}, A) et Eq(A, B) ⇒ Eq(A×{0}, B)
    eq_A0_B = N.modus_ponens(conjonction_intro(eq_A0_A, h), _eq_trans_t(A0, va, vb))
    # Eq(A×{0}, B) et Eq(B, B×{0}) ⇒ Eq(A×{0}, B×{0})
    eq_A0_B0 = N.modus_ponens(conjonction_intro(eq_A0_B, eq_B_B0), _eq_trans_t(A0, vb, B0))
    return N.loi_deduction(equipotent(va, vb), eq_A0_B0)


# ═══════════════════════════════════════════════════════════════════════════════
# Brique partagée :  * ∈ dom h   (sous dom h = A⊔{∅}, via * ∈ A⊔{∅})
# ═══════════════════════════════════════════════════════════════════════════════
def _star_in_dom_h(a, h):
    """{dom h = A⊔{∅}} ⊢ (∃y)((*,y) ∈ h).   (* ∈ A⊔{∅} = dom h, déplié par AXIOME_DOM.)"""
    vh = _t(h)
    AS = _AS(a)
    m_inAS = m_dans_AS(a)                              # * ∈ A⊔{∅}   (clos)
    hdom = N.assume(egal(E.dom(vh), AS))
    eq_dom = N.modus_ponens(hdom, symetrie(E.dom(vh), AS))   # A⊔{∅} = dom h
    m_in_dom = N.modus_ponens(m_inAS, equivalence_avant(N.modus_ponens(
        eq_dom, N.s6(AS, E.dom(vh), "w", appartient(_STAR, var("w"))))))   # * ∈ dom h
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vh), _STAR)     # * ∈ dom h ⇔ (∃y)((*,y)∈h)
    return N.modus_ponens(m_in_dom, equivalence_avant(car))   # (∃y)((*,y)∈h)


def _hstar_in_dom_tau(b, h, tau):
    """{image h = B⊔{∅}, dom τ = B⊔{∅}} ∪ {dom h = A⊔{∅}} ⊢ (∃y)((h(*),y) ∈ τ).

    h(*) ∈ B⊔{∅} (hstar_dans_BS) = dom τ, déplié par AXIOME_DOM.  (Les hypothèses
    dom h = A⊔{∅} et image h = B⊔{∅} sont celles de hstar_dans_BS.)"""
    from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_assemblage import hstar_dans_BS
    vh, vtau = _t(h), _t(tau)
    BS = _BS(b)
    hstar = E.valeur(vh, _STAR)
    hbs = hstar_dans_BS("A", b, h)                    # {dom h=A⊔{∅}, image h=B⊔{∅}} ⊢ h(*) ∈ B⊔{∅}
    # h(*) ∈ dom τ  (de dom τ = B⊔{∅})
    htdom = N.assume(egal(E.dom(vtau), BS))
    eq_tdom = N.modus_ponens(htdom, symetrie(E.dom(vtau), BS))   # B⊔{∅} = dom τ
    hstar_in_domt = N.modus_ponens(hbs, equivalence_avant(N.modus_ponens(
        eq_tdom, N.s6(BS, E.dom(vtau), "w", appartient(hstar, var("w"))))))   # h(*) ∈ dom τ
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vtau), hstar)   # h(*) ∈ dom τ ⇔ (∃y)((h(*),y)∈τ)
    return N.modus_ponens(hstar_in_domt, equivalence_avant(car))   # (∃y)((h(*),y)∈τ)


# ═══════════════════════════════════════════════════════════════════════════════
# h₂ := τ∘h FIXE le marqueur :  (τ∘h)(*) = *
# ═══════════════════════════════════════════════════════════════════════════════
def h2_fixe_le_marqueur(a="A", b="B", h=_H, tau=_TAU):
    """{bij(h,A⊔{∅},B⊔{∅}), bij(τ,B⊔{∅},B⊔{∅}), τ(h(*))=*} ⊢ (τ∘h)(*) = *.

    h₂ = composee(τ, h) = τ∘h.  composition_valeur_t(τ, h, *) donne (τ∘h)(*) =
    τ(h(*)) sous {(∃y)((*,y)∈h), (∃y)((h(*),y)∈τ), τ∘h fonctionnel} ; on coupe ces
    trois hypothèses (les deux domaines depuis dom h=A⊔{∅}, image h=B⊔{∅}, dom τ=
    B⊔{∅} ; la fonctionnalité de τ∘h depuis h,τ fonctionnels par composee_fonctionnelle),
    puis τ(h(*))=* (HT) réécrit le membre droit en *."""
    from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_fonctionnelle
    vh, vtau = _t(h), _t(tau)
    AS, BS = _AS(a), _BS(b)
    hstar = E.valeur(vh, _STAR)
    comp = E.composee(vtau, vh)                       # τ∘h
    tau_hstar = E.valeur(vtau, hstar)                 # τ(h(*))

    # extraire fonctionnel / dom / image de h et τ
    bijh = N.assume(est_bijection_de(vh, AS, BS))
    funh = conjonction_elim_gauche(conjonction_elim_gauche(bijh))   # h fonctionnel
    domh = conjonction_elim_droite(conjonction_elim_gauche(bijh))   # dom h = A⊔{∅}
    imgh = conjonction_elim_droite(conjonction_elim_droite(bijh))   # image h = B⊔{∅}
    bijt = N.assume(est_bijection_de(vtau, BS, BS))
    funt = conjonction_elim_gauche(conjonction_elim_gauche(bijt))   # τ fonctionnel
    domt = conjonction_elim_droite(conjonction_elim_gauche(bijt))   # dom τ = B⊔{∅}

    # (τ∘h)(*) = τ(h(*))  via composition_valeur_t, ses 3 hypothèses coupées
    cv = composition_valeur_t(vtau, vh, _STAR)        # (τ∘h)(*) = τ(h(*))  [3 hyps]
    # hyp 1 : (∃y)((*,y)∈h)   (de dom h = A⊔{∅})
    ex1 = N.modus_ponens(domh, N.loi_deduction(egal(E.dom(vh), AS), _star_in_dom_h(a, h)))
    cv = N.modus_ponens(ex1, N.loi_deduction(
        existe("y", appartient(E.couple(_STAR, var("y")), vh)), cv))
    # hyp 2 : (∃y)((h(*),y)∈τ)   (de dom h=A⊔{∅}, image h=B⊔{∅}, dom τ=B⊔{∅})
    ex2 = _hstar_in_dom_tau(b, h, tau)
    ex2 = N.modus_ponens(domh, N.loi_deduction(egal(E.dom(vh), AS), ex2))
    ex2 = N.modus_ponens(imgh, N.loi_deduction(egal(E.image(vh, AS), BS), ex2))
    ex2 = N.modus_ponens(domt, N.loi_deduction(egal(E.dom(vtau), BS), ex2))
    cv = N.modus_ponens(ex2, N.loi_deduction(
        existe("y", appartient(E.couple(hstar, var("y")), vtau)), cv))
    # hyp 3 : τ∘h fonctionnel   (composee_fonctionnelle sur h,τ fonctionnels)
    comp_func = N.modus_ponens(conjonction_intro(funh, funt),
                               composee_fonctionnelle(tau, h))   # τ∘h fonctionnel
    cv = N.modus_ponens(comp_func, N.loi_deduction(E.est_fonctionnel(comp), cv))
    # cv : (τ∘h)(*) = τ(h(*))   [hyps : bij(h), bij(τ)]
    # τ(h(*)) = *   (HT) ⇒ (τ∘h)(*) = *
    htau = N.assume(egal(tau_hstar, _STAR))           # τ(h(*)) = *
    return composer_egalites(cv, htau)                # (τ∘h)(*) = *


# ═══════════════════════════════════════════════════════════════════════════════
# CŒUR du CAS 2 : Eq(A,B) par composition avec la transposition (ramené au CAS 1)
# ═══════════════════════════════════════════════════════════════════════════════
def h2_cas1_eq(a="A", b="B", h=_H, tau=_TAU):
    """{bij(h,A⊔{∅},B⊔{∅}), bij(τ,B⊔{∅},B⊔{∅}), τ(h(*))=*} ⊢ Eq(A, B).

    h₂ = τ∘h est une bijection A⊔{∅}→B⊔{∅} (composee_bijection : F=h:A⊔{∅}→B⊔{∅},
    G=τ:B⊔{∅}→B⊔{∅}) qui FIXE le marqueur (h2_fixe_le_marqueur).  Donc h₂ est en
    CAS 1, et eq_cas_fixe_implique_eq(h₂) (CAS 1 CLOS) conclut Eq(A,B).  C'est la
    réduction CAS 2 → CAS 1 par la transposition."""
    vh, vtau = _t(h), _t(tau)
    AS, BS = _AS(a), _BS(b)
    comp = E.composee(vtau, vh)                       # h₂ = τ∘h

    # bij(τ∘h, A⊔{∅}, B⊔{∅})   (composee_bijection : f=h, g=τ, x=A⊔{∅}, y=z=B⊔{∅})
    bijh = N.assume(est_bijection_de(vh, AS, BS))
    bijt = N.assume(est_bijection_de(vtau, BS, BS))
    comp_bij_imp = _composee_bijection_t(h, tau, AS, BS, BS)   # (bij(h,·)et bij(τ,·)) ⇒ bij(τ∘h,A⊔{∅},B⊔{∅})
    bij_h2 = N.modus_ponens(conjonction_intro(bijh, bijt), comp_bij_imp)   # bij(τ∘h, A⊔{∅}, B⊔{∅})

    # (τ∘h)(*) = *   (h₂ fixe le marqueur)
    fixe = h2_fixe_le_marqueur(a, b, h, tau)          # [hyps bij(h), bij(τ), τ(h(*))=*]

    # CAS 1 sur h₂ : bij(h₂) ⇒ (h₂(*)=* ⇒ Eq(A,B))
    cas1 = _cas1_t(a, b, comp)                        # bij(τ∘h) ⇒ ((τ∘h)(*)=* ⇒ Eq(A,B))
    return N.modus_ponens(fixe, N.modus_ponens(bij_h2, cas1))   # Eq(A, B)


# ═══════════════════════════════════════════════════════════════════════════════
# CAS 2 sous l'hypothèse EXISTENTIELLE de transposition  HT(B, h(*))
# ═══════════════════════════════════════════════════════════════════════════════
def transposition_hypothese(b="B", c0=None, tau=_TAU):
    """La formule HT(B, c₀) := (∃τ)( bij(τ, B⊔{∅}, B⊔{∅})  et  τ(c₀) = * ).

    « Il existe une transposition de B⊔{∅} ramenant c₀ sur le marqueur * ».
    Brique CONCRÈTE LOCALE (échange ponctuel), à fournir par construction."""
    BS = _BS(b)
    vtau = _t(tau)
    c0 = _STAR if c0 is None else c0
    body = et(est_bijection_de(vtau, BS, BS), egal(E.valeur(vtau, c0), _STAR))
    return existe(tau, body)


def cas2_via_transposition(a="A", b="B", h=_H, tau=_TAU):
    """{HT(B, h(*))} ⊢ (bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0}, B×{0}).

    Le CŒUR du CAS 2 sous la SEULE hypothèse de transposition.  De HT(B,h(*)) on
    prend le témoin τ ; h2_cas1_eq donne Eq(A,B) (par composition τ∘h ramenée au
    CAS 1) ; eq_implique_eq_copies_gauches (sens facile, déjà clos) en tire
    Eq(A×{0},B×{0}) — la forme « copies de gauche » qu'exige exactement H2.
    (h(*)∈B×{0} est l'hypothèse de cadrage du CAS 2 ; elle n'est pas utilisée dans
    cette route — la transposition suffit — mais elle reste pour coller à H2.)"""
    vh, vtau = _t(h), _t(tau)
    AS, BS = _AS(a), _BS(b)
    A0, B0 = _A0(a), _B0(b)
    hstar = E.valeur(vh, _STAR)
    bij_h = est_bijection_de(vh, AS, BS)
    body_tau = et(est_bijection_de(vtau, BS, BS), egal(E.valeur(vtau, hstar), _STAR))

    # sous bij(h), h(*)∈B×{0}, et le corps de la transposition (témoin τ) : Eq(A,B)
    bijh = N.assume(bij_h)
    htau = N.assume(body_tau)
    bijt = conjonction_elim_gauche(htau)              # bij(τ, B⊔{∅}, B⊔{∅})
    fix_t = conjonction_elim_droite(htau)             # τ(h(*)) = *

    eqAB = h2_cas1_eq(a, b, h, tau)                   # {bij(h), bij(τ), τ(h(*))=*} ⊢ Eq(A,B)
    eqAB = N.modus_ponens(bijt, N.loi_deduction(est_bijection_de(vtau, BS, BS), eqAB))
    eqAB = N.modus_ponens(fix_t, N.loi_deduction(egal(E.valeur(vtau, hstar), _STAR), eqAB))
    # Eq(A,B) ⇒ Eq(A×{0},B×{0})   (sens facile, clos)
    facile = _eq_implique_eq_copies_gauches(a, b)     # Eq(A,B) ⇒ Eq(A×{0},B×{0})
    eq_copies = N.modus_ponens(eqAB, facile)          # Eq(A×{0},B×{0})   [hyps : bij(h), corps τ]
    # décharger le corps de la transposition en (∃τ) = HT(B,h(*))
    inner = N.loi_deduction(body_tau, eq_copies)      # corps_τ ⇒ Eq(A×{0},B×{0})   [hyp bij(h)]
    elim = existe_elimination(inner, tau)             # (∃τ)corps_τ ⇒ Eq(A×{0},B×{0})   [hyp bij(h)]
    # (∃τ)corps_τ = HT(B,h(*))  ;  sortir aussi h(*)∈B×{0} (non utilisée) en antécédent
    HT = N.assume(transposition_hypothese(b, hstar, tau))
    eq_copies2 = N.modus_ponens(HT, elim)             # Eq(A×{0},B×{0})   [hyps : bij(h), HT]
    # (bij(h) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})   [hyp HT]
    hab = N.assume(et(bij_h, appartient(hstar, B0)))
    bijh2 = conjonction_elim_gauche(hab)
    eq_copies3 = N.modus_ponens(bijh2, N.loi_deduction(bij_h, eq_copies2))   # [hyps : HT]
    return N.loi_deduction(et(bij_h, appartient(hstar, B0)), eq_copies3)


# ═══════════════════════════════════════════════════════════════════════════════
# H2 (CAS 2) sous l'hypothèse GLOBALE de transposition  HT_glob(A,B)
# ═══════════════════════════════════════════════════════════════════════════════
def transposition_globale(a="A", b="B", h=_H, tau=_TAU):
    """La formule HT_glob(A,B) := (∀h) HT(B, h(*))
       = (∀h)(∃τ)( bij(τ,B⊔{∅},B⊔{∅}) et τ(h(*)) = * ).

    « Pour toute bijection h, il existe une transposition de B⊔{∅} ramenant h(*)
    sur * ».  Conséquence DIRECTE (par instanciation c₀:=h(*)) de l'existence d'une
    transposition pour TOUT point c₀∈B⊔{∅} — la brique concrète unique restante."""
    vh = _t(h)
    hstar = E.valeur(vh, _STAR)
    return pourtout(h, transposition_hypothese(b, hstar, tau))


def h2_de_transposition_globale(a="A", b="B", h=_H, tau=_TAU):
    """⊢ HT_glob(A,B) ⇒ H2(A,B).   (l'hypothèse globale de transposition fournit le CAS 2.)

    H2(A,B) = (∀h)((bij(h,·) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})).  Pour chaque h,
    cas2_via_transposition(h) ⊢ {HT(B,h(*))} ⊢ corps_h ; HT_glob instancié en h
    fournit HT(B,h(*)) ; modus ponens ⇒ corps_h ; généralisation en h ⇒ H2."""
    from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_assemblage import cas2_hypothese
    vh = _t(h)
    hstar = E.valeur(vh, _STAR)
    HTg_f = transposition_globale(a, b, h, tau)
    HTg = N.assume(HTg_f)
    HT_h = instancie(HTg, vh)                         # HT(B, h(*))   (corps de HT_glob en h)
    corps = cas2_via_transposition(a, b, h, tau)      # {HT(B,h(*))} ⊢ (bij(h)et h(*)∈B0) ⇒ Eq(A0,B0)
    corps_h = N.modus_ponens(HT_h, N.loi_deduction(
        transposition_hypothese(b, hstar, tau), corps))   # (bij(h)et h(*)∈B0) ⇒ Eq(A0,B0)  [hyp HT_glob]
    H2 = N.generalisation(h, corps_h)                 # (∀h)(...) = H2(A,B)   [hyp HT_glob]
    return N.loi_deduction(HTg_f, H2)                 # ⊢ HT_glob ⇒ H2


# ═══════════════════════════════════════════════════════════════════════════════
# PROPOSITION 8, MODULO la SEULE hypothèse de transposition  HT_glob
# ═══════════════════════════════════════════════════════════════════════════════
def prop8_via_transposition_mod_HT(a="A", b="B", h=_H, tau=_TAU):
    """⊢ HT_glob(A,B) ⇒ ((successeur(A) = successeur(B)) ⇒ (Card A = Card B)).

    La PROPOSITION 8 ASSEMBLÉE modulo la SEULE brique CONCRÈTE de transposition
    HT_glob(A,B) = (∀h)(∃τ)(bij(τ,B⊔{∅},B⊔{∅}) et τ(h(*))=*).  Sous HT_glob :
        HT_glob ⇒[h2_de_transposition_globale] H2(A,B)
              ⇒[prop8_successeur_injectif_mod_cas2] (succ(A)=succ(B) ⇒ Card A=Card B).
    Donc finir la Proposition 8 inconditionnellement ne demande plus QUE la
    construction concrète de la transposition (un échange ponctuel dans B⊔{∅})."""
    from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_assemblage import (
        prop8_successeur_injectif_mod_cas2)
    HTg_f = transposition_globale(a, b, h, tau)
    ht_to_h2 = h2_de_transposition_globale(a, b, h, tau)   # HT_glob ⇒ H2
    h2_to_prop8 = prop8_successeur_injectif_mod_cas2(a, b, h)   # H2 ⇒ (succ=succ ⇒ Card=Card)
    HTg = N.assume(HTg_f)
    H2 = N.modus_ponens(HTg, ht_to_h2)                # H2   [hyp HT_glob]
    prop8 = N.modus_ponens(H2, h2_to_prop8)           # succ=succ ⇒ Card A=Card B   [hyp HT_glob]
    return N.loi_deduction(HTg_f, prop8)              # ⊢ HT_glob ⇒ (succ=succ ⇒ Card A=Card B)


__all__ = ["transposition_hypothese", "transposition_globale",
           "h2_fixe_le_marqueur", "h2_cas1_eq", "cas2_via_transposition",
           "h2_de_transposition_globale", "prop8_via_transposition_mod_HT"]
