"""§III.3.3 — Arithmétique du produit cardinal (E.III.3, Déf. 3 + Cor. de Prop. 5).

DÉBLOQUÉ par le keystone `eq_produit_invariant`
        ⊢ (Eq(X, X₁) et Eq(Y, Y₁))  ⇒  Eq(X×Y, X₁×Y₁)
(ensembles_produit_equipotence) et par la commutativité ensembliste
        ⊢ Eq(X×Y, Y×X)
(ensembles_produit_commute), reliées aux cardinaux par la Proposition 1
        ⊢ Eq(X, Y) ⇔ (Card X = Card Y)
(ensembles_cardinaux_theoremes).

PRODUIT CARDINAL BINAIRE.  Bourbaki (Déf. 3, E.III.3.3) pose, pour deux cardinaux
a et b, le produit a·b := Card(a × b)  (cardinal du produit ensembliste des deux
ensembles a, b — cas à deux indices de la définition par famille).  C'est donc :

        produit_cardinal_binaire(a, b)  :=  Card(a × b)  =  cardinal(produit(a, b)).

(On NE redéfinit PAS `ensembles_cardinaux.produit_cardinal`, réservé au produit
d'une FAMILLE Card(∏_{ι∈I} a_ι) ; le produit binaire est le cas a·b à deux indices,
codé via le produit ensembliste binaire `E.produit`, support de tout le keystone.)

RÉSULTATS (chacun CERTIFIÉ par le noyau et TESTÉ, test_arith_cardinale.py) :
  • produit_cardinal_bien_defini(X,Y,a,b)
        ⊢ (Card X = a et Card Y = b) ⇒ Card(X×Y) = produit_cardinal_binaire(a,b)
    — Card(X×Y) ne dépend QUE de Card X et Card Y (le produit cardinal est une
      opération bien définie sur les cardinaux) ;
  • produit_cardinal_commutatif(X,Y)
        ⊢ Card(X×Y) = Card(Y×X)        (= produit_cardinal_binaire(X,Y)
                                          = produit_cardinal_binaire(Y,X))
    — commutativité a·b = b·a (Cor. de Prop. 5, E.III.3.3).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient, existe,
                     subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (equipotent_son_cardinal,
                                           cardinal_egal_si_equipotent)
from bourbaki.cardinaux.arithmetique.ensembles_produit_equipotence import eq_produit_invariant
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import eq_produit_commute
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, alpha_existe,
                                      congruence_existe)
from bourbaki.cardinaux.ensembles_cardinaux import equipotent, est_bijection_de


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le produit cardinal BINAIRE  a·b := Card(a×b)  (E.III.3.3, Déf. 3, deux indices) ──
def produit_cardinal_binaire(a, b):
    """a · b := Card(a × b)   (produit cardinal binaire, E.III.3.3, Déf. 3).

    Cardinal du produit ensembliste binaire des deux ensembles/cardinaux a, b.
    C'est le cas à deux indices de la définition par famille ∏_{ι∈I} a_ι ; on le
    code via le produit ensembliste binaire `E.produit`, support du keystone
    d'invariance et de la commutativité ensembliste."""
    return cardinal(E.produit(_t(a), _t(b)))


# ── Pont équipotence ↔ cardinal : Eq(X, a) sous Card X = a ────────────────────
def _eq_son_cardinal_reecrit(x, a):
    """{Card X = a} ⊢ Eq(X, a).   (réécriture de Eq(X, Card X) par Card X = a.)

    equipotent_son_cardinal(X) ⊢ Eq(X, Card X) (clos) ; sous l'hypothèse
    Card X = a, le schéma S6 (Leibniz) transporte le 2ᵉ argument de Card X à a."""
    vX, va = _t(x), _t(a)
    cX = cardinal(vX)
    eq_card = equipotent_son_cardinal(x) if isinstance(x, str) \
        else _eq_son_cardinal_terme(vX)               # Eq(X, Card X)
    # S6 : (Card X = a) ⇒ (Eq(X, Card X) ⇔ Eq(X, a))
    leib = N.s6(cX, va, "w", equipotent(vX, var("w")))
    h = N.assume(egal(cX, va))                         # Card X = a
    equiv = N.modus_ponens(h, leib)                    # Eq(X, Card X) ⇔ Eq(X, a)
    return N.modus_ponens(eq_card, equivalence_avant(equiv))   # Eq(X, a)   [hyp Card X=a]


def _eq_son_cardinal_terme(vX):
    """⊢ Eq(T, Card T) pour un TERME T (généralise equipotent_son_cardinal aux termes)."""
    refl_all = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    return instancie(refl_all, vX)


def _prop1_direct_t(tU, tV):
    """⊢ Eq(U, V) ⇒ (Card U = Card V) pour des TERMES U, V quelconques.

    Version TERME du sens direct de la Proposition 1 (cardinal_egal_si_equipotent
    n'accepte que des NOMS de variables) : on généralise le sens direct en X, Y
    puis on instancie aux termes U, V (robuste grâce au renommage déterministe
    _fraiche → @0,@1)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    gen = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))      # (∀X)(∀Y)(Eq(X,Y) ⇒ Card X=Card Y)
    return instancie(instancie(gen, tU), tV)         # Eq(U,V) ⇒ Card U=Card V


# ── (1) BIEN-DÉFINITION du produit cardinal ───────────────────────────────────
# NB liants : les cardinaux-paramètres a, b sont nommés « A », « B » (et NON « a »,
# « b ») car le keystone eq_produit_invariant utilise « a », « b » comme liants
# INTERNES des projections pr₁/pr₂ du terme produit (E.couple(pr1(k,"a","b"),…)) :
# passer var("a")/var("b") comme X₁/Y₁ y provoquerait une capture (α-divergence ⇒
# « mineure ≠ antécédent »).  « A », « B » sont libres de toute collision.
def produit_cardinal_bien_defini(x="X", y="Y", a="A", b="B"):
    """⊢ (Card X = a et Card Y = b) ⇒ Card(X×Y) = produit_cardinal_binaire(a, b).

    Card(X×Y) ne dépend QUE de Card X et Card Y : le produit cardinal est une
    opération BIEN DÉFINIE sur les cardinaux (E.III.3.3).

    Preuve : sous Card X = a, Card Y = b, on a Eq(X, a) et Eq(Y, b)
    (equipotent_son_cardinal + réécriture S6) ; le keystone eq_produit_invariant
    donne Eq(X×Y, a×b) ; la Proposition 1 (sens direct) conclut
    Card(X×Y) = Card(a×b) = produit_cardinal_binaire(a, b)."""
    vX, vY, va, vb = _t(x), _t(y), _t(a), _t(b)
    cX, cY = cardinal(vX), cardinal(vY)
    XY = E.produit(vX, vY)
    ab = E.produit(va, vb)
    hyp = et(egal(cX, va), egal(cY, vb))
    h = N.assume(hyp)
    hX = conjonction_elim_gauche(h)                    # Card X = a
    hY = conjonction_elim_droite(h)                    # Card Y = b
    # Eq(X, a)  et  Eq(Y, b)
    eqXa = _eq_son_cardinal_reecrit(x, a)              # {Card X=a} ⊢ Eq(X, a)
    eqXa = N.modus_ponens(hX, N.loi_deduction(egal(cX, va), eqXa))   # décharge avec hX
    eqYb = _eq_son_cardinal_reecrit(y, b)              # {Card Y=b} ⊢ Eq(Y, b)
    eqYb = N.modus_ponens(hY, N.loi_deduction(egal(cY, vb), eqYb))
    # Eq(X×Y, a×b)  via le keystone
    inv = eq_produit_invariant("F", "G", vX, vY, va, vb)   # (Eq(X,a) et Eq(Y,b)) ⇒ Eq(X×Y, a×b)
    eqXYab = N.modus_ponens(conjonction_intro(eqXa, eqYb), inv)      # Eq(X×Y, a×b)
    # Card(X×Y) = Card(a×b)  via Proposition 1 (sens direct, version TERME)
    prop1 = _prop1_direct_t(XY, ab)                    # Eq(X×Y, a×b) ⇒ Card(X×Y)=Card(a×b)
    card_eq = N.modus_ponens(eqXYab, prop1)            # Card(X×Y) = Card(a×b) = a·b
    return N.loi_deduction(hyp, card_eq)


# ── (2) COMMUTATIVITÉ du produit cardinal ─────────────────────────────────────
def produit_cardinal_commutatif(x="X", y="Y"):
    """⊢ Card(X×Y) = Card(Y×X).   (= produit_cardinal_binaire(X,Y)
                                     = produit_cardinal_binaire(Y,X) ;
       commutativité a·b = b·a, Cor. de Prop. 5, E.III.3.3.)

    Preuve : eq_produit_commute ⊢ Eq(X×Y, Y×X) ; la Proposition 1 (sens direct)
    conclut Card(X×Y) = Card(Y×X)."""
    vX, vY = _t(x), _t(y)
    XY = E.produit(vX, vY)
    YX = E.produit(vY, vX)
    eq = eq_produit_commute(x, y)                      # Eq(X×Y, Y×X)  (clos)
    prop1 = _prop1_direct_t(XY, YX)                    # Eq(X×Y, Y×X) ⇒ Card(X×Y)=Card(Y×X)
    return N.modus_ponens(eq, prop1)                   # Card(X×Y) = Card(Y×X)


# ── (3) ASSOCIATIVITÉ — fondation : la bijection de réassociation ──────────────
# Associativité a·(b·c) = (a·b)·c repose sur  Eq((X×Y)×Z, X×(Y×Z)),  bijection
#   r : (X×Y)×Z → X×(Y×Z),   w ↦ (pr₁(pr₁w), (pr₂(pr₁w), pr₂w)).
# Son graphe est  R = graphe_terme((X×Y)×Z, (pr₁(pr₁k), (pr₂(pr₁k), pr₂k)), "k").
# MÊME PATRON que le SWAP (ensembles_produit_commute) en liants uniformes : les
# projections EXTERNES sur k utilisent les liants a,b ; les projections INTERNES sur
# pr₁k utilisent c,d (distincts) — aucune capture entre les deux niveaux.
#
# ÉTAT : THÉORÈME COMPLET — tous les paliers CERTIFIÉS ci-dessous (test_arith_cardinale) :
#   • reassoc_graphe_fonctionnel  (clos)         — R fonctionnel ;
#   • reassoc_graphe_domaine      (clos)         — dom R = (X×Y)×Z ;
#   • reassoc_graphe_valeur       {u∈(X×Y)×Z}    — R(u)=(pr₁(pr₁u),(pr₂(pr₁u),pr₂u)) ;
#   • reassoc_graphe_injective    (clos)         — injective_dans(R, (X×Y)×Z) [reconstruction
#       à DEUX niveaux : u=(pr₁u,pr₂u) en a,b ; pr₁u=(pr₁pr₁u,pr₂pr₁u) en c,d] ;
#   • reassoc_graphe_image        (clos)         — image(R,(X×Y)×Z)=X×(Y×Z) [surjectivité :
#       tout z=(e,(g,h))∈X×(Y×Z) a l'antécédent ((e,g),h)∈(X×Y)×Z ; décomposition
#       IMBRIQUÉE en liants e,m,g,h ≠ p,q (internes _inst_produit) ≠ a,b,c,d (projections)] ;
#   • reassoc_est_bijection       (clos)         — est_bijection_de(R, (X×Y)×Z, X×(Y×Z)) ;
#   • eq_produit_associatif       (clos)         — Eq((X×Y)×Z, X×(Y×Z)) (S5) ;
#   • produit_cardinal_associatif (clos)         — Card((X×Y)×Z)=Card(X×(Y×Z)) (Prop. 1).
# MÊME machinerie que le swap, généralisée au produit DOUBLE par la double reconstruction.
def _reassoc_terme(k="k"):
    """T = (pr₁(pr₁k), (pr₂(pr₁k), pr₂k))   (réassociation ((x,y),z) ↦ (x,(y,z))).

    Liants : projections EXTERNES sur k en a,b ; projections INTERNES sur pr₁k en
    c,d (≠ a,b) — pas de capture inter-niveaux, comme le swap en liants uniformes."""
    vk = var(k)
    pr1k = E.pr1(vk, "a", "b")            # pr₁ k
    pr2k = E.pr2(vk, "a", "b")            # pr₂ k
    pr1pr1k = E.pr1(pr1k, "c", "d")       # pr₁(pr₁ k)
    pr2pr1k = E.pr2(pr1k, "c", "d")       # pr₂(pr₁ k)
    return E.couple(pr1pr1k, E.couple(pr2pr1k, pr2k))


def _reassoc_graphe(x, y, z, k="k"):
    """R := graphe_terme((X×Y)×Z, (pr₁(pr₁k),(pr₂(pr₁k),pr₂k)), "k")."""
    A = E.produit(E.produit(_t(x), _t(y)), _t(z))
    return E.graphe_terme(A, _reassoc_terme(k), k)


def reassoc_graphe_fonctionnel(x="X", y="Y", z="Z"):
    """⊢ R est fonctionnel,  R = graphe de ((x,y),z)↦(x,(y,z)).   (cas C54, CLOS.)

    Application directe de graphe_terme_fonctionnel : le graphe d'une fonction
    définie par un terme est toujours fonctionnel (E.II.46)."""
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    A = E.produit(E.produit(_t(x), _t(y)), _t(z))
    return graphe_terme_fonctionnel(A, _reassoc_terme("k"), "k", "y")


def reassoc_graphe_domaine(x="X", y="Y", z="Z"):
    """⊢ dom(R) = (X×Y)×Z.   (la réassociation est définie sur tout (X×Y)×Z ; CLOS.)

    Application directe de graphe_terme_domaine au terme de réassociation."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    A = E.produit(E.produit(_t(x), _t(y)), _t(z))
    return graphe_terme_domaine(A, _reassoc_terme("k"), "k", "y", "z")


# ── (3.1) VALEUR de la réassociation : R(u) = (pr₁(pr₁u), (pr₂(pr₁u), pr₂u)) ───
def reassoc_graphe_valeur(x="X", y="Y", z="Z", u="u"):
    """{u ∈ (X×Y)×Z} ⊢ R(u) = (pr₁(pr₁u), (pr₂(pr₁u), pr₂u)).

    (u,T[u])∈R (couple) → u dans le domaine ; valeur_caracterisation (C46, sous
    « R fonctionnel ») donne T[u]=R(u) ; symétrie conclut.  Même recette que
    swap_graphe_valeur (graphe_terme_valeur ré-implémentée localement avec les
    liants a,b/c,d de _reassoc_terme)."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_couple_dans
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
    A = E.produit(E.produit(_t(x), _t(y)), _t(z))
    T = _reassoc_terme("k")
    xb = "k"
    F = E.graphe_terme(A, T, xb)
    vu = _t(u)
    Tu = subst_t(vu, xb, T)                                  # T[u]
    fu = E.valeur(F, vu)                                     # R(u)
    cpl = graphe_terme_couple_dans(A, T, u, xb, "t")         # {u∈(X×Y)×Z} ⊢ (u,T[u])∈R
    dom_membre = N.modus_ponens(cpl, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))
    vc = valeur_caracterisation(F, vu)                       # y libre
    vc_all = N.generalisation("y", vc)                       # (∀y)(((u,y)∈F)⇔(y=R(u)))
    vc_Tu = instancie(vc_all, Tu)                            # ((u,T[u])∈F) ⇔ (T[u]=R(u))
    Tu_fu = N.modus_ponens(cpl, equivalence_avant(vc_Tu))    # T[u]=R(u)
    fu_Tu = N.modus_ponens(Tu_fu, symetrie(Tu, fu))         # R(u)=T[u]
    fu_Tu = N.modus_ponens(reassoc_graphe_fonctionnel(x, y, z),
                           N.loi_deduction(E.est_fonctionnel(F), fu_Tu))
    fu_Tu = N.modus_ponens(dom_membre,
        N.loi_deduction(existe("y", appartient(E.couple(vu, var("y")), F)), fu_Tu))
    return fu_Tu                                             # {u∈(X×Y)×Z} ⊢ R(u)=T[u]


# ── (3.2) INJECTIVITÉ : injective_dans(R, (X×Y)×Z) ────────────────────────────
def reassoc_graphe_injective(x="X", y="Y", z="Z"):
    """⊢ injective_dans(R, (X×Y)×Z).   (la réassociation est injective sur (X×Y)×Z.)

    R(u)=(pr₁(pr₁u),(pr₂(pr₁u),pr₂u)), R(u')=idem (reassoc_graphe_valeur).  Sous
    R(u)=R(u') : double couple_egal_implique_composantes donne pr₁(pr₁u)=pr₁(pr₁u'),
    pr₂(pr₁u)=pr₂(pr₁u'), pr₂u=pr₂u'.  Or u=(pr₁u,pr₂u) (liants a,b) et
    pr₁u=(pr₁(pr₁u),pr₂(pr₁u)) (liants c,d ; reconstruction de pr₁u∈X×Y) ; deux
    congruences sur pr₁u puis sur u donnent u=u'.  UNIFORME en liants a,b/c,d."""
    from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (_membre_produit_egal_couple_ab,
                                           _membre_produit_pr1_ab)
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    vX, vY, vZ = _t(x), _t(y), _t(z)
    XY = E.produit(vX, vY)
    A = E.produit(XY, vZ)
    R = _reassoc_graphe(x, y, z)
    vu, vup = var("u"), var("up")
    # projections (liants a,b externes sur u ; c,d internes sur pr₁u)
    pr1u, pr2u = E.pr1(vu, "a", "b"), E.pr2(vu, "a", "b")
    pr1up, pr2up = E.pr1(vup, "a", "b"), E.pr2(vup, "a", "b")
    pr1pr1u, pr2pr1u = E.pr1(pr1u, "c", "d"), E.pr2(pr1u, "c", "d")
    pr1pr1up, pr2pr1up = E.pr1(pr1up, "c", "d"), E.pr2(pr1up, "c", "d")
    Tu = E.couple(pr1pr1u, E.couple(pr2pr1u, pr2u))           # R(u) = T[u]
    Tup = E.couple(pr1pr1up, E.couple(pr2pr1up, pr2up))       # R(u')
    hyp = et(et(appartient(vu, A), appartient(vup, A)),
             egal(E.valeur(R, vu), E.valeur(R, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈(X×Y)×Z
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈(X×Y)×Z
    val_eq = conjonction_elim_droite(h)                            # R(u)=R(u')
    Ru_T = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                reassoc_graphe_valeur(x, y, z, "u")))    # R(u)=T[u]
    Rup_T = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                  reassoc_graphe_valeur(x, y, z, "up")))  # R(u')=T[u']
    Tu_Ru = N.modus_ponens(Ru_T, symetrie(E.valeur(R, vu), Tu))    # T[u]=R(u)
    Tu_Tup = composer_egalites(composer_egalites(Tu_Ru, val_eq), Rup_T)  # T[u]=T[u']
    # outer composantes : pr₁(pr₁u)=pr₁(pr₁u')  et  (pr₂(pr₁u),pr₂u)=(pr₂(pr₁u'),pr₂u')
    outer = N.modus_ponens(Tu_Tup,
        couple_egal_implique_composantes(pr1pr1u, E.couple(pr2pr1u, pr2u),
                                         pr1pr1up, E.couple(pr2pr1up, pr2up)))
    eq_pr1pr1 = conjonction_elim_gauche(outer)                     # pr₁(pr₁u)=pr₁(pr₁u')
    eq_tail = conjonction_elim_droite(outer)                       # (pr₂(pr₁u),pr₂u)=(pr₂(pr₁u'),pr₂u')
    inner = N.modus_ponens(eq_tail,
        couple_egal_implique_composantes(pr2pr1u, pr2u, pr2pr1up, pr2up))
    eq_pr2pr1 = conjonction_elim_gauche(inner)                     # pr₂(pr₁u)=pr₂(pr₁u')
    eq_pr2 = conjonction_elim_droite(inner)                        # pr₂u=pr₂u'
    # reconstruction de pr₁u et pr₁u' (liants c,d) sous pr₁u∈X×Y
    pr1u_inXY = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                     _membre_produit_pr1_ab(XY, vZ, "u")))   # pr₁u∈X×Y
    pr1up_inXY = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                       _membre_produit_pr1_ab(XY, vZ, "up")))  # pr₁u'∈X×Y
    pr1u_rec = N.modus_ponens(pr1u_inXY, N.loi_deduction(appartient(pr1u, XY),
                                _membre_produit_egal_couple_ab(vX, vY, pr1u, "c", "d")))   # pr₁u=(pr₁pr₁u,pr₂pr₁u)
    pr1up_rec = N.modus_ponens(pr1up_inXY, N.loi_deduction(appartient(pr1up, XY),
                                _membre_produit_egal_couple_ab(vX, vY, pr1up, "c", "d")))  # pr₁u'=(pr₁pr₁u',pr₂pr₁u')
    # pr₁u = pr₁u' : congruences sur le couple (pr₁pr₁·, pr₂pr₁·)
    c1 = N.modus_ponens(eq_pr1pr1, congruence_terme(pr1pr1u, pr1pr1up,
                                                    E.couple(var("w"), pr2pr1u)))   # (pr₁pr₁u,pr₂pr₁u)=(pr₁pr₁u',pr₂pr₁u)
    c2 = N.modus_ponens(eq_pr2pr1, congruence_terme(pr2pr1u, pr2pr1up,
                                                    E.couple(pr1pr1up, var("w"))))  # (pr₁pr₁u',pr₂pr₁u)=(pr₁pr₁u',pr₂pr₁u')
    cpl_pr1 = composer_egalites(c1, c2)                           # (pr₁pr₁u,pr₂pr₁u)=(pr₁pr₁u',pr₂pr₁u')
    pr1u_eq = composer_egalites(composer_egalites(pr1u_rec, cpl_pr1),
                                N.modus_ponens(pr1up_rec,
                                    symetrie(pr1up, E.couple(pr1pr1up, pr2pr1up))))   # pr₁u=pr₁u'
    # u = u' : u=(pr₁u,pr₂u), congruences avec pr₁u=pr₁u' et pr₂u=pr₂u'
    u_rec = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                 _membre_produit_egal_couple_ab(XY, vZ, "u", "a", "b")))   # u=(pr₁u,pr₂u)
    up_rec = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                   _membre_produit_egal_couple_ab(XY, vZ, "up", "a", "b")))  # u'=(pr₁u',pr₂u')
    d1 = N.modus_ponens(pr1u_eq, congruence_terme(pr1u, pr1up, E.couple(var("w"), pr2u)))    # (pr₁u,pr₂u)=(pr₁u',pr₂u)
    d2 = N.modus_ponens(eq_pr2, congruence_terme(pr2u, pr2up, E.couple(pr1up, var("w"))))    # (pr₁u',pr₂u)=(pr₁u',pr₂u')
    rec_eq = composer_egalites(d1, d2)                            # (pr₁u,pr₂u)=(pr₁u',pr₂u')
    u_eq_up = composer_egalites(composer_egalites(u_rec, rec_eq),
                                N.modus_ponens(up_rec, symetrie(vup, E.couple(pr1up, pr2up))))
    body = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", body))    # injective_dans(R, (X×Y)×Z)


# ── (3.3) IMAGE : image(R, (X×Y)×Z) = X×(Y×Z)  (surjectivité) ─────────────────
def reassoc_graphe_image(x="X", y="Y", z="Z"):
    """⊢ image(R, (X×Y)×Z) = X×(Y×Z).   (réassociation surjective sur X×(Y×Z).)

    z∈R⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈R) ⇔[membre_graphe_terme] (∃t)(t∈A et z=T[t]).
    ⇒ : T[t]=(pr₁(pr₁t),(pr₂(pr₁t),pr₂t))∈X×(Y×Z) car pr₁(pr₁t)∈X, pr₂(pr₁t)∈Y
        (reconstruction de pr₁t∈X×Y, liants c,d) et pr₂t∈Z (liants a,b).
    ⇐ : tout z=(p,(q,r))∈X×(Y×Z) a l'antécédent t₀=((p,q),r)∈(X×Y)×Z avec
        T[t₀]=(pr₁(pr₁t₀),(pr₂(pr₁t₀),pr₂t₀))=(p,(q,r))=z."""
    from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (_membre_produit_pr1_ab,
        _membre_produit_pr2_ab, _projection_premiere_ab, _projection_seconde_ab,
        _couple_dans_produit_t, _inst_produit)
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
    from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
    vX, vY, vZ = _t(x), _t(y), _t(z)
    XY = E.produit(vX, vY)
    A = E.produit(XY, vZ)               # (X×Y)×Z
    YZ = E.produit(vY, vZ)
    XYZ = E.produit(vX, YZ)             # X×(Y×Z)
    T = _reassoc_terme("k")
    R = E.graphe_terme(A, T, "k")
    vz = var("z")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, R), A), vz)
    inner_x = et(appartient(var("x"), A), appartient(E.couple(var("x"), vz), R))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)          # z∈R⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈R)
    vt = var("t")
    Tt = subst_t(vt, "k", T)                                   # T[t]
    pr1t, pr2t = E.pr1(vt, "a", "b"), E.pr2(vt, "a", "b")
    pr1pr1t, pr2pr1t = E.pr1(pr1t, "c", "d"), E.pr2(pr1t, "c", "d")
    # ── ⇒ : z∈R⟨A⟩ ⇒ z∈X×(Y×Z) ──────────────────────────────────────────────
    bodyR = et(appartient(vt, A), appartient(E.couple(vt, vz), R))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                        # t∈A
    cpl_in = conjonction_elim_droite(hbR)                      # (t,z)∈R
    mem = membre_graphe_terme(A, T, "t", "z", "k", "yb")       # ((t,z)∈R)⇔(t∈A et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))  # z=T[t]
    pr1t_inXY = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                     _membre_produit_pr1_ab(XY, vZ, "t")))   # pr₁t∈X×Y
    pr2t_inZ = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                    _membre_produit_pr2_ab(XY, vZ, "t")))    # pr₂t∈Z
    pr1pr1t_inX = N.modus_ponens(pr1t_inXY, N.loi_deduction(appartient(pr1t, XY),
                                    _membre_produit_pr1_ab(vX, vY, pr1t, "c", "d")))   # pr₁(pr₁t)∈X
    pr2pr1t_inY = N.modus_ponens(pr1t_inXY, N.loi_deduction(appartient(pr1t, XY),
                                    _membre_produit_pr2_ab(vX, vY, pr1t, "c", "d")))   # pr₂(pr₁t)∈Y
    # (pr₂(pr₁t), pr₂t) ∈ Y×Z
    tail_in_YZ = N.modus_ponens(conjonction_intro(pr2pr1t_inY, pr2t_inZ),
                                _couple_dans_produit_t(pr2pr1t, pr2t, vY, vZ))   # (pr₂pr₁t,pr₂t)∈Y×Z
    # (pr₁(pr₁t), (pr₂(pr₁t),pr₂t)) ∈ X×(Y×Z)
    Tt_in_XYZ = N.modus_ponens(conjonction_intro(pr1pr1t_inX, tail_in_YZ),
                               _couple_dans_produit_t(pr1pr1t, E.couple(pr2pr1t, pr2t), vX, YZ))
    z_in_XYZ = N.modus_ponens(Tt_in_XYZ, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), XYZ)))))
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_XYZ), "t")   # (∃t)(...) ⇒ z∈X×(Y×Z)
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)            # z∈R⟨A⟩ ⇒ z∈X×(Y×Z)
    # ── ⇐ : z∈X×(Y×Z) ⇒ z∈R⟨A⟩ ──────────────────────────────────────────────
    # liants de décomposition e(X), m(Y×Z), g(Y), h(Z) — TOUS ≠ p,q (binders internes
    # de _inst_produit/_couple_dans_produit_t) et ≠ a,b,c,d (liants des projections).
    # z∈X×(Y×Z) ⇔ (∃e)(∃m)((z=(e,m) et e∈X) et m∈Y×Z)
    prod_car0 = _inst_produit(vX, YZ, vz)                            # liants p,q internes
    inner_q = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vX)),
                 appartient(var("q"), YZ))
    ren_q = alpha_existe("q", "m", inner_q)                          # (∃q)…q… ⇔ (∃m)…m…
    inner_pm = et(et(egal(vz, E.couple(var("p"), var("m"))), appartient(var("p"), vX)),
                  appartient(var("m"), YZ))
    ren_p = alpha_existe("p", "e", existe("m", inner_pm))            # (∃p)(∃m)… ⇔ (∃e)(∃m)…
    ren_q_under_p = congruence_existe(ren_q, "p")                    # (∃p)(∃q)… ⇔ (∃p)(∃m)…
    prod_car = equivalence_transitivite(prod_car0,
                  equivalence_transitivite(ren_q_under_p, ren_p))    # z∈X×(Y×Z) ⇔ (∃e)(∃m)bodyM
    ve, vm = var("e"), var("m")
    bodyM = et(et(egal(vz, E.couple(ve, vm)), appartient(ve, vX)), appartient(vm, YZ))
    hM = N.assume(bodyM)
    z_eq_em = conjonction_elim_gauche(conjonction_elim_gauche(hM))   # z=(e,m)
    e_in_X = conjonction_elim_droite(conjonction_elim_gauche(hM))   # e∈X
    m_in_YZ = conjonction_elim_droite(hM)                           # m∈Y×Z
    # m∈Y×Z ⇔ (∃g)(∃h)((m=(g,h) et g∈Y) et h∈Z)
    prod_car_m0 = _inst_produit(vY, vZ, vm)                          # liants p,q internes
    inner_qm = et(et(egal(vm, E.couple(var("p"), var("q"))), appartient(var("p"), vY)),
                  appartient(var("q"), vZ))
    ren_hm = alpha_existe("q", "h", inner_qm)                        # (∃q)…q… ⇔ (∃h)…h…
    ren_hm_p = congruence_existe(ren_hm, "p")                        # (∃p)(∃q)… ⇔ (∃p)(∃h)…
    inner_ph_m = et(et(egal(vm, E.couple(var("p"), var("h"))), appartient(var("p"), vY)),
                    appartient(var("h"), vZ))
    ren_gm = alpha_existe("p", "g", existe("h", inner_ph_m))         # (∃p)(∃h)… ⇔ (∃g)(∃h)…
    prod_car_m = equivalence_transitivite(prod_car_m0,
                    equivalence_transitivite(ren_hm_p, ren_gm))      # m∈Y×Z ⇔ (∃g)(∃h)bodyGH
    vg, vh = var("g"), var("h")
    bodyGH = et(et(egal(vm, E.couple(vg, vh)), appartient(vg, vY)), appartient(vh, vZ))
    ex_gh = N.modus_ponens(m_in_YZ, equivalence_avant(prod_car_m))   # (∃g)(∃h)bodyGH  [sous bodyM]
    hGH = N.assume(bodyGH)
    m_eq_gh = conjonction_elim_gauche(conjonction_elim_gauche(hGH))  # m=(g,h)
    g_in_Y = conjonction_elim_droite(conjonction_elim_gauche(hGH))  # g∈Y
    h_in_Z = conjonction_elim_droite(hGH)                           # h∈Z
    # antécédent t₀ = ((e,g), h) ∈ (X×Y)×Z
    eg = E.couple(ve, vg)
    t0 = E.couple(eg, vh)
    eg_in_XY = N.modus_ponens(conjonction_intro(e_in_X, g_in_Y),
                              _couple_dans_produit_t(ve, vg, vX, vY))   # (e,g)∈X×Y
    t0_in_A = N.modus_ponens(conjonction_intro(eg_in_XY, h_in_Z),
                             _couple_dans_produit_t(eg, vh, XY, vZ))     # ((e,g),h)∈(X×Y)×Z
    Tt0 = subst_t(t0, "k", T)                                       # T[t₀]
    # T[t₀] = (e, (g, h))  : calcul des projections de t₀
    pr1t0 = E.pr1(t0, "a", "b")
    pr2t0 = E.pr2(t0, "a", "b")
    pr1t0_eq = _projection_premiere_ab(eg, vh, "a", "b")           # pr₁t₀ = (e,g)
    pr2t0_eq = _projection_seconde_ab(eg, vh, "a", "b")           # pr₂t₀ = h
    pr1pr1t0 = E.pr1(pr1t0, "c", "d")
    pr2pr1t0 = E.pr2(pr1t0, "c", "d")
    # pr₁(pr₁t₀) = pr₁((e,g)) = e
    cong_pr1 = N.modus_ponens(pr1t0_eq, congruence_terme(pr1t0, eg, E.pr1(var("w"), "c", "d")))
    pr1pr1t0_eq = composer_egalites(cong_pr1, _projection_premiere_ab(ve, vg, "c", "d"))    # pr₁(pr₁t₀)=e
    cong_pr2 = N.modus_ponens(pr1t0_eq, congruence_terme(pr1t0, eg, E.pr2(var("w"), "c", "d")))
    pr2pr1t0_eq = composer_egalites(cong_pr2, _projection_seconde_ab(ve, vg, "c", "d"))     # pr₂(pr₁t₀)=g
    # T[t₀] = (pr₁pr₁t₀, (pr₂pr₁t₀, pr₂t₀)) → (e, (g, h))
    s1 = N.modus_ponens(pr1pr1t0_eq, congruence_terme(pr1pr1t0, ve,
                            E.couple(var("w"), E.couple(pr2pr1t0, pr2t0))))   # T[t₀]=(e,(pr₂pr₁t₀,pr₂t₀))
    s2 = N.modus_ponens(pr2pr1t0_eq, congruence_terme(pr2pr1t0, vg,
                            E.couple(ve, E.couple(var("w"), pr2t0))))         # =(e,(g,pr₂t₀))
    s3 = N.modus_ponens(pr2t0_eq, congruence_terme(pr2t0, vh,
                            E.couple(ve, E.couple(vg, var("w")))))            # =(e,(g,h))
    Tt0_eq_egh = composer_egalites(composer_egalites(s1, s2), s3)            # T[t₀]=(e,(g,h))
    # z = (e,m) = (e,(g,h))  →  z = T[t₀]
    m_to_gh = N.modus_ponens(m_eq_gh, congruence_terme(vm, E.couple(vg, vh),
                            E.couple(ve, var("w"))))                          # (e,m)=(e,(g,h))
    z_eq_egh = composer_egalites(z_eq_em, m_to_gh)                           # z=(e,(g,h))
    egh_eq_Tt0 = N.modus_ponens(Tt0_eq_egh,
                                symetrie(Tt0, E.couple(ve, E.couple(vg, vh))))  # (e,(g,h))=T[t₀]
    z_eq_Tt0 = composer_egalites(z_eq_egh, egh_eq_Tt0)                       # z=T[t₀]
    # ((t₀, z) ∈ R) directement via l'axiome du graphe (témoins k:=t₀, yb:=z)
    ax_R = N.axiome(E.theorie_graphe_terme(A, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(A, T, "k", "yb", "zz"))   # (∀zz)(zz∈R ⇔ (∃k)(∃yb)body)
    cpl_z = E.couple(t0, vz)                                       # (t₀, z)
    car_z = instancie(ax_R, cpl_z)                                # (t₀,z)∈R ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))), appartient(var("k"), A)),
                 egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)                          # (k|→t₀) body  (libre yb)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_A), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))      # (∃yb)body[k:=t₀]
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))  # (∃k)(∃yb)body
    cpl0_in = N.modus_ponens(ex_kyb, equivalence_arriere(car_z))   # (t₀,z)∈R
    wit_body = conjonction_intro(t0_in_A, cpl0_in)                # t₀∈A et (t₀,z)∈R
    ex_t = N.modus_ponens(wit_body, N.s5(bodyR, t0, "t"))         # (∃t)(t∈A et (t,z)∈R)
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))  # z∈R⟨A⟩
    # décharge des existentiels imbriqués : (∃g)(∃h)bodyGH ⇒ z∈R⟨A⟩
    in_img_gh = N.loi_deduction(bodyGH, in_img)
    in_img_from_m = N.modus_ponens(ex_gh,                          # sous bodyM (donne m∈Y×Z)
        existe_elimination(existe_elimination(in_img_gh, "h"), "g"))
    bwd_inner = existe_elimination(existe_elimination(
        N.loi_deduction(bodyM, in_img_from_m), "m"), "e")          # (∃e)(∃m)bodyM ⇒ z∈R⟨A⟩
    bwd_full = syllogisme(equivalence_avant(prod_car), bwd_inner)  # z∈X×(Y×Z) ⇒ z∈R⟨A⟩
    # ── double inclusion → egalite_par_extension ─────────────────────────────
    equiv_z = conjonction_intro(fwd_full, bwd_full)              # z∈R⟨A⟩ ⇔ z∈X×(Y×Z)
    char_u = N.generalisation("z", equiv_z)
    selfXYZ = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, XYZ)), a_implique_a(appartient(vz, XYZ))))
    return egalite_par_extension(char_u, selfXYZ, E.image(R, A), XYZ, "z")


# ── (3.4) BIJECTION + Eq((X×Y)×Z, X×(Y×Z)) ────────────────────────────────────
def reassoc_est_bijection(x="X", y="Y", z="Z"):
    """⊢ est_bijection_de(R, (X×Y)×Z, X×(Y×Z)).   (R = ((x,y),z)↦(x,(y,z)) bijection.)

    Les 4 conjoints : fonctionnel, domaine (X×Y)×Z, injectif, image X×(Y×Z).
    est_bijection_de = ((func et dom) et (inj et img))."""
    func = reassoc_graphe_fonctionnel(x, y, z)   # est_fonctionnel(R)
    dom = reassoc_graphe_domaine(x, y, z)        # dom R = (X×Y)×Z
    inj = reassoc_graphe_injective(x, y, z)      # injective_dans(R, (X×Y)×Z)
    img = reassoc_graphe_image(x, y, z)          # image(R, (X×Y)×Z) = X×(Y×Z)
    bijective = conjonction_intro(inj, img)      # est_bijective(R, (X×Y)×Z, X×(Y×Z))
    return conjonction_intro(conjonction_intro(func, dom), bijective)


def eq_produit_associatif(x="X", y="Y", z="Z"):
    """⊢ Eq((X×Y)×Z, X×(Y×Z)).   (associativité du produit à équipotence près, §III.3.)

    Témoin = le graphe de réassociation R ; S5 sur est_bijection_de(F,·,·) donne
    (∃F)bij = Eq((X×Y)×Z, X×(Y×Z))."""
    vX, vY, vZ = _t(x), _t(y), _t(z)
    A = E.produit(E.produit(vX, vY), vZ)
    XYZ = E.produit(vX, E.produit(vY, vZ))
    R = _reassoc_graphe(x, y, z)
    bij = reassoc_est_bijection(x, y, z)         # est_bijection_de(R, (X×Y)×Z, X×(Y×Z))
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), A, XYZ), R, "F"))


# ── (3.5) ASSOCIATIVITÉ DU PRODUIT CARDINAL : Card((X×Y)×Z) = Card(X×(Y×Z)) ────
def produit_cardinal_associatif(x="X", y="Y", z="Z"):
    """⊢ Card((X×Y)×Z) = Card(X×(Y×Z)).   (associativité a·(b·c) = (a·b)·c, E.III.3.3.)

    Eq((X×Y)×Z, X×(Y×Z)) (réassociation) ; la Proposition 1 (sens direct, version
    TERME _prop1_direct_t) conclut Card((X×Y)×Z) = Card(X×(Y×Z))."""
    vX, vY, vZ = _t(x), _t(y), _t(z)
    A = E.produit(E.produit(vX, vY), vZ)
    XYZ = E.produit(vX, E.produit(vY, vZ))
    eq = eq_produit_associatif(x, y, z)          # Eq((X×Y)×Z, X×(Y×Z))
    prop1 = _prop1_direct_t(A, XYZ)              # Eq((X×Y)×Z, X×(Y×Z)) ⇒ Card=Card
    return N.modus_ponens(eq, prop1)             # Card((X×Y)×Z) = Card(X×(Y×Z))


__all__ = ["produit_cardinal_binaire", "produit_cardinal_bien_defini",
           "produit_cardinal_commutatif",
           "reassoc_graphe_fonctionnel", "reassoc_graphe_domaine",
           "reassoc_graphe_valeur", "reassoc_graphe_injective",
           "reassoc_graphe_image", "reassoc_est_bijection",
           "eq_produit_associatif", "produit_cardinal_associatif"]
