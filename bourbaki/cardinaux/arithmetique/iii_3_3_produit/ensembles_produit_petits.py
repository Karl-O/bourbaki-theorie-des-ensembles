"""§III.3.3 — Identités du produit cardinal avec 0 et 1 :  a·1 = a  et  a·0 = 0.

Cardinaux particuliers (E.III.3.3, début ; cas dégénérés des Cor. de Prop. 5/6) :
  • 1 = Card({∅})   (cardinal d'un singleton) ;
  • 0 = Card(∅)     (cardinal du vide).

Deux résultats, chacun CERTIFIÉ par le noyau abrégé et testé (test_produit_petits) :

(1)  a·1 = a  —  produit_cardinal_un(A) ⊢ Card(A×{∅}) = Card(A).
     Application témoin = la PROJECTION  p : A×{∅} → A,  (x,∅) ↦ pr₁(x,∅) = x.
     Son graphe est  P := graphe_terme(A×{∅}, pr₁k, "k").  On montre que P est :
       • FONCTIONNEL    (graphe_terme_fonctionnel) ;
       • de DOMAINE A×{∅}  (graphe_terme_domaine) ;
       • INJECTIF sur A×{∅}  (pr₁u=pr₁u' ⇒ u=u' : tout u∈A×{∅} se reconstruit
         u=(pr₁u,pr₂u) avec pr₂u=∅ — la 2ᵉ coordonnée est forcée dans le
         singleton {∅}, donc pr₂u=pr₂u'=∅ ; congruences ⇒ u=u') ;
       • d'IMAGE = A  (surjectivité : tout z∈A a l'antécédent (z,∅)∈A×{∅} avec
         P((z,∅))=pr₁(z,∅)=z).
     Les 4 conjoints donnent est_bijection_de(P, A×{∅}, A), d'où Eq(A×{∅}, A)
     (S5), puis Card(A×{∅})=Card(A) (Proposition 1, version TERME _prop1_direct_t).

(2)  a·0 = 0  —  produit_cardinal_zero(A) ⊢ Card(A×∅) = Card(∅).
     A×∅=∅ (produit_vide_si avec B=∅), puis congruence sur Card.

LIANTS : projections en a,b uniformes (alignées sur graphe_terme_valeur local),
recette identique au swap (ensembles_produit_commute) ; surs u,v,z,t,m,A.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, appartient, existe,
                     subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites,
                                      congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (existe_elimination,
                                      congruence_existe, alpha_existe)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (couple_egal_implique_composantes,
                                 singleton_membre)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (membre_graphe_terme,
                                          graphe_terme_fonctionnel)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_couple_dans, graphe_terme_domaine
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (couple_dans_produit_ssi,
                                    produit_vide_si)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_commute import (
    _membre_produit_egal_couple_ab, _membre_produit_pr1_ab, _membre_produit_pr2_ab,
    _projection_premiere_ab, _couple_dans_produit_t, _inst_produit)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
#  (2)  a·0 = 0  :  Card(A×∅) = Card(∅)   —   le cas simple, livré d'abord
# ══════════════════════════════════════════════════════════════════════════════
def produit_vide_droit(a="A"):
    """⊢ A×∅ = ∅.   (le produit par le vide est vide ; cas B=∅ de Prop. 3.)

    produit_vide_si(A,∅) ⊢ (A=∅ ou ∅=∅) ⇒ A×∅=∅ ; ∅=∅ (réflexivité) donne la
    disjonction de droite, d'où A×∅=∅ par modus ponens."""
    vA = _t(a)
    # produit_vide_si(A,B) ⊢ (A=∅ ou B=∅) ⇒ A×B=∅  (B nom de variable) ; on
    # généralise en B puis on instancie B:=∅ pour obtenir la version TERME ∅
    # (passer E.VIDE directement comme b enveloppe ∅ dans un var fautif).
    imp_gen = N.generalisation("B", produit_vide_si(a, "B"))           # (∀B)((A=∅ ou B=∅)⇒A×B=∅)
    imp = instancie(imp_gen, E.VIDE)                                   # (A=∅ ou ∅=∅) ⇒ A×∅=∅
    vide_eq = egal(E.VIDE, E.VIDE)
    A_eq = egal(vA, E.VIDE)
    # ∅=∅  →  (∅=∅ ou A=∅)  →  (A=∅ ou ∅=∅)
    or1 = N.modus_ponens(N.reflexivite(E.VIDE), N.s2(vide_eq, A_eq))   # (∅=∅ ou A=∅)
    disj = N.modus_ponens(or1, N.s3(vide_eq, A_eq))                    # (A=∅ ou ∅=∅)
    return N.modus_ponens(disj, imp)                                   # A×∅ = ∅


def produit_cardinal_zero(a="A"):
    """⊢ Card(A×∅) = Card(∅).   (a·0 = 0, E.III.3.3 ; 0 = Card(∅).)

    A×∅=∅ (produit_vide_droit) ; la congruence S6/Leibniz sur Card transporte
    l'égalité au cardinal : Card(A×∅) = Card(∅)."""
    vA = _t(a)
    AB = E.produit(vA, E.VIDE)
    eq_ens = produit_vide_droit(a)                       # A×∅ = ∅
    # congruence sur le terme Card(·) : (A×∅=∅) ⇒ Card(A×∅)=Card(∅)
    return N.modus_ponens(eq_ens, congruence_terme(AB, E.VIDE, cardinal(var("w"))))


# ══════════════════════════════════════════════════════════════════════════════
#  (1)  a·1 = a  :  Card(A×{∅}) = Card(A)   via la projection (x,∅)↦x
# ══════════════════════════════════════════════════════════════════════════════
# Le graphe-témoin  P := graphe_terme(A×{∅}, pr₁k, "k")  de la projection p₁.
def _proj_terme(k="k"):
    """T = pr₁k   (la première projection, liants internes a,b ≠ k)."""
    return E.pr1(var(k), "a", "b")


def _proj_graphe(a, k="k"):
    """P := graphe_terme(A×{∅}, pr₁k, "k")   (graphe de (x,∅)↦pr₁(x,∅)=x)."""
    A1 = E.produit(_t(a), E.singleton(E.VIDE))
    return E.graphe_terme(A1, _proj_terme(k), k)


def proj_graphe_fonctionnel(a="A"):
    """⊢ P est fonctionnel,  P = graphe de (x,∅)↦pr₁(x,∅).   (cas C54, CLOS.)"""
    A1 = E.produit(_t(a), E.singleton(E.VIDE))
    return graphe_terme_fonctionnel(A1, _proj_terme("k"), "k", "y")


def proj_graphe_domaine(a="A"):
    """⊢ dom(P) = A×{∅}.   (la projection est définie sur tout A×{∅} ; CLOS.)"""
    A1 = E.produit(_t(a), E.singleton(E.VIDE))
    return graphe_terme_domaine(A1, _proj_terme("k"), "k", "y", "z")


def proj_graphe_valeur(a="A", u="u"):
    """{u ∈ A×{∅}} ⊢ P(u) = pr₁u.   (la valeur de la projection en u, liants a,b.)

    Même recette que swap_graphe_valeur : (u,T[u])∈P (graphe_terme_couple_dans) →
    u dans le domaine ; valeur_caracterisation (C46, sous « P fonctionnel ») donne
    T[u]=P(u) ; symétrie conclut.  T[u]=pr₁u en liants a,b."""
    A1 = E.produit(_t(a), E.singleton(E.VIDE))
    T = _proj_terme("k")
    xb = "k"
    F = E.graphe_terme(A1, T, xb)
    vu = _t(u)
    Tu = subst_t(vu, xb, T)                                  # T[u] = pr₁u
    fu = E.valeur(F, vu)                                     # P(u)
    cpl = graphe_terme_couple_dans(A1, T, u, xb, "t")        # {u∈A×{∅}} ⊢ (u,T[u])∈P
    dom_membre = N.modus_ponens(cpl, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))
    vc = valeur_caracterisation(F, vu)                       # y libre
    vc_all = N.generalisation("y", vc)                       # (∀y)(((u,y)∈P)⇔(y=P(u)))
    vc_Tu = instancie(vc_all, Tu)                            # ((u,T[u])∈P) ⇔ (T[u]=P(u))
    Tu_fu = N.modus_ponens(cpl, equivalence_avant(vc_Tu))    # T[u]=P(u)
    fu_Tu = N.modus_ponens(Tu_fu, symetrie(Tu, fu))         # P(u)=T[u]
    fu_Tu = N.modus_ponens(proj_graphe_fonctionnel(a),
                           N.loi_deduction(E.est_fonctionnel(F), fu_Tu))
    fu_Tu = N.modus_ponens(dom_membre,
        N.loi_deduction(existe("y", appartient(E.couple(vu, var("y")), F)), fu_Tu))
    return fu_Tu                                             # {u∈A×{∅}} ⊢ P(u)=pr₁u


# ── La 2ᵉ coordonnée est forcée : {u ∈ A×{∅}} ⊢ pr₂u = ∅ ──────────────────────
def _pr2_egal_vide(a="A", z="z"):
    """{z ∈ A×{∅}} ⊢ pr₂z[a,b] = ∅.

    pr₂z∈{∅} (_membre_produit_pr2_ab, le 2ᵉ facteur est {∅}) ; singleton_membre
    (∈{∅} ⇔ =∅) conclut pr₂z=∅."""
    vA = _t(a)
    vz = _t(z)
    pr2z = E.pr2(vz, "a", "b")
    sing = E.singleton(E.VIDE)
    pr2_in = _membre_produit_pr2_ab(vA, sing, z)            # {z∈A×{∅}} ⊢ pr₂z∈{∅}
    # pr₂z∈{∅} ⇔ pr₂z=∅  (singleton_membre)
    return N.modus_ponens(pr2_in, equivalence_avant(singleton_membre(pr2z, E.VIDE)))  # {z∈A×{∅}} ⊢ pr₂z=∅


# ── (1.a) INJECTIVITÉ : injective_dans(P, A×{∅}) ──────────────────────────────
def proj_graphe_injective(a="A"):
    """⊢ injective_dans(P, A×{∅}).   ((x,∅)↦pr₁(x,∅) injective sur A×{∅}.)

    P(u)=pr₁u, P(u')=pr₁u' (proj_graphe_valeur).  Sous P(u)=P(u') : pr₁u=pr₁u'.
    Or u=(pr₁u,pr₂u), u'=(pr₁u',pr₂u') (reconstruction, liants a,b) et
    pr₂u=∅=pr₂u' (la 2ᵉ coordonnée est forcée dans {∅}) ; deux congruences donnent
    u=u'.  UNIFORME en liants a,b — comme le swap."""
    vA = _t(a)
    sing = E.singleton(E.VIDE)
    A1 = E.produit(vA, sing)
    P = _proj_graphe(a)
    vu, vup = var("u"), var("up")
    pr1u, pr2u = E.pr1(vu, "a", "b"), E.pr2(vu, "a", "b")
    pr1up, pr2up = E.pr1(vup, "a", "b"), E.pr2(vup, "a", "b")
    hyp = et(et(appartient(vu, A1), appartient(vup, A1)),
             egal(E.valeur(P, vu), E.valeur(P, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈A×{∅}
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈A×{∅}
    val_eq = conjonction_elim_droite(h)                            # P(u)=P(u')
    # pr₁u=P(u), pr₁u'=P(u')
    Pu_pr1 = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A1),
                                                  proj_graphe_valeur(a, "u")))     # P(u)=pr₁u
    Pup_pr1 = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A1),
                                                    proj_graphe_valeur(a, "up")))  # P(u')=pr₁u'
    pr1u_Pu = N.modus_ponens(Pu_pr1, symetrie(E.valeur(P, vu), pr1u))   # pr₁u=P(u)
    eq_pr1 = composer_egalites(composer_egalites(pr1u_Pu, val_eq), Pup_pr1)  # pr₁u=pr₁u'
    # pr₂u=∅=pr₂u'  →  pr₂u=pr₂u'
    pr2u_vide = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A1),
                                                     _pr2_egal_vide(a, "u")))      # pr₂u=∅
    pr2up_vide = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A1),
                                                       _pr2_egal_vide(a, "up")))   # pr₂u'=∅
    eq_pr2 = composer_egalites(pr2u_vide,
                               N.modus_ponens(pr2up_vide, symetrie(pr2up, E.VIDE)))  # pr₂u=pr₂u'
    # reconstruction u=(pr₁u,pr₂u), u'=(pr₁u',pr₂u')
    u_rec = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A1),
                                _membre_produit_egal_couple_ab(vA, sing, "u", "a", "b")))    # u=(pr₁u,pr₂u)
    up_rec = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A1),
                                _membre_produit_egal_couple_ab(vA, sing, "up", "a", "b")))   # u'=(pr₁u',pr₂u')
    c1 = N.modus_ponens(eq_pr1, congruence_terme(pr1u, pr1up, E.couple(var("w"), pr2u)))   # (pr₁u,pr₂u)=(pr₁u',pr₂u)
    c2 = N.modus_ponens(eq_pr2, congruence_terme(pr2u, pr2up, E.couple(pr1up, var("w"))))  # (pr₁u',pr₂u)=(pr₁u',pr₂u')
    rec_eq = composer_egalites(c1, c2)                            # (pr₁u,pr₂u)=(pr₁u',pr₂u')
    u_eq_up = composer_egalites(composer_egalites(u_rec, rec_eq),
                                N.modus_ponens(up_rec, symetrie(vup, E.couple(pr1up, pr2up))))
    body = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", body))    # injective_dans(P, A×{∅})


# ── (1.b) IMAGE : image(P, A×{∅}) = A  (surjectivité) ─────────────────────────
def proj_graphe_image(a="A"):
    """⊢ image(P, A×{∅}) = A.   ((x,∅)↦pr₁(x,∅) surjective de A×{∅} sur A.)

    z∈P⟨A×{∅}⟩ ⇔ (∃t)(t∈A×{∅} et (t,z)∈P) ⇔[membre_graphe_terme]
                (∃t)(t∈A×{∅} et z=T[t]), T[t]=pr₁t.
    ⇒ : pr₁t∈A (_membre_produit_pr1_ab) donc z=pr₁t∈A.
    ⇐ : tout z∈A a l'antécédent t₀=(z,∅)∈A×{∅} avec T[t₀]=pr₁(z,∅)=z."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension as _ext
    vA = _t(a)
    sing = E.singleton(E.VIDE)
    A1 = E.produit(vA, sing)             # A×{∅}
    T = _proj_terme("k")                 # pr₁k
    P = E.graphe_terme(A1, T, "k")
    vz = var("z")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, P), A1), vz)
    inner_x = et(appartient(var("x"), A1), appartient(E.couple(var("x"), vz), P))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)          # z∈P⟨A×{∅}⟩ ⇔ (∃t)(t∈A×{∅} et (t,z)∈P)
    vt = var("t")
    Tt = subst_t(vt, "k", T)                                   # T[t] = pr₁t
    pr1t = E.pr1(vt, "a", "b")
    # ── ⇒ : z∈P⟨A×{∅}⟩ ⇒ z∈A ─────────────────────────────────────────────────
    bodyR = et(appartient(vt, A1), appartient(E.couple(vt, vz), P))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                        # t∈A×{∅}
    cpl_in = conjonction_elim_droite(hbR)                      # (t,z)∈P
    mem = membre_graphe_terme(A1, T, "t", "z", "k", "yb")      # ((t,z)∈P)⇔(t∈A×{∅} et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))  # z=T[t]=pr₁t
    pr1t_inA = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A1),
                                                    _membre_produit_pr1_ab(vA, sing, "t")))   # pr₁t∈A
    z_in_A = N.modus_ponens(pr1t_inA, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), vA)))))
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_A), "t")     # (∃t)(...) ⇒ z∈A
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)           # z∈P⟨A×{∅}⟩ ⇒ z∈A
    # ── ⇐ : z∈A ⇒ z∈P⟨A×{∅}⟩ ──────────────────────────────────────────────────
    hz = N.assume(appartient(vz, vA))                           # z∈A
    # antécédent t₀=(z,∅) ∈ A×{∅}  ;  ∅∈{∅}  via  (∅∈{∅}⇔∅=∅) + réflexivité
    vide_in_sing = N.modus_ponens(N.reflexivite(E.VIDE),
                                  equivalence_arriere(singleton_membre(E.VIDE, E.VIDE)))  # ∅∈{∅}
    t0 = E.couple(vz, E.VIDE)
    t0_in_A = N.modus_ponens(conjonction_intro(hz, vide_in_sing),
                             _couple_dans_produit_t(vz, E.VIDE, vA, sing))   # (z,∅)∈A×{∅}
    Tt0 = subst_t(t0, "k", T)                                   # T[t₀]=pr₁(z,∅)
    pr1t0 = E.pr1(t0, "a", "b")
    pr1t0_eq = _projection_premiere_ab(vz, E.VIDE, "a", "b")    # pr₁(z,∅)=z
    z_eq_Tt0 = N.modus_ponens(pr1t0_eq, symetrie(pr1t0, vz))    # z=T[t₀]
    # ((t₀,z) ∈ P) via l'axiome du graphe (témoins k:=t₀, yb:=z)
    ax_P = N.axiome(E.theorie_graphe_terme(A1, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(A1, T, "k", "yb", "zz"))   # (∀zz)(zz∈P ⇔ (∃k)(∃yb)body)
    cpl_z = E.couple(t0, vz)                                    # (t₀, z)
    car_z = instancie(ax_P, cpl_z)                             # (t₀,z)∈P ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))), appartient(var("k"), A1)),
                 egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)                        # (k|→t₀) body  (libre yb)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_A), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))    # (∃yb)body[k:=t₀]
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))  # (∃k)(∃yb)body
    cpl0_in = N.modus_ponens(ex_kyb, equivalence_arriere(car_z))   # (t₀,z)∈P
    wit_body = conjonction_intro(t0_in_A, cpl0_in)            # t₀∈A×{∅} et (t₀,z)∈P
    ex_t = N.modus_ponens(wit_body, N.s5(bodyR, t0, "t"))      # (∃t)(t∈A×{∅} et (t,z)∈P)
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))  # z∈P⟨A×{∅}⟩
    bwd_full = N.loi_deduction(appartient(vz, vA), in_img)     # z∈A ⇒ z∈P⟨A×{∅}⟩
    # ── double inclusion → egalite_par_extension ─────────────────────────────
    equiv_z = conjonction_intro(fwd_full, bwd_full)           # z∈P⟨A×{∅}⟩ ⇔ z∈A
    char_u = N.generalisation("z", equiv_z)
    selfA = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, vA)), a_implique_a(appartient(vz, vA))))
    return _ext(char_u, selfA, E.image(P, A1), vA, "z")


# ── (1.c) BIJECTION + Eq(A×{∅}, A) ────────────────────────────────────────────
def proj_est_bijection(a="A"):
    """⊢ est_bijection_de(P, A×{∅}, A).   (P = (x,∅)↦x bijection A×{∅}→A.)

    Les 4 conjoints : fonctionnel, domaine A×{∅}, injectif, image A.
    est_bijection_de = ((func et dom) et (inj et img))."""
    func = proj_graphe_fonctionnel(a)     # est_fonctionnel(P)
    dom = proj_graphe_domaine(a)          # dom P = A×{∅}
    inj = proj_graphe_injective(a)        # injective_dans(P, A×{∅})
    img = proj_graphe_image(a)            # image(P, A×{∅}) = A
    bijective = conjonction_intro(inj, img)
    return conjonction_intro(conjonction_intro(func, dom), bijective)


def eq_produit_un(a="A"):
    """⊢ Eq(A×{∅}, A).   (le produit par un singleton est équipotent à A, §III.3.)

    Témoin = le graphe P de la projection ; S5 sur est_bijection_de(F,·,·) donne
    (∃F)bij = Eq(A×{∅}, A)."""
    vA = _t(a)
    A1 = E.produit(vA, E.singleton(E.VIDE))
    P = _proj_graphe(a)
    bij = proj_est_bijection(a)            # est_bijection_de(P, A×{∅}, A)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), A1, vA), P, "F"))


def produit_cardinal_un(a="A"):
    """⊢ Card(A×{∅}) = Card(A).   (a·1 = a, E.III.3.3 ; 1 = Card({∅}).)

    Eq(A×{∅}, A) (eq_produit_un) ; la Proposition 1 (sens direct, version TERME
    _prop1_direct_t) conclut Card(A×{∅}) = Card(A)."""
    vA = _t(a)
    A1 = E.produit(vA, E.singleton(E.VIDE))
    eq = eq_produit_un(a)                   # Eq(A×{∅}, A)
    prop1 = _prop1_direct_t(A1, vA)         # Eq(A×{∅}, A) ⇒ Card(A×{∅})=Card(A)
    return N.modus_ponens(eq, prop1)        # Card(A×{∅}) = Card(A)


__all__ = ["produit_vide_droit", "produit_cardinal_zero",
           "proj_graphe_fonctionnel", "proj_graphe_domaine", "proj_graphe_valeur",
           "proj_graphe_injective", "proj_graphe_image", "proj_est_bijection",
           "eq_produit_un", "produit_cardinal_un"]
