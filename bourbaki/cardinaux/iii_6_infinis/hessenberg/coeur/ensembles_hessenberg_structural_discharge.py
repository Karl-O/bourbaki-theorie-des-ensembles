"""§III.6.3 — DÉCHARGE STRUCTURELLE des hypothèses honnêtes de Hessenberg a²=a.

Le théorème `hessenberg_a_carre_egal_a_inconditionnel`
(`ensembles_hessenberg_recollement_final`) ⊢ est_infini(Card E)⇒Card E·Card E=Card E
porte 9 HYPOTHÈSES HONNÊTES (jamais postulées, toutes VRAIES dans l'argument de Zorn
E.III.48).  Ce module les ATTAQUE comme LEMMES CLOS/réutilisables, par catégorie :

  A. STRUCTUREL bijection : de est_bijection_de(φ,X,Y) extraire dom(φ)=X et
     image(φ,X)=Y.  est_bijection_de(φ,X,Y) := ((fonctionnel ∧ dom=X) ∧ bijective)
     avec bijective := (injective ∧ image=Y).  Extraction par projections.  CLOS.

  C. U-data : (i) U≠∅ depuis Card U≠0 ; (ii) (∀z)(z∈U⇒¬z∈S₀) depuis U⊂E∖S₀.  CLOS.

  E. set→cardinal : Card S₀ ≤ Card E depuis S₀⊂E (pont équipotence sur ≤).

INVARIANT : theorie_ensembles() = 22.  Noyau INTACT ; NOUVEAU module ; rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, est_bijection_de,
)

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (A) STRUCTUREL — bijection ⇒ dom = source, image = target.
#
#  est_bijection_de(F,X,Y) = et( et(est_fonctionnel(F), egal(dom(F),X)),
#                                 est_bijective(F,X,Y) )
#  est_bijective(F,X,Y)    = et( injective_dans(F,X), egal(image(F,X),Y) )
#  d'où :   dom(F)=X      = elim_droite(elim_gauche(h))
#           image(F,X)=Y  = elim_droite(elim_droite(h))
# ════════════════════════════════════════════════════════════════════════════
def bijection_dom(F="phi", X="X", Y="Y"):
    """{ est_bijection_de(F,X,Y) } ⊢ dom(F) = X.        [1 hyp HONNÊTE, structurelle].

    Une bijection est partout définie sur sa source : dom(F)=X est le 2ᵉ conjoint
    (gauche-droite) de la définition est_bijection_de.  CLOS sous l'hyp bijection ;
    conclusion ∉ hyps ; theorie=22.  RÉUTILISABLE (cat. A du frame_pair Hessenberg)."""
    vF, vX, vY = _t(F), _t(X), _t(Y)
    h = N.assume(est_bijection_de(vF, vX, vY))
    res = conjonction_elim_droite(conjonction_elim_gauche(h))      # dom(F)=X
    cible = egal(E.dom(vF), vX)
    assert res.conclusion == cible, \
        f"bijection_dom : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "bijection_dom : VACUOUS"
    return res


def bijection_image(F="phi", X="X", Y="Y"):
    """{ est_bijection_de(F,X,Y) } ⊢ image(F,X) = Y.    [1 hyp HONNÊTE, structurelle].

    Une bijection est surjective sur sa cible : image(F,X)=Y est le conjoint
    droite-droite de est_bijection_de (via est_bijective = injective ∧ image=Y).
    CLOS sous l'hyp bijection ; conclusion ∉ hyps ; theorie=22.  RÉUTILISABLE (cat. A)."""
    vF, vX, vY = _t(F), _t(X), _t(Y)
    h = N.assume(est_bijection_de(vF, vX, vY))
    res = conjonction_elim_droite(conjonction_elim_droite(h))      # image(F,X)=Y
    cible = egal(E.image(vF, vX), vY)
    assert res.conclusion == cible, \
        f"bijection_image : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "bijection_image : VACUOUS"
    return res


def frame_dom_image(E_set="E", S="S0", phi="phi0"):
    """{ est_bijection_de(φ₀, S₀×S₀, S₀) } ⊢ ( dom(φ₀)=S₀×S₀  et  image(φ₀,S₀×S₀)=S₀ ).
                                                       [1 hyp HONNÊTE, structurelle].

    Spécialise (A) au cadre frame_pair de Hessenberg : φ₀ bijection de S₀×S₀ sur S₀
    (= contenu de (S₀,φ₀)∈𝔉(E)) donne les deux ÉGALITÉS structurelles dom/image
    EXIGÉES par phi_etendue_bijection.  CLOS sous la seule hyp bijection ; theorie=22."""
    vE, vS, vphi = _t(E_set), _t(S), _t(phi)
    SxS = E.produit(vS, vS)
    d = bijection_dom(vphi, SxS, vS)                  # dom(φ₀)=S₀×S₀
    i = bijection_image(vphi, SxS, vS)                # image(φ₀,S₀×S₀)=S₀
    res = conjonction_intro(d, i)
    cible = et(egal(E.dom(vphi), SxS), egal(E.image(vphi, SxS), vS))
    assert res.conclusion == cible, \
        f"frame_dom_image : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "frame_dom_image : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (C-i) U-data : Card U ≠ 0  ⊢  U ≠ ∅.
#
#  cardinal_egal_zero_ssi_vide : (Card U = Card ∅) ⇔ (U = ∅).
#  ⇐ : (U=∅) ⇒ (Card U = Card ∅).  Contraposée : (Card U ≠ 0) ⇒ (U ≠ ∅).
# ════════════════════════════════════════════════════════════════════════════
def U_non_vide(U="Ucadre"):
    """{ Card U ≠ Card ∅ } ⊢ U ≠ ∅.           [1 hyp HONNÊTE].

    Le témoin u∈U (U≠∅) de la contradiction de Hessenberg est JUSTIFIÉ : U a un
    cardinal non nul (Card U = 𝔟 infini ⇒ 𝔟≠0).  Via cardinal_egal_zero_ssi_vide
    (⇐ : U=∅ ⇒ Card U=Card∅), contraposée : Card U≠0 ⇒ U≠∅.  CLOS ; theorie=22."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes_prop7 import (
        cardinal_egal_zero_ssi_vide,
    )
    vU = _t(U)
    cU, c0 = cardinal(vU), cardinal(E.VIDE)
    cible = non(egal(vU, E.VIDE))
    h_ne = N.assume(non(egal(cU, c0)))                   # Card U ≠ Card ∅
    # bwd : (U=∅) ⇒ (Card U = Card ∅)
    bwd = equivalence_arriere(cardinal_egal_zero_ssi_vide(U))
    # contraposée explicite : assume U=∅ ⇒ Card U=Card∅ ⇒ ⊥ avec h_ne ⇒ cible.
    h_vide = N.assume(egal(vU, E.VIDE))                  # U=∅
    cardeq = N.modus_ponens(h_vide, bwd)                 # Card U = Card ∅
    falsum = N.modus_ponens(cardeq, N.modus_ponens(h_ne,
        N.s2(non(egal(cU, c0)), cible)))                 # cible (ex falso)
    res = _decharge_auto(h_vide, falsum, vU)
    assert res.conclusion == cible, \
        f"U_non_vide : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "U_non_vide : VACUOUS"
    return res


def _decharge_auto(h_vide, falsum, vU):
    """De {U=∅} ⊢ ¬(U=∅), conclut ⊢ ¬(U=∅) par auto-réfutation."""
    cible = non(egal(vU, E.VIDE))
    impl_p_np = N.loi_deduction(egal(vU, E.VIDE), falsum)   # (U=∅) ⇒ ¬(U=∅)
    return N.modus_ponens(impl_p_np, N.s1(cible))          # ¬(U=∅)


# ════════════════════════════════════════════════════════════════════════════
#  (C-ii) U-data : U ⊂ E∖S₀  ⊢  (∀z)(z∈U ⇒ ¬(z∈S₀)).
#
#  _inst_diff : (z ∈ E∖S₀) ⇔ (z∈E et ¬(z∈S₀)).
#  z∈U ⇒(U⊂E∖S₀) z∈E∖S₀ ⇒ (z∈E et ¬z∈S₀) ⇒ ¬z∈S₀.
# ════════════════════════════════════════════════════════════════════════════
def U_disjoint_S0(E_set="E", S="S0", U="Ucadre", z="z"):
    """{ U ⊂ E∖S₀ } ⊢ (∀z)( z∈U ⇒ ¬(z∈S₀) ).       [1 hyp HONNÊTE].

    U∩S₀=∅ de l'argument de Hessenberg : U est logé dans le COMPLÉMENT E∖S₀, donc
    aucun z∈U n'est dans S₀.  Via l'axiome de différence (_inst_diff) :
    z∈U ⇒ z∈E∖S₀ ⇒ (z∈E ∧ ¬z∈S₀) ⇒ ¬z∈S₀.  CLOS sous U⊂E∖S₀ ; theorie=22.

    ⚠️ binder « z » (binder par défaut de ⊂) pour que U⊂E∖S₀ s'instancie sans
    capture (l'hyp porte exactement (∀z)(z∈U ⇒ z∈E∖S₀))."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_difference import _inst_diff
    vE, vS, vU = _t(E_set), _t(S), _t(U)
    vz = var(z)
    DiffES = E.difference(vE, vS)
    cible = pourtout(z, impl(appartient(vz, vU), non(appartient(vz, vS))))

    h_sub = N.assume(inclus(vU, DiffES))                 # U ⊂ E∖S₀ = (∀z)(z∈U⇒z∈E∖S₀)
    h_z = N.assume(appartient(vz, vU))                   # z∈U
    z_in_diff = N.modus_ponens(h_z, instancie(h_sub, vz))  # z∈E∖S₀
    # _inst_diff : (z∈E∖S₀) ⇔ (z∈E et ¬z∈S₀)
    conj = N.modus_ponens(z_in_diff, equivalence_avant(_inst_diff(vE, vS, vz)))  # z∈E et ¬z∈S₀
    z_not_S = conjonction_elim_droite(conj)              # ¬(z∈S₀)
    body = N.loi_deduction(appartient(vz, vU), z_not_S)  # z∈U ⇒ ¬z∈S₀
    res = N.generalisation(z, body)                      # (∀z)(z∈U ⇒ ¬z∈S₀)
    assert res.conclusion == cible, \
        f"U_disjoint_S0 : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "U_disjoint_S0 : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (E) set→cardinal — S₀ ⊂ E  ⊢  Card S₀ ≤ Card E.
#
#  inf_egal_card_de_inclus : (S₀⊂E) ⇒ inf_egal_card(S₀,E).   [niveau ENSEMBLES]
#  invariance de ≤ par équipotence (Eq(X,Card X), Prop 1) + transitivité :
#     Card S₀ ~ S₀ ≤ E ~ Card E.   ⇒ inf_egal_card(Card S₀, Card E).
# ════════════════════════════════════════════════════════════════════════════
def _eq_implique_le_t(tX, tY):
    """⊢ equipotent(X,Y) ⇒ inf_egal_card(X,Y)  pour des TERMES X,Y (CLOS)."""
    from bourbaki.cardinaux.iii_4_ordinal_cardinal.realisation_segment.ensembles_subset_realise_close import (
        equipotent_implique_inf_egal,
    )
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_implique_inf_egal("X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _eq_card_le_set(tX):
    """⊢ inf_egal_card(Card X, X).   (Card X ~ X via Eq(X,Card X) + symétrie.)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal,
    )
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
    vX = _t(tX)
    cX = cardinal(vX)
    # Eq(X, Card X)  (Prop 1, instanciée au terme X)
    eq_x_cx = instancie(N.generalisation("X", equipotent_son_cardinal("X")), vX)
    # symétrie : Eq(X,Card X) ⇒ Eq(Card X, X)   (instanciée aux termes X, Card X)
    sym = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y"))), vX), cX)
    eq_cx_x = N.modus_ponens(eq_x_cx, sym)                    # Eq(Card X, X)
    return N.modus_ponens(eq_cx_x, _eq_implique_le_t(cX, vX))  # Card X ≤ X


def _set_le_eq_card(tX):
    """⊢ inf_egal_card(X, Card X).   (X ~ Card X via Eq(X,Card X).)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal,
    )
    vX = _t(tX)
    cX = cardinal(vX)
    eq_x_cx = instancie(N.generalisation("X", equipotent_son_cardinal("X")), vX)  # Eq(X,Card X)
    return N.modus_ponens(eq_x_cx, _eq_implique_le_t(vX, cX))  # X ≤ Card X


def _le_trans_t(tX, tY, tZ):
    """⊢ (X≤Y et Y≤Z) ⇒ X≤Z  pour des TERMES (transitivité instanciée)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
        inf_egal_transitive_general,
    )
    g = inf_egal_transitive_general("Xt", "Yt", "Zt")
    return instancie(instancie(instancie(g, _t(tX)), _t(tY)), _t(tZ))


def card_inclus_inf_egal(S="S0", E_set="E"):
    """{ S₀ ⊂ E } ⊢ Card S₀ ≤ Card E.            [1 hyp HONNÊTE].

    🎯 PONT set→cardinal (cat. E) : l'hyp honnête « Card S₀ ≤ Card E » de Hessenberg
    est DÉRIVÉE de l'inclusion ensembliste S₀⊂E.  Chaîne d'invariance de ≤ par
    équipotence (Prop 1, Eq(X,Card X)) :
        Card S₀  ≤  S₀  ≤  E  ≤  Card E
    via `inf_egal_card_de_inclus` (S₀⊂E ⇒ S₀≤E) et transitivité de ≤.  CLOS sous la
    seule hyp S₀⊂E ; conclusion ∉ hyps ; theorie=22."""
    from bourbaki.cardinaux.iii_4_ordinal_cardinal.bon_ordre_intervalle.ensembles_clause_plus_petit_monotonie import (
        inf_egal_card_de_inclus,
    )
    vE, vS = _t(E_set), _t(S)
    cS, cE = cardinal(vS), cardinal(vE)
    cible = inf_egal_card(cS, cE)

    h_sub = N.assume(inclus(vS, vE))                         # S₀ ⊂ E
    # S₀ ≤ E  (niveau ensembles)
    S_le_E = N.modus_ponens(h_sub, inf_egal_card_de_inclus(S, E_set))
    # Card S₀ ≤ S₀
    cS_le_S = _eq_card_le_set(vS)
    # E ≤ Card E
    E_le_cE = _set_le_eq_card(vE)
    # Card S₀ ≤ S₀ ≤ E  : transitivité
    cS_le_E = N.modus_ponens(conjonction_intro(cS_le_S, S_le_E),
                             _le_trans_t(cS, vS, vE))         # Card S₀ ≤ E
    # Card S₀ ≤ E ≤ Card E : transitivité
    res = N.modus_ponens(conjonction_intro(cS_le_E, E_le_cE),
                         _le_trans_t(cS, vE, cE))             # Card S₀ ≤ Card E
    assert res.conclusion == cible, \
        f"card_inclus_inf_egal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "card_inclus_inf_egal : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (B) géométrie produit — CŒUR pointwise de (A∪B)×C = (A×C)∪(B×C).
#
#  Miroir GAUCHE de couple_dans_produit_distributif_reunion (qui couvre A×(B∪C)).
#  (u,v)∈(A∪B)×C ⇔ (u∈A∪B et v∈C) ⇔ ((u∈A ou u∈B) et v∈C)
#               ⇔ ((u∈A et v∈C) ou (u∈B et v∈C))  [distrib via commutativité]
#               ⇔ ((u,v)∈A×C ou (u,v)∈B×C) ⇔ (u,v)∈(A×C)∪(B×C).
#  L'égalité ENSEMBLISTE pleine (∀z couple ou non) reste reportée (extensionnalité +
#  poussée des ∃p,q de AXIOME_PRODUIT) — cf. note du module produit_distributif.
# ════════════════════════════════════════════════════════════════════════════
def couple_dans_produit_reunion_gauche(u="u", v="v", a="A", b="B", c="C"):
    """⊢ ((u,v) ∈ (A∪B)×C) ⇔ ((u,v) ∈ (A×C)∪(B×C)).   [CLOS, 0 hyp].

    🎯 CŒUR pointwise de la GÉOMÉTRIE PRODUIT (cat. B) : distribution GAUCHE du
    produit cartésien sur la réunion (E.II.2), miroir de
    couple_dans_produit_distributif_reunion.  Brique réutilisable vers
    (S₀∪U)²=S₀²∪(S₀×U)∪(U×S₀)∪U² (l'égalité ensembliste pleine reste à lever par
    extensionnalité)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
        et_congruence_gauche, et_ou_distrib, ou_congruence, comm_et,
        equivalence_symetrie, equivalence_transitivite,
    )
    vu, vv, vA, vB, vC = _t(u), _t(v), _t(a), _t(b), _t(c)
    AB = E.reunion(vA, vB)
    uA, uB, vCm = appartient(vu, vA), appartient(vu, vB), appartient(vv, vC)
    # (u,v)∈(A∪B)×C ⇔ (u∈A∪B et v∈C)
    e1 = couple_dans_produit_ssi(vu, vv, AB, vC)
    # (u∈A∪B et v∈C) ⇔ ((u∈A ou u∈B) et v∈C)
    e2 = et_congruence_gauche(_instance_reunion(vA, vB, vu), vCm)
    # ((u∈A ou u∈B) et v∈C) ⇔ (v∈C et (u∈A ou u∈B))   (commutativité)
    e3 = comm_et(ou(uA, uB), vCm)
    # (v∈C et (u∈A ou u∈B)) ⇔ ((v∈C et u∈A) ou (v∈C et u∈B))   (distrib)
    e4 = et_ou_distrib(vCm, uA, uB)
    # ((v∈C et u∈A) ou (v∈C et u∈B)) ⇔ ((u∈A et v∈C) ou (u∈B et v∈C))   (commut sous ou)
    e5 = ou_congruence(comm_et(vCm, uA), comm_et(vCm, uB))
    # ((u∈A et v∈C) ou (u∈B et v∈C)) ⇔ ((u,v)∈A×C ou (u,v)∈B×C)
    e6 = ou_congruence(equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vA, vC)),
                       equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vB, vC)))
    # ((u,v)∈A×C ou (u,v)∈B×C) ⇔ (u,v)∈(A×C)∪(B×C)
    e7 = equivalence_symetrie(_instance_reunion(E.produit(vA, vC), E.produit(vB, vC),
                                                E.couple(vu, vv)))
    res = equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        equivalence_transitivite(equivalence_transitivite(
            equivalence_transitivite(e1, e2), e3), e4), e5), e6), e7)
    return res


__all__ = [
    "bijection_dom",
    "bijection_image",
    "frame_dom_image",
    "U_non_vide",
    "U_disjoint_S0",
    "card_inclus_inf_egal",
    "couple_dans_produit_reunion_gauche",
]
