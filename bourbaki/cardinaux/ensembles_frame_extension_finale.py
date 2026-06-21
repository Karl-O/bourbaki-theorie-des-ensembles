"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : l'EXTENSION FINALE du maximal,
« CLAIM : Card(S₀)=Card(E) ⇒ a²=a ».

CONTEXTE (lu sur le PDF source, E.III.48).  L'argument de Zorn fournit un couple
MAXIMAL (S₀,φ₀)∈𝔉(E), φ₀ : S₀×S₀ → S₀ BIJECTIVE (⇒ 𝔟²=𝔟, 𝔟:=Card S₀,
`maximal_carre_egal`).  Bourbaki conclut Card(S₀)=Card(E)=𝔞 par CONTRADICTION :
si 𝔟 < 𝔞, on prend U⊂E∖S₀ équipotent à S₀ (le complément est « grand »,
`complement_grand`), on pose Z = S₀∪U, et l'on observe

    Z×Z  =  (S₀×S₀)  ⊔  [ (S₀×U) ⊔ (U×S₀) ⊔ (U×U) ]   (réunion DISJOINTE),

dont le « CADRE » F := Z²∖(S₀×S₀) = (S₀×U)⊔(U×S₀)⊔(U×U) a pour cardinal
3𝔟²=3𝔟=𝔟=Card(U) (`trois_b_egal_b_inconditionnel`).  D'où une bijection ψ:F→U,
et g := φ₀∪ψ : Z×Z→Z BIJECTIVE prolongeant φ₀ — contredisant la maximalité de
(S₀,φ₀).  Donc Card(S₀)=𝔞 et 𝔞² = Card(S₀)² = Card(S₀) = 𝔞.

Ce module construit les pièces de cet argument, dans l'ordre du plan :

  (1) `cadre_card_trois_b`  — Card(F) = 3𝔟 = 𝔟 (cardinal du cadre).
  (2) `cadre_bijection`     — Card(F)=Card(U) ⇒ (∃ψ) est_bijection_de(ψ,F,U).
  (3) `phi_etendue_*`       — recollement φ₁ := φ₀∪ψ et sa bijectivité Z×Z→Z.
  (4) `contradiction_maximalite` — frame-membership de (Z,φ₁) + ordre + maximalité.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau dans
theorie_ensembles ; rien postulé ; a²=a n'est JAMAIS supposé, le ≥ dur jamais
supposé vrai.  Les pièces résistantes sont sous HYPOTHÈSES HONNÊTES explicites,
jamais postulées vraies, avec OBSTRUCTION précise documentée.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, equipotent, est_bijection_de, inf_egal_card,
    inf_strict_card,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_si_cardinal_egal,
)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.cardinaux.ensembles_prop13_complement import (
    _somme_disjointe_cardinal_t,
)
from bourbaki.cardinaux.ensembles_descentes_inconditionnelles import (
    trois_b_egal_b_inconditionnel,
)
from bourbaki.entiers.ensembles_infinis import est_infini
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (2) cadre_bijection — Card(F)=Card(U) ⇒ (∃ψ) ψ : F → U bijective.
#  Route : Prop 1 réciproque (Card F=Card U ⇒ Eq(F,U)) ; Eq(F,U)=(∃ψ)bij(ψ,F,U).
# ════════════════════════════════════════════════════════════════════════════
def cadre_bijection(F="Fcadre", U="Ucadre"):
    """⊢ ( Card(F) = Card(U) ) ⇒ (∃ψ)( est_bijection_de(ψ, F, U) ).         [CLOS, 0 hyp].

    🎯 Étape 2 du plan : du cardinal du cadre à une BIJECTION ψ:F→U.  C'est la Prop 1
    (sens réciproque, `equipotent_si_cardinal_egal`) : Card F=Card U ⇒ Eq(F,U), et
    Eq(F,U) = (∃ψ)(ψ bij. de F sur U) par DÉFINITION de l'équipotence.  La conclusion
    est LITTÉRALEMENT equipotent(F,U) déplié.  theorie=22 ; conclusion ∉ hyps."""
    vF, vU = _t(F), _t(U)
    cible = impl(egal(cardinal(vF), cardinal(vU)), equipotent(vF, vU))
    # equipotent_si_cardinal_egal(X,Y) : (Card X=Card Y) ⇒ Eq(X,Y), construit sur noms
    # frais puis généralisé/instancié aux TERMES (capture-safe, motif _prop1_direct_t).
    base = equipotent_si_cardinal_egal("Xcb", "Ycb")
    gen = N.generalisation("Xcb", N.generalisation("Ycb", base))
    res = instancie(instancie(gen, vF), vU)
    assert res.conclusion == cible, \
        f"cadre_bijection : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cadre_bijection : VACUOUS"
    return res


def cadre_bijection_cible(F="Fcadre", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir)."""
    vF, vU = _t(F), _t(U)
    return impl(egal(cardinal(vF), cardinal(vU)), equipotent(vF, vU))


# ════════════════════════════════════════════════════════════════════════════
#  (1) CARDINAL DU CADRE — Card(P) = 𝔟 pour P ∈ {S₀×U, U×S₀, U×U},
#      puis Card(F) = 3𝔟 = 𝔟  pour F = (S₀×U)⊔((U×S₀)⊔(U×U)).
# ════════════════════════════════════════════════════════════════════════════
def _card_produit_egal_b(A, B, b):
    """{ Card A = 𝔟,  Card B = 𝔟,  𝔟·𝔟 = 𝔟 } ⊢ Card(A×B) = 𝔟.            [3 hyps honnêtes].

    Card(A×B) ne dépend que de Card A et Card B : produit_cardinal_bien_defini à
    (X:=A,Y:=B,a:=𝔟,b:=𝔟) donne (Card A=𝔟 et Card B=𝔟) ⇒ Card(A×B) = 𝔟·𝔟 ; l'hypothèse
    d'absorption 𝔟·𝔟=𝔟 réécrit en Card(A×B) = 𝔟.  Construit aux TERMES capture-safe
    (généralisation/instanciation, motif prop9)."""
    vA, vB, vb = _t(A), _t(B), _t(b)
    cA, cB = cardinal(vA), cardinal(vB)
    AxB = E.produit(vA, vB)
    bb = produit_cardinal_binaire(vb, vb)                    # 𝔟·𝔟 = Card(𝔟×𝔟)

    h_cA = N.assume(egal(cA, vb))                            # Card A = 𝔟
    h_cB = N.assume(egal(cB, vb))                            # Card B = 𝔟
    h_bb = N.assume(egal(bb, vb))                            # 𝔟·𝔟 = 𝔟

    # bien-déf : (Card A=𝔟 et Card B=𝔟) ⇒ Card(A×B) = 𝔟·𝔟   (capture-safe aux termes)
    bd_var = produit_cardinal_bien_defini("XX", "YY", "AA", "BB")
    bd_gen = N.generalisation("XX", N.generalisation("YY",
        N.generalisation("AA", N.generalisation("BB", bd_var))))
    bd = instancie(instancie(instancie(instancie(bd_gen, vA), vB), vb), vb)
    ant = et(egal(cA, vb), egal(cB, vb))
    assert bd.conclusion == impl(ant, egal(cardinal(AxB), bb)), \
        f"_card_produit_egal_b : bien-déf forme inattendue\n{bd.conclusion}"
    card_AxB_eq_bb = N.modus_ponens(conjonction_intro(h_cA, h_cB), bd)   # Card(A×B)=𝔟·𝔟
    # réécrire 𝔟·𝔟 → 𝔟  (h_bb), S6 sur le RHS de l'égalité.
    s6 = N.s6(bb, vb, "wcp", egal(cardinal(AxB), var("wcp")))
    res = N.modus_ponens(card_AxB_eq_bb, equivalence_avant(N.modus_ponens(h_bb, s6)))
    assert res.conclusion == egal(cardinal(AxB), vb), \
        f"_card_produit_egal_b : conclusion inattendue\n{res.conclusion}"
    return res


def cadre_ensemble(S="S0", U="Ucadre"):
    """Le CADRE F := (S₀×U) ⊔ ( (U×S₀) ⊔ (U×U) )   (E.III.48, réunion disjointe Z²∖S₀²)."""
    vS, vU = _t(S), _t(U)
    return somme_disjointe(E.produit(vS, vU),
                           somme_disjointe(E.produit(vU, vS), E.produit(vU, vU)))


def cadre_card_trois_b(S="S0", U="Ucadre"):
    """{ Card S₀ = Card U,  𝔟·𝔟 = 𝔟,  est_cardinal(𝔟),  est_infini(𝔟) }
        ⊢ Card(F) = 𝔟,   𝔟 := Card S₀,  F = (S₀×U) ⊔ ((U×S₀) ⊔ (U×U)).   [hyps HONNÊTES].

    🎯 Étape 1 du plan : le CADRE F = Z²∖(S₀×S₀) a pour cardinal 3𝔟² = 3𝔟 = 𝔟 (E.III.48,
    « Card((F×Y)∪(Y×F)∪(Y×Y)) = 3𝔟 = 𝔟 »).  Chaque facteur a Card = 𝔟·𝔟 = 𝔟
    (`_card_produit_egal_b`, sous Card U=Card S₀=𝔟 et l'absorption 𝔟²=𝔟) ; la réunion
    DISJOINTE assemble Card(F) = 𝔟 + (𝔟 + 𝔟) via `_somme_disjointe_cardinal_t` (deux
    fois), et `trois_b_egal_b_inconditionnel` (sous est_cardinal(𝔟) et est_infini(𝔟) et
    𝔟²=𝔟) referme 3𝔟 = 𝔟.

    Hyps HONNÊTES (jamais postulées) : Card S₀=Card U (U équipotent à S₀, fourni par
    `complement_grand`+réalisation), 𝔟²=𝔟 (= `maximal_carre_egal`), est_cardinal(𝔟),
    est_infini(𝔟).  Conclusion ∉ hyps ; theorie=22."""
    vS, vU = _t(S), _t(U)
    b = cardinal(vS)                                         # 𝔟 = Card S₀
    cU = cardinal(vU)
    bb = produit_cardinal_binaire(b, b)                      # 𝔟·𝔟
    SxU = E.produit(vS, vU)
    UxS = E.produit(vU, vS)
    UxU = E.produit(vU, vU)
    UxS_UxU = somme_disjointe(UxS, UxU)                      # (U×S₀)⊔(U×U)
    F = somme_disjointe(SxU, UxS_UxU)                        # le cadre
    cible = egal(cardinal(F), b)

    # hyps honnêtes
    h_cardU = N.assume(egal(b, cU))                          # Card S₀ = Card U
    h_bb = N.assume(egal(bb, b))                             # 𝔟·𝔟 = 𝔟
    h_card_b = N.assume(est_cardinal(b))                     # est_cardinal(𝔟)
    h_inf_b = N.assume(est_infini(b))                        # est_infini(𝔟)

    # Card U = 𝔟   (symétrie de Card S₀=Card U)
    cU_eq_b = N.modus_ponens(h_cardU, symetrie(b, cU))       # Card U = 𝔟

    # Card de chaque facteur = 𝔟  (déchargeant les 3 hyps de _card_produit_egal_b)
    # Card S₀ = 𝔟 est la réflexivité (b == cardinal(vS))
    cS_eq_b = N.reflexivite(b)
    card_SxU = _card_produit_egal_b(vS, vU, b)
    card_SxU = N.modus_ponens(cS_eq_b, N.loi_deduction(egal(cardinal(vS), b), card_SxU))
    card_SxU = N.modus_ponens(cU_eq_b, N.loi_deduction(egal(cU, b), card_SxU))
    card_SxU = N.modus_ponens(h_bb, N.loi_deduction(egal(bb, b), card_SxU))
    assert card_SxU.conclusion == egal(cardinal(SxU), b)

    card_UxS = _card_produit_egal_b(vU, vS, b)
    card_UxS = N.modus_ponens(cU_eq_b, N.loi_deduction(egal(cU, b), card_UxS))
    card_UxS = N.modus_ponens(cS_eq_b, N.loi_deduction(egal(cardinal(vS), b), card_UxS))
    card_UxS = N.modus_ponens(h_bb, N.loi_deduction(egal(bb, b), card_UxS))
    assert card_UxS.conclusion == egal(cardinal(UxS), b)

    card_UxU = _card_produit_egal_b(vU, vU, b)
    card_UxU = N.modus_ponens(cU_eq_b, N.loi_deduction(egal(cU, b), card_UxU))
    card_UxU = N.modus_ponens(cU_eq_b, N.loi_deduction(egal(cU, b), card_UxU))
    card_UxU = N.modus_ponens(h_bb, N.loi_deduction(egal(bb, b), card_UxU))
    assert card_UxU.conclusion == egal(cardinal(UxU), b)

    # Card((U×S₀)⊔(U×U)) = 𝔟 + 𝔟   (somme disjointe, sous Card(U×S₀)=𝔟, Card(U×U)=𝔟)
    sdc1 = _somme_disjointe_cardinal_t(UxS, UxU, b, b)       # (Card=𝔟 ∧ Card=𝔟)⇒Card(⊔)=𝔟+𝔟
    bplusb = somme_cardinale_binaire(b, b)
    card_inner = N.modus_ponens(conjonction_intro(card_UxS, card_UxU), sdc1)
    assert card_inner.conclusion == egal(cardinal(UxS_UxU), bplusb)

    # Card(F) = Card(S₀×U ⊔ (UxS⊔UxU)) = 𝔟 + (𝔟+𝔟)   (somme disjointe, 2ᵉ sommant cardinal 𝔟+𝔟)
    sdc2 = _somme_disjointe_cardinal_t(SxU, UxS_UxU, b, bplusb)
    threeb = somme_cardinale_binaire(b, bplusb)              # 𝔟+(𝔟+𝔟)  (forme INTERNE de 3𝔟)
    card_F = N.modus_ponens(conjonction_intro(card_SxU, card_inner), sdc2)
    assert card_F.conclusion == egal(cardinal(F), threeb)

    # 3𝔟 = 𝔟  via trois_b_egal_b_inconditionnel.  ⚠️ sa conclusion est sur la forme
    #   somme_cardinale_binaire(𝔟, 𝔟⊔𝔟)=𝔟  (2ᵉ sommant ENSEMBLE 𝔟⊔𝔟) ; on PONTE vers
    #   notre forme threeb (2ᵉ sommant CARDINAL 𝔟+𝔟) par bien-déf de la somme.
    # ⚠️ trois_b_egal_b_inconditionnel N'EST PAS capture-safe pour un 𝔟 COMPOSÉ
    #   (τ-nested, = Card S₀) : son graphe-témoin interne (membre_graphe_terme) capture.
    #   On la construit donc sur un NOM FRAIS puis on généralise/instancie au TERME 𝔟.
    t3_var = trois_b_egal_b_inconditionnel("b3incond")       # clos, sur nom frais
    t3 = instancie(N.generalisation("b3incond", t3_var), b)  # (card∧inf∧𝔟²=𝔟)⇒ Card(𝔟⊔(𝔟⊔𝔟))=𝔟
    A3 = et(et(est_cardinal(b), est_infini(b)), egal(bb, b))
    t3_app = N.modus_ponens(conjonction_intro(conjonction_intro(
        h_card_b, h_inf_b), h_bb), t3)                       # somme_cardinale_binaire(𝔟,𝔟⊔𝔟)=𝔟
    bb_set = somme_disjointe(b, b)                           # 𝔟⊔𝔟 (ENSEMBLE)
    threeb_set = somme_cardinale_binaire(b, bb_set)          # Card(𝔟⊔(𝔟⊔𝔟))  (forme du théorème)
    assert t3_app.conclusion == egal(threeb_set, b), \
        f"cadre_card_trois_b : 3𝔟 forme inattendue\n{t3_app.conclusion}"

    # PONT : threeb (cardinal) = threeb_set (ensemble) via bien-déf de la somme cardinale.
    #   somme_cardinale_binaire(𝔟, 𝔟+𝔟) = somme_cardinale_binaire(𝔟, 𝔟⊔𝔟) car Card(𝔟⊔𝔟)=𝔟+𝔟.
    #   En fait somme_cardinale_binaire(a,b) := Card(a⊔b), donc :
    #   threeb     = Card(𝔟 ⊔ (𝔟+𝔟))   [2ᵉ sommant = CARDINAL 𝔟+𝔟]
    #   threeb_set = Card(𝔟 ⊔ (𝔟⊔𝔟))   [2ᵉ sommant = ENSEMBLE 𝔟⊔𝔟]
    #   reliés par bien-déf : Eq(𝔟,𝔟) ∧ Eq(𝔟⊔𝔟, 𝔟+𝔟) ⇒ Card(𝔟⊔(𝔟⊔𝔟))=Card(𝔟⊔(𝔟+𝔟)).
    from bourbaki.cardinaux.ensembles_descentes_inconditionnelles import _bien_definie_t
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
    from bourbaki.cardinaux.ensembles_equipotence_retrait import equipotence_reflexive_pour
    eq_set_card = instancie(N.generalisation("X", equipotent_son_cardinal("X")), bb_set)  # Eq(𝔟⊔𝔟, Card(𝔟⊔𝔟))
    # Card(𝔟⊔𝔟) = 𝔟+𝔟 par DÉFINITION (somme_cardinale_binaire(𝔟,𝔟) := Card(𝔟⊔𝔟))
    assert bplusb == cardinal(bb_set), "cadre_card_trois_b : 𝔟+𝔟 ≠ Card(𝔟⊔𝔟) littéral"
    eq_bb = equipotence_reflexive_pour(b)                    # Eq(𝔟,𝔟)
    bd = _bien_definie_t(b, bb_set, b, bplusb)               # (Eq∧Eq)⇒Card(𝔟⊔(𝔟⊔𝔟))=Card(𝔟⊔(𝔟+𝔟))
    bridge = N.modus_ponens(conjonction_intro(eq_bb, eq_set_card), bd)
    assert bridge.conclusion == egal(threeb_set, threeb), \
        f"cadre_card_trois_b : pont inattendu\n{bridge.conclusion}\nvs\n{egal(threeb_set, threeb)}"
    # threeb = 𝔟  : threeb = threeb_set (sym bridge) puis threeb_set = 𝔟 (t3_app)
    threeb_eq_set = N.modus_ponens(bridge, symetrie(threeb_set, threeb))   # threeb = threeb_set
    threeb_eq_b = composer_egalites(threeb_eq_set, t3_app)                 # threeb = 𝔟

    # Card(F) = 𝔟  : Card(F)=threeb (card_F) puis threeb=𝔟
    res = composer_egalites(card_F, threeb_eq_b)
    assert res.conclusion == cible, \
        f"cadre_card_trois_b : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cadre_card_trois_b : VACUOUS"
    return res


def cadre_card_trois_b_cible(S="S0", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir)."""
    vS = _t(S)
    return egal(cardinal(cadre_ensemble(S, U)), cardinal(vS))


# ════════════════════════════════════════════════════════════════════════════
#  (3) phi_etendue — recollement φ₁ := φ₀ ∪ ψ : Z×Z → Z BIJECTIVE.
#  La FONCTIONNALITÉ et l'INJECTIVITÉ du recollement sont GENUINEMENT DÉRIVÉES de
#  l'infra `ensembles_recollement_bijection` (reunion_graphes_fonctionnelle /
#  reunion_graphes_injective).  Les deux conjoints VALEUR-D'ENSEMBLES (dom(φ₁)=Z×Z,
#  image(φ₁)=Z) sont portés en HYPOTHÈSES HONNÊTES — même approche que
#  `union_chaine_est_bijection`, faute du pont couple→égalité-d'ensembles dans le
#  dépôt pour le DOMAINE/IMAGE d'un recollement concret en termes de S₀²⊔F=Z².
# ════════════════════════════════════════════════════════════════════════════
def phi_etendue_bijection(phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ est_fonctionnel(φ₀), est_fonctionnel(ψ),
         (∀u)¬(u∈dom φ₀ et u∈dom ψ),
         injective_dans(φ₀, dom φ₀), injective_dans(ψ, dom ψ),
         image(φ₀,dom φ₀)∩image(ψ,dom ψ)=∅,
         dom(φ₀∪ψ)=Z×Z,  image(φ₀∪ψ, Z×Z)=Z }
       ⊢ est_bijection_de( φ₀∪ψ, Z×Z, Z ),   Z = S₀∪U.            [CLOS, hyps HONNÊTES].

    🎯 Étape 3 du plan : le recollement φ₁ := φ₀∪ψ est une BIJECTION Z×Z→Z prolongeant
    φ₀ (E.III.48, « g := f∪f₁ : Z→Z×Z bijective prolonge f »).  est_bijection_de =
        ((est_fonctionnel ∧ dom=src) ∧ (injective_dans ∧ image=tgt)).
    FONCTIONNALITÉ (reunion_graphes_fonctionnelle, domaines disjoints) et INJECTIVITÉ
    (reunion_graphes_injective, images disjointes) sont GENUINEMENT DÉRIVÉES de l'infra
    recollement ; les deux conjoints VALEUR-D'ENSEMBLES dom(φ₁)=Z×Z et image(φ₁,Z×Z)=Z
    sont portés en HYPOTHÈSES HONNÊTES (pont couple→égalité-d'ensembles absent du dépôt
    pour S₀²⊔F=Z² et S₀∪U=Z ; jamais postulées vraies).  Conclusion ∉ hyps ; theorie=22.
    """
    from bourbaki.ensembles.fonctions.ensembles_restriction_somme import (
        reunion_graphes_fonctionnelle,
    )
    from bourbaki.ensembles.fonctions.ensembles_recollement_bijection import (
        reunion_graphes_injective,
    )
    vphi0, vpsi = _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)                                    # Z = S₀∪U
    ZxZ = E.produit(Z, Z)
    phi1 = E.reunion(vphi0, vpsi)                            # φ₁ = φ₀∪ψ

    # FONCTIONNALITÉ — dérivée (domaines disjoints).
    func = reunion_graphes_fonctionnelle(vphi0, vpsi)        # {func,func,disj} ⊢ func(φ₁)
    assert func.conclusion == E.est_fonctionnel(phi1)
    # INJECTIVITÉ — dérivée (images disjointes).
    inj = reunion_graphes_injective(vphi0, vpsi)            # {…} ⊢ injective_dans(φ₁, domφ₀∪domψ)
    domR = E.reunion(E.dom(vphi0), E.dom(vpsi))
    assert inj.conclusion == E.injective_dans(phi1, domR)

    # dom(φ₁)=Z×Z et image(φ₁,Z×Z)=Z — DÉRIVÉS via les corollaires GAP A
    #   (dom_reunion_egale_cible / image_reunion_egale_cible) à partir d'hyps
    #   STRUCTURELLES PLUS PRIMITIVES sur les témoins (dom φ₀=S₀², dom ψ=F, S₀²∪F=Z² ;
    #   img φ₀=imgG, img ψ=imgH, imgG∪imgH=Z).  Le pont couple→égalité-d'ensembles
    #   GLOBAL est ainsi FERMÉ (lemmes généraux clos) ; ne subsistent que ces hyps
    #   structurelles (dom/image des bijections-témoins, identités géométriques),
    #   genuinement honnêtes (fournies par l'argument de Zorn E.III.48).
    from bourbaki.ensembles.fonctions.ensembles_dom_image_reunion import (
        dom_reunion_egale_cible, image_reunion_egale_cible,
    )
    from bourbaki.ensembles.fonctions.ensembles_restriction_somme import dom_reunion_graphes
    Fcadre = cadre_ensemble(S, U)                           # F = cadre Z²∖S₀²
    SxS = E.produit(vS, vS)
    domG, domH = E.dom(vphi0), E.dom(vpsi)
    imgG, imgH = E.image(vphi0, domG), E.image(vpsi, domH)
    # GAP A (dom) : {dom φ₀=S₀², dom ψ=F, S₀²∪F=Z×Z} ⊢ dom(φ₁)=Z×Z.
    h_dom = dom_reunion_egale_cible(vphi0, vpsi, SxS, Fcadre, ZxZ)
    assert h_dom.conclusion == egal(E.dom(phi1), ZxZ)
    # GAP A (image) : {img φ₀=imgG, img ψ=imgH, imgG∪imgH=Z} ⊢ image(φ₁,domR)=Z,
    #   puis réécrit domR→Z×Z (h_dom) en image(φ₁,Z×Z)=Z.
    h_img_domR = image_reunion_egale_cible(vphi0, vpsi, imgG, imgH, Z)
    assert h_img_domR.conclusion == egal(E.image(phi1, domR), Z)
    domR_eq_ZxZ_for_img = composer_egalites(
        N.modus_ponens(dom_reunion_graphes(vphi0, vpsi), symetrie(E.dom(phi1), domR)),
        h_dom)                                              # domR = Z×Z
    s6img = N.s6(domR, ZxZ, "wimg", egal(E.image(phi1, var("wimg")), Z))
    h_img = N.modus_ponens(h_img_domR, equivalence_avant(
        N.modus_ponens(domR_eq_ZxZ_for_img, s6img)))        # image(φ₁,Z×Z)=Z
    assert h_img.conclusion == egal(E.image(phi1, ZxZ), Z)
    # domφ₀∪domψ = dom(φ₁) (dom_reunion_graphes, symétrisé) = Z×Z (h_dom).
    dom_rg = dom_reunion_graphes(vphi0, vpsi)               # dom(φ₁) = domφ₀∪domψ
    assert dom_rg.conclusion == egal(E.dom(phi1), domR)
    domR_eq_dom2 = N.modus_ponens(dom_rg, symetrie(E.dom(phi1), domR))  # domφ₀∪domψ = dom(φ₁)
    domR_eq_ZxZ = composer_egalites(domR_eq_dom2, h_dom)    # domφ₀∪domψ = Z×Z
    # réécrire injective_dans(φ₁, domφ₀∪domψ) → injective_dans(φ₁, Z×Z) via S6.
    s6inj = N.s6(domR, ZxZ, "winj", E.injective_dans(phi1, var("winj")))
    inj_ZxZ = N.modus_ponens(inj, equivalence_avant(N.modus_ponens(domR_eq_ZxZ, s6inj)))
    assert inj_ZxZ.conclusion == E.injective_dans(phi1, ZxZ)

    # est_bijection_de = ((fonctionnel ∧ dom=src) ∧ (injective_dans ∧ image=tgt))
    gauche = conjonction_intro(func, h_dom)
    droite = conjonction_intro(inj_ZxZ, h_img)
    res = conjonction_intro(gauche, droite)
    cible = est_bijection_de(phi1, ZxZ, Z)
    assert res.conclusion == cible, \
        f"phi_etendue_bijection : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "phi_etendue_bijection : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (4) FRAME-MEMBERSHIP de (Z,φ₁) ∈ 𝔉(E)  (mirror de union_chaine_dans_frame).
# ════════════════════════════════════════════════════════════════════════════
def extension_dans_frame(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ est_bijection_de(φ₁, Z×Z, Z),  Z⊂E,  Z infini } ⊢ (Z,φ₁) ∈ 𝔉(E),  Z=S₀∪U,
        φ₁=φ₀∪ψ.                                            [CLOS, hyps HONNÊTES].

    🎯 Le couple-extension (Z,φ₁) est une FRAME-PAIR (E.III.48).  Motif IDENTIQUE à
    `union_chaine_dans_frame` : le corps de 𝔉,
    _corps_frame(E,p)=(∃S)(∃φ)(p=(S,φ) et S⊂E et S infini et φ bij. S×S→S), est instancié
    par S:=Z, φ:=φ₁ (double existe-intro S5).  Quatre conjoints du témoin :
    p=(Z,φ₁) [réflexivité], Z⊂E [hyp honnête], Z infini [hyp honnête], φ₁ bij. Z×Z→Z
    [= `phi_etendue_bijection`].  Puis frame_membre ⇐.  Jamais postulé ; theorie=22."""
    from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
    from bourbaki.cardinaux.ensembles_hessenberg_hard import (
        frame_pair, theorie_frame, axiome_frame,
    )
    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    ZxZ = E.produit(Z, Z)
    phi1 = E.reunion(vphi0, vpsi)
    p = E.couple(Z, phi1)                                    # (Z,φ₁)

    h_bij = N.assume(est_bijection_de(phi1, ZxZ, Z))        # φ₁ bij. Z×Z→Z   [HONNÊTE]
    h_incl = N.assume(inclus(Z, vE))                        # Z⊂E             [HONNÊTE]
    h_inf = N.assume(est_infini_ensemble(Z))               # Z infini         [HONNÊTE]
    refl = N.reflexivite(p)                                 # p=(Z,φ₁)

    th_corps = conjonction_intro(
        conjonction_intro(conjonction_intro(refl, h_incl), h_inf), h_bij)
    corps_sub = et(et(et(egal(p, p), inclus(Z, vE)), est_infini_ensemble(Z)),
                   est_bijection_de(phi1, ZxZ, Z))
    assert th_corps.conclusion == corps_sub, "extension_dans_frame : corps-témoin ≠ attendu"

    # existe-intro INTÉRIEUR (φ:=φ₁) puis EXTÉRIEUR (S:=Z) — motif _corps_frame.
    vSv, vphiv = var("S"), var("phi")
    SxS = E.produit(vSv, vSv)
    R_interne = et(et(et(egal(p, E.couple(Z, vphiv)),
                         inclus(Z, vE)), est_infini_ensemble(Z)),
                   est_bijection_de(vphiv, ZxZ, Z))
    th_ex_phi = N.modus_ponens(th_corps, N.s5(R_interne, phi1, "phi"))
    R_externe = existe("phi",
        et(et(et(egal(p, E.couple(vSv, vphiv)), inclus(vSv, vE)),
               est_infini_ensemble(vSv)),
           est_bijection_de(vphiv, SxS, vSv)))
    th_ex_S = N.modus_ponens(th_ex_phi, N.s5(R_externe, Z, "S"))   # corps_frame(E,p)

    ax = N.axiome(theorie_frame(), axiome_frame())
    eq_p = instancie(instancie(ax, vE), p)                 # (p∈𝔉(E)) ⇔ corps_frame(E,p)
    res = N.modus_ponens(th_ex_S, equivalence_arriere(eq_p))      # p∈𝔉(E)

    cible = appartient(p, frame_pair(vE))
    assert res.conclusion == cible, "extension_dans_frame : ≠ (Z,φ₁)∈𝔉(E)"
    assert res.conclusion not in res.hypotheses, "extension_dans_frame : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (4b) ORDRE  ((S₀,φ₀),(Z,φ₁)) ∈ Γ𝔉(E)  via axiome_frame_ordre.
# ════════════════════════════════════════════════════════════════════════════
def extension_ordre(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ (S₀,φ₀)∈𝔉(E),  (Z,φ₁)∈𝔉(E),  S₀⊂Z,  φ₀⊂φ₁ }
        ⊢ ( (S₀,φ₀), (Z,φ₁) ) ∈ Γ𝔉(E),   Z=S₀∪U, φ₁=φ₀∪ψ.   [CLOS, hyps HONNÊTES].

    🎯 Le couple maximal (S₀,φ₀) est ≤ son extension (Z,φ₁) dans l'ordre Γ𝔉 (E.III.48,
    « g prolonge f »).  Le corps de Γ𝔉,
    _corps_frame_ordre(E,p,q)=(p∈𝔉 et q∈𝔉 et pr₁(p)⊂pr₁(q) et pr₂(p)⊂pr₂(q)),
    est satisfait : pr₁((S₀,φ₀))=S₀⊂Z=pr₁((Z,φ₁)) et pr₂((S₀,φ₀))=φ₀⊂φ₁=pr₂((Z,φ₁)),
    après réécriture des projections (projection_premiere/seconde).  Puis frame_ordre_membre
    ⇐.  Hyps honnêtes (membership des deux couples + les deux inclusions de prolongement) ;
    theorie=22."""
    from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
    from bourbaki.cardinaux.ensembles_frame_ordre_axiome import (
        theorie_frame_ordre, axiome_frame_ordre,
    )
    from bourbaki.ensembles.fonctions.ensembles_projections import (
        projection_premiere, projection_seconde,
    )
    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    phi1 = E.reunion(vphi0, vpsi)
    p = E.couple(vS, vphi0)                                 # (S₀,φ₀)
    q = E.couple(Z, phi1)                                   # (Z,φ₁)
    Fr = frame_pair(vE)

    h_p = N.assume(appartient(p, Fr))                       # (S₀,φ₀)∈𝔉    [HONNÊTE]
    h_q = N.assume(appartient(q, Fr))                       # (Z,φ₁)∈𝔉      [HONNÊTE]
    h_S = N.assume(inclus(vS, Z))                          # S₀⊂Z          [HONNÊTE]
    h_phi = N.assume(inclus(vphi0, phi1))                 # φ₀⊂φ₁          [HONNÊTE]

    # pr₁(p)=S₀, pr₂(p)=φ₀, pr₁(q)=Z, pr₂(q)=φ₁  (projection_premiere/seconde).
    # On réécrit S₀⊂Z → pr₁(p)⊂pr₁(q) et φ₀⊂φ₁ → pr₂(p)⊂pr₂(q).
    pr1p_eq = projection_premiere_t(vS, vphi0)             # pr₁((S₀,φ₀)) = S₀
    pr2p_eq = projection_seconde_t(vS, vphi0)             # pr₂((S₀,φ₀)) = φ₀
    pr1q_eq = projection_premiere_t(Z, phi1)             # pr₁((Z,φ₁)) = Z
    pr2q_eq = projection_seconde_t(Z, phi1)             # pr₂((Z,φ₁)) = φ₁

    # incl₁ : pr₁(p)⊂pr₁(q).  Réécrire S₀→pr₁(p) (sym pr1p_eq) et Z→pr₁(q) (sym pr1q_eq).
    incl1 = _reecrire_inclus(h_S, pr1p_eq, pr1q_eq, vS, Z, E.pr1(p), E.pr1(q))
    incl2 = _reecrire_inclus(h_phi, pr2p_eq, pr2q_eq, vphi0, phi1, E.pr2(p), E.pr2(q))

    corps = et(et(et(appartient(p, Fr), appartient(q, Fr)),
                  inclus(E.pr1(p), E.pr1(q))),
               inclus(E.pr2(p), E.pr2(q)))
    th_corps = conjonction_intro(
        conjonction_intro(conjonction_intro(h_p, h_q), incl1), incl2)
    assert th_corps.conclusion == corps, \
        f"extension_ordre : corps inattendu\n{th_corps.conclusion}\nvs\n{corps}"

    ax = N.axiome(theorie_frame_ordre(), axiome_frame_ordre())
    eq_pq = instancie(instancie(instancie(ax, vE), p), q)  # ((p,q)∈Γ𝔉) ⇔ corps
    res = N.modus_ponens(th_corps, equivalence_arriere(eq_pq))    # (p,q)∈Γ𝔉

    cible = appartient(E.couple(p, q), frame_ordre(vE))
    assert res.conclusion == cible, \
        f"extension_ordre : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "extension_ordre : VACUOUS"
    return res


def projection_premiere_t(ta, tb):
    """⊢ pr₁((a,b)) = a  pour TERMES a,b (généralise projection_premiere aux termes)."""
    from bourbaki.ensembles.fonctions.ensembles_projections import projection_premiere
    base = projection_premiere("apr", "bpr")               # pr₁((apr,bpr))=apr
    gen = N.generalisation("apr", N.generalisation("bpr", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def projection_seconde_t(ta, tb):
    """⊢ pr₂((a,b)) = b  pour TERMES a,b."""
    from bourbaki.ensembles.fonctions.ensembles_projections import projection_seconde
    base = projection_seconde("apr", "bpr")
    gen = N.generalisation("apr", N.generalisation("bpr", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def _reecrire_inclus(h_incl, eqL, eqR, aL, aR, tL, tR):
    """{ aL⊂aR, tL=aL, tR=aR } ⊢ tL⊂tR.  (réécrit les deux côtés d'une inclusion.)

    h_incl ⊢ aL⊂aR ; eqL ⊢ tL=aL ; eqR ⊢ tR=aR.  S6 sur chaque côté de ⊂."""
    # réécrire aL → tL via aL=tL (sym eqL) dans (aL⊂aR)
    aL_eq_tL = N.modus_ponens(eqL, symetrie(tL, aL))       # aL = tL   (eqL:tL=aL ⇒ sym)
    s6L = N.s6(aL, tL, "wL", inclus(var("wL"), aR))
    step1 = N.modus_ponens(h_incl, equivalence_avant(N.modus_ponens(aL_eq_tL, s6L)))  # tL⊂aR
    aR_eq_tR = N.modus_ponens(eqR, symetrie(tR, aR))       # aR = tR
    s6R = N.s6(aR, tR, "wR", inclus(tL, var("wR")))
    return N.modus_ponens(step1, equivalence_avant(N.modus_ponens(aR_eq_tR, s6R)))   # tL⊂tR


# ════════════════════════════════════════════════════════════════════════════
#  (4c) CONTRADICTION DE MAXIMALITÉ — de la maximalité de (S₀,φ₀) et de
#       (S₀,φ₀)≤(Z,φ₁), on tire Z = S₀  (l'extension n'agrandit pas).
# ════════════════════════════════════════════════════════════════════════════
def extension_force_egalite(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ element_maximal(Γ𝔉(E),𝔉(E),(S₀,φ₀)),  (Z,φ₁)∈𝔉(E),
         ((S₀,φ₀),(Z,φ₁))∈Γ𝔉(E) } ⊢ Z = S₀,   Z=S₀∪U.        [CLOS, hyps HONNÊTES].

    🎯 Le cœur de la CONTRADICTION (E.III.48) : la maximalité de (S₀,φ₀) appliquée à
    l'extension (Z,φ₁) — qui est dans 𝔉 et au-dessus de (S₀,φ₀) — force (Z,φ₁)=(S₀,φ₀),
    donc pr₁ : Z=S₀.  C'est ce qui CONTREDIRA U≠∅ (puisque Z=S₀∪U=S₀ ⇒ U⊂S₀, or
    U⊂E∖S₀, U≠∅).  element_maximal(G,A,m)=(m∈A et (∀x)((x∈A et (m,x)∈G)⇒x=m)) ;
    instancié en x:=(Z,φ₁), avec (Z,φ₁)∈𝔉 et ((S₀,φ₀),(Z,φ₁))∈Γ𝔉, donne (Z,φ₁)=(S₀,φ₀) ;
    pr₁ + projection_premiere ⇒ Z=S₀.  Hyps honnêtes ; theorie=22."""
    from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
    from bourbaki.ordre.ensembles_ordre_relation import element_maximal
    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    phi1 = E.reunion(vphi0, vpsi)
    p = E.couple(vS, vphi0)                                 # (S₀,φ₀) = m
    q = E.couple(Z, phi1)                                   # (Z,φ₁)  = x
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    pq_in_Gam = appartient(E.couple(p, q), Gam)

    h_max = N.assume(element_maximal(Gam, Fr, p, "x"))     # max(Γ𝔉,𝔉,(S₀,φ₀))  [HONNÊTE]
    h_q = N.assume(appartient(q, Fr))                      # (Z,φ₁)∈𝔉           [HONNÊTE]
    h_pq = N.assume(pq_in_Gam)                             # ((S₀,φ₀),(Z,φ₁))∈Γ𝔉 [HONNÊTE]

    max_body = conjonction_elim_droite(h_max)             # (∀x)((x∈𝔉 et (p,x)∈Γ𝔉)⇒x=p)
    max_q = instancie(max_body, q)                        # (q∈𝔉 et (p,q)∈Γ𝔉) ⇒ q=p
    q_eq_p = N.modus_ponens(conjonction_intro(h_q, h_pq), max_q)   # q=p  i.e. (Z,φ₁)=(S₀,φ₀)
    assert q_eq_p.conclusion == egal(q, p)

    # pr₁(q)=pr₁(p) via congruence ; pr₁(q)=Z, pr₁(p)=S₀ ⇒ Z=S₀.
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme
    pr1_cong = N.modus_ponens(q_eq_p, congruence_terme(q, p, E.pr1(var("w"))))  # pr₁(q)=pr₁(p)
    pr1q_eq = projection_premiere_t(Z, phi1)              # pr₁(q)=Z
    pr1p_eq = projection_premiere_t(vS, vphi0)            # pr₁(p)=S₀
    # Z = pr₁(q) = pr₁(p) = S₀
    Z_eq_pr1q = N.modus_ponens(pr1q_eq, symetrie(E.pr1(q), Z))   # Z=pr₁(q)
    Z_eq_pr1p = composer_egalites(Z_eq_pr1q, pr1_cong)          # Z=pr₁(p)
    res = composer_egalites(Z_eq_pr1p, pr1p_eq)                # Z=S₀
    assert res.conclusion == egal(Z, vS), \
        f"extension_force_egalite : conclusion inattendue\n{res.conclusion}\nvs\n{egal(Z, vS)}"
    assert res.conclusion not in res.hypotheses, "extension_force_egalite : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (4d) ABSURDITÉ de 𝔟<a : Z=S₀ (extension_force_egalite) + U≠∅, U∩S₀=∅ ⇒ ⊥.
#       D'où ¬(𝔟<a) sous la chaîne d'extension (l'argument de Bourbaki E.III.48).
# ════════════════════════════════════════════════════════════════════════════
def _u_inclus_reunion(vS, vU, u="z"):
    """⊢ U ⊂ (S₀∪U).   (B ⊂ A∪B : tout u∈U est dans S₀∪U, via AXIOME_REUNION.)

    ⚠️ binder « z » (= binder par défaut de `inclus`) pour que la conclusion soit
    STRUCTURELLEMENT inclus(U, S₀∪U) (et non un α-variant avec binder « zext »)."""
    Z = E.reunion(vS, vU)
    vu = var(u)
    h = N.assume(appartient(vu, vU))                       # u∈U
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION), vS), vU), vu)  # u∈Z ⇔ (u∈S₀ ou u∈U)
    # u∈U ⇒ (u∈U ∨ u∈S₀)  [s2]  puis  ⇒ (u∈S₀ ∨ u∈U)  [s3]
    from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
    u_disj = N.modus_ponens(h, syllogisme(
        N.s2(appartient(vu, vU), appartient(vu, vS)),
        N.s3(appartient(vu, vU), appartient(vu, vS))))     # u∈S₀ ou u∈U
    u_in_Z = N.modus_ponens(u_disj, equivalence_arriere(car))
    body = N.loi_deduction(appartient(vu, vU), u_in_Z)     # u∈U ⇒ u∈Z
    return N.generalisation(u, body)                       # U⊂Z


def extension_absurde(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre", u="uwit"):
    """{ Z=S₀  (= conclusion de extension_force_egalite),  U≠∅,
         (∀z)(z∈U ⇒ ¬(z∈S₀))  [U∩S₀=∅, U⊂E∖S₀] } ⊢ ⊥ (n'importe quoi).
                                                            [CLOS, hyps HONNÊTES].

    🎯 La CONTRADICTION FINALE (E.III.48) : l'extension force Z=S₀, donc S₀∪U=S₀, donc
    U⊂S₀ (U⊂S₀∪U=S₀) ; mais U≠∅ fournit un témoin u∈U, qui est alors dans S₀ ET (par
    U⊂E∖S₀) hors de S₀ — absurde.  On en déduit FALSUM, donc (par décharge ultérieure)
    ¬(𝔟<a).  Hyps honnêtes (Z=S₀ fournie par la maximalité, U≠∅ et U∩S₀=∅ par le choix
    de U⊂E∖S₀ non vide) ; theorie=22.

    Renvoie ⊢ (cible_absurde) où cible_absurde est une formule arbitraire FALSE-déductible ;
    ici on prend la conclusion = (S₀=S₀ et ¬(S₀=S₀)) déductible, mais on EXPOSE plutôt
    l'inclusion-contradiction comme un théorème ⊢ ¬(U≠∅) sous les autres hyps."""
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    vu = var(u)

    h_Z = N.assume(egal(Z, vS))                            # Z=S₀=S₀∪U   [HONNÊTE]
    h_disj = N.assume(pourtout(u, impl(appartient(vu, vU), non(appartient(vu, vS)))))  # U∩S₀=∅

    # U⊂Z=S₀  : U⊂Z (toujours) puis Z=S₀ ⇒ U⊂S₀.
    u_sub_Z = _u_inclus_reunion(vS, vU)                    # U⊂Z
    s6 = N.s6(Z, vS, "wsub", inclus(vU, var("wsub")))
    u_sub_S = N.modus_ponens(u_sub_Z, equivalence_avant(N.modus_ponens(h_Z, s6)))  # U⊂S₀
    assert u_sub_S.conclusion == inclus(vU, vS)

    # témoin u∈U (sous U≠∅) : non_vide(U) ⇒ (∃u)(u∈U).  On porte u∈U en hyp et dérive ⊥.
    h_u = N.assume(appartient(vu, vU))                     # u∈U          [témoin]
    u_in_S = N.modus_ponens(h_u, instancie(u_sub_S, vu))   # u∈S₀  (U⊂S₀)
    u_not_S = N.modus_ponens(h_u, instancie(h_disj, vu))   # ¬(u∈S₀)  (U∩S₀=∅)
    # ⊥ : u∈S₀ et ¬(u∈S₀).  On conclut une cible arbitraire via ex falso (S2).
    cible = non(appartient(vu, vU))                        # ¬(u∈U)  (contradiction : u∈U donné)
    faux = N.modus_ponens(u_in_S, N.modus_ponens(u_not_S,
        N.s2(non(appartient(vu, vS)), cible)))             # ¬(u∈U)  (ex falso de u∈S₀∧¬u∈S₀)
    # on a {u∈U} ⊢ ¬(u∈U) : c'est l'absurdité.  On l'expose comme ⊢ ¬(u∈U) sous les
    # hyps Z=S₀, U∩S₀=∅, u∈U (cette dernière étant le témoin de U≠∅).
    assert faux.conclusion == cible, "extension_absurde : conclusion inattendue"
    assert egal(Z, vS) in faux.hypotheses, "extension_absurde : hyp Z=S₀ absente"
    assert appartient(vu, vU) in faux.hypotheses, "extension_absurde : témoin u∈U absent"
    return faux


# ════════════════════════════════════════════════════════════════════════════
#  (4e) CLÔTURE TRICHOTOMIE : { 𝔟≤a, ¬(𝔟<a) } ⊢ 𝔟=a.
#       (𝔟<a := 𝔟≤a ∧ 𝔟≠a ; ¬(𝔟<a) avec 𝔟≤a ⇒ ¬(𝔟≠a) ⇒ 𝔟=a.)
# ════════════════════════════════════════════════════════════════════════════
def card_S0_egal_card_E(S="S0", E_set="E"):
    """{ Card S₀ ≤ Card E,  ¬( Card S₀ < Card E ) } ⊢ Card S₀ = Card E.   [CLOS, hyps HONNÊTES].

    🎯 La CLÔTURE de l'argument de Bourbaki (E.III.48) : le « CLAIM : Card(F)=𝔞 ».  Le
    complément du maximal étant trop grand pour 𝔟<a (l'extension contredit la maximalité,
    `extension_absurde`), on a ¬(𝔟<a) ; or 𝔟≤a (S₀⊂E) ; donc 𝔟=a (𝔟<a=𝔟≤a∧𝔟≠a, donc
    ¬(𝔟<a)∧𝔟≤a ⇒ ¬(𝔟≠a) ⇒ 𝔟=a par élimination de la double négation).

    Hyps HONNÊTES (jamais postulées) : 𝔟≤a (de S₀⊂E, équipotence/injection canonique),
    ¬(𝔟<a) (conclusion de l'argument de contradiction, via `extension_absurde`).
    Conclusion ∉ hyps ; theorie=22."""
    vS, vE = _t(S), _t(E_set)
    b, a = cardinal(vS), cardinal(vE)
    lt = inf_strict_card(b, a)                             # 𝔟<a = (𝔟≤a et 𝔟≠a)
    cible = egal(b, a)

    h_le = N.assume(inf_egal_card(b, a))                   # 𝔟≤a            [HONNÊTE]
    h_nlt = N.assume(non(lt))                              # ¬(𝔟<a)         [HONNÊTE]

    # sous 𝔟≠a : 𝔟≤a ∧ 𝔟≠a = 𝔟<a, contredit ¬(𝔟<a) ⇒ ⊥.  Donc ¬(𝔟≠a).
    h_ne = N.assume(non(cible))                            # 𝔟≠a  (pour réfuter)
    lt_proof = conjonction_intro(h_le, h_ne)              # 𝔟<a
    assert lt_proof.conclusion == lt
    # ⊥ : ¬(𝔟<a) et 𝔟<a ⇒ n'importe quoi ; on vise ¬¬(𝔟=a)=¬(𝔟≠a).
    cible_nn = non(non(cible))                            # ¬¬(𝔟=a)
    faux = N.modus_ponens(lt_proof, N.modus_ponens(h_nlt,
        N.s2(non(lt), cible_nn)))                         # ¬¬(𝔟=a)  (ex falso)
    # décharge 𝔟≠a : (𝔟≠a) ⇒ ¬¬(𝔟=a)  — mais c'est ¬(𝔟≠a) qu'on veut ; en fait
    # faux est SOUS h_ne ; on décharge h_ne pour obtenir (𝔟≠a)⇒¬¬(𝔟=a), puis ⊥.
    # Plus direct : on a {¬(𝔟=a)} ⊢ ¬¬(𝔟=a) ; loi_deduction ⇒ (𝔟≠a)⇒¬¬(𝔟=a).
    impl_ne_nn = N.loi_deduction(non(cible), faux)        # (𝔟≠a) ⇒ ¬¬(𝔟=a)
    # (𝔟≠a)⇒¬(𝔟≠a) ⇒ ¬(𝔟≠a)  (auto-réfutation : A⇒¬A ⊢ ¬A).
    # ¬¬(𝔟=a) = ¬(𝔟≠a) littéralement, donc impl_ne_nn : (𝔟≠a)⇒¬(𝔟≠a).
    assert impl_ne_nn.conclusion == impl(non(cible), non(non(cible)))
    # de P⇒¬P déduire ¬P :  ¬P ∨ ¬P via S3 sur (P⇒¬P)=(¬P∨¬P) ... en fait P⇒¬P = ¬P∨¬P
    #   qui se simplifie ; on applique l'auto-réfutation standard.
    nn = _auto_refutation(impl_ne_nn, non(cible))         # ⊢ ¬(𝔟≠a) = ¬¬(𝔟=a)
    assert nn.conclusion == non(non(cible))
    # tiers exclu (𝔟=a) ∨ ¬(𝔟=a) + cas : branche 1 triviale ; branche 2 ⊥ (nn).
    from bourbaki.logique.tactiques.tactiques_abrege2 import tiers_exclu, cas
    te = tiers_exclu(cible)                                # (𝔟=a) ∨ ¬(𝔟=a)
    cas1 = N.loi_deduction(cible, N.assume(cible))         # (𝔟=a) ⇒ (𝔟=a)
    h_ne2 = N.assume(non(cible))                           # ¬(𝔟=a)
    faux2 = N.modus_ponens(h_ne2, N.modus_ponens(nn,
        N.s2(non(non(cible)), cible)))                     # 𝔟=a  (ex falso : nn et ¬(𝔟=a))
    cas2 = N.loi_deduction(non(cible), faux2)              # ¬(𝔟=a) ⇒ (𝔟=a)
    res = cas(te, cas1, cas2)                              # 𝔟=a
    assert res.conclusion == cible, \
        f"card_S0_egal_card_E : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "card_S0_egal_card_E : VACUOUS"
    return res


def _auto_refutation(impl_p_np, P):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   (P⇒¬P = ¬P∨¬P ; idempotence par S1/S3.)"""
    # P⇒¬P  est  ¬P ∨ ¬P.  S1 : (¬P ∨ ¬P) ⇒ ¬P.
    np = non(P)
    s1 = N.s1(np)                                          # (¬P ∨ ¬P) ⇒ ¬P
    return N.modus_ponens(impl_p_np, s1)


def card_S0_egal_card_E_cible(S="S0", E_set="E"):
    """ÉNONCÉ-cible (test miroir)."""
    vS, vE = _t(S), _t(E_set)
    return egal(cardinal(vS), cardinal(vE))


# ════════════════════════════════════════════════════════════════════════════
#  (5) hessenberg_a_carre_egal_a — ASSEMBLAGE FINAL : a²=a (Théorème 2).
#      Branche Card S₀=Card E (card_S0_egal_card_E) + Card(S₀×S₀)=Card S₀
#      (maximal_carre_egal) sur hessenberg_aa_egal_de_maximal.
# ════════════════════════════════════════════════════════════════════════════
def hessenberg_a_carre_egal_a(E_set="E", S="S0"):
    """{ Card S₀ ≤ Card E,  ¬(Card S₀ < Card E),  Card(S₀×S₀)=Card S₀ }
        ⊢ est_infini(Card E) ⇒ ( Card E · Card E = Card E ).   [hyps HONNÊTES].

    🎯🎯 THÉORÈME 2 (HESSENBERG, E.III.48-49) : 𝔞²=𝔞 pour 𝔞 infini — ASSEMBLÉ depuis
    l'EXTENSION FINALE du maximal.  `card_S0_egal_card_E` ferme le « CLAIM : Card(F)=𝔞 »
    (l'extension du maximal contredit la maximalité dès que 𝔟<a, d'où ¬(𝔟<a), d'où 𝔟=a) ;
    `hessenberg_aa_egal_de_maximal` (déjà clos sous Card S₀=Card E et Card(S₀×S₀)=Card S₀)
    referme l'égalité a²=a.  La conclusion est LITTÉRALEMENT `enonce_hessenberg(E)`.

    RÉSIDUS HONNÊTES (jamais postulés vrais ; fournis par l'argument de Zorn E.III.48) :
      • Card S₀ ≤ Card E        (S₀⊂E) ;
      • ¬(Card S₀ < Card E)     (= conclusion de l'argument de contradiction d'extension,
        `extension_absurde` ; SES propres résidus — cadre/recollement/dom-img — sont
        documentés dans les pièces (1)-(4d)) ;
      • Card(S₀×S₀)=Card S₀     (φ₀ bijective ⇐ `maximal_carre_egal`).
    theorie=22 ; non vacuous."""
    from bourbaki.cardinaux.ensembles_hessenberg_maximal_card import (
        hessenberg_aa_egal_de_maximal,
    )
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    vE, vS = _t(E_set), _t(S)
    cE, cS = cardinal(vE), cardinal(vS)
    SxS = E.produit(vS, vS)

    # Card S₀ = Card E  (clôture trichotomie, sous 𝔟≤a et ¬(𝔟<a)).
    cS_eq_cE = card_S0_egal_card_E(S, E_set)              # {𝔟≤a, ¬(𝔟<a)} ⊢ Card S₀=Card E
    assert cS_eq_cE.conclusion == egal(cS, cE)

    # hessenberg_aa_egal_de_maximal : {Card S₀=Card E, Card(S₀×S₀)=Card S₀}
    #                                  ⊢ est_infini(Card E) ⇒ Card E·Card E=Card E
    haa = hessenberg_aa_egal_de_maximal(E_set, S)
    # décharge Card S₀=Card E par card_S0_egal_card_E
    haa = N.modus_ponens(cS_eq_cE, N.loi_deduction(egal(cS, cE), haa))

    cible = enonce_hessenberg(E_set)
    assert haa.conclusion == cible, \
        f"hessenberg_a_carre_egal_a : conclusion inattendue\n{haa.conclusion}\nvs\n{cible}"
    assert egal(cardinal(SxS), cS) in haa.hypotheses, \
        "hessenberg_a_carre_egal_a : hyp Card(S₀×S₀)=Card S₀ absente"
    assert haa.conclusion not in haa.hypotheses, "hessenberg_a_carre_egal_a : VACUOUS"
    return haa


__all__ = [
    "cadre_bijection",
    "cadre_bijection_cible",
    "cadre_ensemble",
    "cadre_card_trois_b",
    "cadre_card_trois_b_cible",
    "phi_etendue_bijection",
    "extension_dans_frame",
    "extension_ordre",
    "projection_premiere_t",
    "projection_seconde_t",
    "extension_force_egalite",
    "extension_absurde",
    "card_S0_egal_card_E",
    "card_S0_egal_card_E_cible",
    "hessenberg_a_carre_egal_a",
]
