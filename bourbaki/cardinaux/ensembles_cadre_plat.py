"""§III.6.3 — CADRE PLAT (Hessenberg a²=a, déverrouillage hyp[2] de la chaîne).

🎯 OBJECTIF.  La chaîne de contradiction de Hessenberg (`chaine_falsum_sous_temoins`)
porte une hypothèse-MUR `(S₀×S₀) ∪ cadre_tagged = Z²` où `cadre_tagged` est en
SOMME-DISJOINTE (tags ×{∅}/×{∅,{∅}}).  Or l'identité géométrique CLOSE 0-hyp
`s0sq_cadre_reunion_egale_carre` prouve la version PLATE (en RÉUNION) :

    (S₀×S₀) ∪ F_plain = Z×Z,   Z = S₀∪U,
    F_plain = (S₀×U) ∪ ( (U×S₀) ∪ (U×U) )   [réunions, PAS sommes disjointes].

Ce module reconstruit le cadre en RÉUNION PLATE pour que `s0sq` s'apparie et que
hyp[2] se DÉCHARGE.  Il fournit, bottom-up :

  P1 `cadre_plat_blocs_disjoints`  — les 3 blocs plats deux à deux disjoints (sous
      U∩S₀=∅), et SxU ∩ ((U×S₀)∪(U×U)) = ∅ via distributivité ∩/∪.
  P2 `cadre_plat_cardinal`         — Card(F_plain) = Card S₀ = 𝔟 (3𝔟 = 𝔟), miroir
      PLAT de `cadre_card_trois_b` (réunions disjointes au lieu de ⊔).
  P3 `cadre_plat_bijection`        — (∃ψ) bij(ψ, F_plain, U).

INVARIANT : theorie_ensembles() = 22.  Aucun axiome ; rien postulé ; tout DÉRIVE de
théorèmes CLOS sous les SEULES gardes honnêtes.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ensembles.familles.ensembles_produit import _instance_produit
from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.ensembles_algebre_booleenne import (
    _instance_inter, distributivite_intersection_reunion,
)
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _vide_inst(vz):
    """⊢ ¬(z ∈ ∅)   (instance de AXIOME_VIDE)."""
    return instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)


def _efq(notP_thm, q):
    """De ⊢¬P, déduire ⊢ (P ⇒ Q)   (ex falso quodlibet)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dni, dne, contraposition
    P = notP_thm.conclusion.sous[0]
    h = N.loi_deduction(non(q), notP_thm)             # ¬Q ⇒ ¬P
    return syllogisme(syllogisme(dni(P), contraposition(h)), dne(q))   # P ⇒ Q


# ════════════════════════════════════════════════════════════════════════════
#  Cœur : un bloc-produit (A₁×B₁) ∩ (A₂×B₂) est VIDE dès qu'une COORDONNÉE
#  partagée tombe dans deux ensembles disjoints.
# ════════════════════════════════════════════════════════════════════════════
def _bloc_produit_disjoint(A1, B1, A2, B2, n_commun, coord, z="z"):
    """⊢ (A₁×B₁) ∩ (A₂×B₂) = ∅, sous l'hypothèse (portée par `n_commun`) qu'aucune
    valeur ne peut être à la fois dans la coordonnée partagée des deux produits.

    `coord` ∈ {"premiere","seconde"} indique laquelle des deux coordonnées entre en
    collision.  `n_commun(t)` doit renvoyer un théorème ⊢ ¬( t∈Xgauche et t∈Xdroite )
    pour un TERME t (la valeur de la coordonnée partagée), où Xgauche est la coord. du
    PREMIER produit et Xdroite celle du SECOND.  Preuve par extensionnalité : tout
    z∈(A₁×B₁)∩(A₂×B₂) se décompose z=(p,q) et z=(p',q') ; l'égalité des couples
    identifie la coordonnée partagée, d'où la contradiction → z∈∅ (ex falso).  La
    réciproque z∈∅⇒z∈inter est vide (ex falso de ¬(z∈∅))."""
    vA1, vB1, vA2, vB2 = _t(A1), _t(B1), _t(A2), _t(B2)
    P1, P2 = E.produit(vA1, vB1), E.produit(vA2, vB2)
    inter = E.intersection(P1, P2)
    vz = var(z)
    zV = appartient(vz, E.VIDE)

    # ── forward : z∈inter ⇒ z∈∅ ───────────────────────────────────────────────
    z_in_inter = N.assume(appartient(vz, inter))
    pair = N.modus_ponens(z_in_inter, equivalence_avant(_instance_inter(P1, P2, vz)))
    z_in_P1 = conjonction_elim_gauche(pair)                  # z∈A₁×B₁
    z_in_P2 = conjonction_elim_droite(pair)                  # z∈A₂×B₂

    # déballer z∈A₁×B₁ = (∃p)(∃q)(z=(p,q) et p∈A₁ et q∈B₁), témoins p,q (binders de l'axiome).
    ex1 = N.modus_ponens(z_in_P1, equivalence_avant(_instance_produit(vA1, vB1, vz)))
    vp, vq = var("p"), var("q")
    body1 = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vA1)), appartient(vq, vB1))

    # Sous {body1} : z=(p,q), p∈A₁, q∈B₁ ; on réécrit z∈A₂×B₂ → (p,q)∈A₂×B₂ et on
    # déplie en p∈A₂ et q∈B₂ via _couple_in_produit (binders internes rr,ss ≠ p,q).
    def from_temoins():
        h1 = N.assume(body1)
        zpq = conjonction_elim_gauche(conjonction_elim_gauche(h1))    # z=(p,q)
        pA1 = conjonction_elim_droite(conjonction_elim_gauche(h1))    # p∈A₁
        qB1 = conjonction_elim_droite(h1)                            # q∈B₁
        # (p,q)∈A₂×B₂  : réécrire z→(p,q) dans z∈A₂×B₂.
        pq_in_P2 = N.modus_ponens(z_in_P2, equivalence_avant(
            N.modus_ponens(zpq, N.s6(vz, E.couple(vp, vq), "wz",
                                     appartient(var("wz"), P2)))))    # (p,q)∈A₂×B₂
        comps2 = N.modus_ponens(pq_in_P2, _couple_in_produit(vp, vq, vA2, vB2))  # p∈A₂ et q∈B₂
        pA2 = conjonction_elim_gauche(comps2)                        # p∈A₂
        qB2 = conjonction_elim_droite(comps2)                        # q∈B₂
        if coord == "premiere":
            commun = conjonction_intro(pA1, pA2)                    # p∈A₁ et p∈A₂
            ncom = n_commun(vp)
        else:
            commun = conjonction_intro(qB1, qB2)                    # q∈B₁ et q∈B₂
            ncom = n_commun(vq)
        # contradiction : commun et ¬commun → z∈∅ (ex falso).
        return N.modus_ponens(commun, _efq(ncom, zV))               # z∈∅

    inner = from_temoins()                                          # {body1} ⊢ z∈∅
    step_b1 = N.loi_deduction(body1, inner)
    elim_q1 = existe_elimination(step_b1, "q")
    elim_p1 = existe_elimination(elim_q1, "p")                      # (∃p)(∃q)body1 ⇒ z∈∅
    z_vide = N.modus_ponens(ex1, elim_p1)                           # z∈∅  (sous {z∈inter})
    fwd = N.loi_deduction(appartient(vz, inter), z_vide)           # z∈inter ⇒ z∈∅

    # ── backward : z∈∅ ⇒ z∈inter  (ex falso) ──────────────────────────────────
    bwd = _efq(_vide_inst(vz), appartient(vz, inter))             # z∈∅ ⇒ z∈inter

    equiv = conjonction_intro(fwd, bwd)                           # z∈inter ⇔ z∈∅
    char_u = N.generalisation(z, equiv)
    char_v = N.generalisation(z, conjonction_intro(
        N.loi_deduction(zV, N.assume(zV)), N.loi_deduction(zV, N.assume(zV))))  # z∈∅⇔z∈∅
    res = egalite_par_extension(char_u, char_v, inter, E.VIDE, x=z)
    assert res.conclusion == egal(inter, E.VIDE), res.conclusion
    return res


def _couple_in_produit(tu, tv, ta, tb):
    """⊢ ((u,v) ∈ A×B) ⇒ (u∈A et v∈B)  pour des TERMES u,v,A,B QUELCONQUES (capture-safe).

    `couple_dans_produit_ssi` interdit que les composantes u,v soient nommées p,q (ses
    binders internes).  On la construit donc sur des NOMS FRAIS (uu,vv,AA,BB), on
    GÉNÉRALISE, puis on INSTANCIE aux TERMES — robuste même pour u=p, v=q (motif _t)."""
    from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
    base = couple_dans_produit_ssi("uu", "vv", "AA", "BB")   # ssi CLOS, noms ≠ p,q
    av = equivalence_avant(base)                             # (uu,vv)∈AA×BB ⇒ (uu∈AA et vv∈BB)
    gen = N.generalisation("uu", N.generalisation("vv",
              N.generalisation("AA", N.generalisation("BB", av))))
    return instancie(instancie(instancie(instancie(gen, _t(tu)), _t(tv)),
                               _t(ta)), _t(tb))


def _n_commun_de_disjoint(disj_thm, X, Y):
    """De ⊢ X∩Y=∅, fabrique t ↦ (⊢ ¬(t∈X et t∈Y)) pour un TERME t.

    Utilise `_disjoint_to_forall` (X∩Y=∅ ⇒ (∀u)¬(u∈X et u∈Y)) puis instancie."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final._recollement import (
        _disjoint_to_forall,
    )
    vX, vY = _t(X), _t(Y)
    forall = N.modus_ponens(disj_thm, _disjoint_to_forall(vX, vY))   # (∀u)¬(u∈X et u∈Y)

    def n_commun(t):
        return instancie(forall, _t(t))
    return n_commun


# ════════════════════════════════════════════════════════════════════════════
#  P1 — les 3 blocs plats deux à deux disjoints + SxU ∩ ((U×S₀)∪(U×U)) = ∅.
# ════════════════════════════════════════════════════════════════════════════
def cadre_plat_blocs_disjoints(S="S0", U="Ucadre"):
    """{ U∩S₀ = ∅ } ⊢ ( (S₀×U)∩(U×S₀)=∅  et  (S₀×U)∩(U×U)=∅
                          et  (U×S₀)∩(U×U)=∅  et  (S₀×U)∩((U×S₀)∪(U×U))=∅ ).
                                                            [1 hyp HONNÊTE : U∩S₀=∅].

    🎯 P1 : les 3 blocs PLATS du cadre F_plain = (S₀×U)∪((U×S₀)∪(U×U)) sont deux à deux
    disjoints (comme ENSEMBLES PLATS), et le bloc-tête S₀×U est disjoint de la réunion
    des deux autres (via distributivité ∩/∪).  Chaque disjonction vient d'une COLLISION
    de coordonnée : un même point serait à la fois dans S₀ et dans U (resp. dans U et
    S₀), or U∩S₀=∅.  Hyp honnête U∩S₀=∅ = le choix U⊂E∖S₀.  theorie=22."""
    vS, vU = _t(S), _t(U)
    SxU = E.produit(vS, vU)
    UxS = E.produit(vU, vS)
    UxU = E.produit(vU, vU)

    h_disj = N.assume(E.sont_disjoints(vU, vS))             # U∩S₀=∅   [HONNÊTE]
    n_US = _n_commun_de_disjoint(h_disj, vU, vS)            # t↦¬(t∈U et t∈S₀)

    # (a) (S₀×U)∩(U×S₀)=∅ : 1ʳᵉ coordonnée p∈S₀ (gauche) et p∈U (droite) → ¬(p∈S₀ et p∈U).
    #     n_commun(p) doit donner ¬(p∈S₀ et p∈U) [Xgauche=S₀, Xdroite=U].
    n_SU = _n_commun_de_disjoint(
        N.modus_ponens(h_disj, _sym_disjoint(vU, vS)), vS, vU)   # t↦¬(t∈S₀ et t∈U)
    bloc_a = _bloc_produit_disjoint(vS, vU, vU, vS, n_SU, "premiere")
    assert bloc_a.conclusion == egal(E.intersection(SxU, UxS), E.VIDE)

    # (b) (S₀×U)∩(U×U)=∅ : 1ʳᵉ coordonnée p∈S₀ (gauche) et p∈U (droite).
    bloc_b = _bloc_produit_disjoint(vS, vU, vU, vU, n_SU, "premiere")
    assert bloc_b.conclusion == egal(E.intersection(SxU, UxU), E.VIDE)

    # (c) (U×S₀)∩(U×U)=∅ : 2ᵉ coordonnée q∈S₀ (gauche) et q∈U (droite).
    bloc_c = _bloc_produit_disjoint(vU, vS, vU, vU, n_SU, "seconde")
    assert bloc_c.conclusion == egal(E.intersection(UxS, UxU), E.VIDE)

    # (S₀×U) ∩ ((U×S₀)∪(U×U)) = ∅  via distributivité ∩/∪ + (a)+(b)+∪(∅,∅)=∅.
    UxS_UxU = E.reunion(UxS, UxU)
    distr = distributivite_intersection_reunion(SxU, UxS, UxU)   # SxU∩(UxS∪UxU)=(SxU∩UxS)∪(SxU∩UxU)
    # réécrire (SxU∩UxS)→∅ (bloc_a) et (SxU∩UxU)→∅ (bloc_b) dans le RHS.
    rhs_inter = distr.conclusion.termes[1]                      # (SxU∩UxS)∪(SxU∩UxU)
    rw_a = N.modus_ponens(bloc_a, N.s6(E.intersection(SxU, UxS), E.VIDE, "wa",
        egal(E.intersection(SxU, UxS_UxU), E.reunion(var("wa"), E.intersection(SxU, UxU)))))
    step_a = N.modus_ponens(distr, equivalence_avant(rw_a))     # = ∅∪(SxU∩UxU)
    rw_b = N.modus_ponens(bloc_b, N.s6(E.intersection(SxU, UxU), E.VIDE, "wb",
        egal(E.intersection(SxU, UxS_UxU), E.reunion(E.VIDE, var("wb")))))
    step_b = N.modus_ponens(step_a, equivalence_avant(rw_b))    # = ∅∪∅
    # ∅∪∅=∅
    from bourbaki.ensembles.ensembles_vide_identites import reunion_vide_neutre
    vide_union = reunion_vide_neutre(E.VIDE)                    # ∅∪∅=∅
    bloc_tete = composer_egalites(step_b, vide_union)           # SxU∩(UxS∪UxU)=∅
    assert bloc_tete.conclusion == egal(E.intersection(SxU, UxS_UxU), E.VIDE)

    res = conjonction_intro(conjonction_intro(conjonction_intro(bloc_a, bloc_b), bloc_c),
                            bloc_tete)
    cible = et(et(et(egal(E.intersection(SxU, UxS), E.VIDE),
                     egal(E.intersection(SxU, UxU), E.VIDE)),
                  egal(E.intersection(UxS, UxU), E.VIDE)),
               egal(E.intersection(SxU, UxS_UxU), E.VIDE))
    assert res.conclusion == cible, f"{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cadre_plat_blocs_disjoints : VACUOUS"
    return res


def _sym_disjoint(X, Y):
    """⊢ (X∩Y=∅) ⇒ (Y∩X=∅).   (commutativité de ∩ transportée à l'égalité au vide.)"""
    from bourbaki.ensembles.ensembles_theoremes import commutativite_intersection
    vX, vY = _t(X), _t(Y)
    h = N.assume(E.sont_disjoints(vX, vY))                  # X∩Y=∅
    comm = commutativite_intersection_t(vY, vX)             # Y∩X = X∩Y
    res = composer_egalites(comm, h)                        # Y∩X=∅
    return N.loi_deduction(E.sont_disjoints(vX, vY), res)


def commutativite_intersection_t(ta, tb):
    """⊢ A∩B = B∩A  pour des TERMES (généralise commutativite_intersection)."""
    from bourbaki.ensembles.ensembles_theoremes import commutativite_intersection
    base = commutativite_intersection("Aci", "Bci")
    gen = N.generalisation("Aci", N.generalisation("Bci", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def cadre_plat_blocs_disjoints_cible(S="S0", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir)."""
    vS, vU = _t(S), _t(U)
    SxU, UxS, UxU = E.produit(vS, vU), E.produit(vU, vS), E.produit(vU, vU)
    return impl(E.sont_disjoints(vU, vS),
                et(et(et(egal(E.intersection(SxU, UxS), E.VIDE),
                         egal(E.intersection(SxU, UxU), E.VIDE)),
                      egal(E.intersection(UxS, UxU), E.VIDE)),
                   egal(E.intersection(SxU, E.reunion(UxS, UxU)), E.VIDE)))


# ════════════════════════════════════════════════════════════════════════════
#  P2 — Card(F_plain) = Card S₀ = 𝔟  (3𝔟 = 𝔟), miroir PLAT de cadre_card_trois_b.
# ════════════════════════════════════════════════════════════════════════════
def _card_reunion_de_somme(A, B, ca, cb, disj_thm):
    """{ Card A = ca, Card B = cb } ∪ ⟨disj_thm ⊢ A∩B=∅⟩
        ⊢ Card(A∪B) = somme_cardinale_binaire(ca, cb).

    Pont RÉUNION DISJOINTE → SOMME CARDINALE.  Sous A∩B=∅ : Eq(A∪B, A⊔B)
    (_eq_reunion_disjointe_somme_t) ⇒ Card(A∪B)=Card(A⊔B) (_prop1_direct_tt) ; puis
    Card(A⊔B)=ca+cb (_somme_disjointe_cardinal_t sous Card A=ca, Card B=cb).  Tout
    capture-safe (helpers _t).  `disj_thm` ⊢ A∩B=∅ est CONSOMMÉ (modus ponens)."""
    from bourbaki.cardinaux.ensembles_prop13_complement import (
        _eq_reunion_disjointe_somme_t, _prop1_direct_tt, _somme_disjointe_cardinal_t,
    )
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
        somme_disjointe, somme_cardinale_binaire,
    )
    vA, vB, vca, vcb = _t(A), _t(B), _t(ca), _t(cb)
    AuB = E.reunion(vA, vB)
    AsB = somme_disjointe(vA, vB)
    # Eq(A∪B, A⊔B) sous A∩B=∅
    eq_us = N.modus_ponens(disj_thm, _eq_reunion_disjointe_somme_t(vA, vB))   # Eq(A∪B,A⊔B)
    card_eq = N.modus_ponens(eq_us, _prop1_direct_tt(AuB, AsB))               # Card(A∪B)=Card(A⊔B)
    # Card(A⊔B) = ca+cb  sous Card A=ca, Card B=cb
    sdc = _somme_disjointe_cardinal_t(vA, vB, vca, vcb)
    h_cA = N.assume(egal(cardinal(vA), vca))
    h_cB = N.assume(egal(cardinal(vB), vcb))
    card_s = N.modus_ponens(conjonction_intro(h_cA, h_cB), sdc)               # Card(A⊔B)=ca+cb
    res = composer_egalites(card_eq, card_s)                                  # Card(A∪B)=ca+cb
    assert res.conclusion == egal(cardinal(AuB), somme_cardinale_binaire(vca, vcb))
    return res, h_cA.conclusion, h_cB.conclusion


def cadre_plat_cardinal(S="S0", U="Ucadre"):
    """{ Card S₀ = Card U,  𝔟·𝔟 = 𝔟,  est_cardinal(𝔟),  est_infini(𝔟),  U∩S₀ = ∅ }
        ⊢ Card(F_plain) = Card S₀,   𝔟 := Card S₀,
        F_plain = (S₀×U) ∪ ((U×S₀) ∪ (U×U)).               [hyps HONNÊTES].

    🎯 P2 : le cadre PLAT a pour cardinal 3𝔟 = 𝔟 (E.III.48).  Miroir EXACT de
    `cadre_card_trois_b` mais sur des RÉUNIONS PLATES (au lieu de sommes disjointes ⊔) :
    la disjointness des blocs (P1, sous U∩S₀=∅) permet de remplacer chaque ∪ par un ⊔
    au niveau des cardinaux (`_card_reunion_de_somme`).  Card(S₀×U)=Card(U×S₀)=
    Card(U×U)=𝔟 (`_card_produit_egal_b`) ; Card((U×S₀)∪(U×U))=𝔟+𝔟 ; Card(F_plain)=
    𝔟+(𝔟+𝔟)=3𝔟=𝔟 (`trois_b_egal_b_inconditionnel` + pont bien-déf, repris VERBATIM de
    cadre_card_trois_b).  theorie=22 ; conclusion ∉ hyps."""
    from bourbaki.cardinaux.ensembles_frame_extension_finale import _card_produit_egal_b
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_binaire,
    )
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
        somme_disjointe, somme_cardinale_binaire,
    )
    from bourbaki.cardinaux.ensembles_descentes_inconditionnelles import (
        trois_b_egal_b_inconditionnel, _bien_definie_t,
    )
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
    from bourbaki.cardinaux.ensembles_equipotence_retrait import equipotence_reflexive_pour
    from bourbaki.entiers.ensembles_infinis import est_infini

    vS, vU = _t(S), _t(U)
    b = cardinal(vS)                                        # 𝔟 = Card S₀
    cU = cardinal(vU)
    bb = produit_cardinal_binaire(b, b)                     # 𝔟·𝔟
    SxU, UxS, UxU = E.produit(vS, vU), E.produit(vU, vS), E.produit(vU, vU)
    UxS_UxU = E.reunion(UxS, UxU)                           # (U×S₀)∪(U×U)
    Fp = E.reunion(SxU, UxS_UxU)                            # F_plain
    cible = egal(cardinal(Fp), b)

    # ── hyps honnêtes ───────────────────────────────────────────────────────────
    h_cardU = N.assume(egal(b, cU))                         # Card S₀ = Card U
    h_bb = N.assume(egal(bb, b))                            # 𝔟·𝔟 = 𝔟
    h_card_b = N.assume(est_cardinal(b))                    # est_cardinal(𝔟)
    h_inf_b = N.assume(est_infini(b))                       # est_infini(𝔟)
    h_disjUS = N.assume(E.sont_disjoints(vU, vS))           # U∩S₀ = ∅

    cU_eq_b = N.modus_ponens(h_cardU, symetrie(b, cU))      # Card U = 𝔟
    cS_eq_b = N.reflexivite(b)                              # Card S₀ = 𝔟

    # ── blocs disjoints (P1) ────────────────────────────────────────────────────
    blocs = N.modus_ponens(h_disjUS, N.loi_deduction(
        E.sont_disjoints(vU, vS), cadre_plat_blocs_disjoints(S, U)))
    # blocs = (a et b et c et tete) ; on extrait (c) et (tête).
    disj_c = conjonction_elim_droite(conjonction_elim_gauche(blocs))    # (U×S₀)∩(U×U)=∅
    disj_tete = conjonction_elim_droite(blocs)                          # (S₀×U)∩((U×S₀)∪(U×U))=∅

    # ── Card de chaque facteur = 𝔟  (déchargeant les 3 hyps de _card_produit_egal_b) ──
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

    # ── Card((U×S₀)∪(U×U)) = 𝔟+𝔟  (réunion disjointe (c)) ────────────────────────
    bplusb = somme_cardinale_binaire(b, b)
    inner_thm, need_cUxS, need_cUxU = _card_reunion_de_somme(UxS, UxU, b, b, disj_c)
    card_inner = N.modus_ponens(card_UxS, N.loi_deduction(need_cUxS,
                  N.modus_ponens(card_UxU, N.loi_deduction(need_cUxU, inner_thm))))
    assert card_inner.conclusion == egal(cardinal(UxS_UxU), bplusb)

    # ── Card(F_plain) = 𝔟+(𝔟+𝔟)  (réunion disjointe tête) ───────────────────────
    threeb = somme_cardinale_binaire(b, bplusb)
    tete_thm, need_cSxU, need_cInner = _card_reunion_de_somme(SxU, UxS_UxU, b, bplusb, disj_tete)
    card_F = N.modus_ponens(card_SxU, N.loi_deduction(need_cSxU,
              N.modus_ponens(card_inner, N.loi_deduction(need_cInner, tete_thm))))
    assert card_F.conclusion == egal(cardinal(Fp), threeb)

    # ── 3𝔟 = 𝔟  (VERBATIM de cadre_card_trois_b : trois_b + pont bien-déf) ──────
    t3_var = trois_b_egal_b_inconditionnel("b3incond")
    t3 = instancie(N.generalisation("b3incond", t3_var), b)
    t3_app = N.modus_ponens(conjonction_intro(conjonction_intro(
        h_card_b, h_inf_b), h_bb), t3)                     # somme_cardinale_binaire(𝔟,𝔟⊔𝔟)=𝔟
    bb_set = somme_disjointe(b, b)                         # 𝔟⊔𝔟
    threeb_set = somme_cardinale_binaire(b, bb_set)
    assert t3_app.conclusion == egal(threeb_set, b)

    eq_set_card = instancie(N.generalisation("X", equipotent_son_cardinal("X")), bb_set)
    assert bplusb == cardinal(bb_set), "cadre_plat_cardinal : 𝔟+𝔟 ≠ Card(𝔟⊔𝔟) littéral"
    eq_bb = equipotence_reflexive_pour(b)
    bd = _bien_definie_t(b, bb_set, b, bplusb)
    bridge = N.modus_ponens(conjonction_intro(eq_bb, eq_set_card), bd)
    assert bridge.conclusion == egal(threeb_set, threeb)
    threeb_eq_set = N.modus_ponens(bridge, symetrie(threeb_set, threeb))   # threeb=threeb_set
    threeb_eq_b = composer_egalites(threeb_eq_set, t3_app)                 # threeb=𝔟

    res = composer_egalites(card_F, threeb_eq_b)
    assert res.conclusion == cible, f"{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cadre_plat_cardinal : VACUOUS"
    return res


def cadre_plat_cardinal_cible(S="S0", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir)."""
    vS = _t(S)
    return egal(cardinal(cadre_plat(S, U)), cardinal(vS))


# ════════════════════════════════════════════════════════════════════════════
#  P3 — (∃ψ) bij(ψ, F_plain, U)  depuis Card(F_plain)=Card U.
# ════════════════════════════════════════════════════════════════════════════
def cadre_plat_bijection(S="S0", U="Ucadre"):
    """{ Card S₀ = Card U,  𝔟·𝔟 = 𝔟,  est_cardinal(𝔟),  est_infini(𝔟),  U∩S₀ = ∅ }
        ⊢ (∃ψ) est_bijection_de(ψ, F_plain, U),  F_plain=(S₀×U)∪((U×S₀)∪(U×U)).
                                                            [hyps HONNÊTES].

    🎯 P3 : du cardinal du cadre PLAT (P2, Card F_plain=Card S₀) et de Card S₀=Card U,
    on tire Card F_plain=Card U, d'où une BIJECTION ψ:F_plain→U (`cadre_bijection`, Prop 1
    réciproque).  Mêmes 5 gardes honnêtes que P2.  theorie=22 ; conclusion ∉ hyps."""
    from bourbaki.cardinaux.ensembles_frame_extension_finale import cadre_bijection
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vS, vU = _t(S), _t(U)
    Fp = cadre_plat(S, U)
    b, cU = cardinal(vS), cardinal(vU)

    # Card(F_plain) = Card S₀   (P2)
    card_F = cadre_plat_cardinal(S, U)                      # Card F_plain = 𝔟
    # Card S₀ = Card U  (hyp honnête, déjà parmi les hyps de card_F)
    h_cardU = N.assume(egal(b, cU))                         # Card S₀ = Card U
    # Card(F_plain) = Card U
    card_F_eq_cU = composer_egalites(card_F, h_cardU)       # Card F_plain = Card U
    assert card_F_eq_cU.conclusion == egal(cardinal(Fp), cU)

    # cadre_bijection(F_plain, U) : (Card F_plain=Card U) ⇒ (∃ψ)bij(ψ,F_plain,U)
    cb = cadre_bijection(Fp, vU)
    res = N.modus_ponens(card_F_eq_cU, cb)                  # (∃ψ)bij(ψ,F_plain,U)
    assert res.conclusion == equipotent(Fp, vU), \
        f"cadre_plat_bijection : conclusion inattendue\n{res.conclusion}"
    assert res.conclusion not in res.hypotheses, "cadre_plat_bijection : VACUOUS"
    return res


def cadre_plat_bijection_cible(S="S0", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir) : equipotent(F_plain, U) = (∃ψ)bij(ψ,F_plain,U)."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    return equipotent(cadre_plat(S, U), _t(U))


# ════════════════════════════════════════════════════════════════════════════
#  Le CADRE PLAT  F_plain = (S₀×U) ∪ ( (U×S₀) ∪ (U×U) ).
# ════════════════════════════════════════════════════════════════════════════
def cadre_plat(S="S0", U="Ucadre"):
    """F_plain := (S₀×U) ∪ ( (U×S₀) ∪ (U×U) )   (réunion PLATE, forme de s0sq)."""
    vS, vU = _t(S), _t(U)
    return E.reunion(E.produit(vS, vU),
                     E.reunion(E.produit(vU, vS), E.produit(vU, vU)))


__all__ = [
    "cadre_plat_blocs_disjoints", "cadre_plat_blocs_disjoints_cible",
    "cadre_plat_cardinal", "cadre_plat_cardinal_cible",
    "cadre_plat_bijection", "cadre_plat_bijection_cible",
    "cadre_plat", "commutativite_intersection_t",
]
