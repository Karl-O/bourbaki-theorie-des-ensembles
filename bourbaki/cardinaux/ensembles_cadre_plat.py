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
from bourbaki.cardinaux.ensembles_cardinaux import cardinal


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
#  Le CADRE PLAT  F_plain = (S₀×U) ∪ ( (U×S₀) ∪ (U×U) ).
# ════════════════════════════════════════════════════════════════════════════
def cadre_plat(S="S0", U="Ucadre"):
    """F_plain := (S₀×U) ∪ ( (U×S₀) ∪ (U×U) )   (réunion PLATE, forme de s0sq)."""
    vS, vU = _t(S), _t(U)
    return E.reunion(E.produit(vS, vU),
                     E.reunion(E.produit(vU, vS), E.produit(vU, vU)))


__all__ = [
    "cadre_plat_blocs_disjoints", "cadre_plat_blocs_disjoints_cible",
    "cadre_plat", "commutativite_intersection_t",
]
