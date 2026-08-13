"""§III.6.3 (support) — DISJONCTIONS DE PRODUITS pour le cadre-RÉUNION de Hessenberg.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Le re-câblage RÉUNION du cadre d'extension (E.III.48, cf. TABLE DE DÉCHARGE
au journal de campagne) remplace la somme disjointe taguée par la réunion
F_r := (S₀×U) ∪ ((U×S₀) ∪ (U×U)).  Les identités de disjonction que le tag
rendait opaques deviennent alors de VRAIS lemmes ensemblistes, prouvés ici par
appartenance (AXIOME_PRODUIT/REUNION/INTER/VIDE + injectivité du couple) :

  • produits_disjoints_premiere : {(∀z)(z∈A ⇒ ¬z∈B)} ⊢ (∀u)¬(u∈A×C et u∈B×D).
  • produits_disjoints_seconde  : {(∀z)(z∈C ⇒ ¬z∈D)} ⊢ (∀u)¬(u∈A×C et u∈B×D).
  • disjoint_reunion_droite     : {¬∧(X,Y), ¬∧(X,Z)} ⊢ (∀u)¬(u∈X et u∈Y∪Z).
  • inter_vide_depuis_disjonction : {(∀z)(z∈A ⇒ ¬z∈B)} ⊢ A∩B = ∅.
  • carre_disjoint_cadre_reunion : {(∀z)(z∈U ⇒ ¬z∈S)} ⊢ (∀u)¬(u∈S² et u∈F_r).

ROUTE ¬-INTRO (uniforme) : sous l'hypothèse conjonctive P, décomposer les deux
appartenances-produit (témoins FRAIS par renommage S5-exotique du ∃ natif p/q
d'AXIOME_PRODUIT), égaler les couples (couple_egal_implique_composantes),
transporter la coordonnée commune dans les deux facteurs (S6) — contradiction
avec la disjonction ; EX FALSO (S2) vers le marqueur ¬(A=A) ; éliminations des
témoins ; loi de déduction ; CONTRAPOSITION + ¬¬(A=A) (réflexivité + dni) ⇒ ¬P ;
généralisation.  INVARIANT : theorie_ensembles()=22 ; rien postulé ; clos modulo
la seule hypothèse de disjonction ∀-close (honnête, satisfiable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, contraposition, dni, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _marqueur(vA):
    """Marqueur FALSUM témoin-libre : ¬(A=A)  (motif _marqueur_faux, stepb2)."""
    return non(egal(vA, vA))


def _disj_forme(A, B, z="zpd"):
    """La FORME d'hypothèse de disjonction : (∀z)( z∈A ⇒ ¬(z∈B) )."""
    vz = var(z)
    return pourtout(z, impl(appartient(vz, _t(A)), non(appartient(vz, _t(B)))))


def _renomme_ex2(corps_frais, ex_natif, p2="p2", q2="q2"):
    """De ⊢ (∃p)(∃q) corps(p,q) déduit ⊢ (∃p2)(∃q2) corps(p2,q2)  (témoins FRAIS).

    Motif S5-exotique (ev. 109) en DEUX étages : q→q2 sous ∃p (monotonie),
    puis p→p2.  corps_frais = corps(p2,q2) ; les substitutions inverses
    corps(p2,q2)[q2←q][p2←p] retombent BYTE-À-BYTE sur le corps natif."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import subst_f
    # étage 1 : (∃q corps(p,q)) ⇒ (∃q2 corps(p,q2))   [S5 puis élim de q]
    corps_pq2 = subst_f(var("p"), p2, corps_frais)     # corps(p, q2)
    imp1 = N.s5(corps_pq2, var("q"), q2)               # corps(p,q) ⇒ ∃q2 corps(p,q2)
    e1 = existe_elimination(imp1, "q")                 # (∃q corps(p,q)) ⇒ ∃q2 …
    lift = monotonie_existe(e1, "p")                   # (∃p∃q …) ⇒ (∃p ∃q2 corps(p,q2))
    ex_pq2 = N.modus_ponens(ex_natif, lift)
    # étage 2 : (∃p (∃q2 corps(p,q2))) ⇒ (∃p2)(∃q2) corps(p2,q2)
    imp2 = N.s5(existe(q2, corps_frais), var("p"), p2) # (∃q2 corps(p,q2)) ⇒ ∃p2∃q2 …
    e2 = existe_elimination(imp2, "p")
    return N.modus_ponens(ex_pq2, e2)


def _corps_produit(vu, vp, vq, vX, vY):
    """Le corps d'AXIOME_PRODUIT : (u=(p,q) et p∈X) et q∈Y."""
    return et(et(egal(vu, E.couple(vp, vq)), appartient(vp, vX)),
              appartient(vq, vY))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.31-37 | PDF p.151  (les quatre produits du carré Z² sont deux à deux disjoints — support du cadre en réunion)
def produits_disjoints_premiere(A="A", B="B", C="C", D="D", u="upd", z="zpd"):
    """{ (∀z)(z∈A ⇒ ¬(z∈B)) } ⊢ (∀u)¬( (u∈A×C) et (u∈B×D) ).      [1 hyp honnête].

    Deux produits dont les PREMIERS facteurs sont disjoints sont disjoints :
    un u commun se décompose u=(p,q)=(p',q'), l'injectivité du couple force
    p=p', qui serait dans A ET dans B.  Route ¬-intro (cf. en-tête)."""
    vA, vB, vC, vD = _t(A), _t(B), _t(C), _t(D)
    vu = var(u)
    AxC, BxD = E.produit(vA, vC), E.produit(vB, vD)
    P = et(appartient(vu, AxC), appartient(vu, BxD))
    marqueur = _marqueur(vA)

    Hd = N.assume(_disj_forme(vA, vB, z))
    Hu = N.assume(P)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    ex1 = N.modus_ponens(conjonction_elim_gauche(Hu), equivalence_avant(
        instancie(instancie(instancie(ax, vA), vC), vu)))     # ∃p∃q corps(A,C)
    ex2n = N.modus_ponens(conjonction_elim_droite(Hu), equivalence_avant(
        instancie(instancie(instancie(ax, vB), vD), vu)))     # ∃p∃q corps(B,D)
    vp, vq, vp2, vq2 = var("p"), var("q"), var("p2"), var("q2")
    corps2_frais = _corps_produit(vu, vp2, vq2, vB, vD)
    ex2 = _renomme_ex2(corps2_frais, ex2n)          # ∃p2∃q2 corps(B,D)

    # ── sous les DEUX corps-témoins, dériver le marqueur ──
    Hb1 = N.assume(_corps_produit(vu, vp, vq, vA, vC))
    Hb2 = N.assume(corps2_frais)
    eq1 = conjonction_elim_gauche(conjonction_elim_gauche(Hb1))    # u=(p,q)
    p_in_A = conjonction_elim_droite(conjonction_elim_gauche(Hb1))
    eq2 = conjonction_elim_gauche(conjonction_elim_gauche(Hb2))    # u=(p2,q2)
    p2_in_B = conjonction_elim_droite(conjonction_elim_gauche(Hb2))
    cc = composer_egalites(
        N.modus_ponens(eq1, symetrie(vu, E.couple(vp, vq))), eq2)  # (p,q)=(p2,q2)
    comp = N.modus_ponens(cc, couple_egal_implique_composantes(vp, vq, vp2, vq2))
    p_eq_p2 = conjonction_elim_gauche(comp)                        # p=p2
    not_p_in_B = N.modus_ponens(p_in_A, instancie(Hd, vp))         # ¬(p∈B)
    s6b = N.s6(vp, vp2, "h6d", appartient(var("h6d"), vB))
    p_in_B = N.modus_ponens(p2_in_B, equivalence_arriere(
        N.modus_ponens(p_eq_p2, s6b)))                             # p∈B
    faux = N.modus_ponens(p_in_B, N.modus_ponens(not_p_in_B,
        N.s2(non(appartient(vp, vB)), marqueur)))                  # marqueur

    # ── éliminer p2,q2 puis p,q ; décharger P ; contraposer ──
    imp2 = N.loi_deduction(corps2_frais, faux)
    imp2 = existe_elimination(imp2, "q2")
    imp2 = existe_elimination(imp2, "p2")
    faux = N.modus_ponens(ex2, imp2)
    imp1 = N.loi_deduction(_corps_produit(vu, vp, vq, vA, vC), faux)
    imp1 = existe_elimination(imp1, "q")
    imp1 = existe_elimination(imp1, "p")
    faux = N.modus_ponens(ex1, imp1)                               # marqueur [Hd, P]
    notP = N.modus_ponens(
        N.modus_ponens(N.reflexivite(vA), dni(egal(vA, vA))),
        contraposition(N.loi_deduction(P, faux)))                  # ¬P  [Hd]
    res = N.generalisation(u, notP)

    cible = pourtout(u, non(P))
    assert res.conclusion == cible, "produits_disjoints_premiere : conclusion ≠"
    assert res.hypotheses == frozenset({_disj_forme(vA, vB, z)}), \
        "produits_disjoints_premiere : hyps ≠ {disjonction}"
    return res


def produits_disjoints_seconde(A="A", B="B", C="C", D="D", u="upd", z="zpd"):
    """{ (∀z)(z∈C ⇒ ¬(z∈D)) } ⊢ (∀u)¬( (u∈A×C) et (u∈B×D) ).      [1 hyp honnête].

    Variante SECONDE COORDONNÉE : q=q2 serait dans C ET dans D."""
    vA, vB, vC, vD = _t(A), _t(B), _t(C), _t(D)
    vu = var(u)
    AxC, BxD = E.produit(vA, vC), E.produit(vB, vD)
    P = et(appartient(vu, AxC), appartient(vu, BxD))
    marqueur = _marqueur(vC)

    Hd = N.assume(_disj_forme(vC, vD, z))
    Hu = N.assume(P)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    ex1 = N.modus_ponens(conjonction_elim_gauche(Hu), equivalence_avant(
        instancie(instancie(instancie(ax, vA), vC), vu)))
    ex2n = N.modus_ponens(conjonction_elim_droite(Hu), equivalence_avant(
        instancie(instancie(instancie(ax, vB), vD), vu)))
    vp, vq, vp2, vq2 = var("p"), var("q"), var("p2"), var("q2")
    corps2_frais = _corps_produit(vu, vp2, vq2, vB, vD)
    ex2 = _renomme_ex2(corps2_frais, ex2n)

    Hb1 = N.assume(_corps_produit(vu, vp, vq, vA, vC))
    Hb2 = N.assume(corps2_frais)
    eq1 = conjonction_elim_gauche(conjonction_elim_gauche(Hb1))
    q_in_C = conjonction_elim_droite(Hb1)                          # q∈C
    eq2 = conjonction_elim_gauche(conjonction_elim_gauche(Hb2))
    q2_in_D = conjonction_elim_droite(Hb2)                         # q2∈D
    cc = composer_egalites(
        N.modus_ponens(eq1, symetrie(vu, E.couple(vp, vq))), eq2)
    comp = N.modus_ponens(cc, couple_egal_implique_composantes(vp, vq, vp2, vq2))
    q_eq_q2 = conjonction_elim_droite(comp)                        # q=q2
    not_q_in_D = N.modus_ponens(q_in_C, instancie(Hd, vq))         # ¬(q∈D)
    s6b = N.s6(vq, vq2, "h6d", appartient(var("h6d"), vD))
    q_in_D = N.modus_ponens(q2_in_D, equivalence_arriere(
        N.modus_ponens(q_eq_q2, s6b)))
    faux = N.modus_ponens(q_in_D, N.modus_ponens(not_q_in_D,
        N.s2(non(appartient(vq, vD)), marqueur)))

    imp2 = N.loi_deduction(corps2_frais, faux)
    imp2 = existe_elimination(imp2, "q2")
    imp2 = existe_elimination(imp2, "p2")
    faux = N.modus_ponens(ex2, imp2)
    imp1 = N.loi_deduction(_corps_produit(vu, vp, vq, vA, vC), faux)
    imp1 = existe_elimination(imp1, "q")
    imp1 = existe_elimination(imp1, "p")
    faux = N.modus_ponens(ex1, imp1)
    notP = N.modus_ponens(
        N.modus_ponens(N.reflexivite(vC), dni(egal(vC, vC))),
        contraposition(N.loi_deduction(P, faux)))
    res = N.generalisation(u, notP)

    cible = pourtout(u, non(P))
    assert res.conclusion == cible, "produits_disjoints_seconde : conclusion ≠"
    assert res.hypotheses == frozenset({_disj_forme(vC, vD, z)}), \
        "produits_disjoints_seconde : hyps ≠ {disjonction}"
    return res


def disjoint_reunion_droite(X="X", Y="Y", Z="Z", u="upd"):
    """{ (∀u)¬(u∈X et u∈Y), (∀u)¬(u∈X et u∈Z) } ⊢ (∀u)¬( u∈X et u∈(Y∪Z) ).

    Distribution de la disjonction sur la réunion à droite (cas par cas)."""
    vX, vY, vZ = _t(X), _t(Y), _t(Z)
    vu = var(u)
    P = et(appartient(vu, vX), appartient(vu, E.reunion(vY, vZ)))
    marqueur = _marqueur(vX)

    hyp_Y = pourtout(u, non(et(appartient(vu, vX), appartient(vu, vY))))
    hyp_Z = pourtout(u, non(et(appartient(vu, vX), appartient(vu, vZ))))
    HY, HZ = N.assume(hyp_Y), N.assume(hyp_Z)
    Hu = N.assume(P)
    in_X = conjonction_elim_gauche(Hu)
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION), vY), vZ), vu)
    disj = N.modus_ponens(conjonction_elim_droite(Hu), equivalence_avant(car))

    def _branche(vW, HW):
        hW = N.assume(appartient(vu, vW))
        paire = conjonction_intro(in_X, hW)
        notp = instancie(HW, vu)                    # ¬(u∈X ∧ u∈W)
        fx = N.modus_ponens(paire, N.modus_ponens(notp,
            N.s2(non(paire.conclusion), marqueur)))
        return N.loi_deduction(appartient(vu, vW), fx)

    faux = cas(disj, _branche(vY, HY), _branche(vZ, HZ))
    notP = N.modus_ponens(
        N.modus_ponens(N.reflexivite(vX), dni(egal(vX, vX))),
        contraposition(N.loi_deduction(P, faux)))
    res = N.generalisation(u, notP)

    cible = pourtout(u, non(P))
    assert res.conclusion == cible, "disjoint_reunion_droite : conclusion ≠"
    assert res.hypotheses == frozenset({hyp_Y, hyp_Z}), \
        "disjoint_reunion_droite : hyps ≠ {2 disjonctions}"
    return res


def inter_vide_depuis_disjonction(A="A", B="B", z="zpd"):
    """{ (∀z)(z∈A ⇒ ¬(z∈B)) } ⊢ A∩B = ∅.                          [1 hyp honnête].

    Extensionnalité : (∀z)(z∈A∩B ⇔ (z∈A et z∈B)) [AXIOME_INTER] et
    (∀z)(z∈∅ ⇔ (z∈A et z∈B)) [→ ex falso d'AXIOME_VIDE ; ← ex falso de la
    disjonction], puis egalite_par_extension."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
        egalite_par_extension,
    )
    vA, vB = _t(A), _t(B)
    vz = var("z")            # liant CANONIQUE de l'extensionnalité (≠ liant de l'hyp)
    inter, vide = E.intersection(vA, vB), E.VIDE
    R = et(appartient(vz, vA), appartient(vz, vB))
    Hd = N.assume(_disj_forme(vA, vB, z))

    car_inter = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), vA), vB), vz)
    thm_u = N.generalisation("z", car_inter)        # (∀z)(z∈A∩B ⇔ R)

    # (∀z)( z∈∅ ⇔ R ) : → par ex falso (¬z∈∅) ; ← par ex falso (disjonction).
    not_in_vide = instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)        # ¬(z∈∅)
    fwd = N.modus_ponens(not_in_vide, N.s2(non(appartient(vz, vide)), R))
    hR = N.assume(R)
    notB = N.modus_ponens(conjonction_elim_gauche(hR), instancie(Hd, vz))
    in_vide = N.modus_ponens(conjonction_elim_droite(hR), N.modus_ponens(
        notB, N.s2(non(appartient(vz, vB)), appartient(vz, vide))))
    bwd = N.loi_deduction(R, in_vide)                              # R ⇒ z∈∅
    thm_v = N.generalisation("z", conjonction_intro(fwd, bwd))     # (∀z)(z∈∅ ⇔ R)

    res = egalite_par_extension(thm_u, thm_v, inter, vide, x="z")
    assert res.conclusion == egal(inter, vide), "inter_vide : conclusion ≠ A∩B=∅"
    assert res.hypotheses == frozenset({_disj_forme(vA, vB, z)}), \
        "inter_vide : hyps ≠ {disjonction}"
    return res


def _flip_disjonction(U="Ucadre", S="S0", z="zpd"):
    """De {(∀z)(z∈U ⇒ ¬z∈S)} ⊢ (∀z)(z∈S ⇒ ¬z∈U)   (contraposition + dni)."""
    vU, vS, vz = _t(U), _t(S), var(z)
    Hd = N.assume(_disj_forme(vU, vS, z))
    inst = instancie(Hd, vz)                        # z∈U ⇒ ¬z∈S
    flip = syllogisme(dni(appartient(vz, vS)), contraposition(inst))
    assert flip.conclusion == impl(appartient(vz, vS), non(appartient(vz, vU)))
    return N.generalisation(z, flip)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.31-37 | PDF p.151  (S₀² est disjoint du cadre F — les quatre morceaux du carré sont deux à deux disjoints)
def carre_disjoint_cadre_reunion(S="S0", U="Ucadre", u="upd", z="zpd"):
    """{ (∀z)(z∈U ⇒ ¬(z∈S)) } ⊢ (∀u)¬( u∈S×S  et  u∈F_r ),
       F_r = (S×U) ∪ ((U×S) ∪ (U×U)).                            [1 hyp honnête].

    L5 — le carré S₀² est disjoint du cadre-réunion : 2de coordonnée contre S×U,
    1re coordonnée contre U×S et U×U, recollées par disjoint_reunion_droite."""
    vS, vU = _t(S), _t(U)
    SxS, SxU = E.produit(vS, vS), E.produit(vS, vU)
    UxS, UxU = E.produit(vU, vS), E.produit(vU, vU)
    disj_US = _disj_forme(vU, vS, z)                # (∀z)(z∈U ⇒ ¬z∈S)  [l'hyp]
    flip = _flip_disjonction(vU, vS, z)             # {..} ⊢ (∀z)(z∈S ⇒ ¬z∈U)

    def _cut(thm):
        """Décharge, dans thm, l'hyp flip par sa preuve (portée par disj_US)."""
        c = flip.conclusion
        if c in thm.hypotheses:
            return N.modus_ponens(flip, N.loi_deduction(c, thm))
        return thm

    # S² vs S×U : 2de coord (S vs U) — hyp = (∀z)(z∈S ⇒ ¬z∈U) = flip.
    d1 = _cut(produits_disjoints_seconde(vS, vS, vS, vU, u, z))
    # S² vs U×S : 1re coord (S vs U) — hyp = flip.
    d2 = _cut(produits_disjoints_premiere(vS, vU, vS, vS, u, z))
    # S² vs U×U : 1re coord (S vs U) — hyp = flip.
    d3 = _cut(produits_disjoints_premiere(vS, vU, vS, vU, u, z))

    # recoller : X=S², ¬∧(X,U×S) + ¬∧(X,U×U) → ¬∧(X, (U×S)∪(U×U)) ; puis avec S×U.
    inner = disjoint_reunion_droite(SxS, UxS, UxU, u)
    for th in (d2, d3):
        c = th.conclusion
        if c in inner.hypotheses:
            inner = N.modus_ponens(th, N.loi_deduction(c, inner))
    outer = disjoint_reunion_droite(SxS, SxU, E.reunion(UxS, UxU), u)
    for th in (d1, inner):
        c = th.conclusion
        if c in outer.hypotheses:
            outer = N.modus_ponens(th, N.loi_deduction(c, outer))

    F_r = E.reunion(SxU, E.reunion(UxS, UxU))
    vu = var(u)
    cible = pourtout(u, non(et(appartient(vu, SxS), appartient(vu, F_r))))
    assert outer.conclusion == cible, "carre_disjoint_cadre_reunion : conclusion ≠"
    assert outer.hypotheses == frozenset({disj_US}), \
        "carre_disjoint_cadre_reunion : hyps ≠ {(∀z)(z∈U ⇒ ¬z∈S)}"
    return outer


__all__ = [
    "produits_disjoints_premiere", "produits_disjoints_seconde",
    "disjoint_reunion_droite", "inter_vide_depuis_disjonction",
    "carre_disjoint_cadre_reunion",
]
