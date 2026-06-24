"""§II.1 — IDENTITÉS de la différence (∖ / ∩ / ∪) et LOIS DU COMPLÉMENT ∁X = E∖X.

Bourbaki E.II.1 (formulaire) : A∩(B∖C)=(A∩B)∖C, (A∖B)∖C=A∖(B∪C) ; et Résumé des
résultats E.R.4 §1 item 14 (∁X = E∖X) : E∖∅=E, E∖(E∖X)=X, X∪(E∖X)=E, X∩(E∖X)=∅,
X∩E=X, X∪E=E.

Tout par extensionnalité (`egalite_par_extension`) sur AXIOME_INTER/DIFF/REUNION/VIDE
(dans les 22) + lois propositionnelles fermées.  Les lois du complément qui invoquent
l'ambiant E (∁∁X=X, X∪∁X=E, X∩E=X, X∪E=E) portent l'hypothèse honnête X⊂E
(`inclus(X,E)`, sous-entendue par « X partie de E ») comme HYPOTHÈSE non déchargée,
conclusion == égalité NUE de Bourbaki.  theorie_ensembles() INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, appartient, et, ou, non, inclus, egal,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    et_congruence_droite, et_congruence_gauche, ou_congruence,
    equivalence_transitivite, equivalence_symetrie, equivalence_avant,
    equivalence_arriere, assoc_et, demorgan_ou,
    equiv_neg, instancie, cas, tiers_exclu, dni, dne, contraposition,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _refl_equiv(f):
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


def _instance_inter(a, b, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), a), b), z)


def _instance_diff(e, x, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF), e), x), z)


def intersection_difference_associe(a="A", b="B", c="C"):
    """⊢ A∩(B∖C) = (A∩B)∖C."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, nC = appartient(vz, va), appartient(vz, vb), non(appartient(vz, vc))
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(va, E.difference(vb, vc), vz),
        et_congruence_droite(zA, _instance_diff(vb, vc, vz))),
        assoc_et(zA, zB, nC)))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_diff(E.intersection(va, vb), vc, vz),
        et_congruence_gauche(_instance_inter(va, vb, vz), nC)))
    return egalite_par_extension(char_u, char_v, E.intersection(va, E.difference(vb, vc)),
                                 E.difference(E.intersection(va, vb), vc))


def difference_reunion(a="A", b="B", c="C"):
    """⊢ (A∖B)∖C = A∖(B∪C)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    nB, nC = non(zB), non(zC)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        _instance_diff(E.difference(va, vb), vc, vz),
        et_congruence_gauche(_instance_diff(va, vb, vz), nC)),
        equivalence_symetrie(assoc_et(zA, nB, nC))),
        et_congruence_droite(zA, equivalence_symetrie(demorgan_ou(zB, zC)))))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_diff(va, E.reunion(vb, vc), vz),
        et_congruence_droite(zA, equiv_neg(_instance_reunion(vb, vc, vz)))))
    return egalite_par_extension(char_u, char_v, E.difference(E.difference(va, vb), vc),
                                 E.difference(va, E.reunion(vb, vc)))


# ═══ LOIS DU COMPLÉMENT  ∁X = E∖X  (Résumé des résultats E.R.4, §1, item 14) ═══
#   item a  : E = ∁∅       →  E∖∅ = E                  [difference_vide ; clos]
#   item (1): ∁(∁X) = X    →  E∖(E∖X) = X   (X⊂E)      [complement_involution]
#   item (3): X∪(∁X) = E   →  X∪(E∖X) = E   (X⊂E)      [reunion_complement_plein]
#             X∩(∁X) = ∅   →  X∩(E∖X) = ∅              [inter_complement_vide ; clos]
#   item (4): X∩E = X                        (X⊂E)      [inter_ambiant_neutre]
#   item (5): X∪E = E                        (X⊂E)      [reunion_ambiant_absorbe]
# ∁X := E∖X = E.difference(E, X) (E ambiant EXPLICITE) ; lois gardées : hyp non
# déchargée inclus(X,E).  (∅ = ∁E EST déjà `ensembles_vide_identites.difference_self`.)


def _vide_inst(vz):
    """⊢ ¬(z ∈ ∅)   (instance de AXIOME_VIDE)."""
    return instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)


def _efq(notP_thm, q):
    """De ⊢¬P, déduire ⊢ (P ⇒ Q)   (ex falso quodlibet ; P⇒¬¬P⇒¬¬Q⇒Q)."""
    P = notP_thm.conclusion.sous[0]
    h = N.loi_deduction(non(q), notP_thm)                          # ¬Q ⇒ ¬P
    return syllogisme(syllogisme(dni(P), contraposition(h)), dne(q))   # P ⇒ Q


def _non_intro(p, imp_r, imp_nr):
    """De ⊢(P⇒R) et ⊢(P⇒¬R), déduire ⊢ ¬P  (réduction à l'absurde, via P⇒¬P)."""
    r = imp_r.conclusion.sous[1]                                   # conséquent R de (P⇒R)
    r_to_np = syllogisme(dni(r), contraposition(imp_nr))           # R ⇒ ¬¬R ⇒ ¬P
    p_to_np = syllogisme(imp_r, r_to_np)                           # P ⇒ ¬P  (= ¬P ∨ ¬P)
    return cas(p_to_np, a_implique_a(non(p)), a_implique_a(non(p)))   # ⊢ ¬P


def _inc_z(vX, vE, vz):
    """Sous l'hypothèse inclus(X,E) : ⊢ (z∈X ⇒ z∈E)   (instanciée en z)."""
    return instancie(N.assume(inclus(vX, vE)), vz)


def difference_vide(e="E"):
    """⊢ E∖∅ = E   (item a : E = ∁∅ ; INCONDITIONNEL).

    z∈E∖∅ ⇔ (z∈E et ¬z∈∅) ⇔ z∈E  (¬z∈∅ toujours vrai, AXIOME_VIDE)."""
    vE, vz = _t(e), var("z")
    zE = appartient(vz, vE)
    notzV = _vide_inst(vz)                                         # ⊢ ¬(z∈∅)
    simpl = conjonction_intro(
        N.loi_deduction(et(zE, non(appartient(vz, E.VIDE))),
                        conjonction_elim_gauche(
                            N.assume(et(zE, non(appartient(vz, E.VIDE)))))),   # ⇒ z∈E
        N.loi_deduction(zE, conjonction_intro(N.assume(zE), notzV)))          # z∈E ⇒ (z∈E et ¬z∈∅)
    char_u = N.generalisation("z", equivalence_transitivite(
        _instance_diff(vE, E.VIDE, vz), simpl))
    char_v = N.generalisation("z", _refl_equiv(zE))
    return egalite_par_extension(char_u, char_v, E.difference(vE, E.VIDE), vE)


def inter_complement_vide(x="X", e="E"):
    """⊢ X∩(E∖X) = ∅   (item (3) droite : X∩(∁X) = ∅ ; INCONDITIONNEL).

    z∈X∩(E∖X) ⇔ (z∈X et (z∈E et ¬z∈X)) ⇔ z∈∅ (z∈X et ¬z∈X contradictoires)."""
    vX, vE, vz = _t(x), _t(e), var("z")
    zX, zE, zV = appartient(vz, vX), appartient(vz, vE), appartient(vz, E.VIDE)
    nX = non(zX)
    inner = et(zX, et(zE, nX))
    h = N.assume(inner)
    zX_h = conjonction_elim_gauche(h)
    nX_h = conjonction_elim_droite(conjonction_elim_droite(h))
    fwd = N.loi_deduction(inner, N.modus_ponens(zX_h, _efq(nX_h, zV)))         # ⇒ z∈∅
    hv = N.assume(zV)
    bwd = N.loi_deduction(zV, conjonction_intro(                              # z∈∅ ⇒ inner (ex falso)
        N.modus_ponens(hv, _efq(_vide_inst(vz), zX)),
        conjonction_intro(N.modus_ponens(hv, _efq(_vide_inst(vz), zE)),
                          N.modus_ponens(hv, _efq(_vide_inst(vz), nX)))))
    contra = conjonction_intro(fwd, bwd)                                       # inner ⇔ z∈∅
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(vX, E.difference(vE, vX), vz),
        et_congruence_droite(zX, _instance_diff(vE, vX, vz))),
        contra))
    char_v = N.generalisation("z", _refl_equiv(zV))
    return egalite_par_extension(char_u, char_v,
                                 E.intersection(vX, E.difference(vE, vX)), E.VIDE)


def inter_ambiant_neutre(x="X", e="E"):
    """⊢ X∩E = X   sous (X⊂E)   (item (4) : X∩E = X).

    z∈X∩E ⇔ (z∈X et z∈E) ⇔ z∈X  (⇐ : z∈X ⇒ z∈E par X⊂E)."""
    vX, vE, vz = _t(x), _t(e), var("z")
    zX, zE = appartient(vz, vX), appartient(vz, vE)
    inc = _inc_z(vX, vE, vz)                                       # (hyp) z∈X ⇒ z∈E
    simpl = conjonction_intro(
        N.loi_deduction(et(zX, zE), conjonction_elim_gauche(N.assume(et(zX, zE)))),  # ⇒ z∈X
        N.loi_deduction(zX, conjonction_intro(N.assume(zX),                          # z∈X ⇒ (z∈X et z∈E)
                                              N.modus_ponens(N.assume(zX), inc))))
    char_u = N.generalisation("z", equivalence_transitivite(
        _instance_inter(vX, vE, vz), simpl))
    char_v = N.generalisation("z", _refl_equiv(zX))
    return egalite_par_extension(char_u, char_v, E.intersection(vX, vE), vX)


def reunion_ambiant_absorbe(x="X", e="E"):
    """⊢ X∪E = E   sous (X⊂E)   (item (5) : X∪E = E).

    z∈X∪E ⇔ (z∈X ou z∈E) ⇔ z∈E  (⇒ : z∈X ⇒ z∈E par X⊂E ; z∈E ⇒ z∈E)."""
    vX, vE, vz = _t(x), _t(e), var("z")
    zX, zE = appartient(vz, vX), appartient(vz, vE)
    inc = _inc_z(vX, vE, vz)                                       # (hyp) z∈X ⇒ z∈E
    e_to_disj = syllogisme(N.s2(zE, zX), N.s3(zE, zX))            # z∈E ⇒ (z∈E∨z∈X) ⇒ (z∈X∨z∈E)
    simpl = conjonction_intro(
        N.loi_deduction(ou(zX, zE), cas(N.assume(ou(zX, zE)), inc, a_implique_a(zE))),  # ⇒ z∈E
        e_to_disj)                                                                       # z∈E ⇒ (z∈X∨z∈E)
    char_u = N.generalisation("z", equivalence_transitivite(
        _instance_reunion(vX, vE, vz), simpl))
    char_v = N.generalisation("z", _refl_equiv(zE))
    return egalite_par_extension(char_u, char_v, E.reunion(vX, vE), vE)


def reunion_complement_plein(x="X", e="E"):
    """⊢ X∪(E∖X) = E   sous (X⊂E)   (item (3) gauche : X∪(∁X) = E).

    z∈X∪(E∖X) ⇔ (z∈X ou (z∈E et ¬z∈X)) ⇔ z∈E (⇒ : X⊂E ; ⇐ : tiers exclu sur z∈X)."""
    vX, vE, vz = _t(x), _t(e), var("z")
    zX, zE = appartient(vz, vX), appartient(vz, vE)
    nX = non(zX)
    inc = _inc_z(vX, vE, vz)                                       # (hyp) z∈X ⇒ z∈E
    inner = et(zE, nX)                                            # z∈E et ¬z∈X
    # ── fwd : (z∈X ou (z∈E et ¬z∈X)) ⇒ z∈E ──
    from_inner = N.loi_deduction(inner, conjonction_elim_gauche(N.assume(inner)))   # inner ⇒ z∈E
    fwd = N.loi_deduction(ou(zX, inner), cas(N.assume(ou(zX, inner)), inc, from_inner))
    # ── bwd : z∈E ⇒ (z∈X ou inner) ──
    hE = N.assume(zE)
    x_to_disj = N.s2(zX, inner)                                   # z∈X ⇒ (z∈X ∨ inner)
    nx_to_inner = N.loi_deduction(nX, conjonction_intro(hE, N.assume(nX)))          # ¬z∈X ⇒ inner (sous z∈E)
    nx_to_disj = syllogisme(nx_to_inner, _oui_d(zX, inner))      # ¬z∈X ⇒ (z∈X ∨ inner)
    bwd = N.loi_deduction(zE, cas(tiers_exclu(zX), x_to_disj, nx_to_disj))
    simpl = conjonction_intro(fwd, bwd)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_reunion(vX, E.difference(vE, vX), vz),
        ou_congruence(_refl_equiv(zX), _instance_diff(vE, vX, vz))),
        simpl))
    char_v = N.generalisation("z", _refl_equiv(zE))
    return egalite_par_extension(char_u, char_v,
                                 E.reunion(vX, E.difference(vE, vX)), vE)


def complement_involution(x="X", e="E"):
    """⊢ E∖(E∖X) = X   sous (X⊂E)   (item (1) : ∁(∁X) = X).

    z∈E∖(E∖X) ⇔ (z∈E et ¬(z∈E∖X)) ⇔ z∈X, via z∈E∖X ⇔ (z∈E et ¬z∈X) :
      ⇒ : tiers exclu sur z∈X (¬z∈X donnerait z∈E∖X, contre ¬(z∈E∖X)).
      ⇐ : z∈X ⇒ z∈E (X⊂E) ; ¬(z∈E∖X) car z∈E∖X donnerait ¬z∈X (contre z∈X)."""
    vX, vE, vz = _t(x), _t(e), var("z")
    zX, zE = appartient(vz, vX), appartient(vz, vE)
    nX = non(zX)
    inc = _inc_z(vX, vE, vz)                                       # (hyp) z∈X ⇒ z∈E
    memb = _instance_diff(vE, vX, vz)                             # z∈E∖X ⇔ (z∈E et ¬z∈X)
    inD = appartient(vz, E.difference(vE, vX))                    # z∈E∖X
    nD = non(inD)
    # ── fwd : (z∈E et ¬(z∈E∖X)) ⇒ z∈X ──
    h = N.assume(et(zE, nD))
    zE_h = conjonction_elim_gauche(h)
    nD_h = conjonction_elim_droite(h)
    nx_build_inD = syllogisme(
        N.loi_deduction(nX, conjonction_intro(zE_h, N.assume(nX))),   # ¬z∈X ⇒ (z∈E et ¬z∈X)   (sous z∈E)
        equivalence_arriere(memb))                                    # (z∈E et ¬z∈X) ⇒ z∈E∖X
    nx_to_x = syllogisme(nx_build_inD, _efq(nD_h, zX))               # ¬z∈X ⇒ z∈E∖X ⇒ z∈X
    fwd = N.loi_deduction(et(zE, nD),
                          cas(tiers_exclu(zX), a_implique_a(zX), nx_to_x))
    # ── bwd : z∈X ⇒ (z∈E et ¬(z∈E∖X)) ──
    hX = N.assume(zX)
    zE_from_X = N.modus_ponens(hX, inc)                              # z∈E   (sous z∈X)
    inD_to_nX = syllogisme(equivalence_avant(memb),                 # z∈E∖X ⇒ (z∈E et ¬z∈X)
                           _proj_droite(zE, nX))                    #        ⇒ ¬z∈X   (R := ¬z∈X)
    inD_to_nnX = syllogisme(N.loi_deduction(inD, hX), dni(zX))      # z∈E∖X ⇒ z∈X ⇒ ¬¬z∈X (= ¬R)
    nD_built = _non_intro(inD, inD_to_nX, inD_to_nnX)              # ¬(z∈E∖X)   (sous z∈X)
    bwd = N.loi_deduction(zX, conjonction_intro(zE_from_X, nD_built))
    simpl = conjonction_intro(fwd, bwd)
    char_u = N.generalisation("z", equivalence_transitivite(
        _instance_diff(vE, E.difference(vE, vX), vz), simpl))
    char_v = N.generalisation("z", _refl_equiv(zX))
    return egalite_par_extension(char_u, char_v,
                                 E.difference(vE, E.difference(vE, vX)), vX)


# ── micro-helpers propositionnels (réexpositions explicites) ─────────────────
def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)."""
    return syllogisme(N.s2(b, a), N.s3(b, a))                        # B⇒(B∨A)⇒(A∨B)


def _proj_droite(a, b):
    """⊢ (A et B) ⇒ B."""
    return N.loi_deduction(et(a, b), conjonction_elim_droite(N.assume(et(a, b))))


# ── cibles (énoncés Bourbaki NUS) + hypothèse, pour l'audit de fidélité ──────
def cibles(x="X", e="E"):
    """Dict {nom_loi → égalité NUE de Bourbaki} ; cibles['hyp'] = X⊂E (lois gardées)."""
    vX, vE = _t(x), _t(e)
    cX = E.difference(vE, vX)                                              # ∁X = E∖X
    return {
        "difference_vide":          egal(E.difference(vE, E.VIDE), vE),    # E∖∅ = E
        "inter_complement_vide":    egal(E.intersection(vX, cX), E.VIDE),  # X∩(E∖X) = ∅
        "inter_ambiant_neutre":     egal(E.intersection(vX, vE), vX),      # X∩E = X
        "reunion_ambiant_absorbe":  egal(E.reunion(vX, vE), vE),           # X∪E = E
        "reunion_complement_plein": egal(E.reunion(vX, cX), vE),           # X∪(E∖X) = E
        "complement_involution":    egal(E.difference(vE, cX), vX),        # E∖(E∖X) = X
        "hyp":                      inclus(vX, vE),                        # X⊂E
    }


# __all__ ne liste que les THÉORÈMES (`cibles` est un helper d'audit hors itération).
__all__ = [
    "intersection_difference_associe", "difference_reunion",
    "difference_vide", "complement_involution", "reunion_complement_plein",
    "inter_complement_vide", "inter_ambiant_neutre", "reunion_ambiant_absorbe",
]
