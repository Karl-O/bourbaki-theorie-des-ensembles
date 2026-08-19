"""§II.1 — CARACTÉRISATIONS de l'inclusion par ∩ / ∪ (lien ordre ↔ treillis)
et ANTITONIE DU COMPLÉMENT (E.II.6, nº7).

Bourbaki E.II.1 : l'inclusion ⊂ se lit dans le treillis (∪, ∩) :

    A ⊂ B   ⇔   A∩B = A          A ⊂ B   ⇔   A∪B = B

CLOSES (0 hyp).  Sens ⇒ par extensionnalité (sous l'hypothèse A⊂B, z∈A ⇔ (z∈A et z∈B),
resp. z∈B ⇔ (z∈A ou z∈B)).  Sens ⇐ par Leibniz (S6) sur l'égalité d'ensembles.

Bourbaki E.II.6, nº7 (« si A, B parties de E, A⊂B et ∁_E B ⊂ ∁_E A sont équivalentes ») :

    A ⊂ B   ⇔   (E∖B) ⊂ (E∖A)         (∁_E X = E∖X = E.difference(E,X))

CLOSE-SOUS-HYPOTHÈSES-HONNÊTES {A⊂E, B⊂E} (« A, B parties de E ») : le sens ⇐ utilise
l'involution ∁∁=id (complement_involution), qui exige X⊂E.  Le sens ⇒ est inconditionnel.
theorie_ensembles() INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient, et, ou, non, impl, inclus, egal
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference_identites import (
    _instance_diff, complement_involution,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    et_congruence_droite, equiv_neg, contraposition, instancie, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _instance_inter(a, b, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), a), b), z)


def _oui_g(a, b):
    """⊢ A ⇒ (A∨B)."""
    return N.s2(a, b)


def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)."""
    return syllogisme(N.s2(b, a), N.s3(b, a))


# @livre Ch.R §1.14 Prop.(d) | E.R.4 L.28-30 | PDF p.307
def inclusion_ssi_intersection_egale(a="A", b="B"):
    """⊢ (A ⊂ B) ⇔ (A∩B = A)."""
    va, vb, vz = _t(a), _t(b), var("z")
    zA, zB = appartient(vz, va), appartient(vz, vb)
    AB = E.intersection(va, vb)
    # ── ⇒ : A⊂B ⇒ A∩B=A ──
    H = N.assume(inclus(va, vb))
    char_u = N.generalisation("z", _instance_inter(va, vb, vz))           # z∈A∩B ⇔ (z∈A et z∈B)
    cv_fwd = N.loi_deduction(zA, conjonction_intro(N.assume(zA),
                             N.modus_ponens(N.assume(zA), instancie(H, vz))))   # z∈A ⇒ (z∈A et z∈B)
    cv_bwd = N.loi_deduction(et(zA, zB), conjonction_elim_gauche(N.assume(et(zA, zB))))
    char_v = N.generalisation("z", conjonction_intro(cv_fwd, cv_bwd))    # z∈A ⇔ (z∈A et z∈B)  [sous H]
    imp1 = N.loi_deduction(inclus(va, vb), egalite_par_extension(char_u, char_v, AB, va))
    # ── ⇐ : A∩B=A ⇒ A⊂B ──
    Heq = N.assume(egal(AB, va))
    sym = N.modus_ponens(Heq, symetrie(AB, va))                          # A = A∩B
    leib = N.modus_ponens(sym, N.s6(va, AB, "w", appartient(vz, var("w"))))   # z∈A ⇔ z∈A∩B
    inter_to_zB = syllogisme(equivalence_avant(_instance_inter(va, vb, vz)),
                             N.loi_deduction(et(zA, zB), conjonction_elim_droite(N.assume(et(zA, zB)))))
    zA_to_zB = syllogisme(equivalence_avant(leib), inter_to_zB)          # z∈A ⇒ z∈B  [sous Heq]
    imp2 = N.loi_deduction(egal(AB, va), N.generalisation("z", zA_to_zB))
    return conjonction_intro(imp1, imp2)


# @livre Ch.R §1.14 Prop.(d) | E.R.4 L.28-30 | PDF p.307
def inclusion_ssi_reunion_egale(a="A", b="B"):
    """⊢ (A ⊂ B) ⇔ (A∪B = B)."""
    va, vb, vz = _t(a), _t(b), var("z")
    zA, zB = appartient(vz, va), appartient(vz, vb)
    AB = E.reunion(va, vb)
    # ── ⇒ : A⊂B ⇒ A∪B=B ──
    H = N.assume(inclus(va, vb))
    char_u = N.generalisation("z", _instance_reunion(va, vb, vz))        # z∈A∪B ⇔ (z∈A ou z∈B)
    cv_fwd = _oui_d(zA, zB)                                              # z∈B ⇒ (z∈A ou z∈B)
    cv_bwd = N.loi_deduction(ou(zA, zB), cas(N.assume(ou(zA, zB)), instancie(H, vz), a_implique_a(zB)))
    char_v = N.generalisation("z", conjonction_intro(cv_fwd, cv_bwd))    # z∈B ⇔ (z∈A ou z∈B)  [sous H]
    imp1 = N.loi_deduction(inclus(va, vb), egalite_par_extension(char_u, char_v, AB, vb))
    # ── ⇐ : A∪B=B ⇒ A⊂B ──
    Heq = N.assume(egal(AB, vb))
    leib = N.modus_ponens(Heq, N.s6(AB, vb, "w", appartient(vz, var("w"))))   # z∈A∪B ⇔ z∈B
    zA_to_union = syllogisme(_oui_g(zA, zB), equivalence_arriere(_instance_reunion(va, vb, vz)))  # z∈A ⇒ z∈A∪B
    zA_to_zB = syllogisme(zA_to_union, equivalence_avant(leib))          # z∈A ⇒ z∈A∪B ⇒ z∈B  [sous Heq]
    imp2 = N.loi_deduction(egal(AB, vb), N.generalisation("z", zA_to_zB))
    return conjonction_intro(imp1, imp2)


# ═══ ANTITONIE DU COMPLÉMENT  (Bourbaki E.II.6, nº7) ═════════════════════════
#   A ⊂ B  ⇔  (E∖B) ⊂ (E∖A)        sous (A⊂E, B⊂E)   [∁_E X = E∖X]
# Sens ⇒ INCONDITIONNEL : par contraposition membre à membre (z∈E∖X = z∈E et ¬z∈X).
# Sens ⇐ : applique ⇒ à ∁B⊂∁A (donne ∁∁A⊂∁∁B), puis réécrit ∁∁A=A, ∁∁B=B
#          (complement_involution, hyp X⊂E) par congruence S6.

def _antitone_impl(a, b):
    """⊢ (A ⊂ B) ⇒ ((E∖B) ⊂ (E∖A))   (CLOS ; sens ⇒, inconditionnel).

    Pour z : z∈E∖B ⇒ (z∈E et ¬z∈B) ⇒ (z∈E et ¬z∈A) ⇒ z∈E∖A,
    le pas central par contraposition de (z∈A ⇒ z∈B) instanciée de A⊂B."""
    va, vb, vE, vz = _t(a), _t(b), _t("E"), var("z")
    zE, nA, nB = appartient(vz, vE), non(appartient(vz, va)), non(appartient(vz, vb))
    H = N.assume(inclus(va, vb))
    contra = contraposition(instancie(H, vz))                       # ¬z∈B ⇒ ¬z∈A
    inner = N.loi_deduction(et(zE, nB), conjonction_intro(          # (z∈E et ¬z∈B) ⇒ (z∈E et ¬z∈A)
        conjonction_elim_gauche(N.assume(et(zE, nB))),
        N.modus_ponens(conjonction_elim_droite(N.assume(et(zE, nB))), contra)))
    chaine = syllogisme(syllogisme(
        equivalence_avant(_instance_diff(vE, vb, vz)),              # z∈E∖B ⇒ (z∈E et ¬z∈B)
        inner),
        equivalence_arriere(_instance_diff(vE, va, vz)))           # (z∈E et ¬z∈A) ⇒ z∈E∖A
    gen = N.generalisation("z", chaine)                            # (∀z)(z∈E∖B ⇒ z∈E∖A) = ∁B⊂∁A
    return N.loi_deduction(inclus(va, vb), gen)


# @livre Ch.II §1.7 Prop.- | E II.6 L.21-23 | PDF p.57
def antitonie_complement(a="A", b="B", e="E"):
    """⊢ (A ⊂ B) ⇔ ((E∖B) ⊂ (E∖A))   sous (A⊂E, B⊂E)   (E.II.6, nº7).

    ∁_E X = E∖X.  Hypothèses honnêtes {A⊂E, B⊂E} (« A, B parties de E ») non
    déchargées : indispensables au sens ⇐ via l'involution ∁∁=id."""
    va, vb, vE = _t(a), _t(b), _t(e)
    cA, cB = E.difference(vE, va), E.difference(vE, vb)            # ∁A, ∁B
    ccA, ccB = E.difference(vE, cA), E.difference(vE, cB)         # ∁∁A, ∁∁B
    # ── ⇒ : A⊂B ⇒ ∁B⊂∁A  (clos) ──
    imp1 = _antitone_impl(va, vb)
    # ── ⇐ : ∁B⊂∁A ⇒ A⊂B  (sous A⊂E, B⊂E) ──
    H = N.assume(inclus(cB, cA))
    incl_cc = N.modus_ponens(H, _antitone_impl(cB, cA))           # {∁B⊂∁A} ⊢ ∁∁A ⊂ ∁∁B
    invA = complement_involution(va, vE)                          # {A⊂E} ⊢ ∁∁A = A
    invB = complement_involution(vb, vE)                          # {B⊂E} ⊢ ∁∁B = B
    # réécrit ∁∁A → A : (∁∁A=A) ⇒ (∁∁A⊂∁∁B ⇔ A⊂∁∁B)
    eqA = N.modus_ponens(invA, N.s6(ccA, va, "w", inclus(var("w"), ccB)))
    step1 = N.modus_ponens(incl_cc, equivalence_avant(eqA))       # ⊢ A ⊂ ∁∁B
    # réécrit ∁∁B → B : (∁∁B=B) ⇒ (A⊂∁∁B ⇔ A⊂B)
    eqB = N.modus_ponens(invB, N.s6(ccB, vb, "w", inclus(va, var("w"))))
    step2 = N.modus_ponens(step1, equivalence_avant(eqB))         # ⊢ A ⊂ B
    imp2 = N.loi_deduction(inclus(cB, cA), step2)                 # {A⊂E,B⊂E} ⊢ ∁B⊂∁A ⇒ A⊂B
    return conjonction_intro(imp1, imp2)


__all__ = ["inclusion_ssi_intersection_egale", "inclusion_ssi_reunion_egale",
           "antitonie_complement"]
