"""§II — caractérisation de l'ensemble vide : A=∅ ⇔ (∀z)¬(z∈A).

Brique réutilisée partout (≠∅ ⇔ a un élément). Forward = Leibniz sur AXIOME_VIDE ;
backward = double inclusion (ex falso + axiome du vide) puis extensionnalité A1.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, non, impl, appartient, pourtout, existe, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, contraposition, dni, dne,
                               instanciation_en_x, instancie)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
from bourbaki.logique.i_4_egalitaires.relations_fonctionnelles_c45 import relation_univoque_x
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


# @livre Ch.II §1.7 Rem.- | E II.6 L.30-30 | PDF p.57
def vide_ssi_sans_element(a="A"):
    """⊢ (A = ∅) ⇔ (∀z)¬(z ∈ A).   (a : variable-nom ou terme quelconque sans z libre.)

    Liant fixé à « z » (cohérent avec inclus/A1 utilisés par l'extensionnalité)."""
    vA, vz = (a if isinstance(a, Terme) else var(a)), var("z")
    sans = pourtout("z", non(appartient(vz, vA)))             # (∀z)¬(z∈A)
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)  # (∀z)¬(z∈∅)

    # ── sens direct : A=∅ ⇒ (∀z)¬(z∈A) ─────────────────────────────────────────
    h = N.assume(egal(vA, E.VIDE))
    vide_egal_a = N.modus_ponens(h, symetrie(vA, E.VIDE))     # ∅=A
    leib = N.s6(E.VIDE, vA, "W", pourtout("z", non(appartient(vz, var("W")))))
    equ = N.modus_ponens(vide_egal_a, leib)                  # (∀z)¬(z∈∅) ⇔ (∀z)¬(z∈A)
    fwd = N.loi_deduction(egal(vA, E.VIDE),
                          N.modus_ponens(ax_vide, equivalence_avant(equ)))

    # ── réciproque : (∀z)¬(z∈A) ⇒ A=∅ ─────────────────────────────────────────
    hs = N.assume(sans)
    nzA = N.modus_ponens(hs, instanciation_en_x(non(appartient(vz, vA)), "z"))   # ¬(z∈A)
    a_sub_vide = N.generalisation("z", N.modus_ponens(
        nzA, N.s2(non(appartient(vz, vA)), appartient(vz, E.VIDE))))             # A⊂∅
    nz0 = N.modus_ponens(ax_vide, instanciation_en_x(non(appartient(vz, E.VIDE)), "z"))
    vide_sub_a = N.generalisation("z", N.modus_ponens(
        nz0, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, vA))))             # ∅⊂A
    ext = extensionnalite_appliquee(vA, E.VIDE)              # (A⊂∅ et ∅⊂A) ⇒ A=∅
    bwd = N.loi_deduction(sans, N.modus_ponens(
        conjonction_intro(a_sub_vide, vide_sub_a), ext))

    return conjonction_intro(fwd, bwd)


def _equiv_neg(thm_pq):
    """⊢ (P⇔Q) ⟹ ⊢ (¬P ⇔ ¬Q)  (congruence de la négation)."""
    return conjonction_intro(contraposition(equivalence_arriere(thm_pq)),
                             contraposition(equivalence_avant(thm_pq)))


# @livre Ch.II §1.7 Rem.- | E II.6 L.30-30 | PDF p.57
def non_vide_ssi_element(a="A"):
    """⊢ ¬(A = ∅) ⇔ (∃z)(z ∈ A).   (a : variable-nom ou terme sans z libre.)"""
    vA, vz = (a if isinstance(a, Terme) else var(a)), var("z")
    R = appartient(vz, vA)
    neg_vide = _equiv_neg(vide_ssi_sans_element(vA))   # ¬(A=∅) ⇔ ¬(∀z)¬R   [= ¬¬(∃z)¬¬R]
    P = existe("z", non(non(R)))                       # (∃z)¬¬R
    step1 = conjonction_intro(dne(P), dni(P))          # ¬¬P ⇔ P   (¬(∀z)¬R ⇔ (∃z)¬¬R)
    step2 = congruence_existe(conjonction_intro(dne(R), dni(R)), "z")   # (∃z)¬¬R ⇔ (∃z)R
    bridge = equivalence_transitivite(step1, step2)    # ¬(∀z)¬R ⇔ (∃z)R
    return equivalence_transitivite(neg_vide, bridge)  # ¬(A=∅) ⇔ (∃z)(z∈A)


# @livre Ch.II §1.7 Th.- | E II.6 L.36-37 | PDF p.57
def vide_inclus_partout(x="X"):
    """⊢ ∅ ⊂ X.   (E II.6 §7 : « On a les théorèmes x∉∅, ∅⊂X, … ».)

    EX FALSO : ¬(z∈∅) [AXIOME_VIDE] donne (z∈∅ ⇒ z∈X) par S2, généralisé sur z.
    Aucune hypothèse (clos) ; theorie==22.  x : nom de variable ou terme sans z libre."""
    vX = x if isinstance(x, Terme) else var(x)
    vz = var("z")
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)        # (∀z)¬(z∈∅)
    nz0 = N.modus_ponens(ax_vide, instanciation_en_x(non(appartient(vz, E.VIDE)), "z"))  # ¬(z∈∅)
    body = N.modus_ponens(nz0, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, vX)))    # z∈∅ ⇒ z∈X
    return N.generalisation("z", body)                             # (∀z)(z∈∅⇒z∈X) = ∅⊂X


# @livre Ch.II §1.7 Th.- | E II.6 L.37-38 | PDF p.57
def sous_ensemble_vide_ssi_egal(x="X"):
    """⊢ (X ⊂ ∅) ⇔ (X = ∅).   (E II.6 §7 : « la relation X⊂∅ est équivalente à X=∅ ».)

    ⇒ : de X⊂∅ et ∅⊂X (`vide_inclus_partout`), l'extensionnalité A1 donne X=∅.
    ⇐ : de X=∅, Leibniz (S6) donne (z∈X ⇔ z∈∅), d'où z∈X⇒z∈∅ ; généralisé = X⊂∅.
    Clos (est_clos=True) ; theorie==22."""
    vX, vz = (x if isinstance(x, Terme) else var(x)), var("z")
    # ── ⇒ : X⊂∅ ⇒ X=∅ (extensionnalité) ────────────────────────────────────────
    h = N.assume(inclus(vX, E.VIDE))
    fwd_concl = N.modus_ponens(conjonction_intro(h, vide_inclus_partout(vX)),
                               extensionnalite_appliquee(vX, E.VIDE))   # X=∅
    fwd = N.loi_deduction(inclus(vX, E.VIDE), fwd_concl)                 # (X⊂∅) ⇒ (X=∅)
    # ── ⇐ : X=∅ ⇒ X⊂∅ (Leibniz sur l'appartenance) ─────────────────────────────
    he = N.assume(egal(vX, E.VIDE))
    eqv_app = N.modus_ponens(he, N.s6(vX, E.VIDE, "W", appartient(vz, var("W"))))  # z∈X ⇔ z∈∅
    X_sub_vide = N.generalisation("z", equivalence_avant(eqv_app))       # X⊂∅
    bwd = N.loi_deduction(egal(vX, E.VIDE), X_sub_vide)                  # (X=∅) ⇒ (X⊂∅)
    return conjonction_intro(fwd, bwd)                                  # (X⊂∅) ⇔ (X=∅)


# @livre Ch.II §1.7 Th.- | E II.6 L.38-39 | PDF p.57
def vacuite_sur_vide(R, x="x"):
    """⊢ (∀x)((x∈∅) ⇒ R{x}).   (E II.6 §7 : « Si R{x} est une relation, la relation
    (∀x)((x∈∅)⇒R{x}) est vraie ».)

    EX FALSO paramétré : ¬(x∈∅) [AXIOME_VIDE instancié] ⇒ (x∈∅ ⇒ R{x}) par S2,
    généralisé sur x.  R = relation (callable Terme↦Formule).  Clos ; theorie==22."""
    vx = var(x)
    nx0 = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vx)   # ¬(x∈∅)
    body = N.modus_ponens(nx0, N.s2(non(appartient(vx, E.VIDE)), R(vx)))  # x∈∅ ⇒ R{x}
    return N.generalisation(x, body)                                     # (∀x)(x∈∅⇒R{x})


def _R_vide():
    """La relation Bourbaki « (∀x)(x∉X) » (X fonctionnelle), liant interne « x »."""
    return pourtout("x", non(appartient(var("x"), var("X"))))


# @livre Ch.II §1.7 Th.1 | E II.6 L.24-27 | PDF p.57
def vide_relation_fonctionnelle():
    """⊢ relation_univoque_X( (∀x)(x∉X) ).   THÉORÈME 1 (Bourbaki E II.6, nº7).

    « La relation (∀x)(x∉X) est FONCTIONNELLE en X » — c'est ce théorème qui
    LÉGITIME la définition ∅ := τX((∀x)(x∉X)).  « Fonctionnelle » = UNIVOQUE
    (au plus un) ∧ EXISTE (au moins un).  On certifie ici le contenu non-trivial,
    l'UNIVOCITÉ, par la preuve EXACTE de Bourbaki (« en vertu de l'axiome
    d'extensionnalité, … donc univoque ») ; l'EXISTENCE est l'axiome du vide
    (AXIOME_VIDE, dont ∅ est le témoin — Bourbaki : « (∀x)(x∉∁_Y Y) est vraie »).

    Preuve de l'univocité : deux ensembles vides Y, Z se contiennent mutuellement
    (EX FALSO : de z∉Y on tire z∈Y ⇒ z∈Z par S2, généralisé = Y⊂Z ; idem Z⊂Y),
    donc Y = Z par l'extensionnalité A1.  CLOS (0 hypothèse) ; theorie==22."""
    vY, vZ, vz = var("Y"), var("Z"), var("z")
    hypY = pourtout("x", non(appartient(var("x"), vY)))   # (∀x)(x∉Y) = (Y|X)R
    hypZ = pourtout("x", non(appartient(var("x"), vZ)))   # (∀x)(x∉Z) = (Z|X)R
    conj = N.assume(et(hypY, hypZ))
    hY, hZ = conjonction_elim_gauche(conj), conjonction_elim_droite(conj)
    # Y⊂Z et Z⊂Y par EX FALSO (S2) sur z∉Y, z∉Z, généralisés sur z :
    YsubZ = N.generalisation("z", N.modus_ponens(
        instancie(hY, vz), N.s2(non(appartient(vz, vY)), appartient(vz, vZ))))
    ZsubY = N.generalisation("z", N.modus_ponens(
        instancie(hZ, vz), N.s2(non(appartient(vz, vZ)), appartient(vz, vY))))
    YeqZ = N.modus_ponens(conjonction_intro(YsubZ, ZsubY),
                          extensionnalite_appliquee(vY, vZ))   # Y = Z (A1)
    imp = N.loi_deduction(et(hypY, hypZ), YeqZ)                # (… et …) ⇒ Y=Z
    return N.generalisation("Y", N.generalisation("Z", imp))   # (∀Y)(∀Z)(…)


def vide_relation_fonctionnelle_cible():
    """Énoncé visé : « (∀x)(x∉X) est univoque en X » (vérification stricte)."""
    return relation_univoque_x(_R_vide(), "X", "Y", "Z")


__all__ = ["vide_ssi_sans_element", "non_vide_ssi_element",
           "vide_inclus_partout", "sous_ensemble_vide_ssi_egal",
           "vacuite_sur_vide", "vide_relation_fonctionnelle",
           "vide_relation_fonctionnelle_cible"]
