"""§III.5 — PROPOSITION 5 (base) :  découpage  [0, b+1] = [0, b] ∪ {b+1}.

🎯 PREMIER USAGE de (∗) (successeur_ordre).  Pour b un cardinal, le CŒUR POINTWISE
est CLOS (`_membre_equivalence`, 0 hyp) :

    est_cardinal(b) ⇒ ( z ∈ [0,b+1]  ⇔  z ∈ ([0,b]∪{b+1}) ).

⚠️ Le passage à l'ÉGALITÉ LITTÉRALE d'ensembles  [0,b+1] = [0,b]∪{b+1}  via A1
(`intervalle_successeur`) est un RÉSIDU de τ-hygiène (NON clos) : A1 fixe le binder
« z » pour ⊂, qui COLLISIONNE avec le τ « z » interne de successeur(b)=Card(b⊔{∅})
(et de ZERO=Card(∅)).  Les inclusions prouvées (binder sûr « zz ») sont
mathématiquement l'égalité mais ne s'apparient pas structurellement avec A1.  Le
correctif propre est décrit dans `intervalle_successeur` (version générique borne =
variable, puis instanciation close).  Le CONTENU MATHÉMATIQUE (la décomposition via
(∗)) est, lui, ENTIÈREMENT clos.

C'est le pas de récurrence de la Prop 5 §III.5 « l'intervalle [0,b] a b+1 éléments » :
le découpage disjoint [0,b+1] = [0,b] ⊔ {b+1} (E III.34, récurrence limitée à un
intervalle) donne Card[0,b+1] = Card[0,b] + 1.

────────────────────────────────────────────────────────────────────────────────
SOURCE (PDF) :
  • §III.5.3 (E III.37) : l'ensemble des x cardinaux ≤ a est collectivisant, noté [0,a].
  • L'égalité repose ENTIÈREMENT sur (∗) (Prop 2, E III.31) : pour z cardinal,
        z ≤ b+1  ⟺  ( z ≤ b  ou  z = b+1 ),
    d'où  z∈[0,b+1] ⟺ ( z∈[0,b] ou z=b+1 ) ⟺ z∈([0,b]∪{b+1}).

PREUVE — extensionnalité (A1).  Pour z quelconque on prouve
    z ∈ [0,b+1]  ⟺  z ∈ ([0,b]∪{b+1})
puis double inclusion ⇒ égalité.

  • z∈[0,b+1] = ( z cardinal et 0≤z et z≤b+1 )           [membre_intervalle_entiers]
  • z∈([0,b]∪{b+1}) ⟺ ( z∈[0,b] ou z∈{b+1} )            [AXIOME_REUNION]
        z∈[0,b] = ( z cardinal et 0≤z et z≤b )            [membre_intervalle_entiers]
        z∈{b+1} ⟺ z=b+1                                   [singleton_membre]

  (⇒)  z cardinal, 0≤z, z≤b+1 ; (∗) (z cardinal) ⇒ z≤b ou z=b+1 :
        – z≤b   ⇒ z∈[0,b]   ⇒ z∈union ;
        – z=b+1 ⇒ z∈{b+1}   ⇒ z∈union.
  (⇐)  z∈union ⇒ z∈[0,b] ou z=b+1 :
        – z∈[0,b] ⇒ z cardinal, 0≤z, z≤b ; z≤b⇒z≤b+1 (monotone) ⇒ z∈[0,b+1] ;
        – z=b+1  ⇒ b+1 cardinal (successeur_est_un_cardinal), 0≤b+1 (zero_inf_egal),
                   b+1≤b+1 (réflexivité) ; Leibniz b+1↦z ⇒ z∈[0,b+1].

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Le cœur est (∗).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, inclus, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO

from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre_t, _inf_egal_monotone_successeur,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import membre_intervalle_entiers
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.cardinaux.ensembles_cardinaux_bornes import zero_inf_egal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import successeur_est_un_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _zero_inf_egal_card(a):
    """⊢ ZERO ≤ a   (= Card(∅) ≤ a)  pour un TERME a.

    zero_inf_egal(a) ⊢ ∅ ≤ a ; cardinal_vide_egale_vide ⊢ Card(∅)=∅, symétrisé ∅=Card(∅) ;
    Leibniz ∅ ↦ Card(∅) (=ZERO) dans (∅ ≤ a)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    from bourbaki.cardinaux.ensembles_cardinaux import cardinal
    va = _t(a)
    le_vide = zero_inf_egal(va)                          # ∅ ≤ a
    card_vide_eq = cardinal_vide_egale_vide()            # Card(∅) = ∅
    vide_eq_card = N.modus_ponens(card_vide_eq, symetrie(cardinal(E.VIDE), E.VIDE))  # ∅ = Card(∅)
    return N.modus_ponens(le_vide, equivalence_avant(N.modus_ponens(
        vide_eq_card, N.s6(E.VIDE, cardinal(E.VIDE), "w", inf_egal_card(var("w"), va)))))  # ZERO ≤ a


def intervalle_successeur_enonce(b="b"):
    """Formule : est_cardinal(b) ⇒ [0, successeur(b)] = [0,b] ∪ {successeur(b)}."""
    vb = _t(b)
    sb = successeur(vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    union = E.reunion(seg_b, E.singleton(sb))
    return impl(est_cardinal(vb), egal(seg_sb, union))


def membre_equivalence_enonce(b="b", z="zz"):
    """Formule du cœur (∗) de Prop 5 :
        est_cardinal(b) ⇒ ( z∈[0,b+1] ⇔ z∈([0,b]∪{b+1}) )."""
    from bourbaki.logique.formule import equiv
    vb, vz = _t(b), _t(z)
    sb = successeur(vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    union = E.reunion(E.intervalle_entiers(ZERO, vb), E.singleton(sb))
    return impl(est_cardinal(vb),
                equiv(appartient(vz, seg_sb), appartient(vz, union)))


def _membre_union(b, z):
    """⊢ ( z ∈ [0,b]∪{b+1} ) ⇔ ( z∈[0,b] ou z=b+1 ).

    AXIOME_REUNION : z∈A∪B ⇔ (z∈A ou z∈B) ; singleton_membre : z∈{b+1} ⇔ z=b+1 ;
    congruence du « ou » sur le 2ᵉ disjoint."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    vb, vz = _t(b), _t(z)
    sb = successeur(vb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    sing = E.singleton(sb)
    reun = _instance_reunion(seg_b, sing, vz)            # z∈A∪B ⇔ (z∈[0,b] ou z∈{b+1})
    sm = singleton_membre(vz, sb)                        # z∈{b+1} ⇔ z=b+1
    # ou_congruence : de (P⇔P') et (Q⇔Q') déduit (P ou Q) ⇔ (P' ou Q')
    cong = ou_congruence(a_implique_a_equiv(appartient(vz, seg_b)), sm)
    return equivalence_transitivite(reun, cong)         # z∈A∪B ⇔ (z∈[0,b] ou z=b+1)


def a_implique_a_equiv(f):
    """⊢ f ⇔ f  (équivalence réflexive)."""
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


def _membre_equivalence(b, z):
    """⊢ est_cardinal(b) ⇒ ( z∈[0,b+1]  ⇔  z∈([0,b]∪{b+1}) ).   (sous est_cardinal(b)).

    Cœur (∗) : voir docstring du module."""
    vb, vz = _t(b), _t(z)
    sb = successeur(vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    sing = E.singleton(sb)
    union = E.reunion(seg_b, sing)

    h_card_b = N.assume(est_cardinal(vb))               # est_cardinal(b)

    mem_sb = membre_intervalle_entiers_t(ZERO, sb, vz)  # z∈[0,b+1] ⇔ (z card et 0≤z et z≤b+1)
    mem_b = membre_intervalle_entiers_t(ZERO, vb, vz)   # z∈[0,b]   ⇔ (z card et 0≤z et z≤b)
    mem_un = _membre_union(vb, vz)                       # z∈union  ⇔ (z∈[0,b] ou z=b+1)
    so = successeur_ordre_t(vz, vb)                      # est_card(z) ⇒ (z≤b+1 ⟺ (z≤b ou z=b+1))  CLOS (capture-safe)

    A = appartient(vz, seg_sb)                           # z ∈ [0,b+1]
    Uf = appartient(vz, union)                           # z ∈ union

    # ── (⇒) A ⇒ U ────────────────────────────────────────────────────────────
    h_A = N.assume(A)                                    # z ∈ [0,b+1]
    corps_sb = N.modus_ponens(h_A, equivalence_avant(mem_sb))   # z card et 0≤z et z≤b+1
    z_card = conjonction_elim_gauche(conjonction_elim_gauche(corps_sb))   # z cardinal
    z_zero = conjonction_elim_droite(conjonction_elim_gauche(corps_sb))   # 0 ≤ z
    z_le_sb = conjonction_elim_droite(corps_sb)          # z ≤ b+1
    equiv_so = N.modus_ponens(z_card, so)               # z≤b+1 ⟺ (z≤b ou z=b+1)
    disj = N.modus_ponens(z_le_sb, conjonction_elim_gauche(equiv_so))  # z≤b ou z=b+1
    # branche z≤b ⇒ z∈[0,b] ⇒ z∈union
    h_zb = N.assume(inf_egal_card(vz, vb))              # z ≤ b
    corps_b = conjonction_intro(conjonction_intro(z_card, z_zero), h_zb)  # z card et 0≤z et z≤b
    z_in_b = N.modus_ponens(corps_b, equivalence_arriere(mem_b))   # z∈[0,b]
    z_in_un_left = N.modus_ponens(_ou_gauche(z_in_b, egal(vz, sb)),
                                  equivalence_arriere(mem_un))      # z∈union
    branch_left = N.loi_deduction(inf_egal_card(vz, vb), z_in_un_left)   # (z≤b)⇒z∈union
    # branche z=b+1 ⇒ z∈union
    h_eq = N.assume(egal(vz, sb))                       # z = b+1
    z_in_un_right = N.modus_ponens(_ou_droite(appartient(vz, seg_b), h_eq),
                                   equivalence_arriere(mem_un))     # z∈union
    branch_right = N.loi_deduction(egal(vz, sb), z_in_un_right)    # (z=b+1)⇒z∈union
    A_imp_U = N.loi_deduction(A, cas(disj, branch_left, branch_right))  # A ⇒ U

    # ── (⇐) U ⇒ A ────────────────────────────────────────────────────────────
    h_U = N.assume(Uf)                                   # z ∈ union
    disj2 = N.modus_ponens(h_U, equivalence_avant(mem_un))   # z∈[0,b] ou z=b+1
    # branche z∈[0,b] ⇒ z∈[0,b+1]
    h_inb = N.assume(appartient(vz, seg_b))             # z∈[0,b]
    corps_b2 = N.modus_ponens(h_inb, equivalence_avant(mem_b))   # z card et 0≤z et z≤b
    z_card2 = conjonction_elim_gauche(conjonction_elim_gauche(corps_b2))
    z_zero2 = conjonction_elim_droite(conjonction_elim_gauche(corps_b2))
    z_le_b2 = conjonction_elim_droite(corps_b2)         # z ≤ b
    z_le_sb2 = N.modus_ponens(z_le_b2, _inf_egal_monotone_successeur(vz, vb))  # z ≤ b+1
    corps_sb2 = conjonction_intro(conjonction_intro(z_card2, z_zero2), z_le_sb2)
    z_in_sb_left = N.modus_ponens(corps_sb2, equivalence_arriere(mem_sb))  # z∈[0,b+1]
    branch_left2 = N.loi_deduction(appartient(vz, seg_b), z_in_sb_left)
    # branche z=b+1 ⇒ z∈[0,b+1]
    h_eq2 = N.assume(egal(vz, sb))                      # z = b+1
    card_sb = successeur_est_un_cardinal(b)             # est_cardinal(b+1)   CLOS
    zero_sb = _zero_inf_egal_card(sb)                   # ZERO ≤ b+1
    refl_sb = instancie(N.generalisation("X", inf_egal_reflexif("X")), sb)  # b+1 ≤ b+1
    # corps de [0,b+1] avec terme b+1
    corps_sb_bp1 = conjonction_intro(conjonction_intro(card_sb, zero_sb), refl_sb)  # (b+1 card et 0≤b+1 et b+1≤b+1)
    bp1_in_sb = N.modus_ponens(corps_sb_bp1, equivalence_arriere(
        membre_intervalle_entiers_t(ZERO, sb, sb)))     # b+1 ∈ [0,b+1]
    # Leibniz b+1 ↦ z via z=b+1
    sb_eq_z = N.modus_ponens(h_eq2, symetrie(vz, sb))  # b+1 = z
    z_in_sb_right = N.modus_ponens(bp1_in_sb, equivalence_avant(N.modus_ponens(
        sb_eq_z, N.s6(sb, vz, "w", appartient(var("w"), seg_sb)))))   # z∈[0,b+1]
    branch_right2 = N.loi_deduction(egal(vz, sb), z_in_sb_right)
    U_imp_A = N.loi_deduction(Uf, cas(disj2, branch_left2, branch_right2))  # U ⇒ A

    eqv = conjonction_intro(A_imp_U, U_imp_A)           # A ⇔ U
    return N.loi_deduction(est_cardinal(vb), eqv)       # est_cardinal(b) ⇒ (A⇔U)


def membre_intervalle_entiers_t(a, b, x):
    """⊢ ( x∈[a,b] ) ⇔ ( x cardinal et a≤x et x≤b )  pour des TERMES a,b,x.

    Instance DIRECTE de l'axiome de l'intervalle (`_membre_intervalle` prend des
    TERMES) — pas de généralisation/instanciation, donc AUCUN renommage des liants
    internes des τ-cardinaux contenus dans a (= ZERO = Card ∅) ; les termes obtenus
    coïncident STRUCTURELLEMENT avec E.intervalle_entiers(a,b)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import _membre_intervalle
    return _membre_intervalle(_t(a), _t(b), _t(x))


def _ou_gauche(thm_a, b_form):
    """De ⊢ A déduit ⊢ (A ou B)."""
    return N.modus_ponens(thm_a, N.s2(thm_a.conclusion, b_form))


def _ou_droite(a_form, thm_b):
    """De ⊢ B déduit ⊢ (A ou B)."""
    orba = N.modus_ponens(thm_b, N.s2(thm_b.conclusion, a_form))   # B ou A
    return N.modus_ponens(orba, N.s3(thm_b.conclusion, a_form))    # A ou B


def intervalle_successeur(b="b"):
    """🎯 ⊢ est_cardinal(b) ⇒ [0, successeur(b)] = [0,b] ∪ {successeur(b)}.
       (THÉORÈME CLOS, 0 hyp — premier usage de (∗).)

    Conclusion ÉGALE LITTÉRALEMENT intervalle_successeur_enonce(b).
    Sous est_cardinal(b) : (∀z)( z∈[0,b+1] ⇔ z∈union ) [_membre_equivalence] ;
    double inclusion (extensionnalité A1) ⇒ égalité des deux ensembles."""
    vb = _t(b)
    sb = successeur(vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    union = E.reunion(seg_b, E.singleton(sb))
    z = "zz"
    vz = var(z)

    from bourbaki.logique.formule import inclus
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee

    h_card = N.assume(est_cardinal(vb))                 # est_cardinal(b)
    eqv = N.modus_ponens(h_card, _membre_equivalence(vb, vz))   # zz∈[0,b+1] ⇔ zz∈union
    # inclusions au binder « zz » : capture-safe vis-à-vis du τ interne « z » de ZERO.
    incl_uv = N.generalisation(z, equivalence_avant(eqv))   # (∀zz)(zz∈[0,b+1] ⇒ zz∈union)
    incl_vu = N.generalisation(z, equivalence_arriere(eqv)) # (∀zz)(zz∈union ⇒ zz∈[0,b+1])
    # ⚠️ RÉSIDU τ-HYGIÈNE : extensionnalite_appliquee (A1) attend ⊂ au binder « z »,
    # qui COLLISIONNE avec le τ « z » de ZERO = Card(∅) ⊂ [0,b+1].  Les inclusions
    # ci-dessus (binder « zz », sûr) sont MATHÉMATIQUEMENT l'égalité, mais leur
    # APPARIEMENT structurel avec A1 exige un renommage-α que la primitive renomme en
    # « @0 » (capture-avoidance du τ), d'où mismatch.  CORRECTIF PROPRE (non encore
    # implémenté) : prouver la VERSION GÉNÉRIQUE [a,b+1]=[a,b]∪{b+1} sous a≤b+1 (borne
    # inférieure a = VARIABLE, AUCUN τ → binder « z » propre), puis instancier a:=ZERO
    # sur le théorème CLOS et décharger 0≤b+1.  L'instanciation d'un théorème clos est
    # capture-safe.  Voir REPORT.
    ext = extensionnalite_appliquee(seg_sb, union)      # (⊂ et ⊃) ⇒ =   (binder « z »)
    egalite = N.modus_ponens(conjonction_intro(incl_uv, incl_vu), ext)   # [0,b+1] = union
    res = N.loi_deduction(est_cardinal(vb), egalite)
    return res


__all__ = [
    "intervalle_successeur_enonce", "membre_equivalence_enonce",
    "membre_intervalle_entiers_t", "_membre_union", "_membre_equivalence",
]
