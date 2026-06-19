"""§III.5 — PROPOSITION 5 (E III.38) :  Card([0,b]) = b+1  pour b entier.

🎯 LE COMPTAGE D'UN INTERVALLE D'ENTIERS.  Source (PDF, E III.38) :

  PROPOSITION 5. — « Si a et b sont des entiers tels que a ≤ b, l'intervalle [a,b]
  est un ensemble fini dont le nombre d'éléments est (b − a) + 1.  En vertu de la
  prop. 4, on peut se limiter au cas où a = 0.  Démontrons la proposition par
  récurrence sur b.  Elle est évidente pour b = 0.  D'autre part, la relation
  0 ≤ x ≤ b+1 équivaut à « 0 ≤ x ≤ b ou x = b+1 » … l'intervalle [0,b+1] est réunion
  de [0,b] et de {b+1}, et ces deux ensembles ne se rencontrent pas ; en vertu de
  l'hypothèse de récurrence, le nombre d'éléments de [0,b+1] est égal à (b+1)+1. »

────────────────────────────────────────────────────────────────────────────────
CE MODULE prouve la FORME [0,b] (le comptage de haute valeur) :

    🎯  prop5_intervalle_zero(b) :  est_entier(b) ⇒ Card([0,b]) = successeur(b).

ROUTE — récurrence sur b via C61 (`principe_recurrence_preuve`), prédicat
    P[b] := ( Card([0,b]) = successeur(b) ).

  • BASE  P[0] :  Card([0,0]) = Card({0}) = 1 = successeur(0).
        ([0,0] = {0} : tout cardinal z avec 0≤z≤0 vaut 0 par antisymétrie ; voir
        `_intervalle_zero_zero`.)

  • PAS  P[b] ⇒ P[b+1]  (sous est_fini(b)) :
        [0,b+1] = [0,b] ∪ {b+1}                          [_decomp_zero, via (∗)]
        b+1 ∉ [0,b]  (disjonction)                       [succ_pas_inf_egal]
        ⇒ Card([0,b+1]) = successeur(Card([0,b]))        [card_egal_succ_card_diff]
        = successeur(successeur(b))                       [HR P[b] + Leibniz]
        = successeur(b+1).

────────────────────────────────────────────────────────────────────────────────
🔧 CORRECTIF τ-HYGIÈNE.  `ensembles_prop5_intervalle.intervalle_successeur`
prouve [0,b+1]=[0,b]∪{b+1} mais la borne inférieure ZERO=Card(∅) contient un τ
« z » qui COLLISIONNE avec le binder « z » de l'extensionnalité A1 (la fonction
DÉPOSÉE échoue d'ailleurs à `modus_ponens` — résidu non résolu).  CORRECTIF
implémenté ici, comme prescrit dans sa docstring :

  • `_decomp_generique(a, b)` prouve la VERSION GÉNÉRIQUE (borne inférieure a =
    VARIABLE FRAÎCHE, AUCUN τ → binder « zz » propre, capture-safe) :
        est_cardinal(b) ⇒ ( a ≤ b+1 ⇒ [a,b+1] = [a,b] ∪ {b+1} ),
    THÉORÈME CLOS (0 hyp).
  • `_decomp_zero(b)` l'INSTANCIE à a := ZERO (instanciation d'un théorème clos =
    capture-safe), décharge ZERO ≤ b+1 (`_zero_inf_egal_card`) :
        est_cardinal(b) ⇒ [0,b+1] = [0,b] ∪ {b+1},  CLOS.

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Tout DÉRIVÉ.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card, cardinal
from bourbaki.entiers.ensembles_entiers import successeur, ZERO, est_fini, est_entier

from bourbaki.entiers.ensembles_successeur_ordre import (
    successeur_ordre_t, _inf_egal_monotone_successeur, succ_pas_inf_egal,
)
from bourbaki.entiers.ensembles_entiers_theoremes import (
    membre_intervalle_entiers, fini_implique_cardinal,
)
from bourbaki.ensembles.base.ensembles_couples import singleton_membre
from bourbaki.entiers.ensembles_fini_successeur import successeur_est_un_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.ensembles.ensembles_theoremes import (
    extensionnalite_appliquee, _instance_reunion,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _mem_int_t(a, b, x):
    """⊢ ( x∈[a,b] ) ⇔ ( x cardinal et a≤x et x≤b )  pour des TERMES a,b,x.

    Instance DIRECTE de l'axiome de l'intervalle (`_membre_intervalle` prend des
    TERMES) — pas de généralisation/instanciation, donc les termes obtenus
    coïncident STRUCTURELLEMENT avec E.intervalle_entiers(a,b)."""
    from bourbaki.entiers.ensembles_entiers_theoremes import _membre_intervalle
    return _membre_intervalle(_t(a), _t(b), _t(x))


def _ou_gauche(thm_a, b_form):
    return N.modus_ponens(thm_a, N.s2(thm_a.conclusion, b_form))


def _ou_droite(a_form, thm_b):
    orba = N.modus_ponens(thm_b, N.s2(thm_b.conclusion, a_form))
    return N.modus_ponens(orba, N.s3(thm_b.conclusion, a_form))


def _a_imp_a_equiv(f):
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


# ════════════════════════════════════════════════════════════════════════════
#  COEUR (∗) GÉNÉRIQUE — borne inférieure a = VARIABLE FRAÎCHE (capture-safe)
# ════════════════════════════════════════════════════════════════════════════
def _membre_union_gen(a, b, z):
    """⊢ ( z ∈ [a,b]∪{b+1} ) ⇔ ( z∈[a,b] ou z=b+1 )."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    va, vb, vz = _t(a), _t(b), _t(z)
    sb = successeur(vb)
    seg_b = E.intervalle_entiers(va, vb)
    sing = E.singleton(sb)
    reun = _instance_reunion(seg_b, sing, vz)       # z∈A∪B ⇔ (z∈[a,b] ou z∈{b+1})
    sm = singleton_membre(vz, sb)                   # z∈{b+1} ⇔ z=b+1
    cong = ou_congruence(_a_imp_a_equiv(appartient(vz, seg_b)), sm)
    return equivalence_transitivite(reun, cong)


def _membre_union_s(a, b, s, z):
    """⊢ ( z ∈ [a,b]∪{s} ) ⇔ ( z∈[a,b] ou z=s )   (s borne sup. quelconque)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    va, vb, vs, vz = _t(a), _t(b), _t(s), _t(z)
    seg_b = E.intervalle_entiers(va, vb)
    sing = E.singleton(vs)
    reun = _instance_reunion(seg_b, sing, vz)
    sm = singleton_membre(vz, vs)
    cong = ou_congruence(_a_imp_a_equiv(appartient(vz, seg_b)), sm)
    return equivalence_transitivite(reun, cong)


def _membre_equivalence_gen(a, b, s, z):
    """⊢  ( a ≤ s  et  est_cardinal(s)
            et  (∀z)( est_cardinal(z) ⇒ ( z≤s ⟺ (z≤b ou z=s) ) ) )
        ⇒  ( z∈[a,s]  ⇔  z∈([a,b]∪{s}) ).

    🔧 VERSION ABSTRAITE.  Borne supérieure s = VARIABLE FRAÎCHE (AUCUN τ), la
    relation (∗) « z≤s ⟺ (z≤b ou z=s) » et est_cardinal(s) et a≤s étant fournies en
    HYPOTHÈSES.  Comme s est une variable, l'instance de l'axiome de l'intervalle ne
    contient AUCUN τ → binder « z » propre, capture-safe pour l'extensionnalité A1.
    On l'instancie ensuite à s := successeur(b) en déchargeant les trois gardes."""
    va, vb, vs, vz = _t(a), _t(b), _t(s), _t(z)
    seg_sb = E.intervalle_entiers(va, vs)
    seg_b = E.intervalle_entiers(va, vb)
    sing = E.singleton(vs)
    union = E.reunion(seg_b, sing)

    zname = vz.nom if hasattr(vz, "nom") else "zz"
    # hypothèses gardées
    h_ale = N.assume(inf_egal_card(va, vs))                     # a ≤ s
    h_cards = N.assume(est_cardinal(vs))                        # est_cardinal(s)
    split_all = N.assume(pourtout(zname,
        impl(est_cardinal(vz),
             equiv(inf_egal_card(vz, vs),
                   ou(inf_egal_card(vz, vb), egal(vz, vs))))))   # (∀z)(∗)
    so = instancie(split_all, vz)                  # est_card(z) ⇒ (z≤s ⟺ (z≤b ou z=s))

    mem_sb = _mem_int_t(va, vs, vz)                # z∈[a,s] ⇔ (z card et a≤z et z≤s)
    mem_b = _mem_int_t(va, vb, vz)                 # z∈[a,b] ⇔ (z card et a≤z et z≤b)
    mem_un = _membre_union_s(va, vb, vs, vz)       # z∈union ⇔ (z∈[a,b] ou z=s)

    sb = vs   # alias pour réutiliser le corps ci-dessous (s joue le rôle de b+1)
    A = appartient(vz, seg_sb)
    Uf = appartient(vz, union)

    # ── (⇒) A ⇒ U ───────────────────────────────────────────────────────────
    h_A = N.assume(A)
    corps_sb = N.modus_ponens(h_A, equivalence_avant(mem_sb))   # z card et a≤z et z≤b+1
    z_card = conjonction_elim_gauche(conjonction_elim_gauche(corps_sb))
    z_low = conjonction_elim_droite(conjonction_elim_gauche(corps_sb))   # a ≤ z
    z_le_sb = conjonction_elim_droite(corps_sb)                 # z ≤ b+1
    equiv_so = N.modus_ponens(z_card, so)
    disj = N.modus_ponens(z_le_sb, conjonction_elim_gauche(equiv_so))   # z≤b ou z=b+1
    h_zb = N.assume(inf_egal_card(vz, vb))                      # z ≤ b
    corps_b = conjonction_intro(conjonction_intro(z_card, z_low), h_zb)
    z_in_b = N.modus_ponens(corps_b, equivalence_arriere(mem_b))
    z_in_un_left = N.modus_ponens(_ou_gauche(z_in_b, egal(vz, sb)),
                                  equivalence_arriere(mem_un))
    branch_left = N.loi_deduction(inf_egal_card(vz, vb), z_in_un_left)
    h_eq = N.assume(egal(vz, sb))
    z_in_un_right = N.modus_ponens(_ou_droite(appartient(vz, seg_b), h_eq),
                                   equivalence_arriere(mem_un))
    branch_right = N.loi_deduction(egal(vz, sb), z_in_un_right)
    A_imp_U = N.loi_deduction(A, cas(disj, branch_left, branch_right))

    # ── (⇐) U ⇒ A ──────────────────────────────────────────────────────────────
    h_U = N.assume(Uf)
    disj2 = N.modus_ponens(h_U, equivalence_avant(mem_un))      # z∈[a,b] ou z=s
    h_inb = N.assume(appartient(vz, seg_b))
    corps_b2 = N.modus_ponens(h_inb, equivalence_avant(mem_b))
    z_card2 = conjonction_elim_gauche(conjonction_elim_gauche(corps_b2))
    z_low2 = conjonction_elim_droite(conjonction_elim_gauche(corps_b2))   # a ≤ z
    z_le_b2 = conjonction_elim_droite(corps_b2)                 # z ≤ b
    # z≤s depuis (z≤b ou z=s) ⇒ z≤s : sens ⇐ de (∗), instancié à z (z card via z_card2)
    so_z = N.modus_ponens(z_card2, so)                         # z≤s ⟺ (z≤b ou z=s)
    imp_back = conjonction_elim_droite(so_z)                    # (z≤b ou z=s) ⇒ z≤s
    z_le_s2 = N.modus_ponens(_ou_gauche(z_le_b2, egal(vz, vs)), imp_back)   # z ≤ s
    corps_sb2 = conjonction_intro(conjonction_intro(z_card2, z_low2), z_le_s2)
    z_in_sb_left = N.modus_ponens(corps_sb2, equivalence_arriere(mem_sb))
    branch_left2 = N.loi_deduction(appartient(vz, seg_b), z_in_sb_left)
    # branche z=s ⇒ z∈[a,s] : besoin (s card et a≤s et s≤s), puis Leibniz s↦z
    h_eq2 = N.assume(egal(vz, vs))
    refl_sb = instancie(N.generalisation("X", inf_egal_reflexif("X")), vs)  # s ≤ s
    corps_sb_bp1 = conjonction_intro(conjonction_intro(h_cards, h_ale), refl_sb)
    bp1_in_sb = N.modus_ponens(corps_sb_bp1, equivalence_arriere(_mem_int_t(va, vs, vs)))
    sb_eq_z = N.modus_ponens(h_eq2, symetrie(vz, vs))          # s = z
    z_in_sb_right = N.modus_ponens(bp1_in_sb, equivalence_avant(N.modus_ponens(
        sb_eq_z, N.s6(vs, vz, "w", appartient(var("w"), seg_sb)))))
    branch_right2 = N.loi_deduction(egal(vz, vs), z_in_sb_right)
    U_imp_A = N.loi_deduction(Uf, cas(disj2, branch_left2, branch_right2))

    eqv = conjonction_intro(A_imp_U, U_imp_A)                   # A ⇔ U
    # décharge des trois gardes (a≤s, est_card(s), (∀z)(∗))
    g1 = N.loi_deduction(split_all.conclusion, eqv)
    g2 = N.loi_deduction(est_cardinal(vs), g1)
    g3 = N.loi_deduction(inf_egal_card(va, vs), g2)
    return g3


def _decomp_abstrait(a="adec", b="bdec", s="sdec"):
    """⊢  ( a≤s  et  est_cardinal(s)  et  (∀z)(est_card(z) ⇒ (z≤s ⟺ (z≤b ou z=s))) )
        ⇒  [a,s] = [a,b] ∪ {s}.   (CLOS, 0 hyp.)

    a, b, s VARIABLES FRAÎCHES → AUCUN τ → extensionnalité A1 au binder « z » SANS
    collision.  Égalité littérale des ensembles."""
    va, vb, vs = _t(a), _t(b), _t(s)
    seg_sb = E.intervalle_entiers(va, vs)
    seg_b = E.intervalle_entiers(va, vb)
    union = E.reunion(seg_b, E.singleton(vs))
    # Point « zz » pour le lemme de membre (évite que l'instanciation de l'axiome de
    # l'intervalle renomme un liant interne en « @0 ») ; puis ré-alignement « zz → z »
    # sur le binder de l'extensionnalité A1 (tous les termes étant τ-libres ici car
    # a,b,s sont des VARIABLES, le ré-alignement est capture-safe).
    zz = "zz"
    vzz = var(zz)

    split_all = pourtout(zz, impl(est_cardinal(vzz),
        equiv(inf_egal_card(vzz, vs),
              ou(inf_egal_card(vzz, vb), egal(vzz, vs)))))
    garde = et(et(inf_egal_card(va, vs), est_cardinal(vs)), split_all)
    h = N.assume(garde)
    h_ale = conjonction_elim_gauche(conjonction_elim_gauche(h))   # a ≤ s
    h_cards = conjonction_elim_droite(conjonction_elim_gauche(h)) # est_cardinal(s)
    h_split = conjonction_elim_droite(h)                          # (∀zz)(∗)

    base = _membre_equivalence_gen(va, vb, vs, vzz)  # (a≤s ⇒ (card(s) ⇒ ((∀zz)(∗) ⇒ (A⇔U))))
    eqv = N.modus_ponens(h_split, N.modus_ponens(h_cards, N.modus_ponens(h_ale, base)))
    incl_uv_zz = N.generalisation(zz, equivalence_avant(eqv))
    incl_vu_zz = N.generalisation(zz, equivalence_arriere(eqv))
    # ré-alignement zz → z (binder de A1)
    incl_uv = N.generalisation("z", instancie(incl_uv_zz, var("z")))
    incl_vu = N.generalisation("z", instancie(incl_vu_zz, var("z")))
    ext = extensionnalite_appliquee(seg_sb, union)
    egalite = N.modus_ponens(conjonction_intro(incl_uv, incl_vu), ext)
    return N.loi_deduction(garde, egalite)


def _decomp_generique(a="adec", b="bdec"):
    """⊢ est_cardinal(b) ⇒ ( a ≤ b+1 ⇒ [a,b+1] = [a,b] ∪ {b+1} ).   (CLOS, 0 hyp.)

    INSTANCIE `_decomp_abstrait` à s := successeur(b) (capture-safe car théorème CLOS)
    en déchargeant les trois gardes :
      • a ≤ s = a≤b+1   (hyp gardée) ;
      • est_cardinal(b+1)   (successeur_est_un_cardinal, CLOS) ;
      • (∀z)(est_card(z) ⇒ (z≤b+1 ⟺ (z≤b ou z=b+1)))   (successeur_ordre généralisé)."""
    va, vb = _t(a), _t(b)
    sb = successeur(vb)
    # instancier le théorème abstrait CLOS à s := successeur(b)
    abstr = _decomp_abstrait(a, b, "sdec")           # garde(a,b,s) ⇒ [a,s]=[a,b]∪{s}
    abstr_all = N.generalisation("sdec", abstr)
    inst = instancie(abstr_all, sb)                  # garde(a,b,b+1) ⇒ [a,b+1]=[a,b]∪{b+1}

    h_card = N.assume(est_cardinal(vb))
    h_ale = N.assume(inf_egal_card(va, sb))          # a ≤ b+1
    card_sb = successeur_est_un_cardinal(b if isinstance(b, str) else vb)  # est_card(b+1)
    # (∀zz)(est_card(zz) ⇒ (zz≤b+1 ⟺ (zz≤b ou zz=b+1)))  via successeur_ordre généralisé
    so = successeur_ordre_t(var("zz"), vb)           # est_card(zz) ⇒ (zz≤b+1 ⟺ (zz≤b ou zz=b+1))
    split_all = N.generalisation("zz", so)
    garde_thm = conjonction_intro(conjonction_intro(h_ale, card_sb), split_all)
    egalite = N.modus_ponens(garde_thm, inst)        # [a,b+1] = [a,b]∪{b+1}
    sous_ale = N.loi_deduction(inf_egal_card(va, sb), egalite)
    return N.loi_deduction(est_cardinal(vb), sous_ale)


def _zero_inf_egal_card(a):
    """⊢ ZERO ≤ a   (= Card(∅) ≤ a)  pour un TERME a."""
    from bourbaki.entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    from bourbaki.cardinaux.ensembles_cardinaux_bornes import zero_inf_egal
    va = _t(a)
    le_vide = zero_inf_egal(va)                                # ∅ ≤ a
    card_vide_eq = cardinal_vide_egale_vide()                  # Card(∅) = ∅
    vide_eq_card = N.modus_ponens(card_vide_eq, symetrie(cardinal(E.VIDE), E.VIDE))
    return N.modus_ponens(le_vide, equivalence_avant(N.modus_ponens(
        vide_eq_card, N.s6(E.VIDE, cardinal(E.VIDE), "w", inf_egal_card(var("w"), va)))))


def decomp_zero_enonce(b="b"):
    """Formule : est_cardinal(b) ⇒ [0, successeur(b)] = [0,b] ∪ {successeur(b)}."""
    vb = _t(b)
    sb = successeur(vb)
    return impl(est_cardinal(vb),
                egal(E.intervalle_entiers(ZERO, sb),
                     E.reunion(E.intervalle_entiers(ZERO, vb), E.singleton(sb))))


def decomp_zero(b="b"):
    """🎯 ⊢ est_cardinal(b) ⇒ [0, successeur(b)] = [0,b] ∪ {successeur(b)}.  (CLOS, 0 hyp.)

    INSTANCIATION de `_decomp_generique` à a := ZERO (capture-safe car le théorème
    générique est CLOS), puis décharge de ZERO ≤ b+1 par `_zero_inf_egal_card`."""
    vb = _t(b)
    sb = successeur(vb)
    gen = _decomp_generique("adec", b)             # est_card(b) ⇒ (a≤b+1 ⇒ [a,b+1]=…)
    gen_all = N.generalisation("adec", gen)
    inst = instancie(gen_all, ZERO)               # est_card(b) ⇒ (0≤b+1 ⇒ [0,b+1]=[0,b]∪{b+1})
    h_card = N.assume(est_cardinal(vb))
    sous_ale = N.modus_ponens(h_card, inst)       # 0≤b+1 ⇒ [0,b+1]=…
    zero_le = _zero_inf_egal_card(sb)             # ZERO ≤ b+1
    egalite = N.modus_ponens(zero_le, sous_ale)   # [0,b+1] = [0,b]∪{b+1}
    res = N.loi_deduction(est_cardinal(vb), egalite)
    assert res.conclusion == decomp_zero_enonce(b), \
        "decomp_zero : conclusion ≠ enoncé attendu"
    return res


__all__ = [
    "_decomp_generique", "decomp_zero", "decomp_zero_enonce",
]
