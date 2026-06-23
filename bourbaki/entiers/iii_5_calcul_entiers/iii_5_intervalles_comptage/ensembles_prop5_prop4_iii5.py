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
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, est_fini, est_entier

from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre_t, _inf_egal_monotone_successeur, succ_pas_inf_egal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    membre_intervalle_entiers, fini_implique_cardinal,
)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import successeur_est_un_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (
    extensionnalite_appliquee, _instance_reunion,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import card_egal_succ_card_diff


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
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import _membre_intervalle
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
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import cardinal_vide_egale_vide
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


# ════════════════════════════════════════════════════════════════════════════
#  BASE de récurrence P[0] :  Card([0,0]) = successeur(0)
# ════════════════════════════════════════════════════════════════════════════
def _intervalle_aa_abstrait(a="aiaa"):
    """⊢ est_cardinal(a) ⇒ [a,a] = {a}.   (CLOS, 0 hyp.)

    a = VARIABLE FRAÎCHE (AUCUN τ) → extensionnalité A1 au binder « z » SANS
    collision.  z∈[a,a] ⟺ (z card et a≤z et z≤a) ; antisymétrie (a≤z et z≤a, avec
    card(a), card(z)) ⇒ z=a ; réciproquement z=a ⇒ (a card, a≤a, a≤a)."""
    from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
        inf_egal_antisymetrique_card,
    )
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
    va = _t(a)
    seg = E.intervalle_entiers(va, va)
    sing = E.singleton(va)
    # Point « zz » pour les caractérisations de membre (évite que l'instanciation des
    # axiomes/lemmes renomme un τ interne) ; la relation commune R := (zz = a) est
    # τ-LIBRE et [a,a]/{a} sont τ-libres (a variable), donc egalite_par_extension
    # (qui ré-instancie à « z ») est capture-safe.
    zz = "zz"
    vz = var(zz)

    h_card_a = N.assume(est_cardinal(va))                # est_cardinal(a)
    mem = _mem_int_t(va, va, vz)                         # zz∈[a,a] ⇔ (zz card et a≤zz et zz≤a)
    sm = singleton_membre(vz, va)                        # zz∈{a} ⇔ zz=a

    # charU : (∀zz)( zz∈[a,a] ⇔ zz=a )
    # (⇒) zz∈[a,a] ⇒ zz=a
    h_in = N.assume(appartient(vz, seg))
    corps = N.modus_ponens(h_in, equivalence_avant(mem))
    z_card = conjonction_elim_gauche(conjonction_elim_gauche(corps))
    z0 = conjonction_elim_droite(conjonction_elim_gauche(corps))   # a ≤ zz
    z1 = conjonction_elim_droite(corps)                  # zz ≤ a
    anti = inf_egal_antisymetrique_card("aant", "bant")  # (∀a∀b)((a≤b et b≤a et card a et card b)⇒a=b)
    anti_inst = instancie(instancie(anti, vz), va)       # (zz≤a et a≤zz et card zz et card a) ⇒ zz=a
    hyp_anti = conjonction_intro(conjonction_intro(conjonction_intro(z1, z0), z_card), h_card_a)
    z_eq_a = N.modus_ponens(hyp_anti, anti_inst)         # zz = a
    imp_fwd = N.loi_deduction(appartient(vz, seg), z_eq_a)
    # (⇐) zz=a ⇒ zz∈[a,a]
    h_eq = N.assume(egal(vz, va))                        # zz = a
    refl_a = instancie(N.generalisation("X", inf_egal_reflexif("X")), va)  # a ≤ a
    corps_a = conjonction_intro(conjonction_intro(h_card_a, refl_a), refl_a)
    a_in_seg = N.modus_ponens(corps_a, equivalence_arriere(_mem_int_t(va, va, va)))  # a∈[a,a]
    a_eq_z = N.modus_ponens(h_eq, symetrie(vz, va))      # a = zz
    z_in_seg = N.modus_ponens(a_in_seg, equivalence_avant(N.modus_ponens(
        a_eq_z, N.s6(va, vz, "w", appartient(var("w"), seg)))))
    imp_bwd = N.loi_deduction(egal(vz, va), z_in_seg)
    charU = N.generalisation(zz, conjonction_intro(imp_fwd, imp_bwd))   # (∀zz)(zz∈[a,a] ⇔ zz=a)
    charV = N.generalisation(zz, sm)                                    # (∀zz)(zz∈{a} ⇔ zz=a)

    egalite = egalite_par_extension(charU, charV, seg, sing, x="z")     # [a,a] = {a}
    return N.loi_deduction(est_cardinal(va), egalite)


def _intervalle_zero_zero():
    """⊢ [0,0] = {0}.   (CLOS, 0 hyp.)

    INSTANCIE `_intervalle_aa_abstrait` à a := ZERO (théorème CLOS → capture-safe),
    décharge est_cardinal(0) (zero_est_un_cardinal)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import zero_est_un_cardinal
    abstr = N.generalisation("aiaa", _intervalle_aa_abstrait("aiaa"))
    inst = instancie(abstr, ZERO)                        # est_cardinal(0) ⇒ [0,0]={0}
    return N.modus_ponens(zero_est_un_cardinal(), inst)  # [0,0] = {0}


def _instance_diff_t(e, x, z):
    """⊢ ( z ∈ e∖x ) ⇔ ( z∈e et ¬(z∈x) )   (axiome de la différence, termes)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, _t(e)), _t(x)), _t(z))


def _singleton_diff_self_abstrait(a="asds"):
    """⊢ {a} ∖ {a} = ∅.   (CLOS, 0 hyp.)

    a = VARIABLE FRAÎCHE.  z∈{a}∖{a} ⟺ (z∈{a} et z∉{a}) — contradictoire — d'où
    {a}∖{a} et ∅ ont les mêmes membres (aucun)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension, vide_sans_element
    va = _t(a)
    sing = E.singleton(va)
    diff = E.difference(sing, sing)
    zz = "zz"
    vz = var(zz)

    di = _instance_diff_t(sing, sing, vz)          # zz∈{a}∖{a} ⇔ (zz∈{a} et zz∉{a})
    # (⇒) zz∈{a}∖{a} ⇒ zz∈∅  (faux ⇒ tout) : de (zz∈{a} et zz∉{a}) déduire ⊥ puis zz∈∅
    h_in = N.assume(appartient(vz, diff))
    conj = N.modus_ponens(h_in, equivalence_avant(di))   # zz∈{a} et zz∉{a}
    pin = conjonction_elim_gauche(conj)            # zz∈{a}
    pnin = conjonction_elim_droite(conj)           # ¬(zz∈{a})
    falso = N.modus_ponens(pin, N.modus_ponens(pnin,
        N.s2(non(appartient(vz, sing)), appartient(vz, E.VIDE))))   # ⊥ ⇒ zz∈∅
    imp_fwd = N.loi_deduction(appartient(vz, diff), falso)
    # (⇐) zz∈∅ ⇒ zz∈{a}∖{a}  (vide_sans_element : ¬(zz∈∅))
    h_vide = N.assume(appartient(vz, E.VIDE))
    falso2 = N.modus_ponens(h_vide, N.modus_ponens(vide_sans_element(zz),
        N.s2(non(appartient(vz, E.VIDE)), appartient(vz, diff))))   # ⊥ ⇒ zz∈{a}∖{a}
    imp_bwd = N.loi_deduction(appartient(vz, E.VIDE), falso2)
    charU = N.generalisation(zz, conjonction_intro(imp_fwd, imp_bwd))   # (∀zz)(zz∈diff ⇔ zz∈∅)
    charV = N.generalisation(zz, _a_imp_a_equiv(appartient(vz, E.VIDE)))  # (∀zz)(zz∈∅ ⇔ zz∈∅)
    return egalite_par_extension(charU, charV, diff, E.VIDE, x="z")     # {a}∖{a} = ∅


def _card_singleton_zero_egale_succ_zero():
    """⊢ Card({0}) = successeur(0).   (CLOS, 0 hyp.)

    card_egal_succ_card_diff({0}, 0) : 0∈{0} ⇒ Card{0} = successeur(Card({0}∖{0})) ;
    {0}∖{0}=∅ (_singleton_diff_self) ⇒ Card({0}∖{0})=Card∅ ; or 0 = Card∅
    (définitionnel ZERO=Card(∅)), donc successeur(Card∅) = successeur(0)."""
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import card_egal_succ_card_diff
    sing0 = E.singleton(ZERO)
    diff0 = E.difference(sing0, sing0)

    # 0 ∈ {0} : singleton_membre(0,0) sens ⇐ depuis 0=0
    zero_in = N.modus_ponens(N.reflexivite(ZERO),
                             equivalence_arriere(singleton_membre(ZERO, ZERO)))   # 0 ∈ {0}
    # card_egal_succ_card_diff sur des NOMS frais puis instanciation aux termes
    cesd_gen = N.generalisation("Xcesd", N.generalisation("x0cesd",
        card_egal_succ_card_diff(var("Xcesd"), var("x0cesd"))))
    cesd = instancie(instancie(cesd_gen, sing0), ZERO)   # (0∈{0}) ⇒ Card{0}=successeur(Card({0}∖{0}))
    card0_eq = N.modus_ponens(zero_in, cesd)        # Card{0} = successeur(Card({0}∖{0}))
    diff_eq = N.generalisation("asds", _singleton_diff_self_abstrait("asds"))
    diff_eq0 = instancie(diff_eq, ZERO)             # {0}∖{0} = ∅
    # Card({0}∖{0}) = Card∅  (Leibniz du terme Card)
    card_diff_eq_card_vide = N.modus_ponens(N.reflexivite(cardinal(diff0)),
        equivalence_avant(N.modus_ponens(diff_eq0,
            N.s6(diff0, E.VIDE, "w", egal(cardinal(diff0), cardinal(var("w")))))))  # Card({0}∖{0})=Card∅
    # successeur(Card({0}∖{0})) = successeur(Card∅)   (congruence de successeur via Leibniz)
    refl_succ = N.reflexivite(successeur(cardinal(diff0)))   # succ(Card({0}∖{0})) = succ(Card({0}∖{0}))
    succ_eq = N.modus_ponens(refl_succ, equivalence_avant(N.modus_ponens(
        card_diff_eq_card_vide,
        N.s6(cardinal(diff0), cardinal(E.VIDE), "w",
             egal(successeur(cardinal(diff0)), successeur(var("w")))))))   # succ(Card({0}∖{0}))=succ(Card∅)
    # ZERO == cardinal(VIDE) définitionnellement, donc successeur(Card∅)==successeur(ZERO)
    return composer_egalites(card0_eq, succ_eq)     # Card{0} = successeur(0)


def prop5_base_enonce():
    """Formule : Card([0,0]) = successeur(0)."""
    return egal(cardinal(E.intervalle_entiers(ZERO, ZERO)), successeur(ZERO))


def prop5_base():
    """🎯 ⊢ Card([0,0]) = successeur(0).   (CLOS, 0 hyp — base de la récurrence Prop 5.)

    [0,0] = {0} (_intervalle_zero_zero) ⇒ Card[0,0] = Card{0} (Leibniz) ;
    Card{0} = successeur(0) (_card_singleton_zero_egale_succ_zero)."""
    seg = E.intervalle_entiers(ZERO, ZERO)
    sing0 = E.singleton(ZERO)
    eq_sets = _intervalle_zero_zero()                   # [0,0] = {0}
    # Card[0,0] = Card{0}  : Leibniz seg↦sing0 dans (Card seg = Card seg)
    refl = N.reflexivite(cardinal(seg))                 # Card[0,0] = Card[0,0]
    card_seg_eq_card_sing = N.modus_ponens(refl, equivalence_avant(N.modus_ponens(
        eq_sets, N.s6(seg, sing0, "w", egal(cardinal(seg), cardinal(var("w")))))))  # Card[0,0]=Card{0}
    card_sing_eq = _card_singleton_zero_egale_succ_zero()   # Card{0} = successeur(0)
    res = composer_egalites(card_seg_eq_card_sing, card_sing_eq)   # Card[0,0] = successeur(0)
    assert res.conclusion == prop5_base_enonce(), "prop5_base : conclusion inattendue"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  PAS de récurrence :  ( A∪{x} )∖{x} = A   sous  x∉A
# ════════════════════════════════════════════════════════════════════════════
def _union_singleton_diff_abstrait(a="auds", x="xuds"):
    """⊢ ¬(x∈A)  ⇒  ( A∪{x} )∖{x} = A.   (CLOS, 0 hyp.)

    A, x VARIABLES FRAÎCHES (τ-libres).  z∈(A∪{x})∖{x} ⟺ ((z∈A ou z=x) et z≠x)
    ⟺ z∈A (sous x∉A : si z∈A alors z≠x ; et z∈A donne le ou).  R := z∈A τ-libre."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
    va, vx = _t(a), _t(x)
    sing = E.singleton(vx)
    union = E.reunion(va, sing)
    diff = E.difference(union, sing)
    zz = "zz"
    vz = var(zz)

    h_xnA = N.assume(non(appartient(vx, va)))      # x ∉ A
    di = _instance_diff_t(union, sing, vz)         # z∈(A∪{x})∖{x} ⇔ (z∈A∪{x} et z∉{x})
    ru = _instance_reunion(va, sing, vz)           # z∈A∪{x} ⇔ (z∈A ou z∈{x})
    sm = singleton_membre(vz, vx)                  # z∈{x} ⇔ z=x

    # (⇒) z∈diff ⇒ z∈A
    h_in = N.assume(appartient(vz, diff))
    conj = N.modus_ponens(h_in, equivalence_avant(di))   # z∈A∪{x} et z∉{x}
    z_in_u = conjonction_elim_gauche(conj)         # z∈A∪{x}
    z_nin_sing = conjonction_elim_droite(conj)     # ¬(z∈{x})
    disj = N.modus_ponens(z_in_u, equivalence_avant(ru))  # z∈A ou z∈{x}
    branch_A = a_implique_a(appartient(vz, va))    # (z∈A) ⇒ z∈A
    h_zsing = N.assume(appartient(vz, sing))       # z∈{x}
    falso = N.modus_ponens(h_zsing, N.modus_ponens(z_nin_sing,
        N.s2(non(appartient(vz, sing)), appartient(vz, va))))   # ⊥ ⇒ z∈A
    branch_S = N.loi_deduction(appartient(vz, sing), falso)
    z_in_A = cas(disj, branch_A, branch_S)         # z∈A
    imp_fwd = N.loi_deduction(appartient(vz, diff), z_in_A)
    # (⇐) z∈A ⇒ z∈diff   (sous x∉A : z∈A ⇒ z≠x)
    h_zA = N.assume(appartient(vz, va))            # z∈A
    z_in_u2 = N.modus_ponens(_ou_gauche(h_zA, appartient(vz, sing)),
                             equivalence_arriere(ru))   # z∈A∪{x}
    # z∉{x} : si z∈{x} alors z=x, Leibniz z↦x dans z∈A donne x∈A, contredit x∉A
    h_zsing2 = N.assume(appartient(vz, sing))      # z∈{x}
    z_eq_x = N.modus_ponens(h_zsing2, equivalence_avant(sm))   # z = x
    x_in_A = N.modus_ponens(h_zA, equivalence_avant(N.modus_ponens(
        z_eq_x, N.s6(vz, vx, "w", appartient(var("w"), va)))))   # x∈A
    falso2 = N.modus_ponens(x_in_A, N.modus_ponens(h_xnA,
        N.s2(non(appartient(vx, va)), non(appartient(vz, sing)))))   # ⊥ ⇒ ¬(z∈{x})
    z_nin_sing2 = N.modus_ponens(N.loi_deduction(appartient(vz, sing), falso2),
                                 N.s1(non(appartient(vz, sing))))    # ¬(z∈{x})
    z_in_diff = N.modus_ponens(conjonction_intro(z_in_u2, z_nin_sing2),
                               equivalence_arriere(di))   # z∈diff
    imp_bwd = N.loi_deduction(appartient(vz, va), z_in_diff)

    charU = N.generalisation(zz, conjonction_intro(imp_fwd, imp_bwd))   # (∀zz)(zz∈diff ⇔ zz∈A)
    charV = N.generalisation(zz, _a_imp_a_equiv(appartient(vz, va)))    # (∀zz)(zz∈A ⇔ zz∈A)
    egalite = egalite_par_extension(charU, charV, diff, va, x="z")      # (A∪{x})∖{x} = A
    return N.loi_deduction(non(appartient(vx, va)), egalite)


def _succ_non_dans_intervalle_zero(b="b"):
    """⊢ est_fini(b) ⇒ ¬( successeur(b) ∈ [0,b] ).   (CLOS, 0 hyp.)

    si b+1∈[0,b] alors b+1≤b (borne sup. de l'intervalle), or ¬(b+1≤b)
    (succ_pas_inf_egal sous est_fini(b))."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import intervalle_implique_borne_sup
    vb = _t(b)
    sb = successeur(vb)
    seg = E.intervalle_entiers(ZERO, vb)

    h_fini = N.assume(est_fini(vb))
    n_le = N.modus_ponens(h_fini, succ_pas_inf_egal(b))   # ¬(b+1 ≤ b)
    # b+1∈[0,b] ⇒ b+1≤b   (intervalle_implique_borne_sup, termes)
    bsup = _intervalle_borne_sup_t(ZERO, vb, sb)          # b+1∈[0,b] ⇒ b+1≤b
    h_in = N.assume(appartient(sb, seg))                  # b+1 ∈ [0,b]
    le = N.modus_ponens(h_in, bsup)                       # b+1 ≤ b
    falso = N.modus_ponens(le, N.modus_ponens(n_le,
        N.s2(non(inf_egal_card(sb, vb)), non(appartient(sb, seg)))))   # ⊥ ⇒ ¬(b+1∈[0,b])
    n_in = N.modus_ponens(N.loi_deduction(appartient(sb, seg), falso),
                          N.s1(non(appartient(sb, seg))))  # ¬(b+1∈[0,b])
    return N.loi_deduction(est_fini(vb), n_in)


def _intervalle_borne_sup_t(a, b, x):
    """⊢ ( x∈[a,b] ) ⇒ ( x≤b )   pour des TERMES (instance directe, sans renommage)."""
    mem = _mem_int_t(a, b, x)                       # x∈[a,b] ⇔ (x card et a≤x et x≤b)
    h = N.assume(appartient(_t(x), E.intervalle_entiers(_t(a), _t(b))))
    corps = N.modus_ponens(h, equivalence_avant(mem))
    sup = conjonction_elim_droite(corps)            # x ≤ b
    return N.loi_deduction(appartient(_t(x), E.intervalle_entiers(_t(a), _t(b))), sup)


# ════════════════════════════════════════════════════════════════════════════
#  PROP 5 (forme [0,b]) :  est_entier(b) ⇒ Card([0,b]) = successeur(b)
# ════════════════════════════════════════════════════════════════════════════
def _P(b):
    """Prédicat P[b] := ( Card([0,b]) = successeur(b) )."""
    vb = _t(b)
    return egal(cardinal(E.intervalle_entiers(ZERO, vb)), successeur(vb))


def _diff_intervalle_succ(b):
    """⊢ est_fini(b) ⇒ ( [0,b+1] ∖ {b+1} = [0,b] ).   (CLOS, 0 hyp.)

    decomp_zero : [0,b+1]=[0,b]∪{b+1} (sous est_cardinal(b)) ;
    _union_singleton_diff_abstrait(A:=[0,b], x:=b+1) sous (b+1∉[0,b]) :
        ([0,b]∪{b+1})∖{b+1} = [0,b] ;
    Leibniz [0,b]∪{b+1} ↦ [0,b+1] (via decomp_zero symétrisé) dans le membre gauche."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
    vb = _t(b)
    sb = successeur(vb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    sing = E.singleton(sb)
    union = E.reunion(seg_b, sing)

    h_fini = N.assume(est_fini(vb))
    card_b = N.modus_ponens(h_fini, fini_implique_cardinal(vb))   # est_cardinal(b)
    dz = N.modus_ponens(card_b, decomp_zero(b))                   # [0,b+1] = [0,b]∪{b+1}
    n_in = N.modus_ponens(h_fini, _succ_non_dans_intervalle_zero(b))  # ¬(b+1∈[0,b])
    # ([0,b]∪{b+1})∖{b+1} = [0,b]   via lemme abstrait instancié (A:=[0,b], x:=b+1)
    uds = N.generalisation("auds", N.generalisation("xuds",
        _union_singleton_diff_abstrait("auds", "xuds")))
    uds_inst = instancie(instancie(uds, seg_b), sb)              # ¬(b+1∈[0,b]) ⇒ (([0,b]∪{b+1})∖{b+1}=[0,b])
    eq_union_diff = N.modus_ponens(n_in, uds_inst)              # ([0,b]∪{b+1})∖{b+1} = [0,b]
    # Leibniz : remplacer [0,b]∪{b+1} par [0,b+1] dans le membre gauche, via dz symétrisé
    union_eq_sb = N.modus_ponens(dz, symetrie(seg_sb, union))   # [0,b]∪{b+1} = [0,b+1]
    diff_union = E.difference(union, sing)
    diff_sb = E.difference(seg_sb, sing)
    # (diff_union = [0,b]) et (diff_union = diff_sb) ⇒ diff_sb = [0,b]
    diff_union_eq_diff_sb = N.modus_ponens(N.reflexivite(diff_union),
        equivalence_avant(N.modus_ponens(union_eq_sb,
            N.s6(union, seg_sb, "w", egal(diff_union, E.difference(var("w"), sing))))))  # diff_union = diff_sb
    diff_sb_eq_union = symetrie_thm = N.modus_ponens(diff_union_eq_diff_sb,
        symetrie(diff_union, diff_sb))                          # diff_sb = diff_union
    res = composer_egalites(diff_sb_eq_union, eq_union_diff)    # [0,b+1]∖{b+1} = [0,b]
    return N.loi_deduction(est_fini(vb), res)


def _prop5_pas(b):
    """⊢ ( est_fini(b) et P[b] )  ⇒  P[b+1].   (CLOS, 0 hyp.)

    P[b+1] = ( Card([0,b+1]) = successeur(b+1) ).  Chaîne :
        Card([0,b+1]) = successeur(Card([0,b+1]∖{b+1}))   [card_egal_succ_card_diff, b+1∈[0,b+1]]
                      = successeur(Card([0,b]))            [_diff_intervalle_succ + Leibniz]
                      = successeur(successeur(b))          [HR P[b] + Leibniz]
                      = successeur(b+1)."""
    vb = _t(b)
    sb = successeur(vb)
    seg_sb = E.intervalle_entiers(ZERO, sb)
    seg_b = E.intervalle_entiers(ZERO, vb)
    sing = E.singleton(sb)
    diff_sb = E.difference(seg_sb, sing)

    h = N.assume(et(est_fini(vb), _P(vb)))
    h_fini = conjonction_elim_gauche(h)            # est_fini(b)
    h_HR = conjonction_elim_droite(h)              # Card([0,b]) = successeur(b)

    # b+1 ∈ [0,b+1] : singleton_membre + (b+1 card, 0≤b+1, b+1≤b+1) via _mem_int_t
    card_sb = successeur_est_un_cardinal(b if isinstance(b, str) else vb)   # est_card(b+1)
    zero_le = _zero_inf_egal_card(sb)              # 0 ≤ b+1
    refl_sb = instancie(N.generalisation("X", inf_egal_reflexif("X")), sb)  # b+1 ≤ b+1
    corps = conjonction_intro(conjonction_intro(card_sb, zero_le), refl_sb)
    sb_in = N.modus_ponens(corps, equivalence_arriere(_mem_int_t(ZERO, sb, sb)))   # b+1∈[0,b+1]

    # Card([0,b+1]) = successeur(Card([0,b+1]∖{b+1}))
    cesd_gen = N.generalisation("Xcesd", N.generalisation("x0cesd",
        card_egal_succ_card_diff(var("Xcesd"), var("x0cesd"))))
    cesd = instancie(instancie(cesd_gen, seg_sb), sb)   # (b+1∈[0,b+1]) ⇒ Card[0,b+1]=succ(Card([0,b+1]∖{b+1}))
    card_sb_eq = N.modus_ponens(sb_in, cesd)            # Card[0,b+1] = successeur(Card([0,b+1]∖{b+1}))

    # successeur(Card([0,b+1]∖{b+1})) = successeur(Card([0,b]))  via [0,b+1]∖{b+1}=[0,b]
    diff_eq = N.modus_ponens(h_fini, _diff_intervalle_succ(b))   # [0,b+1]∖{b+1} = [0,b]
    refl_succ = N.reflexivite(successeur(cardinal(diff_sb)))
    succ_card_diff_eq = N.modus_ponens(refl_succ, equivalence_avant(N.modus_ponens(
        diff_eq, N.s6(diff_sb, seg_b, "w",
            egal(successeur(cardinal(diff_sb)), successeur(cardinal(var("w"))))))))
    # successeur(Card([0,b])) = successeur(successeur(b))  via HR
    refl_succ2 = N.reflexivite(successeur(cardinal(seg_b)))
    succ_HR = N.modus_ponens(refl_succ2, equivalence_avant(N.modus_ponens(
        h_HR, N.s6(cardinal(seg_b), sb, "w",
            egal(successeur(cardinal(seg_b)), successeur(var("w")))))))   # succ(Card[0,b])=succ(succ b)

    # assemblage : Card[0,b+1] = succ(Card([0,b+1]∖{b+1})) = succ(Card[0,b]) = succ(succ b) = succ(b+1)
    chain1 = composer_egalites(card_sb_eq, succ_card_diff_eq)   # Card[0,b+1]=succ(Card[0,b])
    chain2 = composer_egalites(chain1, succ_HR)                # Card[0,b+1]=succ(succ b) = succ(b+1)
    # successeur(successeur(b)) IS successeur(b+1) (sb==successeur(b)) → conclusion == P[b+1]
    res = chain2
    cible = _P(sb)                                             # Card([0,b+1]) = successeur(b+1)
    assert res.conclusion == cible, "prop5_pas : conclusion ≠ P[b+1]"
    return N.loi_deduction(et(est_fini(vb), _P(vb)), res)


def prop5_intervalle_zero_enonce(b="b"):
    """Formule : est_entier(b) ⇒ Card([0,b]) = successeur(b)."""
    vb = _t(b)
    return impl(est_entier(vb), _P(vb))


def prop5_intervalle_zero(b="b"):
    """🎯🎯 ⊢ est_entier(b) ⇒ Card([0,b]) = successeur(b).   (CLOS, 0 hyp.)

    PROPOSITION 5 §III.5 (E III.38), forme a=0 : « l'intervalle [0,b] a b+1
    éléments ».  Récurrence sur b via C61 (`principe_recurrence_preuve`) avec le
    prédicat P[b] := (Card([0,b]) = successeur(b)) :
      • base P[0] = prop5_base (Card[0,0]=successeur(0)) ;
      • pas (est_fini(b) et P[b]) ⇒ P[b+1] = _prop5_pas (decomp disjoint + additivité)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve, predecesseur_fini_universel,
    )
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    vb = _t(b)
    n, k = "npr5", "kpr5"

    # base et pas, généralisés au binder n de la récurrence
    p0 = prop5_base()                              # P[0]   (Card[0,0]=successeur(0))
    # step : (∀n)((est_fini(n) et P[n]) ⇒ P[n+1])
    pas_n = _prop5_pas(var(n))                     # (est_fini(n) et P[n]) ⇒ P[n+1]
    step = N.generalisation(n, pas_n)

    # C61 sur le prédicat P
    princ_imp = principe_recurrence_preuve(_P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))
    ante = conjonction_intro(p0, step)             # P[0] et step
    fini_implique_Pn = N.modus_ponens(ante, princ_imp)   # (∀n)(est_fini(n) ⇒ P[n])

    h_ent = N.assume(est_entier(vb))               # est_entier(b) = est_fini(b)
    Pb = N.modus_ponens(h_ent, instancie(fini_implique_Pn, vb))   # P[b]
    res = N.loi_deduction(est_entier(vb), Pb)
    assert res.conclusion == prop5_intervalle_zero_enonce(b), \
        "prop5_intervalle_zero : conclusion ≠ enoncé attendu"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 4 §III.5 (E III.37) — translation x ↦ a+x : [0,b] → [a,a+b]
#
#  « L'application x ↦ a+x est un isomorphisme strictement croissant de [0,b] sur
#    [a,a+b], et y ↦ y−a est l'isomorphisme réciproque. »
#
#  PROUVÉ ICI (inconditionnel, honnête) :
#    • prop4_translation_bien_definie : x∈[0,b] ⇒ (a+x)∈[a,a+b]   (l'image tombe dans
#      le bon intervalle — « well-defined ») ;
#    • prop4_translation_croissante   : x≤x' ⇒ a+x ≤ a+x'        (CROISSANCE LARGE).
#
#  ⚠️ REPORTÉ (bloqué sur la DIFFÉRENCE OPAQUE `difference_entiers` = μc.(b=a+c), sans
#     axiome caractérisant — cf. ensembles_entiers.py:151) ET sur la STRICTE monotonie
#     (`prop3_somme_stricte_cible` elle-même REPORTÉE dans le dépôt, cf.
#     ensembles_calcul_entiers_props.py:349, exige cardinal_pas_entre/la différence) :
#       – la STRICTE croissance x<x' ⇒ a+x < a+x'  (⇒ injectivité) ;
#       – la SURJECTIVITÉ sur [a,a+b] et l'inverse y↦y−a (exigent y−a, opaque) ;
#       – donc l'isomorphisme d'ordre COMPLET.
#     Jamais postulé.  La croissance LARGE + le bon ciblage sont le cœur prouvable.
# ════════════════════════════════════════════════════════════════════════════
def prop4_translation_bien_definie_enonce(a="a", b="b", x="x"):
    """Formule : ( est_cardinal(a) et x∈[0,b] ) ⇒ ( a+x ∈ [a, a+b] )."""
    va, vb, vx = _t(a), _t(b), _t(x)
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
    ax = somme_cardinale_binaire(va, vx)
    ab = somme_cardinale_binaire(va, vb)
    return impl(et(est_cardinal(va), appartient(vx, E.intervalle_entiers(ZERO, vb))),
                appartient(ax, E.intervalle_entiers(va, ab)))


def prop4_translation_bien_definie(a="a", b="b", x="x"):
    """🎯 ⊢ ( est_cardinal(a) et x∈[0,b] ) ⇒ ( a+x ∈ [a, a+b] ).   (CLOS, 0 hyp.)

    PROPOSITION 4, « well-defined » : la translation x↦a+x envoie [0,b] DANS [a,a+b].
    Membre de [a,a+b] ⟺ (a+x cardinal et a≤a+x et a+x≤a+b) :
      • a+x = Card(a⊔x) est un cardinal (card_est_un_cardinal) ;
      • a ≤ a+x : Card a ≤ a+x (inf_egal_somme_gauche_binaire) et Card a = a
        (cardinal_de_cardinal sous est_cardinal a) ;
      • a+x ≤ a+b : de x≤b (borne sup. de [0,b]) via somme_binaire_monotone_droite."""
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire, somme_disjointe,
    )
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
        inf_egal_somme_gauche_binaire, somme_binaire_monotone_droite,
    )
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
    va, vb, vx = _t(a), _t(b), _t(x)
    ax = somme_cardinale_binaire(va, vx)               # a+x = Card(a⊔x)
    ab = somme_cardinale_binaire(va, vb)               # a+b
    seg_codomaine = E.intervalle_entiers(va, ab)

    h = N.assume(et(est_cardinal(va), appartient(vx, E.intervalle_entiers(ZERO, vb))))
    h_card_a = conjonction_elim_gauche(h)              # est_cardinal(a)
    h_in = conjonction_elim_droite(h)                  # x ∈ [0,b]

    # a+x cardinal  (= Card(a⊔x))
    ax_card = card_est_un_cardinal(somme_disjointe(va, vx), "X")   # est_cardinal(a+x)

    # a ≤ a+x : Card a ≤ a+x, puis Card a = a
    # (lemmes sommes sur NOMS frais puis instanciation — leurs binders internes « x »
    #  collisionnent avec un point « x » ; on contourne par generalise/instancie)
    iesgb = N.generalisation("aieg", N.generalisation("bieg",
        inf_egal_somme_gauche_binaire("aieg", "bieg")))
    cardA_le_ax = instancie(instancie(iesgb, va), vx)              # Card a ≤ a+x
    cardA_eq_a = N.modus_ponens(h_card_a, cardinal_de_cardinal(va)) # Card a = a
    a_le_ax = N.modus_ponens(cardA_le_ax, equivalence_avant(N.modus_ponens(
        cardA_eq_a, N.s6(cardinal(va), va, "w", inf_egal_card(var("w"), ax)))))   # a ≤ a+x

    # x ≤ b  (borne sup. de [0,b]) → a+x ≤ a+b
    x_le_b = N.modus_ponens(h_in, _intervalle_borne_sup_t(ZERO, vb, vx))   # x ≤ b
    sbmd = N.generalisation("asbm", N.generalisation("bsbm", N.generalisation("csbm",
        somme_binaire_monotone_droite("asbm", "bsbm", "csbm"))))
    sbmd_inst = instancie(instancie(instancie(sbmd, vx), vb), va)  # (x≤b) ⇒ (a+x ≤ a+b)
    ax_le_ab = N.modus_ponens(x_le_b, sbmd_inst)                   # a+x ≤ a+b

    corps = conjonction_intro(conjonction_intro(ax_card, a_le_ax), ax_le_ab)
    ax_in = N.modus_ponens(corps, equivalence_arriere(_mem_int_t(va, ab, ax)))   # a+x ∈ [a,a+b]
    res = N.loi_deduction(et(est_cardinal(va), appartient(vx, E.intervalle_entiers(ZERO, vb))), ax_in)
    assert res.conclusion == prop4_translation_bien_definie_enonce(a, b, x), \
        "prop4_translation_bien_definie : conclusion inattendue"
    return res


def prop4_translation_croissante_enonce(a="a", x="x", x2="xp"):
    """Formule : ( x ≤ x' ) ⇒ ( a+x ≤ a+x' )   (croissance LARGE)."""
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
    va, vx, vx2 = _t(a), _t(x), _t(x2)
    return impl(inf_egal_card(vx, vx2),
                inf_egal_card(somme_cardinale_binaire(va, vx),
                              somme_cardinale_binaire(va, vx2)))


def prop4_translation_croissante(a="a", x="x", x2="xp"):
    """🎯 ⊢ ( x ≤ x' ) ⇒ ( a+x ≤ a+x' ).   (CLOS, 0 hyp — CROISSANCE LARGE.)

    PROPOSITION 4, monotonie large de la translation : instance directe de
    somme_binaire_monotone_droite (sommant gauche fixe a).  La STRICTE croissance est
    REPORTÉE (cf. en-tête de section)."""
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import somme_binaire_monotone_droite
    va, vx, vx2 = _t(a), _t(x), _t(x2)
    sbmd = N.generalisation("asbm", N.generalisation("bsbm", N.generalisation("csbm",
        somme_binaire_monotone_droite("asbm", "bsbm", "csbm"))))
    res = instancie(instancie(instancie(sbmd, vx), vx2), va)   # (x≤x') ⇒ (a+x ≤ a+x')
    assert res.conclusion == prop4_translation_croissante_enonce(a, x, x2), \
        "prop4_translation_croissante : conclusion inattendue"
    return res


__all__ = [
    "_decomp_generique", "decomp_zero", "decomp_zero_enonce",
    "prop5_base", "prop5_base_enonce",
    "prop5_intervalle_zero", "prop5_intervalle_zero_enonce",
    "prop4_translation_bien_definie", "prop4_translation_bien_definie_enonce",
    "prop4_translation_croissante", "prop4_translation_croissante_enonce",
]
