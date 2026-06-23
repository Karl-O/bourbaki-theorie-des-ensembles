"""§III.4-5 — (∗) ORDRE & SUCCESSEUR :  x ≤ b+1  ⟺  ( x ≤ b  ou  x = b+1 ).

🎯 LE VERROU combinatoire de §III.5 (E III.30-37).  Pour x un cardinal et b
quelconque :

    successeur_ordre(x, b) :=
        est_cardinal(x) ⇒ ( ( x ≤ b+1 )  ⟺  ( x ≤ b  ou  x = b+1 ) ).

────────────────────────────────────────────────────────────────────────────────
SOURCE (lecture du PDF, vérifiée) :

  • PROPOSITION 2 §III.4.2 (E III.31) : « Soit n un entier.  Tout cardinal a tel
    que a ≤ n est un entier.  Si n ≠ 0, il existe un entier m et un seul tel que
    n = m+1, et la relation a < n est équivalente à a ≤ m. »

  • Notre (∗) est la forme « ≤ » de cette équivalence pour n = b+1, m = b :
        a < b+1  ⟺  a ≤ b      [Prop 2]
        a ≤ b+1  ⟺  ( a < b+1  ou  a = b+1 )   [split ≤ / <, logique + réflexivité]
    d'où  a ≤ b+1 ⟺ ( a ≤ b  ou  a = b+1 ).

────────────────────────────────────────────────────────────────────────────────
PREUVE — les DEUX sens sont déjà disponibles dans le dépôt :

  • SENS DIRECT (le DUR : « pas de cardinal strictement entre b et b+1 ») :
        cardinal_pas_entre_garde(x, b)  (ensembles_cardinal_pas_entre_univ, CLOS)
            ⊢ est_cardinal(x) ⇒ ( ( x ≤ b+1 ) ⇒ ( x ≤ b ou x = b+1 ) ).
        C'est exactement `cardinal_pas_entre(x, b)` (ensembles_recurrence_C61),
        DÉJÀ FERMÉ inconditionnellement (theorie=22).

  • SENS RÉCIPROQUE ( ( x ≤ b ou x = b+1 ) ⇒ x ≤ b+1 ), élémentaire :
        – x ≤ b  ⇒ x ≤ b+1 :  b ≤ successeur(b) (_inf_egal_k_successeur, CLOS) puis
          transitivité de ≤ (inf_egal_transitive) ;
        – x = b+1 ⇒ x ≤ b+1 :  réflexivité (b+1) ≤ (b+1) (inf_egal_reflexif_general,
          CLOS) puis Leibniz x ↦ b+1.

COMPAGNONS (corollaires immédiats) :
  • successeur_ordre_strict :  est_cardinal(x) ⇒ ( ( x < b+1 ) ⟺ ( x ≤ b ) )
        (« x < b+1 ⟺ x ≤ b », Prop 2 forme strict), via (∗) + définition de < .

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé.  (∗) est DÉRIVÉ, ses deux
sens venant de théorèmes clos.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, equiv,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie, cas,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, est_fini

# ── briques CLOSES réutilisées ───────────────────────────────────────────────
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_cardinal_pas_entre_univ import cardinal_pas_entre_garde
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinal_pas_entre
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import _inf_egal_k_successeur
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS
# ════════════════════════════════════════════════════════════════════════════
def successeur_ordre_enonce(x="x", b="b"):
    """Formule de (∗) :
        est_cardinal(x) ⇒ ( ( x ≤ b+1 ) ⟺ ( x ≤ b  ou  x = b+1 ) )."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    return impl(est_cardinal(vx),
                equiv(inf_egal_card(vx, sb),
                      ou(inf_egal_card(vx, vb), egal(vx, sb))))


# ════════════════════════════════════════════════════════════════════════════
#  SENS RÉCIPROQUE  :  ( x ≤ b  ou  x = b+1 )  ⇒  x ≤ b+1   (CLOS, 0 hyp)
# ════════════════════════════════════════════════════════════════════════════
def _inf_egal_monotone_successeur(x, b):
    """⊢ ( x ≤ b )  ⇒  ( x ≤ successeur(b) ).   (CLOS, 0 hyp.)

    b ≤ successeur(b) (_inf_egal_k_successeur) ; transitivité de ≤."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    le_b_sb = _inf_egal_k_successeur(vb)                   # b ≤ successeur(b)  CLOS
    trans = instancie(instancie(instancie(N.generalisation("X", N.generalisation("Y",
        N.generalisation("Z", inf_egal_transitive("F", "G", "X", "Y", "Z")))),
        vx), vb), sb)                                     # (x≤b et b≤succ b) ⇒ x≤succ b
    h = N.assume(inf_egal_card(vx, vb))                    # x ≤ b
    res = N.modus_ponens(conjonction_intro(h, le_b_sb), trans)  # x ≤ succ b
    return N.loi_deduction(inf_egal_card(vx, vb), res)     # (x≤b) ⇒ (x≤succ b)


def _egal_successeur_inf_egal(x, b):
    """⊢ ( x = successeur(b) )  ⇒  ( x ≤ successeur(b) ).   (CLOS, 0 hyp.)

    Réflexivité (succ b) ≤ (succ b) (inf_egal_reflexif_general) ; Leibniz réécrit le
    membre gauche succ b ↦ x via x = succ b."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    refl = instancie(N.generalisation("X", inf_egal_reflexif("X")), sb)  # succ b ≤ succ b
    h_eq = N.assume(egal(vx, sb))                          # x = successeur(b)
    sb_eq_x = N.modus_ponens(h_eq, symetrie(vx, sb))       # successeur(b) = x
    res = N.modus_ponens(refl, equivalence_avant(N.modus_ponens(
        sb_eq_x, N.s6(sb, vx, "w", inf_egal_card(var("w"), sb)))))   # x ≤ succ b
    return N.loi_deduction(egal(vx, sb), res)              # (x=succ b) ⇒ (x≤succ b)


def successeur_ordre_reciproque(x="x", b="b"):
    """⊢ ( x ≤ b  ou  x = successeur(b) )  ⇒  ( x ≤ successeur(b) ).   (CLOS, 0 hyp.)

    Disjonction des cas (tactique `cas`)."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    imp_gauche = _inf_egal_monotone_successeur(vx, vb)     # (x≤b) ⇒ (x≤succ b)
    imp_droite = _egal_successeur_inf_egal(vx, vb)         # (x=succ b) ⇒ (x≤succ b)
    h_ou = N.assume(ou(inf_egal_card(vx, vb), egal(vx, sb)))   # x≤b ou x=succ b
    concl = cas(h_ou, imp_gauche, imp_droite)              # x ≤ succ b
    return N.loi_deduction(ou(inf_egal_card(vx, vb), egal(vx, sb)), concl)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 (∗) — successeur_ordre  :  est_cardinal(x) ⇒ ( x≤b+1 ⟺ (x≤b ou x=b+1) )
# ════════════════════════════════════════════════════════════════════════════
def successeur_ordre(x="x", b="b"):
    """🎯 ⊢ est_cardinal(x) ⇒ ( ( x ≤ b+1 ) ⟺ ( x ≤ b  ou  x = b+1 ) ).
       (THÉORÈME CLOS, 0 hyp.)

    Conclusion ÉGALE LITTÉRALEMENT successeur_ordre_enonce(x, b).

    SENS DIRECT  : cardinal_pas_entre_garde(x, b) (CLOS) ⊢ est_cardinal(x) ⇒
                   ( x≤b+1 ⇒ (x≤b ou x=b+1) ).
    SENS RÉCIPRO. : successeur_ordre_reciproque(x, b) (CLOS) ⊢ (x≤b ou x=b+1) ⇒ x≤b+1.
    Sous est_cardinal(x), conjonction des deux implications = l'équivalence."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    A = inf_egal_card(vx, sb)                              # x ≤ b+1
    Bf = ou(inf_egal_card(vx, vb), egal(vx, sb))          # x≤b ou x=b+1

    # SENS DIRECT : sous est_cardinal(x), (x≤b+1) ⇒ (x≤b ou x=b+1)
    garde = cardinal_pas_entre_garde(x, b)                # est_cardinal(x) ⇒ cardinal_pas_entre(x,b)  CLOS
    assert garde.conclusion == impl(est_cardinal(vx), cardinal_pas_entre(vx, vb)), \
        "cardinal_pas_entre_garde : forme inattendue"
    h_card = N.assume(est_cardinal(vx))                   # est_cardinal(x)
    imp_AB = N.modus_ponens(h_card, garde)                # (x≤b+1) ⇒ (x≤b ou x=b+1)
    assert imp_AB.conclusion == impl(A, Bf), "sens direct : forme inattendue"

    # SENS RÉCIPROQUE (inconditionnel)
    imp_BA = successeur_ordre_reciproque(vx, vb)          # (x≤b ou x=b+1) ⇒ (x≤b+1)
    assert imp_BA.conclusion == impl(Bf, A), "sens réciproque : forme inattendue"

    # équivalence = (A⇒B) et (B⇒A)
    eq = conjonction_intro(imp_AB, imp_BA)               # A ⟺ B  [est_cardinal(x)]
    assert eq.conclusion == equiv(A, Bf), "équivalence mal formée"
    res = N.loi_deduction(est_cardinal(vx), eq)          # est_cardinal(x) ⇒ (A⟺B)
    assert res.conclusion == successeur_ordre_enonce(x, b), \
        "successeur_ordre : conclusion ≠ successeur_ordre_enonce(x, b)"
    return res                                            # CLOS, 0 hyp


# ════════════════════════════════════════════════════════════════════════════
#  COMPAGNON STRICT  :  est_cardinal(x) ⇒ ( ( x < b+1 ) ⟺ ( x ≤ b ) )   (Prop 2)
# ════════════════════════════════════════════════════════════════════════════
# ════════════════════════════════════════════════════════════════════════════
#  LEMME COMPAGNON  ¬( b+1 ≤ b )   ( b+1 ∉ [0,b] )   sous est_fini(b)
# ════════════════════════════════════════════════════════════════════════════
def succ_pas_inf_egal_enonce(b="b"):
    """Formule : est_fini(b) ⇒ ¬( successeur(b) ≤ b )."""
    vb = _t(b)
    return impl(est_fini(vb), non(inf_egal_card(successeur(vb), vb)))


def succ_pas_inf_egal(b="b"):
    """⊢ est_fini(b) ⇒ ¬( successeur(b) ≤ b ).   (THÉORÈME CLOS, 0 hyp.)

    « b+1 ∉ [0,b] » sous b fini.  Sous est_fini(b) :  est_cardinal(b)
    (fini_implique_cardinal), est_cardinal(b+1) (successeur_est_un_cardinal), b≠b+1
    (fini_implique_distinct_successeur).  Si b+1≤b : on a aussi b≤b+1
    (_inf_egal_k_successeur), donc par ANTISYMÉTRIE des cardinaux b+1=b ⇒ (sym) b=b+1,
    contredisant b≠b+1.  D'où ¬(b+1≤b)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        fini_implique_distinct_successeur, fini_implique_cardinal,
    )
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import successeur_est_un_cardinal
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
        inf_egal_antisymetrique_card,
    )
    vb = _t(b)
    sb = successeur(vb)

    h_fini = N.assume(est_fini(vb))                       # est_fini(b)
    card_b = N.modus_ponens(h_fini, fini_implique_cardinal(vb))   # est_cardinal(b)
    card_sb = successeur_est_un_cardinal(b)               # est_cardinal(b+1)   CLOS
    b_ne_sb = N.modus_ponens(h_fini, fini_implique_distinct_successeur(vb))  # ¬(b=b+1)

    le_b_sb = _inf_egal_k_successeur(vb)                  # b ≤ b+1   CLOS

    # antisymétrie instanciée à (b+1, b) : (b+1≤b et b≤b+1 et card(b+1) et card(b)) ⇒ b+1=b
    anti = inf_egal_antisymetrique_card("a", "bb")        # (∀a∀b)(…)
    anti_inst = instancie(instancie(anti, sb), vb)
    h_sb_le_b = N.assume(inf_egal_card(sb, vb))           # b+1 ≤ b   (réfutation)
    hyp_anti = conjonction_intro(conjonction_intro(conjonction_intro(
        h_sb_le_b, le_b_sb), card_sb), card_b)            # b+1≤b et b≤b+1 et card(b+1) et card(b)
    sb_eq_b = N.modus_ponens(hyp_anti, anti_inst)         # b+1 = b
    b_eq_sb = N.modus_ponens(sb_eq_b, symetrie(sb, vb))   # b = b+1
    falso = N.modus_ponens(b_eq_sb, N.modus_ponens(b_ne_sb,
        N.s2(non(egal(vb, sb)), non(inf_egal_card(sb, vb)))))   # ¬(b+1≤b)
    n_sb_le_b = N.modus_ponens(N.loi_deduction(inf_egal_card(sb, vb), falso),
                               N.s1(non(inf_egal_card(sb, vb))))   # ¬(b+1≤b)
    res = N.loi_deduction(est_fini(vb), n_sb_le_b)        # est_fini(b) ⇒ ¬(b+1≤b)
    assert res.conclusion == succ_pas_inf_egal_enonce(b), \
        "succ_pas_inf_egal : conclusion ≠ enoncé attendu"
    return res                                            # CLOS, 0 hyp


# ════════════════════════════════════════════════════════════════════════════
#  COMPAGNON STRICT  :  ( est_cardinal(x) et est_fini(b) ) ⇒ ( (x<b+1) ⟺ (x≤b) )
# ════════════════════════════════════════════════════════════════════════════
def successeur_ordre_strict_enonce_fini(x="x", b="b"):
    """Formule : ( est_cardinal(x) et est_fini(b) ) ⇒ ( ( x < b+1 ) ⟺ ( x ≤ b ) )."""
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)
    return impl(et(est_cardinal(vx), est_fini(vb)),
                equiv(inf_strict_card(vx, sb), inf_egal_card(vx, vb)))


def successeur_ordre_strict(x="x", b="b"):
    """⊢ ( est_cardinal(x) et est_fini(b) ) ⇒ ( ( x < b+1 ) ⟺ ( x ≤ b ) ).
       (THÉORÈME CLOS, 0 hyp.)

    « a < n ⟺ a ≤ m » de la PROPOSITION 2 §III.4.2, pour n = b+1, m = b.
    Conclusion ÉGALE LITTÉRALEMENT successeur_ordre_strict_enonce_fini(x, b).
    L'hypothèse est_fini(b) sert UNIQUEMENT à b+1 ∉ [0,b] (succ_pas_inf_egal).

    x < b+1 = ( x≤b+1 et ¬(x=b+1) ).
      • (⇒) sous est_cardinal(x), via (∗) : x≤b+1 ⇒ (x≤b ou x=b+1) ; ¬(x=b+1) élimine
        la 2ᵉ branche ⇒ x≤b.
      • (⇐) sous est_fini(b) : x≤b ⇒ x≤b+1 (monotone) ; ¬(x=b+1) car x=b+1 ⇒ b+1≤b
        (Leibniz dans x≤b), contredisant ¬(b+1≤b) (succ_pas_inf_egal)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
    vx, vb = _t(x), _t(b)
    sb = successeur(vb)

    ante = et(est_cardinal(vx), est_fini(vb))
    h = N.assume(ante)
    h_card = conjonction_elim_gauche(h)                   # est_cardinal(x)
    h_fini = conjonction_elim_droite(h)                   # est_fini(b)

    so = successeur_ordre(x, b)                            # est_card(x) ⇒ (x≤b+1 ⟺ (x≤b ou x=b+1))  CLOS
    equiv_AB = N.modus_ponens(h_card, so)                 # x≤b+1 ⟺ (x≤b ou x=b+1)
    imp_AB = conjonction_elim_gauche(equiv_AB)            # (x≤b+1) ⇒ (x≤b ou x=b+1)

    # ── (⇒)  x<b+1 ⇒ x≤b ─────────────────────────────────────────────────────
    h_strict = N.assume(inf_strict_card(vx, sb))          # x < b+1 = (x≤b+1 et ¬(x=b+1))
    h_le = conjonction_elim_gauche(h_strict)              # x ≤ b+1
    h_ne = conjonction_elim_droite(h_strict)              # ¬(x = b+1)
    disj = N.modus_ponens(h_le, imp_AB)                   # x≤b ou x=b+1
    branch_left = a_implique_a(inf_egal_card(vx, vb))     # (x≤b) ⇒ (x≤b)
    h_eq = N.assume(egal(vx, sb))                         # x = b+1
    falso = N.modus_ponens(h_eq, N.modus_ponens(h_ne,
        N.s2(non(egal(vx, sb)), inf_egal_card(vx, vb))))  # ⊥ ⇒ x≤b
    branch_right = N.loi_deduction(egal(vx, sb), falso)   # (x=b+1) ⇒ (x≤b)
    x_le_b = cas(disj, branch_left, branch_right)         # x ≤ b
    imp_strict_le = N.loi_deduction(inf_strict_card(vx, sb), x_le_b)  # (x<b+1) ⇒ (x≤b)

    # ── (⇐)  x≤b ⇒ x<b+1 = (x≤b+1 et ¬(x=b+1)) ───────────────────────────────
    mono = _inf_egal_monotone_successeur(vx, vb)          # (x≤b) ⇒ (x≤b+1)
    n_sb_le_b = N.modus_ponens(h_fini, succ_pas_inf_egal(b))   # ¬(b+1 ≤ b)
    h_xle_b = N.assume(inf_egal_card(vx, vb))             # x ≤ b
    x_le_sb = N.modus_ponens(h_xle_b, mono)               # x ≤ b+1
    # ¬(x=b+1) : si x=b+1, Leibniz x↦b+1 dans (x≤b) ⇒ b+1≤b, contredit ¬(b+1≤b)
    h_eq2 = N.assume(egal(vx, sb))                        # x = b+1
    sb_le_b = N.modus_ponens(h_xle_b, equivalence_avant(N.modus_ponens(
        h_eq2, N.s6(vx, sb, "w", inf_egal_card(var("w"), vb)))))   # b+1 ≤ b
    contra = N.modus_ponens(sb_le_b, N.modus_ponens(n_sb_le_b,
        N.s2(non(inf_egal_card(sb, vb)), non(egal(vx, sb)))))   # ⊥ ⇒ ¬(x=b+1)
    n_eq = N.modus_ponens(N.loi_deduction(egal(vx, sb), contra),
                          N.s1(non(egal(vx, sb))))        # ¬(x=b+1)
    strict = conjonction_intro(x_le_sb, n_eq)            # x < b+1
    imp_le_strict = N.loi_deduction(inf_egal_card(vx, vb), strict)   # (x≤b) ⇒ (x<b+1)

    eq = conjonction_intro(imp_strict_le, imp_le_strict)  # (x<b+1) ⟺ (x≤b)
    res = N.loi_deduction(ante, eq)                      # (est_card(x) et est_fini(b)) ⇒ ((x<b+1)⟺(x≤b))
    assert res.conclusion == successeur_ordre_strict_enonce_fini(x, b), \
        "successeur_ordre_strict : conclusion ≠ enoncé attendu"
    return res


def successeur_ordre_t(x_term, b_term):
    """⊢ est_cardinal(X) ⇒ ( ( X ≤ B+1 ) ⟺ ( X ≤ B ou X = B+1 ) )  pour des TERMES.

    successeur_ordre (CLOS avec des NOMS « xso », « bso ») GÉNÉRALISÉ sur les deux
    puis INSTANCIÉ aux TERMES — capture-safe (les termes peuvent contenir des
    τ-cardinaux ou des variables liées en aval ; l'instanciation d'un théorème clos
    renomme déterministe sans collision)."""
    base = successeur_ordre("xso", "bso")                 # CLOS (noms)
    gen = N.generalisation("xso", N.generalisation("bso", base))
    return instancie(instancie(gen, _t(x_term)), _t(b_term))


__all__ = [
    "successeur_ordre_enonce", "successeur_ordre_reciproque", "successeur_ordre",
    "successeur_ordre_t",
    "succ_pas_inf_egal_enonce", "succ_pas_inf_egal",
    "successeur_ordre_strict_enonce_fini", "successeur_ordre_strict",
]
