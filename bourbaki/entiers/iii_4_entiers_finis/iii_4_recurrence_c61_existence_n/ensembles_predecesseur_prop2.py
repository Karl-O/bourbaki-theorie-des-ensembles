"""§III.5 — PROPOSITION 2 :  « tout entier (cardinal fini) m ≠ 0 est un successeur ».

🎯🎯🎯 LE DERNIER MAILLON AVANT ℕ — fermé INCONDITIONNELLEMENT.  Ce module CLÔT le
résidu honnête `predecesseur_fini_universel` (ensembles_principe_recurrence_preuve),
seul report de `N_collectivise_vrai` (ensembles_recurrence_vraie), et en déduit
`N_existe` ⊢ coll(x, Fini x) à 0 HYPOTHÈSE : ℕ EXISTE, INCONDITIONNEL.

    predecesseur_fini_universel() :=
        (∀m)( ( Fini m et ¬(m = 0) ) ⇒
              (∃k)( m = successeur(k)  et  est_cardinal(k)  et  k < m ) ).

────────────────────────────────────────────────────────────────────────────────
PREUVE (m cardinal fini ≠ 0 ; témoin k := Card(m∖{x0}) pour x0 ∈ m) :

  • Fini(m) ⇒ est_cardinal(m) (fini_implique_cardinal) ⇒ Card m = m (cardinal_de_cardinal).
  • m ≠ 0 = ∅ ⇒ m NON VIDE ⇒ (∃x0)(x0 ∈ m)  (non_vide_ssi_element).  Fixe x0.
  • D := m∖{x0}.  CŒUR (surgery « retrait + adjonction d'un point », eq_retire_ajoute) :
        x0 ∈ m  ⇒  Eq( m, D ⊔ {∅} ).
  • m = Card m = Card(D⊔{∅})            (Eq(m,D⊔{∅}) ⇒ Card =, _prop1_direct_t) ;
    successeur(Card D) = Card(Card D ⊔ {∅})  (successeur_egale_card_somme) ;
    Card(Card D ⊔ {∅}) = Card(D⊔{∅})      (Eq(Card D, D) ⇒ Card =, somme invariance) ;
    ⇒ m = successeur(Card D).  POSE k := Card D.
  • est_cardinal(k) = est_cardinal(Card D)  (card_est_un_cardinal, INCONDITIONNEL).
  • k < m :  k ≤ successeur(k) = m (_inf_egal_k_successeur) ; k ≠ m (sinon
    m = successeur(m) contredit Fini(m) = (… et m ≠ m+1)).

────────────────────────────────────────────────────────────────────────────────
LE CŒUR `eq_retire_ajoute` (CLOS, 0 hyp) :  m = D ∪ {x0} ({x0}⊂m, partie_reunion_
complement + commutativité) ; D ∩ {x0} = ∅ ; Eq(D∪{x0}, D⊔{x0}) (réunion disjointe ≃
somme, Prop. 10 §II.4 — `eq_reunion_disjointe_somme`, CLOS) ; Eq({x0},{∅})
(eq_singletons) + Eq(D,D) ⇒ Eq(D⊔{x0}, D⊔{∅}) (eq_somme_invariant) ; transitivité ⇒
Eq(m, D⊔{∅}).

  La bijectivité INCONDITIONNELLE du recollement canonique W (D∪{x0} → D⊔{x0}, sous
  disjonction) — le « dernier mille » jadis laissé à un round dédié — est désormais
  PROUVÉE (ensembles_reunion_somme_bijection.eq_reunion_somme, CLOS : les 4 conjoints
  de est_bijection_de assemblés depuis les copies marquées + l'infra recollement,
  toutes closes).  Plus AUCUN résidu.

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    contraposition, antecedent_consequent,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, equipotent, cardinal, inf_egal_card, inf_strict_card,
    est_bijection_de,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO

# ── briques CLOSES réutilisées ───────────────────────────────────────────────
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, card_est_un_cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_bornes import cardinal_inf_egal_successeur
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.cardinaux.arithmetique.ensembles_prop8_successeur import (
    successeur_egale_card_somme,
)
from bourbaki.cardinaux.arithmetique.ensembles_somme_equipotence import eq_somme_invariant
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_zero_plus_un import eq_singletons
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import partie_reunion_complement
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import commutativite_reunion

# énoncé EXACT à fermer
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    predecesseur_fini, predecesseur_fini_universel,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible (ex falso quodlibet)."""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P  ((P⇒¬P) = (¬P∨¬P) → ¬P par S1)."""
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _eq_sym_t(tx, ty):
    """⊢ Eq(X, Y) ⇒ Eq(Y, X)  pour des TERMES X, Y."""
    from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import _eq_sym_t as _s
    return _s(_t(tx), _t(ty))


def _eq_trans_t(tx, ty, tz):
    """⊢ (Eq(X,Y) et Eq(Y,Z)) ⇒ Eq(X,Z)  pour des TERMES X, Y, Z."""
    from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import _eq_trans_t as _tr
    return _tr(_t(tx), _t(ty), _t(tz))


def _comm_reunion_t(ta, tb):
    """⊢ (A∪B) = (B∪A)  pour des TERMES A, B (commutativité de ∪, version terme)."""
    gen = N.generalisation("ca", N.generalisation("cb", commutativite_reunion("ca", "cb")))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def _eq_son_cardinal(tX):
    """⊢ Eq(T, Card T)  pour un TERME T."""
    from bourbaki.cardinaux.ensembles_cardinaux_props_restantes import _eq_son_cardinal_t
    return _eq_son_cardinal_t(_t(tX))


def _eq_somme_invariant_t(ta, tb, ta1, tb1):
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Eq(A⊔B, A₁⊔B₁)  pour des TERMES A,B,A₁,B₁ QUELCONQUES.

    eq_somme_invariant (CLOS avec des NOMS) GÉNÉRALISÉ sur les 4 ensembles puis
    INSTANCIÉ aux termes — capture-safe même si les termes contiennent des τ-cardinaux
    imbriqués (sinon les liants internes du graphe-somme « k »/« t »/« x »/« y »
    collisionneraient avec les liants des τ, cf. _prop1_direct_t)."""
    inv = eq_somme_invariant("F", "G", "Asi", "Bsi", "A1si", "B1si")   # CLOS
    gen = N.generalisation("Asi", N.generalisation("Bsi",
              N.generalisation("A1si", N.generalisation("B1si", inv))))
    return instancie(instancie(instancie(instancie(gen, _t(ta)), _t(tb)),
                               _t(ta1)), _t(tb1))


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR — surgery « retrait + adjonction d'un point »  (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def _disjoint_diff_singleton(x, x0):
    """⊢ ( (X∖{x0}) ∩ {x0} ) = ∅.   (D et {x0} sont DISJOINTS, D := X∖{x0}.)

    partie_disjoint_complement(X, {x0}) ⊢ {x0} ∩ (X∖{x0}) = ∅ ; commutativité de ∩
    (version terme) réécrit en (X∖{x0}) ∩ {x0} = ∅."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import partie_disjoint_complement
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import commutativite_intersection
    vX, vx0 = _t(x), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vX, sing)                             # D = X∖{x0}
    pdc = partie_disjoint_complement(vX, sing)             # {x0} ∩ (X∖{x0}) = ∅
    gen = N.generalisation("ci", N.generalisation("cj", commutativite_intersection("ci", "cj")))
    comm = instancie(instancie(gen, D), sing)             # (D∩{x0}) = ({x0}∩D)
    return composer_egalites(comm, pdc)                   # (D∩{x0}) = ∅


def eq_reunion_disjointe_somme(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ Eq(A ∪ B, A ⊔ B).   (THÉORÈME CLOS, 0 hyp — Prop. 10 §II.4.)

    La réunion (disjointe) A∪B est équipotente à la somme A⊔B, pour A, B DISJOINTS.
    Réexporte le théorème CLOS `eq_reunion_somme` (ensembles_reunion_somme_bijection),
    où la bijectivité INCONDITIONNELLE du recollement canonique W (sous A∩B=∅) est
    PROUVÉE (les 4 conjoints assemblés depuis les copies marquées + l'infra recollement,
    toutes closes)."""
    from bourbaki.cardinaux.ensembles_reunion_somme_bijection import eq_reunion_somme
    return eq_reunion_somme(_t(a), _t(b))                  # (A∩B=∅) ⇒ Eq(A∪B, A⊔B)  CLOS


def singleton_inclus(x0, e):
    """⊢ (x0 ∈ E) ⇒ ( {x0} ⊂ E ).   ( {x0} = {z | z = x0} ⊂ E sous x0∈E.)

    z∈{x0} ⇔ z=x0 (singleton_membre) ; sous z=x0, Leibniz x0↦z dans x0∈E donne z∈E."""
    vx0, vE = _t(x0), _t(e)
    sing = E.singleton(vx0)
    vz = var("z")
    h_x0 = N.assume(appartient(vx0, vE))                   # x0 ∈ E
    hz = N.assume(appartient(vz, sing))                    # z ∈ {x0}
    z_eq = N.modus_ponens(hz, equivalence_avant(singleton_membre(vz, vx0)))  # z = x0
    x0_eq_z = N.modus_ponens(z_eq, symetrie(vz, vx0))      # x0 = z
    z_in_E = N.modus_ponens(h_x0, equivalence_avant(N.modus_ponens(
        x0_eq_z, N.s6(vx0, vz, "w", appartient(var("w"), vE)))))  # z ∈ E
    body = N.loi_deduction(appartient(vz, sing), z_in_E)   # z∈{x0} ⇒ z∈E
    sub = N.generalisation("z", body)                      # {x0} ⊂ E
    return N.loi_deduction(appartient(vx0, vE), sub)       # (x0∈E) ⇒ {x0}⊂E


def eq_retire_ajoute(x, x0):
    """⊢ ( x0 ∈ X ) ⇒ Eq( X, (X∖{x0}) ⊔ {∅} ).   (THÉORÈME CLOS, 0 hyp.)

    🎯 LE CŒUR de la Proposition 2 : retirer le point x0 de X puis ré-adjoindre la
    marque {∅} redonne un ensemble équipotent à X.  Sous x0∈X :
      • {x0} ⊂ X (singleton_inclus) ⇒ {x0}∪D = X (partie_reunion_complement, D=X∖{x0}) ;
        commutativité ⇒ D∪{x0} = X, d'où X = D∪{x0} ;
      • D ∩ {x0} = ∅ (_disjoint_diff_singleton) ;
      • Eq(D∪{x0}, D⊔{x0})  (eq_reunion_disjointe_somme sous D∩{x0}=∅, CLOS — Prop. 10 §II.4) ;
      • réécriture D∪{x0}↦X (Leibniz) ⇒ Eq(X, D⊔{x0}) ;
      • Eq(D,D) (réflexivité) et Eq({x0},{∅}) (eq_singletons) ⇒ Eq(D⊔{x0}, D⊔{∅})
        (eq_somme_invariant) ;
      • transitivité ⇒ Eq(X, D⊔{∅}).
    INCONDITIONNEL (aucune hypothèse résiduelle)."""
    vX, vx0 = _t(x), _t(x0)
    sing = E.singleton(vx0)                                # {x0}
    D = E.difference(vX, sing)                             # D = X∖{x0}
    sing_vide = E.singleton(E.VIDE)                        # {∅}
    DsX0 = somme_disjointe(D, sing)                        # D ⊔ {x0}
    DsVide = somme_disjointe(D, sing_vide)                 # D ⊔ {∅}
    Dux0 = E.reunion(D, sing)                              # D ∪ {x0}

    h_x0 = N.assume(appartient(vx0, vX))                   # x0 ∈ X

    # ── X = D ∪ {x0} ──────────────────────────────────────────────────────────
    sub = N.modus_ponens(h_x0, singleton_inclus(vx0, vX))  # {x0} ⊂ X
    # partie_reunion_complement(X, {x0}) : ({x0}⊂X) ⇒ ({x0}∪(X∖{x0}) = X)
    prc = partie_reunion_complement(vX, sing)              # ({x0}⊂X) ⇒ ({x0}∪D = X)
    x0uD_eq_X = N.modus_ponens(sub, prc)                   # {x0}∪D = X
    comm = _comm_reunion_t(D, sing)                        # D∪{x0} = {x0}∪D
    Dux0_eq_X = composer_egalites(comm, x0uD_eq_X)         # D∪{x0} = X

    # ── Eq(D∪{x0}, D⊔{x0})  (CLOS, Prop. 10 §II.4), via D∩{x0}=∅ ────────────────
    disj = _disjoint_diff_singleton(vX, vx0)               # (D∩{x0}) = ∅
    eq_union_somme = N.modus_ponens(disj, eq_reunion_disjointe_somme(D, sing))  # Eq(D∪{x0}, D⊔{x0})
    # réécrire D∪{x0} ↦ X  ⇒  Eq(X, D⊔{x0})
    eq_X_somme = N.modus_ponens(eq_union_somme, equivalence_avant(N.modus_ponens(
        Dux0_eq_X, N.s6(Dux0, vX, "w", equipotent(var("w"), DsX0)))))  # Eq(X, D⊔{x0})

    # ── Eq(D⊔{x0}, D⊔{∅}) via eq_somme_invariant(Eq(D,D), Eq({x0},{∅})) ────────
    eq_DD = instancie(N.generalisation("X", equipotence_reflexive("X")), D)  # Eq(D, D)
    eq_sing = eq_singletons(vx0, E.VIDE)                   # Eq({x0}, {∅})
    inv = _eq_somme_invariant_t(D, sing, D, sing_vide)    # (Eq(D,D)et Eq({x0},{∅}))⇒Eq(D⊔{x0},D⊔{∅})
    eq_somme_somme = N.modus_ponens(conjonction_intro(eq_DD, eq_sing), inv)  # Eq(D⊔{x0}, D⊔{∅})

    # ── transitivité ⇒ Eq(X, D⊔{∅}) ───────────────────────────────────────────
    trans = _eq_trans_t(vX, DsX0, DsVide)                  # (Eq(X,D⊔{x0})et Eq(D⊔{x0},D⊔{∅}))⇒Eq(X,D⊔{∅})
    eq_X_DsVide = N.modus_ponens(conjonction_intro(eq_X_somme, eq_somme_somme), trans)  # Eq(X, D⊔{∅})
    assert eq_X_DsVide.conclusion == equipotent(vX, DsVide), \
        "eq_retire_ajoute : conclusion ≠ Eq(X, D⊔{∅})"
    return N.loi_deduction(appartient(vx0, vX), eq_X_DsVide)  # (x0∈X) ⇒ Eq(X, D⊔{∅})  CLOS


# ════════════════════════════════════════════════════════════════════════════
#  ÉGALITÉ NOYAU :  m = successeur( Card(m∖{x0}) )   sous { Fini m, x0 ∈ m }
# ════════════════════════════════════════════════════════════════════════════
def m_egal_successeur_card_diff(m, x0):
    """⊢ ( est_cardinal(m)  et  x0 ∈ m )  ⇒  ( m = successeur( Card(m∖{x0}) ) ).
       (THÉORÈME CLOS, 0 hyp.)

    Sous est_cardinal(m) et x0∈m, avec D := m∖{x0} :
      • Card m = m            (cardinal_de_cardinal) ;
      • Eq(m, D⊔{∅})          (eq_retire_ajoute) ⇒ Card m = Card(D⊔{∅})  (_prop1_direct_t) ;
      • successeur(Card D) = Card(Card D ⊔ {∅})  (successeur_egale_card_somme) ;
      • Eq(Card D, D) (réflexion équipotent_son_cardinal) ⇒ Card(Card D ⊔ {∅}) = Card(D⊔{∅})
        (eq_somme_invariant + _prop1_direct_t) ;
      • composition des égalités ⇒ m = Card m = Card(D⊔{∅}) = Card(Card D ⊔ {∅}) = successeur(Card D)."""
    vm, vx0 = _t(m), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vm, sing)                             # D = m∖{x0}
    cD = cardinal(D)                                       # Card D = k
    sing_vide = E.singleton(E.VIDE)                        # {∅}
    DsVide = somme_disjointe(D, sing_vide)                 # D ⊔ {∅}
    cDsVide = cardinal(DsVide)                             # Card(D⊔{∅})
    cDsVide_card = somme_disjointe(cD, sing_vide)          # Card D ⊔ {∅}

    ante = et(est_cardinal(vm), appartient(vx0, vm))
    h = N.assume(ante)
    h_card_m = conjonction_elim_gauche(h)                  # est_cardinal(m)
    h_x0 = conjonction_elim_droite(h)                      # x0 ∈ m

    # Card m = m
    card_m_eq_m = N.modus_ponens(h_card_m, cardinal_de_cardinal(vm))   # Card m = m
    m_eq_card_m = N.modus_ponens(card_m_eq_m, symetrie(cardinal(vm), vm))  # m = Card m

    # Eq(m, D⊔{∅}) ⇒ Card m = Card(D⊔{∅})
    eq_m_DsVide = N.modus_ponens(h_x0, eq_retire_ajoute(vm, vx0))   # Eq(m, D⊔{∅})  CLOS
    card_eq = N.modus_ponens(eq_m_DsVide, _prop1_direct_t(vm, DsVide))  # Card m = Card(D⊔{∅})

    # successeur(Card D) = Card(Card D ⊔ {∅})
    succ_eq = successeur_egale_card_somme(cD)              # successeur(Card D) = Card(Card D ⊔ {∅})

    # Card(Card D ⊔ {∅}) = Card(D⊔{∅})  via Eq(Card D, D) (eq_somme_invariant + prop1)
    eq_cardD_D = _eq_sym_t(D, cD)                          # Eq(D, Card D) ⇒ Eq(Card D, D)
    eq_cardD_D = N.modus_ponens(_eq_son_cardinal(D), eq_cardD_D)   # Eq(Card D, D)
    eq_vide = instancie(N.generalisation("X", equipotence_reflexive("X")), sing_vide)  # Eq({∅},{∅})
    inv = _eq_somme_invariant_t(cD, sing_vide, D, sing_vide)  # (Eq(CardD,D)et Eq({∅},{∅}))⇒Eq(CardD⊔{∅},D⊔{∅})
    eq_sommes = N.modus_ponens(conjonction_intro(eq_cardD_D, eq_vide), inv)  # Eq(Card D⊔{∅}, D⊔{∅})
    card_sommes_eq = N.modus_ponens(eq_sommes, _prop1_direct_t(cDsVide_card, DsVide))  # Card(CardD⊔{∅})=Card(D⊔{∅})

    # m = Card m = Card(D⊔{∅}) = Card(Card D ⊔ {∅}) = successeur(Card D)
    # chaîne : m = Card m  [m_eq_card_m]
    #            = Card(D⊔{∅})  [card_eq]
    chain1 = composer_egalites(m_eq_card_m, card_eq)       # m = Card(D⊔{∅})
    # Card(D⊔{∅}) = Card(Card D ⊔ {∅})  (symétrie de card_sommes_eq)
    card_DsVide_eq = N.modus_ponens(card_sommes_eq, symetrie(cardinal(cDsVide_card), cDsVide))  # Card(D⊔{∅}) = Card(CardD⊔{∅})
    chain2 = composer_egalites(chain1, card_DsVide_eq)     # m = Card(Card D ⊔ {∅})
    # Card(Card D ⊔ {∅}) = successeur(Card D)  (symétrie de succ_eq)
    card_card_eq_succ = N.modus_ponens(succ_eq, symetrie(successeur(cD), cardinal(cDsVide_card)))  # Card(CardD⊔{∅}) = succ(CardD)
    m_eq_succ = composer_egalites(chain2, card_card_eq_succ)  # m = successeur(Card D)
    assert m_eq_succ.conclusion == egal(vm, successeur(cD)), \
        "m_egal_successeur_card_diff : conclusion ≠ (m = successeur(Card D))"
    return N.loi_deduction(ante, m_eq_succ)                # (est_cardinal(m) et x0∈m) ⇒ m = successeur(Card D)


# ════════════════════════════════════════════════════════════════════════════
#  k < m   (k := Card D = Card(m∖{x0})), depuis  m = successeur(k)  et  Fini m.
# ════════════════════════════════════════════════════════════════════════════
def _inf_egal_k_successeur(k_term):
    """⊢ k ≤ successeur(k)  pour un TERME k (= Card(k⊔{∅})).

    Patron de un_inf_egal_deux : inf_egal_successeur(k) ⇒ k ≤ k⊔{∅} [SET] ;
    Eq(k⊔{∅}, Card(k⊔{∅})) (equipotent_son_cardinal) ⇒ (k⊔{∅}) ≤ Card(k⊔{∅})
    (equipotence_implique_inf_egal) ; transitivité ⇒ k ≤ Card(k⊔{∅}) = successeur(k)."""
    from bourbaki.cardinaux.ensembles_cardinaux_bornes import inf_egal_successeur
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
    from bourbaki.cardinaux.ensembles_cardinaux_ordre import (
        equipotence_implique_inf_egal, inf_egal_transitive,
    )
    vk = _t(k_term)
    Sk = somme_disjointe(vk, E.singleton(E.VIDE))          # k ⊔ {∅}
    cardSk = cardinal(Sk)                                  # Card(k⊔{∅}) = successeur(k)
    le1 = instancie(N.generalisation("A", inf_egal_successeur("A")), vk)   # k ≤ k⊔{∅}
    eqSk = instancie(N.generalisation("X", equipotent_son_cardinal("X")), Sk)  # Eq(k⊔{∅}, Card(k⊔{∅}))
    imp = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y"))), Sk), cardSk)      # Eq(k⊔{∅},Card(k⊔{∅})) ⇒ ≤
    le2 = N.modus_ponens(eqSk, imp)                        # (k⊔{∅}) ≤ Card(k⊔{∅})
    trans = instancie(instancie(instancie(N.generalisation("X", N.generalisation("Y",
        N.generalisation("Z", inf_egal_transitive("F", "G", "X", "Y", "Z")))),
        vk), Sk), cardSk)                                  # (k≤k⊔{∅} et k⊔{∅}≤Card(k⊔{∅})) ⇒ k≤Card(k⊔{∅})
    return N.modus_ponens(conjonction_intro(le1, le2), trans)   # k ≤ Card(k⊔{∅}) = successeur(k)


def _k_inf_strict_m(m, k_term):
    """⊢ ( est_fini(m)  et  est_cardinal(k)  et  ( m = successeur(k) ) )  ⇒  ( k < m ).

    k < m := (k ≤ m et k ≠ m).
      • k ≤ m :  k ≤ successeur(k) (_inf_egal_k_successeur) ; réécriture successeur(k)↦m
        (m = successeur(k)) ⇒ k ≤ m.
      • k ≠ m :  si k = m alors m = successeur(k) = successeur(m), or Fini(m) =
        (est_cardinal(m) et ¬(m = successeur(m))) ⇒ contradiction."""
    vm, vk = _t(m), _t(k_term)
    succ_k = successeur(vk)

    ante = et(et(est_fini(vm), est_cardinal(vk)), egal(vm, succ_k))
    h = N.assume(ante)
    h_fini_m = conjonction_elim_gauche(conjonction_elim_gauche(h))   # Fini m
    h_card_k = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(k)
    h_m_eq_succ = conjonction_elim_droite(h)                         # m = successeur(k)

    # ── k ≤ m ──────────────────────────────────────────────────────────────────
    le_k_succ = _inf_egal_k_successeur(vk)                 # k ≤ successeur(k)
    # réécrire successeur(k) ↦ m via m = successeur(k) (symétrie)
    succ_eq_m = N.modus_ponens(h_m_eq_succ, symetrie(vm, succ_k))   # successeur(k) = m
    le_k_m = N.modus_ponens(le_k_succ, equivalence_avant(N.modus_ponens(
        succ_eq_m, N.s6(succ_k, vm, "w", inf_egal_card(vk, var("w"))))))  # k ≤ m

    # ── k ≠ m :  si k = m, m = successeur(k) = successeur(m), contredit Fini(m) ──
    n_m_eq_succ_m = conjonction_elim_droite(h_fini_m)      # ¬(m = successeur(m))
    h_k_eq_m = N.assume(egal(vk, vm))                      # k = m  (réfutation)
    # successeur(k) = successeur(m)  (congruence)
    succ_k_eq_succ_m = N.modus_ponens(h_k_eq_m, congruence_terme(vk, vm, successeur(var("w")), "w"))
    # m = successeur(k) = successeur(m)
    m_eq_succ_m = composer_egalites(h_m_eq_succ, succ_k_eq_succ_m)   # m = successeur(m)
    contra = _ex_falso(m_eq_succ_m, n_m_eq_succ_m, non(egal(vk, vm)))  # ¬(k = m)
    k_ne_m = _refute_self(N.loi_deduction(egal(vk, vm), contra))    # ¬(k = m)

    strict = conjonction_intro(le_k_m, k_ne_m)             # k ≤ m et k ≠ m = k < m
    assert strict.conclusion == inf_strict_card(vk, vm), \
        "_k_inf_strict_m : conclusion ≠ (k < m)"
    return N.loi_deduction(ante, strict)                   # (Fini m et card k et m=succ k) ⇒ k < m


def _k_inf_strict_m_t(m_term, k_term):
    """⊢ ( Fini m et est_cardinal(k) et m=successeur(k) ) ⇒ ( k < m )  pour des TERMES.

    _k_inf_strict_m (CLOS avec des NOMS « mks », « kks ») GÉNÉRALISÉ puis INSTANCIÉ aux
    TERMES — capture-safe (k=Card(m∖{x0}) contient des τ-cardinaux ; l'instanciation
    dans le théorème déjà clos renomme déterministe sans collision)."""
    base = _k_inf_strict_m("mks", "kks")                   # CLOS (noms)
    gen = N.generalisation("mks", N.generalisation("kks", base))
    return instancie(instancie(gen, _t(m_term)), _t(k_term))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PROPOSITION 2 (E.III.5) — predecesseur_fini_universel
# ════════════════════════════════════════════════════════════════════════════
def predecesseur_fini_universel_preuve(m="mpred", k="kpred", x0="x0pred"):
    """🎯🎯 ⊢ predecesseur_fini_universel().   (THÉORÈME CLOS, 0 hyp.)

    La PROPOSITION 2 §III.5 « tout entier ≠ 0 est un successeur », INCONDITIONNELLE.
    Conclusion ÉGALE LITTÉRALEMENT predecesseur_fini_universel(k='kpred').

    Sous Fini(m) et m≠0 :  Fini(m) ⇒ est_cardinal(m) ; m≠∅ ⇒ (∃x0)(x0∈m), témoin x0 ;
    k := Card(m∖{x0}) ; m = successeur(k) (m_egal_successeur_card_diff) ;
    est_cardinal(k) (card_est_un_cardinal) ; k < m (_k_inf_strict_m_t) ; ∃-introduction
    du témoin k ; généralisation sur m et décharge de l'antécédent.  theorie=22."""
    vm = var(m)
    sing0 = E.singleton(var(x0))                           # {x0}
    D = E.difference(vm, sing0)                            # D = m∖{x0}
    cD = cardinal(D)                                       # k := Card D

    # ── on assume ( Fini m et m≠0 ) ────────────────────────────────────────────
    ante = et(est_fini(vm), non(egal(vm, ZERO)))
    h = N.assume(ante)
    h_fini = conjonction_elim_gauche(h)                    # Fini m
    h_ne0 = conjonction_elim_droite(h)                     # ¬(m = 0)
    card_m = N.modus_ponens(h_fini, fini_implique_cardinal(vm))   # est_cardinal(m)

    # ── m ≠ 0 = ∅ ⇒ (∃x0)(x0 ∈ m) ──────────────────────────────────────────────
    # ZERO = Card(∅) ; m ≠ 0.  Pour appliquer non_vide_ssi_element il faut ¬(m = ∅).
    # Or 0 = ZERO = Card(∅), et m est un cardinal donc m=∅ ⇒ m=0 (Card∅=∅... non) :
    # on relie m=∅ et m=0 par : 0 = Card(∅) et Card(∅) = ∅ (cardinal_vide_egale_vide)
    # ⇒ 0 = ∅.  Donc ¬(m=0) ⇒ ¬(m=∅) (Leibniz 0=∅).
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    card_vide_eq_vide = cardinal_vide_egale_vide()         # Card(∅) = ∅
    # 0 = ZERO = Card(∅) (def ZERO = CARD_VIDE = Card(∅)) ; ZERO == cardinal(VIDE) littéralement
    zero_eq_vide = card_vide_eq_vide                       # ZERO = ∅   (ZERO = Card(∅) littéral)
    assert zero_eq_vide.conclusion == egal(ZERO, E.VIDE), "ZERO = Card(∅) ; attendu ZERO = ∅"
    # ¬(m=0) ⇒ ¬(m=∅) :  contraposée de (m=∅) ⇒ (m=0) (Leibniz ∅↦0 via 0=∅ symétrisé)
    vide_eq_zero = N.modus_ponens(zero_eq_vide, symetrie(ZERO, E.VIDE))  # ∅ = 0
    # On construit (m=∅) ⇒ (m=0) directement (Leibniz ∅↦0).
    h_m_eq_vide = N.assume(egal(vm, E.VIDE))               # m = ∅
    m_eq_zero = N.modus_ponens(h_m_eq_vide, equivalence_avant(N.modus_ponens(
        vide_eq_zero, N.s6(E.VIDE, ZERO, "w", egal(vm, var("w"))))))   # m = 0
    imp_vide_zero = N.loi_deduction(egal(vm, E.VIDE), m_eq_zero)       # (m=∅) ⇒ (m=0)
    m_ne_vide = N.modus_ponens(h_ne0, contraposition(imp_vide_zero))   # ¬(m = ∅)
    ex_x0 = N.modus_ponens(m_ne_vide, equivalence_avant(non_vide_ssi_element(vm)))  # (∃z)(z∈m)

    # ── corps (sous le témoin x0 ∈ m) : (∃k)(m=succ k et card k et k<m) ─────────
    vx0 = var(x0)
    h_x0_in_m = N.assume(appartient(vx0, vm))              # x0 ∈ m

    # m = successeur(Card D)
    m_eq_succ = N.modus_ponens(conjonction_intro(card_m, h_x0_in_m),
                               m_egal_successeur_card_diff(vm, vx0))   # m = successeur(Card D)
    # est_cardinal(Card D) — on ALIGNE le liant interne sur celui de est_cardinal (« X »),
    # forme attendue par predecesseur_fini et _k_inf_strict_m_t (card_est_un_cardinal
    # utilise « X' » par défaut).
    card_cD = card_est_un_cardinal(D, lieur=est_cardinal(cD).lieur)   # est_cardinal(Card D)
    assert card_cD.conclusion == est_cardinal(cD), "est_cardinal(Card D) : liant non aligné"
    # k < m
    strict = N.modus_ponens(
        conjonction_intro(conjonction_intro(h_fini, card_cD), m_eq_succ),
        _k_inf_strict_m_t(vm, cD))                         # Card D < m

    # corps de predecesseur_fini(m, k=kpred) avec témoin k := Card D
    corps_k = et(et(egal(vm, successeur(cD)), est_cardinal(cD)), inf_strict_card(cD, vm))
    corps_thm = conjonction_intro(conjonction_intro(m_eq_succ, card_cD), strict)
    assert corps_thm.conclusion == corps_k, "corps de predecesseur_fini mal formé"

    # ∃-introduction du témoin Card D dans (∃kpred)( m=succ kpred et card kpred et kpred<m )
    cible_pred = predecesseur_fini(vm, k)                  # (∃kpred)( … )
    ex_k = N.modus_ponens(corps_thm, N.s5(cible_pred.sous[0], cD, k))   # (∃kpred)( … )
    assert ex_k.conclusion == cible_pred, "∃-intro du témoin Card D ne donne pas predecesseur_fini(m)"

    # ── décharge PROPRE du témoin x0 (x0 NON libre dans la conclusion ni dans les
    #    hypothèses ouvertes : ante sans x0, et le CŒUR eq_retire_ajoute est CLOS) ──
    imp_x0 = N.loi_deduction(appartient(vx0, vm), ex_k)    # (x0∈m) ⇒ predecesseur_fini(m)
    ex_imp = existe_elimination(imp_x0, x0)                # (∃x0)(x0∈m) ⇒ predecesseur_fini(m)
    # ex_x0 lie « z » : on l'α-renomme « z »→x0 pour l'apparier à ex_imp.
    ex_x0_renomme = N.modus_ponens(ex_x0,
        equivalence_avant(alpha_existe("z", x0, appartient(var("z"), vm))))  # (∃x0)(x0∈m)
    pred_m = N.modus_ponens(ex_x0_renomme, ex_imp)         # predecesseur_fini(m)  [ante]
    assert pred_m.conclusion == predecesseur_fini(vm, k), \
        "predecesseur_fini(m) mal formé après élimination du témoin"

    # ── (Fini m et m≠0) ⇒ predecesseur_fini(m), généralisation sur m ────────────
    corps_concl = N.loi_deduction(ante, pred_m)            # (Fini m et m≠0) ⇒ predecesseur_fini(m)  CLOS
    res = N.generalisation(m, corps_concl)                 # (∀m)( … )
    assert res.conclusion == predecesseur_fini_universel(k=k), \
        "conclusion ≠ predecesseur_fini_universel(k='kpred')"
    return res                                             # CLOS, 0 hyp


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 ℕ EXISTE — N_collectivise_vrai DÉCHARGÉ de predecesseur_fini_universel
# ════════════════════════════════════════════════════════════════════════════
def N_existe(a="a", x="x", c="c", b="b", Y="y", k="kpred"):
    """🎯🎯🎯 ⊢ coll(x, Fini x).   (THÉORÈME CLOS, 0 hyp — ℕ EXISTE, INCONDITIONNEL.)

    L'ensemble ℕ des entiers naturels EXISTE (Théorème 1, E.III.6.1), SANS AUCUNE
    hypothèse.  `N_collectivise_vrai` (ensembles_recurrence_vraie) conclut coll(x,Fini x)
    sous le SEUL résidu `predecesseur_fini_universel` (Prop. 2 §III.5) ; ce module ferme
    Prop. 2 INCONDITIONNELLEMENT (predecesseur_fini_universel_preuve, CLOS).  On DÉCHARGE
    donc predecesseur_fini_universel par notre preuve close ⇒ coll(x, Fini x) à 0 hyp.
    theorie=22, rien postulé."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import N_collectivise_vrai
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import _coll_fini
    ncv = N_collectivise_vrai(a, x, c, b, Y)               # coll(x,Fini x)  [predecesseur_fini_universel]
    pfu = predecesseur_fini_universel(k=k)                 # le résidu de N_collectivise_vrai
    assert pfu in ncv.hypotheses, \
        "predecesseur_fini_universel absent des hypothèses de N_collectivise_vrai (forme ?)"
    preuve_pfu = predecesseur_fini_universel_preuve(k=k)   # ⊢ pfu  (CLOS, 0 hyp)
    assert preuve_pfu.conclusion == pfu, \
        "predecesseur_fini_universel_preuve ne conclut pas le résidu attendu"
    res = _cut(ncv, pfu, preuve_pfu)                       # coll(x,Fini x)  (CLOS, 0 hyp)
    assert res.conclusion == _coll_fini(x), "N_existe : conclusion ≠ coll(x, Fini x)"
    return res


__all__ = [
    "eq_reunion_disjointe_somme", "singleton_inclus", "eq_retire_ajoute",
    "m_egal_successeur_card_diff", "_k_inf_strict_m", "_k_inf_strict_m_t",
    "predecesseur_fini_universel_preuve",
    "N_existe",
]
