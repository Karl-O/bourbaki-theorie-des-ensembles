"""§III.3 — CONSÉQUENCES de l'ordre des cardinaux : ordre strict, Cantor, bornes.

Module NEUF (campagne III.3/III.5, salvage).  Il ASSEMBLE, à partir de théorèmes
DÉJÀ CLOS (rien postulé, theorie_ensembles() = 22), les conséquences directes de :
  • la TOTALITÉ de l'ordre ≤ des cardinaux  (comparabilite_cardinaux, via Zorn) ;
  • CANTOR  Card X < Card P(X)  (cantor_strict) ;
  • la STRUCTURE D'ORDRE de ≤  (réflexif/transitif, antisymétrie sur cardinaux =
    Cantor–Bernstein + Prop. 1).

──────────────────────────────────────────────────────────────────────────────
THÉORÈMES INCONDITIONNELS (clos, 0 hypothèse) :

  (A) `strict_implique_inf_egal`  ⊢ (a < b) ⇒ (a ≤ b).
      x < y := (x ≤ y et x ≠ y) [inf_strict_card, VERBATIM] ; projection gauche.
      C'est «  < ⊆ ≤  » de Bourbaki (l'ordre strict raffine l'ordre large).

  (B) `strict_irreflexif`  ⊢ ¬(a < a).
      a < a := (a ≤ a et a ≠ a) ; le 2ᵉ conjoint a ≠ a est contradictoire
      (réflexivité de =).  Un ordre strict est irréflexif.

  (C) `aucun_plus_grand_cardinal`  ⊢ (∀X)(∃Y)(X < Y).
      COROLLAIRE DE CANTOR : pour tout X, Card X < Card P(X) (cantor_strict),
      donc Y := P(X) témoigne X < Y.  Il N'Y A PAS DE PLUS GRAND CARDINAL.

  (D) `inf_egal_strict_compose`  ⊢ (a ≤ b et b < c) ⇒ (a < c).      [voir garde]
      `strict_inf_egal_compose`  ⊢ (a < b et b ≤ c) ⇒ (a < c).      [voir garde]
      `strict_transitive`        ⊢ (a < b et b < c) ⇒ (a < c).      [voir garde]
      ─ TRANSITIVITÉ de l'ordre STRICT (et ses formes mixtes ≤/<).  Le maillon « ≤ »
      vient de inf_egal_transitive (composée d'injections) ; la STRICTITÉ (a ≠ c)
      exige l'ANTISYMÉTRIE de ≤, qui sur des cardinaux donne l'ÉGALITÉ (Cantor–
      Bernstein + Prop. 1) — d'où la GARDE « a, b, c cardinaux » (fidèle : la
      relation R{x,y} du Théorème 1 est elle-même gardée par « x, y cardinaux »).

──────────────────────────────────────────────────────────────────────────────
THÉORÈMES CONDITIONNELS (hypothèse explicite = injection de support, verrou dur
reporté — même verrou que exposant_monotone, cf. ce module) :

  (E) `un_inf_egal_exposant_conditionnel`  ⊢ (1 ≤ 𝓕(b;a)) ⇒ (1 ≤ a^b).
      `base_inf_egal_exposant_conditionnel` ⊢ (a ≤ 𝓕(b;a)) ⇒ (a ≤ a^b).
      a^b = Card(𝓕(b;a)) ; l'inégalité au niveau des SUPPORTS (ensemble des
      applications) se transporte au niveau des CARDINAUX par
      inf_egal_transporte_cardinal (le PONT, contenu réel).  La DÉCHARGE des
      hypothèses (construction des injections 1 ↪ 𝓕(b;a) et a ↪ 𝓕(b;a) quand
      b ≠ 0) est le verrou dur reporté (machinerie « valeur d'application »).

Tout est CERTIFIÉ par le noyau.  Aucun axiome nouveau.  theorie_ensembles() = 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, ou, non, impl, existe)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    affaiblissement, instancie, equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import cantor_strict
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


def _inf_egal_transitive_t(tA, tB, tC):
    """⊢ (A≤B et B≤C) ⇒ A≤C  pour des TERMES A, B, C (transitivité de ≤, instance-terme)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(gen, _t(tA)), _t(tB)), _t(tC))


def _antisym_t(tA, tB):
    """⊢ (A≤B et B≤A et est_cardinal(A) et est_cardinal(B)) ⇒ A=B  pour TERMES A, B.

    inf_egal_antisymetrique_card est (∀a∀b)(... ⇒ a=b) ; on l'instancie aux termes."""
    gen = inf_egal_antisymetrique_card("a", "b")   # déjà (∀a∀b)(...)
    return instancie(instancie(gen, _t(tA)), _t(tB))


# ══════════════════════════════════════════════════════════════════════════════
#  (A)  a < b ⇒ a ≤ b     (l'ordre strict raffine l'ordre large)
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Rem.- | E III.25 L.4-6 | PDF p.128
#   (ordre strict x < y := (x ≤ y et x ≠ y) dérivé de la relation ≤ notée ici ;
#    propriété « < ⊆ ≤ » implicite dans le livre, infra d'assemblage.)
def strict_implique_inf_egal(a="a", b="b"):
    """⊢ (a < b) ⇒ (a ≤ b).   (E.III.3.2 : « < ⊆ ≤ », l'ordre strict raffine ≤.)

    a < b := (a ≤ b et a ≠ b) [inf_strict_card, VERBATIM] ; le sens ⇒ est la simple
    PROJECTION GAUCHE de la conjonction.  INCONDITIONNEL."""
    vA, vB = _t(a), _t(b)
    h = N.assume(inf_strict_card(vA, vB))          # a < b
    le = conjonction_elim_gauche(h)                # a ≤ b
    return N.loi_deduction(inf_strict_card(vA, vB), le)


# ══════════════════════════════════════════════════════════════════════════════
#  (B)  ¬(a < a)     (irréflexivité de l'ordre strict)
# ══════════════════════════════════════════════════════════════════════════════
def strict_irreflexif(a="a"):
    """⊢ ¬(a < a).   (E.III.3.2 : l'ordre strict des cardinaux est IRRÉFLEXIF.)

    a < a := (a ≤ a et a ≠ a).  Sous a < a on extrait a ≠ a (= ¬(a=a)), contredit
    par la RÉFLEXIVITÉ de l'égalité (a = a) ; ex falso donne ¬(a < a) [sous a < a],
    puis idempotence (S1) décharge.  INCONDITIONNEL."""
    vA = _t(a)
    strict = inf_strict_card(vA, vA)               # a < a = (a≤a et a≠a)
    h = N.assume(strict)
    ne = conjonction_elim_droite(h)                # ¬(a = a)
    refl = N.reflexivite(vA)                        # a = a
    contra = _ex_falso(refl, ne, non(strict))      # ¬(a<a)   [sous a<a]
    imp = N.loi_deduction(strict, contra)          # (a<a) ⇒ ¬(a<a)
    return N.modus_ponens(imp, N.s1(non(strict)))  # ¬(a<a)


# ══════════════════════════════════════════════════════════════════════════════
#  (C)  PAS DE PLUS GRAND CARDINAL   (corollaire de Cantor)
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.6 Th.2 | E III.30 L.22-22 | PDF p.133
#   (conséquence directe du Théorème 2 (Cantor) 2^a > a : témoin Y := P(X) ;
#    le corollaire du livre L.29-33 « pas d'ensemble de tous les cardinaux »
#    n'est PAS encore formalisé — cf. non_formalises campagne @livre.)
def cantor_strict_existe(x="X"):
    """⊢ (∃Y)(X < Y).   (corollaire de CANTOR : il existe un cardinal STRICTEMENT
    plus grand que Card X — témoin Y := P(X).)

    cantor_strict(X) ⊢ X < P(X) = inf_strict_card(X, P(X)) ; S5 (témoin P(X))
    introduit (∃Y)(X < Y).  INCONDITIONNEL."""
    vX = _t(x)
    PX = E.parties(vX)
    strict = cantor_strict(x)                       # X < P(X)
    # (∃Y)(X < Y)   via S5, témoin Y := P(X)
    cible = existe("Y", inf_strict_card(vX, var("Y")))
    return N.modus_ponens(strict, N.s5(inf_strict_card(vX, var("Y")), PX, "Y"))


def aucun_plus_grand_cardinal(x="X"):
    """⊢ (∀X)(∃Y)(X < Y).   (E.III.3 : IL N'Y A PAS DE PLUS GRAND CARDINAL.)

    Pour tout X, P(X) est strictement plus grand (Cantor) : cantor_strict_existe
    donne (∃Y)(X<Y) ; clôture universelle en X.  INCONDITIONNEL.  C'est la forme
    « aucun cardinal n'est maximal » du théorème de Cantor."""
    return N.generalisation(x, cantor_strict_existe(x))


# ══════════════════════════════════════════════════════════════════════════════
#  (D)  TRANSITIVITÉ de l'ordre strict (gardée par « cardinaux ») et formes mixtes
# ══════════════════════════════════════════════════════════════════════════════
#  Sur des cardinaux, l'antisymétrie de ≤ donne l'ÉGALITÉ (Cantor–Bernstein +
#  Prop. 1).  C'est nécessaire pour la STRICTITÉ (a ≠ c) : la garde reproduit
#  exactement celle de la relation R du Théorème 1.
# ══════════════════════════════════════════════════════════════════════════════
def inf_egal_strict_compose(a="a", b="b", c="c"):
    """⊢ (a≤b et b<c et a,b,c cardinaux) ⇒ (a<c).   (≤ puis < donne <.)

    a≤b et b≤c (de b<c) ⇒ a≤c (transitivité).  STRICTITÉ a≠c : si a=c, alors c≤b
    (réécriture de a≤b) et b≤c (de b<c) donnent, par antisymétrie sur les cardinaux
    b,c, b=c — contredisant b≠c (de b<c).  D'où a≠c ; (a≤c et a≠c) = a<c."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    hyp = et(et(et(inf_egal_card(vA, vB), inf_strict_card(vB, vC)),
                est_cardinal(vA)), est_cardinal(vB))
    hyp = et(hyp, est_cardinal(vC))
    h = N.assume(hyp)
    le_ab = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # a ≤ b
    strict_bc = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # b < c
    card_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(b)
    card_c = conjonction_elim_droite(h)             # est_cardinal(c)
    le_bc = conjonction_elim_gauche(strict_bc)      # b ≤ c
    ne_bc = conjonction_elim_droite(strict_bc)      # b ≠ c
    # a ≤ c   (transitivité)
    le_ac = N.modus_ponens(conjonction_intro(le_ab, le_bc), _inf_egal_transitive_t(vA, vB, vC))
    # a ≠ c   par l'absurde : a = c ⇒ b = c (antisymétrie) contredit b ≠ c
    h_eq = N.assume(egal(vA, vC))                   # a = c
    # c ≤ b  : réécrire a en c dans « a ≤ b »  (Leibniz S6 sur le 1er argument)
    c_le_b = N.modus_ponens(le_ab, equivalence_avant(N.modus_ponens(h_eq,
        N.s6(vA, vC, "w", inf_egal_card(var("w"), vB)))))   # c ≤ b
    # antisymétrie sur b, c : (b≤c et c≤b et card b et card c) ⇒ b=c
    bc_eq = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        le_bc, c_le_b), card_b), card_c), _antisym_t(vB, vC))   # b = c
    contra = _ex_falso(bc_eq, ne_bc, non(egal(vA, vC)))         # ¬(a=c)  [sous a=c]
    ne_ac = N.modus_ponens(N.loi_deduction(egal(vA, vC), contra), N.s1(non(egal(vA, vC))))  # a≠c
    strict_ac = conjonction_intro(le_ac, ne_ac)     # a < c
    return N.loi_deduction(hyp, strict_ac)


def strict_inf_egal_compose(a="a", b="b", c="c"):
    """⊢ (a<b et b≤c et a,b,c cardinaux) ⇒ (a<c).   (< puis ≤ donne <.)

    a≤b (de a<b) et b≤c ⇒ a≤c.  STRICTITÉ a≠c : si a=c, alors b≤c=a (réécriture)
    et a≤b donnent, par antisymétrie sur a,b, a=b — contredisant a≠b (de a<b)."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    hyp = et(et(et(inf_strict_card(vA, vB), inf_egal_card(vB, vC)),
                est_cardinal(vA)), est_cardinal(vB))
    hyp = et(hyp, est_cardinal(vC))
    h = N.assume(hyp)
    strict_ab = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # a < b
    le_bc = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # b ≤ c
    card_a = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # est_cardinal(a)
    card_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(b)
    card_c = conjonction_elim_droite(h)             # est_cardinal(c)
    le_ab = conjonction_elim_gauche(strict_ab)      # a ≤ b
    ne_ab = conjonction_elim_droite(strict_ab)      # a ≠ b
    le_ac = N.modus_ponens(conjonction_intro(le_ab, le_bc), _inf_egal_transitive_t(vA, vB, vC))
    # a ≠ c : si a=c, alors b ≤ a (réécrire c→a dans b≤c) et a≤b ⇒ a=b (antisym)
    h_eq = N.assume(egal(vA, vC))                   # a = c
    c_eq_a = N.modus_ponens(h_eq, symetrie(vA, vC)) # c = a
    b_le_a = N.modus_ponens(le_bc, equivalence_avant(N.modus_ponens(c_eq_a,
        N.s6(vC, vA, "w", inf_egal_card(vB, var("w"))))))   # b ≤ a
    ab_eq = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        le_ab, b_le_a), card_a), card_b), _antisym_t(vA, vB))   # a = b
    contra = _ex_falso(ab_eq, ne_ab, non(egal(vA, vC)))         # ¬(a=c)  [sous a=c]
    ne_ac = N.modus_ponens(N.loi_deduction(egal(vA, vC), contra), N.s1(non(egal(vA, vC))))  # a≠c
    strict_ac = conjonction_intro(le_ac, ne_ac)
    return N.loi_deduction(hyp, strict_ac)


def strict_transitive(a="a", b="b", c="c"):
    """⊢ (a<b et b<c et a,b,c cardinaux) ⇒ (a<c).   (TRANSITIVITÉ de l'ordre STRICT.)

    a<b donne a≤b ; b<c donne b≤c ; on enchaîne par inf_egal_strict_compose
    (≤ puis < donne <), avec b<c gardé.  GARDE « a,b,c cardinaux » (antisymétrie)."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    hyp = et(et(et(inf_strict_card(vA, vB), inf_strict_card(vB, vC)),
                est_cardinal(vA)), est_cardinal(vB))
    hyp = et(hyp, est_cardinal(vC))
    h = N.assume(hyp)
    strict_ab = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # a < b
    strict_bc = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h))))               # b < c
    card_a = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))
    card_b = conjonction_elim_droite(conjonction_elim_gauche(h))
    card_c = conjonction_elim_droite(h)
    le_ab = conjonction_elim_gauche(strict_ab)      # a ≤ b
    # (a≤b et b<c et card a,b,c) ⇒ a<c
    comp = inf_egal_strict_compose(a, b, c)
    inner = et(et(et(inf_egal_card(vA, vB), inf_strict_card(vB, vC)),
                   est_cardinal(vA)), est_cardinal(vB))
    inner = et(inner, est_cardinal(vC))
    strict_ac = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(le_ab, strict_bc), card_a), card_b), card_c), comp)   # a < c
    return N.loi_deduction(hyp, strict_ac)


# ══════════════════════════════════════════════════════════════════════════════
#  (E)  BORNES EXPONENTIELLES  (conditionnelles — verrou de support reporté)
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.5 Def.4 | E III.28 L.20-21 | PDF p.131
#   (bornes 1 ≤ a^b et a ≤ a^b : conséquences directes de la Déf. 4, non énoncées
#    telles quelles dans le livre ; version inconditionnelle dans
#    somme_produit_bornes/ensembles_bornes_exposant.py.)
def un_inf_egal_exposant_conditionnel(a="a", b="b"):
    """⊢ (1 ≤ 𝓕(b;a)) ⇒ (1 ≤ a^b).   (borne inférieure 1 ≤ a^b, E.III.3.5.)

    a^b := Card(𝓕(b;a)).  L'hypothèse 1 ≤ 𝓕(b;a) (le SET 1 s'injecte dans
    l'ensemble des applications de b dans a) se TRANSPORTE au niveau des cardinaux
    par inf_egal_transporte_cardinal (le PONT, contenu réel) : Card 1 ≤ Card(𝓕(b;a))
    = a^b ; comme Card(1)=1 est un cardinal canonique, c'est 1 ≤ a^b modulo cette
    identification.  NON tautologique (le pont est inf_egal_transporte_cardinal).

    REPORTÉ : la DÉCHARGE de l'hypothèse (1 ↪ 𝓕(b;a), i.e. 𝓕(b;a) ≠ ∅, qui résulte
    de l'existence d'au moins une application — VRAI dès que a≠0, construction
    « valeur d'application »).  Conditionnel ici."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
    vA, vB = _t(a), _t(b)
    Fba = E.applications(vB, vA)                     # 𝓕(b;a)  (support)
    # (X ≤ Y) ⇒ (Card X ≤ Card Y)  au TERME (1, 𝓕(b;a))
    pont = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))     # (∀XY)((X≤Y)⇒(CardX≤CardY))
    pont_inst = instancie(instancie(pont, UN), Fba)  # (1≤𝓕(b;a)) ⇒ (Card 1 ≤ Card 𝓕(b;a))
    h = N.assume(inf_egal_card(UN, Fba))             # 1 ≤ 𝓕(b;a)
    card_le = N.modus_ponens(h, pont_inst)           # Card 1 ≤ Card 𝓕(b;a) = Card 1 ≤ a^b
    return N.loi_deduction(inf_egal_card(UN, Fba), card_le)


def base_inf_egal_exposant_conditionnel(a="a", b="b"):
    """⊢ (a ≤ 𝓕(b;a)) ⇒ (Card a ≤ a^b).   (borne a ≤ a^b pour b ≠ 0, E.III.3.5.)

    Même transport par le pont : a ≤ 𝓕(b;a) (au niveau des SUPPORTS) donne
    Card a ≤ Card 𝓕(b;a) = a^b.  L'hypothèse a ≤ 𝓕(b;a) est vraie quand b ≠ 0
    (l'application constante x↦v plonge a dans 𝓕(b;a) en fixant un point de b) ;
    sa DÉCHARGE est le verrou « valeur d'application » reporté.  Conditionnel."""
    vA, vB = _t(a), _t(b)
    Fba = E.applications(vB, vA)
    pont = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    pont_inst = instancie(instancie(pont, vA), Fba)  # (a≤𝓕(b;a)) ⇒ (Card a ≤ Card 𝓕(b;a))
    h = N.assume(inf_egal_card(vA, Fba))             # a ≤ 𝓕(b;a)
    card_le = N.modus_ponens(h, pont_inst)           # Card a ≤ Card 𝓕(b;a) = a^b
    return N.loi_deduction(inf_egal_card(vA, Fba), card_le)


__all__ = [
    "strict_implique_inf_egal", "strict_irreflexif",
    "cantor_strict_existe", "aucun_plus_grand_cardinal",
    "inf_egal_strict_compose", "strict_inf_egal_compose", "strict_transitive",
    "un_inf_egal_exposant_conditionnel", "base_inf_egal_exposant_conditionnel",
]
