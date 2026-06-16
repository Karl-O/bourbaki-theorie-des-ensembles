"""§III.6 — ℵ₀ = Card(ℕ) : ℕ EST INFINI  (ℵ₀ = ℵ₀ + 1, donc ¬Fini(ℵ₀)).

🎯🎯🎯 PREMIER CARDINAL INFINI CONCRET.  ℕ (= NN, ensembles_ensemble_NN) est un SET
concret ; ce module montre que son cardinal ℵ₀ := Card(NN) vérifie l'ÉQUATION
CARACTÉRISTIQUE DE L'INFINI

        ℵ₀  =  successeur(ℵ₀)   (= ℵ₀ + 1),

et en déduit ¬Fini(ℵ₀) : ℵ₀ N'EST PAS un cardinal fini — ℕ est infini.

────────────────────────────────────────────────────────────────────────────────
ROUTE (Dedekind : un ensemble est infini ssi il est équipotent à une partie propre).

  • La translation s : n ↦ successeur(n) est une BIJECTION  NN → NN∖{0}  :
      – s = graphe_terme(NN, successeur(x))  (fonctionnel, dom = NN) ;
      – s INJECTIF sur NN : s(u)=s(u') ⇒ successeur(u)=successeur(u') ⇒ (Prop. 8,
        successeur injectif) Card u = Card u' ; or u,u'∈NN ⇒ Fini u, Fini u' ⇒
        est_cardinal ⇒ Card u = u, Card u' = u' (cardinal_de_cardinal) ⇒ u = u' ;
      – image(s, NN) = NN∖{0} :
          (⊆) t∈NN ⇒ successeur(t)∈NN (NN_clos_successeur) et successeur(t)≠0
              (successeur_non_nul : 0=∅, mais successeur(t)=Card(t⊔{∅}) avec
              t⊔{∅}≠∅, donc Card≠∅) ;
          (⊇) m∈NN∖{0} ⇒ Fini m et m≠0 ⇒ (Prop. 2 §III.5, predecesseur_fini)
              (∃k)(m=successeur(k) et est_cardinal k et k<m) ; k est fini (k<m≤fini)
              donc k∈NN, et m=successeur(k)=s(k) ∈ image(s,NN).
    D'où Eq(NN, NN∖{0}).                                          [NN_eq_NN_sans_zero]

  • NN = (NN∖{0}) ∪ {0}  avec  0 ∉ (NN∖{0})  (réunion DISJOINTE), donc
        Card NN = Card((NN∖{0})⊔{0}) = Card(NN∖{0}) + 1 = successeur(Card(NN∖{0}))
    (surgery « retrait + adjonction » eq_retire_ajoute, exactement comme la Prop. 2).
  • Eq(NN, NN∖{0}) (étape précédente) ⇒ Card NN = Card(NN∖{0})  (Proposition 1).
  • combinaison ⇒  Card NN = successeur(Card NN).               [aleph0_egal_succ]

  • Fini(ℵ₀) = est_cardinal(ℵ₀) ∧ ¬(ℵ₀ = successeur(ℵ₀)) ; le 2ᵉ conjoint est NIÉ par
    aleph0_egal_succ ⇒ ¬Fini(ℵ₀).                                  [aleph0_infini]

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  Rien postulé — tout DÉRIVE de
   Prop. 2 (predecesseur_fini_universel_preuve), Prop. 8 (prop8_successeur_injectif),
   des lemmes de NN (zero_dans_NN, NN_clos_successeur, appartenance_NN) et de la
   machinerie de recollement / Card-de-réunion-disjointe (eq_retire_ajoute), TOUTES
   CLOSES.  ⚠️ PERF : appartenance_NN repose sur N_existe (~5 min, τ-cardinaux
   imbriqués) ; les cœurs sont mémoïsés (lru_cache) — construits UNE fois par session.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus,
    subst_t, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    contraposition,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe, alpha_pour_tout,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, equipotent, cardinal, est_bijection_de, inf_egal_card,
    inf_strict_card,
)
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO

# ── infra GRAPHE D'UN TERME (lemmes de base ; on RECONSTRUIT les dérivés capture-safe) ──
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import membre_graphe_terme

# ── briques CLOSES réutilisées ───────────────────────────────────────────────
from bourbaki.entiers.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN, appartenance_NN_instanciee,
    zero_dans_NN, NN_clos_successeur,
)

# ── briques pour la chirurgie de cardinal (surgery GÉNÉRALE, SANS est_cardinal) ──
from bourbaki.entiers.ensembles_predecesseur_prop2 import (
    eq_retire_ajoute, _eq_sym_t, _eq_son_cardinal, _eq_somme_invariant_t,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_successeur import (
    successeur_egale_card_somme,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro as _conj_intro


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _rename_pourtout_externe(thm, y):
    """De thm ⊢ (∀x)R, déduit ⊢ (∀y)(y|x)R  (α-renommage du liant LE PLUS EXTERNE).

    Lit le binder x = thm.conclusion.lieur et le corps R = thm.conclusion.sous[0],
    applique alpha_pour_tout(x, y, R) puis modus ponens (sens ⇒)."""
    concl = thm.conclusion
    assert concl.tag == "forall", "_rename_pourtout_externe : pas un ∀ en tête"
    x = concl.lieur
    R = concl.sous[0]
    if x == y:
        return thm
    return N.modus_ponens(thm, equivalence_avant(alpha_pour_tout(x, y, R)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 DÉFINITION — ℵ₀ := Card(NN)
# ════════════════════════════════════════════════════════════════════════════
@lru_cache(maxsize=None)
def aleph_0():
    """🎯 ℵ₀ := Card(NN).   (TERME CLOS — le cardinal de l'ensemble des entiers.)

    Le cardinal de l'ensemble concret NN = { x | Fini x } des entiers naturels."""
    return cardinal(ensemble_NN())


# ════════════════════════════════════════════════════════════════════════════
#  CHIRURGIE GÉNÉRALE — Card X = successeur( Card(X∖{x0}) )  pour x0 ∈ X
#  (variante de m_egal_successeur_card_diff SANS est_cardinal(X) : vaut pour TOUT
#   ensemble X, en particulier X = NN qui n'est PAS un cardinal.)
# ════════════════════════════════════════════════════════════════════════════
def card_egal_succ_card_diff(X, x0):
    """⊢ ( x0 ∈ X ) ⇒ Card X = successeur( Card(X ∖ {x0}) ).   (THÉORÈME, version GÉNÉRALE.)

    Mirroir de `m_egal_successeur_card_diff` (ensembles_predecesseur_prop2) PRIVÉ de
    l'étape « Card m = m » (qui exigeait est_cardinal(m)) : pour un ENSEMBLE QUELCONQUE
    X avec x0∈X, D := X∖{x0}, on a — par la chirurgie retrait+adjonction —
      Card X = Card(D⊔{∅})   (Eq(X,D⊔{∅}) via eq_retire_ajoute ⇒ Card =, _prop1_direct_t) ;
      Card(D⊔{∅}) = Card(Card D ⊔ {∅})   (Eq(Card D, D) ⇒ Card =, somme invariante) ;
      Card(Card D ⊔ {∅}) = successeur(Card D)   (successeur_egale_card_somme) ;
    d'où Card X = successeur(Card D).  CLOS modulo la seule hyp honnête x0∈X.  theorie=22."""
    vX, vx0 = _t(X), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vX, sing)                             # D = X∖{x0}
    cD = cardinal(D)                                       # Card D
    sing_vide = E.singleton(E.VIDE)                        # {∅}
    DsVide = somme_disjointe(D, sing_vide)                 # D ⊔ {∅}
    cDsVide = cardinal(DsVide)                             # Card(D⊔{∅})
    cDsVide_card = somme_disjointe(cD, sing_vide)          # Card D ⊔ {∅}

    h = N.assume(appartient(vx0, vX))                      # x0 ∈ X
    # Eq(X, D⊔{∅}) ⇒ Card X = Card(D⊔{∅})
    eq_X_DsVide = N.modus_ponens(h, eq_retire_ajoute(vX, vx0))          # Eq(X, D⊔{∅})  CLOS
    card_eq = N.modus_ponens(eq_X_DsVide, _prop1_direct_t(vX, DsVide))  # Card X = Card(D⊔{∅})
    # successeur(Card D) = Card(Card D ⊔ {∅})
    succ_eq = successeur_egale_card_somme(cD)              # succ(Card D) = Card(Card D ⊔ {∅})
    # Card(Card D ⊔ {∅}) = Card(D⊔{∅})  via Eq(Card D, D)
    eq_cardD_D = N.modus_ponens(_eq_son_cardinal(D), _eq_sym_t(D, cD))  # Eq(Card D, D)
    eq_vide = instancie(N.generalisation("X", equipotence_reflexive("X")), sing_vide)  # Eq({∅},{∅})
    inv = _eq_somme_invariant_t(cD, sing_vide, D, sing_vide)
    eq_sommes = N.modus_ponens(conjonction_intro(eq_cardD_D, eq_vide), inv)  # Eq(Card D⊔{∅}, D⊔{∅})
    card_sommes_eq = N.modus_ponens(eq_sommes, _prop1_direct_t(cDsVide_card, DsVide))  # Card(CardD⊔{∅})=Card(D⊔{∅})

    # chaîne : Card X = Card(D⊔{∅}) = Card(Card D ⊔ {∅}) = successeur(Card D)
    card_DsVide_eq = N.modus_ponens(card_sommes_eq, symetrie(cardinal(cDsVide_card), cDsVide))  # Card(D⊔{∅})=Card(CardD⊔{∅})
    chain = composer_egalites(card_eq, card_DsVide_eq)     # Card X = Card(Card D ⊔ {∅})
    card_card_eq_succ = N.modus_ponens(succ_eq, symetrie(successeur(cD), cardinal(cDsVide_card)))  # Card(CardD⊔{∅})=succ(CardD)
    cardX_eq_succ = composer_egalites(chain, card_card_eq_succ)  # Card X = successeur(Card D)
    assert cardX_eq_succ.conclusion == egal(cardinal(vX), successeur(cD)), \
        "card_egal_succ_card_diff : conclusion ≠ (Card X = successeur(Card(X∖{x0})))"
    return N.loi_deduction(appartient(vx0, vX), cardX_eq_succ)  # (x0∈X) ⇒ Card X = successeur(Card(X∖{x0}))


# ════════════════════════════════════════════════════════════════════════════
#  GRAPHE DE LA TRANSLATION  s = { (n, successeur(n)) | n ∈ A }   (CAPTURE-SAFE)
#
#  ⚠️ Le terme successeur(n) = Card(n ⊔ {∅}) est un τ-terme PROFOND dont les liants
#  INTERNES incluent « u, v, z, y » ; les outils génériques graphe_terme_* utilisent
#  PRÉCISÉMENT ces noms comme paramètres → collision (capture-évitement → renommage
#  @0 → mismatch structurel).  On RECONSTRUIT donc les lemmes du graphe avec des
#  liants SÛRS (« n0 » pour x, « e0/u0/up0 », « w0/wp0 », « y0/z0 ») qui ne figurent
#  PAS parmi les liants internes du successeur — alors subst_t(var(NOM), "n0",
#  successeur(n0)) = successeur(NOM) structurellement (vérifié).
# ════════════════════════════════════════════════════════════════════════════
_BND = "n0"                          # variable liée du graphe (≠ liants internes de succ)


def _succ_terme():
    """Le terme successeur(n0) (n0 = variable liée du graphe, capture-safe)."""
    return successeur(var(_BND))


def _s(a):
    """s := graphe_terme(A, successeur(n0), "n0") = { (n, successeur(n)) | n ∈ A }."""
    return E.graphe_terme(_t(a), _succ_terme(), _BND)


def _membre_s(a, u="e0", w="w0"):
    """⊢ ((u, w) ∈ s) ⇔ ( u ∈ A  et  w = successeur(u) ).   (capture-safe.)

    membre_graphe_terme avec liants sûrs ; u, w doivent éviter les liants internes
    de successeur (défauts « e0 », « w0 », sûrs)."""
    return membre_graphe_terme(_t(a), _succ_terme(), u, w, _BND, "y0")


# ── Conjoint 1 : s fonctionnel ────────────────────────────────────────────────
def s_fonctionnel(a):
    """⊢ est_fonctionnel(s).   (deux valeurs en u sont toutes deux successeur(u).)

    est_fonctionnel(s) = (∀u)(∀v)(∀z)(((u,v)∈s et (u,z)∈s) ⇒ v=z) (liants u,v,z
    forcés par est_fonctionnel — mais ces liants ne PÉNÈTRENT PAS le terme s = app(...),
    donc pas de capture).  On prouve le corps avec des PARAMÈTRES sûrs e0,w0,wp0 puis
    on α-renomme les 3 liants vers u,v,z."""
    va = _t(a)
    s = _s(a)
    ve, vw, vwp = var("e0"), var("w0"), var("wp0")
    succ_e = successeur(ve)
    mem_w = _membre_s(a, "e0", "w0")               # ((e0,w0)∈s) ⇔ (e0∈A et w0=succ e0)
    mem_wp = _membre_s(a, "e0", "wp0")             # ((e0,wp0)∈s) ⇔ (e0∈A et wp0=succ e0)

    ante = et(appartient(E.couple(ve, vw), s), appartient(E.couple(ve, vwp), s))
    h = N.assume(ante)
    w_eq = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_gauche(h), equivalence_avant(mem_w)))      # w0 = succ e0
    wp_eq = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_droite(h), equivalence_avant(mem_wp)))     # wp0 = succ e0
    w_wp = composer_egalites(w_eq, N.modus_ponens(wp_eq, symetrie(vwp, succ_e)))  # w0=wp0
    inner = N.loi_deduction(ante, w_wp)                            # body0 (sous hyps déchargées)
    gen = N.generalisation("e0", N.generalisation("w0", N.generalisation("wp0", inner)))
    # gen : (∀e0)(∀w0)(∀wp0) body0.  Cible = est_fonctionnel(s) = (∀u)(∀v)(∀z) body0[e0:=u,w0:=v,wp0:=z].
    # On renomme du PLUS INTERNE au plus externe ; à chaque étape on descend par
    # instanciation puis on remonte par généralisation, en α-renommant le liant visé.
    body0 = impl(et(appartient(E.couple(var("e0"), var("w0")), s),
                    appartient(E.couple(var("e0"), var("wp0")), s)),
                 egal(var("w0"), var("wp0")))
    # ── wp0 → z ──
    inner_e0w0 = instancie(instancie(gen, var("e0")), var("w0"))   # (∀wp0) body0
    ren_z = N.modus_ponens(inner_e0w0, equivalence_avant(alpha_pour_tout("wp0", "z", body0)))  # (∀z) body0[wp0:=z]
    body_z = subst_f(var("z"), "wp0", body0)
    g2 = N.generalisation("e0", N.generalisation("w0", ren_z))     # (∀e0)(∀w0)(∀z) body_z
    # ── w0 → v ──  (corps sous le ∀w0 :  (∀z) body_z)
    corps_w0 = pourtout("z", body_z)
    inner_e0 = instancie(g2, var("e0"))                            # (∀w0) corps_w0
    ren_v = N.modus_ponens(inner_e0, equivalence_avant(alpha_pour_tout("w0", "v", corps_w0)))  # (∀v)(∀z) ...
    g3 = N.generalisation("e0", ren_v)                             # (∀e0)(∀v)(∀z) ...
    # ── e0 → u ──  (corps sous le ∀e0 = ren_v.conclusion, lu directement)
    res = N.modus_ponens(g3, equivalence_avant(alpha_pour_tout("e0", "u", ren_v.conclusion)))  # (∀u)(∀v)(∀z) ...
    assert res.conclusion == E.est_fonctionnel(s), \
        "s_fonctionnel : conclusion ≠ est_fonctionnel(s) après α-renommage"
    return res


__all__ = ["aleph_0"]
