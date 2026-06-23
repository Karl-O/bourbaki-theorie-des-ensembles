"""§III.6 (prérequis Lemme 2, ℵ₀·ℵ₀=ℵ₀) — arithmétique multiplicative de ℕ vers
l'injection de couplage  (m,n) ↦ 2^m·3^n  :  ℕ×ℕ ↪ ℕ.

Construit bottom-up (cf. PLAN) :
  1. puissance_succ_eq_incond ⊢ (card a et Fini n) ⇒ a^(n+1) = a^n · a   (INCONDITIONNEL,
     hyp (B) de support déchargée par `B_preuve`, instance du keystone CLOS
     `eq_exposant_invariant`, exactement comme `puissance_entiers_ferme_inconditionnel`) ;
  2. trois_puiss_impair ⊢ Fini n ⇒ est_impair_propre(3^n)   (3^n impair, récurrence) ;
  3. deux_puiss_pair ⊢ (Fini k et k≠0) ⇒ est_pair_propre(2^k)   (2^k pair pour k≥1) ;
  4. puissance_strict_croissante ⊢ (Fini m et Fini m' et m<m') ⇒ 3^m < 3^m'  (⇒ injective).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, non, impl, existe, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal, inf_strict_card
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.entiers.ensembles_entiers import est_fini, est_entier, successeur, ZERO, DEUX, TROIS


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ══════════════════════════════════════════════════════════════════════════════
#  (1)  a^(n+1) = a^n · a   INCONDITIONNEL
# ══════════════════════════════════════════════════════════════════════════════
def puissance_succ_eq_incond_cible(a="Apsi", n="Npsi"):
    va, vn = _t(a), _t(n)
    an = exposant_cardinal_binaire(va, vn)
    lhs = exposant_cardinal_binaire(va, successeur(vn))
    rhs = produit_cardinal_binaire(an, va)
    return impl(et(est_cardinal(va), est_fini(vn)), egal(lhs, rhs))


def puissance_succ_eq_incond(a="Apsi", n="Npsi"):
    """🎯 ⊢ (est_cardinal a et Fini n) ⇒ a^(n+1) = a^n · a.   (INCONDITIONNEL.)

    `puissance_succ_eq(a,n)` ⊢ (B) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a) ;
    `B_preuve(a,n)` (instance CLOSE du keystone `eq_exposant_invariant`) décharge (B) ;
    `est_fini n` fournit `est_cardinal n` (1er conjoint).  theorie=22."""
    from bourbaki.cardinaux.ensembles_n_arith_iii5 import (
        puissance_succ_eq, exposant_invariance_enonce,
    )
    from bourbaki.cardinaux.ensembles_puissance_entiers_inconditionnel import B_preuve
    va, vn = _t(a), _t(n)

    pse = puissance_succ_eq(va, vn)        # (B) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a)
    B = B_preuve(va, vn)                    # ⊢ (B)  CLOS
    assert B.conclusion == exposant_invariance_enonce(va, vn), "B_preuve : forme ≠ (B)"
    sous_card = N.modus_ponens(B, pse)     # (card a et card n) ⇒ a^(n+1)=a^n·a

    h = N.assume(et(est_cardinal(va), est_fini(vn)))
    ca = conjonction_elim_gauche(h)        # est_cardinal a
    fn = conjonction_elim_droite(h)        # Fini n
    cn = conjonction_elim_gauche(fn)       # est_cardinal n
    eq = N.modus_ponens(conjonction_intro(ca, cn), sous_card)   # a^(n+1)=a^n·a
    out = N.loi_deduction(et(est_cardinal(va), est_fini(vn)), eq)
    assert out.conclusion == puissance_succ_eq_incond_cible(a, n), \
        f"puissance_succ_eq_incond : conclusion inattendue\n{out.conclusion}"
    return out


__all__ = ["puissance_succ_eq_incond", "puissance_succ_eq_incond_cible"]
