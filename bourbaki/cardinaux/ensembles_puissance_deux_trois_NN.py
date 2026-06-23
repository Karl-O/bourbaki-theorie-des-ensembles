"""§III.5.1 / §III.6 (prérequis Lemme 2) — les puissances 2^n et 3^n SONT DES ENTIERS.

🎯 BRIQUE de base pour l'injection de couplage  (m,n) ↦ 2^m·3^n  :  ℕ×ℕ ↪ ℕ
   (direction DURE du Lemme 2 §III.6, ℵ₀·ℵ₀=ℵ₀).  Avant de prouver l'injectivité,
   il faut savoir que les images 2^m, 3^n VIVENT dans ℕ (sont des entiers / cardinaux
   finis).  C'est l'objet de ce module — DEUX lemmes INCONDITIONNELS, CLOS :

        `deux_puissance_dans_NN`   ⊢  Fini n  ⇒  Fini( 2^n ),
        `trois_puissance_dans_NN`  ⊢  Fini n  ⇒  Fini( 3^n ).

ROUTE (non circulaire, ré-emploi pur) — `puissance_entiers_ferme_inconditionnel`
(Cor. 3 §III.5.1, DÉJÀ CLOS) donne  ( Fini a et Fini b ) ⇒ Fini(a^b) ;  on GÉNÉRALISE
sur la base puis on INSTANCIE a := 2 (resp. 3) au TERME, et on DÉCHARGE le conjoint
Fini(2) (resp. Fini(3)) par `fini_deux` (resp. `fini_trois`).  Il reste exactement
Fini(n) ⇒ Fini(2^n)  (resp. 3^n).  2^n := exposant_cardinal_binaire(2, n).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import instancie

from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.ensembles_puissance_entiers_inconditionnel import (
    puissance_entiers_ferme_inconditionnel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, DEUX, TROIS
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import fini_deux
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_trois_quatre import fini_trois


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    """{preuve_hyp ⊢ hyp} + (thm ⊢ hyp ⇒ C)  →  ⊢ C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _base_puissance_dans_NN(base_terme, fini_base, n="npdt"):
    """{fini_base ⊢ Fini(base)} ⊢ Fini(n) ⇒ Fini(base^n).

    `puissance_entiers_ferme_inconditionnel` ⊢ (Fini a et Fini b) ⇒ Fini(a^b),
    généralisé sur la base 'apuf' puis instancié au TERME base ; on décharge le
    conjoint Fini(base) par `fini_base`, laissant Fini(n) ⇒ Fini(base^n)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro
    vbase, vn = _t(base_terme), _t(n)
    # (Fini a et Fini b) ⇒ Fini(a^b)  sur NOMS FRAIS apuf,bpuf, capture-safe
    pef = puissance_entiers_ferme_inconditionnel("apuf", "bpuf")
    # généraliser sur la base 'apuf' puis sur l'exposant 'bpuf', instancier base, n
    gen = N.generalisation("apuf", N.generalisation("bpuf", pef))
    inst = instancie(instancie(gen, vbase), vn)        # (Fini base et Fini n) ⇒ Fini(base^n)
    # sous {Fini n}, construire (Fini base et Fini n), déduire Fini(base^n)
    h_n = N.assume(est_fini(vn))
    conj = conjonction_intro(fini_base, h_n)                 # Fini base et Fini n  [Fini n]
    fini_pow = N.modus_ponens(conj, inst)                    # Fini(base^n)         [Fini n]
    out = N.loi_deduction(est_fini(vn), fini_pow)            # Fini(n) ⇒ Fini(base^n)
    cible = impl(est_fini(vn), est_fini(exposant_cardinal_binaire(vbase, vn)))
    assert out.conclusion == cible, \
        f"_base_puissance_dans_NN : conclusion inattendue\n{out.conclusion}\n{cible}"
    assert out.est_clos, "_base_puissance_dans_NN : non clos"
    return out


def deux_puissance_dans_NN(n="npdt"):
    """🎯 ⊢ Fini(n) ⇒ Fini( 2^n ).   (CLOS, 0 hyp, theorie=22.)

    2^n := exposant_cardinal_binaire(2, n).  Instance base=2 de Cor. 3 §III.5.1,
    Fini(2) déchargé par `fini_deux`."""
    return _base_puissance_dans_NN(DEUX, fini_deux(), n)


def trois_puissance_dans_NN(n="npdt"):
    """🎯 ⊢ Fini(n) ⇒ Fini( 3^n ).   (CLOS, 0 hyp, theorie=22.)

    3^n := exposant_cardinal_binaire(3, n).  Instance base=3 de Cor. 3 §III.5.1,
    Fini(3) déchargé par `fini_trois`."""
    return _base_puissance_dans_NN(TROIS, fini_trois(), n)


__all__ = ["deux_puissance_dans_NN", "trois_puissance_dans_NN"]
