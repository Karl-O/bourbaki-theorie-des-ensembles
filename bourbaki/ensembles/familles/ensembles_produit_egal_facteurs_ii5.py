"""§II.5 — ÉGALITÉ du produit d'une famille d'ensembles à facteurs égaux.

Corollaire de la Prop. 10 (E.II.5) / du lemme `facteurs_egaux_donne_inclus` :

    ( (∀ι)(ι∈I ⇒ X_ι = Y_ι) )  ⇒  ( ∏_{ι∈I} X_ι = ∏_{ι∈I} Y_ι ).

Preuve (DOUBLE INCLUSION, SANS récurrence, INCONDITIONNELLE) :
  - le lemme clos `facteurs_egaux_donne_inclus(f,g,I)` donne, sous H, ∏X ⊂ ∏Y ;
  - sous H' := (∀ι)(ι∈I ⇒ Y_ι = X_ι) (obtenu de H par symétrie de = relevée sous
    le quantificateur), le même lemme appliqué à (g,f) donne ∏Y ⊂ ∏X ;
  - A1 (extensionnalité, `extensionnalite_appliquee`) conclut ∏X = ∏Y.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, et, impl, appartient, egal, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, conjonction_intro)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.familles.ensembles_produit_props2 import facteurs_egaux_donne_inclus


def _enonce(f="f", g="g", i="I"):
    """L'énoncé visé (cible) : facteurs égaux ⇒ produits égaux."""
    vf, vg, vI = var(f), var(g), var(i)
    vi = var("i")
    hyp = pourtout("i", impl(appartient(vi, vI),
                             egal(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi))))
    concl = egal(E.produit_famille(vf, vI), E.produit_famille(vg, vI))
    return impl(hyp, concl)


def _cible(f="f", g="g", i="I"):
    return _enonce(f, g, i)


def _symetrise_sous_quantif(h, vf, vg, vI, iota="i"):
    """De H=(∀ι)(ι∈I⇒X_ι=Y_ι), déduire H'=(∀ι)(ι∈I⇒Y_ι=X_ι).

    Indice frais « a » (pas de capture : a ∉ τ internes des familles)."""
    va = var("a")
    Xa = E.valeur_famille(vf, va)
    Ya = E.valeur_famille(vg, va)
    inst = instancie(h, va)                              # a∈I ⇒ X_a=Y_a
    ha = N.assume(appartient(va, vI))                    # a∈I
    eq_xy = N.modus_ponens(ha, inst)                     # X_a=Y_a
    eq_yx = N.modus_ponens(eq_xy, symetrie(Xa, Ya))      # Y_a=X_a
    imp_a = N.loi_deduction(appartient(va, vI), eq_yx)   # a∈I ⇒ Y_a=X_a
    forall_a = N.generalisation("a", imp_a)              # (∀a)(a∈I ⇒ Y_a=X_a)
    # α-renommer le liant « a » → « i » pour coïncider avec l'hypothèse attendue
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    membre = impl(appartient(va, vI),
                  egal(E.valeur_famille(vg, va), E.valeur_famille(vf, va)))
    return N.modus_ponens(forall_a,
                          equivalence_avant(alpha_pour_tout("a", iota, membre)))


def produit_egal_si_facteurs_egaux(f="f", g="g", i="I"):
    """⊢ ((∀ι)(ι∈I ⇒ X_ι=Y_ι)) ⇒ (∏(f,I) = ∏(g,I)).   (§II.5, corollaire Prop.10.)"""
    vf, vg, vI = var(f), var(g), var(i)
    vi = var("i")

    hyp = pourtout("i", impl(appartient(vi, vI),
                             egal(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi))))
    h = N.assume(hyp)

    # ∏X ⊂ ∏Y  (lemme clos appliqué à H)
    incl_lemme = facteurs_egaux_donne_inclus(f, g, i)    # H ⇒ (∏X ⊂ ∏Y)
    incl_XY = N.modus_ponens(h, incl_lemme)              # ∏X ⊂ ∏Y

    # H' : (∀ι)(ι∈I ⇒ Y_ι=X_ι) puis ∏Y ⊂ ∏X
    hp = _symetrise_sous_quantif(h, vf, vg, vI)          # (∀ι)(ι∈I ⇒ Y_ι=X_ι)
    incl_lemme2 = facteurs_egaux_donne_inclus(g, f, i)   # H' ⇒ (∏Y ⊂ ∏X)
    incl_YX = N.modus_ponens(hp, incl_lemme2)            # ∏Y ⊂ ∏X

    # A1 : (∏X ⊂ ∏Y et ∏Y ⊂ ∏X) ⇒ ∏X = ∏Y
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    ext = extensionnalite_appliquee(prodX, prodY)
    eq = N.modus_ponens(conjonction_intro(incl_XY, incl_YX), ext)  # ∏X = ∏Y

    return N.loi_deduction(hyp, eq)


__all__ = ["produit_egal_si_facteurs_egaux", "_cible"]
