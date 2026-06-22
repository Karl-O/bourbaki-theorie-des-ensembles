"""§II.5 — Monotonie du produit d'une famille d'ensembles (sens « ⊂ »).

Prop. 10 (E.II.5), forme support FINISHABLE (le sens direct de l'équivalence
∏Xⱼ ⊂ ∏Yⱼ ⟺ ∀j Xⱼ⊂Yⱼ) :

    ( (∀ι)(ι∈I ⇒ Xι ⊂ Yι) )  ⇒  ( ∏_{ι∈I} Xι ⊂ ∏_{ι∈I} Yι ).

Avec Xι = valeur_famille(f, ι) et Yι = valeur_famille(g, ι) (deux familles
f, g sur le MÊME ensemble d'indices I).

Preuve (purement « pointwise », SANS récurrence) :
  soit F ∈ ∏(f,I) ; par la Déf. 1 F est fonctionnel, dom F = I, et pour tout
  ι∈I, F(ι) ∈ Xι ; l'hypothèse donne Xι ⊂ Yι donc F(ι) ∈ Yι ; les trois
  conjoints (fonctionnel, dom F = I, ∀ι F(ι)∈Yι) caractérisent F ∈ ∏(g,I).
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, et, impl, appartient, inclus, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout


def _inst_produit(f, i, ff):
    """⊢ (F ∈ ∏(f,I)) ⇔ ( F fonctionnel ∧ dom F = I ∧ (∀i)(i∈I ⇒ F(i)∈X_i) )."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, f), i), ff)


def _enonce(f="f", g="g", i="I"):
    """L'énoncé visé (cible) : hypothèse ⇒ inclusion des produits."""
    vf, vg, vI = var(f), var(g), var(i)
    vi = var("i")
    hyp = pourtout("i", impl(appartient(vi, vI),
                             inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi))))
    concl = inclus(E.produit_famille(vf, vI), E.produit_famille(vg, vI))
    return impl(hyp, concl)


def _cible(f="f", g="g", i="I"):
    return _enonce(f, g, i)


def produit_monotone(f="f", g="g", i="I", ff="F"):
    """⊢ ((∀ι)(ι∈I ⇒ Xι⊂Yι)) ⇒ (∏(f,I) ⊂ ∏(g,I)).   (§II.5, Prop.10, sens direct.)"""
    vf, vg, vI, vF = var(f), var(g), var(i), var(ff)
    vi = var("i")

    # Hypothèse : (∀ι)(ι∈I ⇒ Xι⊂Yι)
    hyp = pourtout("i", impl(appartient(vi, vI),
                             inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi))))
    h = N.assume(hyp)

    # Supposons F ∈ ∏(f,I).
    hF = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(hF, equivalence_avant(_inst_produit(vf, vI, vF)))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # F fonctionnel
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps))       # dom F = I
    forall_f = conjonction_elim_droite(corps)            # (∀i)(i∈I ⇒ F(i)∈X_i)

    # Objectif : (∀i)(i∈I ⇒ F(i)∈Y_i).
    # On travaille sur un indice frais « a » (pas de capture : a ∉ τ internes).
    va = var("a")
    inst_fF = instancie(forall_f, va)                    # a∈I ⇒ F(a)∈X_a
    inst_hyp = instancie(h, va)                          # a∈I ⇒ X_a⊂Y_a

    ha = N.assume(appartient(va, vI))                    # a∈I
    Fa_in_Xa = N.modus_ponens(ha, inst_fF)               # F(a)∈X_a
    Xa_sub_Ya = N.modus_ponens(ha, inst_hyp)             # X_a⊂Y_a  =  (∀z)(z∈X_a⇒z∈Y_a)
    # instancier l'inclusion en z := F(a)
    Fa = E.valeur(vF, va)
    incl_Fa = instancie(Xa_sub_Ya, Fa)                   # F(a)∈X_a ⇒ F(a)∈Y_a
    Fa_in_Ya = N.modus_ponens(Fa_in_Xa, incl_Fa)         # F(a)∈Y_a

    imp_a = N.loi_deduction(appartient(va, vI), Fa_in_Ya)   # a∈I ⇒ F(a)∈Y_a
    forall_a = N.generalisation("a", imp_a)              # (∀a)(a∈I ⇒ F(a)∈Y_a)

    # α-renommer le liant « a » → « i » pour coïncider avec le corps de ∏(g,I)
    membre_g = impl(appartient(va, vI),
                    appartient(E.valeur(vF, va), E.valeur_famille(vg, va)))
    forall_i = N.modus_ponens(forall_a,
                              equivalence_avant(alpha_pour_tout("a", "i", membre_g)))

    # Reconstituer le corps de ∏(g,I) : (F fonctionnel ∧ dom F = I) ∧ ∀i …
    corps_g = conjonction_intro(conjonction_intro(fonctionnel, domaine), forall_i)
    F_in_prod_g = N.modus_ponens(corps_g, equivalence_arriere(_inst_produit(vg, vI, vF)))

    # F∈∏(f,I) ⇒ F∈∏(g,I), généraliser sur F → inclusion (liant « z »)
    imp_F = N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), F_in_prod_g)
    forall_F = N.generalisation(ff, imp_F)
    membre_incl = impl(appartient(vF, E.produit_famille(vf, vI)),
                       appartient(vF, E.produit_famille(vg, vI)))
    incl_z = N.modus_ponens(forall_F,
                            equivalence_avant(alpha_pour_tout(ff, "z", membre_incl)))
    return N.loi_deduction(hyp, incl_z)


__all__ = ["produit_monotone", "_cible"]
