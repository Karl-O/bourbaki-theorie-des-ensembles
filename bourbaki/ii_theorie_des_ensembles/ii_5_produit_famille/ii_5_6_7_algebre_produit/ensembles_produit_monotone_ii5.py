"""§II.5 — Monotonie du produit d'une famille d'ensembles (sens « ⊂ »).

Prop. 10 (E.II.5), forme support FINISHABLE (le sens direct de l'équivalence
∏Xⱼ ⊂ ∏Yⱼ ⟺ ∀j Xⱼ⊂Yⱼ) :

    ( (∀ι)(ι∈I ⇒ Xι ⊂ Yι) )  ⇒  ( ∏_{ι∈I} Xι ⊂ ∏_{ι∈I} Yι ).

Avec Xι = valeur_famille(f, ι) et Yι = valeur_famille(g, ι) (deux familles
f, g sur le MÊME ensemble d'indices I).

Preuve (purement « pointwise », SANS récurrence) :
  soit F ∈ ∏(f,I) ; par la Déf. 1 F est un graphe inclus dans I×⋃Xι, fonctionnel,
  dom F = I, et pour tout ι∈I, F(ι) ∈ Xι ; l'hypothèse donne Xι ⊂ Yι donc
  F(ι) ∈ Yι ; le transport vers ∏(g,I) reconstruit le conjoint de tête F ⊂ I×⋃Yι
  (la réunion change avec la famille) et conserve les deux autres.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, et, impl, appartient, inclus, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    composants_membre, transporter_dans_produit)


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


# @livre Ch.II §5.4 Cor.3 | E II.34 L.40-44 | PDF p.85
# @livre Ch.R §4 Prop.- | E.R.21 item 12a (∀ι Xι⊂Yι ⇒ ∏Xι⊂∏Yι) | PDF p.324
def produit_monotone(f="f", g="g", i="I", ff="F"):
    """⊢ ((∀ι)(ι∈I ⇒ Xι⊂Yι)) ⇒ (∏(f,I) ⊂ ∏(g,I)).   (§II.5, Prop.10, sens direct.)"""
    vf, vg, vI, vF = var(f), var(g), var(i), var(ff)
    vi = var("i")

    # Hypothèse : (∀ι)(ι∈I ⇒ Xι⊂Yι)
    hyp = pourtout("i", impl(appartient(vi, vI),
                             inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi))))
    h = N.assume(hyp)

    # Supposons F ∈ ∏(f,I).  Les quatre composants du corps (Déf. 1) sont lus par
    # `composants_membre` : c'est lui qui porte les chemins d'accès, pas ce module.
    hF = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    _incl, _fonctionnel, _domaine, forall_f = composants_membre(hF, vf, vI, vF)

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

    # Passer de ∏(f,I) à ∏(g,I) : est_fonctionnel et dom F = I sont conservés, le
    # conjoint de tête F ⊂ I×⋃Y_ι est RECONSTRUIT (la réunion change avec la famille).
    F_in_prod_g = transporter_dans_produit(hF, forall_i, vF, vf, vg, vI)

    # F∈∏(f,I) ⇒ F∈∏(g,I), généraliser sur F → inclusion (liant « z »)
    imp_F = N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), F_in_prod_g)
    forall_F = N.generalisation(ff, imp_F)
    membre_incl = impl(appartient(vF, E.produit_famille(vf, vI)),
                       appartient(vF, E.produit_famille(vg, vI)))
    incl_z = N.modus_ponens(forall_F,
                            equivalence_avant(alpha_pour_tout(ff, "z", membre_incl)))
    return N.loi_deduction(hyp, incl_z)


__all__ = ["produit_monotone", "_cible"]
