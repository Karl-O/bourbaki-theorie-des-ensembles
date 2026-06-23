"""§II.4 — Réunion et intersection d'une famille d'ensembles.

Termes définis ⋃_{ι∈I} X_ι, ⋂_{ι∈I} X_ι (E.II.4.1, Déf. 1 et 2) avec axiomes
caractérisants (légitimés par S8 = sélection-réunion + extensionnalité A1, comme
produit/image). Une famille (X_ι)_{ι∈I} est une fonction ι↦X_ι ; X_ι est noté
par le terme valeur_famille(f, i).

Théorèmes certifiés : caractérisation de l'appartenance (instances des axiomes),
introduction dans la réunion, élimination de l'intersection, MONOTONIE de ⋃ et ⋂
(§II.4.2, demi-Prop. de croissance), et ⋃_{ι∈∅} X_ι = ∅ (note de la Déf. 1).

Les Propositions 1-10 et Déf. 4-8 plus profondes (reparamétrage surjectif,
associativité, image directe/réciproque, De Morgan sur familles, recollement,
somme) sont REPORTÉES (cf. rapport) : elles exigent une infrastructure absente
(complémentaire ∁_E, recollement de fonctions, sommes, surjections) ou de très
longues preuves multi-étapes nouvelles.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, existe, pourtout, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, instancie, contraposition,
                               projection_gauche, dni)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import monotonie_existe, monotonie_pour_tout
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import vide_sans_element
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element


def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def membre_reunion_famille(f="f", i="I", z="z"):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i).   (E.II.4.1, Déf. 1 — appartenance.)"""
    return _inst_reunion(var(f), var(i), var(z))


def membre_inter_famille(f="f", i="I", z="z"):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i).   (E.II.4.1, Déf. 2 — appartenance.)"""
    return _inst_inter(var(f), var(i), var(z))


def reunion_famille_intro(f="f", i="I", a="a", z="z"):
    """⊢ ((a∈I) et (z∈X_a)) ⇒ (z ∈ ⋃_{ι∈I} X_ι).   (un élément d'un X_a est dans ⋃.)"""
    vf, vI, va, vz = var(f), var(i), var(a), var(z)
    body = et(appartient(va, vI), appartient(vz, E.valeur_famille(vf, va)))
    h = N.assume(body)
    # (a∈I et z∈X_a) ⇒ (∃i)(i∈I et z∈X_i)   par S5 (témoin a)
    inner = et(appartient(var("i"), vI), appartient(vz, E.valeur_famille(vf, var("i"))))
    ex = N.modus_ponens(h, N.s5(inner, va, "i"))                  # (∃i)(i∈I et z∈X_i)
    zU = N.modus_ponens(ex, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    return N.loi_deduction(body, zU)


def inter_famille_elim(f="f", i="I", a="a", z="z"):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇒ ((a∈I) ⇒ (z∈X_a)).   (l'intersection est incluse dans chaque X_a.)"""
    vf, vI, va, vz = var(f), var(i), var(a), var(z)
    h = N.assume(appartient(vz, E.inter_famille(vf, vI)))
    forall = N.modus_ponens(h, equivalence_avant(_inst_inter(vf, vI, vz)))   # (∀i)(i∈I⇒z∈X_i)
    inst = instancie(forall, va)                       # (a∈I ⇒ z∈X_a)
    return N.loi_deduction(appartient(vz, E.inter_famille(vf, vI)), inst)


def monotonie_reunion_famille(f="f", g="g", i="I"):
    """⊢ ((∀i)(X_i ⊂ Y_i)) ⇒ (⋃_{ι∈I} X_ι ⊂ ⋃_{ι∈I} Y_ι).   (§II.4.2, monotonie de ⋃.)

    X_i = valeur_famille(f,i), Y_i = valeur_famille(g,i)."""
    vf, vg, vI, vz, vi = var(f), var(g), var(i), var("z"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    h = N.assume(hyp)
    incl_i = instancie(h, vi)                          # X_i ⊂ Y_i  = (∀z')(z'∈X_i ⇒ z'∈Y_i)
    zXi_zYi = instancie(incl_i, vz)                    # z∈X_i ⇒ z∈Y_i
    # (i∈I et z∈X_i) ⇒ (i∈I et z∈Y_i)
    inner = et(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    hi = N.assume(inner)
    conc = conjonction_intro(conjonction_elim_gauche(hi),
                             N.modus_ponens(conjonction_elim_droite(hi), zXi_zYi))
    step = N.loi_deduction(inner, conc)                # {hyp} ⊢ inner ⇒ inner'
    mono = monotonie_existe(step, "i")                 # (∃i …X) ⇒ (∃i …Y)
    z_imp = syllogisme(equivalence_avant(_inst_reunion(vf, vI, vz)),
                       syllogisme(mono, equivalence_arriere(_inst_reunion(vg, vI, vz))))
    gen = N.generalisation("z", z_imp)                 # {hyp} ⊢ ⋃X ⊂ ⋃Y
    return N.loi_deduction(hyp, gen)


def monotonie_inter_famille(f="f", g="g", i="I"):
    """⊢ ((∀i)(X_i ⊂ Y_i)) ⇒ (⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈I} Y_ι).   (§II.4.2, monotonie de ⋂.)"""
    vf, vg, vI, vz, vi = var(f), var(g), var(i), var("z"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    h = N.assume(hyp)
    incl_i = instancie(h, vi)                          # X_i ⊂ Y_i
    zXi_zYi = instancie(incl_i, vz)                    # z∈X_i ⇒ z∈Y_i
    # (i∈I ⇒ z∈X_i) ⇒ (i∈I ⇒ z∈Y_i)
    inner = impl(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    hi = N.assume(inner)
    # construire (i∈I ⇒ z∈Y_i) à partir de (i∈I ⇒ z∈X_i)
    hii = N.assume(appartient(vi, vI))
    zYi = N.modus_ponens(N.modus_ponens(hii, hi), zXi_zYi)        # {inner, i∈I} ⊢ z∈Y_i
    inner_imp = N.loi_deduction(inner, N.loi_deduction(appartient(vi, vI), zYi))
    mono = monotonie_pour_tout(inner_imp, "i")         # (∀i …X) ⇒ (∀i …Y)
    z_imp = syllogisme(equivalence_avant(_inst_inter(vf, vI, vz)),
                       syllogisme(mono, equivalence_arriere(_inst_inter(vg, vI, vz))))
    gen = N.generalisation("z", z_imp)
    return N.loi_deduction(hyp, gen)


def reunion_famille_vide(f="f"):
    """⊢ ⋃_{ι∈∅} X_ι = ∅.   (note de la Déf. 1 : réunion sur l'ensemble d'indices vide.)"""
    vf, vz, vi = var(f), var("z"), var("i")
    # ¬(i∈∅ et z∈X_i) pour tout i, donc ¬(∃i)(…), donc ¬(z∈⋃)
    body = et(appartient(vi, E.VIDE), appartient(vz, E.valeur_famille(vf, vi)))
    n_body = N.modus_ponens(vide_sans_element("i"),
        contraposition(projection_gauche(appartient(vi, E.VIDE),
                                         appartient(vz, E.valeur_famille(vf, vi)))))  # ¬body
    n_ex = N.modus_ponens(N.generalisation("i", n_body),
                          contraposition(monotonie_existe(dni(body), "i")))
    nz = N.modus_ponens(n_ex, contraposition(equivalence_avant(
        _inst_reunion(vf, E.VIDE, vz))))                # ¬(z∈⋃_{∅})
    return N.modus_ponens(N.generalisation("z", nz),
        equivalence_arriere(vide_ssi_sans_element(E.reunion_famille(vf, E.VIDE))))


__all__ = ["membre_reunion_famille", "membre_inter_famille",
           "reunion_famille_intro", "inter_famille_elim",
           "monotonie_reunion_famille", "monotonie_inter_famille",
           "reunion_famille_vide"]
