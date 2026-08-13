#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BIBLIOTHÈQUE de notions APPRISES — auto-générée par flywheel.py (JALON 2).

Chaque tactique dérivée ci-dessous a été INVENTÉE par anti-unification d'un motif
récurrent, NOMMÉE, et CERTIFIÉE par le noyau (gate MDL : re-prouve ≥2 théorèmes
identiquement, corpus strictement plus court, zéro théorème faux). Injectée dans le
namespace du module-preuve à l'usage (comme le fait le gate). Ne PAS éditer à la main.
Tour généré le 2026-08-08 — 18 notions, gain MDL total ≈80 pas.
"""


# notion réutilisée dans 21 preuves (noyau OK) : caracterisation_couple, produit_egalite_par_couples, produit_distrib_reunion_premier_facteur_ensembliste, produit_inter_ensembliste, image_image_reciproque_inclus, image_reciproque_image_inclus_si_injective, pr1_reciproque_produit, composee_bijectives, retraction_implique_injective, retraction_construite_par_tau, theoreme1_c_injective, surjective_image_donne_valeur, theoreme1_e_injective_valeur, theoreme1_f_injective_valeur, image_reciproque_inter_binaire, image_reciproque_difference, image_inter_inclusion, image_difference_injective, sature_partie_saturee, b_surjective_valeurs, relation_induite_transitive
def notion_conjonction_elim_gauche_2p_10(p0, SLOT0):
    _v0 = conjonction_elim_gauche(SLOT0)
    _v1 = conjonction_elim_droite(SLOT0)
    return (_v0, _v1)

# notion réutilisée dans 10 preuves (noyau OK) : inclus_image_reciproque_image, prop9a_factorisation_valeur, prop9b_factorisation_valeur, reciproque_compose_identite_valeur, section_compose_valeur, section_construite_par_tau, section_implique_surjective_valeur, theoreme1_a_retraction_valeur, theoreme1_d_surjective_valeur, theoreme1_b_section_valeur
def notion_instancie_3p_24(p0, p1, p2):
    _v0 = instancie(p0, p1)
    _v1 = N.assume(appartient(p1, p2))
    _v2 = N.modus_ponens(_v1, _v0)
    return (_v0, _v1, _v2)

# notion réutilisée dans 5 preuves (noyau OK) : pr1_reciproque_produit, image_reciproque_inter_binaire, image_reciproque_difference, image_inter_inclusion, image_difference_injective
def notion_assume_4p_53(p0, p1, p2, p3, p4, SLOT0, SLOT1):
    _v0 = N.assume(appartient(p0, p1))
    _v1 = N.modus_ponens(_v0, equivalence_avant(SLOT0))
    _v2 = N.assume(SLOT1)
    _v3 = conjonction_elim_gauche(_v2)
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 4 preuves (noyau OK) : image_reciproque_inter_binaire, image_reciproque_difference, image_inter_inclusion, image_difference_injective
def notion_appartient_4p_83(p0, p1, p2, p3, p4, SLOT0, SLOT1):
    _v0 = lambda u: appartient(E.couple(u, SLOT0), SLOT1)
    _v1 = lambda u: et(appartient(u, p2), _v0(u))
    _v2 = lambda u: et(appartient(u, p3), _v0(u))
    _v3 = lambda u: et(appartient(u, p4), _v0(u))
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 4 preuves (noyau OK) : fini_somme_cardinal, fini_somme_successeur, fini_somme_cardinal_successeur, prop2_sous_somme_finie
def notion_SC_4p_84(p0, p1, SLOT0):
    _v0, _v1 = (var(p0), var(p1))
    _v2 = SC(_v0, _v1)
    _v3 = N.assume(et(est_fini(_v0), est_fini(_v1)))
    _v4 = mp(_v3, SLOT0(p0, p1))
    return (_v0, _v1, _v2, _v3, _v4)

# notion réutilisée dans 3 preuves (noyau OK) : image_reciproque_difference, image_difference_injective, sature_partie_saturee
def notion_assume_4p_134(p0, p1, p2, SLOT0, SLOT1):
    _v0 = N.assume(SLOT0)
    _v1 = conjonction_elim_gauche(_v0)
    _v2 = conjonction_elim_droite(_v0)
    _v3 = N.assume(SLOT1(p1, p2))
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 3 preuves (noyau OK) : image_image_reciproque_inclus, image_reciproque_image_inclus_si_injective, image_image_reciproque_contient_si_surjective
def notion_et_4p_140(p0, p1, p2, p3, p4, p5, SLOT0):
    _v0 = lambda u: et(appartient(u, p0), appartient(E.couple(u, p2), p1))
    _v1 = N.modus_ponens(p3, equivalence_avant(p4))
    _v2 = N.modus_ponens(_v1, equivalence_avant(alpha_existe('x', SLOT0, _v0(var('x')))))
    _v3 = N.assume(_v0(p5))
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 4 preuves (noyau OK) : image_reciproque_inter_binaire, image_reciproque_difference, image_inter_inclusion, image_difference_injective
def notion_appartient_3p_150(p0, p1, p2, p3, SLOT0, SLOT1):
    _v0 = lambda u: appartient(E.couple(u, SLOT0), SLOT1)
    _v1 = lambda u: et(appartient(u, p2), _v0(u))
    _v2 = lambda u: et(appartient(u, p3), _v0(u))
    return (_v0, _v1, _v2)

# notion réutilisée dans 4 preuves (noyau OK) : image_reciproque_inter_binaire, image_reciproque_difference, image_inter_inclusion, image_difference_injective
def notion_et_3p_151(p0, p1, p2, p3):
    _v0 = lambda u: et(appartient(u, p0), p1(u))
    _v1 = lambda u: et(appartient(u, p2), p1(u))
    _v2 = lambda u: et(appartient(u, p3), p1(u))
    return (_v0, _v1, _v2)

# notion réutilisée dans 3 preuves (noyau OK) : image_reciproque_inter_binaire, image_reciproque_difference, image_difference_injective
def notion_assume_4p_152(p0, p1, p2, p3, SLOT0, SLOT1):
    _v0 = N.assume(SLOT0(p0))
    _v1 = lambda u: appartient(E.couple(u, p1), SLOT1)
    _v2 = lambda u: et(appartient(u, p2), _v1(u))
    _v3 = lambda u: et(appartient(u, p3), _v1(u))
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 4 preuves (noyau OK) : fini_somme_cardinal, fini_somme_successeur, fini_somme_cardinal_successeur, prop2_sous_somme_finie
def notion_SC_3p_155(p0, p1):
    _v0, _v1 = (var(p0), var(p1))
    _v2 = SC(_v0, _v1)
    _v3 = N.assume(et(est_fini(_v0), est_fini(_v1)))
    return (_v0, _v1, _v2, _v3)

# notion réutilisée dans 4 preuves (noyau OK) : fini_somme_cardinal, fini_somme_successeur, fini_somme_cardinal_successeur, prop2_sous_somme_finie
def notion_SC_3p_156(p0, p1, p2, p3, SLOT0):
    _v0 = SC(p0, p1)
    _v1 = N.assume(et(est_fini(p0), est_fini(p1)))
    _v2 = mp(_v1, SLOT0(p2, p3))
    return (_v0, _v1, _v2)

# notion réutilisée dans 5 preuves (noyau OK) : section_implique_surjective_valeur, theoreme1_a_retraction_valeur, theoreme1_d_surjective_valeur, theoreme1_b_section_valeur, theoreme1_f_retraction_valeur
def notion_modus_ponens_2p_168(p0, p1, p2, p3):
    _v0 = N.modus_ponens(p0, p1)
    _v1 = E.valeur(p2, p3)
    return (_v0, _v1)

# notion réutilisée dans 3 preuves (noyau OK) : disjonction_complement, sup_universel_binaire, recouvrement_complement
def notion_loi_deduction_3p_175(p0, p1, p2, p3):
    _v0 = N.loi_deduction(p0, p1)
    _v1 = N.assume(p2)
    _v2 = instancie(_v1, p3)
    return (_v0, _v1, _v2)

# notion réutilisée dans 3 preuves (noyau OK) : image_image_reciproque_inclus, image_reciproque_image_inclus_si_injective, image_reciproque_inter_binaire
def notion_existe_elimination_3p_187(p0, p1, p2, p3, p4, p5, SLOT0, SLOT1):
    _v0 = existe_elimination(N.loi_deduction(p1(p2), p0), SLOT0)
    _v1 = N.modus_ponens(p3, _v0)
    _v2 = existe_elimination(N.loi_deduction(p4(p5), _v1), SLOT1)
    return (_v0, _v1, _v2)

# notion réutilisée dans 3 preuves (noyau OK) : image_image_reciproque_contient_si_surjective, image_reciproque_inclus_domaine, reciproque_intersection_image
def notion_assume_3p_188(p0, p1, p2, p3, SLOT0, SLOT1):
    _v0 = N.assume(SLOT0)
    _v1 = conjonction_elim_droite(_v0)
    _v2 = N.modus_ponens(_v1, SLOT1)
    return (_v0, _v1, _v2)

# notion réutilisée dans 3 preuves (noyau OK) : theoreme1_a_retraction_valeur, theoreme1_b_section_valeur, theoreme1_f_retraction_valeur
def notion_instancie_3p_195(p0, p1, p2, p3, p4):
    _v0 = instancie(p0, p1)
    _v1 = N.modus_ponens(p2, _v0)
    _v2 = E.valeur(p3, p4)
    return (_v0, _v1, _v2)

# notion réutilisée dans 3 preuves (noyau OK) : image_reciproque_inter_binaire, image_reciproque_difference, image_difference_injective
def notion_assume_3p_196(p0, p1, p2, SLOT0, SLOT1):
    _v0 = N.assume(SLOT0(p0))
    _v1 = lambda u: appartient(E.couple(u, p1), SLOT1)
    _v2 = lambda u: et(appartient(u, p2), _v1(u))
    return (_v0, _v1, _v2)
