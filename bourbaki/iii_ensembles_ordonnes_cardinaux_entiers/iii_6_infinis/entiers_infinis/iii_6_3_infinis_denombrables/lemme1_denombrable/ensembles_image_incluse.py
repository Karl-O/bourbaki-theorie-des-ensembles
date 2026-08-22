# -*- coding: utf-8 -*-
"""§III.6.3 — K6f : L'IMAGE DE L'ITÉRÉE VIT DANS E.

🎯 CIBLE (g := le témoin gcap via le corps FORT ; D := g⟨ℕ⟩) :

    image_incluse :
        { corps_c63_fort(S_c, x0),  x0∈E,  u⊂E×E,  dom u=E }
            ⊢ g⟨ℕ⟩ ⊂ E                                            [4 hyps]

Point à point : z∈g⟨ℕ⟩ donne (AXIOME_IMAGE) un témoin x∈ℕ avec (x,z)∈g ;
la fonctionnalité (du corps fort) fait z = g(x) (C46), et valeurs_dans_E
(K6c) place g(x) dans E ; Leibniz conclut z∈E, l'élimination du témoin et
la généralisation referment l'inclusion.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_union_rec import (
    _valeur_depuis_couple,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63, corps_c63_fort,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    regle_clampee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_valeurs_iteration import (
    _cut, valeurs_dans_E,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def image_incluse(u, x0, e, g="gcap", zname="zcl", yname="ycl", z="z"):
    """🎯 K6f : { corps_c63_fort(S_c,x0), x0∈E, u⊂E×E, dom u=E } ⊢ g⟨ℕ⟩ ⊂ E
       [4 hyps — le corps FORT porte la fonctionnalité ET décharge le faible]."""
    vu, vx0, ve, vg, vz = _t(u), _t(x0), _t(e), _t(g), var(z)
    NN = ensemble_NN()
    _, S_c = regle_clampee(u, x0, e, zname, yname)
    D = E.image(vg, NN)

    h_fort = N.assume(corps_c63_fort(S_c, vx0, g=g))        # corps FORT [HONNÊTE]
    func = conjonction_elim_gauche(conjonction_elim_gauche(h_fort))
    corps_faible = conjonction_elim_droite(h_fort)
    vals = _cut(corps_faible, corps_c63(S_c, vx0, g=g),
                valeurs_dans_E(u, x0, e, g, zname, yname))  # (∀n∈ℕ)(g(n)∈E)

    h_z = N.assume(appartient(vz, D))                       # z∈g⟨ℕ⟩
    ex = N.modus_ponens(h_z, equivalence_avant(membre_image(vg, NN, vz)))
    vx = var("x")                                           # le liant de l'axiome
    corps_wit = et(appartient(vx, NN), appartient(E.couple(vx, vz), vg))
    h_w = N.assume(corps_wit)
    x_in = conjonction_elim_gauche(h_w)
    cpl = conjonction_elim_droite(h_w)                      # (x,z)∈g
    val_eq = _valeur_depuis_couple(vg, vx, vz, cpl, func)   # z = g(x)
    gx_in = N.modus_ponens(x_in, instancie(vals, vx))       # g(x)∈E
    z_in = N.modus_ponens(gx_in, equivalence_arriere(N.modus_ponens(
        val_eq, N.s6(vz, E.valeur(vg, vx), "wim",
                     appartient(var("wim"), ve)))))         # z∈E
    exi = existe_elimination(N.loi_deduction(corps_wit, z_in), "x")
    z_in_final = N.modus_ponens(ex, exi)
    res = N.generalisation(z, N.loi_deduction(appartient(vz, D), z_in_final))
    assert res.conclusion == inclus(D, ve), "image_incluse : forme"
    assert len(res.hypotheses) == 4, "image_incluse : hyps ≠ 4"
    return res


__all__ = ["image_incluse"]
