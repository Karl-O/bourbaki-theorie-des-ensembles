# -*- coding: utf-8 -*-
"""§III.6.3 — K6g : LE LEMME 1 SOUS HYPOTHÈSES DEDEKIND (l'assemblage).

🎯 CIBLE (les 6 hypothèses du chantier ; D := g⟨ℕ⟩ le témoin) :

    lemme1_sous_hypotheses :
        { corps_c63_fort(S_c, x0),  x0∈E,  u⊂E×E,  dom u=E,  hors,  inj }
            ⊢ (∃D)( D ⊂ E  ∧  Eq(D, ℕ) )                          [6 hyps]

C'est l'énoncé du Lemme 1 de Bourbaki (« Tout ensemble infini E contient un
ensemble équipotent à ℕ », E III.47) MODULO les données (u, x0) de Dedekind,
que l'étape D1 construira sous est_infini(Card E).  Eq(D, ℕ) est le flip
(symétrie de l'équipotence) de Eq(ℕ, D) = K6e ; D ⊂ E est K6f ; S5 au
témoin D referme l'∃.

⚠️ Fidélité : l'énoncé colle au livre ; la DÉMONSTRATION du livre passe par
le bon ordre (isomorphisme avec un segment de ℕ), la nôtre par l'itération
de Dedekind — écart de preuve à consigner dans ANOMALIES à la clôture.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
    equipotence_symetrique,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_equipotence_image import (
    equipotence_iteree,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_image_incluse import (
    image_incluse,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Lem.1 | E III.47 L.34-35 | PDF p.150  (énoncé ; ici SOUS les
#   hypothèses Dedekind (u, x0) — la décharge sous est_infini est l'étape D1)
def lemme1_sous_hypotheses(u, x0, e, g="gcap", zname="zcl", yname="ycl",
                           D_binder="Dld"):
    """🎯 K6g : { corps_c63_fort(S_c,x0), x0∈E, u⊂E×E, dom u=E, hors, inj }
       ⊢ (∃D)( D ⊂ E ∧ Eq(D, ℕ) )   [6 hyps].

    conjonction (K6f, flip de K6e) puis S5 au témoin D := g⟨ℕ⟩."""
    vg, ve = _t(g), _t(e)
    NN = ensemble_NN()
    D = E.image(vg, NN)
    incl = image_incluse(u, x0, e, g, zname, yname)         # {4} D⊂E
    eq_nd = equipotence_iteree(u, x0, e, g, zname, yname)   # {6} Eq(ℕ,D)
    eq_dn = N.modus_ponens(eq_nd,
                           equipotence_symetrique("F", NN, D))  # Eq(D,ℕ)
    conj = conjonction_intro(incl, eq_dn)                   # D⊂E ∧ Eq(D,ℕ)
    vD = var(D_binder)
    corps = et(inclus(vD, ve), equipotent(vD, NN))
    res = N.modus_ponens(conj, N.s5(corps, D, D_binder))
    assert res.conclusion == existe(D_binder, corps), \
        "lemme1_sous_hypotheses : forme"
    assert len(res.hypotheses) == 6, "lemme1_sous_hypotheses : hyps ≠ 6"
    return res


__all__ = ["lemme1_sous_hypotheses"]
