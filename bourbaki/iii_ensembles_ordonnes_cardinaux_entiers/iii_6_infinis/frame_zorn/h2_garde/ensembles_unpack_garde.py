# -*- coding: utf-8 -*-
"""§III.6.3 — OUVRIR LE MAXIMAL SANS PAYER SON PRIX (règle perf).

🎯 CIBLE :

    unpack_sous_maximal(E, derive) :
        { (∃m) element_maximal(Γ𝔉,𝔉,m) }  ∪  résidus de `derive`  ⊢  C

C'est `unpack_maximal` (assemblage_vrai) avec l'existence du maximal portée
en HYPOTHÈSE au lieu d'être appelée : les trois données du maximal (sa
bijection φ₀, S₀⊂E, S₀ infini, et la maximalité elle-même) sont fournies à
`derive` dans une portée fraîche, et les témoins éliminés à la sortie.

Pourquoi cette variante : `hess_maximal` (certifié cette nuit) prouve
l'existence du maximal, mais coûte 1 h 25 de dérivation.  Le porter en
hypothèse ici et ne le décharger qu'au tout dernier étage rend tout
l'assemblage du CLAIM testable en quelques secondes — c'est exactement la
règle « un gros lemme clos devient une hypothèse, déchargée une seule fois ».

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, appartient, inclus, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final import (
    _frame_membre_t_named,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def existence_maximal(E_set="E", m="mmx"):
    """L'hypothèse portée : (∃m) element_maximal( Γ𝔉(E), 𝔉(E), m ).

    Prouvée par `hess_maximal` sous « E infini » et l'énoncé du recollement."""
    vE = _t(E_set)
    return existe(m, element_maximal(frame_ordre(vE), frame_pair(vE), var(m), "x"))


def unpack_sous_maximal(E_set, derive, mfresh="mmx", Sf="Smx", phif="phimx"):
    """{ existence_maximal(E) } ∪ résidus(derive) ⊢ C.

    `derive(bij0, S0_inclus, S0_infini, maximal_hyp, vS0, vphi0, m_egal_couple)`
    reçoit les quatre données du maximal PLUS l'égalité m=(S₀,φ₀) — celle-ci
    permet de transporter par Leibniz les énoncés portant sur m (maximalité,
    appartenance à 𝔉) vers leur forme en (S₀,φ₀).  Sa conclusion C ne doit
    mentionner librement ni Sf, ni phif, ni mfresh."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    vm, vS0, vphi0 = var(mfresh), var(Sf), var(phif)
    SxS = E.produit(vS0, vS0)

    max_m = element_maximal(Gam, Fr, vm, "x")
    h_max = N.assume(max_m)
    m_in_Fr = conjonction_elim_gauche(h_max)                # mmx ∈ 𝔉(E)

    body_fresh = et(et(et(egal(vm, E.couple(vS0, vphi0)), inclus(vS0, vE)),
                       est_infini_ensemble(vS0)),
                    est_bijection_de(vphi0, SxS, vS0))

    def inner(b):
        hh = N.assume(b)
        bij0 = conjonction_elim_droite(hh)
        S_inf = conjonction_elim_droite(conjonction_elim_gauche(hh))
        S_inc = conjonction_elim_droite(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))                   # mmx = (S₀,φ₀)
        res_C = derive(bij0, S_inc, S_inf, h_max, vS0, vphi0, p_eq)
        for bad in (Sf, phif, mfresh):
            assert bad not in libres_f(res_C.conclusion), \
                "unpack_sous_maximal : %r libre dans la conclusion" % bad
        return N.loi_deduction(b, res_C)

    imp_C = inner(body_fresh)
    imp_exS = existe_elimination(existe_elimination(imp_C, phif), Sf)
    decl = N.modus_ponens(m_in_Fr,
                          equivalence_avant(_frame_membre_t_named(vE, vm, Sf, phif)))
    C_thm = N.modus_ponens(decl, imp_exS)                   # sous h_max ⊢ C
    imp_exm = existe_elimination(N.loi_deduction(max_m, C_thm), mfresh)
    res = N.modus_ponens(N.assume(existence_maximal(E_set, mfresh)), imp_exm)

    assert res.conclusion == C_thm.conclusion, "unpack_sous_maximal : conclusion"
    assert existence_maximal(E_set, mfresh) in res.hypotheses, \
        "unpack_sous_maximal : l'existence du maximal doit rester en hypothèse"
    return res


__all__ = ["existence_maximal", "unpack_sous_maximal"]
