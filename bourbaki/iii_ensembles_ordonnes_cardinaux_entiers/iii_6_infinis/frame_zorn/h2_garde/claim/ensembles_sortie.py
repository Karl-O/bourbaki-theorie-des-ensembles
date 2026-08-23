# -*- coding: utf-8 -*-
"""§III.6.3 — LA CONTRADICTION DE BOURBAKI, PUIS LA SORTIE DE PORTÉE.

🎯 CIBLES :

    u_non_vide          : { Card U = Card S₀, S₀ infini } ⊢ ¬( U = ∅ )
    non_strict_sous_garde : { paquet, U⊂E∖S₀, Card U=Card S₀, S₀ infini,
                              données du maximal } ⊢ ¬( Card S₀ < Card E )

L'argument de Bourbaki abouti (E.III.48-49) : sous l'hypothèse de l'absurde,
la bijection étendue φ₁ = φ₀ ∪ ψ contredit la maximalité de (S₀,φ₀).  Ici la
contradiction prend la forme la plus commode pour sortir de la portée :

  • STEP 5 donne ¬(u∈U) pour un u ARBITRAIRE ; comme u n'est libre dans aucune
    hypothèse (le témoin u∈U est d'abord déchargé par S1), on GÉNÉRALISE :
    (∀u)¬(u∈U), c'est-à-dire U = ∅ ;
  • mais U est équipotent à S₀, qui est infini, donc U ≠ ∅.

De « U=∅ et U≠∅ » on tire n'importe quoi, en particulier la NÉGATION de
l'hypothèse de l'absurde — et cette conclusion-là ne mentionne ni U, ni ψ, ni
u, ce qui rend licites les trois éliminations de témoins qui suivent.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, appartient, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    contraposition, equivalence_avant, equivalence_arriere,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    vide_ssi_sans_element,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, est_fini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_props import (
    _refuter,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_paquet import (
    contradiction_sous_paquet,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.29-30 | PDF p.151  (Y équipotente à F, donc non vide)
def u_non_vide(E_set="E", S="S0", U="Ucadre"):
    """{ Card U = Card S₀, S₀ infini } ⊢ ¬( U = ∅ ).

    U a le cardinal de S₀, qui est infini : U est donc infini lui aussi
    (Leibniz sur les cardinaux), et le vide, lui, est FINI (`fini_zero`)."""
    vS, vU = _t(S), _t(U)
    cU, cS = cardinal(vU), cardinal(vS)
    h_card = N.assume(egal(cU, cS))                          # Card U = Card S₀
    h_inf = N.assume(est_infini_ensemble(vS))                # ¬Fini(Card S₀)

    #  Fini(Card U) ⇒ Fini(Card S₀), donc ¬Fini(Card S₀) ⇒ ¬Fini(Card U)
    equiv_fini = N.modus_ponens(h_card, N.s6(cU, cS, "wfi", est_fini(var("wfi"))))
    inf_U = N.modus_ponens(h_inf, contraposition(equivalence_avant(equiv_fini)))
    assert inf_U.conclusion == est_infini_ensemble(vU), "u_non_vide : U infini"

    #  sous « U = ∅ » : U hérite de la finitude du vide
    equiv_vide = N.modus_ponens(N.assume(egal(vU, E.VIDE)),
                                N.s6(vU, E.VIDE, "wse", est_fini_ensemble(var("wse"))))
    fini_U = N.modus_ponens(fini_zero(), equivalence_arriere(equiv_vide))

    res = _refuter(egal(vU, E.VIDE), fini_U, inf_U)
    assert res.conclusion == non(egal(vU, E.VIDE)), "u_non_vide : forme"
    assert len(res.hypotheses) == 2, "u_non_vide : hyps ≠ 2"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.49 L.3-5 | PDF p.152
#   (« ce qui est contraire à la définition de f » — l'absurde est atteint)
def non_strict_sous_garde(E_set="E", S="S0", phi0="phi0", psi="psi",
                          U="Ucadre", u="z"):
    """{ paquet, U⊂E∖S₀, Card U=Card S₀, S₀ infini, données du maximal }
           ⊢ ¬( Card S₀ < Card E ).

    ⚠️ Le témoin u est nommé « z » à dessein : après généralisation, le liant
    doit être celui de `vide_ssi_sans_element` (fixé à z par extensionnalité).

    La conclusion ne mentionne NI U, NI ψ, NI u — c'est la condition pour que
    les éliminations de témoins qui suivent soient licites."""
    vE, vS, vU, vu = _t(E_set), _t(S), _t(U), var(u)
    step5 = contradiction_sous_paquet(E_set, S, phi0, psi, U, u)
    temoin = appartient(vu, vU)

    #  décharger le témoin : de « u∈U ⇒ ¬(u∈U) » vient ¬(u∈U) tout court (S1)
    sans_temoin = N.modus_ponens(N.loi_deduction(temoin, step5), N.s1(non(temoin)))
    for h in sans_temoin.hypotheses:
        assert u not in libres_f(h), \
            "non_strict_sous_garde : %r libre dans une hypothèse (généralisation)" % u
    vide = N.modus_ponens(N.generalisation(u, sans_temoin),
                          equivalence_arriere(vide_ssi_sans_element(vU)))  # U = ∅

    absurde = inf_strict_card(cardinal(vS), cardinal(vE))
    res = _refuter(absurde, vide, u_non_vide(E_set, S, U))

    assert res.conclusion == non(absurde), "non_strict_sous_garde : forme"
    for nom in (U if isinstance(U, str) else U.nom,
                psi if isinstance(psi, str) else psi.nom, u):
        assert nom not in libres_f(res.conclusion), \
            "non_strict_sous_garde : %r libre dans la conclusion" % nom
    return res


__all__ = ["u_non_vide", "non_strict_sous_garde"]
