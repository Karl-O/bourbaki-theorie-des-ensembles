"""§III.7.6 Prop. 6, 1° — EXISTENCE de u : la relation (24) est RÉALISÉE.

────────────────────────────────────────────────────────────────────────────────
Le couronnement du 1° : l'application déduite du recollement v par passage au
quotient — CONSTRUITE par C57 (ii_6_5_decomposition, témoin canonique τ, sans
axiome du choix) — vérifie exactement (24) :

    H := graphe_terme( E, v(τz(t = p(z))), t )        (p = canonique G → E=G/R)

  { v compatible avec R,  p caractérise R,  p(x)∈E,
    v coïncide avec u_{λ(·)} sur G,  λ(x)=α,  α∈I, x∈E_α, x∈G }
      ⊢  H( f_α(x) )  =  u_α(x)                                       (24)

car f_α(x) EST valeur(p, x) : la canonique inductive est la restriction de p.
Chaîne : H(f_α(x)) = H(p(x)) = v(x) [C57] = u_{λ(x)}(x) [coïncidence]
= u_α(x) [λ(x)=α].  Plus AUCUN report : l'hypothèse « v compatible avec R »
est elle-même DÉMONTRÉE par `compatible_v_coherence` (ev. 141) dès que les
gardes d'appartenance sont fournies — cf. sa docstring.
Avec prop6_unicite (1°), prop6_surjectif (2°) et prop6_injectif (3°), la
Proposition 6 de E III.62 est intégralement formalisée.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_c57_passage_quotient import (
    c57_application_deduite, graphe_deduit,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_assemblage import (
    hyp_v_coincide_graphe, hyp_lambda_indice,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §7.6 Prop.6 | E III.62 L.30-33 | PDF p.165  (Prop. 6, 1° EXISTENCE : l'application déduite du recollement vérifie u_α = u∘f_α — plus aucun report, C57 étant démontré)
def prop6_existence(v="vr", uf="uf", Efam="E", f="f", i="I", somme=None,
                    gleq=None, leq=None, a="ai", x="xi", t="t", z="zq"):
    """{ v compatible avec R, p caractérise R, p(x)∈E, v coïncide, λ(x)=α,
        α∈I, x∈E_α, x∈G } ⊢ H( f_α(x) ) = u_α(x).            [(24) RÉALISÉE]."""
    if leq is None:
        leq = C._gleq()
    vv, vuf, vE, vf, vi = _t(v), _t(uf), _t(Efam), _t(f), _t(i)
    vG = E.somme_famille(vE, vi) if somme is None else _t(somme)
    va, vx = var(a), var(x)
    p = C.f_canon_ind(vE, vf, vi, gleq)                # p : G → G/R
    lim = C.lim_ind(vE, vf, vi, gleq)                  # E = G/R
    R = C.coherence_rel(vf, leq, vi, g="gc")
    H = graphe_deduit(vv, p, lim, vG, t, z)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    lx = C.lambda_indice(vx)

    # (1) C57 : H( p(x) ) = v(x)          [3 hyps : v compatible, p caractérise, p(x)∈E]
    c57 = c57_application_deduite(vv, p, lim, vG, R, x, t, z)
    # (2) v(x) = u_{λ(x)}(x)              [recollement]
    hv = N.assume(hyp_v_coincide_graphe(vv, vuf, vG))
    hxG = N.assume(appartient(vx, vG))
    vx_eq = N.modus_ponens(hxG, instancie(hv, vx))
    # (3) u_{λ(x)}(x) = u_α(x)            [λ(x)=α sur E_α]
    hl = N.assume(hyp_lambda_indice(vE, vi))
    ha = N.assume(appartient(va, vi))
    hx = N.assume(appartient(vx, E.valeur_famille(vE, va)))
    lam = N.modus_ponens(conjonction_intro(ha, hx),
                         instancie(instancie(hl, va), vx))
    cong_u = N.modus_ponens(lam, congruence_terme(
        lx, va, E.valeur(C.u_indice(vuf, var("w6e")), vx), w="w6e"))

    res = composer_egalites(composer_egalites(c57, vx_eq), cong_u)
    cible = egal(E.valeur(H, fa_x), E.valeur(C.u_indice(vuf, va), vx))
    assert res.conclusion == cible, "prop6_existence : ≠ (24) réalisée"
    assert len(res.hypotheses) == 8, "prop6_existence : hyps ≠ 8"
    return res


__all__ = ["prop6_existence"]
