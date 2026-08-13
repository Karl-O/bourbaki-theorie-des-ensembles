"""§III.7.6 Prop. 6, 1° — l'assemblage : de v = h∘p à la relation (24).

────────────────────────────────────────────────────────────────────────────────
Dernier maillon du 1° : SI h est déduite de v par passage au quotient (le
prédicat v = h∘p de E II.6.5), ALORS h vérifie exactement la relation (24) :

  { v = h∘p,  v coïncide avec u_{λ(x)} sur G,  λ(x)=α sur E_α,
    α∈I, x∈E_α, x∈G, + les 3 hyps de composition_valeur_t }
      ⊢  h( f_α(x) ) = u_α(x)                                        (24)

car f_α(x) EST valeur(p, x) (f_canon_ind = application canonique de G sur G/R),
donc h(f_α(x)) = (h∘p)(x) = v(x) = u_{λ(x)}(x) = u_α(x).

⚠️ CE QUI RESTE : l'EXISTENCE de h, c'est-à-dire le critère **C57** (E II.44)
« f compatible avec R ⇒ f se met sous la forme h∘p » — REPORTÉ AU CHAPITRE II
(cf. application_deduite_quotient : « L'existence/unicité effective de h
(h = f∘s) est REPORTÉE (Critère C57) »).  Le mur de la Prop. 6 1° n'est donc
PAS dans III.7 : il est en amont, dans le passage au quotient de II.6.5.
Ici v, h, p sont des GRAPHES (convention de application_deduite_quotient).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    composition_valeur_t,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ensembles_quotient_complements import (
    application_deduite_quotient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites_canoniques as C,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def hyp_v_coincide_graphe(v, uf, somme, x="xi"):
    """(∀x)( x∈G ⇒ valeur(V,x) = u_{λ(x)}(x) )  — V = GRAPHE du recollement v."""
    vv, vuf, vG, vx = _t(v), _t(uf), _t(somme), var(x)
    return pourtout(x, impl(appartient(vx, vG),
                            egal(E.valeur(vv, vx),
                                 E.valeur(C.u_indice(vuf, C.lambda_indice(vx)), vx))))


def hyp_lambda_indice(Efam, i, a="ai", x="xi"):
    """(∀a)(∀x)( (a∈I et x∈E_a) ⇒ λ(x) = a )  — l'indice d'un élément de E_α est α."""
    vE, vi, va, vx = _t(Efam), _t(i), var(a), var(x)
    return pourtout(a, pourtout(x, impl(
        et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va))),
        egal(C.lambda_indice(vx), va))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.30-33 | PDF p.165  (assemblage du 1° : l'application déduite par passage au quotient vérifie (24) — CLOS modulo C57, report du chapitre II)
def relation_24_modulo_c57(h="h", v="v", uf="uf", Efam="E", f="f", i="I",
                           somme=None, gleq=None, a="ai", x="xi"):
    """{ v=h∘p, v coïncide, λ(x)=α, α∈I, x∈E_α, x∈G, composition }
        ⊢ h( f_α(x) ) = u_α(x).                          [(24), modulo C57]."""
    vh, vv, vuf = _t(h), _t(v), _t(uf)
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    vG = E.somme_famille(vE, vi) if somme is None else _t(somme)
    va, vx = var(a), var(x)
    p = C.f_canon_ind(vE, vf, vi, gleq)                # p : G → G/R
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    lx = C.lambda_indice(vx)

    hq = N.assume(application_deduite_quotient(vv, p, vh))   # V = H∘P
    hv = N.assume(hyp_v_coincide_graphe(vv, vuf, vG))
    hl = N.assume(hyp_lambda_indice(vE, vi))
    ha = N.assume(appartient(va, vi))
    hx = N.assume(appartient(vx, E.valeur_famille(vE, va)))
    hxG = N.assume(appartient(vx, vG))

    cv = composition_valeur_t(vh, p, vx)               # (H∘P)(x) = H(P(x))  [3 hyps]
    cong = N.modus_ponens(hq, congruence_terme(
        vv, E.composee(vh, p), E.valeur(var("w6q"), vx), w="w6q"))
    #     V(x) = (H∘P)(x)
    vx_eq = N.modus_ponens(hxG, instancie(hv, vx))     # V(x) = u_{λx}(x)
    lam = N.modus_ponens(conjonction_intro(ha, hx),
                         instancie(instancie(hl, va), vx))   # λ(x) = α
    cong_u = N.modus_ponens(lam, congruence_terme(
        lx, va, E.valeur(C.u_indice(vuf, var("w6u")), vx), w="w6u"))
    #     u_{λx}(x) = u_α(x)
    res = composer_egalites(composer_egalites(composer_egalites(
        N.modus_ponens(cv, symetrie(E.valeur(E.composee(vh, p), vx),
                                    E.valeur(vh, E.valeur(p, vx)))),
        N.modus_ponens(cong, symetrie(E.valeur(vv, vx),
                                      E.valeur(E.composee(vh, p), vx)))),
        vx_eq), cong_u)
    cible = egal(E.valeur(vh, fa_x), E.valeur(C.u_indice(vuf, va), vx))
    assert res.conclusion == cible, "relation_24_modulo_c57 : ≠ (24) au point"
    assert {hq.conclusion, hv.conclusion, hl.conclusion, ha.conclusion,
            hx.conclusion, hxG.conclusion} <= set(res.hypotheses), \
        "relation_24_modulo_c57 : hypothèses attendues absentes"
    return res


__all__ = ["hyp_v_coincide_graphe", "hyp_lambda_indice", "relation_24_modulo_c57"]
