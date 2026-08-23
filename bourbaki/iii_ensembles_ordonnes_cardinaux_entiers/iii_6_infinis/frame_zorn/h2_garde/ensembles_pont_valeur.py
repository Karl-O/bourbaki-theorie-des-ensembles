# -*- coding: utf-8 -*-
"""§III.6.3 — H2 (β) : DU NIVEAU COUPLE AU NIVEAU VALEUR pour le recollement.

🎯 CIBLE : supprimer les hypothèses VALEUR de `union_chaine_est_bijection`
(dom(⋃φ)=US×US, injective_dans, image=US) en les DÉRIVANT du niveau couple,
déjà établi par l'amont.

    dom_union_egale :
        { recollement_domaine(𝔇, US×US),  dom(⋃𝔇) ⊂ US×US }
            ⊢ dom(⋃𝔇) = US×US

Les deux briques existaient séparément — `union_chaine_dom` (couverture du
domaine, niveau couple) et `couple_domaine_implique_dom_egale` (le pont
générique) — mais avec des LIANTS différents ; alpha_bridge les raccorde,
conformément à la leçon 15 (partir des théorèmes, ponter en α, ne jamais
reconstruire).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_frame_membership import (
    union_chaine_est_bijection, union_chaine_dans_frame,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_surjective_frame import (
    union_chaine_dom, recollement_domaine, union_chaine_surjective,
    recollement_surjectif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_injectif_graphe_pont import (
    injectif_graphe_implique_injective_dans,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_ponts_couple_valeur_surj import (
    domaine_couple, couple_domaine_implique_dom_egale,
    surjectif_couple_riche, couple_surjectif_implique_image_egale,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def dom_union_egale(D="Dchaine", US="USchaine"):
    """🎯 { recollement_domaine(𝔇, US×US), dom(⋃𝔇) ⊂ US×US } ⊢ dom(⋃𝔇) = US×US.

    La couverture couple-niveau du recollement (union_chaine_dom) est
    exactement `domaine_couple` à un renommage de liants près ; le pont
    générique conclut à l'égalité des ensembles."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)

    couverture = alpha_bridge(union_chaine_dom(vD, Prod), domaine_couple(U, Prod))
    pont = couple_domaine_implique_dom_egale(U, Prod)
    res = _cut(couverture, domaine_couple(U, Prod), pont)

    assert res.conclusion == egal(E.dom(U), Prod), "dom_union_egale : forme"
    assert set(res.hypotheses) == {recollement_domaine(vD, Prod),
                                   inclus(E.dom(U), Prod)}, \
        "dom_union_egale : hyps ≠ {recollement_domaine, inclusion}"
    return res


def surj_riche(D="Dchaine", US="USchaine", w="wsr", a="asr"):
    """{ recollement_surjectif(𝔇,US), recollement_domaine, dom(⋃𝔇)⊂US×US }
       ⊢ surjectif_couple_riche( ⋃𝔇, US×US, US ).

    L'amont donne la surjectivité couple-niveau PAUVRE : tout w∈US a un
    antécédent a avec (a,w)∈⋃𝔇, sans dire où vit a.  Le pont du domaine
    (dom(⋃𝔇)=US×US) l'enrichit : (a,w)∈⋃𝔇 place a dans le domaine, donc
    dans US×US."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)
    vw, va = var(w), var(a)

    pauvre = union_chaine_surjective(vD, vUS)          # (∀w)(w∈US ⇒ (∃a)((a,w)∈⋃𝔇))
    dom_eq = dom_union_egale(D, US)                    # dom(⋃𝔇) = US×US

    h_w = N.assume(appartient(vw, vUS))
    ex_a = N.modus_ponens(h_w, instancie(alpha_bridge(pauvre, pourtout(w, impl(
        appartient(vw, vUS), existe(a, appartient(E.couple(va, vw), U))))), vw))
    corps = appartient(E.couple(va, vw), U)
    h_a = N.assume(corps)
    #   (a,w)∈⋃𝔇 ⇒ a∈dom(⋃𝔇)  (AXIOME_DOM, sens ⇐ avec témoin w)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, U), va)          # a∈dom U ⇔ (∃y)((a,y)∈U)
    ex_y = N.modus_ponens(h_a, N.s5(appartient(E.couple(va, var("y")), U), vw, "y"))
    a_dom = N.modus_ponens(ex_y, equivalence_arriere(car))
    a_prod = N.modus_ponens(a_dom, equivalence_avant(N.modus_ponens(
        dom_eq, N.s6(E.dom(U), Prod, "wpv", appartient(va, var("wpv"))))))
    wit = N.modus_ponens(conjonction_intro(a_prod, h_a),
                         N.s5(et(appartient(va, Prod), corps), va, a))
    inner = existe_elimination(N.loi_deduction(corps, wit), a)
    res_w = N.modus_ponens(ex_a, inner)
    res = N.generalisation(w, N.loi_deduction(appartient(vw, vUS), res_w))

    assert res.conclusion == surjectif_couple_riche(U, Prod, vUS, w, a),         "surj_riche : forme"
    assert len(res.hypotheses) == 3, "surj_riche : hyps ≠ 3"
    return res


def image_union_egale(D="Dchaine", US="USchaine"):
    """🎯 { recollement_surjectif, recollement_domaine, dom⊂US×US,
           image(⋃𝔇, US×US) ⊂ US } ⊢ image( ⋃𝔇, US×US ) = US.

    surj_riche fournit la surjectivité couple-niveau RICHE ; le pont générique
    (couple_surjectif_implique_image_egale) en tire l'égalité d'ensembles."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)
    riche = surj_riche(D, US)
    pont = couple_surjectif_implique_image_egale(U, Prod, vUS)
    res = _cut(riche, surjectif_couple_riche(U, Prod, vUS), pont)
    assert res.conclusion == egal(E.image(U, Prod), vUS), "image_union_egale : forme"
    assert len(res.hypotheses) == 4, "image_union_egale : hyps ≠ 4"
    return res


def inj_valeur(D="Dchaine", US="USchaine"):
    """🎯 { fonctionnel(⋃𝔇), injectif_graphe(⋃𝔇), recollement_domaine, dom⊂US×US }
       ⊢ injective_dans( ⋃𝔇, US×US ).

    Le pont générique du dépôt donne injective_dans(F, dom F) ; le pont du
    domaine identifie dom(⋃𝔇) à US×US, et Leibniz transporte."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)
    sur_dom = injectif_graphe_implique_injective_dans(U)   # injective_dans(U, dom U)
    dom_eq = dom_union_egale(D, US)                        # dom U = US×US
    res = N.modus_ponens(sur_dom, equivalence_avant(N.modus_ponens(
        dom_eq, N.s6(E.dom(U), Prod, "wij",
                     E.injective_dans(U, var("wij"))))))
    assert res.conclusion == E.injective_dans(U, Prod), "inj_valeur : forme"
    assert len(res.hypotheses) == 4, "inj_valeur : hyps ≠ 4"
    return res


def bijection_sans_valeur(D="Dchaine", US="USchaine"):
    """🎯🎯 union_chaine_est_bijection AVEC SES TROIS HYPOTHÈSES VALEUR DÉRIVÉES :
       { famille_compatible, famille_dirigee, membres_injectifs,
         recollement_surjectif, recollement_domaine,
         dom(⋃𝔇)⊂US×US, image(⋃𝔇,US×US)⊂US }
           ⊢ est_bijection_de( ⋃𝔇, US×US, US ).

    Les trois hypothèses VALEUR que le dépôt portait faute de pont
    (dom=US×US, injective_dans, image=US) sont désormais DÉRIVÉES du niveau
    couple ; il ne reste que des données couple-natives et deux inclusions."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)
    base = union_chaine_est_bijection(vD, vUS)
    base = _cut(dom_union_egale(D, US), egal(E.dom(U), Prod), base)
    base = _cut(inj_valeur(D, US), E.injective_dans(U, Prod), base)
    base = _cut(image_union_egale(D, US), E.est_surjective(U, Prod, vUS), base)
    assert base.conclusion == est_bijection_de(U, Prod, vUS),         "bijection_sans_valeur : forme"
    assert egal(E.dom(U), Prod) not in base.hypotheses,         "bijection_sans_valeur : hyp dom non déchargée"
    assert E.injective_dans(U, Prod) not in base.hypotheses,         "bijection_sans_valeur : hyp injective non déchargée"
    return base


def frame_de_recollement(D="Dchaine", US="USchaine", E_set="E"):
    """🎯🎯🎯 { données couple-natives, US⊂E, US infini, 2 inclusions }
       ⊢ ( US, ⋃𝔇 ) ∈ 𝔉(E).

    union_chaine_dans_frame avec ses TROIS hypothèses valeur déchargées par
    les ponts : le couple-recollement d'une chaîne est une frame-pair sans
    qu'aucune donnée de niveau valeur ne soit postulée."""
    vD, vUS, vE = _t(D), _t(US), _t(E_set)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)
    base = union_chaine_dans_frame(vE, vD, vUS)
    base = _cut(dom_union_egale(D, US), egal(E.dom(U), Prod), base)
    base = _cut(inj_valeur(D, US), E.injective_dans(U, Prod), base)
    base = _cut(image_union_egale(D, US), E.est_surjective(U, Prod, vUS), base)
    assert base.conclusion == appartient(E.couple(vUS, U), frame_pair(vE)),         "frame_de_recollement : forme"
    assert egal(E.dom(U), Prod) not in base.hypotheses,         "frame_de_recollement : hyp valeur non déchargée"
    return base


__all__ = ["dom_union_egale", "surj_riche", "image_union_egale", "inj_valeur",
           "bijection_sans_valeur", "frame_de_recollement"]
