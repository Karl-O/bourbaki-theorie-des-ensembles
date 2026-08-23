# -*- coding: utf-8 -*-
"""§III.6.3 — DONNÉE 7/11 : le graphe recollé atteint tout point de US.

🎯 CIBLE :

    surj_union_us : { chaine(Γ𝔉,𝔉,C) }
        ⊢ (∀w)( w ∈ US(C) ⇒ (∃p)( p ∈ 𝔇(C) et (∃a)( (a,w) ∈ p ) ) )

⚠️ Cette donnée INVERSE la mécanique des précédentes.  Les données (9) et (10)
DÉFAISAIENT une appartenance pour remonter à un membre ; celle-ci doit
PRODUIRE un témoin.  D'où deux emplois en sens ARRIÈRE : `membre_famille` pour
établir que pr₂(u) appartient bien à la famille, et S5 pour livrer le membre
demandé.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, existe, impl, pourtout, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, membre_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_union_premiere import (
    valeur_atteinte,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _membre_famille_t(C, terme, g="gsj"):
    """⊢ ( T ∈ 𝔇(C) ) ⇔ (∃q)( q∈C et T = pr₂(q) )  pour un TERME T.

    `membre_famille` attend un NOM (LEÇON 17) ; on la ∀-clôture sur ce nom —
    licite, elle est CLOSE — puis on instancie au terme voulu."""
    return instancie(N.generalisation(g, membre_famille(C, g)), _t(terme))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (le recollement est surjectif sur la réunion des bases)
def surj_union_us(E_set="E", C="Cch", w="wsj", p="psj", a="asj"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ (∀w)( w ∈ US ⇒ (∃p)( p∈𝔇 et (∃a)((a,w)∈p) ) ).
       [donnée 7/11].

    w ∈ US fournit un u de la chaîne dont la base contient w ; `valeur_atteinte`
    en donne un antécédent dans pr₂(u) ; et pr₂(u) est bien membre de 𝔇, ce que
    `membre_famille` établit en sens ARRIÈRE, u se prenant pour témoin."""
    vE, vC, vw = _t(E_set), _t(C), var(w)
    D, US, Fr = famille_de_chaine(vC), union_premiere(vC), frame_pair(vE)
    h_ch = N.assume(chaine(frame_ordre(vE), Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)

    mem = membre_union_premiere(C, w)
    ex_u = N.modus_ponens(N.assume(appartient(vw, US)), equivalence_avant(mem))
    nu, corps_u = ex_u.conclusion.lieur, ex_u.conclusion.sous[0]
    vu = var(nu)

    h_u = N.assume(corps_u)
    u_in_C, w_in_pr1 = conjonction_elim_gauche(h_u), conjonction_elim_droite(h_u)
    pr2u = E.pr2(vu)

    #  un antécédent de w dans pr₂(u)
    u_in_Fr = N.modus_ponens(u_in_C, instancie(C_inc, vu))
    val = N.modus_ponens(u_in_Fr, N.loi_deduction(
        appartient(vu, Fr), valeur_atteinte(E_set, vu, w, a)))
    ex_a = N.modus_ponens(w_in_pr1, instancie(val, vw))

    #  pr₂(u) est membre de 𝔇 : sens ARRIÈRE, u pour témoin
    equiv_m = _membre_famille_t(C, pr2u)
    #  ⚠️ une implication est `ou(non A, B)` : on prend l'antécédent par
    #  `antecedent_consequent`, jamais par `.sous[0]` (qui rend la négation).
    ante = antecedent_consequent(equivalence_arriere(equiv_m).conclusion)[0]
    nq, corps_q = ante.lieur, ante.sous[0]
    temoin = conjonction_intro(u_in_C, N.reflexivite(pr2u))
    pr2u_in_D = N.modus_ponens(
        N.modus_ponens(temoin, N.s5(corps_q, vu, nq)), equivalence_arriere(equiv_m))

    #  le membre demandé
    corps_but = et(appartient(var(p), D),
                   existe(a, appartient(E.couple(var(a), vw), var(p))))
    but = N.modus_ponens(conjonction_intro(pr2u_in_D, ex_a),
                         N.s5(corps_but, pr2u, p))

    sortie = N.modus_ponens(ex_u, existe_elimination(
        N.loi_deduction(corps_u, but), nu))
    res = N.generalisation(w, N.loi_deduction(appartient(vw, US), sortie))

    assert res.conclusion == pourtout(w, impl(appartient(vw, US),
                                              existe(p, corps_but))), \
        "surj_union_us : forme"
    assert len(res.hypotheses) == 1, "surj_union_us : hyps ≠ 1"
    return res


__all__ = ["surj_union_us"]
