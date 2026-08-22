# -*- coding: utf-8 -*-
"""§III.6.3 — H2 : LA FAMILLE DES GRAPHES D'UNE CHAÎNE, ET SON UNION.

🎯 CIBLES (C une chaîne de couples p=(S,φ) ; 𝔇(C) := pr₂⟨C⟩) :

    famille_de_chaine(C) := image( graphe_terme(C, p ↦ pr₂ p), C )
    membre_famille  : ⊢ ( g ∈ 𝔇(C) ) ⇔ (∃p)( p∈C ∧ g = pr₂ p )
    union_fam_egale : ⊢ union_famille( 𝔇(C) ) = ⋃φ(C)

Ce lemme d'égalité est le RACCORD manquant : les lemmes de recollement du
dépôt (union_chaine_est_bijection, union_chaine_dans_frame) concluent sur
union_famille(𝔇) — un terme de famille de graphes — tandis que le résidu H2
porte sur ⋃φ(C) = union_seconde(C), la seconde projection de la chaîne.  Les
deux termes ont la même caractérisation membre-à-membre : l'extensionnalité
les identifie, et Leibniz transporte ensuite TOUS les résultats amont sans
en re-prouver aucun.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, membre_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_seconde, membre_union_seconde,
)

_X = "xdd"          # liant du graphe-terme p ↦ pr₂ p
_G = "punion"     # liant du ∃ de union_famille (axiome c60)
_P = "punionpr"   # liant du ∃ de union_seconde (axiome chaîne)
_Q = "qfam"       # liant PROPRE de membre_famille — JAMAIS le témoin pr₂p
#   ⚠️ leçon de capture : le témoin pr₂(p) contient p ; si le liant de
#   membre_famille était p lui-même, S5 abstrairait aussi les occurrences du
#   témoin.  D'où un liant distinct.


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def graphe_pr2(C):
    """Le graphe-terme p ↦ pr₂(p), restreint à la chaîne C."""
    vC = _t(C)
    return E.graphe_terme(vC, E.pr2(var(_X)), _X)


def famille_de_chaine(C):
    """𝔇(C) := pr₂⟨C⟩ — la famille des graphes des membres de la chaîne."""
    vC = _t(C)
    return E.image(graphe_pr2(vC), vC)


def membre_famille(C="Cch", g=_G):
    """⊢ ( g ∈ 𝔇(C) ) ⇔ (∃p)( p∈C ∧ g = pr₂(p) )   (CLOS).

    AXIOME_IMAGE déplie l'image en (∃p)(p∈C ∧ (p,g)∈graphe_pr2) ; l'axiome du
    graphe-terme remplace le second conjoint par (p∈C ∧ g=pr₂p) ; le premier
    conjoint devient redondant, d'où la forme annoncée."""
    vC, vg = _t(C), var(g)
    vp = var(_Q)
    Gp = graphe_pr2(vC)
    cible = existe(_Q, et(appartient(vp, vC), egal(vg, E.pr2(vp))))

    img = membre_image(Gp, vC, vg)      # g∈𝔇 ⇔ (∃x)(x∈C ∧ (x,g)∈Gp), liant « x »
    #   sens ⇒ : sous le corps de l'image, l'axiome du graphe-terme conclut
    vx = var("x")
    corps_img = et(appartient(vx, vC), appartient(E.couple(vx, vg), Gp))
    h_img = N.assume(corps_img)
    mgt = membre_graphe_terme(vC, E.pr2(var(_X)), "x", g, _X, "ydd")
    conj = N.modus_ponens(conjonction_elim_droite(h_img), equivalence_avant(mgt))
    wit = conjonction_intro(conjonction_elim_gauche(h_img),
                            conjonction_elim_droite(conj))   # x∈C ∧ g=pr₂x
    avant_inner = N.modus_ponens(wit, N.s5(
        et(appartient(vp, vC), egal(vg, E.pr2(vp))), vx, _Q))
    avant = N.modus_ponens(N.modus_ponens(N.assume(appartient(vg, famille_de_chaine(vC))),
                                          equivalence_avant(img)),
                           existe_elimination(N.loi_deduction(corps_img, avant_inner), "x"))
    #   sens ⇐ : d'un p témoin, reconstruire l'appartenance à l'image
    corps_cible = et(appartient(vp, vC), egal(vg, E.pr2(vp)))
    h_c = N.assume(corps_cible)
    p_in = conjonction_elim_gauche(h_c)
    g_eq = conjonction_elim_droite(h_c)
    mgt_p = membre_graphe_terme(vC, E.pr2(var(_X)), _Q, g, _X, "ydd")
    cpl = N.modus_ponens(conjonction_intro(p_in, g_eq), equivalence_arriere(mgt_p))
    ex_img = N.modus_ponens(conjonction_intro(p_in, cpl),
                            N.s5(et(appartient(vx, vC),
                                    appartient(E.couple(vx, vg), Gp)), vp, "x"))
    arriere_inner = N.modus_ponens(ex_img, equivalence_arriere(img))
    arriere = N.modus_ponens(N.assume(cible),
        existe_elimination(N.loi_deduction(corps_cible, arriere_inner), _Q))
    res = conjonction_intro(
        N.loi_deduction(appartient(vg, famille_de_chaine(vC)), avant),
        N.loi_deduction(cible, arriere))
    assert res.est_clos, "membre_famille : non clos"
    return res


def union_fam_egale(C="Cch", w="z", _trace=False):
    """🎯 ⊢ union_famille( 𝔇(C) ) = ⋃φ(C)   (CLOS — le RACCORD).

    Les deux termes ont la même caractérisation : w y appartient exactement
    quand un membre p de la chaîne a w dans sa seconde projection.  Le membre
    gauche passe par la famille 𝔇(C) (un graphe g=pr₂p intermédiaire), le
    membre droit directement ; l'extensionnalité conclut."""
    vC, vw = _t(C), var(w)
    D = famille_de_chaine(vC)
    UD, US = union_famille(D), union_seconde(vC)
    vp, vg = var(_P), var(_G)

    mu = instancie(instancie(N.generalisation("Df", N.generalisation(
        "wf", membre_union_famille("Df", "wf"))), D), vw)   # w∈⋃𝔇 ⇔ (∃p)(p∈𝔇 ∧ w∈p)
    ms = membre_union_seconde(vC, vw)                       # w∈⋃φ ⇔ (∃p)(p∈C ∧ w∈pr₂p)
    #   ⚠️ LEÇON : pr₁/pr₂ sont des τ-termes dont le liant interne est renommé à
    #   l'instanciation — on EXTRAIT donc les corps des axiomes au lieu de les
    #   reconstruire (sinon l'égalité structurelle échoue silencieusement).
    corps_droit = antecedent_consequent(
        equivalence_arriere(ms).conclusion)[0].sous[0]
    corps_gauche = antecedent_consequent(
        equivalence_arriere(mu).conclusion)[0].sous[0]

    #   ⇒ : w∈⋃𝔇 donne un graphe g∈𝔇 avec w∈g ; g=pr₂p pour un p∈C
    h_g = N.assume(corps_gauche)
    g_in_D = conjonction_elim_gauche(h_g)
    w_in_g = conjonction_elim_droite(h_g)
    ex_p = N.modus_ponens(g_in_D, equivalence_avant(membre_famille(vC, _G)))
    vq = var(_Q)
    h_p = N.assume(et(appartient(vq, vC), egal(vg, E.pr2(vq))))
    w_in_pr2 = N.modus_ponens(w_in_g, equivalence_avant(N.modus_ponens(
        conjonction_elim_droite(h_p),
        N.s6(vg, E.pr2(vq), "wfc", appartient(vw, var("wfc"))))))
    #   ⚠️ témoin = vq (le membre issu de la famille), JAMAIS vp qui EST le liant
    wit_d = N.modus_ponens(conjonction_intro(conjonction_elim_gauche(h_p), w_in_pr2),
                           N.s5(corps_droit, vq, _P))
    inner_d = N.modus_ponens(ex_p, existe_elimination(
        N.loi_deduction(et(appartient(vq, vC), egal(vg, E.pr2(vq))), wit_d), _Q))
    avant = N.modus_ponens(N.modus_ponens(N.assume(appartient(vw, UD)),
                                          equivalence_avant(mu)),
                           existe_elimination(N.loi_deduction(corps_gauche, inner_d), _G))
    droit = N.modus_ponens(avant, equivalence_arriere(ms))

    #   ⇐ : d'un p∈C avec w∈pr₂p, le graphe g:=pr₂p est dans 𝔇 et contient w
    h_d = N.assume(corps_droit)
    p_in, w_in = conjonction_elim_gauche(h_d), conjonction_elim_droite(h_d)
    fam_g = instancie(N.generalisation(_G, membre_famille(vC, _G)), E.pr2(vp))
    g_in = N.modus_ponens(N.modus_ponens(
        conjonction_intro(p_in, N.reflexivite(E.pr2(vp))),
        N.s5(et(appartient(var(_Q), vC), egal(E.pr2(vp), E.pr2(var(_Q)))), vp, _Q)),
        equivalence_arriere(fam_g))
    wit_g = N.modus_ponens(conjonction_intro(g_in, w_in),
                           N.s5(corps_gauche, E.pr2(vp), _G))
    inner_g = N.modus_ponens(wit_g, equivalence_arriere(mu))
    arriere = N.modus_ponens(N.modus_ponens(N.assume(appartient(vw, US)),
                                            equivalence_avant(ms)),
                             existe_elimination(N.loi_deduction(corps_droit, inner_g), _P))

    equiv_w = conjonction_intro(N.loi_deduction(appartient(vw, UD), droit),
                                N.loi_deduction(appartient(vw, US), arriere))
    incl_ds = N.generalisation(w, equivalence_avant(equiv_w))
    incl_sd = N.generalisation(w, equivalence_arriere(equiv_w))
    res = N.modus_ponens(conjonction_intro(incl_ds, incl_sd),
                         extensionnalite_appliquee(UD, US))
    assert res.conclusion == egal(UD, US), "union_fam_egale : forme"
    assert res.est_clos, "union_fam_egale : non clos"
    return res


__all__ = ["graphe_pr2", "famille_de_chaine", "membre_famille", "union_fam_egale"]
