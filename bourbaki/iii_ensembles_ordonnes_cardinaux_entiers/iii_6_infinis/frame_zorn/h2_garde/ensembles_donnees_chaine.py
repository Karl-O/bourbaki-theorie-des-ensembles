# -*- coding: utf-8 -*-
"""§III.6.3 — H2 : LES DONNÉES DU RECOLLEMENT, TIRÉES DE « C CHAÎNE NON VIDE ».

🎯 CIBLES — DEUX des neuf données que `frame_de_recollement` réclame, DÉRIVÉES :

    us_inclus_E   : { chaîne(Γ𝔉,𝔉,C) }            ⊢ ⋃S(C) ⊂ E
    us_infini     : { chaîne(Γ𝔉,𝔉,C), C≠∅ }       ⊢ est_infini_ensemble( ⋃S(C) )

Deux des données les plus simples : la réunion des premières projections
reste incluse dans E (chaque membre du frame a la sienne incluse), et elle
est infinie dès que la chaîne a un membre (celui-ci a déjà une première
projection infinie).  C'est ici que « C non vide » sert vraiment.

⚠️ LE PIÈGE QUI LES AVAIT BLOQUÉES (2026-08-23).  `membre_union_premiere`
attend des NOMS de variables — il applique `var()` lui-même.  Lui passer des
Termes fabriquait une variable bâtarde (une variable dont le nom EST un Terme),
et le modus ponens échouait sur « mineure ≠ antécédent ».  Rien à voir avec un
piège τ : une simple API mal appelée, qui avait fait classer le module en
chantier.  Règle : vérifier si une fonction prend des noms ou des termes.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
    equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    non_vide_ssi_element,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import (
    _frame_membre_t, est_infini_union_chaine,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def pr1_inclus_E(E_set="E", p="pmemb"):
    """{ p ∈ 𝔉(E) } ⊢ pr₁(p) ⊂ E   (2ᵉ conjoint du corps du frame).

    Patron de _membre_pr1_infini : élimination des deux existentielles du
    corps, extraction de « S⊂E », identification pr₁(p)=S."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme,
    )
    vE, vp = _t(E_set), _t(p)
    pr1p = E.pr1(vp)
    cible = inclus(pr1p, vE)
    decl = N.modus_ponens(N.assume(appartient(vp, frame_pair(vE))),
                          equivalence_avant(_frame_membre_t(vE, vp)))
    exS = decl.conclusion
    nS, bodyS = exS.lieur, exS.sous[0]
    nphi, bodyphi = bodyS.lieur, bodyS.sous[0]

    def inner(b):
        hh = N.assume(b)
        S_inc = conjonction_elim_droite(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))                   # S⊂E
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))                   # p=(S,φ)
        vS, vphi = var(nS), var(nphi)
        cong = N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr1(var("wdc")), "wdc"))
        eq_pr1 = composer_egalites(cong, projection_premiere(nS, nphi))
        return N.loi_deduction(b, N.modus_ponens(S_inc, equivalence_avant(
            N.modus_ponens(N.modus_ponens(eq_pr1, symetrie(pr1p, vS)),
                           N.s6(vS, pr1p, "wdc", inclus(var("wdc"), vE))))))

    imp_phi = existe_elimination(inner(bodyphi), nphi)
    body = N.modus_ponens(N.assume(bodyS), imp_phi)
    imp_S = existe_elimination(N.loi_deduction(bodyS, body), nS)
    res = N.modus_ponens(decl, imp_S)
    assert res.conclusion == cible, "pr1_inclus_E : forme"
    assert list(res.hypotheses) == [appartient(vp, frame_pair(vE))], \
        "pr1_inclus_E : hyps"
    return res


def us_inclus_E(E_set="E", C="Cch", x="xdc", p="punionpr"):
    """🎯 { chaîne(Γ𝔉,𝔉,C) } ⊢ ⋃S(C) ⊂ E.   [1 hyp].

    Point à point : x∈⋃S donne un p∈C avec x∈pr₁(p) ; la chaîne étant
    incluse dans 𝔉, pr₁(p)⊂E, donc x∈E."""
    vE, vC, vx = _t(E_set), _t(C), var(x)
    US = union_premiere(vC)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    h_ch = N.assume(chaine(Gam, Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)                   # C⊂𝔉
    #  ⚠️ `membre_union_premiere` attend des NOMS (il applique var() lui-même) :
    #  lui passer des Termes fabrique une variable bâtarde et le modus ponens rate.
    mem = membre_union_premiere(C, x)
    #   ⚠️ LEÇON 15 : pr₁ est un τ-terme — on EXTRAIT le corps ET le nom du
    #   liant réel de l'axiome (l'instanciation a pu le renommer).
    ex_reel = antecedent_consequent(equivalence_avant(mem).conclusion)[1]
    p, corps = ex_reel.lieur, ex_reel.sous[0]
    vp = var(p)
    h_c = N.assume(corps)
    p_in_Fr = N.modus_ponens(conjonction_elim_gauche(h_c), instancie(C_inc, vp))
    incl_E = N.modus_ponens(p_in_Fr, N.loi_deduction(
        appartient(vp, Fr), pr1_inclus_E(E_set, vp)))
    incl_ax = alpha_bridge(incl_E, inclus(
        conjonction_elim_droite(h_c).conclusion.termes[1], vE, x))
    x_in_E = N.modus_ponens(conjonction_elim_droite(h_c),
                            instancie(incl_ax, vx))
    ex = existe_elimination(N.loi_deduction(corps, x_in_E), p)
    x_final = N.modus_ponens(N.modus_ponens(
        N.assume(appartient(vx, US)), equivalence_avant(mem)), ex)
    res = N.generalisation(x, N.loi_deduction(appartient(vx, US), x_final))
    assert res.conclusion == inclus(US, vE, x), "us_inclus_E : forme"
    assert len(res.hypotheses) == 1, "us_inclus_E : hyps ≠ 1"
    return res


def us_infini(E_set="E", C="Cch", p="pmemb"):
    """🎯 { chaîne(Γ𝔉,𝔉,C), C≠∅ } ⊢ est_infini_ensemble( ⋃S(C) ).   [2 hyps].

    « C non vide » fournit un membre p ; il est dans 𝔉 (la chaîne y est
    incluse) et sa première projection est infinie, donc ⋃S l'est aussi."""
    vE, vC = _t(E_set), _t(C)
    US = union_premiere(vC)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    cible = est_infini_ensemble(US)

    h_ch = N.assume(chaine(Gam, Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)
    h_nv = N.assume(non(egal(vC, E.VIDE)))
    ex_z = N.modus_ponens(h_nv, equivalence_avant(non_vide_ssi_element(vC)))
    #   « z » est aussi le binder de chaine : α-renommer le témoin
    ex_z = N.modus_ponens(ex_z, equivalence_avant(
        alpha_existe("z", "ztem", appartient(var("z"), vC))))
    vz = var("ztem")
    h_z = N.assume(appartient(vz, vC))                      # z∈C
    z_in_Fr = N.modus_ponens(h_z, instancie(C_inc, vz))
    inf = est_infini_union_chaine(E_set, C, "ztem")         # {z∈C, z∈𝔉} ⊢ ⋃S infini
    inf = N.modus_ponens(z_in_Fr, N.loi_deduction(appartient(vz, Fr), inf))
    inf = N.modus_ponens(h_z, N.loi_deduction(appartient(vz, vC), inf))
    res = N.modus_ponens(ex_z, existe_elimination(
        N.loi_deduction(appartient(vz, vC), inf), "ztem"))
    assert res.conclusion == cible, "us_infini : forme"
    assert len(res.hypotheses) == 2, "us_infini : hyps ≠ 2"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151  (chaque φ de la chaîne est injectif)
def pr2_injectif(E_set="E", p="pmemb"):
    """{ p ∈ 𝔉(E) } ⊢ injectif_graphe( pr₂(p) ).

    Miroir de `pr1_inclus_E` pour la SECONDE projection : le corps du frame
    donne `est_bijection_de(φ, S×S, S)`, dont on extrait la fonctionnalité et
    l'injectivité au niveau VALEUR ; le pont réciproque
    (`injective_dans_implique_injectif_graphe`) la convertit en forme COUPLE,
    qui est celle qu'exige `membres_injectifs`.

    ⚠️ Le pont est appelé par le NOM du liant (nphi), jamais par le terme : il
    relaie vers `couple_donne_valeur`, qui attend des noms (LEÇON 17)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_seconde,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
        injectif_graphe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_injectif_graphe_pont import (
        injective_dans_implique_injectif_graphe,
    )
    vE, vp = _t(E_set), _t(p)
    pr2p = E.pr2(vp)
    decl = N.modus_ponens(N.assume(appartient(vp, frame_pair(vE))),
                          equivalence_avant(_frame_membre_t(vE, vp)))
    exS = decl.conclusion
    nS, bodyS = exS.lieur, exS.sous[0]
    nphi, bodyphi = bodyS.lieur, bodyS.sous[0]

    def inner(b):
        hh = N.assume(b)
        vS, vphi = var(nS), var(nphi)
        bij = conjonction_elim_droite(hh)                   # est_bijection_de(φ,S×S,S)
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(
            conjonction_elim_gauche(hh)))                   # p = (S,φ)
        fonc = conjonction_elim_gauche(conjonction_elim_gauche(bij))
        dom_eq = conjonction_elim_droite(conjonction_elim_gauche(bij))
        inj_A = conjonction_elim_gauche(conjonction_elim_droite(bij))

        #  injective_dans(φ, S×S)  →  injective_dans(φ, dom φ)   [Leibniz]
        SxS = E.produit(vS, vS)
        equiv = N.modus_ponens(dom_eq, N.s6(E.dom(vphi), SxS, "wij",
                                            E.injective_dans(vphi, var("wij"))))
        inj_dom = N.modus_ponens(inj_A, equivalence_arriere(equiv))

        pont = injective_dans_implique_injectif_graphe(nphi)
        ig = N.modus_ponens(fonc, N.loi_deduction(E.est_fonctionnel(vphi), pont))
        ig = N.modus_ponens(inj_dom, N.loi_deduction(
            E.injective_dans(vphi, E.dom(vphi)), ig))       # injectif_graphe(φ)

        #  transport φ → pr₂(p)   (patron de pr1_inclus_E)
        cong = N.modus_ponens(p_eq, congruence_terme(
            vp, E.couple(vS, vphi), E.pr2(var("wdc")), "wdc"))
        eq_pr2 = composer_egalites(cong, projection_seconde(nS, nphi))
        return N.loi_deduction(b, N.modus_ponens(ig, equivalence_avant(
            N.modus_ponens(N.modus_ponens(eq_pr2, symetrie(pr2p, vphi)),
                           N.s6(vphi, pr2p, "wdc",
                                injectif_graphe(var("wdc")))))))

    imp_phi = existe_elimination(inner(bodyphi), nphi)
    body = N.modus_ponens(N.assume(bodyS), imp_phi)
    imp_S = existe_elimination(N.loi_deduction(bodyS, body), nS)
    res = N.modus_ponens(decl, imp_S)
    assert res.conclusion == injectif_graphe(pr2p), "pr2_injectif : forme"
    assert list(res.hypotheses) == [appartient(vp, frame_pair(vE))],         "pr2_injectif : hyps"
    return res


__all__ = ["pr1_inclus_E", "pr2_injectif", "us_infini", "us_inclus_E"]
