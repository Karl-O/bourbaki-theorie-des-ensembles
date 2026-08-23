# -*- coding: utf-8 -*-
"""§III.6.3 — LA FAMILLE 𝔇(C) EST DIRIGÉE (donnée 4/11 du recollement).

⚠️ CE QUI AVAIT BLOQUÉ (essais 1-2, résolu au 3ᵉ).  L'introduction
existentielle échouait parce que les deux inclusions du corps étaient
INTERVERTIES dans une des deux branches : le corps attend « p⊂r PUIS q⊂r »,
or quand r := p c'est la RÉFLEXIVITÉ qui vient en premier et la dérivée en
second — l'inverse de la branche r := q.  Le liant de `inclus`, d'abord
suspecté, était hors de cause : la comparaison des formules l'a montré en
trois lignes, là où retoucher la preuve à l'aveugle aurait coûté des essais.

🎯 CIBLES :

    famille_dirigee_de_chaine : { chaine(Γ𝔉,𝔉,C) } ⊢ famille_dirigee( 𝔇(C) )
    union_dirigee_injective   : { chaine(Γ𝔉,𝔉,C) } ⊢ injectif_graphe( ⋃𝔇(C) )

La direction est la traduction, au niveau de la famille des graphes, du fait
que C est une CHAÎNE : deux membres de 𝔇(C) sont pr₂(u) et pr₂(v) pour u,v ∈ C
comparables dans Γ𝔉, lequel ordonne par EXTENSION (pr₁⊂pr₁ et pr₂⊂pr₂) — le
plus grand des deux sert de majorant r, l'autre inclusion étant la réflexivité.

La seconde cible tombe alors immédiatement : `union_famille_injective` (déjà
dans le dépôt) réclame exactement { famille_dirigee, membres_injectifs }, et
`membres_famille_injectifs` a clos la seconde ce matin.  C'est la donnée 2/11.

⚠️ PIÈGE ÉVITÉ.  `membre_famille` fixe le nom de son liant existentiel ; on
l'appelle DEUX fois (pour p et pour q), d'où deux ∃ de même liant qu'on ne peut
pas éliminer imbriqués sans capture.  Le second est α-renommé avant usage.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    famille_dirigee, injectif_graphe, membres_injectifs, union_famille_injective,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import (
    frame_ordre_membre_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_est_ordre import (
    inclusion_reflexive_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, membre_famille, membres_famille_injectifs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_donnees_chaine import (
    pr2_fonctionnel,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge `formule` de `thm` par `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _inclusion_membres(vE, vmaj, autre, eq_autre, eq_maj, dans_Gam):
    """De (autre,vmaj) ∈ Γ𝔉 tirer X ⊂ Y, où X et Y sont les MEMBRES de 𝔇
    associés (eq_autre : X = pr₂(autre), eq_maj : Y = pr₂(vmaj)).

    ⚠️ Les termes X et Y sont pris sur les ÉGALITÉS, jamais relus sur la
    conclusion : `inclus` construit un ∀, qui n'a pas de `.termes`."""
    corps = N.modus_ponens(dans_Gam, equivalence_avant(
        frame_ordre_membre_t(vE, autre, vmaj)))
    incl = conjonction_elim_droite(corps)                # pr₂(autre) ⊂ pr₂(vmaj)
    pr2_a, pr2_m = E.pr2(autre), E.pr2(vmaj)
    X, Y = eq_autre.conclusion.termes[0], eq_maj.conclusion.termes[0]

    vers_X = N.modus_ponens(incl, equivalence_avant(N.modus_ponens(
        N.modus_ponens(eq_autre, symetrie(X, pr2_a)),
        N.s6(pr2_a, X, "wdi", inclus(var("wdi"), pr2_m)))))      # X ⊂ pr₂(vmaj)
    return N.modus_ponens(vers_X, equivalence_avant(N.modus_ponens(
        N.modus_ponens(eq_maj, symetrie(Y, pr2_m)),
        N.s6(pr2_m, Y, "wdj", inclus(X, var("wdj"))))))          # X ⊂ Y


# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-26 | PDF p.151
#   (« l'ensemble des prolongements est totalement ordonné » — la famille est dirigée)
def famille_dirigee_de_chaine(E_set="E", C="Cch", p="pdir", q="qdir", r="rdir"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ famille_dirigee( 𝔇(C) ).   [donnée 4/11].

    Les liants portent les noms de `famille_dirigee` (pdir, qdir, rdir), pour
    une conclusion identique au caractère près (LEÇON 15)."""
    vE, vC = _t(E_set), _t(C)
    vp, vq = var(p), var(q)
    D = famille_de_chaine(vC)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)

    h_ch = N.assume(chaine(Gam, Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)                    # C ⊂ 𝔉(E)
    comparables = conjonction_elim_droite(conjonction_elim_droite(h_ch))

    prem = et(appartient(vp, D), appartient(vq, D))
    h_pq = N.assume(prem)
    ex_u = N.modus_ponens(conjonction_elim_gauche(h_pq),
                          equivalence_avant(membre_famille(C, p)))
    ex_v0 = N.modus_ponens(conjonction_elim_droite(h_pq),
                           equivalence_avant(membre_famille(C, q)))
    nu, corps_u = ex_u.conclusion.lieur, ex_u.conclusion.sous[0]
    #  ⚠️ même liant que ex_u : on α-renomme AVANT d'imbriquer les éliminations
    nv = nu + "b"
    ex_v = N.modus_ponens(ex_v0, equivalence_avant(
        alpha_existe(nu, nv, ex_v0.conclusion.sous[0])))
    corps_v = ex_v.conclusion.sous[0]

    def inner(bu, bv):
        hu, hv = N.assume(bu), N.assume(bv)
        vu, vv = var(nu), var(nv)
        u_in, eq_p = conjonction_elim_gauche(hu), conjonction_elim_droite(hu)
        v_in, eq_q = conjonction_elim_gauche(hv), conjonction_elim_droite(hv)
        disj = N.modus_ponens(conjonction_intro(u_in, v_in),
                              instancie(instancie(comparables, vu), vv))

        def _cote(vmaj, autre, eq_autre, eq_maj, membre_maj, r_terme, maj_est_q):
            """Branche « autre ≼ vmaj » : le majorant r est le membre associé à
            vmaj.  Le corps attend l'ordre (p⊂r, PUIS q⊂r) : selon que r vaut q
            ou p, c'est la dérivée puis la réflexivité, ou l'inverse."""
            derivee = _inclusion_membres(vE, vmaj, autre, eq_autre, eq_maj, N.assume(
                appartient(E.couple(autre, vmaj), Gam)))
            refl = inclusion_reflexive_terme(r_terme)
            deux, trois = (derivee, refl) if maj_est_q else (refl, derivee)
            majore = conjonction_intro(conjonction_intro(membre_maj, deux), trois)
            return N.loi_deduction(appartient(E.couple(autre, vmaj), Gam),
                                   N.modus_ponens(majore, N.s5(
                                       et(et(appartient(var(r), D), inclus(vp, var(r))),
                                          inclus(vq, var(r))), r_terme, r)))

        gauche = _cote(vv, vu, eq_p, eq_q, conjonction_elim_droite(h_pq), vq, True)
        droite = _cote(vu, vv, eq_q, eq_p, conjonction_elim_gauche(h_pq), vp, False)
        return cas(disj, gauche, droite)

    but = inner(corps_u, corps_v)
    imp_v = existe_elimination(N.loi_deduction(corps_v, but), nv)
    etape = N.modus_ponens(ex_v, imp_v)
    imp_u = existe_elimination(N.loi_deduction(corps_u, etape), nu)
    sortie = N.modus_ponens(ex_u, imp_u)
    res = N.generalisation(p, N.generalisation(q, N.loi_deduction(prem, sortie)))

    assert res.conclusion == famille_dirigee(D, p, q, r), \
        "famille_dirigee_de_chaine : forme"
    assert len(res.hypotheses) == 1, "famille_dirigee_de_chaine : hyps ≠ 1"
    return res


def union_dirigee_injective(E_set="E", C="Cch"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ injectif_graphe( ⋃𝔇(C) ).   [donnée 2/11].

    `union_famille_injective` (déjà dans le dépôt) réclame exactement les deux
    données qu'on vient de clore : la direction et l'injectivité des membres."""
    vC = _t(C)
    D = famille_de_chaine(vC)
    base = union_famille_injective(D)
    base = _cut(famille_dirigee_de_chaine(E_set, C), famille_dirigee(D), base)
    base = _cut(membres_famille_injectifs(E_set, C), membres_injectifs(D), base)
    assert base.conclusion == injectif_graphe(union_famille(D)),         "union_dirigee_injective : forme"
    assert len(base.hypotheses) == 1, "union_dirigee_injective : hyps ≠ 1"
    return base


# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-26 | PDF p.151
#   (deux prolongements comparables s'accordent sur leur domaine commun)
def famille_compatible_de_chaine(E_set="E", C="Cch", p="pcf", q="qcf",
                                 a="acf", b="bcf", c="ccf"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ famille_compatible( 𝔇(C) ).   [donnée 3/11].

    Deux membres de 𝔇(C) sont emboîtés (même départ que la direction) ; les deux
    couples (a,b) et (a,c) se retrouvent donc dans le PLUS GRAND, qui est une
    FONCTION (`pr2_fonctionnel`) — d'où b = c.

    ⚠️ ASYMÉTRIE (LEÇON 18) : c'est le couple du PETIT qu'il faut transporter,
    donc (a,b) quand le majorant est q, mais (a,c) quand c'est p.  L'énoncé
    b=c a beau paraître symétrique, la construction ne l'est pas."""
    vE, vC = _t(E_set), _t(C)
    vp, vq, va, vb, vc = var(p), var(q), var(a), var(b), var(c)
    D = famille_de_chaine(vC)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)

    h_ch = N.assume(chaine(Gam, Fr, vC, "xmaj", "y", "z"))
    C_inc = conjonction_elim_gauche(h_ch)
    comparables = conjonction_elim_droite(conjonction_elim_droite(h_ch))

    prem = et(et(appartient(vp, D), appartient(vq, D)),
              et(appartient(E.couple(va, vb), vp), appartient(E.couple(va, vc), vq)))
    h = N.assume(prem)
    p_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    q_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    ab_p = conjonction_elim_gauche(conjonction_elim_droite(h))
    ac_q = conjonction_elim_droite(conjonction_elim_droite(h))

    ex_u = N.modus_ponens(p_in, equivalence_avant(membre_famille(C, p)))
    ex_v0 = N.modus_ponens(q_in, equivalence_avant(membre_famille(C, q)))
    nu = ex_u.conclusion.lieur
    nv = nu + "b"
    ex_v = N.modus_ponens(ex_v0, equivalence_avant(
        alpha_existe(nu, nv, ex_v0.conclusion.sous[0])))
    corps_u, corps_v = ex_u.conclusion.sous[0], ex_v.conclusion.sous[0]

    def inner(bu, bv):
        hu, hv = N.assume(bu), N.assume(bv)
        vu, vv = var(nu), var(nv)
        u_in, eq_p = conjonction_elim_gauche(hu), conjonction_elim_droite(hu)
        v_in, eq_q = conjonction_elim_gauche(hv), conjonction_elim_droite(hv)
        disj = N.modus_ponens(conjonction_intro(u_in, v_in),
                              instancie(instancie(comparables, vu), vv))

        def _cote(vmaj, autre, eq_autre, eq_maj, maj_dans_C, maj_est_q):
            dans_Gam = N.assume(appartient(E.couple(autre, vmaj), Gam))
            incl = _inclusion_membres(vE, vmaj, autre, eq_autre, eq_maj, dans_Gam)
            Y, pr2_m = eq_maj.conclusion.termes[0], E.pr2(vmaj)
            fonc = _cut(N.modus_ponens(maj_dans_C, instancie(C_inc, vmaj)),
                        appartient(vmaj, Fr), pr2_fonctionnel(E_set, vmaj))
            fonc_Y = N.modus_ponens(fonc, equivalence_avant(N.modus_ponens(
                N.modus_ponens(eq_maj, symetrie(Y, pr2_m)),
                N.s6(pr2_m, Y, "wfc", E.est_fonctionnel(var("wfc"))))))
            if maj_est_q:            # majorant q : transporter (a,b) de p vers q
                deux = conjonction_intro(
                    N.modus_ponens(ab_p, instancie(incl, E.couple(va, vb))), ac_q)
            else:                    # majorant p : transporter (a,c) de q vers p
                deux = conjonction_intro(
                    ab_p, N.modus_ponens(ac_q, instancie(incl, E.couple(va, vc))))
            egalite = N.modus_ponens(deux, instancie(instancie(
                instancie(fonc_Y, va), vb), vc))
            return N.loi_deduction(dans_Gam.conclusion, egalite)

        return cas(disj, _cote(vv, vu, eq_p, eq_q, v_in, True),
                   _cote(vu, vv, eq_q, eq_p, u_in, False))

    but = inner(corps_u, corps_v)
    etape = N.modus_ponens(ex_v, existe_elimination(
        N.loi_deduction(corps_v, but), nv))
    sortie = N.modus_ponens(ex_u, existe_elimination(
        N.loi_deduction(corps_u, etape), nu))
    imp = N.loi_deduction(prem, sortie)
    res = N.generalisation(p, N.generalisation(q, N.generalisation(
        a, N.generalisation(b, N.generalisation(c, imp)))))

    assert res.conclusion == famille_compatible(D, p, q, a, b, c),         "famille_compatible_de_chaine : forme"
    assert len(res.hypotheses) == 1, "famille_compatible_de_chaine : hyps ≠ 1"
    return res


def union_compatible_fonctionnelle(E_set="E", C="Cch"):
    """🎯 { chaine(Γ𝔉,𝔉,C) } ⊢ est_fonctionnel( ⋃𝔇(C) ).   [donnée 6/11].

    `union_famille_fonctionnelle` (déjà dans le dépôt) ne réclame que la
    compatibilité — qu'on vient de clore.  Même mécanique que (2) tombant
    de (4)+(5) : la cartographie R-13 rend chaque donnée mécanique dès que
    ses prémisses sont acquises."""
    vC = _t(C)
    D = famille_de_chaine(vC)
    base = union_famille_fonctionnelle(D)
    base = _cut(famille_compatible_de_chaine(E_set, C), famille_compatible(D), base)
    assert base.conclusion == E.est_fonctionnel(union_famille(D)),         "union_compatible_fonctionnelle : forme"
    assert len(base.hypotheses) == 1, "union_compatible_fonctionnelle : hyps ≠ 1"
    return base


__all__ = ["famille_dirigee_de_chaine", "union_dirigee_injective",
           "famille_compatible_de_chaine", "union_compatible_fonctionnelle"]
