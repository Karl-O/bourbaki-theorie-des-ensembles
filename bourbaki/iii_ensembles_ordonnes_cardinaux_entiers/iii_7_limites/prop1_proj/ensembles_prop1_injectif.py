"""§III.7.2 Prop. 1, 2° — critère d'injectivité de u : F → lim← E_α.

────────────────────────────────────────────────────────────────────────────────
« Pour que u soit injective, il faut et il suffit que, pour tout couple
d'éléments distincts y, z de F, il existe α tel que u_α(y) ≠ u_α(z) »
(E III.53) — REPORTÉ jusqu'ici (REPORTES de ensembles_limites_iii7).

On démontre ici sa forme CONTRAPOSÉE, qui est le contenu utile et évite tout
raisonnement par l'absurde :

  { u ∈ 𝓕(F;lim←),  relation (6) : f_α(u(y)) = u_α(y),  images-graphes,
    y∈F, z∈F,  (∀α)(α∈I ⇒ u_α(y) = u_α(z)) }
      ⊢  u(y) = u(z)                                    [coordonnees_egales_points]

— « deux points de F qui ont mêmes coordonnées ont même image » ; l'injectivité
de u donne alors y = z, et réciproquement.  L'assemblage est celui de
`cone_unicite` (§III.7.2), transposé de « deux applications en un point » à
« une application en deux points » : mêmes coordonnées f_α ⇒ mêmes projections
pr_α (coords_donnent_projections, CLOS) ⇒ égalité par extensionnalité du
produit.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
    extensionnalite_produit,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_application_valeur import (
    valeur_application_dans_but,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
    cone_map_valeur, coords_donnent_projections, _lim_dans_produit, _gleq,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §7.2 Prop.1 | E III.53 L.1-3 | PDF p.156  (relation (6) au point : f_α(u(y)) = u_α(y) pour α∈I, y∈F)
def relation_6_au_point(Efam, f, u, uf, i, ff, a="a", y="yy"):
    """(∀a)(∀y)( (a∈I et y∈F) ⇒ f_a( u(y) ) = u_a(y) )."""
    vE, vf, vi, vF = _t(Efam), _t(f), _t(i), _t(ff)
    va, vy = var(a), var(y)
    return pourtout(a, pourtout(y, impl(
        et(appartient(va, vi), appartient(vy, vF)),
        egal(C.application_canonique_proj_valeur(vE, vf, va, cone_map_valeur(u, vy)),
             E.valeur(C.u_indice(_t(uf), va), vy)))))


def images_graphes_points(u, ff, y="yy", z="zz"):
    """(graphe(u(y)) et graphe(u(z)))  — hypothèse honnête (comme cone_images_graphes)."""
    return et(E.est_un_graphe(cone_map_valeur(u, var(y))),
              E.est_un_graphe(cone_map_valeur(u, var(z))))


# @livre Ch.III §7.2 Prop.1 | E III.53 L.10-11 | PDF p.156  (Prop. 1, 2° : deux points de mêmes coordonnées ont même image — forme contraposée du critère d'injectivité)
def coordonnees_egales_points(Efam="E", f="f", u="u", uf="uf", leq=None,
                              i="I", ff="F", a="a", y="yy", z="zz"):
    """{ u∈𝓕(F;lim←), (6), y∈F, z∈F, mêmes coordonnées }
        ⊢ u(y) = u(z).                       [critère d'injectivité, 2° de la Prop. 1].

    ✅ La prémisse « images-graphes » a sauté : u(y), u(z) sont établis dans lim←
    par `valeur_application_dans_but`, d'où leur caractère de graphe via
    `point_limite_est_graphe` (§7.1).  Le constructeur `images_graphes_points`
    reste exporté pour mémoire de l'énoncé historique, mais n'est plus supposé —
    l'assertion finale le vérifie."""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vuf = _t(Efam), _t(f), _t(u), _t(uf)
    vi, vF = _t(i), _t(ff)
    va, vy, vz = var(a), var(y), var(z)
    LIM = L.lim_proj(vE, vf)
    u_y, u_z = cone_map_valeur(vu, vy), cone_map_valeur(vu, vz)

    h6 = N.assume(relation_6_au_point(vE, vf, vu, vuf, vi, vF, a, y))
    h_yF = N.assume(appartient(vy, vF))
    h_zF = N.assume(appartient(vz, vF))
    h_coord = N.assume(pourtout(a, impl(appartient(va, vi), egal(
        E.valeur(C.u_indice(vuf, va), vy), E.valeur(C.u_indice(vuf, va), vz)))))

    # (∀a)(a∈I ⇒ f_a(u(y)) = f_a(u(z)))   [(6) en y et z + mêmes coordonnées]
    h_aI = N.assume(appartient(va, vi))
    e_y = N.modus_ponens(conjonction_intro(h_aI, h_yF),
                         instancie(instancie(h6, va), vy))     # f_a(u(y))=u_a(y)
    e_z = N.modus_ponens(conjonction_intro(h_aI, h_zF),
                         instancie(instancie(h6, va), vz))     # f_a(u(z))=u_a(z)
    eq_a = N.modus_ponens(h_aI, instancie(h_coord, va))        # u_a(y)=u_a(z)
    fz = C.application_canonique_proj_valeur(vE, vf, va, u_z)
    chain = composer_egalites(composer_egalites(e_y, eq_a), N.modus_ponens(
        e_z, symetrie(fz, E.valeur(C.u_indice(vuf, va), vz))))
    coords = N.generalisation(a, N.loi_deduction(appartient(va, vi), chain))

    # mêmes projections, puis extensionnalité du produit (motif cone_unicite)
    uy_in = valeur_application_dans_but(vu, vF, LIM, vy)
    uz_in = valeur_application_dans_but(vu, vF, LIM, vz)
    cdp = coords_donnent_projections(Efam, f, leq, i, "zp1", "zp2", a)
    proj_eq = N.modus_ponens(
        conjonction_intro(conjonction_intro(uy_in, uz_in), coords),
        instancie(instancie(cdp, u_z), u_y))
    uy_prod = _lim_dans_produit(Efam, f, leq, i, u_y, uy_in)
    uz_prod = _lim_dans_produit(Efam, f, leq, i, u_z, uz_in)
    # graphes DÉDUITS de u(y), u(z) ∈ lim← (déjà établi) — plus d'hypothèse
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_lim_graphe import (
        point_limite_est_graphe,
    )
    g_uy = point_limite_est_graphe(Efam, f, leq, i, u_y, uy_in)
    g_uz = point_limite_est_graphe(Efam, f, leq, i, u_z, uz_in)
    ext_gen = N.generalisation("zextp", N.generalisation("zext", extensionnalite_produit(
        vE, vi, var("zext"), var("zextp"), a)))
    ext = instancie(instancie(ext_gen, u_z), u_y)
    res = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(uy_prod, uz_prod), g_uy), g_uz), proj_eq), ext)
    assert res.conclusion == egal(u_y, u_z), "coordonnees_egales_points : ≠ u(y)=u(z)"
    assert images_graphes_points(vu, vF, y, z) not in res.hypotheses, \
        "coordonnees_egales_points : la prémisse images-graphes devrait avoir sauté"
    return res


__all__ = ["relation_6_au_point", "images_graphes_points",
           "coordonnees_egales_points"]
