"""§III.7.2 — UNICITÉ du cône de la limite projective (Proposition 1, « et une seule »).

Complète la partie REPORTÉE de `ensembles_limites_iii7` (l'EXISTENCE y est déjà
prouvée) : la propriété universelle (Prop. 1, §III.7.2) affirme qu'il existe une
application u : F → E = lim← E_α « ET UNE SEULE » telle que u_α = f_α ∘ u.  Ce
module NEUF prouve l'UNICITÉ, en réutilisant (import, AUCUNE modification de fichier
déposé) :

 - `ensembles_extensionnalite_produit.extensionnalite_produit` (PART A — deux points
   du produit qui ont les mêmes projections sont égaux) ;
 - `ensembles_application_valeur.{valeur_application_dans_but, application_egale_par_valeurs}`
   (l'image d'un point de la source est dans le but ; extensionnalité des applications) ;
 - `ensembles_limites.appartient_limite_projective` (lim← ⊂ ∏ : z∈lim← ⇒ z∈∏) ;
 - `ensembles_limites_iii7._canonique_proj_valeur_terme` (f_α(z)=pr_α z sur lim←).

ÉNONCÉ.  Soient u, u' : F → lim← deux applications telles que, pour tout y∈F et tout
α∈I,  f_α(u(y)) = f_α(u'(y))  (« mêmes coordonnées » : f_α∘u = f_α∘u' = u_α).
Alors  u = u'.

PREUVE.  Pour y∈F fixé, u(y), u'(y) ∈ lim← (image d'une application F→lim←), donc
∈ ∏_α E_α (lim← ⊂ ∏).  Pour α∈I :
    pr_α(u(y)) = f_α(u(y))    [f_α = pr_α sur lim←, symétrisé]
               = f_α(u'(y))   [hypothèse « mêmes coordonnées »]
               = pr_α(u'(y))  [f_α = pr_α sur lim←],
donc (∀α∈I) pr_α(u(y)) = pr_α(u'(y)) ; par EXTENSIONNALITÉ DU PRODUIT (PART A),
u(y) = u'(y).  Vrai pour tout y∈F ⇒ par EXTENSIONNALITÉ DES APPLICATIONS, u = u'.

HYPOTHÈSES HONNÊTES (non vacuous — u=u' n'y figure pas) :
  • u ∈ 𝓕(F; lim←),  u' ∈ 𝓕(F; lim←)   — u, u' sont des applications F → lim← ;
  • (∀α∀y)((α∈I et y∈F) ⇒ f_α(u(y)) = f_α(u'(y)))   — mêmes coordonnées (relation (6)
    pour u et u' donne f_α∘u = u_α = f_α∘u') ;
  • (∀y)(y∈F ⇒ (graphe(u(y)) et graphe(u'(y))))   — les images sont des ensembles de
    couples (« points du produit »), prémisse honnête de extensionnalite_produit
    (exactement comme application_egale_par_valeurs expose la nature « graphe »).
Aucune n'est fausse ; la conclusion u=u' ne figure dans aucune.

CODAGE.  u(y) := valeur(graphe_de(u), y) (« f(x) au sens de Bourbaki », sur le GRAPHE
de l'application u), exactement la valeur qu'attend application_egale_par_valeurs.

Liants : indice « a » (=α), point « yy » (=y) côté cône ; le liant interne « x » de
egalite_valeurs_application / extensionnalite_produit reste distinct (pas de capture).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient,
                                       pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites as L
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites_iii7 as I7
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant)
from bourbaki.cardinaux.arithmetique.fondations.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    valeur_application_dans_but, application_egale_par_valeurs,
    egalite_valeurs_application)
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
    extensionnalite_produit)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


def cone_map_valeur(u, y):
    """u(y) := valeur(graphe_de(u), y)  (« u(y) au sens de Bourbaki », sur le graphe)."""
    return E.valeur(graphe_de(_t(u)), _t(y))


def cone_coordonnees_egales(Efam, f, u, up, leq, i, ff, a="a", y="yy"):
    """« u et u' ont les mêmes coordonnées » (relation (6) commune) :=
        (∀α)(∀y)( (α∈I et y∈F) ⇒ f_α(u(y)) = f_α(u'(y)) ).

    f_α(u(y)) = application_canonique_proj_valeur(Efam,f,α,u(y))  (la canonique f_α
    appliquée à l'image u(y) ∈ lim←)."""
    from bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques import application_canonique_proj_valeur
    vE, vf, vi, vF = _t(Efam), _t(f), _t(i), _t(ff)
    va, vy = var(a), var(y)
    u_y = cone_map_valeur(u, vy)
    up_y = cone_map_valeur(up, vy)
    hyp = et(appartient(va, vi), appartient(vy, vF))
    concl = egal(application_canonique_proj_valeur(vE, vf, va, u_y),
                 application_canonique_proj_valeur(vE, vf, va, up_y))
    return pourtout(a, pourtout(y, impl(hyp, concl)))


def cone_images_graphes(u, up, ff, y="yy"):
    """« les images de u, u' sont des graphes » :=
        (∀y)( y∈F ⇒ (graphe(u(y)) et graphe(u'(y))) ).

    Prémisse honnête de extensionnalite_produit (u(y), u'(y) sont des points du
    produit, donc des ensembles de couples)."""
    vF, vy = _t(ff), var(y)
    u_y = cone_map_valeur(u, vy)
    up_y = cone_map_valeur(up, vy)
    return pourtout(y, impl(appartient(vy, vF),
                            et(E.est_un_graphe(u_y), E.est_un_graphe(up_y))))


def coords_donnent_projections(Efam="E", f="f", leq=None, i="I", z="zp1", zp="zp2", a="a"):
    """⊢ (∀z)(∀z')( ( z∈lim← et z'∈lim← et (∀α)(α∈I ⇒ f_α(z)=f_α(z')) )
                     ⇒ (∀α)(α∈I ⇒ pr_α(z)=pr_α(z')) ).   CLOS.

    « Mêmes coordonnées f_α ⇒ mêmes projections pr_α », sur la limite.  PROUVÉ pour
    des POINTS PLAINS z, z' (single-τ : pas d'imbrication τ_y(τ_y) qui casserait
    symetrie/composer_egalites) ; pour α∈I :
        pr_α(z) = f_α(z)   [f_α=pr_α sur lim←, symétrisé]
                = f_α(z')  [mêmes coordonnées]
                = pr_α(z') [f_α=pr_α sur lim←].
    On GÉNÉRALISE ensuite sur z, z' (théorème clos) : l'appelant l'INSTANCIE aux
    valeurs τ-imbriquées u(y), u'(y) — instanciation capture-évitante SAINE (subst_t),
    qui produit EXACTEMENT le même terme substitué que l'instance de
    extensionnalite_produit aux mêmes points (donc les hypothèses s'apparient)."""
    if leq is None:
        leq = _gleq()
    from bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques import application_canonique_proj_valeur
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    vz, vzp, va = var(z), var(zp), var(a)
    LIM = L.lim_proj(vE, vf)

    def fa(t):
        return application_canonique_proj_valeur(vE, vf, va, t)

    def pr(t):
        return E.projection_indice(t, va)

    coords = pourtout(a, impl(appartient(va, vi), egal(fa(vz), fa(vzp))))
    hyp = et(et(appartient(vz, LIM), appartient(vzp, LIM)), coords)
    H = N.assume(hyp)
    z_lim = conjonction_elim_gauche(conjonction_elim_gauche(H))
    zp_lim = conjonction_elim_droite(conjonction_elim_gauche(H))
    Hc = conjonction_elim_droite(H)

    h_aI = N.assume(appartient(va, vi))
    # f_α(z)=pr_α(z) ; couper {z∈lim←, α∈I}
    faz = I7._canonique_proj_valeur_terme(Efam, f, leq, i, va, vz)
    faz_imp = N.loi_deduction(appartient(vz, LIM), N.loi_deduction(appartient(va, vi), faz))
    faz_g = N.modus_ponens(h_aI, N.modus_ponens(z_lim, faz_imp))    # f_α(z)=pr_α(z)
    # f_α(z')=pr_α(z')
    fazp = I7._canonique_proj_valeur_terme(Efam, f, leq, i, va, vzp)
    fazp_imp = N.loi_deduction(appartient(vzp, LIM), N.loi_deduction(appartient(va, vi), fazp))
    fazp_g = N.modus_ponens(h_aI, N.modus_ponens(zp_lim, fazp_imp))  # f_α(z')=pr_α(z')
    # f_α(z)=f_α(z')  (mêmes coordonnées)
    faz_eq_fazp = N.modus_ponens(h_aI, instancie(Hc, va))
    # pr_α(z)=f_α(z)=f_α(z')=pr_α(z')   (symetrie/composer SAINS : z,z' plains, single-τ)
    prz_eq_faz = N.modus_ponens(faz_g, symetrie(fa(vz), pr(vz)))    # pr_α(z)=f_α(z)
    t1 = composer_egalites(prz_eq_faz, faz_eq_fazp)                 # pr_α(z)=f_α(z')
    prz_eq_przp = composer_egalites(t1, fazp_g)                     # pr_α(z)=pr_α(z')
    imp = N.loi_deduction(appartient(va, vi), prz_eq_przp)
    forall_a = N.generalisation(a, imp)                            # (∀α)(α∈I⇒pr_α z=pr_α z')
    lemme = N.loi_deduction(hyp, forall_a)                         # HYP ⇒ proj_eq  [clos]
    return N.generalisation(zp, N.generalisation(z, lemme))        # (∀z)(∀z')(HYP⇒proj_eq)


def cone_unicite(Efam="E", f="f", u="u", up="up", leq=None, i="I", ff="F",
                 a="a", y="yy"):
    """{ u ∈ 𝓕(F;lim←), u' ∈ 𝓕(F;lim←),
         (∀α∀y)((α∈I et y∈F) ⇒ f_α(u(y)) = f_α(u'(y))),
         (∀y)(y∈F ⇒ (graphe(u(y)) et graphe(u'(y)))) }
       ⊢  u = u'.

    UNICITÉ du cône (Proposition 1, §III.7.2, « et une seule ») : deux applications
    F → lim← de mêmes coordonnées (f_α∘u = f_α∘u' = u_α) sont égales.  Assemble
    extensionnalite_produit (PART A) point par point puis application_egale_par_valeurs.

    Hypothèses honnêtes (voir docstring du module) ; conclusion u=u' EXACTE, non
    vacuous.  Frontière restante : aucune pour cet énoncé."""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vup, vi, vF = _t(Efam), _t(f), _t(u), _t(up), _t(i), _t(ff)
    LIM = L.lim_proj(vE, vf)
    vy = var(y)

    # hypothèses (portées en Γ)
    h_coord = N.assume(cone_coordonnees_egales(Efam, f, u, up, leq, i, ff, a, y))
    h_graphes = N.assume(cone_images_graphes(u, up, ff, y))

    u_y = cone_map_valeur(u, vy)
    up_y = cone_map_valeur(up, vy)

    h_yF = N.assume(appartient(vy, vF))                            # y∈F  (porté en Γ)

    # ── pour y∈F fixé : u(y)=u'(y) ──────────────────────────────────────────────
    # u(y) ∈ lim←, u'(y) ∈ lim←  (image d'une application F→lim←)
    # valeur_application_dans_but : {u∈𝓕(F;lim←), y∈F} ⊢ valeur(graphe_de u, y)∈lim←.
    u_in_lim = valeur_application_dans_but(vu, vF, LIM, vy)   # {u∈𝓕(F;LIM), y∈F} ⊢ u(y)∈lim←
    up_in_lim = valeur_application_dans_but(vup, vF, LIM, vy) # {u'∈𝓕(F;LIM), y∈F} ⊢ u'(y)∈lim←

    # mêmes coordonnées en y fixé : (∀α)(α∈I ⇒ f_α(u(y))=f_α(u'(y)))
    coords_y = _coords_en_y(h_coord, u, up, vi, vF, vy, leq, Efam, f, a)

    # (∀α)(α∈I ⇒ pr_α(u(y))=pr_α(u'(y)))   via le LEMME PLAIN coords_donnent_projections
    # INSTANCIÉ aux valeurs τ-imbriquées u(y), u'(y) — l'instanciation produit le MÊME
    # terme substitué que l'instance de extensionnalite_produit (cf. infra) → match.
    cdp = coords_donnent_projections(Efam, f, leq, i, "zp1", "zp2", a)  # (∀z)(∀z')(HYP⇒proj)
    cdp_inst = instancie(instancie(cdp, up_y), u_y)   # HYP(u(y),u'(y)) ⇒ proj_eq(u(y),u'(y))
    hyp_cdp = conjonction_intro(conjonction_intro(u_in_lim, up_in_lim), coords_y)
    proj_eq = N.modus_ponens(hyp_cdp, cdp_inst)       # (∀α)(α∈I ⇒ pr_α u(y)=pr_α u'(y))

    # u(y) ∈ ∏, u'(y) ∈ ∏   (lim← ⊂ ∏ : z∈lim← ⇒ z∈∏)
    u_in_prod = _lim_dans_produit(Efam, f, leq, i, u_y, u_in_lim)
    up_in_prod = _lim_dans_produit(Efam, f, leq, i, up_y, up_in_lim)

    # graphe(u(y)), graphe(u'(y))   (de h_graphes sous y∈F)
    graphes = N.modus_ponens(h_yF, instancie(h_graphes, vy))   # graphe(u(y)) et graphe(u'(y))
    g_u = conjonction_elim_gauche(graphes)
    g_up = conjonction_elim_droite(graphes)

    # extensionnalite_produit : prouvé sur POINTS PLAINS (zext,zext') puis GÉNÉRALISÉ et
    # INSTANCIÉ aux valeurs τ-imbriquées u(y),u'(y) (impossible de l'appeler DIRECTEMENT
    # sur des τ : graphe_egal_par_valeurs interne se capture).  L'instance partage avec
    # cdp_inst les MÊMES sous-termes substitués pr_α(u(y)) → les hypothèses s'apparient.
    ext_plain = extensionnalite_produit(vE, vi, var("zext"), var("zextp"), a)
    ext_gen = N.generalisation("zextp", N.generalisation("zext", ext_plain))
    ext = instancie(instancie(ext_gen, up_y), u_y)   # HYP(u(y),u'(y)) ⇒ u(y)=u'(y)
    hyp_ext = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        u_in_prod, up_in_prod), g_u), g_up), proj_eq)
    uy_eq_upy = N.modus_ponens(hyp_ext, ext)                  # u(y) = u'(y)

    # ── (∀y)(y∈F ⇒ u(y)=u'(y))  puis  application_egale_par_valeurs ⇒ u=u' ───────
    imp_y = N.loi_deduction(appartient(vy, vF), uy_eq_upy)    # y∈F ⇒ u(y)=u'(y)
    val_eq = N.generalisation(y, imp_y)   # ≈ egalite_valeurs_application(u,u',F) (liant y)
    # APPARIER le liant : application_egale_par_valeurs attend le liant « x » (défaut) ;
    # on α-renomme y → x.
    val_eq_x = _renomme_liant(val_eq, u, up, vF, y)

    aev = application_egale_par_valeurs(vu, vup, vF, LIM)      # {u,u'∈𝓕, mêmes valeurs} ⊢ u=u'
    # aev a l'hypothèse « egalite_valeurs_application(u,u',F) » (liant « x ») : on la
    # DÉCHARGE puis on l'alimente par val_eq_x (Γ-porté).  u∈𝓕(F;lim←), u'∈𝓕(F;lim←)
    # restent en hypothèses honnêtes.
    vals_hyp = egalite_valeurs_application(vu, vup, vF)       # (∀x)(x∈F⇒valeur(gr u,x)=valeur(gr u',x))
    aev_imp = N.loi_deduction(vals_hyp, aev)                  # vals_hyp ⇒ u=u'
    return N.modus_ponens(val_eq_x, aev_imp)                  # u = u'


# ── helpers d'assemblage ────────────────────────────────────────────────────────
def _coords_en_y(h_coord, u, up, vi, vF, vy, leq, Efam, f, a="a"):
    """{ (∀α∀y)((α∈I et y∈F) ⇒ f_α(u(y))=f_α(u'(y))), y∈F }
       ⊢ (∀α)(α∈I ⇒ f_α(u(y))=f_α(u'(y))).

    Spécialise les « mêmes coordonnées » au point y fixé (forme attendue par
    coords_donnent_projections, où z:=u(y), z':=u'(y))."""
    va = var(a)
    coord_inst = instancie(instancie(h_coord, va), vy)    # (α∈I et y∈F) ⇒ f_α(u(y))=f_α(u'(y))
    h_aI = N.assume(appartient(va, vi))
    h_yF = N.assume(appartient(vy, vF))
    eq = N.modus_ponens(conjonction_intro(h_aI, h_yF), coord_inst)   # f_α(u(y))=f_α(u'(y))
    imp = N.loi_deduction(appartient(va, vi), eq)         # α∈I ⇒ f_α(u(y))=f_α(u'(y))
    return N.generalisation(a, imp)                       # (∀α)(α∈I ⇒ …)   [hyp y∈F]


def _lim_dans_produit(Efam, f, leq, i, terme, preuve_in_lim):
    """{ hyps de preuve_in_lim } ⊢ terme ∈ ∏_α E_α.

    z∈lim← ⇔ (z∈∏ et cond1) (appartient_limite_projective) ; conjonction gauche
    donne z∈∏.  On coupe l'hypothèse z∈lim← par preuve_in_lim."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    car = L.appartient_limite_projective(Efam, f, leq, i, terme)   # terme∈lim← ⇔ (terme∈∏ et cond1)
    Hz = N.assume(appartient(terme, L.lim_proj(vE, vf)))
    both = N.modus_ponens(Hz, equivalence_avant(car))             # terme∈∏ et cond1
    in_prod = conjonction_elim_gauche(both)                       # terme∈∏
    imp = N.loi_deduction(appartient(terme, L.lim_proj(vE, vf)), in_prod)
    return N.modus_ponens(preuve_in_lim, imp)                     # terme∈∏ (hyps de preuve_in_lim)


def _renomme_liant(val_eq, u, up, vF, y):
    """α-renomme le liant « y » de val_eq en « x » pour APPARIER
    egalite_valeurs_application(u,u',F) (liant interne « x » par défaut)."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
    vy = var(y)
    u_y = cone_map_valeur(u, vy)
    up_y = cone_map_valeur(up, vy)
    corps = impl(appartient(vy, vF), egal(u_y, up_y))
    if y == "x":
        return val_eq
    return N.modus_ponens(val_eq, equivalence_avant(alpha_pour_tout(y, "x", corps)))


__all__ = ["cone_map_valeur", "cone_coordonnees_egales", "cone_images_graphes",
           "coords_donnent_projections", "cone_unicite"]
