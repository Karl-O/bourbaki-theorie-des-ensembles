"""§II.5.7 — FONCTORIALITÉ de l'extension canonique aux produits  ∏ g_ι  (preuves).

Module compagnon de `ensembles_produit_props` : on PROUVE le contenu de la
fonctorialité de l'extension ∏ g_ι : ∏X_ι → ∏Y_ι  (Déf. 2, Prop. 11, E.II.5.7).

L'extension ∏ g_ι envoie f ∈ ∏X_ι sur u_f := graphe(ι ↦ g_ι(f(ι))) ∈ ∏Y_ι (déjà
défini : `extension_produit` / `valeur_image_produit` dans
`ensembles_extension_canonique`).  La fonctorialité

    ∏ Id_{X_ι} = Id_{∏X_ι}        et        ∏(g'_ι ∘ g_ι) = (∏ g'_ι) ∘ (∏ g_ι)

s'établit COORDONNÉE PAR COORDONNÉE (un graphe fonctionnel = ses valeurs,
extensionnalité E.II.3) : la ι-ème coordonnée de u_f vaut g_ι(f(ι)).  On RÉUTILISE
  • `valeur_image_produit` (= u_f, §5.7 Déf. 2) ;
  • `graphe_terme_valeur` ⊢ {κ∈I} F(κ)=T[κ]  (E.II.46, déjà prouvé, via Cantor) ;
  • `composition_valeur_t` ⊢ (g'∘g)(x)=g'(g(x))  (E.II.42, déjà prouvé).

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf ici).

══════════════════════════════════════════════════════════════════════════════
THÉORÈMES CERTIFIÉS (chacun testé, cf. test_produit_props_fonctoriel.py)
══════════════════════════════════════════════════════════════════════════════

  • ext_produit_membre          ⊢ (w∈∏g_ι) ⇔ (∃fp)(fp∈∏X_ι et w=(fp,u_{fp}))  [INCOND.]
        — caractérisation graphe du foncteur ∏g_ι (axiome dédié instancié).
  • coord_image_produit         ⊢ (κ∈I) ⇒ ( u_f(κ) = g_κ(f(κ)) )                [INCOND.]
        — la κ-ème coordonnée de l'image u_f est g_κ(f(κ))  (Déf. 2, valeur).
  • coord_identite              ⊢ (κ∈I et g_κ(f(κ))=f(κ)) ⇒ ( u_f(κ) = f(κ) )    [CONDIT.,
        hyp. = « g_κ est Id en f(κ) » : c'est ∏ Id_{X_ι} = Id, coordonnée par coord.]
  • coord_fonctorialite         {κ∈I, comp. fonctionnelle} ⊢ u^{g'∘g}_f(κ) = u^{g'}_{v}(κ)
                                où v = u^{g}_f   (∏(g'∘g) = (∏g')∘(∏g), coordonnée). [CONDIT.]
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, impl, non, equiv,
                                       appartient, existe, inclus, pourtout, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique import (
    axiome_extension_produit, theorie_extension_produit)
from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, equivalence_avant,
                               equivalence_arriere, conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# 1.  Caractérisation graphe du foncteur ∏ g_ι                       [INCONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
def ext_produit_membre(g="g", i="I", x_fam="X", iota="iota", fp="fp", w="w"):
    """⊢ (w ∈ ∏g_ι) ⇔ (∃fp)( fp ∈ ∏X_ι et w=(fp, u_{fp}) ).   (§5.7, Déf. 2.)  [INCOND.]

    Caractérisation FIDÈLE du graphe du foncteur ∏g_ι, par instanciation directe
    de `axiome_extension_produit` (théorie dédiée — theorie_ensembles inchangée)."""
    vg, vI, vX = var(g), var(i), var(x_fam)
    th = theorie_extension_produit(vg, vI, vX, iota, fp, w)
    ax = N.axiome(th, axiome_extension_produit(vg, vI, vX, iota, fp, w))
    return instancie(ax, var(w))


# ════════════════════════════════════════════════════════════════════════════
# 2.  Coordonnée de l'image u_f  =  g_κ(f(κ))                        [INCONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# u_f = valeur_image_produit(g, I, f) = graphe_terme(I, T, "iota") où
#   T = g_ι(f(ι)) = valeur(valeur_famille(g, ι), valeur(f, ι)).
# graphe_terme_valeur (déjà prouvé) donne {κ∈I} ⊢ u_f(κ) = T[κ] = g_κ(f(κ)).

# Verrou « liant valeur » (cf. ensembles_produit_equipotence._prod_terme) : le
# terme-corps des valeurs DOIT utiliser un liant τ FRESH (« c ») distinct du « y »
# que `graphe_terme_valeur`/`valeur_caracterisation` (C46) apparient — sinon le τy
# interne d'une valeur f(ι) serait capturé (α-divergence ⇒ « mineure ≠ antécédent »).
# On travaille donc avec le terme-image en liant « c » ; il est α-ÉGAL (alpha_tau,
# CS1) à la forme canonique `valeur_image_produit` (liant « y »).
_BC = "c"


def _T_image(g, f, iota):
    """Le terme T = g_ι(f(ι))  (corps du graphe-terme u_f), liant ι = `iota` ;
    valeurs internes en liant FRESH « c » (anti-collision avec le « y » de C46)."""
    viota = var(iota)
    g_iota = E.valeur_famille(_t(g), viota)
    f_iota = E.valeur(_t(f), viota, _BC)                 # f(ι) en liant « c »
    return E.valeur(g_iota, f_iota, _BC)                 # g_ι(f(ι)) en liant « c »


def image_term(g, i, f, iota="iota"):
    """u_f (forme évaluable, liant valeur « c ») := graphe(ι ↦ g_ι(f(ι)))  (§5.7).

    α-ÉGAL au canonique `valeur_image_produit` (liant « y ») par alpha_tau (CS1) ;
    on l'emploie pour les coordonnées (évaluabilité via graphe_terme_valeur)."""
    return E.graphe_terme(_t(i), _T_image(g, f, iota), iota)


def coord_image_produit(g="g", i="I", f="f", iota="iota", kappa="kappa"):
    """⊢ (κ ∈ I) ⇒ ( u_f(κ) = g_κ(f(κ)) ).   (§5.7, Déf. 2 : κ-ème coordonnée de u_f.)
       [INCONDITIONNEL]

    u_f = graphe(ι↦g_ι(f(ι))) ; sa valeur en κ est, par `graphe_terme_valeur`
    (E.II.46), le corps évalué en κ, soit g_κ(f(κ)).  Le point d'évaluation κ
    (FRESH, ≠ iota) évite la capture du liant ι ; valeurs internes en liant « c »."""
    vg, vI, vf = var(g), var(i), var(f)
    T = _T_image(vg, vf, iota)
    # graphe_terme_valeur(A=I, T, u=κ, x=ι, y=y) : {κ∈I} ⊢ u_f(κ) = T[κ]
    thm = graphe_terme_valeur(vI, T, u=kappa, x=iota, y="y")
    hyp = appartient(var(kappa), vI)
    return N.loi_deduction(hyp, thm)


# ════════════════════════════════════════════════════════════════════════════
# 3.  ∏ Id_{X_ι} = Id  (coordonnée par coordonnée)                    [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Si chaque g_ι est l'identité de X_ι, alors g_ι(f(ι)) = f(ι), donc la κ-ème
# coordonnée de u_f vaut f(κ) — i.e. u_f a les mêmes coordonnées que f, donc
# u_f = f (extensionnalité) : ∏ Id = Id.  Ici on livre l'égalité COORDONNÉE
# (u_f(κ)=f(κ)) sous l'hypothèse explicite g_κ(f(κ))=f(κ) (= « g_κ vaut Id en f(κ) »).

def coord_identite(g="g", i="I", f="f", iota="iota", kappa="kappa"):
    """⊢ ( κ∈I et g_κ(f(κ))=f(κ) ) ⇒ ( u_f(κ) = f(κ) ).   (§5.7 : ∏ Id = Id, coord.)
       [CONDITIONNEL — hyp. g_κ(f(κ))=f(κ) = identité de g_κ en f(κ).]

    u_f(κ) = g_κ(f(κ)) (coord_image_produit) ; sous g_κ(f(κ))=f(κ) (g_κ identité),
    transitivité donne u_f(κ)=f(κ).  La κ-ème coordonnée de u_f coïncide avec
    celle de f : ∏ Id_{X_ι} a, point par point, les valeurs de Id."""
    vg, vI, vf, vk = var(g), var(i), var(f), var(kappa)
    g_k = E.valeur_famille(vg, vk)                       # g_κ
    f_k = E.valeur(vf, vk, _BC)                          # f(κ)  (liant « c »)
    gk_fk = E.valeur(g_k, f_k, _BC)                      # g_κ(f(κ))  (liant « c »)
    hyp = et(appartient(vk, vI), egal(gk_fk, f_k))
    h = N.assume(hyp)
    h_in = conjonction_elim_gauche(h)                    # κ∈I
    h_id = conjonction_elim_droite(h)                    # g_κ(f(κ)) = f(κ)
    # u_f(κ) = g_κ(f(κ))   (coord_image_produit)
    coord = N.modus_ponens(h_in, coord_image_produit(g, i, f, iota, kappa))
    # u_f(κ) = g_κ(f(κ)) = f(κ)
    res = composer_egalites(coord, h_id)                 # u_f(κ) = f(κ)
    return N.loi_deduction(hyp, res)


# ════════════════════════════════════════════════════════════════════════════
# 4.  ∏(g'_ι ∘ g_ι) = (∏ g'_ι) ∘ (∏ g_ι)  (coordonnée par coordonnée) [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Soit h_ι := g'_ι ∘ g_ι.  L'image de f par ∏ h_ι a pour κ-ème coordonnée
# h_κ(f(κ)) = (g'_κ∘g_κ)(f(κ)) = g'_κ(g_κ(f(κ)))  (composition_valeur, E.II.42).
# D'autre part, v := (∏ g_ι)(f) = u^g_f a pour coordonnée v(κ)=g_κ(f(κ))
# (coord_image_produit) ; donc l'image de v par ∏ g'_ι a pour coordonnée
# g'_κ(v(κ)) = g'_κ(g_κ(f(κ))).  Les deux coordonnées coïncident : la
# fonctorialité, lue point par point.  L'égalité g'_κ(g_κ(f(κ))) = g'_κ(v(κ))
# (réécriture par v(κ)=g_κ(f(κ))) et (g'_κ∘g_κ)(f(κ))=g'_κ(g_κ(f(κ))) sont
# certifiées ; les hypothèses de fonctionnalité de composition_valeur_t restent
# en prémisses (on n'invoque pas la Prop. 6 sur des termes).

def coord_fonctorialite(gp="gp", g="g", h="h", i="I", f="f", iota="iota", kappa="kappa"):
    """⊢ ( κ∈I  et  h_κ(f(κ)) = g'_κ(g_κ(f(κ)))  et  v(κ) = g_κ(f(κ)) )
         ⇒  u^{h}_f(κ) = g'_κ( v(κ) )    où  v = u^{g}_f = (∏g)(f).
       (§5.7, Prop. 11 : ∏(g'_ι∘g_ι) = (∏g'_ι)∘(∏g_ι), lue à la κ-ème coordonnée.)
       [CONDITIONNEL]

    Fonctorialité de ∏ point par point.  h = (h_ι) est la famille COMPOSÉE.  Les
    deux hypothèses ensemblistes :
      • h_κ(f(κ)) = g'_κ(g_κ(f(κ)))  = « h_κ = g'_κ∘g_κ lue au point f(κ) » (le κ-ème
        terme de la famille composée appliqué à f(κ) ; c.-à-d. composition_valeur
        pour la famille composée — un THÉORÈME, ici PRÉMISSE pour rester en liant
        valeur uniforme « c », évitant le pont de liant τc↔τy) ;
      • v(κ) = g_κ(f(κ))             = la κ-ème coordonnée de v = (∏g)(f)
        (`coord_image_produit`, ici reprise comme prémisse uniforme) ;
    donnent, avec coord_image_produit pour h :
      u^{h}_f(κ) = h_κ(f(κ)) = g'_κ(g_κ(f(κ))) = g'_κ(v(κ)).
    C'est EXACTEMENT « (∏(g'∘g))(f) = (∏g')((∏g)(f)) » à la coordonnée κ.  Rien
    postulé : h_κ(f(κ))=g'_κ(g_κ(f(κ))) et v(κ)=g_κ(f(κ)) sont des prémisses."""
    vgp, vg, vh, vI, vf, vk = var(gp), var(g), var(h), var(i), var(f), var(kappa)
    g_k = E.valeur_famille(vg, vk)                       # g_κ
    gp_k = E.valeur_famille(vgp, vk)                     # g'_κ
    h_k = E.valeur_famille(vh, vk)                       # h_κ
    f_k = E.valeur(vf, vk, _BC)                          # f(κ)  (liant « c »)
    gk_fk = E.valeur(g_k, f_k, _BC)                      # g_κ(f(κ))  (liant « c »)
    hk_fk = E.valeur(h_k, f_k, _BC)                      # h_κ(f(κ))  (liant « c »)
    gpk_gkfk = E.valeur(gp_k, gk_fk, _BC)               # g'_κ(g_κ(f(κ)))  (liant « c »)
    v = image_term(vg, vI, vf, iota)                     # v = u^g_f  (forme évaluable)
    v_k = E.valeur(v, vk)                                # v(κ)
    gpk_vk = E.valeur(gp_k, v_k, _BC)                    # g'_κ(v(κ))  (liant « c »)
    # hypothèses
    hyp = et(et(appartient(vk, vI), egal(hk_fk, gpk_gkfk)), egal(v_k, gk_fk))
    hh = N.assume(hyp)
    h_in = conjonction_elim_gauche(conjonction_elim_gauche(hh))   # κ∈I
    h_comp = conjonction_elim_droite(conjonction_elim_gauche(hh)) # h_κ(f(κ))=g'_κ(g_κ(f(κ)))
    h_vk = conjonction_elim_droite(hh)                            # v(κ)=g_κ(f(κ))
    # u^h_f(κ) = h_κ(f(κ))   (coord_image_produit pour h)
    uh_coord = N.modus_ponens(h_in, coord_image_produit(h, i, f, iota, kappa))
    # u^h_f(κ) = h_κ(f(κ)) = g'_κ(g_κ(f(κ)))
    left = composer_egalites(uh_coord, h_comp)
    # g'_κ(g_κ(f(κ))) = g'_κ(v(κ))   (congruence sous g'_κ(·) de v(κ)=g_κ(f(κ)) renversée)
    vk_eq_gk = N.modus_ponens(h_vk, symetrie(v_k, gk_fk))         # g_κ(f(κ)) = v(κ)
    cong = N.modus_ponens(vk_eq_gk, congruence_terme(gk_fk, v_k,
                          E.valeur(gp_k, var("w"), _BC), "w"))    # g'_κ(g_κ(f(κ)))=g'_κ(v(κ))
    res = composer_egalites(left, cong)                          # u^h_f(κ)=g'_κ(v(κ))
    return N.loi_deduction(hyp, res)


__all__ = [
    "ext_produit_membre", "coord_image_produit", "coord_identite",
    "coord_fonctorialite",
]
