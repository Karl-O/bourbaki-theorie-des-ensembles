"""Tests §II.5.7 — FONCTORIALITÉ de l'extension aux produits ∏ g_ι (preuves).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
Aucun fichier existant n'est modifié ; theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.logique.formule import (var, egal, et, impl, non, appartient, existe,
                                       inclus, pourtout, equiv)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_produit_props_fonctoriel as F
from bourbaki.ensembles.familles import ensembles_extension_canonique as X


# ── 1. Caractérisation graphe du foncteur ∏ g_ι ──────────────────────────────
def test_ext_produit_membre():
    thm = F.ext_produit_membre("g", "I", "X", "iota", "fp", "w")
    vg, vI, vX = var("g"), var("I"), var("X")
    vw, vfp = var("w"), var("fp")
    ufp = X.valeur_image_produit(vg, vI, vfp, "iota")
    corps = existe("fp", et(appartient(vfp, E.produit_famille(vX, vI)),
                            egal(vw, E.couple(vfp, ufp))))
    cible = equiv(appartient(vw, X.extension_produit(vg, vI)), corps)
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 2. Coordonnée de l'image u_f = g_κ(f(κ)) ─────────────────────────────────
def test_coord_image_produit():
    thm = F.coord_image_produit("g", "I", "f", "iota", "kappa")
    vg, vI, vf, vk = var("g"), var("I"), var("f"), var("kappa")
    uf = F.image_term(vg, vI, vf, "iota")
    uf_k = E.valeur(uf, vk)                              # outer liant « y » (défaut)
    g_k = E.valeur_famille(vg, vk)
    f_k = E.valeur(vf, vk, "c")
    gk_fk = E.valeur(g_k, f_k, "c")
    cible = impl(appartient(vk, vI), egal(uf_k, gk_fk))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 3. ∏ Id = Id (coordonnée) ────────────────────────────────────────────────
def test_coord_identite():
    thm = F.coord_identite("g", "I", "f", "iota", "kappa")
    vg, vI, vf, vk = var("g"), var("I"), var("f"), var("kappa")
    uf = F.image_term(vg, vI, vf, "iota")
    uf_k = E.valeur(uf, vk)
    g_k = E.valeur_famille(vg, vk)
    f_k = E.valeur(vf, vk, "c")
    gk_fk = E.valeur(g_k, f_k, "c")
    hyp = et(appartient(vk, vI), egal(gk_fk, f_k))
    cible = impl(hyp, egal(uf_k, f_k))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 4. ∏(g'∘g) = (∏g')∘(∏g) (coordonnée) ─────────────────────────────────────
def test_coord_fonctorialite():
    thm = F.coord_fonctorialite("gp", "g", "h", "I", "f", "iota", "kappa")
    vgp, vg, vh, vI, vf, vk = (var("gp"), var("g"), var("h"), var("I"),
                               var("f"), var("kappa"))
    g_k = E.valeur_famille(vg, vk)
    gp_k = E.valeur_famille(vgp, vk)
    h_k = E.valeur_famille(vh, vk)
    f_k = E.valeur(vf, vk, "c")
    gk_fk = E.valeur(g_k, f_k, "c")
    hk_fk = E.valeur(h_k, f_k, "c")
    gpk_gkfk = E.valeur(gp_k, gk_fk, "c")
    v = F.image_term(vg, vI, vf, "iota")
    v_k = E.valeur(v, vk)
    gpk_vk = E.valeur(gp_k, v_k, "c")
    hyp = et(et(appartient(vk, vI), egal(hk_fk, gpk_gkfk)), egal(v_k, gk_fk))
    uh = F.image_term(vh, vI, vf, "iota")               # u^h_f
    uh_k = E.valeur(uh, vk)                             # u^h_f(κ)
    cible = impl(hyp, egal(uh_k, gpk_vk))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
