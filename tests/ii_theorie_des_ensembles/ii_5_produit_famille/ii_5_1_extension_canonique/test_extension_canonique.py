"""Tests §II.5 (notions « manquantes » du produit) — extension canonique aux
parties, application/diagonale, produit partiel & pr_J, extension aux produits.

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
Aucun fichier existant n'est modifié : toutes les notions vivent dans le module
neuf `ensembles_extension_canonique` ; les axiomes neufs (ext. aux produits) sont
dans une THÉORIE DÉDIÉE — theorie_ensembles() reste à 22 axiomes (test dédié).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, non, appartient, existe,
                                       inclus, pourtout, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique import ensembles_extension_canonique as X


# ── 1. Extension canonique aux parties (§5.1) ─────────────────────────────────
def test_graphe_extension_canonique_terme():
    vG, vA = var("G"), var("A")
    t = X.graphe_extension_canonique(vG, vA, "Xi")
    cible = E.graphe_terme(E.parties(vA), E.image(vG, var("Xi")), "Xi")
    assert t == cible


def test_extension_canonique_terme():
    vG, vA, vB = var("G"), var("A"), var("B")
    t = X.extension_canonique(vG, vA, vB, "Xi")
    cible = E.fonction_terme(E.parties(vA), E.image(vG, var("Xi")), E.parties(vB), "Xi")
    assert t == cible


def test_ext_canonique_graphe_membre():
    thm = X.ext_canonique_graphe_membre("G", "A", "Xi")
    vG, vA, vw, vXi, vy = var("G"), var("A"), var("w"), var("Xi"), var("y")
    corps = existe("Xi", existe("y",
        et(et(egal(vw, E.couple(vXi, vy)), appartient(vXi, E.parties(vA))),
           egal(vy, E.image(vG, vXi)))))
    cible = equiv(appartient(vw, X.graphe_extension_canonique(vG, vA, "Xi")), corps)
    assert thm.conclusion == cible
    assert thm.est_clos


def test_ext_canonique_valeur():
    thm = X.ext_canonique_valeur("G", "A", "X", "Xi")
    vG, vA, vX = var("G"), var("A"), var("X")
    GX = E.image(vG, vX)
    graphe = X.graphe_extension_canonique(vG, vA, "Xi")
    cible = impl(appartient(vX, E.parties(vA)),
                 appartient(E.couple(vX, GX), graphe))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 2. Application diagonale & diagonale Δ (§5.3) ─────────────────────────────
def test_famille_constante_terme():
    vI, vx = var("I"), var("x")
    t = X.famille_constante(vI, vx, "iota")
    cible = E.graphe_terme(vI, vx, "iota")
    assert t == cible


def test_application_diagonale_terme():
    vE, vI = var("E"), var("I")
    t = X.application_diagonale(vE, vI, "xa", "iota")
    xt = X.famille_constante(vI, var("xa"), "iota")
    cible = E.fonction_terme(vE, xt, E.exposant(vI, vE), "xa")
    assert t == cible


def test_diagonale_produit_terme():
    vE, vI = var("E"), var("I")
    t = X.diagonale_produit(vE, vI, "xa", "iota")
    cible = E.image(X.graphe_application_diagonale(vE, vI, "xa", "iota"), vE)
    assert t == cible


def test_diagonale_valeur():
    thm = X.diagonale_valeur("I", "x", "iota")
    vI, vx, vw, viota, vy = var("I"), var("x"), var("w"), var("iota"), var("y")
    corps = existe("iota", existe("y",
        et(et(egal(vw, E.couple(viota, vy)), appartient(viota, vI)), egal(vy, vx))))
    cible = equiv(appartient(vw, X.famille_constante(vI, vx, "iota")), corps)
    assert thm.conclusion == cible
    assert thm.est_clos


def test_diag_application_membre():
    thm = X.diag_application_membre("E", "I", "xa", "iota")
    vE, vI, vw, vxa, vy = var("E"), var("I"), var("w"), var("xa"), var("y")
    T = X.famille_constante(vI, vxa, "iota")
    corps = existe("xa", existe("y",
        et(et(egal(vw, E.couple(vxa, vy)), appartient(vxa, vE)), egal(vy, T))))
    cible = equiv(appartient(vw, X.graphe_application_diagonale(vE, vI, "xa", "iota")), corps)
    assert thm.conclusion == cible
    assert thm.est_clos


def test_membre_diagonale():
    thm = X.membre_diagonale("E", "I", "xa", "iota")
    vE = var("E")
    GD = X.graphe_application_diagonale(vE, var("I"), "xa", "iota")
    vz, vxb = var("z"), var("x")
    corps = existe("x", et(appartient(vxb, vE), appartient(E.couple(vxb, vz), GD)))
    cible = equiv(appartient(vz, X.diagonale_produit(vE, var("I"), "xa", "iota")), corps)
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 3. Produit partiel & projection pr_J (§5.4) ───────────────────────────────
def test_produit_partiel_terme():
    vf, vJ = var("f"), var("J")
    assert X.produit_partiel(vf, vJ) == E.produit_famille(vf, vJ)


def test_projection_J_terme():
    vF, vJ = var("F"), var("J")
    assert X.projection_J(vF, vJ) == E.restriction(vF, vJ)


def test_pr_partiel_valeur():
    thm = X.pr_partiel_valeur("F", "J")
    vF, vJ = var("F"), var("J")
    assert thm.conclusion == egal(E.restriction(vF, vJ), E.restriction(vF, vJ))
    assert thm.est_clos


def _corps_produit(vG, vf, vJ):
    """Corps à QUATRE conjoints de la Déf. 1 (E II.32), RECONSTRUIT À LA MAIN.

    Conjoint de tête « G ⊂ J × ⋃_{ι∈J} X_ι » rétabli le 26 juil. 2026."""
    vi = var("i")
    return et(et(et(inclus(vG, E.produit(vJ, E.reunion_famille(vf, vJ))),
                    E.est_fonctionnel(vG)),
                 egal(E.dom(vG), vJ)),
              pourtout("i", impl(appartient(vi, vJ),
                                 appartient(E.valeur(vG, vi), E.valeur_famille(vf, vi)))))


def test_membre_produit_partiel():
    thm = X.membre_produit_partiel("f", "J", "G")
    vf, vJ, vG = var("f"), var("J"), var("G")
    cible = equiv(appartient(vG, X.produit_partiel(vf, vJ)), _corps_produit(vG, vf, vJ))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_restriction_dans_produit_partiel():
    thm = X.restriction_dans_produit_partiel("f", "J", "G")
    vf, vJ, vG = var("f"), var("J"), var("G")
    cible = impl(appartient(vG, X.produit_partiel(vf, vJ)), egal(E.dom(vG), vJ))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── 4. Extension canonique aux produits ∏ g_ι (§5.7, Déf. 2) ──────────────────
def test_valeur_image_produit_terme():
    vg, vI, vf = var("g"), var("I"), var("f")
    t = X.valeur_image_produit(vg, vI, vf, "iota")
    g_iota = E.valeur_famille(vg, var("iota"))
    f_iota = E.valeur(vf, var("iota"))
    cible = E.graphe_terme(vI, E.valeur(g_iota, f_iota), "iota")
    assert t == cible


def test_extension_produit_terme():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app
    vg, vI = var("g"), var("I")
    assert X.extension_produit(vg, vI) == app("extension_produit", vg, vI)


def test_axiome_extension_produit_bien_forme():
    vg, vI, vX = var("g"), var("I"), var("X")
    ax = X.axiome_extension_produit(vg, vI, vX, "iota", "fp", "w")
    th = X.theorie_extension_produit(vg, vI, vX, "iota", "fp", "w")
    # l'axiome est exploitable via N.axiome (clos)
    assert N.axiome(th, ax).est_clos
    # forme : (∀w)(w∈∏g ⇔ (∃fp)(fp∈∏X et w=(fp,u_{fp})))
    vw, vfp = var("w"), var("fp")
    ufp = X.valeur_image_produit(vg, vI, vfp, "iota")
    corps = existe("fp", et(appartient(vfp, E.produit_famille(vX, vI)),
                            egal(vw, E.couple(vfp, ufp))))
    cible = pourtout("w", equiv(appartient(vw, X.extension_produit(vg, vI)), corps))
    assert ax == cible


def test_ext_produit_valeur():
    thm = X.ext_produit_valeur("g", "I", "X", "f", "iota", "fp", "w")
    vg, vI, vX, vf = var("g"), var("I"), var("X"), var("f")
    uf = X.valeur_image_produit(vg, vI, vf, "iota")
    cible = impl(appartient(vf, E.produit_famille(vX, vI)),
                 appartient(E.couple(vf, uf), X.extension_produit(vg, vI)))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── theorie_ensembles() reste à 22 axiomes (aucun axiome neuf n'y est versé) ──
def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
