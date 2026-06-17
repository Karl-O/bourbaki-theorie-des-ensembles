"""Tests §II.3.6, Exemple 2 — première/seconde fonction coordonnée sur G
(applications z↦pr₁z, z↦pr₂z ; notion auparavant ABSENTE au niveau application).
Définitions fidèles + fonctionnalité du graphe (C54) close.  theorie=22."""
from bourbaki.logique.formule import var
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.fonctions import ensembles_fonctions_coordonnees as FC


# ── DÉFINITIONS ───────────────────────────────────────────────────────────────
def test_premiere_fonction_coordonnee_forme():
    vG, vz = var("G"), var("c0")
    # z ↦ pr₁z (z∈G) = fonction_terme(G, pr₁z, dom G)  (liant « c0 »)
    assert FC.premiere_fonction_coordonnee(vG) == \
        E.fonction_terme(vG, E.pr1(vz), E.dom(vG), "c0")


def test_seconde_fonction_coordonnee_forme():
    vG, vz = var("G"), var("c0")
    assert FC.seconde_fonction_coordonnee(vG) == \
        E.fonction_terme(vG, E.pr2(vz), E.img(vG), "c0")


def test_coordonnees_distinctes():
    # les deux fonctions coordonnée sont des objets DISTINCTS (pr₁G=dom, pr₂G=img)
    vG = var("G")
    assert FC.premiere_fonction_coordonnee(vG) != FC.seconde_fonction_coordonnee(vG)


# ── PROPRIÉTÉS CLOSES (C54) ───────────────────────────────────────────────────
def test_premiere_coordonnee_fonctionnelle_close():
    thm = FC.premiere_coordonnee_fonctionnelle("G")
    assert thm.est_clos
    # la conclusion est « graphe_terme(G, pr₁z) est fonctionnel »  (liant « c0 »)
    vG, vz = var("G"), var("c0")
    F = E.graphe_terme(vG, E.pr1(vz), "c0")
    assert thm.conclusion == E.est_fonctionnel(F)


def test_seconde_coordonnee_fonctionnelle_close():
    thm = FC.seconde_coordonnee_fonctionnelle("G")
    assert thm.est_clos
    vG, vz = var("G"), var("c0")
    F = E.graphe_terme(vG, E.pr2(vz), "c0")
    assert thm.conclusion == E.est_fonctionnel(F)


# ── garde-fou theorie ─────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
