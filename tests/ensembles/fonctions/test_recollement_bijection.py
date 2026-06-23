"""Tests — INFRA RECOLLEMENT : valeur / image / injectivité de G∪H.

Chaque test vérifie la CONCLUSION EXACTE et les HYPOTHÈSES du théorème via le
noyau abrégé.  Lemmes GÉNÉRAUX (réutilisables : Cantor–Bernstein ET Prop 9).
"""
from bourbaki.logique.formule import (var, egal, et, non, appartient, pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
    valeur_reunion_gauche, valeur_reunion_droite,
    image_reunion_graphes, reunion_graphes_injective)


def _disj(vG, vH):
    return pourtout("u", non(et(appartient(var("u"), E.dom(vG)),
                                appartient(var("u"), E.dom(vH)))))


def test_valeur_reunion_gauche():
    """{func G, func H, dom disjoints, u∈dom G} ⊢ valeur(G∪H,u)=valeur(G,u)."""
    th = valeur_reunion_gauche()
    vG, vH, vu = var("G"), var("H"), var("u")
    GuH = E.reunion(vG, vH)
    assert th.conclusion == egal(E.valeur(GuH, vu), E.valeur(vG, vu))
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vG), E.est_fonctionnel(vH), _disj(vG, vH),
        appartient(vu, E.dom(vG))})


def test_valeur_reunion_droite():
    """{func G, func H, dom disjoints, u∈dom H} ⊢ valeur(G∪H,u)=valeur(H,u)."""
    th = valeur_reunion_droite()
    vG, vH, vu = var("G"), var("H"), var("u")
    GuH = E.reunion(vG, vH)
    assert th.conclusion == egal(E.valeur(GuH, vu), E.valeur(vH, vu))
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vG), E.est_fonctionnel(vH), _disj(vG, vH),
        appartient(vu, E.dom(vH))})


def test_image_reunion_graphes():
    """⊢ image(G∪H, domG∪domH) = image(G,domG) ∪ image(H,domH), clos."""
    th = image_reunion_graphes()
    vG, vH = var("G"), var("H")
    GuH = E.reunion(vG, vH)
    domG, domH = E.dom(vG), E.dom(vH)
    domR = E.reunion(domG, domH)
    imgG, imgH = E.image(vG, domG), E.image(vH, domH)
    assert th.est_clos
    assert th.conclusion == egal(E.image(GuH, domR), E.reunion(imgG, imgH))


def test_reunion_graphes_injective():
    """{func G,H, dom disjoints, G inj/domG, H inj/domH, images disjointes}
       ⊢ injective_dans(G∪H, domG∪domH)."""
    th = reunion_graphes_injective()
    vG, vH = var("G"), var("H")
    GuH = E.reunion(vG, vH)
    domG, domH = E.dom(vG), E.dom(vH)
    domR = E.reunion(domG, domH)
    imgG, imgH = E.image(vG, domG), E.image(vH, domH)
    assert th.conclusion == E.injective_dans(GuH, domR)
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vG), E.est_fonctionnel(vH), _disj(vG, vH),
        E.injective_dans(vG, domG), E.injective_dans(vH, domH),
        egal(E.intersection(imgG, imgH), E.VIDE)})
