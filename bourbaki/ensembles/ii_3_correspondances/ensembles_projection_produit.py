"""§II.3 — Projections d'un produit : pr₁⟨X×Y⟩ = X (si Y≠∅), pr₂⟨X×Y⟩ = Y (si X≠∅).

Résumé §3 item 3f (E.R.12) : « si Y ≠ ∅, pr₁(X×Y) = X ».  Ici pr₁⟨G⟩ = dom G =
{x | (∃y)((x,y)∈G)} (E.II.38) est la première projection du GRAPHE, et de même
pr₂⟨G⟩ = img G.  On certifie (par double inclusion + extensionnalité A1) :
    (∃e)(e∈Y)  ⊢  dom(X×Y) = X          [pr₁⟨X×Y⟩ = X]
    (∃e)(e∈X)  ⊢  img(X×Y) = Y          [pr₂⟨X×Y⟩ = Y]
L'hypothèse « Y ≠ ∅ » est encodée constructivement par « (∃e)(e∈Y) » (Y admet un
élément) — nécessaire au seul sens X ⊂ dom(X×Y) (il faut un témoin e∈Y pour former
(z,e)∈X×Y).  L'inclusion dom(X×Y) ⊂ X, elle, est INCONDITIONNELLE.

Repose sur AXIOME_DOM/AXIOME_IMG (caractérisation dom/img), `couple_dans_produit_ssi`
((u,v)∈A×B ⇔ u∈A et v∈B), et `extensionnalite_appliquee` (A1).  Rien postulé ;
theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, existe, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi)


def _inst_dom(g, z):
    """⊢ (z ∈ dom G) ⇔ (∃y)((z,y) ∈ G).   (instance de AXIOME_DOM ; liant 'y'.)"""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), g), z)


def _inst_img(g, z):
    """⊢ (z ∈ img G) ⇔ (∃x)((x,z) ∈ G).   (instance de AXIOME_IMG ; liant 'x'.)"""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_IMG), g), z)


# @livre Ch.R §3 Prop.- | E.R.12 item 3f ((25) si Y≠∅, pr₁(X×Y)=X) | PDF p.315
def pr1_produit(x="X", y="Y"):
    """⊢ (∃e)(e∈Y) ⇒ dom(X×Y) = X.   (pr₁⟨X×Y⟩ = X si Y non vide.)"""
    vX, vY, vz, vy, ve = var(x), var(y), var("z"), var("y"), var("e")
    prod, dom_prod = E.produit(vX, vY), E.dom(E.produit(vX, vY))
    ynv = existe("e", appartient(ve, vY))                       # Y non vide

    # ── dom(X×Y) ⊂ X  (inconditionnel) ──
    hzy = N.assume(appartient(E.couple(vz, vy), prod))
    zX_u = conjonction_elim_gauche(N.modus_ponens(              # (z,y)∈X×Y ⊢ z∈X
        hzy, equivalence_avant(couple_dans_produit_ssi(vz, vy, vX, vY))))
    elim_y = existe_elimination(                               # (∃y)((z,y)∈X×Y) ⇒ z∈X
        N.loi_deduction(appartient(E.couple(vz, vy), prod), zX_u), "y")
    hz_dom = N.assume(appartient(vz, dom_prod))
    zX = N.modus_ponens(N.modus_ponens(hz_dom, equivalence_avant(_inst_dom(prod, vz))), elim_y)
    incl1 = N.generalisation("z", N.loi_deduction(appartient(vz, dom_prod), zX))

    # ── X ⊂ dom(X×Y)  (sous Y non vide, témoin e∈Y) ──
    hz_X = N.assume(appartient(vz, vX))
    zeprod = N.modus_ponens(conjonction_intro(hz_X, N.assume(appartient(ve, vY))),
                            equivalence_arriere(couple_dans_produit_ssi(vz, ve, vX, vY)))  # (z,e)∈X×Y
    ex_y = N.modus_ponens(zeprod, N.s5(appartient(E.couple(vz, vy), prod), ve, "y"))
    z_dom = N.modus_ponens(ex_y, equivalence_arriere(_inst_dom(prod, vz)))   # z∈dom(X×Y)
    elim_e = existe_elimination(N.loi_deduction(appartient(ve, vY), z_dom), "e")
    z_dom2 = N.modus_ponens(N.assume(ynv), elim_e)
    incl2 = N.generalisation("z", N.loi_deduction(appartient(vz, vX), z_dom2))

    eq = N.modus_ponens(conjonction_intro(incl1, incl2), extensionnalite_appliquee(dom_prod, vX))
    return N.loi_deduction(ynv, eq)                            # (∃e)(e∈Y) ⇒ dom(X×Y)=X


# @livre Ch.R §3 Prop.- | E.R.12 item 3f (dual (25) : si X≠∅, pr₂(X×Y)=Y) | PDF p.315
def pr2_produit(x="X", y="Y"):
    """⊢ (∃e)(e∈X) ⇒ img(X×Y) = Y.   (pr₂⟨X×Y⟩ = Y si X non vide, dual de pr1_produit.)"""
    vX, vY, vz, vx, ve = var(x), var(y), var("z"), var("x"), var("e")
    prod, img_prod = E.produit(vX, vY), E.img(E.produit(vX, vY))
    xnv = existe("e", appartient(ve, vX))                       # X non vide

    # ── img(X×Y) ⊂ Y  (inconditionnel) ──
    hxz = N.assume(appartient(E.couple(vx, vz), prod))
    zY_u = conjonction_elim_droite(N.modus_ponens(             # (x,z)∈X×Y ⊢ z∈Y
        hxz, equivalence_avant(couple_dans_produit_ssi(vx, vz, vX, vY))))
    elim_x = existe_elimination(
        N.loi_deduction(appartient(E.couple(vx, vz), prod), zY_u), "x")
    hz_img = N.assume(appartient(vz, img_prod))
    zY = N.modus_ponens(N.modus_ponens(hz_img, equivalence_avant(_inst_img(prod, vz))), elim_x)
    incl1 = N.generalisation("z", N.loi_deduction(appartient(vz, img_prod), zY))

    # ── Y ⊂ img(X×Y)  (sous X non vide, témoin e∈X) ──
    hz_Y = N.assume(appartient(vz, vY))
    ezprod = N.modus_ponens(conjonction_intro(N.assume(appartient(ve, vX)), hz_Y),
                            equivalence_arriere(couple_dans_produit_ssi(ve, vz, vX, vY)))  # (e,z)∈X×Y
    ex_x = N.modus_ponens(ezprod, N.s5(appartient(E.couple(vx, vz), prod), ve, "x"))
    z_img = N.modus_ponens(ex_x, equivalence_arriere(_inst_img(prod, vz)))   # z∈img(X×Y)
    elim_e = existe_elimination(N.loi_deduction(appartient(ve, vX), z_img), "e")
    z_img2 = N.modus_ponens(N.assume(xnv), elim_e)
    incl2 = N.generalisation("z", N.loi_deduction(appartient(vz, vY), z_img2))

    eq = N.modus_ponens(conjonction_intro(incl1, incl2), extensionnalite_appliquee(img_prod, vY))
    return N.loi_deduction(xnv, eq)                            # (∃e)(e∈X) ⇒ img(X×Y)=Y


def cible_pr1_produit(x="X", y="Y"):
    """Conclusion exacte : (∃e)(e∈Y) ⇒ dom(X×Y) = X."""
    vX, vY = var(x), var(y)
    return impl(existe("e", appartient(var("e"), vY)), egal(E.dom(E.produit(vX, vY)), vX))


def cible_pr2_produit(x="X", y="Y"):
    """Conclusion exacte : (∃e)(e∈X) ⇒ img(X×Y) = Y."""
    vX, vY = var(x), var(y)
    return impl(existe("e", appartient(var("e"), vX)), egal(E.img(E.produit(vX, vY)), vY))


__all__ = ["pr1_produit", "pr2_produit", "cible_pr1_produit", "cible_pr2_produit"]
