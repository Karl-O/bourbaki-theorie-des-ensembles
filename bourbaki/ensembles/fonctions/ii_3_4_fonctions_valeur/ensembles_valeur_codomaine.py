"""§II.3.4 — PONT GÉNÉRAL « valeur d'un graphe fonctionnel dans son but ».

Ce module GÉNÉRALISE à un point x ET un domaine E quelconques les deux lemmes que
`exposant_un` (a^1=a) avait prouvés UNIQUEMENT pour le point ∅ et le domaine {∅}
(exposant_couple_dans / exposant_valeur_dans_A).  C'est le PONT manquant, nommé
identiquement dans les rapports des Prop 9, Prop 10 et Prop 12 (sens inverse) :

    « valeur(G,x) ∈ but, le long de x∈E, pour un graphe fonctionnel G⊂E×F de
      domaine E ».

  • couple_valeur_dans_graphe(G,E,x) : {dom G=E, x∈E} ⊢ (x, G(x)) ∈ G ;
  • valeur_dans_codomaine(G,E,F,x)   : {G⊂E×F, dom G=E, x∈E} ⊢ G(x) ∈ F.

Aucun axiome ajouté (theorie_ensembles inchangée) : tout sort de AXIOME_DOM,
valeur_dans_graphe (= existe_temoin/τ), AXIOME_PRODUIT (via couple_dans_produit_ssi)
et la substitution de Leibniz (S6).  Rien n'est postulé.

Pour une APPLICATION f = ((G,E),F) ∈ 𝓕(E;F), le consommateur récupère le graphe G
(témoin de l'existentielle d'axiome_applications, avec f=((G,E),F) et G∈F^E donc
G⊂E×F et dom G=E), puis applique ces lemmes : f(x), entendu comme G(x), est dans F.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, appartient, existe, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, equivalence_avant, equivalence_arriere, instancie)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §3.4 Lem.- | E II.13 L.24-33 | PDF p.64
def couple_valeur_dans_graphe(g="G", e="E", x="x"):
    """{dom G = E, x ∈ E} ⊢ (x, G(x)) ∈ G.

    x∈E et dom G=E ⇒ x∈dom G (Leibniz S6) ; x∈dom G ⇔ (∃y)((x,y)∈G) [AXIOME_DOM] ;
    valeur_dans_graphe (existe_temoin) ⇒ (x, G(x))∈G, où G(x)=τy((x,y)∈G).
    Généralise exposant_couple_dans (qui le faisait pour x=∅, E={∅})."""
    vG, vE, vx, vy = _t(g), _t(e), _t(x), var("y")
    h_dom = N.assume(egal(E.dom(vG), vE))            # dom G = E
    h_xin = N.assume(appartient(vx, vE))             # x ∈ E
    # dom G=E ⇒ (x∈dom G ⇔ x∈E)  ;  x∈E ⇒ x∈dom G
    leib = N.s6(E.dom(vG), vE, "w", appartient(vx, var("w")))
    x_in_dom = N.modus_ponens(h_xin,
        equivalence_arriere(N.modus_ponens(h_dom, leib)))        # x ∈ dom G
    # x∈dom G ⇔ (∃y)((x,y)∈G)  [AXIOME_DOM]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), vx)               # x∈dom G ⇔ (∃y)((x,y)∈G)
    ex_y = N.modus_ponens(x_in_dom, equivalence_avant(dom_car))  # (∃y)((x,y)∈G)
    cpl = valeur_dans_graphe(vG, vx)                 # {(∃y)((x,y)∈G)} ⊢ (x,G(x))∈G
    return N.modus_ponens(ex_y,
        N.loi_deduction(existe("y", appartient(E.couple(vx, vy), vG)), cpl))  # (x,G(x))∈G


# @livre Ch.II §3.4 Lem.- | E II.13 L.24-33 | PDF p.64
def valeur_dans_codomaine(g="G", e="E", f="F", x="x"):
    """{G ⊂ E×F, dom G = E, x ∈ E} ⊢ G(x) ∈ F.

    (x,G(x))∈G [couple_valeur_dans_graphe] et G⊂E×F ⇒ (x,G(x))∈E×F ; la 2ᵉ projection
    de couple_dans_produit_ssi donne G(x)∈F.  Généralise exposant_valeur_dans_A
    (qui le faisait pour x=∅, E={∅}, F=A) : c'est « le graphe total fonctionnel prend
    ses valeurs dans son but »."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    vG, vE, vF, vx = _t(g), _t(e), _t(f), _t(x)
    fx = E.valeur(vG, vx)                            # G(x)
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))  # G ⊂ E×F   (= (∀z)(z∈G ⇒ z∈E×F))
    cpl = couple_valeur_dans_graphe(g, e, x)         # (x,G(x))∈G   [hyps dom G=E, x∈E]
    incl_inst = instancie(h_incl, E.couple(vx, fx))  # (x,G(x))∈G ⇒ (x,G(x))∈E×F
    in_prod = N.modus_ponens(cpl, incl_inst)         # (x,G(x))∈E×F
    ssi = couple_dans_produit_ssi(vx, fx, vE, vF)    # ((x,G(x))∈E×F) ⇔ (x∈E et G(x)∈F)
    return conjonction_elim_droite(
        N.modus_ponens(in_prod, equivalence_avant(ssi)))          # G(x) ∈ F


__all__ = ["couple_valeur_dans_graphe", "valeur_dans_codomaine"]
