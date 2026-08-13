"""Résumé §2 (E.R.7 item 3) — L'INJECTION CANONIQUE de A ⊂ E dans E. CLOS.

Bourbaki : « l'application x ↦ x de A dans E (dite application canonique, ou
injection canonique, de A dans E) » — c'est l'identité sur A, lue à valeurs
dans un sur-ensemble E.

DÉRIVÉ ici, avec UNE hypothèse honnête { A ⊂ E } :

    ⊢ est_injection_de( Δ_A , A , E )

où Δ_A = E.diagonale(A) est le graphe x↦x déposé.  Route = le patron de
inf_egal_reflexif (Δ_A fonctionnel + domaine + injectif + image ⊂ A, tous
CLOS), le codomaine étant élargi de A à E par inclusion_transitive.
En corollaire (même patron que X ≤ X) :  { A ⊂ E } ⊢ Card(A) ≤ Card(E).
theorie_ensembles = 22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, inclusion_transitive, instancie)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inclusion_reflexive)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_fonctionnelle, diagonale_domaine, diagonale_image,
    diagonale_injective)


def injection_canonique(a: str = "A"):
    """Le GRAPHE de l'injection canonique de A : Δ_A (x ↦ x sur A)."""
    return E.diagonale(var(a))


# @livre Ch.R §2 Def.- | E.R.7 item 3 | PDF p.310  (application/injection canonique de A ⊂ E dans E — DÉRIVÉE)
# @livre Ch.R §2 Demo.- | E.R.7 item 3 | PDF p.310  (démo : lemmes diagonale CLOS + élargissement du codomaine par transitivité de ⊂)
def injection_canonique_theoreme(a: str = "A", e: str = "E"):
    """🎯 { A ⊂ E } ⊢ est_injection_de(Δ_A, A, E).   [1 hypothèse HONNÊTE]

    Δ_A est fonctionnel, de domaine A, injectif sur A (lemmes CLOS), et son
    image Δ_A⟨A⟩ ⊂ A ⊂ E (transitivité de l'inclusion sous l'hypothèse)."""
    vA, vE = var(a), var(e)
    DA = E.diagonale(vA)

    # image(Δ_A, A) ⊂ A   (patron exact de inf_egal_reflexif, CLOS)
    incl_img_A = N.modus_ponens(inclusion_reflexive(a), equivalence_arriere(
        N.modus_ponens(diagonale_image(a),
                       N.s6(E.image(DA, vA), vA, "w", inclus(var("w"), vA)))))

    # élargissement du codomaine : (image ⊂ A) et (A ⊂ E) ⇒ (image ⊂ E)
    h = N.assume(inclus(vA, vE))                    # A ⊂ E   [HONNÊTE]
    g = N.generalisation("ia", N.generalisation("ib", N.generalisation("ic",
        inclusion_transitive("ia", "ib", "ic"))))
    it = instancie(instancie(instancie(g, E.image(DA, vA)), vA), vE)
    incl_img_E = N.modus_ponens(conjonction_intro(incl_img_A, h), it)

    inj = conjonction_intro(conjonction_intro(conjonction_intro(
        diagonale_fonctionnelle(a), diagonale_domaine(a)),
        diagonale_injective(a)), incl_img_E)
    assert inj.conclusion == est_injection_de(DA, vA, vE), \
        "injection canonique : conclusion ≠ est_injection_de(Δ_A, A, E)"
    assert inj.hypotheses == frozenset({inclus(vA, vE)}), \
        "injection canonique : hypothèses ≠ {A ⊂ E}"
    return inj


def sous_ensemble_inf_egal(a: str = "A", e: str = "E"):
    """Corollaire :  { A ⊂ E } ⊢ Card(A) ≤ Card(E)  (Δ_A témoigne l'injection,
    même clôture existentielle S5 que dans inf_egal_reflexif)."""
    vA, vE = var(a), var(e)
    inj = injection_canonique_theoreme(a, e)
    res = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), vA, vE),
                                   E.diagonale(vA), "F"))
    assert res.conclusion == inf_egal_card(vA, vE), "corollaire : conclusion ≠ A ≤ E"
    return res


__all__ = ["injection_canonique", "injection_canonique_theoreme",
           "sous_ensemble_inf_egal"]
