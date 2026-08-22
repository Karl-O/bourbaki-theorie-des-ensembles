# -*- coding: utf-8 -*-
"""§III.6.3 — D1b : LES DONNÉES DE DEDEKIND (u, x0) CONSTRUITES DEPUIS h.

🎯 Sous h_bij := est_bijection_de(h, W, E)  (h : W → E, témoin de Eq(W,E), D1a),
avec W := E⊔{∅} et le MARQUEUR m := (∅, 1) — le point de la copie droite :

    x0_dedekind(h)    := h(m)                      — le point « neuf » de E
    u_dedekind(h, E)  := graphe_terme(E, x ↦ h((x, 0)))   — E → E

    marqueur_dans_W   :  ⊢ m ∈ W                                  (CLOS)
    x0_dans_E         :  { h_bij } ⊢ x0 ∈ E                       [1 hyp]

Les helpers _couple_valeur (t∈W → (t,h(t))∈h) et _valeur_dans_E
(t∈W → h(t)∈E, par l'image h⟨W⟩=E) resservent en D1c pour u⊂E×E,
« hors » et l'injectivité.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    ZERO, UN, somme_disjointe, injection_droite_dans_somme, _dans_singleton,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_carte_egale import (
    SINGZ, ensemble_marque,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


MARQUEUR = E.couple(ZERO, UN)                               # m = (∅, 1) ∈ {∅}×{1}


def x0_dedekind(h):
    """x0 := h(m) — l'image du marqueur, le point de E hors de l'image de u."""
    return E.valeur(_t(h), MARQUEUR)


def u_dedekind(h, e, x="xdk"):
    """u := graphe_terme(E, x ↦ h((x, 0))) — l'application E → E de Dedekind."""
    return E.graphe_terme(_t(e), E.valeur(_t(h), E.couple(var(x), ZERO)), x)


def marqueur_dans_W(e="Eld"):
    """⊢ m ∈ W   (injection droite, ∅∈{∅} ; CLOS)."""
    ve = _t(e)
    res = N.modus_ponens(_dans_singleton(E.VIDE),
                         injection_droite_dans_somme(E.VIDE, ve, SINGZ))
    assert res.conclusion == appartient(MARQUEUR, ensemble_marque(ve)), \
        "marqueur_dans_W : forme"
    assert res.est_clos, "marqueur_dans_W : non clos"
    return res


def _couple_valeur(vh, W, t, func, dom_h, preuve_t_in):
    """{func h, dom h=W, t∈W (preuve)} ⊢ (t, h(t)) ∈ h.

    t∈dom h (Leibniz sur dom h=W), AXIOME_DOM avant → (∃y)((t,y)∈h) ;
    C46 (valeur_caracterisation) instanciée à h(t), réflexivité."""
    ht = E.valeur(vh, t)
    t_dom = N.modus_ponens(preuve_t_in, equivalence_arriere(N.modus_ponens(
        dom_h, N.s6(E.dom(vh), W, "wdk", appartient(t, var("wdk"))))))
    ex_y = N.modus_ponens(t_dom, equivalence_avant(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vh), t)))
    vc_ht = instancie(N.generalisation("y", valeur_caracterisation(vh, t)), ht)
    cpl = N.modus_ponens(N.reflexivite(ht), equivalence_arriere(vc_ht))
    cpl = _cut(ex_y, existe("y", appartient(E.couple(t, var("y")), vh)), cpl)
    return _cut(func, E.est_fonctionnel(vh), cpl)           # (t, h(t)) ∈ h


def _valeur_dans_E(vh, W, ve, t, func, dom_h, img, preuve_t_in):
    """{func, dom h=W, h⟨W⟩=E, t∈W (preuve)} ⊢ h(t) ∈ E.

    (t,h(t))∈h + t∈W → h(t)∈h⟨W⟩ (AXIOME_IMAGE, témoin t) → h(t)∈E (Leibniz).
    ⚠️ t ne doit pas contenir « x » libre (liant interne de l'axiome-image)."""
    ht = E.valeur(vh, t)
    cpl = _couple_valeur(vh, W, t, func, dom_h, preuve_t_in)
    R = et(appartient(var("x"), W), appartient(E.couple(var("x"), ht), vh))
    ex = N.modus_ponens(conjonction_intro(preuve_t_in, cpl), N.s5(R, t, "x"))
    dans_img = N.modus_ponens(ex, equivalence_arriere(membre_image(vh, W, ht)))
    return N.modus_ponens(dans_img, equivalence_avant(N.modus_ponens(
        img, N.s6(E.image(vh, W), ve, "wdk", appartient(ht, var("wdk"))))))


def _extraire_bijection(h, e):
    """Assume h_bij et retourne (vh, ve, W, func, dom_h, inj_h, img)."""
    vh, ve = _t(h), _t(e)
    W = ensemble_marque(ve)
    h_bij = N.assume(est_bijection_de(vh, W, ve))           # [HONNÊTE]
    func = conjonction_elim_gauche(conjonction_elim_gauche(h_bij))
    dom_h = conjonction_elim_droite(conjonction_elim_gauche(h_bij))
    inj_h = conjonction_elim_gauche(conjonction_elim_droite(h_bij))
    img = conjonction_elim_droite(conjonction_elim_droite(h_bij))
    return vh, ve, W, func, dom_h, inj_h, img


def x0_dans_E(h="hdk", e="Eld"):
    """🎯 D1b : { est_bijection_de(h, W, E) } ⊢ x0 ∈ E   [1 hyp]."""
    vh, ve, W, func, dom_h, inj_h, img = _extraire_bijection(h, e)
    res = _valeur_dans_E(vh, W, ve, MARQUEUR, func, dom_h, img,
                         marqueur_dans_W(e))
    assert res.conclusion == appartient(x0_dedekind(vh), ve), "x0_dans_E : forme"
    assert list(res.hypotheses) == [est_bijection_de(vh, W, ve)], \
        "x0_dans_E : hyps"
    return res


__all__ = ["MARQUEUR", "x0_dedekind", "u_dedekind", "marqueur_dans_W",
           "x0_dans_E"]
