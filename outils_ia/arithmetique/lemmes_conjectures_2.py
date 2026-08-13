"""Lemmes DÉCOUVERTS PAR LA MACHINE — 2ᵉ fournée (CY3 en streaming, 8 août 2026).

────────────────────────────────────────────────────────────────────────────────
PROVENANCE — le COMPOUNDING à l'œuvre, pour la première fois en profondeur 2.

Le run CY3 (5 tours en 10,2 min, 64 découvertes, trace au fil de l'eau —
ev.310-313) avait les QUATRE lemmes machine de la 1ʳᵉ fournée dans son pool
d'implications : ces trois-ci sont nés en les CHAÎNANT — le produit du cycle
précédent est l'engrais du suivant.

    succ_fini_cardinal(a)            ⊢ Fini a ⇒ est_cardinal(a+1)
        [transit.σ  fini_succ + fini_implique_cardinal]
    fini_somme_cardinal_successeur(a,b) ⊢ (Fini a et Fini b) ⇒ est_cardinal((a+b)+1)
        [transit.σ  M:fini_somme_successeur + fini_implique_cardinal — un lemme
         machine de la 1ʳᵉ fournée comme PREMIER maillon]
    prop2_sous_somme_finie(a,b,p,c)  ⊢ (Fini a et Fini b) ⇒ ( p = (a+b)+c ⇒ (a+b) ≤ p )
        [transit.σ  somme_binaire_entier + M:prop2_sous_fini — idem, second maillon]

Chaque redérivation suit la chaîne de la découverte en pas de noyau explicites ;
chaque conclusion est vérifiée à la construction, et sa compagne `_cible`
(zéro-arg, énoncé par combinateurs) nourrit le gate du volant.

⚠️ COÛT : machinerie C61 au premier appel d'un process frais (~200 s) — marker slow.
INVARIANT : primitives du noyau uniquement ; theorie_ensembles() reste à 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_binaire_entier,
)

from outils_ia.arithmetique.machine_num import fic_t
from outils_ia.arithmetique.lemmes_conjectures import (
    _fifs_t, fini_somme_successeur, prop2_sous_fini,
)

mp = N.modus_ponens


def succ_fini_cardinal(a="a"):
    """⊢ Fini a ⇒ est_cardinal(a+1).            [CY3, transit.σ fini_succ + fic]

    Chaîne de la découverte : Fini a ⇒ Fini(a+1) (fini_succ au terme a), puis
    fini_implique_cardinal au terme a+1."""
    va = var(a)
    h = N.assume(est_fini(va))
    fini_sa = mp(h, _fifs_t(va))                            # Fini(a+1)
    r = N.loi_deduction(est_fini(va), mp(fini_sa, fic_t(successeur(va))))
    assert r.conclusion == impl(est_fini(va), est_cardinal(successeur(va)))
    assert r.est_clos
    return r


def succ_fini_cardinal_cible():
    """Énoncé visé : Fini a ⇒ est_cardinal(a+1)."""
    va = var("a")
    return impl(est_fini(va), est_cardinal(successeur(va)))


def fini_somme_cardinal_successeur(a="a", b="b"):
    """⊢ (Fini a et Fini b) ⇒ est_cardinal((a+b)+1).
                     [CY3, transit.σ M:fini_somme_successeur + fic — profondeur 2]

    PREMIER lemme né d'un lemme machine : le premier maillon est
    `fini_somme_successeur` (1ʳᵉ fournée), pas un théorème du dépôt."""
    va, vb = var(a), var(b)
    ab = SC(va, vb)
    h = N.assume(et(est_fini(va), est_fini(vb)))
    f_succ = mp(h, fini_somme_successeur(a, b))             # Fini((a+b)+1)
    r = N.loi_deduction(et(est_fini(va), est_fini(vb)),
                        mp(f_succ, fic_t(successeur(ab))))
    assert r.conclusion == impl(et(est_fini(va), est_fini(vb)),
                                est_cardinal(successeur(ab)))
    assert r.est_clos
    return r


def fini_somme_cardinal_successeur_cible():
    """Énoncé visé : (Fini a et Fini b) ⇒ est_cardinal((a+b)+1)."""
    va, vb = var("a"), var("b")
    return impl(et(est_fini(va), est_fini(vb)),
                est_cardinal(successeur(SC(va, vb))))


def prop2_sous_somme_finie(a="a", b="b", p="p", c="c"):
    """⊢ (Fini a et Fini b) ⇒ ( p = (a+b)+c ⇒ (a+b) ≤ p ).
                 [CY3, transit.σ somme_binaire_entier + M:prop2_sous_fini — prof. 2]

    Le second maillon est le lemme machine `prop2_sous_fini`, instancié AU TERME
    a+b via le motif généraliser-puis-instancier (un nom frais lie le lemme, le
    terme le remplace — même geste que `_fifs_t`)."""
    va, vb = var(a), var(b)
    ab = SC(va, vb)
    h = N.assume(et(est_fini(va), est_fini(vb)))
    fini_ab = mp(h, somme_binaire_entier(a, b))             # Fini(a+b)
    lemme_t = instancie(N.generalisation("xl2", prop2_sous_fini("xl2", p, c)), ab)
    r = N.loi_deduction(et(est_fini(va), est_fini(vb)), mp(fini_ab, lemme_t))
    assert r.conclusion == impl(
        et(est_fini(va), est_fini(vb)),
        impl(egal(var(p), SC(ab, var(c))), inf_egal_card(ab, var(p))))
    assert r.est_clos
    return r


def prop2_sous_somme_finie_cible():
    """Énoncé visé : (Fini a et Fini b) ⇒ ( p = (a+b)+c ⇒ (a+b) ≤ p )."""
    va, vb, vp, vc = var("a"), var("b"), var("p"), var("c")
    ab = SC(va, vb)
    return impl(et(est_fini(va), est_fini(vb)),
                impl(egal(vp, SC(ab, vc)), inf_egal_card(ab, vp)))


__all__ = ["succ_fini_cardinal", "succ_fini_cardinal_cible",
           "fini_somme_cardinal_successeur", "fini_somme_cardinal_successeur_cible",
           "prop2_sous_somme_finie", "prop2_sous_somme_finie_cible"]
