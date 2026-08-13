"""Tactique générique : porter un théorème écrit AUX NOMS vers des TERMES.

────────────────────────────────────────────────────────────────────────────────
Problème récurrent du dépôt.  Une brique est écrite sur des variables (« X »,
« u »…) parce que c'est ainsi qu'on la démontre ; on veut l'appliquer à des
TERMES construits (τ, valeurs, projections).  La route naïve — généraliser puis
instancier — est REFUSÉE par le noyau dès que le nom apparaît libre dans une
hypothèse : conditions de domaine, gardes, appartenances.  C'est légitime (la
généralisation serait illicite), mais bloquant.

La manœuvre correcte tient en cinq temps, et c'est celle qu'automatise
`porter_aux_termes` :
    décharger les hypothèses PORTANTES en antécédents  →  généraliser  →
    instancier aux termes  →  ré-assumer les hypothèses SUBSTITUÉES.
Les hypothèses qui ne mentionnent aucun des noms ne sont pas touchées.

HISTORIQUE.  Ce motif a d'abord été écrit à la main sous les noms `_cva_t`,
`_dval_t`, `_nt` dans plusieurs modules (fonctorialité des produits, CST1
identité, fibres de la Prop. 2…), puis rendu autonome dans le chantier des
limites projectives (`iii_7_limites/prop1_proj/ensembles_prolongement_cofinal`)
avant d'être promu ici : c'est une TACTIQUE, elle n'appartient à aucune théorie
particulière et ne doit pas forcer le chapitre IV à importer le chapitre III.
Le module d'origine la ré-exporte, les imports existants restent valides.

FRONTIÈRE DE CONFIANCE.  Rien ici ne fabrique de `Theoreme` : tout passe par
`loi_deduction`, `generalisation`, `instancie` (dérivée) et `modus_ponens` du
noyau.  Un portage refusé lève, il ne produit jamais un théorème non fondé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N


def porter_aux_termes(thm, substitutions):
    """Porte un théorème écrit AUX NOMS vers des TERMES.  [tactique générique].

    `substitutions` : dict {nom: terme}, appliqué SIMULTANÉMENT.

    Découvre lui-même les hypothèses portantes (`libres_f`), les décharge en
    antécédents, généralise, instancie, puis les ré-assume une fois substituées.
    Les hypothèses qui ne portent aucun des noms restent en place.

    ⚠️ Les termes fournis ne doivent pas capturer : cf. les noms réservés du
    dépôt (u, v, z pour est_fonctionnel ; v et y pour le kit C54 ; z pour
    est_un_graphe).  En cas de capture, l'assertion de conclusion du site
    appelant le révèle — ne jamais se contenter du compte d'hypothèses."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f, subst_f,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie,
    )
    noms = list(substitutions)
    portantes = [h for h in thm.hypotheses
                 if any(n in libres_f(h) for n in noms)]
    imp = thm
    for h in portantes:                       # empile : la dernière est l'externe
        imp = N.loi_deduction(h, imp)
    for n in noms:                            # ∀ dans l'ordre de `noms`
        imp = N.generalisation(n, imp)
    inst = imp
    for n in reversed(noms):                  # instancie dans l'ordre inverse
        inst = instancie(inst, substitutions[n])
    for h in reversed(portantes):             # dépile et ré-assume, substitué
        hs = h
        for n, t in substitutions.items():
            hs = subst_f(t, n, hs)
        inst = N.modus_ponens(N.assume(hs), inst)
    return inst


__all__ = ["porter_aux_termes"]
