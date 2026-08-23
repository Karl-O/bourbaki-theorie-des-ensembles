# -*- coding: utf-8 -*-
"""§III.6.1 — UN ENSEMBLE INFINI A UN ÉLÉMENT.

🎯 CIBLES, toutes deux CLOSES :

    infini_implique_non_vide(A) :  ⊢ est_infini(Card A) ⇒ ¬(A = ∅)
    infini_donne_element(A)     :  ⊢ est_infini(Card A) ⇒ (∃z)( z ∈ A )

POURQUOI.  Le Corollaire 1 du Théorème 2 (aⁿ = a) porte l'hypothèse `a₀ ∈ A` :
la récurrence a besoin d'un point de A pour construire ses injections.  Bourbaki
ne la mentionne pas, et il a raison — elle découle de « A infini ».  Encore
faut-il la dériver, ce que ce module fait, pour que le corollaire puisse s'en
débarrasser par ∃-élimination.

LA ROUTE, courte, et entièrement par contraposition :
  · si A = ∅ alors Card A = Card ∅ = 0 (Leibniz S6 sous l'égalité) ;
  · `fini_zero` est CLOSE : ⊢ Fini(0), premier entier naturel concret du dépôt ;
  · donc (A = ∅) ⇒ Fini(Card A), théorème CLOS ;
  · sa contraposée est exactement ¬Fini(Card A) ⇒ ¬(A = ∅), et `est_infini` est
    *par définition* ¬Fini (E III.6.1, Déf. 1) — aucun pont à construire ;
  · `non_vide_ssi_element` livre enfin le témoin.

⚠️ Rien ici ne suppose A infini au sens intuitif : la preuve ne connaît que la
définition de Bourbaki, « n'est pas un entier ».

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, existe, impl, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    contraposition, equivalence_arriere, equivalence_avant, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    non_vide_ssi_element,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)

_FRAIS = "wnv"


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.1 Def.1 | E III.45 L.3-4 | PDF p.148
#   (conséquence immédiate de la Déf. 1 : ∅ est fini, donc un infini n'est pas ∅)
def vide_est_fini(a="A"):
    """⊢ (A = ∅) ⇒ Fini(Card A).   CLOS — 0 hypothèse.

    Sous l'égalité, Leibniz (S6) transporte `Fini(Card ·)` de ∅ vers A ; et
    `Card ∅` EST `0` syntaxiquement (ZERO = CARD_VIDE), si bien que `fini_zero`
    s'applique sans réécriture."""
    vA = _t(a)
    h = N.assume(egal(vA, E.VIDE))
    leib = N.s6(vA, E.VIDE, _FRAIS, est_fini(cardinal(var(_FRAIS))))
    equiv = N.modus_ponens(h, leib)                 # Fini(Card A) ⇔ Fini(Card ∅)
    fini_A = N.modus_ponens(fini_zero(), equivalence_arriere(equiv))
    res = N.loi_deduction(egal(vA, E.VIDE), fini_A)
    assert res.conclusion == impl(egal(vA, E.VIDE), est_fini(cardinal(vA))), \
        "vide_est_fini : forme"
    assert not res.hypotheses, "vide_est_fini : doit être CLOS"
    return res


# @livre Ch.III §6.1 Def.1 | E III.45 L.3-4 | PDF p.148
def infini_implique_non_vide(a="A"):
    """🎯 ⊢ est_infini(Card A) ⇒ ¬(A = ∅).   CLOS — 0 hypothèse.

    La contraposée de `vide_est_fini`, et rien d'autre : `est_infini` étant
    DÉFINI comme ¬Fini (E III.6.1, Déf. 1), la contraposition tombe exactement
    sur la forme voulue, sans pont ni réécriture."""
    vA = _t(a)
    res = contraposition(vide_est_fini(a))
    assert res.conclusion == impl(est_infini(cardinal(vA)), non(egal(vA, E.VIDE))), \
        "infini_implique_non_vide : forme (est_infini a-t-il changé de définition ?)"
    assert not res.hypotheses, "infini_implique_non_vide : doit être CLOS"
    return res


# @livre Ch.III §6.1 Def.1 | E III.45 L.3-4 | PDF p.148
def infini_donne_element(a="A", z="z"):
    """🎯 ⊢ est_infini(Card A) ⇒ (∃z)( z ∈ A ).   CLOS — 0 hypothèse.

    Ce que le Corollaire 1 consomme : un point de A, dont il fera l'origine de
    ses injections.  `non_vide_ssi_element` attend un NOM (LEÇON 17) ; on la
    ∀-clôture avant d'instancier au terme."""
    vA = _t(a)
    frais = var(_FRAIS + "e")
    equiv = N.generalisation(frais.nom, non_vide_ssi_element(frais.nom))
    equiv = instancie(equiv, vA)                    # ¬(A=∅) ⇔ (∃z)(z∈A)
    h = N.assume(est_infini(cardinal(vA)))
    non_vide = N.modus_ponens(h, infini_implique_non_vide(a))
    elem = N.modus_ponens(non_vide, equivalence_avant(equiv))
    res = N.loi_deduction(est_infini(cardinal(vA)), elem)
    assert res.conclusion == impl(est_infini(cardinal(vA)),
                                  existe(z, appartient(var(z), vA))), \
        "infini_donne_element : forme (liant du ∃ ?)"
    assert not res.hypotheses, "infini_donne_element : doit être CLOS"
    return res


__all__ = ["vide_est_fini", "infini_implique_non_vide", "infini_donne_element"]
