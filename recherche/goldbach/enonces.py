# -*- coding: utf-8 -*-
"""Goldbach — LE SOCLE D'ÉNONCÉS : prélever les formules sans jamais les deviner.

POURQUOI CE MODULE EXISTE. Tous les résultats de l'arc Goldbach parlent des
mêmes deux morceaux de la forme « moitiés » :

    H := (∀k)[ A(k) ⇒ DEP(2k) ]
    A(k) := ( Fini k ∧ k ≠ 0 ) ∧ k ≠ 1        l'antécédent
    DEP(2k) := (∃p)(∃q)( premier₁(p) ∧ premier₂(q) ∧ k+k = p+q )

Chaque script de l'exploration les re-prélevait à la main, en descendant dans
`.sous[...]` à une profondeur devinée. C'est le plus gros gisement d'erreurs
silencieuses du chantier : `pourtout(x, F)` vaut `¬∃x¬F` et `impl(a, b)` vaut
`ou(¬a, b)`, si bien qu'un antécédent se lit à **profondeur exactement 3** puis
`.sous[0].sous[0]` — un cran de trop et l'on obtient une sous-formule qui a
l'air correcte et ne l'est pas.

LA GARDE ADOPTÉE ICI, et qui vaut pour tout le dossier : **tout prélèvement est
suivi d'une RECOMPOSITION vérifiée**. On redescend, puis on reconstruit la
formule d'origine à partir des morceaux et on exige l'égalité. Un prélèvement
faux ne peut alors pas se propager — il lève au premier appel.

⚠️ HONNÊTETÉ DE LA CLÔTURE. `N.axiome(TH, f)` rend un théorème dont
`hypotheses` est vide : `est_clos` ne signifie donc PAS « sans axiome ad hoc ».
Les modules qui consomment une théorie dédiée (le crible) exposent leurs
axiomes et passent par `atteste`, qui refuse de dire « clos » sans les nommer.
`theorie_ensembles() == 22` certifie la non-pollution de la théorie du livre,
pas l'absence d'axiome ajouté ailleurs.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    et, impl, non, pourtout, var,
)
from outils_ia.conjectures.goldbach import est_premier
from outils_ia.conjectures.goldbach_reduction import hypothese_moities

#: le liant de travail de tout l'arc — celui de `hypothese_moities`
LIANT_K = "kgb"


def _corps_du_pourtout(f, k):
    """Le corps d'un `pourtout(k, ·)`, prélevé à la profondeur RÉELLE.

    `pourtout(k, C)` est `¬(∃k)¬C` : trois niveaux, pas un de plus."""
    assert getattr(f, "tag", None) == "non", "attendu ¬∃¬ (pourtout)"
    ex = f.sous[0]
    assert getattr(ex, "tag", None) == "exists" and ex.lieur == k, \
        "pourtout : lieur %r attendu, %r trouvé" % (k, getattr(ex, "lieur", None))
    interne = ex.sous[0]
    assert getattr(interne, "tag", None) == "non", "pourtout : ¬ interne absent"
    return interne.sous[0]


def _membres_de_l_implication(c):
    """(antécédent, conséquent) d'un `impl(a, b)` = `ou(¬a, b)`."""
    assert getattr(c, "tag", None) == "ou", "attendu une implication (ou)"
    gauche = c.sous[0]
    assert getattr(gauche, "tag", None) == "non", "implication : ¬a attendu"
    return gauche.sous[0], c.sous[1]


def antecedent_et_decomposition(k=LIANT_K):
    """→ (A(k), DEP(2k)) prélevés de `hypothese_moities`, RECOMPOSITION vérifiée.

    C'est le seul endroit du dossier qui descend dans la structure de H : tous
    les autres modules appellent cette fonction."""
    H = hypothese_moities(k)
    corps = _corps_du_pourtout(H, k)
    a, dep = _membres_de_l_implication(corps)
    #   la garde : on remonte, et l'on exige l'identité avec l'original
    assert pourtout(k, impl(a, dep)) == H, \
        "prélèvement de H : la recomposition ne redonne pas l'original"
    return a, dep


def antecedent_moities(k=LIANT_K):
    """A(k) := ( Fini k ∧ k ≠ 0 ) ∧ k ≠ 1."""
    return antecedent_et_decomposition(k)[0]


def decomposition_de(k=LIANT_K):
    """DEP(2k) := (∃p)(∃q)( premier₁(p) ∧ premier₂(q) ∧ k+k = p+q ).

    ⚠️ NON GARDÉE : les témoins ne sont pas contraints à être des entiers.
    C'est l'énoncé du dépôt, avec son défaut de fidélité mesuré (voir
    `audit_fidelite`). La forme GARDÉE vit dans `crible.decomposition_gardee`,
    et les deux ne sont PAS interchangeables : `DEC_ent ⇒ DEP` est démontré
    (`synthese.gardee_implique_depot`), la réciproque ne l'est pas."""
    return antecedent_et_decomposition(k)[1]


def hypothese_composes_decomposition(k=LIANT_K):
    """HC_dep := (∀k)[ ( A(k) ∧ ¬premier₁(k) ) ⇒ DEP(2k) ].

    « la conjecture restreinte à ses instances COMPOSÉES », version
    décomposition. C'est l'hypothèse de la réduction GG7."""
    a, dep = antecedent_et_decomposition(k)
    return pourtout(k, impl(et(a, non(est_premier(var(k), d="d1", q="q1"))), dep))


def hypothese_composes_rencontre(k=LIANT_K):
    """HC_renc := (∀k)[ ( A(k) ∧ ¬premier₁(k) ) ⇒ rencontre(k) ].

    ⚠️ À NE PAS CONFONDRE avec `hypothese_composes_decomposition` : même
    antécédent, conséquent différent (la forme crible au lieu de la forme
    décomposition). Les deux se ressemblent à l'affichage — la confusion a
    déjà été faite. C'est l'hypothèse de la synthèse GG24."""
    from recherche.goldbach.crible import rencontre
    a, _ = antecedent_et_decomposition(k)
    return pourtout(k, impl(et(a, non(est_premier(var(k), d="d1", q="q1"))),
                            rencontre(k)))


def atteste(th, axiomes=()):
    """→ une ligne d'état HONNÊTE pour un théorème.

    `est_clos` seul est trompeur : un théorème tiré d'une théorie dédiée par
    `N.axiome` a bien zéro hypothèse. Cette fonction force à nommer les
    axiomes ad hoc consommés — s'il y en a, elle le dit."""
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    etat = "CLOS" if (th.est_clos and not th.hypotheses) else (
        "SOUS %d hypothèse(s)" % len(th.hypotheses))
    socle = ("0 axiome ad hoc" if not axiomes
             else "%d axiome(s) ad hoc : %s" % (len(axiomes), ", ".join(axiomes)))
    return "%s | %s | theorie_ensembles() = %d" % (
        etat, socle, len(E.theorie_ensembles().axiomes))


__all__ = [
    "LIANT_K", "antecedent_et_decomposition", "antecedent_moities",
    "decomposition_de", "hypothese_composes_decomposition",
    "hypothese_composes_rencontre", "atteste",
]
