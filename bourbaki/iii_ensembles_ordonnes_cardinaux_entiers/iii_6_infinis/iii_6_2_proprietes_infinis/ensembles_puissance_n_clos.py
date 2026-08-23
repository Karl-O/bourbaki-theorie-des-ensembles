# -*- coding: utf-8 -*-
"""§III.6.3, Corollaire 1 — aⁿ = a POUR a INFINI, sous la seule hypothèse du livre.

🎯 CIBLE :

    puissance_n_clos(A) :
        { enonce_hessenberg(A) }  ⊢  est_infini(Card A) ⇒ (∀n)( (n entier et n≥1)
                                                                ⇒ Eq(𝓕(n;A), A) )

CE QUI MANQUAIT.  `a_puissance_n_egale_a` construit tout le corollaire —
récurrence sur n depuis 1, bornes inf et sup, Cantor–Bernstein — mais sous TROIS
hypothèses.  Sa docstring annonçait la décharge de la principale « via
hessenberg_0hyp » : cette fonction n'a jamais été écrite (une seule occurrence
dans tout le dépôt, celle de la docstring qui la promet).  Les trois décharges
sont maintenant disponibles, et ce module les assemble.

    hyp_carre(A) = Eq(A×A, A)      ← `carre_equipotent_sous_hessenberg`
    a₀ ∈ A                         ← `infini_donne_element` (CLOS) + ∃-élimination
    predecesseur_fini_universel    ← `predecesseur_fini_universel_preuve` (CLOS)

⚠️ RÈGLE PERF.  `enonce_hessenberg(A)` reste une HYPOTHÈSE HONNÊTE : sa preuve
coûte 5172,8 s (mesuré le 2026-08-23).  On ne la décharge qu'au tout dernier
étage, jamais ici.

⚠️ L'∃-ÉLIMINATION est licite parce que la conclusion NE MENTIONNE PAS a₀ — et
parce qu'à l'instant où on l'applique, les deux hypothèses restantes
(`enonce_hessenberg(A)` et `est_infini(Card A)`) ne le mentionnent pas non plus.
D'où l'ordre imposé : décharger d'abord pfu et le carré, éliminer a₀ ENSUITE.

⚠️ Le liant du ∃ diffère d'un module à l'autre — « z » chez
`infini_donne_element` (il vient de `non_vide_ssi_element`), « a0 » chez le
corollaire.  Pont α explicite, jamais de reconstruction de formule (LEÇON 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, impl, appartient, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_a_puissance_n_er import (
    a_puissance_n_egale_a, enonce_a_puissance_n_egale_a, hyp_carre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_carre_equipotent import (
    carre_equipotent_sous_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_infini_non_vide import (
    infini_donne_element,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge `formule` de `thm` au moyen de `preuve` (modus ponens + déduction)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _pfu_preuve():
    """`predecesseur_fini_universel_preuve` — CLOSE (Prop. 2 §III.5, ~7,7 s).

    Import PARESSEUX : le module est lourd et n'est utile qu'ici."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    return predecesseur_fini_universel_preuve()


# @livre Ch.III §6.3 Cor.1 | E III.49 L.5-6 | PDF p.152
def puissance_n_sous_hessenberg(a0="a0", a="A"):
    """{ enonce_hessenberg(A), est_infini(Card A) } ⊢ (∀n≥1) aⁿ = a.

    Étage intermédiaire : les trois hypothèses du corollaire déchargées, mais
    a₀ pas encore éliminé — c'est l'étage où il faut vérifier que plus aucune
    hypothèse ne le mentionne, condition de licéité de l'∃-élimination."""
    vA = _t(a)
    base = a_puissance_n_egale_a(a0, a)          # {pfu, hyp_carre, a₀∈A}

    #  (1) predecesseur_fini_universel : le dépôt la PROUVE, il ne la branchait pas.
    pfu = _pfu_preuve()
    if pfu.conclusion in base.hypotheses:
        base = _cut(pfu, pfu.conclusion, base)

    #  (2) le carré : Hessenberg relu au niveau des ENSEMBLES.
    carre = carre_equipotent_sous_hessenberg(a)   # {enonce_hessenberg, est_infini}
    assert carre.conclusion == hyp_carre(a), \
        "puissance_n : le pont ne conclut plus hyp_carre"
    assert carre.conclusion in base.hypotheses, \
        "puissance_n : hyp_carre absente des hypothèses du corollaire"
    base = _cut(carre, carre.conclusion, base)

    reste = set(base.hypotheses) - {appartient(var(a0), vA)}
    assert not any(a0 in libres_f(h) for h in reste), \
        "puissance_n : a₀ encore libre dans une hypothèse — ∃-élimination illicite"
    return base


# @livre Ch.III §6.3 Cor.1 | E III.49 L.5-6 | PDF p.152
def puissance_n_clos(a0="a0", a="A"):
    """🎯🎯 { enonce_hessenberg(A) } ⊢
           est_infini(Card A) ⇒ (∀n)( (n entier et n≥1) ⇒ Eq(𝓕(n;A), A) ).

    Le Corollaire 1 sous la SEULE hypothèse du livre — le Théorème 2 lui-même,
    porté en hypothèse honnête pour ne pas repayer ses 5172,8 s à chaque appel.

    `a₀ ∈ A` disparaît par ∃-élimination : `infini_donne_element` fournit
    l'existence d'un point, et la conclusion n'en nomme aucun."""
    vA = _t(a)
    infini = est_infini(cardinal(vA))
    base = puissance_n_sous_hessenberg(a0, a)

    #  (3) a₀ ∈ A : ∃-élimination.  Le liant vient de `non_vide_ssi_element`
    #  (« z ») et doit devenir « a0 » — pont α, jamais de reconstruction.
    elem = N.modus_ponens(N.assume(infini), infini_donne_element(a))
    if elem.conclusion.lieur != a0:
        elem = N.modus_ponens(elem, equivalence_avant(alpha_existe(
            elem.conclusion.lieur, a0, elem.conclusion.sous[0])))
    assert elem.conclusion.lieur == a0, "puissance_n_clos : pont α insuffisant"

    porte = N.loi_deduction(appartient(var(a0), vA), base)
    res = N.modus_ponens(elem, existe_elimination(porte, a0))

    res = N.loi_deduction(infini, res)
    assert res.conclusion == impl(infini, enonce_a_puissance_n_egale_a(a)), \
        "puissance_n_clos : forme"
    assert set(res.hypotheses) == {enonce_hessenberg(a)}, \
        "puissance_n_clos : il ne doit rester QUE le Théorème 2 (%d hyps)" % len(res.hypotheses)
    assert res.conclusion not in res.hypotheses, "puissance_n_clos : VACUOUS"
    return res


__all__ = ["puissance_n_sous_hessenberg", "puissance_n_clos"]
