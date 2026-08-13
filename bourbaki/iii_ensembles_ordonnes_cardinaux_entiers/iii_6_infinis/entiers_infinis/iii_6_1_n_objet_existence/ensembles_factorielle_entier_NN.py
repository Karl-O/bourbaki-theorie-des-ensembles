"""§III.6.1 — LA RÉCOLTE (brique N2) :  « n! est un entier », SUR ℕ, à 4 hypothèses.

`factorielle_entier_complet` (les DEUX moitiés (R0)/(Rs) dérivées) instancié aux
TERMES CLOS ℕ = ensemble_NN() et G≤ = G_ordre_NN(), puis TOUT ce qui se décharge
est déchargé :

    bo(R_G≤, ℕ)       ← `bo_graphe_NN()`                    [CLOS]
    ZERO ∈ ℕ          ← `zero_dans_NN()`                    [CLOS]
    H1..H4 (position) ← `donnees_ordre_NN()`  (brique N1)   [CLOSES]

RESTE : { essais_bien_formes, rule_codomain, essais_restriction } — les données de
la RÈGLE seules — plus UN résidu nommé : seg(ℕ, ZERO) = ∅ (« rien avant 0 »,
dérivable au terme mais pas encore dérivé — brique séparée).  Statut :
**CLOS MODULO données de la règle + seg(ℕ,0)=∅** — 4 hypothèses.

⚠️ PERF : tout est τ-lourd à ℕ (l'inflation variables→termes clos est le poste
dominant mesuré du dépôt) — test en arrière-plan détaché, jamais inline.
INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, pourtout, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, zero_dans_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, bo_graphe_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (
    donnees_ordre_NN, seg_zero_vide,
)


def _dech(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 { ebf, rc, essais_restriction, seg(ℕ,0)=∅ } ⊢ (∀n)( Fini n ⇒ Fini f(n) )
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (la caractérisation de n!, instanciée sur le VRAI ℕ ; bo et toutes les données de position DÉCHARGÉES — restent les données de la règle et « rien avant 0 »)
def factorielle_entier_NN(V="Vfac62"):
    """🎯🎯🎯 { essais_bien_formes, rule_codomain, essais_restriction } ⊢
        (∀n)( est_fini n ⇒ est_fini( valeur(f, n) ) )   à  e=ℕ, G=G≤     [3 hyps]

    LE CAPSTONE DE L'INSTANCIATION : « n! est un entier » sur le VRAI ℕ, les deux
    moitiés (R0)/(Rs) dérivées, et TOUT le reste déchargé par des théorèmes CLOS —
    bo (`bo_graphe_NN`), 0∈ℕ (`zero_dans_NN`), H1..H4 (`donnees_ordre_NN`) et
    seg(ℕ,0)=∅ (`seg_zero_vide`).  Les 3 hypothèses restantes sont LES DONNÉES DE
    LA RÈGLE SEULES (le prix honnête de « la règle factorielle est bien formée »).
    Chaque coupe est assertée par APPARTENANCE de la conclusion close au jeu
    d'hypothèses — un désalignement de forme échoue ICI, nommément, pas en aval."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ_vraie import (
        factorielle_entier_complet,
    )
    NN, G = ensemble_NN(), G_ordre_NN()

    base = factorielle_entier_complet(e=NN, G=G, V=V)    # 10 hyps, aux TERMES
    res = base

    # (1) bo(R_G≤, ℕ)  ←  bo_graphe_NN  [CLOS]
    bo = bo_graphe_NN()
    assert bo.conclusion in res.hypotheses, \
        "factorielle_entier_NN : bo_graphe_NN ≠ l'hypothèse bo de la chaîne (liants ?)"
    res = _dech(res, bo.conclusion, bo)

    # (2) ZERO ∈ ℕ  ←  zero_dans_NN  [CLOS]
    z = zero_dans_NN()
    assert z.conclusion in res.hypotheses, \
        "factorielle_entier_NN : zero_dans_NN ≠ l'hypothèse ZERO∈E de la chaîne"
    res = _dech(res, z.conclusion, z)

    # (3) H1..H4  ←  donnees_ordre_NN  [CLOSES]  (miroir asserté dans N1)
    for i, hi in enumerate(donnees_ordre_NN()):
        assert hi.conclusion in res.hypotheses, \
            "factorielle_entier_NN : H%d absente des hypothèses (forme ?)" % (i + 1)
        res = _dech(res, hi.conclusion, hi)

    # (4) seg(ℕ, ZERO) = ∅  ←  seg_zero_vide  [CLOS]  (« rien avant 0 », dérivé)
    s0 = seg_zero_vide()
    assert s0.conclusion in res.hypotheses, \
        "factorielle_entier_NN : seg_zero_vide ≠ l'hypothèse seg(ℕ,0)=∅ de la chaîne"
    res = _dech(res, s0.conclusion, s0)

    # reste : { ebf, rc, essais_restriction } — les données de la RÈGLE seules
    assert len(res.hypotheses) == 3, \
        "factorielle_entier_NN : hyps ≠ 3 (%d) — une coupe a raté" % len(res.hypotheses)

    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
        fonction_globale,
    )
    vn = var("nfe")
    fx = E.valeur(fonction_globale(NN, V), vn)           # le miroir de la cible
    assert res.conclusion == pourtout("nfe", impl(est_fini(vn), est_fini(fx))), \
        "factorielle_entier_NN : conclusion ≠ (∀n)(Fini n ⇒ Fini f(n)) à ℕ"
    assert res.conclusion not in res.hypotheses, "factorielle_entier_NN : VACUOUS"
    return res


__all__ = ["factorielle_entier_NN"]
