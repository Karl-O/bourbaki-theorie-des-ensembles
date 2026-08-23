# -*- coding: utf-8 -*-
"""§III.6.3, Corollaire 4 — VOLET PRODUIT : a · b = a pour 1 ≤ b ≤ a, a infini.

🎯 CIBLE :

    cor4_produit(A, b) :
        { enonce_hessenberg(A), est_infini(Card A), b ≤ Card A, 1 ≤ b }
            ⊢  Card A · b = Card A

C'est l'autre moitié du Corollaire 4 (E III.49), « ab = sup(a,b) ».  Le volet
SOMME est dans `ensembles_cor4_somme` ; les deux ensemble donnent l'énoncé du
livre, sous la garde « b ≤ Card A » qui explicite le sup (cf. la note de forme
dans le module somme).

⚠️ C'EST ICI QUE SERT « b ≠ 0 ».  Bourbaki exige a et b NON NULS ; la garde
n'avait pas encore servi dans le volet somme (a + b ≥ a vaut même pour b = 0).
Pour le produit elle est indispensable : a · 0 = 0 ≠ a.  On la prend sous la
forme utilisable « 1 ≤ b », équivalente à b ≠ 0 pour un cardinal.

LA ROUTE :
    a · b ≤ a · a          [monotonie droite du produit, sous b ≤ a]
    a · a = a              [le conséquent du Théorème 2]
    a = a · 1 ≤ a · b      [1 est neutre, puis monotonie sous 1 ≤ b]
    ⇒ a · b = a            [antisymétrie de ≤ sur les cardinaux]

⚠️ La borne INFÉRIEURE n'est pas symétrique de celle de la somme : là où
« a ≤ a + b » se lit sur l'injection gauche, « a ≤ a · b » passe par la
neutralité de 1 — et donc par le PIÈGE DES TROIS « UN » (LEÇON 16), que
`produit_par_un` encapsule une fois pour toutes.

⚠️ RÈGLE PERF : `enonce_hessenberg(A)` reste porté, jamais dérivé ici.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    cardinal_egal_si_equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinal_ordre_props import (
    produit_cardinale_monotone_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    _cardinal_est_son_cardinal_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    UN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
    est_cardinal_de_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_absorption import (
    produit_par_un,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_absorption_generale import (
    carre_depuis_hessenberg,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def enonce_cor4_produit(a="A", b="bc4"):
    """FORMULE : Card A · b = Card A."""
    cA = cardinal(_t(a))
    return egal(produit_cardinal_binaire(cA, _t(b)), cA)


# @livre Ch.III §6.3 Cor.4 | E III.49 L.28-30 | PDF p.152
#   (« ab = sup(a,b) » — moitié PRODUIT, cas binaire, sous 1 ≤ b ≤ a)
def cor4_produit(a="A", b="bc4"):
    """🎯 { enonce_hessenberg(A), est_infini(Card A), b ≤ Card A, 1 ≤ b }
           ⊢ Card A · b = Card A.

    La moitié « produit » du Corollaire 4.  La garde « 1 ≤ b » est le « b non
    nul » de Bourbaki, sous la forme dont la preuve a besoin."""
    vA, vb = _t(a), _t(b)
    cA = cardinal(vA)
    prod_ab = produit_cardinal_binaire(cA, vb)
    carre = produit_cardinal_binaire(cA, cA)

    #  ── (0) a est un cardinal, donc Card a = a ──────────────────────────────
    h_card = est_cardinal_de_cardinal(vA)                # est_cardinal(Card A)
    card_a = N.modus_ponens(h_card, _cardinal_est_son_cardinal_t(cA))

    #  ── (1) a·b ≤ a·a   (monotonie du facteur DROIT, sous b ≤ a) ───────────
    h_le = N.assume(inf_egal_card(vb, cA))
    haut = N.modus_ponens(h_le, produit_cardinale_monotone_droite(vb, cA, cA))
    assert haut.conclusion == inf_egal_card(prod_ab, carre), \
        "cor4_produit : la monotonie ne donne pas a·b ≤ a·a"

    #  ── (2) a·a = a, puis réécriture de Leibniz SUR LA FORMULE ─────────────
    sq = carre_depuis_hessenberg(a)                      # a·a = a
    haut = N.modus_ponens(haut, equivalence_avant(N.modus_ponens(
        sq, N.s6(carre, cA, "wp4", inf_egal_card(prod_ab, var("wp4"))))))
    assert haut.conclusion == inf_egal_card(prod_ab, cA), "cor4_produit : a·b ≤ a"

    #  ── (3) a = a·1 ≤ a·b   (neutralité de 1, puis monotonie sous 1 ≤ b) ───
    _, a_un = produit_par_un(cA, card_a)                 # a·1 = a
    h_un = N.assume(inf_egal_card(UN, vb))
    bas = N.modus_ponens(h_un, produit_cardinale_monotone_droite(UN, vb, cA))
    assert bas.conclusion == inf_egal_card(produit_cardinal_binaire(cA, UN), prod_ab), \
        "cor4_produit : la monotonie ne donne pas a·1 ≤ a·b"
    bas = N.modus_ponens(bas, equivalence_avant(N.modus_ponens(
        a_un, N.s6(produit_cardinal_binaire(cA, UN), cA, "wp4",
                   inf_egal_card(var("wp4"), prod_ab)))))
    assert bas.conclusion == inf_egal_card(cA, prod_ab), "cor4_produit : a ≤ a·b"

    #  ── (4) antisymétrie ────────────────────────────────────────────────────
    anti = instancie(instancie(inf_egal_antisymetrique_card(), prod_ab), cA)
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(haut, bas), est_cardinal_de_cardinal(E.produit(cA, vb))),
        h_card), anti)

    assert res.conclusion == enonce_cor4_produit(a, b), "cor4_produit : forme"
    assert set(res.hypotheses) == {enonce_hessenberg(a), est_infini(cA),
                                   inf_egal_card(vb, cA), inf_egal_card(UN, vb)}, \
        "cor4_produit : hypothèses résiduelles inattendues (%d)" % len(res.hypotheses)
    return res


__all__ = ["enonce_cor4_produit", "cor4_produit"]
