# -*- coding: utf-8 -*-
"""Goldbach — LA SYMÉTRIE DU CRIBLE : les solutions vont par paires.

🎯 CIBLE de ce module :

    ⊢ (∀k)(∀m)[ ( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ )
                ⇒ (∃m')( ( m' ∈ P₂ₖ ∧ m' ∈ Q₂ₖ ) ∧ 2k = m + m' ) ]

Dès qu'un point de la rencontre existe, il vient **avec son partenaire**, et
les deux somment à `2k`. La rencontre est donc stable par l'involution
`m ↦ 2k − m`, dont le point fixe est `k` (puisque `2k = k + k`).

POURQUOI CE RÉSULTAT-LÀ, MAINTENANT. La carte a refermé deux voies par la
négative : le **comptage** brut (le critère des tiroirs `2·π(2k) > 2k+1` ne
tient pour aucun `k ≥ 2`) et l'**équationnel** (les organes de réécriture ne
déplacent pas la frontière d'un pouce). Les deux disent la même chose : il
faut de l'information sur la **répartition** de `P₂ₖ`, pas sur sa taille ni
sur la forme de l'énoncé. La symétrie est exactement cela — une contrainte
structurelle sur *où* les solutions peuvent se trouver.

LA ROUTE, en une phrase : le partenaire `m'` est le **témoin `y` du miroir**.
`m ∈ Q₂ₖ` fournit un `y` premier avec `2k = m + y` ; ce `y` est dans `P₂ₖ`
(premier, et borné par `y ≤ m + y = 2k`), et `m` rejoue dans le miroir de `y`
par commutativité de la somme.

⚠️ LES DEUX HABITS α SE CROISENT ICI, et c'est ce qui rend le portage non
trivial. Le témoin du miroir sort en habit 2 et doit entrer dans `P` en
habit 1 ; réciproquement `m` sort de `P` en habit 1 et doit entrer dans le
miroir en habit 2. Les **deux** sens de `pont_alpha_premier_ent` sont donc
requis — c'est ce besoin qui a fait paramétrer le pont.

⚠️ CE QUE ÇA N'ÉTABLIT PAS. Rien sur l'existence d'une solution : l'énoncé est
conditionnel (« s'il y en a une, il y en a deux »). Goldbach reste ouverte.
[CLOS au sens du noyau, SOUS les 2 axiomes de la théorie du crible.]
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, et, existe, subst_f, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    membre_intervalle_entiers_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.machine_num import NUM, fic_t
from recherche.goldbach.composes import HABIT_1, HABIT_2, pont_alpha_premier_ent
from recherche.goldbach.crible import (
    LIANT_K, LIANT_M, membre_miroir, membre_premiers_bornes, miroir,
    premiers_bornes,
)

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite
ZERO = NUM(0)

#: liant du partenaire — frais vis-à-vis de m, y, p, q
LIANT_PARTENAIRE = "mp2"


def _borne_droite(vm, vy):
    """⊢ Card y ≤ m + y   (la borne par le membre DROIT de la somme)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
        inf_egal_somme_droite_binaire,
    )
    return inf_egal_somme_droite_binaire(vm, vy)


def cible_partenaire(k=LIANT_K, m=LIANT_M):
    """(∃m')( ( m' ∈ P₂ₖ ∧ m' ∈ Q₂ₖ ) ∧ 2k = m + m' )."""
    M = SC(var(k), var(k))
    vmp = var(LIANT_PARTENAIRE)
    return existe(LIANT_PARTENAIRE,
                  et(et(appartient(vmp, premiers_bornes(M)),
                        appartient(vmp, miroir(M))),
                     egal(M, SC(var(m), vmp))))


def symetrie_du_crible(k=LIANT_K, m=LIANT_M):
    """🎯 ⊢ (∀k)(∀m)[ m ∈ P₂ₖ ∩ Q₂ₖ ⇒ (∃m') m' ∈ P₂ₖ ∩ Q₂ₖ ∧ 2k = m + m' ].

    `m` est GÉNÉRALISÉ, pas éliminé : la cible parle de lui (`2k = m + m'`),
    donc on ne peut pas le décharger comme un témoin anonyme."""
    vk, vm = var(k), var(m)
    M = SC(vk, vk)

    hm = N.assume(et(appartient(vm, premiers_bornes(M)),
                     appartient(vm, miroir(M))))
    #   premier_ent₁(m), depuis P
    prem_m1 = _cg(_mp(_cg(hm), _cg(membre_premiers_bornes(M, vm))))
    #   le témoin y du miroir — on LIT le liant produit par le noyau
    corps_Q = _mp(_cd(hm), _cg(membre_miroir(M, vm)))
    exY = corps_Q.conclusion
    assert getattr(exY, "tag", None) == "exists", "symétrie : miroir sans ∃"
    ly, maty = exY.lieur, exY.sous[0]
    vy = var(ly)

    hy = N.assume(maty)
    prem_y2, somme_my = _cg(hy), _cd(hy)       # premier_ent₂(y) ; 2k = m+y
    fini_y = _cg(prem_y2)

    #   ── y ∈ P₂ₖ : il faut l'habit 1, et la borne y ≤ 2k ────────────────
    prem_y1 = _mp(prem_y2, pont_alpha_premier_ent(ly, HABIT_2, HABIT_1))
    card_y = _mp(fini_y, fic_t(vy))
    zero_le_y = _mp(card_y, N.loi_deduction(est_cardinal(vy),
                                            zero_inf_egal_cardinal(vy)))
    #   Card y ≤ m+y, puis on réécrit m+y en 2k, puis Card y en y (Leibniz S6)
    somme_sym = _mp(somme_my, symetrie(M, SC(vm, vy)))         # m+y = 2k
    s6b = N.s6(SC(vm, vy), M, "wsym", inf_egal_card(cardinal(vy), var("wsym")))
    cardy_le_2k = _mp(_borne_droite(vm, vy), _cg(_mp(somme_sym, s6b)))
    s6y = N.s6(cardinal(vy), vy, "wsy2", inf_egal_card(var("wsy2"), M))
    y_le_2k = _mp(cardy_le_2k,
                  _cg(_mp(_mp(card_y, _cardinal_est_son_cardinal(vy)), s6y)))
    y_in_int = _mp(conjonction_intro(conjonction_intro(card_y, zero_le_y),
                                     y_le_2k),
                   _cd(membre_intervalle_entiers_t(ZERO, M, vy)))
    y_in_P = _mp(conjonction_intro(prem_y1, y_in_int),
                 _cd(membre_premiers_bornes(M, vy)))

    #   ── m ∈ Q₂ₖ (le miroir de y) : habit 2 pour m, et 2k = y+m ─────────
    prem_m2 = _mp(prem_m1, pont_alpha_premier_ent(m, HABIT_1, HABIT_2))
    somme_ym = composer_egalites(somme_my, somme_cardinale_commutative(vm, vy))
    impQ_y = _cd(membre_miroir(M, vy))
    exZ = impQ_y.conclusion.sous[0].sous[0]
    assert getattr(exZ, "tag", None) == "exists", "symétrie : miroir de y sans ∃"
    fourni = conjonction_intro(prem_m2, somme_ym)
    assert fourni.conclusion == subst_f(vm, exZ.lieur, exZ.sous[0]), \
        "symétrie : matrice du miroir de y ≠ attendue"
    m_in_Q = _mp(_mp(fourni, N.s5(exZ.sous[0], vm, exZ.lieur)), impQ_y)

    #   ── le partenaire m' := y ──────────────────────────────────────────
    CIBLE = cible_partenaire(k, m)
    ex_mp = _mp(conjonction_intro(conjonction_intro(y_in_P, m_in_Q), somme_my),
                N.s5(CIBLE.sous[0], vy, LIANT_PARTENAIRE))
    assert ex_mp.conclusion == CIBLE, "symétrie : cible partenaire mal formée"

    imp_y = existe_elimination(N.loi_deduction(maty, ex_mp), ly)
    corps = N.loi_deduction(hm.conclusion, _mp(corps_Q, imp_y))
    th = N.generalisation(k, N.generalisation(m, corps))
    assert th.est_clos and not th.hypotheses, "symétrie du crible : non clos"
    return th


__all__ = ["LIANT_PARTENAIRE", "cible_partenaire", "symetrie_du_crible"]
