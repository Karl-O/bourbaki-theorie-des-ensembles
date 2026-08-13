"""Énumération et calcul sur les numéraux — ⊢ N(m)+N(n) = N(m+n), ⊢ N(m)·N(n) = N(m·n).

Séparé de `machine_num.py` (qui porte l'ordre et les génériques) pour tenir la
règle « une responsabilité par fichier » : ici, ce qui CALCULE.

────────────────────────────────────────────────────────────────────────────────
`enum` est la pièce qui referme un domaine borné : d ≤ N(k) ⇒ d = N(0) ou … ou
N(k).  C'est elle qui transforme un énoncé quantifié en un nombre FINI de cas, et
donc ce qui rend décidables, dans ce noyau, la non-divisibilité et la primalité.

`somme_num` et `produit_num` portent l'arithmétique proprement dite.  Tous deux
sont mémoïsés : sans cela `somme_num(3,3)` coûtait 54,4 s à chaque appel (mesuré
le 6 août 2026), le travail étant intégralement repayé.

Aucun `Theoreme` fabriqué, aucun axiome ajouté ; chaque résultat est vérifié à la
construction (conclusion attendue + clôture).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, ou, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    cardinal_vide_egale_vide,
)

from outils_ia.arithmetique.machine_num import (
    NUM, card_num, reecrit, _HOLE, _ble0_t, _so_t, _szn_t, _pcz_t, _ssd_t, _psd_t,
)

mp = N.modus_ponens


# ══════════════════════════════════════════════════════════════════════════════
#  ÉNUMÉRATION  —  ce qui referme un domaine borné
# ══════════════════════════════════════════════════════════════════════════════
def disj(vd, k):
    """La formule  ((d = N(0) ou d = N(1)) ou …) ou d = N(k)   (associée à gauche)."""
    f = egal(vd, NUM(0))
    for i in range(1, k + 1):
        f = ou(f, egal(vd, NUM(i)))
    return f


def enum(vd, k, card_d=None):
    """{est_cardinal(d)} ⊢ ( d ≤ N(k) ) ⇒ ( d = N(0) ou … ou d = N(k) ).

    Récurrence externe sur k : `successeur_ordre` scinde d ≤ N(j+1) en
    « d ≤ N(j) ou d = N(j+1) », et l'on recolle les deux branches par `cas`.
    Le cas de base est `b_le_0_implique_egal_0` (d ≤ 0 ⇒ d = 0)."""
    if card_d is None:
        card_d = N.assume(est_cardinal(vd))     # l'hypothèse reste dans le résultat
    cur = _ble0_t(vd)
    assert cur.conclusion == impl(inf_egal_card(vd, NUM(0)), disj(vd, 0))
    for j in range(0, k):
        Dj, eqj1 = disj(vd, j), egal(vd, NUM(j + 1))
        d_ou = mp(N.assume(inf_egal_card(vd, NUM(j + 1))),
                  equivalence_avant(mp(card_d, _so_t(vd, NUM(j)))))
        gg = mp(mp(N.assume(inf_egal_card(vd, NUM(j))), cur), N.s2(Dj, eqj1))
        br_g = N.loi_deduction(inf_egal_card(vd, NUM(j)), gg)
        dd = mp(mp(N.assume(eqj1), N.s2(eqj1, Dj)), N.s3(eqj1, Dj))
        br_d = N.loi_deduction(eqj1, dd)
        cur = N.loi_deduction(inf_egal_card(vd, NUM(j + 1)), cas(d_ou, br_g, br_d))
        assert cur.conclusion == impl(inf_egal_card(vd, NUM(j + 1)), ou(Dj, eqj1))
    return cur


# ══════════════════════════════════════════════════════════════════════════════
#  CALCUL  —  somme et produit de numéraux (mémoïsés : c'est la seconde économie)
# ══════════════════════════════════════════════════════════════════════════════
_SOMME, _PRODUIT = {}, {}


def somme_num(m, n):
    """⊢ N(m) + N(n) = N(m+n).   Récurrence sur n via `somme_succ_distribue`."""
    if (m, n) in _SOMME:
        return _SOMME[(m, n)]
    if n == 0:
        r = mp(card_num(m), _szn_t(NUM(m)))
    else:
        step = mp(conjonction_intro(card_num(m), card_num(n - 1)),
                  _ssd_t(NUM(m), NUM(n - 1)))
        cong = mp(somme_num(m, n - 1),
                  congruence_terme(somme_cardinale_binaire(NUM(m), NUM(n - 1)),
                                   NUM(m + n - 1), successeur(var(_HOLE)), w=_HOLE))
        r = composer_egalites(step, cong)
    assert r.conclusion == egal(somme_cardinale_binaire(NUM(m), NUM(n)), NUM(m + n))
    assert r.est_clos, "somme_num(%d,%d) non clos" % (m, n)
    _SOMME[(m, n)] = r
    return r


def produit_num(m, n):
    """⊢ N(m) · N(n) = N(m·n).   Récurrence sur n via `produit_succ_distribue`.

    Le cas n = 0 passe par `produit_cardinal_zero` puis la réécriture ∅ = Card ∅
    (`cardinal_vide_egale_vide` retournée) : les deux termes diffèrent, et les
    confondre serait la faute de fidélité déjà consignée ailleurs."""
    if (m, n) in _PRODUIT:
        return _PRODUIT[(m, n)]
    if n == 0:
        vide_eq = mp(cardinal_vide_egale_vide(), symetrie(cardinal(E.VIDE), E.VIDE))
        r = reecrit(vide_eq, _pcz_t(NUM(m)),
                    egal(cardinal(E.produit(NUM(m), var(_HOLE))), cardinal(E.VIDE)))
    else:
        step = mp(conjonction_intro(card_num(m), card_num(n - 1)),
                  _psd_t(NUM(m), NUM(n - 1)))
        cong = mp(produit_num(m, n - 1),
                  congruence_terme(produit_cardinal_binaire(NUM(m), NUM(n - 1)),
                                   NUM(m * (n - 1)),
                                   somme_cardinale_binaire(var(_HOLE), NUM(m)), w=_HOLE))
        r = composer_egalites(composer_egalites(step, cong), somme_num(m * (n - 1), m))
    assert r.conclusion == egal(produit_cardinal_binaire(NUM(m), NUM(n)), NUM(m * n))
    assert r.est_clos, "produit_num(%d,%d) non clos" % (m, n)
    _PRODUIT[(m, n)] = r
    return r


# Gate paramétré du volant (7 août 2026) — instances canoniques + caches déclarés.
somme_num_gate_caches = ("_SOMME",)


def somme_num_instances():
    """Instances canoniques : (args, énoncé attendu par ==)."""
    return [((1, 1), egal(somme_cardinale_binaire(NUM(1), NUM(1)), NUM(2))),
            ((2, 1), egal(somme_cardinale_binaire(NUM(2), NUM(1)), NUM(3)))]


produit_num_gate_caches = ("_PRODUIT",)


def produit_num_instances():
    return [((2, 1), egal(produit_cardinal_binaire(NUM(2), NUM(1)), NUM(2))),
            ((2, 2), egal(produit_cardinal_binaire(NUM(2), NUM(2)), NUM(4)))]


__all__ = ["disj", "enum", "somme_num", "produit_num"]
