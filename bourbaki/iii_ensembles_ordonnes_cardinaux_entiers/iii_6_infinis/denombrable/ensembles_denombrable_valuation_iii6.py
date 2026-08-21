# -*- coding: utf-8 -*-
"""§III.6 (prérequis Lemme 2, ℵ₀·ℵ₀=ℵ₀) — le PONT « a^(m+d) = a^m · a^d » au niveau
des opérations cardinales du dépôt (brique W3a de la 2-valuation).

🎯 CIBLE.  `exposant_somme_pont(base, m, d)` :

    ⊢ exposant_cardinal_binaire(base, m+d) = produit_cardinal_binaire(base^m, base^d),

avec m+d := somme_cardinale_binaire(m,d) = Card(m⊔d) et base^x :=
exposant_cardinal_binaire(base, x) = Card(𝓕(x; base)).  INCONDITIONNEL (0 hyp) :
les trois maillons sont Eq-ponts d'invariance, tous CLOS.

CHAÎNE (composer_egalites ×2), miroir exact de `distributivite_operations` :
  g1  Card(𝓕(Card(m⊔d); base)) = Card(𝓕(m⊔d; base))
      [Eq(Card(m⊔d), m⊔d) (equipotent_son_cardinal + symétrie) poussée par le
       keystone `eq_exposant_invariant` (but A ∀-clos puis instancié au TERME
       base), puis Prop. 1 directe] ;
  g2  Card(𝓕(m⊔d; base)) = Card(𝓕(m;base) × 𝓕(d;base))
      [`prop9_close` (a^(b+c)=a^b·a^c, INCONDITIONNEL, Cantor–Bernstein)] ;
  g3  Card(𝓕(m;base) × 𝓕(d;base)) = Card(base^m × base^d)
      [Eq(S, Card S) ×2 poussées par `eq_produit_invariant` (témoins F/G
       α-figés), puis Prop. 1 directe].

Usage aval : W3 (2-valuation, base:=DEUX) et W4 (3-injectivité, base:=TROIS).
theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _eq_son_cardinal_terme(t):
    """⊢ Eq(T, Card T) pour un TERME T (∀-clôture de equipotent_son_cardinal)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal)
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), _t(t))


def _eq_sym_t(tX, tY, eq_thm):
    """De ⊢ Eq(X,Y) déduit ⊢ Eq(Y,X)   (symétrie de Eq via _sym_all, aux termes)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        _sym_all)
    return N.modus_ponens(eq_thm, instancie(instancie(_sym_all(), _t(tX)), _t(tY)))


def exposant_somme_pont_cible(base, m, d):
    """Formule : base^(m+d) = base^m · base^d   (niveau opérations cardinales)."""
    vb, vm, vd = _t(base), _t(m), _t(d)
    lhs = exposant_cardinal_binaire(vb, somme_cardinale_binaire(vm, vd))
    rhs = produit_cardinal_binaire(exposant_cardinal_binaire(vb, vm),
                                   exposant_cardinal_binaire(vb, vd))
    return egal(lhs, rhs)


# @livre Ch.III §3.5 Cor.1 | E III.28 L.29-30 | PDF p.131
def exposant_somme_pont(base, m="mvw", d="dvw"):
    """🎯 ⊢ base^(m+d) = base^m · base^d.   (Cor.1 §III.3.5 aux OPÉRATIONS cardinales.)

    Voir la chaîne g1-g2-g3 en tête de module.  base, m, d : noms OU termes ;
    INCONDITIONNEL (0 hyp)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import (
        eq_exposant_invariant)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
        eq_produit_invariant)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_final_close import (
        prop9_close)

    vb, vm, vd = _t(base), _t(m), _t(d)
    MD = somme_disjointe(vm, vd)                       # m ⊔ d
    SC = cardinal(MD)                                  # m + d = Card(m⊔d)
    Fsc = E.applications(SC, vb)                       # 𝓕(m+d; base)
    Fmd = E.applications(MD, vb)                       # 𝓕(m⊔d; base)
    Fm = E.applications(vm, vb)                        # 𝓕(m; base)
    Fd = E.applications(vd, vb)                        # 𝓕(d; base)
    expm = exposant_cardinal_binaire(vb, vm)           # base^m = Card 𝓕(m;base)
    expd = exposant_cardinal_binaire(vb, vd)           # base^d

    # g1 : Card 𝓕(m+d;base) = Card 𝓕(m⊔d;base)
    eq_sc_md = _eq_sym_t(MD, SC, _eq_son_cardinal_terme(MD))     # Eq(Card(m⊔d), m⊔d)
    #   keystone AUX NOMS (ses sous-lemmes internes sont à noms fixes X/Y) :
    #   ∀-clore sur A, X, Y puis instancier aux TERMES (le noyau α-gère les
    #   τ-cardinaux passés en argument)
    g_inv = N.generalisation("A", N.generalisation("X", N.generalisation(
        "Y", eq_exposant_invariant("X", "Y", "A"))))
    inv_exp = instancie(instancie(instancie(g_inv, vb), SC), MD)
    eq_F = N.modus_ponens(eq_sc_md, inv_exp)           # Eq(𝓕(m+d;base), 𝓕(m⊔d;base))
    g1 = N.modus_ponens(eq_F, _prop1_direct_t(Fsc, Fmd))

    # g2 : Card 𝓕(m⊔d;base) = Card(𝓕(m;base) × 𝓕(d;base))   (Prop. 9, INCONDITIONNEL)
    g2 = prop9_close(vb, vm, vd)

    # g3 : Card(𝓕(m;base) × 𝓕(d;base)) = Card(base^m × base^d)
    eq_m = _eq_son_cardinal_terme(Fm)                  # Eq(𝓕(m;base), base^m)
    eq_d = _eq_son_cardinal_terme(Fd)                  # Eq(𝓕(d;base), base^d)
    inv_prod = eq_produit_invariant("F", "G", Fm, Fd, expm, expd)
    eq_prod = N.modus_ponens(conjonction_intro(eq_m, eq_d), inv_prod)
    g3 = N.modus_ponens(eq_prod, _prop1_direct_t(E.produit(Fm, Fd),
                                                 E.produit(expm, expd)))

    res = composer_egalites(composer_egalites(g1, g2), g3)
    assert res.conclusion == exposant_somme_pont_cible(vb, vm, vd), \
        f"exposant_somme_pont : conclusion inattendue\n{res.conclusion}"
    assert not res.hypotheses, "exposant_somme_pont : hypothèses résiduelles"
    return res


__all__ = ["exposant_somme_pont", "exposant_somme_pont_cible"]
