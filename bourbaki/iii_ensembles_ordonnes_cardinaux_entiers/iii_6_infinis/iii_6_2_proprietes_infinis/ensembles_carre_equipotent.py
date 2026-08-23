# -*- coding: utf-8 -*-
"""§III.6.3 — LE PONT du Théorème 2 : du niveau CARDINAL au niveau ENSEMBLE.

🎯 CIBLE :

    carre_equipotent_sous_hessenberg(A) :
        { enonce_hessenberg(A), est_infini(Card A) }  ⊢  Eq(A × A, A)

POURQUOI CE MODULE EXISTE.  Le Théorème 2 est prouvé au niveau des CARDINAUX —
`enonce_hessenberg(A)` conclut `Card A · Card A = Card A`.  Mais son corollaire
aⁿ = a (`ensembles_a_puissance_n_er`) réclame l'hypothèse au niveau des
ENSEMBLES, sous la forme `hyp_carre(A) = Eq(A×A, A)`.  Sa docstring annonçait
une décharge « via hessenberg_0hyp » — cette fonction n'a jamais été écrite, et
le pont manquait.  Le voici.

⚠️ RÈGLE PERF.  `enonce_hessenberg(A)` est porté en HYPOTHÈSE HONNÊTE, non
dérivé ici : sa preuve coûte 5172,8 s (mesuré le 2026-08-23).  On la décharge
UNE fois, au dernier étage, jamais dans une brique intermédiaire.

LA ROUTE, en trois pas et sans détour :
  · `produit_cardinal_bien_defini(A, A, Card A, Card A)` nourri de deux
    réflexivités donne  Card(A×A) = Card A · Card A  — le produit cardinal ne
    dépend que des cardinaux des facteurs (E III.3.3) ;
  · Hessenberg donne  Card A · Card A = Card A ;
  · la transitivité donne  Card(A×A) = Card A, et la Proposition 1 dans son
    sens RÉCIPROQUE (`equipotent_si_cardinal_egal`) conclut  Eq(A×A, A).

⚠️ LEÇON 17.  `equipotent_si_cardinal_egal` et `produit_cardinal_bien_defini`
attendent des NOMS de variables, pas des termes : on les ∀-clôture (licite,
elles sont CLOSES) avant d'instancier aux termes voulus.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_si_cardinal_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _clot_puis_instancie(thm, noms, termes):
    """∀-clôture sur `noms` puis instanciation à `termes`, positionnellement.

    ⚠️ LEÇON 23 — `generalisation` EMPILE vers l'extérieur, `instancie` DÉPILE
    depuis l'extérieur.  Le dernier nom généralisé est donc le PREMIER
    instancié.  Pour que `noms[i]` reçoive `termes[i]`, il faut généraliser
    dans l'ordre INVERSE.  Généraliser dans l'ordre naturel produit une
    permutation silencieuse des arguments, dont le seul symptôme est un
    « mineure ≠ antécédent » très en aval."""
    for nom in reversed(noms):
        thm = N.generalisation(nom, thm)
    for terme in termes:
        thm = instancie(thm, terme)
    return thm


def _bien_defini_t(tX, tY, ta, tb):
    """`produit_cardinal_bien_defini` pour des TERMES (LEÇON 17 : elle veut des NOMS)."""
    return _clot_puis_instancie(
        produit_cardinal_bien_defini("Xpcd", "Ypcd", "apcd", "bpcd"),
        ("Xpcd", "Ypcd", "apcd", "bpcd"), (tX, tY, ta, tb))


def _prop1_reciproque_t(tX, tY):
    """`equipotent_si_cardinal_egal` pour des TERMES : ⊢ (Card X = Card Y) ⇒ Eq(X, Y)."""
    return _clot_puis_instancie(equipotent_si_cardinal_egal("Xp1r", "Yp1r"),
                                ("Xp1r", "Yp1r"), (tX, tY))


# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
#   (le Théorème 2 relu au niveau des ENSEMBLES : A×A est équipotent à A)
def carre_du_produit(a="A"):
    """⊢ Card(A × A) = Card A · Card A.   CLOS — 0 hypothèse.

    Le produit cardinal est BIEN DÉFINI : Card(X×Y) ne dépend que de Card X et
    Card Y (E III.3.3).  En X := Y := A et a := b := Card A, les deux
    antécédents sont des réflexivités."""
    vA = _t(a)
    cA = cardinal(vA)
    base = _bien_defini_t(vA, vA, cA, cA)
    res = N.modus_ponens(conjonction_intro(N.reflexivite(cA), N.reflexivite(cA)), base)
    assert res.conclusion == egal(cardinal(E.produit(vA, vA)),
                                  produit_cardinal_binaire(cA, cA)), \
        "carre_du_produit : forme"
    assert not res.hypotheses, "carre_du_produit : doit être CLOS"
    return res


# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
def carre_equipotent_sous_hessenberg(a="A"):
    """🎯 { enonce_hessenberg(A), est_infini(Card A) } ⊢ Eq(A × A, A).

    Le pont qui manquait entre le Théorème 2 et son Corollaire 1 : celui-là
    conclut sur les CARDINAUX, celui-ci réclame l'ENSEMBLE.

    Hessenberg est porté en hypothèse honnête (RÈGLE PERF : sa dérivation coûte
    5172,8 s, on ne la paie qu'une fois, au dernier étage)."""
    vA = _t(a)
    cA = cardinal(vA)
    AA = E.produit(vA, vA)

    #  Hessenberg, sous son antécédent : Card A · Card A = Card A
    hess = N.modus_ponens(N.assume(est_infini(cA)), N.assume(enonce_hessenberg(a)))
    assert hess.conclusion == egal(produit_cardinal_binaire(cA, cA), cA), \
        "carre_equipotent : l'énoncé de Hessenberg a changé de forme"

    #  Card(A×A) = Card A · Card A = Card A
    cardAA_eq = composer_egalites(carre_du_produit(a), hess)
    assert cardAA_eq.conclusion == egal(cardinal(AA), cA), \
        "carre_equipotent : Card(A×A) = Card A mal formé"

    res = N.modus_ponens(cardAA_eq, _prop1_reciproque_t(AA, vA))
    assert res.conclusion == equipotent(AA, vA), "carre_equipotent : forme"
    assert set(res.hypotheses) == {enonce_hessenberg(a), est_infini(cA)}, \
        "carre_equipotent : hypothèses résiduelles inattendues"
    return res


__all__ = ["carre_du_produit", "carre_equipotent_sous_hessenberg"]
