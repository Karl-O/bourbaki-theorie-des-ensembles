"""§III.4-5 — PIGEONHOLE, forme ÉQUIPOTENTE : une partie d'un FINI ÉQUIPOTENTE
au tout EST le tout.

🎯  partie_equipotente_egale :
        ⊢ ( X⊂E  et  est_fini_ensemble(E)  et  Eq(X,E) ) ⇒ X = E.

C'est EXACTEMENT le contenu combinatoire §III.4 réclamé par la résolution de la
trichotomie d'ordinaux (Prop. 6 §III.5, résidu `resolution_trichotomie` de
`ensembles_prop6_iso_iii5`) : « un SEGMENT (donc une PARTIE) d'un fini bien ordonné
ÉQUIPOTENT au tout est le tout entier » — un segment PROPRE aurait un cardinal
STRICTEMENT plus petit (Cor. 2 §III.4) et ne pourrait donc être équipotent au tout.

Ici on l'énonce SET-THÉORIQUEMENT (pour une partie quelconque, a fortiori un
segment) : c'est la brique combinatoire pure que la pigeonhole `partie_egal_cardinal_egal`
décharge enfin.

ROUTE (entièrement à partir de briques CLOSES) :
  1. Eq(X,E) ⇒ Card X = Card E   (Proposition 1 §III.3, SENS DIRECT,
     `cardinal_egal_si_equipotent`, généralisée-instanciée aux TERMES) ;
  2. ( X⊂E et est_fini_ensemble(E) et Card X = Card E ) ⇒ X = E   (pigeonhole
     `partie_egal_cardinal_egal`, CLOS 0 hyp).

⚠ INVARIANT : theorie_ensembles() = 22.  Rien postulé.  CLOS, 0 hypothèse.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import cardinal_egal_si_equipotent
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_pigeonhole_sous_lemme import (
    partie_egal_cardinal_egal, partie_egal_cardinal_egal_enonce,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cardinal_egal_si_equipotent_t(tX, tE):
    """⊢ Eq(tX,tE) ⇒ (Card tX = Card tE), capture-safe pour TERMES quelconques
    (généralise-instancie : les témoins-graphes internes de Prop 1 capturent sinon)."""
    g = N.generalisation("Xpeq", N.generalisation("Ypeq",
                         cardinal_egal_si_equipotent("Xpeq", "Ypeq")))
    return instancie(instancie(g, tX), tE)


def partie_equipotente_egale_enonce(X="Xpeq", Eens="Epeq"):
    """⊢-cible : ( X⊂E et est_fini_ensemble(E) et Eq(X,E) ) ⇒ X = E."""
    vX, vE = _t(X), _t(Eens)
    ante = et(et(inclus(vX, vE), est_fini_ensemble(vE)),
              equipotent(vX, vE))
    return impl(ante, egal(vX, vE))


def partie_equipotente_egale(X="Xpeq", Eens="Epeq"):
    """🎯 ⊢ ( X⊂E et est_fini_ensemble(E) et Eq(X,E) ) ⇒ X = E.   (CLOS, 0 hyp.)

    Pigeonhole, forme équipotente (cœur de la résolution-trichotomie Prop. 6 §III.5).
    Voir docstring de module pour la route."""
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)
    incl = inclus(vX, vE)
    Efini = est_fini_ensemble(vE)
    eqXE = equipotent(vX, vE)

    ante = et(et(incl, Efini), eqXE)
    h = N.assume(ante)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(h))    # X⊂E
    h_fini = conjonction_elim_droite(conjonction_elim_gauche(h))    # fini E
    h_eq = conjonction_elim_droite(h)                              # Eq(X,E)

    # (1) Card X = Card E   via Prop 1 (sens direct), capture-safe aux termes.
    card_eq = N.modus_ponens(h_eq, _cardinal_egal_si_equipotent_t(vX, vE))
    assert card_eq.conclusion == egal(cX, cE), \
        f"card_eq : {card_eq.conclusion} vs {egal(cX, cE)}"

    # (2) pigeonhole : ( X⊂E et fini E et Card X=Card E ) ⇒ X=E.
    pige = partie_egal_cardinal_egal(vX, vE)
    assert pige.conclusion == partie_egal_cardinal_egal_enonce(vX, vE)
    pige_ante = conjonction_intro(conjonction_intro(h_incl, h_fini), card_eq)
    X_eq_E = N.modus_ponens(pige_ante, pige)                       # X = E
    assert X_eq_E.conclusion == egal(vX, vE)

    res = N.loi_deduction(ante, X_eq_E)
    assert res.conclusion == partie_equipotente_egale_enonce(vX, vE), "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "partie_equipotente_egale : non close !"
    return res


__all__ = ["partie_equipotente_egale", "partie_equipotente_egale_enonce"]
