"""Tests — SIMPLIFICATION ADDITIVE FINIE (Cor. 3 §III.5) + unicité de la soustraction.

  • simplification_additive_finie : est_entier(a) ⇒ (∀c)(∀c')((card c et card c'
    et a+c=a+c') ⇒ c=c').  CLOS, 0 hyp, theorie=22.
  • soustraction_unicite_close : (est_entier a et card c et card c' et a+c=b et
    a+c'=b) ⇒ c=c'.  CLOS, 0 hyp (résidu de simplifiabilité DÉCHARGÉ).

⚠️ Chaque preuve invoque la récurrence C61 sur a (τ-cardinaux imbriqués) ~5-6 min.
"""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_simplification_additive import (
    simplification_additive_finie, simplification_additive_finie_enonce,
    soustraction_unicite_close, soustraction_unicite_close_enonce,
)
from bourbaki.ensembles import ensembles_abrege as E


def test_simplification_additive_finie_close():
    r = simplification_additive_finie()
    assert r.est_clos and not r.hypotheses
    assert r.conclusion == simplification_additive_finie_enonce()


def test_soustraction_unicite_close():
    r = soustraction_unicite_close()
    assert r.est_clos and not r.hypotheses
    assert r.conclusion == soustraction_unicite_close_enonce()


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
