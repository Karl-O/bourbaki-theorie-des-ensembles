# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 équation FIDÈLE, fichier 6 : (∀n∈E) f(n) = T(f|seg(n)),
puis le PAQUET ∃ à la lettre du livre (E III.46).

Règle OPAQUE T(t)=app('Trule',t) ; 4 hyps honnêtes (3 C62 + lecture-restriction).
Le MIROIR de `existence_fonction_restriction_c62` reconstruit ICI, à la main et hors du
module, la conclusion ET les quatre hypothèses, et compare par ÉGALITÉ EXACTE.  Il est
ensuite MUTÉ (pollution / substitution / α-variante, mutants fabriqués en mémoire par
gestes noyau purs) — un mutant survivant voudrait dire que le miroir est décoratif.
theorie==22."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, var, egal, et, impl, appartient, existe, pourtout, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import (
    essais_restriction, equation_restriction_fonction, existence_fonction_restriction_c62,
)

_T = lambda t: app("Trule", t)
_E, _G, _V, _FB, _ZN = "Enat", "Gle", "Uval", "fglb", "zfgl"


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equation_restriction():
    """🎯🎯 {bo, ebf, rc, essais_restriction} ⊢ (∀n∈E)(f(n)=T(f|seg(n)))."""
    th = equation_restriction_fonction(_T, _T)
    assert essais_restriction(_T, _T) in th.hypotheses
    assert len(th.hypotheses) == 4
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  MIROIR du paquet ∃ « à la lettre » — E III.46 C62, moitié EXISTENCE.
# ════════════════════════════════════════════════════════════════════════════
def _cible_a_la_main():
    """(∃f)( func ∧ graphe ∧ dom=E ∧ (∀n∈E)( f(n)=T(f|seg n) ) ) — RE-ÉCRIT ICI.

    On n'appelle PAS `c62_livre_cible` : comparer le module à son propre énoncé ne
    prouverait rien.  Association de `et` : (((func ∧ graphe) ∧ dom) ∧ équation)."""
    ve, vf, vz = var(_E), var(_FB), var(_ZN)
    seg = E.segment_extremite(var(_G), ve, vz)
    corps = et(et(et(E.est_fonctionnel(vf), E.est_un_graphe(vf)), egal(E.dom(vf), ve)),
               pourtout(_ZN, impl(appartient(vz, ve),
                                  egal(E.valeur(vf, vz), _T(E.restriction(vf, seg))))))
    return existe(_FB, corps)


def _hypotheses_a_la_main():
    """Les QUATRE hypothèses attendues, épelées une par une."""
    return frozenset({
        E.est_bien_ordonne(_graphe_R(_G), var(_E)),
        essais_bien_formes(_T, _E, _G, _V, "qwf", "wwf", "zess"),
        rule_codomain(_T, _V, "zess"),
        essais_restriction(_T, _T, _E, _G),
    })


def _miroir(th):
    assert th.conclusion == _cible_a_la_main(), "MIROIR-CONCLUSION"
    assert frozenset(th.hypotheses) == _hypotheses_a_la_main(), "MIROIR-HYPOTHESES"
    assert th.conclusion not in th.hypotheses, "MIROIR-VACUOUS"


def _bien_forme(th, nom):
    assert hasattr(th, "conclusion") and hasattr(th, "hypotheses"), \
        "%s : mutant CASSÉ (pas un Theoreme)" % nom
    assert th.conclusion is not None, "%s : mutant CASSÉ (conclusion nulle)" % nom
    return th


def test_miroir_existence_fonction_restriction_c62():
    """🎯🎯🎯 { bo, ebf, rc, essais_restriction } ⊢ (∃f)( … f(n)=T(f|seg n) ) — E III.46."""
    th = existence_fonction_restriction_c62(_T, _T, _E, _G, _V, _FB, _ZN)
    _miroir(th)
    assert len(th.hypotheses) == 4
    assert th.conclusion.tag == "exists" and th.conclusion.lieur == _FB
    assert len(E.theorie_ensembles().axiomes) == 22


def test_mutant_pollution_est_tue():
    """POLLUTION : même conclusion, hypothèse parasite empilée (gestes noyau purs)."""
    th = existence_fonction_restriction_c62(_T, _T, _E, _G, _V, _FB, _ZN)
    parasite = appartient(var("pollutionC62"), var(_E))
    mut = _bien_forme(N.modus_ponens(N.assume(parasite),
                                     N.loi_deduction(parasite, th)), "pollution")
    assert mut.conclusion == th.conclusion and len(mut.hypotheses) == 5
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-HYPOTHESES" in str(exc.value)


def test_mutant_substitution_conclusion_affaiblie_est_tue():
    """SUBSTITUTION : ∃ ré-introduit sur un témoin AUTRE (une variable nue).

    Hypothèses INCHANGÉES, compte INCHANGÉ : seule la comparaison exacte de la
    conclusion voit que le témoin quantifié n'est plus celui du livre."""
    th = existence_fonction_restriction_c62(_T, _T, _E, _G, _V, _FB, _ZN)
    # (∃f)(P(f)) ⇒ (∃w)((∃f)(P(f)))  : un ∃ PARASITE en tête, même force logique
    faible = existe("wbidon", th.conclusion)
    mut = _bien_forme(N.modus_ponens(th, N.s5(th.conclusion, var("qq"), "wbidon")),
                      "substitution")
    assert mut.conclusion == faible
    assert frozenset(mut.hypotheses) == frozenset(th.hypotheses)   # indiscernable côté hyps
    assert len(mut.hypotheses) == 4
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-CONCLUSION" in str(exc.value)


def test_mutant_alpha_variant_est_tue():
    """ALPHA-VARIANT : `essais_restriction` échangée contre sa α-variante.

    Même conclusion, même NOMBRE d'hypothèses, même force logique — seul le nom des
    liants ∀q,∀w change.  Le noyau n'identifie pas les α-variants."""
    th = existence_fonction_restriction_c62(_T, _T, _E, _G, _V, _FB, _ZN)
    hyp = essais_restriction(_T, _T, _E, _G)
    hyp_a = essais_restriction(_T, _T, _E, _G, "qrsALPHA", "wrsALPHA")
    assert hyp != hyp_a and alpha_egal(hyp, hyp_a), "α-variante mal construite"
    pont = alpha_bridge(N.assume(hyp_a), hyp)                      # {hyp_a} ⊢ hyp
    mut = _bien_forme(N.modus_ponens(pont, N.loi_deduction(hyp, th)), "alpha")
    assert mut.conclusion == th.conclusion and len(mut.hypotheses) == 4
    assert hyp_a in mut.hypotheses and hyp not in mut.hypotheses
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-HYPOTHESES" in str(exc.value)
