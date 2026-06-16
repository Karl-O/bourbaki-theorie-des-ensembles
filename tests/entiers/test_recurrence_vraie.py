"""Tests — §III.4/§III.6.1 RÉCURRENCE VRAIE : clôture CORRECTE de ℕ sous le SEUL
résidu honnête `predecesseur_fini_universel` (report #2 FAUX éliminé)."""
import pytest

from bourbaki.logique.formule import var, et, impl, non, pourtout, existe
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
from bourbaki.entiers.ensembles_entiers import est_fini, ZERO, successeur
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.entiers.ensembles_recurrence_vraie import (
    preuve_P0_vrai, preuve_step_vrai, recurrence_fini_implique_P_vrai,
    fini_downward_garde_thm, cardinal_infini_existe_card, N_collectivise_vrai,
    _Pp, _fini_implique_P,
)
from bourbaki.entiers.ensembles_principe_recurrence_preuve import predecesseur_fini_universel
from bourbaki.entiers.ensembles_N_collectivise import fini_downward, _coll_fini


def _Pp_pred(b="b"):
    return lambda t: _Pp(t, b)


# ────────────────────────────────────────────────────────────────────────────
#  theorie inchangée = 22
# ────────────────────────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  BASE P'[0]  (INCONDITIONNEL, CLOS)
# ────────────────────────────────────────────────────────────────────────────
def test_P0_vrai_clos():
    p0 = preuve_P0_vrai("b")
    assert p0.est_clos
    assert p0.conclusion == _Pp(ZERO, "b")


# ────────────────────────────────────────────────────────────────────────────
#  PAS  (Fini c et P'[c]) ⇒ P'[c+1]  (CLOS)
# ────────────────────────────────────────────────────────────────────────────
def test_step_vrai_clos():
    step = preuve_step_vrai("c", "b")
    assert step.est_clos
    vc = var("c")
    expected = pourtout("c", impl(et(est_fini(vc), _Pp(vc, "b")), _Pp(successeur(vc), "b")))
    assert step.conclusion == expected


# ────────────────────────────────────────────────────────────────────────────
#  RÉCURRENCE  (∀c)(Fini c ⇒ P'[c])  sous le SEUL résidu pfu
# ────────────────────────────────────────────────────────────────────────────
def test_recurrence_residual_pfu():
    rec = recurrence_fini_implique_P_vrai("c", "b")
    assert rec.conclusion == _fini_implique_P(_Pp_pred("b"), "c")
    pfu = predecesseur_fini_universel()
    assert len(rec.hypotheses) == 1
    assert all(h == pfu for h in rec.hypotheses)
    assert not rec.est_clos


# ────────────────────────────────────────────────────────────────────────────
#  (∃a)(est_cardinal(a) et ¬Fini a)  de A4  (CLOS)
# ────────────────────────────────────────────────────────────────────────────
def test_cardinal_infini_existe_card_clos():
    t = cardinal_infini_existe_card("a", "X")
    assert t.est_clos
    assert t.conclusion == existe("a", et(est_cardinal(var("a")), non(est_fini(var("a")))))


# ────────────────────────────────────────────────────────────────────────────
#  TRANSPORT gardé : (∀x)fini_downward(a,x)  sous {est_cardinal(a), pfu}
# ────────────────────────────────────────────────────────────────────────────
def test_fini_downward_garde_residuals():
    fd = fini_downward_garde_thm("a", "x", "c", "b")
    assert fd.conclusion == pourtout("x", fini_downward(var("a"), var("x")))
    pfu = predecesseur_fini_universel()
    card_a = est_cardinal(var("a"))
    # exactement deux hyps : est_cardinal(a) et pfu
    assert all((h == pfu or h == card_a) for h in fd.hypotheses)
    assert any(h == pfu for h in fd.hypotheses)
    assert any(h == card_a for h in fd.hypotheses)


# ────────────────────────────────────────────────────────────────────────────
#  🎯 ℕ EXISTE : coll(x, Fini x) sous EXACTEMENT {predecesseur_fini_universel}
# ────────────────────────────────────────────────────────────────────────────
def test_N_collectivise_vrai_residual_pfu():
    thm = N_collectivise_vrai("a", "x", "c", "b", "y")
    # conclusion LITTÉRALEMENT coll(x, Fini x)
    assert thm.conclusion == _coll_fini("x")
    # UNIQUE résidu : predecesseur_fini_universel
    pfu = predecesseur_fini_universel()
    assert len(thm.hypotheses) == 1, [repr(h) for h in thm.hypotheses]
    assert all(h == pfu for h in thm.hypotheses)
    assert not thm.est_clos


def test_N_collectivise_vrai_pas_dans_theorie():
    # le théorème ne doit JAMAIS avoir ajouté d'axiome à theorie_ensembles
    N_collectivise_vrai("a", "x", "c", "b", "y")
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  La nouvelle dichotomie gardée est VRAIE (non vacuité / non la forme FAUSSE)
# ────────────────────────────────────────────────────────────────────────────
def test_dichotomie_gardee_pas_nue():
    # cardinal_pas_entre_univ est gardé par est_cardinal(b) : la forme NUE serait FAUSSE.
    from bourbaki.cardinaux.ensembles_cardinal_pas_entre_univ import (
        cardinal_pas_entre_univ, cible_bare_universel, cible_cardinal_pas_entre_univ,
    )
    t = cardinal_pas_entre_univ("b", "c")
    assert t.est_clos
    assert t.conclusion == cible_cardinal_pas_entre_univ("b", "c")
    # la garde est_cardinal(b) DOIT être présente (≠ forme nue)
    assert t.conclusion != cible_bare_universel("b", "c")
