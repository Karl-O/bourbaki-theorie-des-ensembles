"""Tests — §II.4 / §III.3.3 PROP. 10 (binaire) : A∩B=∅ ⇒ Eq(A∪B, A⊔B).

Bijectivité INCONDITIONNELLE (sous A∩B=∅) du recollement canonique W = Δ₀(A)∪Δ₁(B)
de A∪B sur A⊔B — le « dernier mille » jadis laissé à un round dédié, désormais CLOS."""
import pytest

from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe

import bourbaki.cardinaux.ensembles_reunion_somme_bijection as R


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_domaines_disjoints_clos():
    dd = R._domaines_disjoints("At", "Bt")
    assert dd.est_clos and len(dd.hypotheses) == 0


def test_W_fonctionnel_clos():
    wf = R.W_fonctionnel("At", "Bt")
    assert wf.est_clos and len(wf.hypotheses) == 0


def test_W_domaine_clos():
    wd = R.W_domaine("At", "Bt")
    assert wd.est_clos and len(wd.hypotheses) == 0
    assert wd.conclusion == egal(E.dom(R._W("At", "Bt")),
                                 E.reunion(var("At"), var("Bt")))


def test_W_image_clos():
    wi = R.W_image("At", "Bt")
    assert wi.est_clos and len(wi.hypotheses) == 0
    assert wi.conclusion == egal(E.image(R._W("At", "Bt"), E.reunion(var("At"), var("Bt"))),
                                 somme_disjointe(var("At"), var("Bt")))


def test_images_disjointes_clos():
    idj = R._images_disjointes("At", "Bt")
    assert idj.est_clos and len(idj.hypotheses) == 0


def test_W_injective_clos():
    wj = R.W_injective("At", "Bt")
    assert wj.est_clos and len(wj.hypotheses) == 0


def test_W_est_bijection_clos():
    """(A∩B=∅) ⇒ est_bijection_de(W, A∪B, A⊔B)  — CLOS (les 4 conjoints assemblés)."""
    wb = R.W_est_bijection("At", "Bt")
    assert wb.est_clos and len(wb.hypotheses) == 0


def test_eq_reunion_somme_clos():
    """🎯 (A∩B=∅) ⇒ Eq(A∪B, A⊔B)  — Prop. 10 §II.4 binaire, CLOS, 0 hyp."""
    ers = R.eq_reunion_somme("At", "Bt")
    assert ers.est_clos and len(ers.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22
