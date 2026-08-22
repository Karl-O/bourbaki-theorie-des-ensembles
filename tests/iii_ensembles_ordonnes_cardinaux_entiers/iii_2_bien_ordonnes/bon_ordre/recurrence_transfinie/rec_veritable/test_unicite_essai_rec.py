# -*- coding: utf-8 -*-
"""Tests R2'b — unicité au point : p(z)=q(z) sous l'HR transfinie (5 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_restrictions_egales import (
    hypothese_recurrence,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_unicite_essai_rec import (
    unicite_au_point, couverture_unicite,
)

_P, _Q = var("pre"), var("qre")
_G, _E, _X, _Z = var("Gsr"), var("Esr"), var("xsr"), var("zsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_unicite_au_point():
    """{bo, essai p, essai q, z∈dom_essai(x), HR} ⊢ p(z)=q(z) — 5 hyps exactes."""
    t = unicite_au_point(_vh)
    assert t.conclusion == egal(E.valeur(_P, _Z), E.valeur(_Q, _Z))
    hyps = list(t.hypotheses)
    assert len(hyps) == 5
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert est_essai_rec(_P, _vh, _G, _E, _X) in hyps
    assert est_essai_rec(_Q, _vh, _G, _E, _X) in hyps
    assert appartient(_Z, dom_essai(_G, _E, _X)) in hyps
    assert hypothese_recurrence(_P, _Q, _G, _E, _Z) in hyps
    assert t.conclusion not in hyps
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couverture_unicite():
    """{bo, essai p, essai q} ⊢ (∀x0tf)(x0tf∈E ⇒ (x0tf∈dom_essai(x) ⇒ p=q))."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        impl, pourtout,
    )
    t = couverture_unicite(_vh)
    vy = var("x0tf")
    domx = dom_essai(_G, _E, _X)
    attendu = pourtout("x0tf", impl(appartient(vy, _E),
        impl(appartient(vy, domx),
             egal(E.valeur(_P, vy), E.valeur(_Q, vy)))))
    assert t.conclusion == attendu
    hyps = list(t.hypotheses)
    assert len(hyps) == 3
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert est_essai_rec(_P, _vh, _G, _E, _X) in hyps
    assert est_essai_rec(_Q, _vh, _G, _E, _X) in hyps
    assert t.conclusion not in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
