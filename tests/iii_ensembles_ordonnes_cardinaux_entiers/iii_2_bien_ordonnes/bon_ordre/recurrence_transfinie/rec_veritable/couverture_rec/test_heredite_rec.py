# -*- coding: utf-8 -*-
"""Tests R5'-final (briques ambiantes) — graphe, réunion, extension dans 𝔓(E×V)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    membre_ambiant_graphe, union_rec_ambiante, extension_ambiante,
    regle_dans_V, heredite_rec,
)

_G, _E, _X = var("Gsr"), var("Esr"), var("xsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_membre_ambiant_graphe():
    """{p∈𝔓(E×V)} ⊢ est_un_graphe(p)."""
    t = membre_ambiant_graphe()
    assert t.conclusion == E.est_un_graphe(var("pha"))
    assert list(t.hypotheses) == [appartient(var("pha"), ambiant("Esr"))]
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_rec_ambiante():
    """⊢ ⋃Dfam_rec(x) ∈ 𝔓(E×V) — clos."""
    t = union_rec_ambiante(_vh)
    U = union_famille(Dfam_rec(_G, _E, _X))
    assert t.conclusion == appartient(U, ambiant("Esr"))
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_ambiante():
    """{p∈𝔓(E×V), x∈E, v∈V} ⊢ p∪{(x,v)} ∈ 𝔓(E×V)."""
    t = extension_ambiante()
    pS = E.reunion(var("pha"), E.singleton(E.couple(_X, var("vha"))))
    assert t.conclusion == appartient(pS, ambiant("Esr"))
    hyps = list(t.hypotheses)
    assert len(hyps) == 3
    assert appartient(var("pha"), ambiant("Esr")) in hyps
    assert appartient(_X, _E) in hyps
    assert appartient(var("vha"), var("Vval")) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22


def test_heredite_rec():
    """🎯 R5'-FINAL : {bo, regle_dans_V} ⊢ heredite_couverture(couvert_amb)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
        _graphe_R,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
        heredite_couverture,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
        couvert_essai_rec_amb,
    )
    t = heredite_rec(_vh)
    couvert = couvert_essai_rec_amb(_vh, "Gsr", "Esr")
    assert t.conclusion == heredite_couverture(couvert, "Gsr", _E, "x0tf", "ytf")
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert regle_dans_V(_vh) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couverture_totale_rec():
    """🎯🎯 R6' : {bo, règle bornée} ⊢ (∀x∈E)(∃p ambiant) est_essai_rec(p, x)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
        _graphe_R,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
        couvert_essai_rec_amb,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
        couverture_totale_rec,
    )
    t = couverture_totale_rec(_vh)
    couvert = couvert_essai_rec_amb(_vh, "Gsr", "Esr")
    vx0 = var("x0tf")
    attendu = pourtout("x0tf", impl(appartient(vx0, _E), couvert(vx0)))
    assert t.conclusion == attendu
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert regle_dans_V(_vh) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
