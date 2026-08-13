"""Tests §III.3 Prop 10 Cor 2 : (∏a_ι)^b = ∏ a_ι^b (forme ensembliste + réduction)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl, egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop10_currying.ensembles_prop10cor2_iii3 import (
    membre_source, membre_but, source, but,
    eq_source_son_cardinal, eq_but_son_cardinal,
    cor2_via_eq,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_source_clos():
    th = membre_source()
    assert th.est_clos


def test_membre_but_clos_et_exact():
    """CLOS **et** conclusion EXACTE — le garde-fou contre la DÉRIVE SILENCIEUSE.

    Ce test n'assertait que `est_clos` jusqu'au 26 juil. 2026 : la réparation de
    `AXIOME_PRODUIT_FAM` (conjoint de tête « F ⊂ I × ⋃X_ι » rétabli) a changé la
    conclusion de `membre_but` sans rien casser, et rien ne l'aurait signalé.  La
    cible est donc RECONSTRUITE ICI, à la main, hors du module testé."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, impl as _impl, appartient, inclus, pourtout, equiv)
    th = membre_but()
    assert th.est_clos
    vfamF, vI, vF, vi = var("famF"), var("I"), var("F"), var("i")
    corps = et(et(et(inclus(vF, E.produit(vI, E.reunion_famille(vfamF, vI))),
                     E.est_fonctionnel(vF)),
                  egal(E.dom(vF), vI)),
               pourtout("i", _impl(appartient(vi, vI),
                                   appartient(E.valeur(vF, vi),
                                              E.valeur_famille(vfamF, vi)))))
    assert th.conclusion == equiv(appartient(vF, E.produit_famille(vfamF, vI)), corps)


def test_eq_source_son_cardinal_clos():
    assert eq_source_son_cardinal().est_clos


def test_eq_but_son_cardinal_clos():
    assert eq_but_son_cardinal().est_clos


def test_cor2_via_eq_clos_et_exact():
    """Eq(source,but) ⇒ Card(source)=Card(but) : CLOS, 0 hyp, conclusion EXACTE."""
    th = cor2_via_eq()
    assert th.est_clos
    src, tgt = source(), but()
    cible = impl(equipotent(src, tgt), egal(cardinal(src), cardinal(tgt)))
    assert th.conclusion == cible
