"""Tests — sous-lemme de Tukey prouvé par récurrence finie (§III.4-5)."""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ensembles_finis.ensembles_tukey_sous_lemme import sous_lemme_preuve
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ensembles_finis.ensembles_tukey_iii4 import (
    sous_lemme_partie_finie_dans_membre, Incl,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, existe, appartient


def test_sous_lemme_conclusion_et_hyps():
    r = sous_lemme_preuve()
    # conclusion = EXACTEMENT le résidu déposé dans Tukey
    assert r.conclusion == sous_lemme_partie_finie_dans_membre("S", "T", "Y", "Mtk")
    # 2 hypothèses HONNÊTES (non vacueuses) : 𝔗 chaîne + 𝔗 non vide
    assert len(r.hypotheses) == 2
    assert totalement_ordonne(Incl(var("S")), var("T")) in r.hypotheses
    assert existe("M0tk", appartient(var("M0tk"), var("T"))) in r.hypotheses
    # anti-vacuité : la conclusion n'est PAS dans les hypothèses
    assert r.conclusion not in r.hypotheses


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_tukey_complet_clos():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ensembles_finis.ensembles_tukey_sous_lemme import (
        Tukey_theoreme_complet, chaines_non_vides,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ensembles_finis.ensembles_tukey_iii4 import Incl
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import de_caractere_fini
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import enonce_non_vide
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import element_maximal
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, existe
    r = Tukey_theoreme_complet()
    assert r.est_clos and len(r.hypotheses) == 0
    cf = de_caractere_fini(var("S"), var("E"))
    nv = enonce_non_vide(var("S"), "x")
    cnv = chaines_non_vides("S", "Tchain", "x", "y", "z", "M0tk")
    target = impl(et(et(cf, nv), cnv),
                  existe("m", element_maximal(Incl(var("S")), var("S"), var("m"), "x")))
    assert r.conclusion == target
