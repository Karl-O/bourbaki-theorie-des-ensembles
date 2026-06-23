"""Tests — Théorème 1 §III.4 (TUKEY–TEICHMÜLLER) via ZORN.

Vérifie : l'ordre d'inclusion Incl sur 𝔖 est un ordre (inconditionnel) et
inductif (sous caractère fini + sous-lemme « partie finie de ⋃(chaîne) ⊂ un
membre »), d'où — par zorn_theoreme — l'existence d'un élément maximal de 𝔖.
theorie_ensembles() reste = 22 (noyau inchangé)."""
from bourbaki.ordre.iii_4_ensembles_finis import ensembles_tukey_iii4 as TK
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif, enonce_non_vide
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre, element_maximal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import de_caractere_fini
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.formule import var, existe


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_incl_est_ordre_clos():
    th = TK.Incl_est_ordre()
    assert th.est_clos
    assert th.conclusion == est_ordre(TK.Incl(var("S")), var("S"), "x", "y", "z")


def test_union_dans_S_trois_hyps():
    th = TK.union_dans_S()
    assert not th.est_clos
    assert len(th.hypotheses) == 3
    vS, vT = var("S"), var("T")
    from bourbaki.logique.formule import inclus
    hyps = list(th.hypotheses)
    assert inclus(vT, vS) in hyps                       # 𝔗⊂𝔖
    assert de_caractere_fini(vS, var("E")) in hyps      # caractère fini
    assert TK.sous_lemme_partie_finie_dans_membre() in hyps  # sous-lemme


def test_incl_est_inductif():
    th = TK.Incl_est_inductif()
    assert th.conclusion == est_inductif(TK.Incl(var("S")), var("S"),
                                         "C", "m", "x", "y", "z")
    # deux hypothèses honnêtes : caractère fini + sous-lemme universel
    assert len(th.hypotheses) == 2


def test_tukey_theoreme_clos():
    th = TK.Tukey_theoreme()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    # conclusion = ( crochet ) ⇒ (∃m) element_maximal(Incl, 𝔖, m)
    GIncl = TK.Incl(var("S"))
    exp_cons = existe("m", element_maximal(GIncl, var("S"), var("m")))
    # le conséquent de l'implication est exactement (∃m) element_maximal
    cons = th.conclusion.sous[1]
    assert cons == exp_cons
    # NON vacueux : le conséquent n'est pas l'antécédent
    assert th.conclusion.sous[1] != th.conclusion.sous[0]
    assert len(E.theorie_ensembles().axiomes) == 22
