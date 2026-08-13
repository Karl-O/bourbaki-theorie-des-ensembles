"""Un diviseur est majoré par son dividende — le lemme qui débloque la primalité.

Ce lemme n'existait pas au dépôt. Il ferme le domaine du (∀d) de la primalité :
sans lui, il faut traiter TOUS les d et rien ne les borne.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_diviseur_majore import (
    cible, diviseur_majore, diviseur_majore_brut, diviseur_majore_quantifie,
    instance_un,
)


def test_le_lemme_est_clos_et_egale_sa_cible():
    """👑 ⊢ (Fini(d) et ¬(p=0) et d|p) ⇒ d ≤ p, sans hypothèse résiduelle."""
    th = diviseur_majore()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_les_trois_hypotheses_sont_toutes_porteuses():
    """Les hypothèses sont MESURÉES, pas déclarées : `assume` ne les fait entrer
    dans le séquent que si elles ont servi. En trouver exactement trois prouve
    qu'aucune n'est décorative.

    ⚠️ Mesuré au passage : `est_fini(p)` — que l'énoncé visé réclamait — ne porte
    PAS. Le lemme est donc strictement plus fort que la cible initiale."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, non,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, ZERO,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        divise_propre,
    )
    brut = diviseur_majore_brut()
    assert len(brut.hypotheses) == 3
    vd, vp = var("ddm"), var("pdm")
    assert est_fini(vd) in brut.hypotheses
    assert non(egal(vp, ZERO)) in brut.hypotheses
    assert divise_propre(vd, vp, q="qdiv") in brut.hypotheses
    assert est_fini(vp) not in brut.hypotheses, \
        "est_fini(p) ne doit PAS porter : le lemme est plus fort que la cible visée"


def test_la_forme_quantifiee_s_emboite_dans_la_primalite():
    """La forme ¬(p=0) ⇒ (∀d)((Fini d et d|p) ⇒ d ≤ p) est close, et son
    antécédent interne est LITTÉRALEMENT celui du (∀d) de `est_premier`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        divise_propre,
    )
    from outils_ia.conjectures.goldbach import est_premier, deux
    q = diviseur_majore_quantifie()
    assert q.est_clos and len(q.hypotheses) == 0

    vd = var("ddm")
    ante = et(est_fini(vd), divise_propre(vd, deux(), q="qdiv"))

    def _contient(f, c):
        return f == c or any(_contient(s, c) for s in getattr(f, "sous", ()))

    assert _contient(est_premier(deux(), d="ddm", q="qdiv"), ante), \
        "l'antécédent du lemme doit apparaître tel quel dans est_premier"


def test_anti_vacuite_l_antecedent_est_atteignable():
    """🔴 Une implication close dont l'antécédent serait contradictoire ne vaudrait
    rien. On PROUVE l'antécédent en d = p = 1 et on dérive 1 ≤ 1 à travers le lemme."""
    inst, ante, concl = instance_un()
    assert ante.est_clos, "l'antécédent doit être prouvé, pas supposé"
    assert concl.est_clos and len(concl.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22
