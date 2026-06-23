"""Tests MIROIR — ensembles_ordre_induit_sousensemble : TRANSPORT du BON ORDRE à un
sous-ensemble par l'ORDRE INDUIT (E.III.2.1).

    { bo(_R_de(Ro),a),  B⊆a }  ⊢  bo( _R_de(graphe_induit(Ro,B)) , B ).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : la conclusion n'est aucune de ses hypothèses.
Hypothèses EXACTES contrôlées (test miroir).
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_ordre_induit_sousensemble as OI


def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bo_induit_B_conclusion():
    t = OI.bo_induit_B()
    assert t.conclusion == OI.bo_induit_B_cible()


def test_bo_induit_B_hypotheses_exactes():
    t = OI.bo_induit_B()
    assert set(t.hypotheses) == OI.bo_induit_B_hypotheses()
    assert len(t.hypotheses) == 2


def test_bo_induit_B_non_vacueux():
    t = OI.bo_induit_B()
    assert t.conclusion not in set(t.hypotheses)


def test_bo_induit_B_theorie_22():
    OI.bo_induit_B()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_graphe_induit_forme():
    # (u,v)∈graphe_induit(Ro,B) ⇔ ((u,v)∈Ro et (u∈B et v∈B)) — instance d'axiome (clos)
    eqv = OI.membre_graphe_induit()
    from bourbaki.logique.i_1_termes_relations.formule import equiv, appartient, et
    from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import _R_de
    Rof = _R_de("Ro")
    u, v, B = E.var("ui"), E.var("vi"), E.var("B")
    cible = equiv(appartient(E.couple(u, v), OI.graphe_induit("Ro", "B")),
                  et(Rof(u, v), et(appartient(u, B), appartient(v, B))))
    assert eqv.conclusion == cible
    assert len(E.theorie_ensembles().axiomes) == 22
