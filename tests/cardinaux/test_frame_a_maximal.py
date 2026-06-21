"""Tests — §III.6.3 (Hessenberg, Zorn E.III.48) : assemblage vers l'existence d'un
élément maximal du poset 𝔉(E) des couples-bijections.

  • est_infini_union_chaine : ⋃S(C) infinie (sur-ensemble d'un infini)  — 2 hyps honnêtes.
  • frame_inductif_clean    : est_inductif(Γ𝔉,𝔉) sous l'unique résidu m_dans_frame.
  • frame_a_maximal         : (∃m)element_maximal(Γ𝔉,𝔉,m) sous {𝔉≠∅, m_dans_frame}.

theorie_ensembles() reste = 22 ; noyau INTACT ; aucune conclusion vacuous.
"""
from bourbaki.logique.formule import var, appartient, existe
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.cardinaux.ensembles_chaine_temoin_abstrait import union_premiere
from bourbaki.cardinaux.ensembles_frame_inductif_assemblage import m_dans_frame_universel
from bourbaki.ordre.ensembles_zorn import est_inductif, enonce_non_vide
from bourbaki.ordre.ensembles_ordre_relation import element_maximal, est_ordre
from bourbaki.cardinaux.ensembles_frame_a_maximal import (
    est_infini_union_chaine, frame_inductif_clean, frame_a_maximal,
)


def _theorie_22():
    from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
    return len(theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert _theorie_22()


def test_est_infini_union_chaine():
    r = est_infini_union_chaine("E", "Cch", "pmemb")
    vp, vC = var("pmemb"), var("Cch")
    assert r.conclusion == est_infini_ensemble(union_premiere(vC))
    # 2 hyps honnêtes : p∈C, p∈𝔉(E)
    assert appartient(vp, vC) in r.hypotheses
    assert appartient(vp, frame_pair(var("E"))) in r.hypotheses
    assert r.conclusion not in r.hypotheses     # non vacuous
    assert _theorie_22()


def test_frame_inductif_clean():
    r = frame_inductif_clean()
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert r.conclusion == est_inductif(Gam, Fr, "C", "m", "xmaj", "y", "z")
    # est_ordre DÉCHARGÉ : il ne reste que le résidu m_dans_frame_universel
    assert est_ordre(Gam, Fr) not in r.hypotheses
    assert m_dans_frame_universel("E", "C") in r.hypotheses
    assert len(list(r.hypotheses)) == 1
    assert r.conclusion not in r.hypotheses
    assert _theorie_22()


def test_frame_a_maximal():
    r = frame_a_maximal("E")
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert r.conclusion == existe("m", element_maximal(Gam, Fr, var("m"), "x"))
    # résidus honnêtes : 𝔉≠∅ et m_dans_frame_universel
    assert enonce_non_vide(Fr, "x") in r.hypotheses
    assert m_dans_frame_universel("E", "C") in r.hypotheses
    assert r.conclusion not in r.hypotheses     # non vacuous
    assert _theorie_22()
