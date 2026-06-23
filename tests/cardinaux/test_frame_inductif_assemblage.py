"""Tests — assemblage final de l'inductivité du poset 𝔉 (Hessenberg/Zorn, E.III.48).

`enonce_chaine_majoree_preuve` décharge `enonce_chaine_majoree` de `frame_inductif`
sous l'UNIQUE résidu honnête `(∀C) (⋃S(C),⋃φ(C))∈𝔉(E)` (frame-membership du
recollement).  `frame_inductif_inconditionnel` ⊢ est_inductif(Γ𝔉,𝔉) sous ce résidu
+ est_ordre(Γ𝔉,𝔉).  theorie_ensembles() reste = 22.
"""
from bourbaki.cardinaux import ensembles_frame_inductif_assemblage as M
from bourbaki.cardinaux.ensembles_hessenberg_inductivite import enonce_chaine_majoree
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre
from bourbaki.logique.formule import var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def _GamFr():
    vE = var("E")
    return frame_ordre(vE), frame_pair(vE)


def test_enonce_chaine_majoree_preuve():
    Gam, Fr = _GamFr()
    r = M.enonce_chaine_majoree_preuve("E")
    # conclusion EXACTE = enonce_chaine_majoree(Γ𝔉,𝔉)
    assert r.conclusion == enonce_chaine_majoree(Gam, Fr, "C", "m", "xmaj", "y", "z")
    # UNIQUE hypothèse honnête, close en C, non vacuous
    assert len(r.hypotheses) == 1
    assert list(r.hypotheses)[0] == M.m_dans_frame_universel("E", "C")
    assert r.conclusion not in r.hypotheses


def test_frame_inductif_inconditionnel():
    Gam, Fr = _GamFr()
    f = M.frame_inductif_inconditionnel("E")
    assert f.conclusion == est_inductif(Gam, Fr, "C", "m", "xmaj", "y", "z")
    # EXACTEMENT deux hyps honnêtes : le résidu + l'ordre de 𝔉
    attendu = {M.m_dans_frame_universel("E", "C"),
               est_ordre(Gam, Fr, "xmaj", "y", "z")}
    assert set(f.hypotheses) == attendu
    assert f.conclusion not in f.hypotheses


def test_theorie_inchangee():
    M.enonce_chaine_majoree_preuve("E")
    M.frame_inductif_inconditionnel("E")
    assert len(E.theorie_ensembles().axiomes) == 22
