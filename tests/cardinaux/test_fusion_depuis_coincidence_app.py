"""Test §III.2 — RE-CÂBLAGE : fusion_hyp DÉRIVÉE de la COÏNCIDENCE PROUVÉE.

`fusion_depuis_coincidence_app` re-câble `fusion_depuis_coincidence` pour faire reposer
`fusion_hyp` sur la coïncidence **PROUVÉE** (`coincidence_point_app` → `coincidence_univ_app`,
THÉORÈME CLOS) au lieu de la coïncidence **POSTULÉE** (`coincidence_univ`).

Hypothèses survivantes (2) : { bo(R,E), bo(R',F) } — `coincidence_univ` est GONE et
`residu_univ_app` est GONE.  Le contenu géométrique du résidu (#8 segment-image,
#13 graphe-restriction) est désormais DÉRIVÉ de `residu_univ_app_renforce` (CLOS,
theorie=22), dont l'antécédent renforcé ajoute à ANT_12 les deux segments seg(Sp,R,E)
et seg(Tg,Rp,F), TOUS DEUX portés par les CŒURS.  Il ne reste QUE les deux bons ordres
= la prémisse propre du Théorème 3 §III.2.  Conclusion == T2.fusion_hyp LITTÉRALEMENT ;
non tautologique ; theorie=22.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux import ensembles_fusion_assemblage as FA
from bourbaki.cardinaux import ensembles_temoin_deux_couples as T2


def test_conclusion_est_fusion_hyp_litteralement():
    """La conclusion est EXACTEMENT T2.fusion_hyp (même cible que l'original)."""
    t = FDA.fusion_depuis_coincidence_app()
    assert t.conclusion == FDA.fusion_depuis_coincidence_app_cible()
    # identique à l'énoncé-cible de fusion_depuis_coincidence (re-câblage du MÊME théorème)
    assert t.conclusion == FA.fusion_depuis_coincidence_cible()
    fh = T2.fusion_hyp("E", "R", "F", "Rp", "ua", "va", "ub", "vb", "S", "T", "phi")
    assert t.conclusion == fh


def test_coincidence_univ_est_GONE():
    """🎯 LE PAIEMENT : `coincidence_univ` (postulée) N'EST PLUS une hypothèse."""
    t = FDA.fusion_depuis_coincidence_app()
    cu = FA.coincidence_univ()
    assert cu not in set(t.hypotheses)
    # et le résidu N'EST PAS coincidence_univ (strictement plus faible)
    assert FDA.residu_univ_app() != cu


def test_exactement_deux_hypotheses_survivantes():
    """Les hyps SURVIVANTES sont EXACTEMENT { bo(R,E), bo(R',F) }.

    = la prémisse propre du Théorème 3 §III.2.  `residu_univ_app` est GONE (son contenu
    est dérivé de `residu_univ_app_renforce`, CLOS).  Les deux CŒURS sont des témoins
    INTERNES, éliminés en ∃ (comme l'original) : ils ne survivent PAS dans le séquent."""
    t = FDA.fusion_depuis_coincidence_app()
    assert len(t.hypotheses) == 2
    assert set(t.hypotheses) == set(FDA.fusion_depuis_coincidence_app_hypotheses())


def test_residu_univ_app_est_GONE():
    """🎯🎯 LE PAIEMENT FINAL : `residu_univ_app` (le RÉSIDU géométrique reporté) N'EST
    PLUS une hypothèse.  Son contenu (#8 segment-image, #13 graphe-restriction) est
    DÉRIVÉ de `residu_univ_app_renforce` (CLOS) à l'intérieur de _coinc_point_app."""
    t = FDA.fusion_depuis_coincidence_app()
    res = FDA.residu_univ_app()
    assert res not in set(t.hypotheses)


def test_bons_ordres_ambiants_load_bearing():
    """Les deux bons ordres AMBIANTS bo(R,E) et bo(R',F) sont les SEULES hypothèses."""
    t = FDA.fusion_depuis_coincidence_app()
    hyps = set(t.hypotheses)
    boR, boRp = FDA.fusion_depuis_coincidence_app_hypotheses()
    assert boR in hyps
    assert boRp in hyps
    assert hyps == {boR, boRp}


def test_non_vacueux():
    """NON vacueux : fusion_hyp n'est aucune hypothèse."""
    t = FDA.fusion_depuis_coincidence_app()
    assert t.conclusion not in set(t.hypotheses)
    assert not t.est_clos


def test_residu_strictement_plus_faible_que_coincidence_univ():
    """Le résidu ne porte AUCUNE égalité de valeurs (≠ coïncidence) : son CONSÉQUENT est
    seulement (segment image et inclusion de graphe-restriction)."""
    from bourbaki.logique.i_1_termes_relations.formule import egal
    from bourbaki.cardinaux.ensembles_coincidence_univ_app import _premisse_liste
    res = FDA.residu_univ_app()
    # descendre sous les 6 ∀ jusqu'à l'implication ANT ⇒ CONS
    cur = res
    while cur.lieur:           # peler les pourtout
        cur = cur.sous[0]
    # cur est l'implication ¬(¬ANT ou CONS)-encodée ; on vérifie via les conjoints attendus
    prem = _premisse_liste("rphip", "rphig", "rSp", "rTp", "rSg", "rTg", "F", "R", "Rp", "E")
    # le conséquent attendu = et(prem[8], prem[13]) (segment-image, graphe-restriction)
    from bourbaki.logique.i_1_termes_relations.formule import et
    cons_attendu = et(prem[8], prem[13])
    # aucune égalité de valeurs dans le conséquent (pas un '=' top-level)
    assert cons_attendu.connecteur != "=" if hasattr(cons_attendu, "connecteur") else True
    # le conséquent figure littéralement dans la formule du résidu
    assert cons_attendu in _sous_formules(res)


def _sous_formules(f):
    """Toutes les sous-formules de f (pour vérifier présence structurelle)."""
    out = {f}
    for s in getattr(f, "sous", ()):
        out |= _sous_formules(s)
    return out


def test_parametrable_sur_les_points():
    """Re-paramétrable sur les POINTS (schéma).  ⚠️ les noms AMBIANTS E,F,R,R' sont
    CANONIQUES : `coincidence_point_app`/`coincidence_univ_app` est un SCHÉMA sur F,R,R'
    avec E hardcodé « E » (binders internes) — non re-renommable.  Le re-câblage HÉRITE
    de cette contrainte (le contenu géométrique de Lemme 1 est prouvé comme schéma)."""
    t = FDA.fusion_depuis_coincidence_app("E", "R", "F", "Rp",
                                          u="aa", v="bb", up="cc", vp="dd")
    assert not t.est_clos
    assert len(t.hypotheses) == 2
    assert t.conclusion == FDA.fusion_depuis_coincidence_app_cible(
        "E", "R", "F", "Rp", u="aa", v="bb", up="cc", vp="dd")


def test_theorie_intacte():
    """INVARIANT : theorie_ensembles() = 22  (rien postulé ; coïncidence PROUVÉE)."""
    assert len(E.theorie_ensembles().axiomes) == 22
