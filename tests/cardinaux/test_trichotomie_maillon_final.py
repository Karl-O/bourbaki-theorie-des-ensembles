"""Tests §III.2 — MAILLON FINAL de la trichotomie contre la CIBLE SAINE (canon).

Certifie que l'endgame logique tient : à partir des deux isos (h : D≅I, hi : I≅D),
de la maximalité (D=E ou I=F) et des deux segments, on conclut la trichotomie SAINE
(trichotomie_ordinaux_canon, forme anti-capture). 5 hyps structurelles, non tautologique.
"""
from bourbaki.logique.formule import var, egal, ou, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_maillon_final as MF
from bourbaki.ordre import ensembles_iso_ordre_canon as C


def _Rf(g):
    vg = var(g)
    return lambda a, b: appartient(E.couple(a, b), vg)


def test_maillon_final_conclut_cible_saine():
    """{2 isos, (D=E ou I=F), 2 segments} ⊢ trichotomie_ordinaux_canon(E,R,F,Rp)."""
    t = MF.maillon_final()
    assert not t.est_clos
    assert len(t.hypotheses) == 5
    # la conclusion est la cible SAINE (anti-capture), pas la forme défaut défectueuse
    assert t.conclusion == MF.maillon_final_cible()
    assert t.conclusion == C.trichotomie_ordinaux_canon("E", _Rf("R"), "F", _Rf("Rp"))
    assert t.conclusion not in t.hypotheses


def test_les_5_hypotheses_sont_structurelles():
    """Les hypothèses sont : iso(h,D,I), iso(hi,I,D), (D=E ou I=F), seg(D), seg(I)."""
    t = MF.maillon_final()
    Rf, Rpf = _Rf("R"), _Rf("Rp")
    iso_h = C.est_isomorphisme_ordre_canon(var("h"), var("D"), var("I"), Rf, Rpf)
    iso_hi = C.est_isomorphisme_ordre_canon(var("hi"), var("I"), var("D"), Rpf, Rf)
    disj = ou(egal(var("D"), var("E")), egal(var("I"), var("F")))
    seg_D = E.est_segment(var("D"), Rf, var("E"), C.ISO_X, C.ISO_Y)
    seg_I = E.est_segment(var("I"), Rpf, var("F"), C.ISO_X, C.ISO_Y)
    for h in (iso_h, iso_hi, disj, seg_D, seg_I):
        assert h in t.hypotheses


def test_maillon_final_h_chaine_les_pieces_commitees():
    """maillon_final_h : la cible SAINE est dérivée de l'iso maximal h, avec les 2
    hypothèses d'iso DÉCHARGÉES via h_est_isomorphisme_ordre_sous_hyp + reciproque
    (keystone).  Il reste les hypothèses PLUS PROFONDES (cohérences/témoins, surjectivité,
    func, dom, maximalité, segments) — le vrai gap restant."""
    t = MF.maillon_final_h()
    assert not t.est_clos
    # conclusion = la cible SAINE (anti-capture)
    assert t.conclusion == MF.maillon_final_cible()
    assert t.conclusion not in t.hypotheses
    # les 2 hypothèses d'iso (h, h⁻¹) ne sont PLUS là (déchargées sur les pièces commitées)
    import bourbaki.cardinaux.ensembles_trichotomie_scaffold as TS
    from bourbaki.cardinaux.ensembles_trichotomie_maillon_final import _R_de
    from bourbaki.ordre import ensembles_iso_ordre_canon as C
    h = TS.h_iso_max("E", "R", "F", "Rp")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    iso_h = C.est_isomorphisme_ordre_canon(h, E.dom(h), E.img(h), Rf, Rpf)
    assert iso_h not in t.hypotheses          # déchargée (n'est plus une hypothèse)


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
