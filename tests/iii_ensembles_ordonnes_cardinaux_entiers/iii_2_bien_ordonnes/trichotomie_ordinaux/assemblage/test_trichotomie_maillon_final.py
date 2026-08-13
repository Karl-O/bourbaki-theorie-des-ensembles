"""Tests §III.2 — MAILLON FINAL de la trichotomie contre la CIBLE SAINE (canon).

Certifie que l'endgame logique tient : à partir des deux isos (h : D≅I, hi : I≅D),
de la maximalité (D=E ou I=F) et des deux segments, on conclut la trichotomie SAINE
(trichotomie_ordinaux_canon, forme anti-capture). 5 hyps structurelles, non tautologique.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, ou, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_maillon_final as MF
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre import ensembles_iso_ordre_canon as C


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
    import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_scaffold as TS
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_maillon_final import _R_de
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre import ensembles_iso_ordre_canon as C
    h = TS.h_iso_max("E", "R", "F", "Rp")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    iso_h = C.est_isomorphisme_ordre_canon(h, E.dom(h), E.img(h), Rf, Rpf)
    assert iso_h not in t.hypotheses          # déchargée (n'est plus une hypothèse)


def test_maillon_final_h_plus_resserre_au_coeur():
    """maillon_final_h_plus : la cible SAINE dérivée de h, avec EN PLUS la surjectivité
    (CLOS) et les égalités réflexives déchargées.  Il ne reste que les 6 hypothèses
    SUBSTANTIELLES — dont le CŒUR DUR (compatibilite_inverse_h, compatibilite_ordre_h
    = Lemme 1 §III.2)."""
    import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_h_iso as HI
    import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_coherences as COH
    t = MF.maillon_final_h_plus()
    assert not t.est_clos
    assert t.conclusion == MF.maillon_final_cible()
    assert t.conclusion not in t.hypotheses
    assert len(t.hypotheses) <= 6                      # resserré (depuis 8)
    # la surjectivité (CLOS) est bien déchargée
    assert COH.surjectivite_h_image().conclusion not in t.hypotheses
    # le cœur dur reste (Lemme 1 §III.2) — honnêtement reporté
    assert HI.compatibilite_inverse_h() in t.hypotheses
    assert HI.compatibilite_ordre_h() in t.hypotheses


def test_maillon_final_h_plus2_reduit_au_lemme1():
    """maillon_final_h_plus2 : les cohérences (compatibilite_inverse_h/ordre_h) sont
    déchargées sur les TÉMOINS COMMUNS (= Lemme 1 §III.2).  La trichotomie (saine) est
    réduite à ses hypothèses IRRÉDUCTIBLES : Lemme 1 + maximalité + segments (+func)."""
    import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_h_iso as HI
    t = MF.maillon_final_h_plus2()
    assert not t.est_clos
    assert t.conclusion == MF.maillon_final_cible()
    assert t.conclusion not in t.hypotheses
    # les cohérences (forme intermédiaire) ne sont plus là : déchargées sur les témoins
    assert HI.compatibilite_inverse_h() not in t.hypotheses
    assert HI.compatibilite_ordre_h() not in t.hypotheses


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
