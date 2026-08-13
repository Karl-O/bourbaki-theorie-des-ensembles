"""Tests — §III.2 coincidence_univ_app_point : réduction à une PRÉMISSE PROPRE.

Vérifie que coincidence_univ_close_isos est ramené à EXACTEMENT la prémisse propre
(isos/func/dom + segments + bons ordres + inclus(S1,S2) + 2 inclusions de graphe),
que la conclusion est la cible, que theorie=22, et que le séquent est non vacueux.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import afficher_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion.ensembles_coincidence_univ_app import (
    coincidence_univ_app,
    coincidence_univ_app_cible,
    coincidence_univ_app_point,
    coincidence_univ_app_point_cible,
    coincidence_univ_app_point_premisse,
    reciproque_inclusion_monotone,
    reciproque_inclus_produit_miroir,
)


def test_theorie_inchangee():
    """La théorie reste à 22 axiomes (rien postulé)."""
    coincidence_univ_app_point()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_conclusion_est_la_cible():
    """La conclusion est (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))."""
    thm = coincidence_univ_app_point()
    assert thm.conclusion == coincidence_univ_app_point_cible()


def test_hypotheses_sont_la_premisse_propre():
    """Les hypothèses du séquent sont EXACTEMENT la prémisse propre (14 formules).

    🔑 BON ORDRE AMBIANT VRAI : les SEULS bons ordres sont ceux des ENSEMBLES AMBIANTS
    bo(R,E) [R-side] + bo(R',F) [F-side] ; TOUS les bons ordres sur des segments propres
    (bo(R,S1), bo(R,S2), bo(R',T1), bo(R',image)) ont disparu (faux sur segment propre).
    inclus(S1,E) est fournie par est_segment(S1,R,E) dans la fusion → prémisse DISCHARGEABLE."""
    thm = coincidence_univ_app_point()
    hyps = set(thm.hypotheses)
    premisse = coincidence_univ_app_point_premisse()
    manquantes = premisse - hyps
    superflues = hyps - premisse
    assert not manquantes, "prémisse non couverte:\n" + "\n".join(
        afficher_f(f)[:160] for f in manquantes)
    assert not superflues, "hypothèses brutes résiduelles (non déchargées):\n" + "\n".join(
        afficher_f(f)[:160] for f in superflues)
    assert hyps == premisse
    assert len(hyps) == 14
    # le bon ordre est AMBIANT VRAI : bo(R,E)+bo(R',F), JAMAIS bo sur un segment (propre)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, inclus
    Rf = lambda a, b: appartient(E.couple(a, b), var("R"))
    Rpf = lambda a, b: appartient(E.couple(a, b), var("Rp"))
    img = E.image(var("phi2"), var("S1"))
    assert E.est_bien_ordonne(Rf, var("E")) in hyps
    assert E.est_bien_ordonne(Rpf, var("F")) in hyps
    assert inclus(var("S1"), var("E")) in hyps            # fournie par est_segment(S1,R,E)
    assert E.est_bien_ordonne(Rf, var("S2")) not in hyps
    assert E.est_bien_ordonne(Rf, var("S1")) not in hyps
    assert E.est_bien_ordonne(Rpf, var("T1")) not in hyps
    assert E.est_bien_ordonne(Rpf, img) not in hyps


def test_non_vacueux():
    """Le séquent n'est pas vacueux : la conclusion n'est pas l'une de ses hypothèses."""
    thm = coincidence_univ_app_point()
    assert thm.conclusion not in set(thm.hypotheses)


def test_reciproque_inclusion_monotone_close():
    """La monotonie de la réciproque est CLOSE (0 hypothèse)."""
    m = reciproque_inclusion_monotone("G", "H")
    assert len(m.hypotheses) == 0


def test_reciproque_inclus_produit_miroir():
    """reciproque(G) ⊂ B×A sous la seule hyp forward G ⊂ A×B."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, inclus
    p = reciproque_inclus_produit_miroir(var("G"), var("A"), var("B"))
    assert p.conclusion == inclus(E.reciproque(var("G")), E.produit(var("B"), var("A")))
    assert set(p.hypotheses) == {inclus(var("G"), E.produit(var("A"), var("B")))}


def test_coincidence_univ_app_FORMULE_close():
    """🎯🎯🎯 La FORMULE coincidence_univ' (renforcée, généralisée sur 6 témoins) est CLOSE."""
    t = coincidence_univ_app()
    assert t.est_clos                                   # THÉORÈME inconditionnel (0 hyp)
    assert t.conclusion == coincidence_univ_app_cible()
    assert len(E.theorie_ensembles().axiomes) == 22
