"""Tests — ponts couple→égalité-d'ensembles (surjectivité/domaine du recollement)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_ponts_couple_valeur_surj import (
    surjectif_couple_riche, domaine_couple,
    couple_surjectif_implique_image_egale, couple_domaine_implique_dom_egale,
)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pont_surjectif_image_egale():
    r = couple_surjectif_implique_image_egale()
    vF, vD, vT = var("Fsr"), var("Dsr"), var("Tsr")
    img = E.image(vF, vD)
    # conclusion = image(F,D) = T  (= est_surjective(F,D,T))
    assert r.conclusion == egal(img, vT)
    assert r.conclusion == E.est_surjective(vF, vD, vT)
    # 2 hyps honnêtes
    assert surjectif_couple_riche(vF, vD, vT) in r.hypotheses
    assert inclus(img, vT) in r.hypotheses
    assert r.conclusion not in r.hypotheses          # non vacuous


def test_pont_domaine_dom_egale():
    r = couple_domaine_implique_dom_egale()
    vF, vD = var("Fdc"), var("Ddc")
    dm = E.dom(vF)
    assert r.conclusion == egal(dm, vD)
    assert domaine_couple(vF, vD) in r.hypotheses
    assert inclus(dm, vD) in r.hypotheses
    assert r.conclusion not in r.hypotheses          # non vacuous
