# -*- coding: utf-8 -*-
"""Tests — l'organe qui rapproche deux preuves de même squelette.

⚠️ CET ORGANE NE DÉMONTRE RIEN. Aucun `Theoreme` n'en sort, et c'est vérifié
plus bas. Ce qu'on teste, c'est qu'il calcule ce qu'il annonce et qu'il
retrouve une analogie que nous savons vraie — un test qu'on peut perdre, ce
qui en fait un test."""
from __future__ import annotations

from outils_ia.corpus.analogie_preuves import (
    SEUIL_ANALOGIE, distance, forme, graphe_appels, paires_analogues, taille,
    vocabulaire_de_liaison, vocabulaires_opposes,
)

#: la cible de validation : deux preuves qui SONT la même, écrites deux fois
CIBLE = ("symetrie.symetrie_du_crible", "crible_abstrait.symetrie_additive")


def _graphe_jouet():
    """Trois modules. `mp` et `cg` sont partout (liaison), le reste est local."""
    return {
        "m1.preuve_a": ["mp", "cg", "mp", "premiers_bornes", "miroir"],
        "m2.preuve_b": ["mp", "cg", "mp", "elements_bornes", "miroir_additif"],
        "m3.preuve_c": ["mp", "cg", "autre_chose"],
    }


def test_la_liaison_est_decidee_par_la_seule_frequence():
    """Aucune liste blanche écrite à la main : le corpus décide seul.

    C'est ce qui fait que le critère survit à l'extension du corpus — un nom
    qui devient commun à trois sujets devient de la liaison sans qu'on
    touche au code."""
    liaison = vocabulaire_de_liaison(_graphe_jouet(), seuil=3)
    assert liaison == {"mp", "cg"}
    #   le vocabulaire de domaine n'est PAS de la liaison
    assert "premiers_bornes" not in liaison
    assert "miroir_additif" not in liaison


def test_la_forme_efface_le_domaine_et_garde_la_liaison():
    """Le cœur de l'organe tient dans cette ligne, et la voici verrouillée."""
    g = _graphe_jouet()
    liaison = vocabulaire_de_liaison(g, seuil=3)
    fa, fb = forme("m1.preuve_a", g, liaison), forme("m2.preuve_b", g, liaison)
    assert fa == fb, "deux sujets différents, même squelette : formes égales"
    assert fa["mp"] == 2 and fa["cg"] == 1
    assert fa["?"] == 2, "le domaine doit être effacé, pas gardé"
    assert "premiers_bornes" not in fa


def test_la_distance_se_comporte_en_distance():
    """Nulle sur soi-même, symétrique, bornée par 1."""
    g = _graphe_jouet()
    liaison = vocabulaire_de_liaison(g, seuil=3)
    fa = forme("m1.preuve_a", g, liaison)
    fb = forme("m2.preuve_b", g, liaison)
    fc = forme("m3.preuve_c", g, liaison)
    assert distance(fa, fa) == 0.0
    assert distance(fa, fb) == 0.0            # même forme, sujets différents
    assert distance(fa, fc) == distance(fc, fa)
    assert 0.0 <= distance(fa, fc) <= 1.0
    assert taille(fa) == 5


def test_le_copier_colle_intra_module_n_est_pas_une_analogie():
    """Deux jumeaux dans le MÊME module sont une redite, pas un transport.

    Sans cette exclusion le classement se remplit de familles copiées-collées
    (`lemme_alg_8..15`), constaté le 12 août."""
    g = {
        "m1.f": ["mp"] * 20,
        "m1.g": ["mp"] * 20,          # jumeau, même module → écarté
        "m2.h": ["mp"] * 20,          # autre module → retenu
    }
    paires = paires_analogues(g, mini=20)
    couples = {frozenset((a, b)) for (_d, a, b) in paires}
    assert frozenset(("m1.f", "m1.g")) not in couples
    assert frozenset(("m1.f", "m2.h")) in couples


def test_le_plancher_de_taille_ecarte_les_petites_formes():
    """Deux fonctions de trois appels se ressemblent sans que ça signifie rien."""
    g = {"m1.f": ["mp", "cg", "mp"], "m2.g": ["mp", "cg", "mp"]}
    assert paires_analogues(g, mini=20) == []
    assert paires_analogues(g, mini=3) != []


def test_la_cible_de_validation_est_appariee():
    """🎯 `symetrie_du_crible` ≈ `symetrie_additive` — deux fois LA MÊME preuve.

    L'une parle des premiers, l'autre d'un prédicat paramètre. C'est la paire
    que la version du 12 août ratait, et le seul juge de cet organe.

    Ce qu'il a fallu corriger : ce n'était PAS l'égalité qui était trop
    stricte (le plan écrit alors), c'était le DÉPLIAGE des lemmes sur trois
    niveaux — 5 nœuds d'écart à profondeur 1, 104 à profondeur 3."""
    g = graphe_appels()
    assert all(qn in g for qn in CIBLE), "corpus : la cible a bougé de place"
    paires = paires_analogues(g)
    couples = [frozenset((a, b)) for (_d, a, b) in paires]
    assert frozenset(CIBLE) in couples, "la cible de validation n'est pas appariée"
    #   sous le seuil, et dans le haut du classement — pas noyée
    rang = couples.index(frozenset(CIBLE)) + 1
    dist = paires[rang - 1][0]
    assert dist <= SEUIL_ANALOGIE
    assert rang <= 10, "cible au rang %d : le signal s'est dégradé" % rang


def test_les_deux_analogies_sont_emboitees():
    """LE RÉSULTAT INATTENDU, et il faut le garder.

    `demi.rencontre_se_restreint` ≈ `demi_abstrait.restriction_a_la_moitie`
    sort en TÊTE — personne ne l'avait montrée à l'organe. Et son vocabulaire
    de domaine est exactement la cible de validation : la grande analogie
    est BÂTIE SUR la petite. L'organe retrouve donc l'emboîtement, pas
    seulement une ressemblance.

    Si ce test tombe parce que les deux versions ont été unifiées, ce sera
    une bonne nouvelle à réécrire, pas à supprimer."""
    g = graphe_appels()
    liaison = vocabulaire_de_liaison(g)
    haut, bas = "demi.rencontre_se_restreint", "demi_abstrait.restriction_a_la_moitie"
    assert haut in g and bas in g, "corpus : la paire emboîtée a bougé de place"
    va, vb = vocabulaires_opposes(haut, bas, g, liaison)
    assert "symetrie_du_crible" in va
    assert "symetrie_additive" in vb


def test_aucun_theoreme_ne_sort_de_cet_organe():
    """LE TEST DE SÛRETÉ. Une piste n'est pas une preuve.

    Une forme commune ne démontre PAS que deux preuves se transportent l'une
    en l'autre — seul le noyau pourrait le juger. L'organe ne doit donc
    rendre que des noms et des nombres, jamais un objet certifié."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau.noyau import (
        Theoreme,
    )

    paires = paires_analogues(graphe_appels())
    assert paires, "corpus vide : le test ne prouverait rien"
    for (d, a, b) in paires:
        assert isinstance(d, float) and isinstance(a, str) and isinstance(b, str)
        assert not isinstance(d, Theoreme)
