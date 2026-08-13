"""Le pont de cardinalité — ⊢ Card(m⊔m) = Card(Card m ⊔ Card m), terme ARBITRAIRE.

C'est la pièce qui a débloqué Goldbach sur n : le témoin de « n est pair » est un
ensemble QUELCONQUE, et ce pont le remplace par son cardinal, sur lequel les
lemmes d'ordre s'appliquent.  Ces tests protègent la clôture, la généralité (m
n'a PAS besoin d'être un cardinal), et le piège de capture qui a imposé la voie
quantifiée.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, libres_t,
)
from outils_ia.arithmetique.machine_num import NUM
from outils_ia.arithmetique.pont_cardinal import (
    LIANTS_CARD, cible_pont, pont_card, pont_card_quantifie,
)


def test_le_pont_est_clos_pour_un_terme_arbitraire():
    """Numéral, variable libre, terme composé : aucun n'exige d'être un cardinal."""
    for m in (NUM(3), var("m"), E.reunion(E.paire(var("u"), var("u")),
                                          E.paire(var("v"), var("v")))):
        th = pont_card(m)
        assert th.est_clos and not th.hypotheses
        assert th.conclusion == cible_pont(m)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_la_forme_quantifiee_est_close():
    """⊢ (∀m)( Card(m⊔m) = Card(Card m ⊔ Card m) ) — la forme à consommer."""
    th = pont_card_quantifie()
    assert th.est_clos and not th.hypotheses


def test_le_piege_de_capture_est_reel():
    """🔴 Card(·) LIE des lettres ({F, Z, u, …}) : un m qui en porte une serait
    capturé par la construction directe.  C'est pourquoi la cible passe par
    subst_f sur un nom neutre.  Si LIANTS_CARD devenait vide, le garde-fou
    n'aurait plus d'objet — et il faudrait comprendre pourquoi."""
    assert LIANTS_CARD, "Card ne lie plus rien ?"
    nom = sorted(LIANTS_CARD)[0]
    m_piege = var(nom)                       # une variable qui PORTE un nom lié
    th = pont_card(m_piege)                  # la voie quantifiée doit survivre
    assert th.est_clos and th.conclusion == cible_pont(m_piege)
    assert nom in libres_t(m_piege)
