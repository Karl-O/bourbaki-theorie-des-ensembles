"""Tests §1.11 — caractérisation LEIBNIZIENNE de l'égalité (Résumé E.R.3, n°11).

    ⊢ ( (x=y) ⇔ (∀X)( (x∈X) ⇒ (y∈X) ) )

Honnêteté LCF : le théorème est APPELÉ (un import ne prouve rien) ; conclusion ==
cible (== structurelle, l'équivalence Bourbaki verbatim) ; est_clos == True (0
hypothèse, les deux sens déchargés par C6) ; pas de tautologie déguisée (le sens
⇐ FABRIQUE x=y via le témoin X:={x}, les deux membres diffèrent de la
conclusion) ; theorie_ensembles() = 22 axiomes (aucune théorie dédiée, aucun S8).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, appartient, equiv, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ii_1_algebre_booleenne.ensembles_egalite_leibniz as L

x, y = var("x"), var("y")
X = var("X")


def _cible():
    """Énoncé Bourbaki exact : (x=y) ⇔ (∀X)(x∈X ⇒ y∈X)."""
    return equiv(egal(x, y),
                 pourtout("X", impl(appartient(x, X), appartient(y, X))))


def test_conclusion_est_la_cible():
    t = L.egalite_leibniz_parties()
    assert t.conclusion == _cible()


def test_est_clos_zero_hypothese():
    t = L.egalite_leibniz_parties()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_pas_de_tautologie_deguisee():
    # le contenu est une CARACTÉRISATION (Leibniz) ; les deux membres de
    # l'équivalence diffèrent réellement l'un de l'autre et de la conclusion.
    t = L.egalite_leibniz_parties()
    membre_g = egal(x, y)
    membre_d = pourtout("X", impl(appartient(x, X), appartient(y, X)))
    assert t.conclusion != membre_g
    assert t.conclusion != membre_d
    assert membre_g != membre_d


def test_theorie_inchangee_22():
    L.egalite_leibniz_parties()
    assert len(E.theorie_ensembles().axiomes) == 22
