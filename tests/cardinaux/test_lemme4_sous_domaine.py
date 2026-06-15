"""Tests §III.2 — LEMME 4 généralisé à un SOUS-DOMAINE S ⊆ E.

On certifie : l'axiome définitionnel de A (theorie=22), A=∅ sous les bonnes hypothèses,
lemme_4_sous_domaine à 4 hypothèses STRUCTURELLES (bon ordre AMBIANT bo(R,E) + inclus(S,E)
+ f:S→S + f strictement croissante S→S), conclusion fidèle, non tautologique, et que
JAMAIS bo(R,S) n'apparaît en hypothèse (le tout l'enjeu de la généralisation).
"""
from bourbaki.logique.formule import var, egal, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_lemme4_sous_domaine as L
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de
from bourbaki.ordre.ensembles_ordre_monotone import est_strictement_croissante


def test_axiome_A_membre_clos():
    """u∈A ⇔ (u∈S et f(u)<u) — axiome définitionnel instancié, CLOS."""
    am = L.A_membre()
    assert am.est_clos
    ie = L.A_inclus_S()
    assert ie.est_clos and not ie.hypotheses        # A⊂S inconditionnel


def test_A_inclus_E():
    """A⊂E sous la seule hypothèse inclus(S,E)."""
    ae = L.A_inclus_E()
    assert len(ae.hypotheses) == 1
    assert inclus(var("S"), var("E")) in ae.hypotheses


def test_A_vide():
    """{ bo(R,E), inclus(S,E), f:S→S, f strict crois. S→S } ⊢ A = ∅."""
    av = L.A_vide()
    assert not av.est_clos
    assert len(av.hypotheses) == 4
    A = L.A_bad(var("R"), var("S"), var("f"))
    assert av.conclusion == egal(A, E.VIDE)
    assert av.conclusion not in av.hypotheses


def test_lemme_4_sous_domaine():
    """{ bo(R,E), inclus(S,E), f:S→S, f strict crois. S→S } ⊢ (∀x)(x∈S ⇒ R{x,f(x)})."""
    l4 = L.lemme_4_sous_domaine()
    assert not l4.est_clos
    assert len(l4.hypotheses) == 4
    assert l4.conclusion == L.lemme_4_sous_domaine_cible()
    assert l4.conclusion not in l4.hypotheses
    # les 4 hypothèses STRUCTURELLES : bon ordre AMBIANT bo(R,E), inclus(S,E), f:S→S, f strict crois.
    Rf = _R_de("R")
    bo_E = E.est_bien_ordonne(Rf, var("E"))
    bo_S = E.est_bien_ordonne(Rf, var("S"))
    sincl = inclus(var("S"), var("E"))
    scr = est_strictement_croissante(var("R"), var("R"), var("f"), var("S"), var("S"))
    assert bo_E in l4.hypotheses                      # bon ordre AMBIANT (R,E)
    assert sincl in l4.hypotheses                     # inclus(S,E) réellement requis
    assert scr in l4.hypotheses                       # stricte croissance sur S réellement requise
    assert bo_S not in l4.hypotheses                  # 🎯 JAMAIS bo(R,S) (faux pour S⊊E !)


def test_cor1_sous_domaine():
    """{ bo(R,E), inclus(S,E), a∈S, g:S→S, g strict crois. S→S }
            ⊢ ¬(∀t)(t∈S ⇒ g(t)∈]←,a[ de S)  (Cor 1 §III.2 sous-domaine)."""
    c1 = L.cor1_sous_domaine()
    assert not c1.est_clos
    assert c1.conclusion == L.cor1_sous_domaine_cible()
    assert c1.conclusion not in c1.hypotheses
    Rf = _R_de("R")
    bo_E = E.est_bien_ordonne(Rf, var("E"))
    bo_S = E.est_bien_ordonne(Rf, var("S"))
    assert bo_E in c1.hypotheses                      # bon ordre AMBIANT (R,E)
    assert inclus(var("S"), var("E")) in c1.hypotheses
    assert bo_S not in c1.hypotheses                  # 🎯 JAMAIS bo(R,S)


def test_parametrable():
    l4 = L.lemme_4_sous_domaine("Rp", "F", "T", "g")
    assert len(l4.hypotheses) == 4
    assert l4.conclusion == L.lemme_4_sous_domaine_cible("Rp", "F", "T", "g")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
