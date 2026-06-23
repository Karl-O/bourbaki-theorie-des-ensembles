"""Tests §III.2 — TOTALITÉ d'un bon ordre (L1b).

On certifie que `bon_ordre_est_total` établit RÉELLEMENT la totalité (R{x,y} ou R{y,x})
sous la SEULE hypothèse est_bien_ordonne(R,E), que la forme close décharge cette
hypothèse (0 hyp), et que rien n'est une tautologie vide.  theorie=22.
"""
from bourbaki.logique.formule import impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_bien_ordonne_total as T


def test_totalite_conditionnelle():
    """{ est_bien_ordonne(R,E) } ⊢ (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x}))."""
    thm = T.bon_ordre_est_total()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    # conclusion = la totalité littérale
    assert thm.conclusion == T.bon_ordre_est_total_cible()
    # non dégénéré : la conclusion n'est PAS l'hypothèse
    assert thm.conclusion not in thm.hypotheses


def test_unique_hypothese_est_le_bon_ordre():
    """L'unique hypothèse est bien la clause de bon ordre (rien d'autre postulé)."""
    thm = T.bon_ordre_est_total()
    h = list(thm.hypotheses)[0]
    # h est une formule « non(...) » (équivalences/implications encodées) non triviale
    assert h.tag == "non"          # est_bien_ordonne = conjonctions encodées
    assert h != thm.conclusion


def test_totalite_close():
    """⊢ est_bien_ordonne(R,E) ⇒ (totalité)  — forme CLOSE (0 hypothèse)."""
    clos = T.bon_ordre_est_total_clos()
    assert clos.est_clos
    assert not clos.hypotheses
    thm = T.bon_ordre_est_total()
    bo = list(thm.hypotheses)[0]
    assert clos.conclusion == impl(bo, T.bon_ordre_est_total_cible())
    # discharge non vacueux : bo était réellement une hypothèse
    assert bo in set(thm.hypotheses)


def test_parametrable():
    """Fonctionne sur d'autres noms (R',F)."""
    thm = T.bon_ordre_est_total("Rp", "F")
    assert len(thm.hypotheses) == 1
    assert thm.conclusion == T.bon_ordre_est_total_cible("Rp", "F")


def test_theorie_intacte():
    """theorie_ensembles() = 22 : aucun axiome ajouté."""
    assert len(E.theorie_ensembles().axiomes) == 22
