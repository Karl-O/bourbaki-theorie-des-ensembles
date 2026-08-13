"""Tests §III.2.1 — un ensemble bien ordonné est TOTALEMENT ordonné.

On certifie que `bien_ordonne_est_total` établit RÉELLEMENT
    { est_bien_ordonne(R,E) } ⊢ est_totalement_ordonne(R,E)
sous la SEULE hypothèse est_bien_ordonne(R,E) (un unique élément, pas de variante
redondante de R), que la conclusion == est_totalement_ordonne(Rf,E) littéral, que la
forme close décharge l'hypothèse (0 hyp), et que theorie=22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments import ensembles_bon_ordre_total as T


def test_total_conditionnel():
    """{ est_bien_ordonne(R,E) } ⊢ est_totalement_ordonne(R,E)."""
    thm = T.bien_ordonne_est_total()
    assert not thm.est_clos
    # conclusion = est_totalement_ordonne(Rf,E) LITTÉRAL
    assert thm.conclusion == T.bien_ordonne_est_total_cible()
    # non dégénéré : la conclusion n'est PAS l'hypothèse
    assert thm.conclusion not in thm.hypotheses


def test_unique_hypothese_est_le_bon_ordre():
    """EXACTEMENT une hypothèse, et c'est est_bien_ordonne(Rf,E) (rien d'autre,
    aucune variante redondante de R)."""
    thm = T.bien_ordonne_est_total()
    assert len(thm.hypotheses) == 1
    h = list(thm.hypotheses)[0]
    # l'unique hypothèse est bien la clause de bon ordre canonique sur le graphe Rf
    Rf = T._R_de("R")
    assert h == E.est_bien_ordonne(Rf, E._terme_var("E"))
    assert h.tag == "non"          # conjonctions encodées
    assert h != thm.conclusion


def test_total_clos():
    """⊢ est_bien_ordonne(R,E) ⇒ est_totalement_ordonne(R,E) — forme CLOSE (0 hyp)."""
    clos = T.bien_ordonne_est_total_clos()
    assert clos.est_clos
    assert not clos.hypotheses
    thm = T.bien_ordonne_est_total()
    bo = list(thm.hypotheses)[0]
    assert clos.conclusion == impl(bo, T.bien_ordonne_est_total_cible())
    # discharge non vacueux : bo était réellement une hypothèse
    assert bo in set(thm.hypotheses)


def test_parametrable():
    """Fonctionne sur d'autres noms (R',F), toujours une seule hypothèse."""
    thm = T.bien_ordonne_est_total("Rp", "F")
    assert len(thm.hypotheses) == 1
    assert thm.conclusion == T.bien_ordonne_est_total_cible("Rp", "F")


def test_theorie_intacte():
    """theorie_ensembles() = 22 : aucun axiome ajouté."""
    assert len(E.theorie_ensembles().axiomes) == 22
