# -*- coding: utf-8 -*-
"""Tests — injectivité de g généralisée à tout λ (Prop. 3).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    libres_f,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop3_injectif_total import (
    coordonnees_egales_partout, REPORTES,
)


def test_coordonnees_egales_partout():
    """🎯 Le cœur pointwise se généralise à TOUT λ, prémisse réduite à « λ∈I ».

    C'est la forme EXACTE qu'attend extensionnalite_produit : les conditions de
    témoin (β(λ)∈J, β(λ)∈I, λ≤β(λ)) sont fournies sous λ∈I, pas laissées en
    prémisse."""
    th = coordonnees_egales_partout()
    assert len(th.hypotheses) == 4
    # la généralisation n'est licite que si λ ne reste libre dans aucune hypothèse
    assert all("lam" not in libres_f(h) for h in th.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_report_honnete():
    """L'assemblage final « g bijective » est explicitement reporté."""
    assert len(REPORTES) == 1


def test_prop3_g_injective():
    """👑 INJECTIVITÉ complète de la canonique cofinale : g(x)=g(x') ⊢ x=x'."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop3_injectif_total import (
        prop3_g_injective,
    )
    th = prop3_g_injective()
    assert th.conclusion == egal(var("xx"), var("xp"))
    assert len(th.hypotheses) == 4
    # les conditions de graphe sont DÉDUITES de l'appartenance à lim←, pas supposées
    assert E.est_un_graphe(var("xx")) not in th.hypotheses
    assert E.est_un_graphe(var("xp")) not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop3_g_injective_universelle():
    """👑👑 Injectivité UNIVERSELLE : (∀x)(∀x')(… ⇒ x=x') — 2 hyps de contexte.

    Vérifie l'invariant qui rend la généralisation licite : aucun des deux
    points ne reste libre dans une hypothèse."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop3_injectif_total import (
        prop3_g_injective_universelle,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    th = prop3_g_injective_universelle()
    assert len(th.hypotheses) == 1
    assert all("xx" not in libres_f(h) and "xp" not in libres_f(h)
               for h in th.hypotheses)

    def _contient(f, cible):
        return f == cible or any(_contient(s, cible) for s in getattr(f, "sous", ()))

    # la prémisse ne porte plus de condition de graphe (lemme point_limite_est_graphe)
    assert not _contient(th.conclusion, E.est_un_graphe(var("xx")))
    assert not _contient(th.conclusion, E.est_un_graphe(var("xp")))
    assert len(E.theorie_ensembles().axiomes) == 22
