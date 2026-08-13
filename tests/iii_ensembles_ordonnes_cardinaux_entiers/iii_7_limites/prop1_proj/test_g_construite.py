# -*- coding: utf-8 -*-
"""Tests — g canonique CONSTRUITE : func + dom + formule (3).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
    graphe_g, corps_formule_3, formule_3_reproduit_l_axiome, g_est_fonctionnelle,
    g_est_un_graphe, g_domaine, g_formule_3, g_formule_3_quantifiee, REPORTES,
)


def test_g_est_fonctionnelle_close():
    """🎯 est_fonctionnel(g) — CLOS.  Le terme opaque ne donnait RIEN de tel."""
    th = g_est_fonctionnelle()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == E.est_fonctionnel(graphe_g())
    assert len(E.theorie_ensembles().axiomes) == 22


def test_g_est_un_graphe_close():
    th = g_est_un_graphe()
    assert th.est_clos
    assert th.conclusion == E.est_un_graphe(graphe_g())


def test_g_domaine_clos():
    """🎯 dom(g) = lim←_I — CLOS.  Avec le test précédent, c'est la moitié
    « (func ∧ dom=X) » de est_bijection_de, celle qui manquait entièrement."""
    th = g_domaine()
    assert th.est_clos
    assert th.conclusion == egal(E.dom(graphe_g()), L.lim_proj(var("E"), var("f")))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_g_formule_3_deux_hypotheses_exactes():
    """👑 La formule (3) DÉMONTRÉE — sous ses deux prémisses, ni plus ni moins.

    Ce sont exactement les prémisses de l'axiome qu'elle rend superflu ; le test
    fige l'ensemble d'hypothèses, pas seulement son cardinal."""
    th = g_formule_3()
    assert th.hypotheses == frozenset({
        appartient(var("p"), L.lim_proj(var("E"), var("f"))),
        appartient(var("q"), var("J")),
    })
    assert len(E.theorie_ensembles().axiomes) == 22


def test_corps_formule_3_reproduit_l_axiome_du_depot():
    """👑👑 MIROIR : le constructeur partagé, appliqué au terme OPAQUE, rend
    l'axiome `axiome_canonique_g` mot pour mot.

    C'est ce test qui autorise à dire que l'énoncé démontré pour la g construite
    EST celui de l'axiome — sans lui, ce ne serait qu'une lecture à l'œil."""
    assert formule_3_reproduit_l_axiome()


def test_g_formule_3_quantifiee_close():
    """👑👑👑 L'axiome (3) est DÉMONTRABLE : forme quantifiée, 0 hypothèse.

    Un axiome démontrable est un axiome de confort, pas une hypothèse sur le
    monde — et theorie_ensembles() reste à 22."""
    th = g_formule_3_quantifiee()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == corps_formule_3(graphe_g())
    assert len(E.theorie_ensembles().axiomes) == 22


def test_report_migration_honnete():
    """La fin de migration reste explicitement reportée (2ᵉ entrée)."""
    assert any("MIGRATION" in r for r in REPORTES)


def test_brique_coordonnee_accepte_la_formule_construite():
    """👑 MIGRATION, premier pas : `cofinal_canonique_coordonnee` n'est plus
    câblée sur l'AXIOME — elle accepte une preuve de (3) en paramètre.

    Passée la version CONSTRUITE, elle rend le même énoncé, sous les mêmes
    hypothèses, mais portant sur le terme construit au lieu du terme opaque."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_props2 import (
        cofinal_canonique_coordonnee,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    hist = cofinal_canonique_coordonnee()                       # route AXIOME
    constr = cofinal_canonique_coordonnee(                      # route CONSTRUITE
        formule_3=g_formule_3_quantifiee())
    assert constr.hypotheses == hist.hypotheses
    assert constr.conclusion == egal(
        E.projection_indice(E.valeur(graphe_g(), var("x")), var("a")),
        C.application_canonique_proj_valeur(var("E"), var("f"),
                                            var("a"), var("x")))
    # les deux énoncés diffèrent : ils parlent de deux termes distincts
    assert constr.conclusion != hist.conclusion
    assert len(E.theorie_ensembles().axiomes) == 22


def test_graphe_terme_ne_lie_pas_ses_liants():
    """⚠️⚠️ PIÈGE MAJEUR figé : `graphe_terme` NE LIE PAS.

    Son encodage est app("graphe_terme", A, T) — le paramètre `x` est
    documentaire.  Le terme construit porte donc ses deux « liants » comme
    variables LIBRES.  C'est pour cela qu'il faut des noms FRAIS au site
    d'accueil, sans quoi la substitution de l'indice atteint le terme g."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_t,
    )
    assert libres_t(graphe_g()) == {"E", "J", "f", "x", "a"}
    assert libres_t(graphe_g(pt="s", idx="t")) == {"E", "J", "f", "s", "t"}


def test_injectivite_sur_le_terme_construit():
    """👑👑 L'injectivité de la Prop. 3 portée sur le g CONSTRUIT — 2 hyps.

    C'est ce qui rend la conjonction avec func/dom LICITE : les trois énoncés
    parlent enfin du même terme.  Le test l'exige explicitement."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        injectivite_g_construite,
    )
    G = graphe_g(pt="s", idx="t")
    inj = injectivite_g_construite()
    func = g_est_fonctionnelle(pt="s", idx="t")
    dom = g_domaine(pt="s", idx="t")
    assert len(inj.hypotheses) == 1
    assert func.conclusion == E.est_fonctionnel(G)      # même terme G
    assert dom.conclusion == egal(E.dom(G), L.lim_proj(var("E"), var("f")))

    def _contient(f, cible):
        return f == cible or any(_contient(s, cible) for s in getattr(f, "sous", ()))

    assert _contient(inj.conclusion,
                     egal(E.valeur(G, var("xx")), E.valeur(G, var("xp"))))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_g_injective_dans_liants_du_depot():
    """👑👑 L'injectivité dans le VOCABULAIRE du dépôt : injective_dans(G, lim←_I).

    Les liants sont ceux du dépôt (« u »/« up »), obtenus par renommage-α : on ne
    peut pas démontrer directement avec « u », qui est un liant réservé du kit."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        g_injective_dans,
    )
    th = g_injective_dans()
    G = graphe_g(pt="s", idx="t")
    assert th.conclusion == E.injective_dans(G, L.lim_proj(var("E"), var("f")))
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_g_bijection_sous_surjectivite():
    """👑👑👑 LA PROP. 3 en vocabulaire du dépôt, à UNE prémisse nommée près.

    ⊢ ( G⟨lim←_I⟩ = lim←_J ) ⇒ est_bijection_de(G, lim←_I, lim←_J), sous les
    deux seules hypothèses de la Prop. 3.  Trois des quatre conjoints sont
    acquis sur le terme construit ; le quatrième est porté en prémisse EXPLICITE
    plutôt que passé sous silence.  Que la conjonction se forme prouve au
    passage que les quatre portent bien sur le MÊME terme."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        g_bijection_sous_surjectivite,
    )
    th = g_bijection_sous_surjectivite()
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reports_a_jour():
    """Deux reports honnêtes : la surjectivité ensembliste et la fin de migration."""
    assert len(REPORTES) == 2
    assert "SURJECTIVITÉ ENSEMBLISTE" in REPORTES[0]
