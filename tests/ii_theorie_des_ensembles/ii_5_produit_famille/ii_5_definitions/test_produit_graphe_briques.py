"""Tests §II.5.3 Déf.1 — les trois briques du conjoint « F ⊂ I × ⋃X_ι », et la recette.

Chaque énoncé est RECONSTRUIT À LA MAIN ici (hors des modules testés) et comparé
par égalité EXACTE ; les hypothèses sont assertées par égalité de frozenset ;
`theorie_ensembles()` vaut 22 avant ET après.

Les briques sont testées SUR DES TERMES COMPOSÉS autant que sur des noms : c'est la
term-safety qui est en jeu (les dépendances `couple_dans_produit` et
`reunion_famille_intro` n'acceptent, elles, que des NOMS — les briques les
généralisent-instancient, et une capture de liant se verrait ici).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, inclus, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    inclus_produit_est_graphe, pivot_inclusion_produit, graphe_apres_adjonction,
    hypothese_valeurs,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    composants_membre, graphe_du_point, transporter_dans_produit,
)

vG, vF, vI, vf, vg = var("G"), var("F"), var("I"), var("f"), var("g")
#: un ensemble d'indices COMPOSÉ (I ∪ {j}) — pour éprouver la term-safety
I_COMP = E.reunion(var("Iq"), E.singleton(var("jq")))


def test_invariant_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── B1 ────────────────────────────────────────────────────────────────────────
def test_inclus_produit_est_graphe():
    thm = inclus_produit_est_graphe("G", "E", "F")
    vE, vFb = var("E"), var("F")
    assert thm.conclusion == E.est_un_graphe(vG)
    assert thm.hypotheses == frozenset({inclus(vG, E.produit(vE, vFb))})


def test_inclus_produit_est_graphe_sur_termes():
    A = E.reunion_famille(vf, I_COMP)
    thm = inclus_produit_est_graphe(vG, I_COMP, A)
    assert thm.conclusion == E.est_un_graphe(vG)
    assert thm.hypotheses == frozenset({inclus(vG, E.produit(I_COMP, A))})


# ── B2 : LE PIVOT ─────────────────────────────────────────────────────────────
def _quatre_hypotheses(g, fam, i):
    return frozenset({E.est_un_graphe(g), E.est_fonctionnel(g), egal(E.dom(g), i),
                      hypothese_valeurs(fam, i, "i", g)})


def test_pivot_inclusion_produit():
    """⊢ G ⊂ I × ⋃_{ι∈I} X_ι, sous les QUATRE hypothèses EXACTES."""
    thm = pivot_inclusion_produit("G", "f", "I")
    assert thm.conclusion == inclus(vG, E.produit(vI, E.reunion_famille(vf, vI)))
    assert thm.hypotheses == _quatre_hypotheses(vG, vf, vI)
    assert len(thm.hypotheses) == 4


def test_pivot_sur_un_ensemble_d_indices_compose():
    """Term-safety : I = Iq ∪ {jq} (la forme des sites d'adjonction du III.3.6)."""
    thm = pivot_inclusion_produit(vG, vf, I_COMP)
    assert thm.conclusion == inclus(vG, E.produit(I_COMP, E.reunion_famille(vf, I_COMP)))
    assert thm.hypotheses == _quatre_hypotheses(vG, vf, I_COMP)


def test_hypothese_valeurs_est_la_quatrieme_clause():
    """La 4ᵉ clause porte le liant « i » — CELUI de l'axiome, pas un autre."""
    vi = var("i")
    assert hypothese_valeurs(vf, vI, "i", vG) == pourtout("i", impl(
        appartient(vi, vI), appartient(E.valeur(vG, vi), E.valeur_famille(vf, vi))))


# ── B3 ────────────────────────────────────────────────────────────────────────
def test_graphe_apres_adjonction():
    thm = graphe_apres_adjonction("G", "j", "x0")
    vj, vx = var("j"), var("x0")
    cible = E.est_un_graphe(E.reunion(vG, E.singleton(E.couple(vj, vx))))
    assert thm.conclusion == cible
    assert thm.hypotheses == frozenset({E.est_un_graphe(vG)})


# ── La recette d'écriture ─────────────────────────────────────────────────────
def test_composants_membre_rend_les_quatre_conjoints():
    """Les quatre chemins d'accès (g,g,g / g,g,d / g,d / d), dans l'ordre du corps."""
    membre = appartient(vF, E.produit_famille(vf, vI))
    h = N.assume(membre)
    incl, fonct, dom_eq, vals = composants_membre(h, vf, vI, vF)
    assert incl.conclusion == inclus(vF, E.produit(vI, E.reunion_famille(vf, vI)))
    assert fonct.conclusion == E.est_fonctionnel(vF)
    assert dom_eq.conclusion == egal(E.dom(vF), vI)
    assert vals.conclusion == hypothese_valeurs(vf, vI, "i", vF)
    for th in (incl, fonct, dom_eq, vals):
        assert th.hypotheses == frozenset({membre})


def test_composants_membre_refuse_un_theoreme_etranger():
    """Le garde-fou : on n'extrait pas les conjoints d'un théorème qui n'est pas F∈∏."""
    import pytest
    h = N.assume(appartient(vF, vI))
    with pytest.raises(AssertionError):
        composants_membre(h, vf, vI, vF)


def test_graphe_du_point_est_desormais_un_theoreme():
    """« Les points du produit sont des graphes » : hypothèse honnête devenue dérivée."""
    membre = appartient(vF, E.produit_famille(vf, vI))
    h = N.assume(membre)
    incl = composants_membre(h, vf, vI, vF)[0]
    thm = graphe_du_point(incl, vF, vI, vf)
    assert thm.conclusion == E.est_un_graphe(vF)
    assert thm.hypotheses == frozenset({membre})


def test_transporter_dans_produit():
    """Γ ⊢ F∈∏(f,I), Δ ⊢ (∀ι)(ι∈I⇒F(ι)∈Y_ι)  ⟹  Γ∪Δ ⊢ F∈∏(g,I)."""
    membre = appartient(vF, E.produit_famille(vf, vI))
    vals_g = hypothese_valeurs(vg, vI, "i", vF)
    thm = transporter_dans_produit(N.assume(membre), N.assume(vals_g), vF, vf, vg, vI)
    assert thm.conclusion == appartient(vF, E.produit_famille(vg, vI))
    assert thm.hypotheses == frozenset({membre, vals_g})


def test_transporter_refuse_des_valeurs_qui_ne_sont_pas_celles_du_but():
    """Garde-fou : thm_valeurs doit porter sur la famille BUT, pas sur la source."""
    import pytest
    membre = appartient(vF, E.produit_famille(vf, vI))
    vals_f = hypothese_valeurs(vf, vI, "i", vF)          # valeurs de la SOURCE
    with pytest.raises(AssertionError):
        transporter_dans_produit(N.assume(membre), N.assume(vals_f), vF, vf, vg, vI)


def test_invariant_22_axiomes_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
