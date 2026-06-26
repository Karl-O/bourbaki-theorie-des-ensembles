"""Tests — §III.1.6 : ordre « point par point » sur les applications (E III.6).

Couvre la DÉFINITION et les DEUX héritages (réflexivité, transitivité) du module
`ensembles_ordre_applications`.  Pour chaque théorème on vérifie :
  • conclusion == cible  (égalité STRUCTURELLE, == puis alpha_egal) ;
  • hypotheses == exactement { est_ordre(GF,F) }  (jamais la conclusion en
    hypothèse, aucune antisymétrie ni autre hypothèse parasite) ;
  • est_clos == False  (l'unique hypothèse est_ordre(GF,F) reste non déchargée) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé au niveau module).
Plus un test de FORME pour ordre_pointwise (c'est bien (∀x)(x∈E ⇒ (f(x),g(x))∈GF)).

Un import réussi ne prouve rien : chaque test APPELLE le théorème et inspecte son
séquent (conclusion + hypotheses + est_clos).
"""
from bourbaki.logique.i_1_termes_relations.formule import (
    var, et, impl, appartient, pourtout, alpha_egal,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre,
)
from bourbaki.ordre.iii_1_relations_ordre.iii_1_6_ordre_produit.ensembles_ordre_applications import (
    ordre_pointwise, pointwise_reflexif, pointwise_transitif, cible_transitif,
)

GF, F, E_set = var("GF"), var("F"), var("E")
f, g, h = var("f"), var("g"), var("h")


def _couple_dans(t, u, G):
    return appartient(E.couple(t, u), G)


def _val(t, x):
    return E.valeur(t, x, b="j")


# ── DÉFINITION : forme de ordre_pointwise ────────────────────────────────────
def test_ordre_pointwise_forme():
    """ordre_pointwise(GF,F,f,g,E) == (∀x)(x∈E ⇒ (f(x),g(x))∈GF), liant x frais."""
    vx = var("x")
    attendu = pourtout("x", impl(appartient(vx, E_set),
                                 _couple_dans(_val(f, vx), _val(g, vx), GF)))
    obtenu = ordre_pointwise(GF, F, f, g, E_set)
    assert obtenu == attendu
    assert alpha_egal(obtenu, attendu)


# ── HÉRITAGE 1 : réflexivité ─────────────────────────────────────────────────
def _refl():
    return pointwise_reflexif(GF, F, E_set, f)


def test_reflexif_conclusion_egale_cible():
    """⊢ (∀f)( (∀x)(x∈E ⇒ f(x)∈F) ⇒ ordre_pointwise(GF,F,f,f,E) )."""
    thm = _refl()
    vx = var("x")
    envoie = pourtout("x", impl(appartient(vx, E_set), appartient(_val(f, vx), F)))
    cible = pourtout("f", impl(envoie, ordre_pointwise(GF, F, f, f, E_set)))
    assert thm.conclusion == cible
    assert alpha_egal(thm.conclusion, cible)


def test_reflexif_hypotheses_et_clos():
    thm = _refl()
    assert thm.hypotheses == {est_ordre(GF, F)}
    assert not thm.est_clos                       # est_ordre(GF,F) non déchargée
    # honnêteté : la conclusion n'est pas glissée en hypothèse
    assert thm.conclusion not in thm.hypotheses


# ── HÉRITAGE 2 : transitivité ────────────────────────────────────────────────
def _trans():
    return pointwise_transitif(GF, F, f, g, h, E_set)


def test_transitif_conclusion_egale_cible():
    """⊢ (f≤g et g≤h) ⇒ f≤h  (point par point)."""
    thm = _trans()
    cible = cible_transitif(GF, F, f, g, h, E_set)
    assert thm.conclusion == cible
    assert alpha_egal(thm.conclusion, cible)
    # la cible est bien une implication dont la prémisse est la conjonction des
    # deux relations point par point et la conclusion la troisième.
    attendu = impl(et(ordre_pointwise(GF, F, f, g, E_set),
                      ordre_pointwise(GF, F, g, h, E_set)),
                   ordre_pointwise(GF, F, f, h, E_set))
    assert thm.conclusion == attendu


def test_transitif_hypotheses_et_clos():
    thm = _trans()
    assert thm.hypotheses == {est_ordre(GF, F)}
    assert not thm.est_clos                       # est_ordre(GF,F) non déchargée
    assert thm.conclusion not in thm.hypotheses


# ── invariant global ─────────────────────────────────────────────────────────
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
