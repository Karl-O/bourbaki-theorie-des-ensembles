"""Tests §III.3.5 — 1^a = 1   (Proposition 11, E.III.3.5), DÉRIVÉ (rien postulé).

THÉORÈME : ⊢ exposant_cardinal_un_base(A) = Card({∅})  (= 1^a = 1, où 1 = {∅}),
car 𝓕(A;{∅}) est un SINGLETON : son UNIQUE élément est l'application ω = ((M,A),{∅})
de graphe M = A×{∅} (chaque x∈A n'a qu'une image possible, ∅).

PALIERS :
  (1) M = A×{∅} fonctionnel/dom=A/⊂A×{∅}/∈{∅}^A ;
  (2) CŒUR : tout G∈{∅}^A est M (unicité du graphe fonctionnel A→{∅}) ;
      d'où G∈{∅}^A ⇔ G=M ;
  (3) 𝓕(A;{∅}) = {((M,A),{∅})} (singleton) ;
  (4) Card(𝓕(A;{∅})) = Card({∅}) = 1 (Proposition 1 + équipotence des singletons).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, equiv, appartient, existe, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition import ensembles_exposant_un_base as M


def _one():
    return E.singleton(E.VIDE)               # 1 = {∅}


def _mm(a):
    return E.produit(a, _one())              # M = A×{∅}


# ── PALIER 1 : le graphe M = A×{∅} ────────────────────────────────────────────
def test_mm_fonctionnel():
    """⊢ est_fonctionnel(A×{∅}), CLOS."""
    t = M.mm_fonctionnel("A")
    assert t.conclusion == E.est_fonctionnel(_mm(var("A")))
    assert t.est_clos


def test_mm_domaine():
    """⊢ dom(A×{∅}) = A, CLOS."""
    t = M.mm_domaine("A")
    assert t.conclusion == egal(E.dom(_mm(var("A"))), var("A"))
    assert t.est_clos


def test_mm_inclus_produit():
    """⊢ (A×{∅}) ⊂ (A×{∅}), CLOS."""
    t = M.mm_inclus_produit("A")
    assert t.conclusion == inclus(_mm(var("A")), _mm(var("A")))
    assert t.est_clos


def test_mm_dans_exposant():
    """⊢ (A×{∅}) ∈ {∅}^A, CLOS  (forward de la caractérisation de {∅}^A)."""
    t = M.mm_dans_exposant("A")
    assert t.conclusion == appartient(_mm(var("A")), E.exposant(var("A"), _one()))
    assert t.est_clos


# ── PALIER 2 : caractérisation de {∅}^A (le cœur) ─────────────────────────────
def test_exposant_membre_implique_couple():
    """{G∈{∅}^A} ⊢ (z∈A×{∅}) ⇒ (z∈G)  (tout point de M est dans G)."""
    vG, vA = var("G"), var("A")
    t = M.exposant_membre_implique_couple("G", "A")
    assert t.conclusion == impl(appartient(var("z"), _mm(vA)), appartient(var("z"), vG))
    assert list(t.hypotheses) == [appartient(vG, E.exposant(vA, _one()))]


def test_exposant_egal_mm():
    """{G∈{∅}^A} ⊢ G = A×{∅}  (CŒUR : unicité du graphe fonctionnel A→{∅})."""
    vG, vA = var("G"), var("A")
    t = M.exposant_egal_mm("G", "A")
    assert t.conclusion == egal(vG, _mm(vA))
    assert list(t.hypotheses) == [appartient(vG, E.exposant(vA, _one()))]


def test_exposant_un_base_caracterise():
    """⊢ (G∈{∅}^A) ⇔ (G = A×{∅}), CLOS  (caractérisation COMPLÈTE de {∅}^A)."""
    vG, vA = var("G"), var("A")
    t = M.exposant_un_base_caracterise("G", "A")
    assert t.conclusion == equiv(appartient(vG, E.exposant(vA, _one())), egal(vG, _mm(vA)))
    assert t.est_clos


# ── PALIER 3 : 𝓕(A;{∅}) est un singleton ──────────────────────────────────────
def test_applications_un_base_singleton():
    """⊢ 𝓕(A;{∅}) = { ((A×{∅},A),{∅}) }, CLOS  (l'unique application A→{∅})."""
    vA = var("A")
    omega = E.couple(E.couple(_mm(vA), vA), _one())
    t = M.applications_un_base_singleton("A")
    assert t.conclusion == egal(E.applications(vA, _one()), E.singleton(omega))
    assert t.est_clos


# ── PALIER 4 : 1^a = 1 ────────────────────────────────────────────────────────
def test_eq_applications_un_base_singleton():
    """⊢ Eq(𝓕(A;{∅}), {∅}), CLOS."""
    vA = var("A")
    t = M.eq_applications_un_base_singleton("A")
    assert t.conclusion == equipotent(E.applications(vA, _one()), _one())
    assert t.est_clos


def test_exposant_un_base_egale():
    """⊢ Card(𝓕(A;{∅})) = Card({∅}), CLOS  (= 1^a = 1, Proposition 11, E.III.3.5)."""
    vA = var("A")
    t = M.exposant_un_base_egale("A")
    assert t.conclusion == egal(cardinal(E.applications(vA, _one())), cardinal(_one()))
    # = exposant_cardinal_un_base(A) = Card({∅})
    assert t.conclusion == egal(M.exposant_cardinal_un_base(vA), cardinal(_one()))
    assert t.est_clos


def test_exposant_cardinal_un_base_egale():
    """⊢ 1^a = Card({∅}), CLOS  (1^a = 1 sur l'OPÉRATEUR exposant_cardinal_un_base)."""
    vA = var("A")
    t = M.exposant_cardinal_un_base_egale("A")
    assert t.conclusion == egal(M.exposant_cardinal_un_base(vA), cardinal(_one()))
    assert t.est_clos


def test_exposant_un_base_egale_terme():
    """Robustesse : 1^a = 1 tient quand A est un TERME composé (A = U×V)."""
    T = E.produit(var("U"), var("V"))
    t = M.exposant_un_base_egale(T)
    assert t.conclusion == egal(cardinal(E.applications(T, _one())), cardinal(_one()))
    assert t.est_clos
