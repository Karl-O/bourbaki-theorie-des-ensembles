"""Tests §III.3.5 — a^1 = a   (Proposition 11, E.III.3.5), DÉRIVÉ (rien postulé).

THÉORÈME : ⊢ exposant_cardinal_un(A) = Card(A)  (= a^1 = a, où 1 = {∅}), via la
bijection RÉCIPROQUE de l'évaluation  η : A → 𝓕({∅};A), v ↦ ((G_v,{∅}),A), avec
G_v = graphe constant {(∅,v)}.

PALIERS :
  (1) G_v fonctionnel/dom={∅}/⊂{∅}×A/∈A^{∅}/déterminé par v ; z∈G_v ⇔ z=(∅,v) ;
  (2) η fonctionnelle/dom=A/injective ;
  (3) CŒUR : tout G∈A^{∅} est G_{G(∅)} (unicité graphe domaine {∅}), surjectivité
      image(η,A)=𝓕({∅};A) ;
  (4) bijection η ⇒ Eq(A,𝓕)/Eq(𝓕,A) ⇒ a^1=a (Proposition 1).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, existe, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, equipotent, est_bijection_de
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition import exposant_un as M


def _one():
    return E.singleton(E.VIDE)               # 1 = {∅}


# ── PALIER 1 : le graphe constant G_v = {(∅,v)} ───────────────────────────────
def test_gv_fonctionnel():
    """⊢ est_fonctionnel(G_v), CLOS."""
    t = M.gv_fonctionnel()
    assert t.conclusion == E.est_fonctionnel(M._gv(var("c")))
    assert t.est_clos


def test_gv_domaine():
    """⊢ dom(G_v) = {∅}, CLOS."""
    t = M.gv_domaine()
    assert t.conclusion == egal(E.dom(M._gv(var("c"))), _one())
    assert t.est_clos


def test_gv_couple_dans():
    """⊢ (∅, v) ∈ G_v, CLOS  (le couple (∅,v) est dans le graphe constant)."""
    t = M.gv_couple_dans()
    assert t.conclusion == appartient(E.couple(E.VIDE, var("c")), M._gv(var("c")))
    assert t.est_clos


def test_gv_inclus_produit():
    """⊢ (v∈A) ⇒ (G_v ⊂ {∅}×A), CLOS."""
    t = M.gv_inclus_produit("c", "A")
    assert t.conclusion == impl(appartient(var("c"), var("A")),
                                inclus(M._gv(var("c")), E.produit(_one(), var("A"))))
    assert t.est_clos


def test_gv_dans_exposant():
    """⊢ (v∈A) ⇒ (G_v ∈ A^{∅}), CLOS  (forward de la caractérisation de A^{∅})."""
    t = M.gv_dans_exposant("c", "A")
    assert t.conclusion == impl(appartient(var("c"), var("A")),
                                appartient(M._gv(var("c")), E.exposant(_one(), var("A"))))
    assert t.est_clos


def test_gv_injectif():
    """⊢ (G_v = G_{v'}) ⇒ (v = v'), CLOS  (le graphe constant détermine sa valeur)."""
    t = M.gv_injectif()
    assert t.conclusion == impl(egal(M._gv(var("c")), M._gv(var("cp"))),
                                egal(var("c"), var("cp")))
    assert t.est_clos


def test_gv_membre():
    """⊢ (z ∈ G_v) ⇔ (z = (∅,v)), CLOS  (G_v a pour seul élément (∅,v))."""
    from bourbaki.logique.i_1_termes_relations.formule import equiv
    t = M.gv_membre()
    assert t.conclusion == equiv(appartient(var("z"), M._gv(var("c"))),
                                 egal(var("z"), E.couple(E.VIDE, var("c"))))
    assert t.est_clos


# ── PALIER 2 : la réciproque η : A → 𝓕({∅};A) ─────────────────────────────────
def test_eta_fonctionnel():
    """⊢ est_fonctionnel(η), CLOS."""
    t = M.eta_fonctionnel("A")
    assert t.conclusion == E.est_fonctionnel(M._eta(var("A")))
    assert t.est_clos


def test_eta_domaine():
    """⊢ dom(η) = A, CLOS."""
    t = M.eta_domaine("A")
    assert t.conclusion == egal(E.dom(M._eta(var("A"))), var("A"))
    assert t.est_clos


def test_eta_injective():
    """⊢ injective_dans(η, A), CLOS."""
    t = M.eta_injective("A")
    assert t.conclusion == E.injective_dans(M._eta(var("A")), var("A"))
    assert t.est_clos


# ── PALIER 3 : caractérisation de A^{∅} + surjectivité (le cœur) ──────────────
def test_exposant_couple_dans():
    """{G∈A^{∅}} ⊢ (∅, G(∅)) ∈ G  (∅ est dans dom G={∅})."""
    vG, vA = var("G"), var("A")
    t = M.exposant_couple_dans("G", "A")
    assert t.conclusion == appartient(E.couple(E.VIDE, E.valeur(vG, E.VIDE)), vG)
    # conditionnel sous la seule hypothèse G∈A^{∅}
    assert list(t.hypotheses) == [appartient(vG, E.exposant(_one(), vA))]


def test_exposant_valeur_dans_A():
    """{G∈A^{∅}} ⊢ G(∅) ∈ A  (la valeur en ∅ est dans le but)."""
    vG, vA = var("G"), var("A")
    t = M.exposant_valeur_dans_A("G", "A")
    assert t.conclusion == appartient(E.valeur(vG, E.VIDE), vA)
    assert list(t.hypotheses) == [appartient(vG, E.exposant(_one(), vA))]


def test_exposant_egal_gv():
    """{G∈A^{∅}} ⊢ G = G_{G(∅)}  (CŒUR : unicité du graphe fonctionnel de domaine {∅})."""
    vG, vA = var("G"), var("A")
    t = M.exposant_egal_gv("G", "A")
    assert t.conclusion == egal(vG, M._gv(E.valeur(vG, E.VIDE)))
    assert list(t.hypotheses) == [appartient(vG, E.exposant(_one(), vA))]


def test_exposant_un_est_gv():
    """{G∈A^{∅}} ⊢ (∃v)(v∈A et G=G_v)  (caractérisation COMPLÈTE de A^{∅})."""
    vG, vA = var("G"), var("A")
    t = M.exposant_un_est_gv("G", "A")
    corps = et(appartient(var("v"), vA), egal(vG, M._gv(var("v"))))
    assert t.conclusion == existe("v", corps)
    assert list(t.hypotheses) == [appartient(vG, E.exposant(_one(), vA))]


def test_eta_image():
    """⊢ image(η, A) = 𝓕({∅};A), CLOS  (SURJECTIVITÉ de η)."""
    vA = var("A")
    t = M.eta_image("A")
    assert t.conclusion == egal(E.image(M._eta(vA), vA), E.applications(_one(), vA))
    assert t.est_clos


# ── PALIER 4 : bijection, équipotence, a^1 = a ────────────────────────────────
def test_eta_bijection():
    """⊢ est_bijection_de(η, A, 𝓕({∅};A)), CLOS."""
    vA = var("A")
    t = M.eta_bijection("A")
    assert t.conclusion == est_bijection_de(M._eta(vA), vA, E.applications(_one(), vA))
    assert t.est_clos


def test_eq_A_applications():
    """⊢ Eq(A, 𝓕({∅};A)), CLOS."""
    vA = var("A")
    t = M.eq_A_applications("A")
    assert t.conclusion == equipotent(vA, E.applications(_one(), vA))
    assert t.est_clos


def test_eq_applications_A():
    """⊢ Eq(𝓕({∅};A), A), CLOS  (symétrie)."""
    vA = var("A")
    t = M.eq_applications_A("A")
    assert t.conclusion == equipotent(E.applications(_one(), vA), vA)
    assert t.est_clos


def test_exposant_un_egale():
    """⊢ Card(𝓕({∅};A)) = Card(A), CLOS  (= a^1 = a, Proposition 11, E.III.3.5)."""
    vA = var("A")
    t = M.exposant_un_egale("A")
    assert t.conclusion == egal(cardinal(E.applications(_one(), vA)), cardinal(vA))
    # = exposant_cardinal_un(A) = Card(A)
    assert t.conclusion == egal(M.exposant_cardinal_un(vA), cardinal(vA))
    assert t.est_clos


def test_exposant_cardinal_un_egale():
    """⊢ a^1 = Card(A), CLOS  (a^1 = a sur l'OPÉRATEUR exposant_cardinal_un)."""
    vA = var("A")
    t = M.exposant_cardinal_un_egale("A")
    assert t.conclusion == egal(M.exposant_cardinal_un(vA), cardinal(vA))
    assert t.est_clos


def test_exposant_un_egale_terme():
    """Robustesse : a^1 = a tient quand A est un TERME composé (A = U×V)."""
    T = E.produit(var("U"), var("V"))
    t = M.exposant_un_egale(T)
    assert t.conclusion == egal(cardinal(E.applications(_one(), T)), cardinal(T))
    assert t.est_clos
