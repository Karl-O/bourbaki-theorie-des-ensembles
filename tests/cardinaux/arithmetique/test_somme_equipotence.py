"""Tests — §III.3.3 : invariance de la SOMME par équipotence (miroir de
eq_produit_invariant).

        ⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Eq(A⊔B, A₁⊔B₁).

La bijection somme K : A⊔B → A₁⊔B₁ agit selon le marqueur :
(u,0)↦(F(u),0) et (v,1)↦(G(v),1).  On vérifie ses paliers : fonctionnel,
domaine, valeur sur chaque copie (puis injectif/image/assemblage si atteints).
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.iii_3_3_somme import ensembles_somme_equipotence as S
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, subst_t


def _K():
    return S._somme_graphe("F", "G", "A", "B", "k")


# ── PALIER 1 : K fonctionnel ──────────────────────────────────────────────────
def test_somme_graphe_fonctionnel_clos():
    """K est fonctionnel : conclusion == est_fonctionnel(K) EXACTE, théorème CLOS."""
    thm = S.somme_graphe_fonctionnel()
    assert thm.conclusion == E.est_fonctionnel(_K())
    assert thm.est_clos


# ── PALIER 2 : dom K = A⊔B ────────────────────────────────────────────────────
def test_somme_graphe_domaine_clos():
    """dom(K) = A⊔B : conclusion EXACTE, théorème CLOS."""
    thm = S.somme_graphe_domaine()
    cible = egal(E.dom(_K()), S.somme_disjointe(var("A"), var("B")))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── PALIER 3a : K(u) = T[u]  (valeur générique sur A⊔B) ───────────────────────
def test_somme_graphe_valeur_generique():
    """{u∈A⊔B} ⊢ K(u) = T[u] : valeur de la fonction somme (hyp = appartenance)."""
    thm = S.somme_graphe_valeur()
    T = S._somme_terme("F", "G", "k")
    Tu = subst_t(var("u"), "k", T)
    assert thm.conclusion == egal(E.valeur(_K(), var("u")), Tu)
    assert list(thm.hypotheses) == [appartient(var("u"),
                                               S.somme_disjointe(var("A"), var("B")))]


# ── PALIER 3 : valeur de K sur chaque copie ───────────────────────────────────
def test_somme_graphe_valeur_gauche():
    """{u∈A} ⊢ K((u,0)) = (F(u),0) : la bijection somme sur la copie de gauche."""
    thm = S.somme_graphe_valeur_gauche()
    vu = var("u")
    cible = egal(E.valeur(_K(), E.couple(vu, S.ZERO)),
                 E.couple(E.valeur(var("F"), vu, "c"), S.ZERO))
    assert thm.conclusion == cible
    assert list(thm.hypotheses) == [appartient(vu, var("A"))]


def test_somme_graphe_valeur_droite():
    """{v∈B} ⊢ K((v,1)) = (G(v),1) : la bijection somme sur la copie de droite."""
    thm = S.somme_graphe_valeur_droite()
    vv = var("v")
    cible = egal(E.valeur(_K(), E.couple(vv, S.UN)),
                 E.couple(E.valeur(var("G"), vv, "c"), S.UN))
    assert thm.conclusion == cible
    assert list(thm.hypotheses) == [appartient(vv, var("B"))]


# ── PALIER 4 : injective_dans(K, A⊔B) ─────────────────────────────────────────
def test_somme_graphe_injective():
    """{F inj/A, G inj/B} ⊢ injective_dans(K, A⊔B) : conclusion EXACTE + hyps."""
    thm = S.somme_graphe_injective()
    AB = S.somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == E.injective_dans(_K(), AB, "s", "sp")
    assert set(thm.hypotheses) == {E.injective_dans(var("F"), var("A")),
                                   E.injective_dans(var("G"), var("B"))}


# ── PALIER 5 : image(K, A⊔B) = A₁⊔B₁ ──────────────────────────────────────────
def test_somme_graphe_image():
    """{F func,dom F=A,F⟨A⟩=A₁, G func,dom G=B,G⟨B⟩=B₁} ⊢ image(K,A⊔B)=A₁⊔B₁."""
    thm = S.somme_graphe_image()
    AB = S.somme_disjointe(var("A"), var("B"))
    A1B1 = S.somme_disjointe(var("A1"), var("B1"))
    assert thm.conclusion == egal(E.image(_K(), AB), A1B1)
    F, G, A, B, A1, B1 = (var(x) for x in ["F", "G", "A", "B", "A1", "B1"])
    assert set(thm.hypotheses) == {
        E.est_fonctionnel(F), egal(E.dom(F), A), egal(E.image(F, A), A1),
        E.est_fonctionnel(G), egal(E.dom(G), B), egal(E.image(G, B), B1)}


# ── PALIER 6 : assemblage bijection + INVARIANCE ──────────────────────────────
def test_somme_est_bijection():
    """{F bij A→A₁, G bij B→B₁} ⊢ est_bijection_de(K, A⊔B, A₁⊔B₁) : EXACTE + hyps."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    thm = S.somme_est_bijection()
    AB = S.somme_disjointe(var("A"), var("B"))
    A1B1 = S.somme_disjointe(var("A1"), var("B1"))
    assert thm.conclusion == est_bijection_de(_K(), AB, A1B1)
    assert set(thm.hypotheses) == {
        est_bijection_de(var("F"), var("A"), var("A1")),
        est_bijection_de(var("G"), var("B"), var("B1"))}


def test_eq_somme_invariant_clos():
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Eq(A⊔B, A₁⊔B₁) : INVARIANCE de la somme, CLOS."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    from bourbaki.logique.i_1_termes_relations.formule import impl, et
    thm = S.eq_somme_invariant()
    AB = S.somme_disjointe(var("A"), var("B"))
    A1B1 = S.somme_disjointe(var("A1"), var("B1"))
    cible = impl(et(equipotent(var("A"), var("A1")), equipotent(var("B"), var("B1"))),
                 equipotent(AB, A1B1))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── Robustesse sur TERMES composés (ex. Card U) ───────────────────────────────
def test_somme_graphe_fonctionnel_termes():
    """K fonctionnel tient quand A est un TERME composé (ex. Card U)."""
    CU = E.app("card", var("U"))
    thm = S.somme_graphe_fonctionnel("F", "G", CU, "B")
    assert thm.conclusion == E.est_fonctionnel(S._somme_graphe("F", "G", CU, "B", "k"))
    assert thm.est_clos


def test_somme_cardinale_bien_definie_clos():
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Card(A⊔B)=Card(A₁⊔B₁) : BIEN-DÉFINITION, CLOS.

    La somme cardinale a+b := Card(A⊔B) ne dépend que de Card A, Card B."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent, cardinal
    from bourbaki.logique.i_1_termes_relations.formule import impl, et
    thm = S.somme_cardinale_bien_definie()
    AB = S.somme_disjointe(var("A"), var("B"))
    A1B1 = S.somme_disjointe(var("A1"), var("B1"))
    cible = impl(et(equipotent(var("A"), var("A1")), equipotent(var("B"), var("B1"))),
                 egal(cardinal(AB), cardinal(A1B1)))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_eq_somme_invariant_termes():
    """L'invariance tient sur des TERMES composés (ex. A = Card U)."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    from bourbaki.logique.i_1_termes_relations.formule import impl, et
    CU = E.app("card", var("U"))
    thm = S.eq_somme_invariant("F", "G", CU, "B", "A1", "B1")
    AB = S.somme_disjointe(CU, var("B"))
    A1B1 = S.somme_disjointe(var("A1"), var("B1"))
    cible = impl(et(equipotent(CU, var("A1")), equipotent(var("B"), var("B1"))),
                 equipotent(AB, A1B1))
    assert thm.conclusion == cible
    assert thm.est_clos
