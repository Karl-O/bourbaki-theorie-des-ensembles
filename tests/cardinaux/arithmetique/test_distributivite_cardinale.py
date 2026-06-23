"""Tests — §III.3.3 : DISTRIBUTIVITÉ du produit sur la somme cardinale (E.III.3.3,
Prop. 3) :

        ⊢ Card(A × (B⊔C)) = Card((A×B) ⊔ (A×C))      [ a·(b+c) = a·b + a·c ].

La bijection distributive D : A×(B⊔C) → (A×B)⊔(A×C) est le ré-arrangement
(x,(y,m)) ↦ ((x,y),m) (PAS de cas-analyse dans le terme).  On vérifie ses
paliers : fonctionnel, domaine, valeur générique + sur chaque copie, injectif,
image, puis l'assemblage bijection / Eq / égalité des cardinaux.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.iii_3_3_produit import ensembles_distributivite_cardinale as D
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, cardinal, equipotent
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, subst_t


def _D():
    return D._distrib_graphe("A", "B", "C", "k")


def _Dom():
    return E.produit(var("A"), D.somme_disjointe(var("B"), var("C")))


def _Cod():
    AB = E.produit(var("A"), var("B"))
    AC = E.produit(var("A"), var("C"))
    return D.somme_disjointe(AB, AC)


# ── PALIER 1 : D fonctionnel ──────────────────────────────────────────────────
def test_distrib_graphe_fonctionnel_clos():
    """D est fonctionnel : conclusion == est_fonctionnel(D) EXACTE, théorème CLOS."""
    thm = D.distrib_graphe_fonctionnel()
    assert thm.conclusion == E.est_fonctionnel(_D())
    assert thm.est_clos


# ── PALIER 2 : dom D = A×(B⊔C) ────────────────────────────────────────────────
def test_distrib_graphe_domaine_clos():
    """dom(D) = A×(B⊔C) : conclusion EXACTE, théorème CLOS."""
    thm = D.distrib_graphe_domaine()
    assert thm.conclusion == egal(E.dom(_D()), _Dom())
    assert thm.est_clos


# ── PALIER 3 : D(u) = T[u]  (valeur générique sur A×(B⊔C)) ─────────────────────
def test_distrib_graphe_valeur_generique():
    """{u∈A×(B⊔C)} ⊢ D(u) = T[u] : valeur de la fonction distributive (hyp = appartenance)."""
    thm = D.distrib_graphe_valeur()
    T = D._distrib_terme("k")
    Tu = subst_t(var("u"), "k", T)
    assert thm.conclusion == egal(E.valeur(_D(), var("u")), Tu)
    assert list(thm.hypotheses) == [appartient(var("u"), _Dom())]


# ── PALIER 3g/3d : valeur de D sur chaque copie ───────────────────────────────
def test_distrib_graphe_valeur_gauche():
    """{x∈A, y∈B} ⊢ D((x,(y,0))) = ((x,y),0) : la bijection distributive, copie gauche."""
    thm = D.distrib_graphe_valeur_gauche()
    vx, ve = var("x"), var("e")
    cpl = E.couple(vx, E.couple(ve, D.ZERO))
    cible = egal(E.valeur(_D(), cpl), E.couple(E.couple(vx, ve), D.ZERO))
    assert thm.conclusion == cible
    assert set(thm.hypotheses) == {appartient(vx, var("A")), appartient(ve, var("B"))}


def test_distrib_graphe_valeur_droite():
    """{x∈A, z∈C} ⊢ D((x,(z,1))) = ((x,z),1) : la bijection distributive, copie droite."""
    thm = D.distrib_graphe_valeur_droite()
    vx, ve = var("x"), var("e")
    cpl = E.couple(vx, E.couple(ve, D.UN))
    cible = egal(E.valeur(_D(), cpl), E.couple(E.couple(vx, ve), D.UN))
    assert thm.conclusion == cible
    assert set(thm.hypotheses) == {appartient(vx, var("A")), appartient(ve, var("C"))}


# ── PALIER 4 : injective_dans(D, A×(B⊔C)) ─────────────────────────────────────
def test_distrib_graphe_injective_clos():
    """⊢ injective_dans(D, A×(B⊔C)) : conclusion EXACTE (liants s,sp), théorème CLOS.

    Reconstruction pure (pas de cas-analyse de marqueur) : pr₂u∈B⊔C est un couple."""
    thm = D.distrib_graphe_injective()
    assert thm.conclusion == E.injective_dans(_D(), _Dom(), "s", "sp")
    assert thm.est_clos


# ── PALIER 5 : image(D, A×(B⊔C)) = (A×B)⊔(A×C) ────────────────────────────────
def test_distrib_graphe_image_clos():
    """⊢ image(D, A×(B⊔C)) = (A×B)⊔(A×C) : surjectivité, conclusion EXACTE, CLOS."""
    thm = D.distrib_graphe_image()
    assert thm.conclusion == egal(E.image(_D(), _Dom()), _Cod())
    assert thm.est_clos


# ── PALIER 6 : assemblage bijection + Eq + égalité des cardinaux ──────────────
def test_distrib_est_bijection_clos():
    """⊢ est_bijection_de(D, A×(B⊔C), (A×B)⊔(A×C)) : conclusion EXACTE, CLOS."""
    thm = D.distrib_est_bijection()
    assert thm.conclusion == est_bijection_de(_D(), _Dom(), _Cod())
    assert thm.est_clos


def test_eq_distributivite_clos():
    """⊢ Eq(A×(B⊔C), (A×B)⊔(A×C)) : distributivité ensembliste, CLOS."""
    thm = D.eq_distributivite()
    assert thm.conclusion == equipotent(_Dom(), _Cod())
    assert thm.est_clos


def test_distributivite_cardinale_clos():
    """⊢ Card(A×(B⊔C)) = Card((A×B)⊔(A×C)) : a·(b+c)=a·b+a·c, CLOS.

    LE théorème de distributivité du produit cardinal sur la somme cardinale."""
    thm = D.distributivite_cardinale()
    assert thm.conclusion == egal(cardinal(_Dom()), cardinal(_Cod()))
    assert thm.est_clos


# ── Robustesse sur TERMES composés (ex. Card U) ───────────────────────────────
def test_distributivite_cardinale_termes():
    """La distributivité tient quand A,B,C sont des TERMES composés (ex. A = Card U)."""
    CU = E.app("card", var("U"))
    thm = D.distributivite_cardinale(CU, "B", "C")
    Dom = E.produit(CU, D.somme_disjointe(var("B"), var("C")))
    AB = E.produit(CU, var("B"))
    AC = E.produit(CU, var("C"))
    Cod = D.somme_disjointe(AB, AC)
    assert thm.conclusion == egal(cardinal(Dom), cardinal(Cod))
    assert thm.est_clos
