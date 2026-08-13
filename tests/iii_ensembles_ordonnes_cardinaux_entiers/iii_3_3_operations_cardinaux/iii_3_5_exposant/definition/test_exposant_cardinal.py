"""Tests §III.3.5 — Exponentiation cardinale fidèle  a^b := Card(𝓕(b;a)).

VOIE FIDÈLE (les axiomes de membership de 𝓕(E;F) et F^E sont des DÉFINITIONS, pas
des théorèmes) ; a^0 = 1 (Prop. 11) est DÉRIVÉ, pas postulé :

  • lemmes vide : ∅⊂X, est_fonctionnel(∅), dom(∅)=∅, ∅×F=∅ ;
  • exposant_contient_vide : ∅∈F^∅, exposant_vide_est_vide : G∈F^∅ ⇒ G=∅ ;
  • applications_vide_egale_singleton : 𝓕(∅;F)={((∅,∅),F)}  (DÉRIVÉ) ;
  • eq_applications_vide_singleton : Eq(𝓕(∅;F), {∅}) ;
  • exposant_zero_egale_un : Card(𝓕(∅;F)) = Card({∅})  (= a^0 = 1) ;
  • exposant_cardinal_zero_egale_un : exposant_cardinal_binaire(a,0) = Card({∅}).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition import ensembles_exposant_cardinal as X


def test_exposant_cardinal_binaire_def():
    """a^b = Card(𝓕(b;a))  (forme exacte du cardinal exponentiation, Déf. 4)."""
    va, vb = var("a"), var("b")
    assert X.exposant_cardinal_binaire(va, vb) == cardinal(E.applications(vb, va))


# ── axiomes de DÉFINITION bien formés (membership, S8+A1, pas des théorèmes) ────
def test_axiome_exposant_bien_forme():
    """L'axiome de membership de F^E se construit et caractérise bien G∈F^E."""
    vE, vF, vG = var("E"), var("F"), var("G")
    ax = E.axiome_exposant(vE, vF)
    # corps : G⊂E×F et G fonctionnel et dom G=E
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus, pourtout, equiv
    corps = et(et(inclus(vG, E.produit(vE, vF)), E.est_fonctionnel(vG)),
               egal(E.dom(vG), vE))
    assert ax == pourtout("G", equiv(appartient(vG, E.exposant(vE, vF)), corps))


def test_axiome_applications_bien_forme():
    """L'axiome de membership de 𝓕(E;F) caractérise t comme triple ((G,E),F)."""
    vE, vF = var("E"), var("F")
    ax = E.axiome_applications(vE, vF)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import pourtout, equiv, existe
    vt, vG = var("t"), var("G")
    triple = E.couple(E.couple(vG, vE), vF)
    corps = existe("G", et(egal(vt, triple), appartient(vG, E.exposant(vE, vF))))
    assert ax == pourtout("t", equiv(appartient(vt, E.applications(vE, vF)), corps))


# ── (a) lemmes sur le vide ─────────────────────────────────────────────────────
def test_vide_inclus():
    """⊢ ∅ ⊂ X, CLOS  (le vide est inclus dans tout ensemble)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    t = X.vide_inclus("X")
    assert t.conclusion == inclus(E.VIDE, var("X"))
    assert t.est_clos


def test_vide_est_fonctionnel():
    """⊢ est_fonctionnel(∅), CLOS  (le graphe vide est fonctionnel)."""
    t = X.vide_est_fonctionnel()
    assert t.conclusion == E.est_fonctionnel(E.VIDE)
    assert t.est_clos


def test_dom_vide_egale_vide():
    """⊢ dom(∅) = ∅, CLOS."""
    t = X.dom_vide_egale_vide()
    assert t.conclusion == egal(E.dom(E.VIDE), E.VIDE)
    assert t.est_clos


def test_produit_vide_gauche():
    """⊢ ∅×F = ∅, CLOS."""
    t = X.produit_vide_gauche("F")
    assert t.conclusion == egal(E.produit(E.VIDE, var("F")), E.VIDE)
    assert t.est_clos


# ── (a) ∅ est l'unique graphe fonctionnel de domaine ∅ ─────────────────────────
def test_exposant_contient_vide():
    """⊢ ∅ ∈ F^∅, CLOS  (∅ est un graphe fonctionnel de domaine ∅)."""
    vF = var("F")
    t = X.exposant_contient_vide("F")
    assert t.conclusion == appartient(E.VIDE, E.exposant(E.VIDE, vF))
    assert t.est_clos


def test_exposant_vide_est_vide():
    """⊢ (G ∈ F^∅) ⇒ (G = ∅), CLOS  (∅ est l'UNIQUE graphe fonctionnel de domaine ∅)."""
    vF, vG = var("F"), var("G")
    t = X.exposant_vide_est_vide("F", "G")
    assert t.conclusion == impl(appartient(vG, E.exposant(E.VIDE, vF)), egal(vG, E.VIDE))
    assert t.est_clos


# ── (b) 𝓕(∅;F) = {((∅,∅),F)}  (DÉRIVÉ) ─────────────────────────────────────────
def test_applications_vide_egale_singleton():
    """⊢ 𝓕(∅; F) = {((∅,∅),F)}, CLOS  (l'application vide est l'unique application ∅→F)."""
    vF = var("F")
    omega = E.application_vide(vF)
    t = X.applications_vide_egale_singleton("F")
    assert t.conclusion == egal(E.applications(E.VIDE, vF), E.singleton(omega))
    assert t.est_clos


# ── (c) a^0 = 1  (Proposition 11) ──────────────────────────────────────────────
def test_eq_applications_vide_singleton():
    """⊢ Eq(𝓕(∅;B), {∅}), CLOS  (l'ensemble des applications de ∅ dans B est ~ {∅}).

    Le but est nommé « B » (pas « F ») : la relation Eq(·,·) lie elle-même « F »
    (Eq(X,Y):=(∃F)bij), donc un but nommé F serait capturé — limitation honnête,
    le résultat valant pour tout ensemble indépendamment de son nom."""
    vB = var("B")
    t = X.eq_applications_vide_singleton("B")
    assert t.conclusion == equipotent(E.applications(E.VIDE, vB), E.singleton(E.VIDE))
    assert t.est_clos


def test_exposant_zero_egale_un():
    """⊢ Card(𝓕(∅;B)) = Card({∅}), CLOS  (= a^0 = 1, Proposition 11, E.III.3.5)."""
    vB = var("B")
    t = X.exposant_zero_egale_un("B")
    assert t.conclusion == egal(cardinal(E.applications(E.VIDE, vB)),
                                cardinal(E.singleton(E.VIDE)))
    assert t.est_clos


def test_exposant_cardinal_zero_egale_un():
    """⊢ exposant_cardinal_binaire(a, 0) = Card({∅}), CLOS  (a^0 = 1 sur l'OPÉRATEUR)."""
    va = var("a")
    t = X.exposant_cardinal_zero_egale_un("a")
    # LHS == a^0 := Card(applications(0, a)) = exposant_cardinal_binaire(a, 0)
    assert t.conclusion == egal(X.exposant_cardinal_binaire(va, E.VIDE),
                                cardinal(E.singleton(E.VIDE)))
    assert t.est_clos


def test_exposant_zero_egale_un_terme():
    """Robustesse : a^0 = 1 tient quand le but est un TERME composé (B = U×V).

    Le cardinal a = Card B est en général un terme composé ; la dérivation reste
    CLOSE (instances-termes débloquées par le fix α @0/@1)."""
    T = E.produit(var("U"), var("V"))
    t = X.exposant_zero_egale_un(T)
    assert t.conclusion == egal(cardinal(E.applications(E.VIDE, T)),
                                cardinal(E.singleton(E.VIDE)))
    assert t.est_clos
