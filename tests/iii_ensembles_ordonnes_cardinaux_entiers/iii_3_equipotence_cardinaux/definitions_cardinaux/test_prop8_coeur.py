"""Tests §III.3.4 — Proposition 8, CŒUR back-and-forth, CAS 1 (h fixe le marqueur).

Vérifie (conclusions EXACTES + hypothèses contrôlées) la construction de la
restriction g = h|(A×{0}) en bijection A×{0}→B×{0} sous l'hypothèse h(*)=*, puis
la réduction finale du CAS 1 :

  • g_fonctionnel  : {h fonctionnel} ⊢ est_fonctionnel(g) ;
  • g_domaine      : {A×{0}⊂dom h} ⊢ dom g = A×{0} ;
  • g_injective    : héritée de h ;
  • g_image        : {h-hyps + h(*)=*} ⊢ image(g, A×{0}) = B×{0}   (la partie dure) ;
  • cas_fixe_bijection : {bij(h,A⊔{∅},B⊔{∅}), h(*)=*} ⊢ bij(g, A×{0}, B×{0}) ;
  • eq_copies_cas_fixe : ⊢ bij(h,A⊔{∅},B⊔{∅}) ⇒ (h(*)=* ⇒ Eq(A×{0},B×{0})) ;
  • eq_cas_fixe_implique_eq : ⊢ bij(h,A⊔{∅},B⊔{∅}) ⇒ (h(*)=* ⇒ Eq(A,B)).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import UN, ZERO, somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur import prop8_coeur as C


_M = E.couple(E.VIDE, UN)                     # * = (∅, 1)


def _AS(t):
    return somme_disjointe(t, E.singleton(E.VIDE))


def _A0(t):
    return E.produit(t, E.singleton(ZERO))


def test_g_fonctionnel():
    """{est_fonctionnel(h)} ⊢ est_fonctionnel(g),  g = h|(A×{0})."""
    t = C.g_fonctionnel("A", "h")
    vh = var("h")
    assert t.conclusion == E.est_fonctionnel(C.G_RESTR("A", "h"))
    assert t.hypotheses == frozenset({E.est_fonctionnel(vh)})


def test_g_domaine():
    """{A×{0}⊂dom h} ⊢ dom g = A×{0}."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    t = C.g_domaine("A", "h")
    vh = var("h")
    g = C.G_RESTR("A", "h")
    assert t.conclusion == egal(E.dom(g), _A0(var("A")))
    assert t.hypotheses == frozenset({inclus(_A0(var("A")), E.dom(vh))})


def test_g_injective():
    """Injectivité héritée : injective_dans(g, A×{0}) sous les hyp de h."""
    AS = _AS(var("A"))
    t = C.g_injective("A", AS, "h")
    g = C.G_RESTR("A", "h")
    assert t.conclusion == E.injective_dans(g, _A0(var("A")))
    # 4 hypothèses « sur h » + inclusions
    assert len(t.hypotheses) == 4


def test_g_image():
    """{h fonct, inj, dom h=A⊔{∅}, image h=B⊔{∅}, h(*)=*} ⊢ image(g,A×{0}) = B×{0}.

    Le conjoint DUR du CAS 1 (le marqueur, fixé, est exclu des deux côtés)."""
    t = C.g_image("A", "B", "h")
    vh = var("h")
    g = C.G_RESTR("A", "h")
    assert t.conclusion == egal(E.image(g, _A0(var("A"))), _A0(var("B")))
    exp = {E.est_fonctionnel(vh), E.injective_dans(vh, _AS(var("A"))),
           egal(E.dom(vh), _AS(var("A"))), egal(E.image(vh, _AS(var("A"))), _AS(var("B"))),
           egal(E.valeur(vh, _M), _M)}
    assert t.hypotheses == frozenset(exp)


def test_cas_fixe_bijection():
    """{bij(h,A⊔{∅},B⊔{∅}), h(*)=*} ⊢ bij(g, A×{0}, B×{0})."""
    t = C.cas_fixe_bijection("A", "B", "h")
    vh = var("h")
    g = C.G_RESTR("A", "h")
    assert t.conclusion == est_bijection_de(g, _A0(var("A")), _A0(var("B")))
    assert t.hypotheses == frozenset({
        est_bijection_de(vh, _AS(var("A")), _AS(var("B"))),
        egal(E.valeur(vh, _M), _M)})


def test_eq_copies_cas_fixe():
    """⊢ bij(h,A⊔{∅},B⊔{∅}) ⇒ (h(*)=* ⇒ Eq(A×{0}, B×{0})),  CLOS."""
    t = C.eq_copies_cas_fixe("A", "B", "h")
    vh = var("h")
    target = impl(est_bijection_de(vh, _AS(var("A")), _AS(var("B"))),
                  impl(egal(E.valeur(vh, _M), _M),
                       equipotent(_A0(var("A")), _A0(var("B")))))
    assert t.conclusion == target
    assert t.est_clos


def test_eq_cas_fixe_implique_eq():
    """⊢ bij(h,A⊔{∅},B⊔{∅}) ⇒ (h(*)=* ⇒ Eq(A, B)),  CLOS  (CAS 1 COMPLET)."""
    t = C.eq_cas_fixe_implique_eq("A", "B", "h")
    vh = var("h")
    target = impl(est_bijection_de(vh, _AS(var("A")), _AS(var("B"))),
                  impl(egal(E.valeur(vh, _M), _M),
                       equipotent(var("A"), var("B"))))
    assert t.conclusion == target
    assert t.est_clos
