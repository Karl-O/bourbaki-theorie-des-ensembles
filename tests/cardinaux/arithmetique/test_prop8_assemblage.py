"""Tests §III.3.4 — Proposition 8 : ASSEMBLAGE du cœur back-and-forth par cas.

Vérifie (conclusions EXACTES + hypothèses contrôlées) le RECOLLEMENT certifié des
deux cas de la preuve back-and-forth, le CAS 1 (h(*)=*) étant clos et le CAS 2
(h(*)∈B×{0}) formulé comme l'hypothèse universelle H2 :

  • hstar_dans_BS                 : {dom h=A⊔{∅}, image h=B⊔{∅}} ⊢ h(*) ∈ B⊔{∅} ;
  • eq_copies_par_cas            : {H2} ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A×{0},B×{0}) ;
  • eq_somme_un_implique_eq_mod_cas2 : ⊢ H2 ⇒ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B))  [CLOS] ;
  • prop8_successeur_injectif_mod_cas2 : ⊢ H2 ⇒ (succ(A)=succ(B) ⇒ Card A=Card B) [CLOS].

H2(A,B) = (∀h)((bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})) est le SEUL
lemme reporté (le CAS 2, échange a₀↦b₀) ; tout le reste est certifié.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN, somme_disjointe
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur import ensembles_prop8_assemblage as A


_M = E.couple(E.VIDE, UN)                     # * = (∅, 1)


def _AS(t):
    return somme_disjointe(t, E.singleton(E.VIDE))


def _A0(t):
    return E.produit(t, E.singleton(ZERO))


def test_hstar_dans_BS():
    """{dom h=A⊔{∅}, image h=B⊔{∅}} ⊢ h(*) ∈ B⊔{∅}."""
    t = A.hstar_dans_BS("A", "B", "h")
    vh = var("h")
    hstar = E.valeur(vh, _M)
    assert t.conclusion == appartient(hstar, _AS(var("B")))
    assert t.hypotheses == frozenset({
        egal(E.dom(vh), _AS(var("A"))),
        egal(E.image(vh, _AS(var("A"))), _AS(var("B")))})


def test_cas2_hypothese():
    """H2 = (∀h)((bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0}))."""
    from bourbaki.logique.i_1_termes_relations.formule import et, pourtout
    H2 = A.cas2_hypothese("A", "B", "h")
    vh = var("h")
    hstar = E.valeur(vh, _M)
    expected = pourtout("h", impl(
        et(est_bijection_de(vh, _AS(var("A")), _AS(var("B"))),
           appartient(hstar, _A0(var("B")))),
        equipotent(_A0(var("A")), _A0(var("B")))))
    assert H2 == expected


def test_eq_copies_par_cas():
    """{H2} ⊢ Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A×{0}, B×{0})."""
    t = A.eq_copies_par_cas("A", "B", "h")
    H2 = A.cas2_hypothese("A", "B", "h")
    target = impl(equipotent(_AS(var("A")), _AS(var("B"))),
                  equipotent(_A0(var("A")), _A0(var("B"))))
    assert t.conclusion == target
    assert t.hypotheses == frozenset({H2})


def test_eq_somme_un_implique_eq_mod_cas2():
    """⊢ H2 ⇒ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)),  CLOS."""
    t = A.eq_somme_un_implique_eq_mod_cas2("A", "B", "h")
    H2 = A.cas2_hypothese("A", "B", "h")
    target = impl(H2, impl(equipotent(_AS(var("A")), _AS(var("B"))),
                           equipotent(var("A"), var("B"))))
    assert t.conclusion == target
    assert t.est_clos


def test_prop8_successeur_injectif_mod_cas2():
    """⊢ H2 ⇒ ((successeur(A)=successeur(B)) ⇒ (Card A=Card B)),  CLOS.

    La Proposition 8 (E.III.3.4) ASSEMBLÉE modulo le seul CAS 2."""
    t = A.prop8_successeur_injectif_mod_cas2("A", "B", "h")
    H2 = A.cas2_hypothese("A", "B", "h")
    va, vb = var("A"), var("B")
    target = impl(H2, impl(egal(Ent.successeur(va), Ent.successeur(vb)),
                           egal(cardinal(va), cardinal(vb))))
    assert t.conclusion == target
    assert t.est_clos
