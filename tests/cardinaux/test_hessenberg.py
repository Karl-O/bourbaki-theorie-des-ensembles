"""Tests §III.6.3 — Théorème 2 (HESSENBERG) : 𝔞·𝔞 = 𝔞 pour 𝔞 infini.

ÉTAT (honnête) :
  • Direction FACILE  a ≤ a·a  CLOSE (diagonale u↦(u,u)) ;
  • Réduction Cantor–Bernstein  (a≤a·a et a·a≤a) ⇒ a·a=a  CLOSE ;
  • Ponts conditionnels  (a·a≤a)⇒a·a=a  et  (a∞⇒a·a≤a)⇒(a∞⇒a·a=a)  CLOS ;
  • Direction PROFONDE  a·a≤a (pour a infini) : OUVERTE, isolée en hypothèse honnête
    (enonce_hard_aa_inf_egal_a).
Aucun théorème faux ; theorie_ensembles() = 22 (rien postulé).
"""
from bourbaki.logique.formule import var, egal, et, impl
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, est_injection_de)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.cardinaux import ensembles_hessenberg as H


# ════════════════════════════════════════════════════════════════════════════
#  INJECTION DIAGONALE  u ↦ (u,u)   (les quatre conjoints + l'assemblage)
# ════════════════════════════════════════════════════════════════════════════
def test_diag_fonctionnel():
    """⊢ est_fonctionnel(graphe_terme(A,(d0,d0))), CLOS."""
    t = H.diag_fonctionnel()
    assert t.est_clos and len(t.hypotheses) == 0


def test_diag_domaine():
    """⊢ dom(F) = A  (la diagonale est définie sur tout A), CLOS."""
    t = H.diag_domaine()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == egal(E.dom(H._F(var("A"))), var("A"))


def test_diag_valeur():
    """⊢_{u∈A}  F(u) = (u,u), CLOS sous l'hypothèse u∈A."""
    t = H.diag_valeur()
    assert t.est_clos and len(t.hypotheses) == 0
    F = H._F(var("A"))
    assert t.conclusion == impl(E.appartient(var("u"), var("A")),
                                egal(E.valeur(F, var("u")), E.couple(var("u"), var("u"))))


def test_diag_injective():
    """⊢ injective_dans(F, A), CLOS."""
    t = H.diag_injective()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == E.injective_dans(H._F(var("A")), var("A"))


def test_diag_image_inclus():
    """⊢ image(F, A) ⊂ A×A, CLOS."""
    t = H.diag_image_inclus()
    assert t.est_clos and len(t.hypotheses) == 0
    F = H._F(var("A"))
    assert t.conclusion == E.inclus(E.image(F, var("A")), E.produit(var("A"), var("A")))


# ════════════════════════════════════════════════════════════════════════════
#  DIRECTION FACILE :  A ≤ A×A   et   a ≤ a·a
# ════════════════════════════════════════════════════════════════════════════
def test_diag_inf_egal_produit():
    """⊢ A ≤ A×A  (l'injection diagonale), CLOS, conclusion == inf_egal_card(A, A×A)."""
    t = H.diag_inf_egal_produit()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == inf_egal_card(var("A"), E.produit(var("A"), var("A")))


def test_cardinal_inf_egal_carre():
    """⊢ Card(A) ≤ produit_cardinal_binaire(Card A, Card A)  (= a ≤ a·a), CLOS.

    Conclusion == a ≤ a·a sur les VRAIS cardinaux (a·a := Card(a×a))."""
    t = H.cardinal_inf_egal_carre()
    assert t.est_clos and len(t.hypotheses) == 0
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert t.conclusion == inf_egal_card(a, aa)


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION par CANTOR–BERNSTEIN
# ════════════════════════════════════════════════════════════════════════════
def test_carre_inf_egal_si_hard():
    """⊢ (a≤a·a et a·a≤a) ⇒ a·a=a, CLOS (antisymétrie de ≤ + Prop. 1)."""
    t = H.carre_inf_egal_si_hard()
    assert t.est_clos and len(t.hypotheses) == 0
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert t.conclusion == impl(et(inf_egal_card(a, aa), inf_egal_card(aa, a)),
                                egal(aa, a))


def test_hessenberg_si_hard():
    """⊢ (a·a≤a) ⇒ a·a=a, CLOS  (la diagonale fournit le ≤ ; CB referme)."""
    t = H.hessenberg_si_hard()
    assert t.est_clos and len(t.hypotheses) == 0
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert t.conclusion == impl(inf_egal_card(aa, a), egal(aa, a))


def test_hessenberg_depuis_hard():
    """⊢ (a∞⇒a·a≤a) ⇒ (a∞⇒a·a=a), CLOS — PONT FINAL vers le théorème complet."""
    t = H.hessenberg_depuis_hard()
    assert t.est_clos and len(t.hypotheses) == 0
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert t.conclusion == impl(impl(est_infini(a), inf_egal_card(aa, a)),
                                impl(est_infini(a), egal(aa, a)))


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS-FRONTIÈRE (formules, non prouvées — honnêteté anti-faux)
# ════════════════════════════════════════════════════════════════════════════
def test_enonce_hessenberg_forme():
    """L'énoncé final est bien  est_infini(a) ⇒ (a·a = a)."""
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert H.enonce_hessenberg() == impl(est_infini(a), egal(aa, a))


def test_enonce_hard_forme():
    """Le verrou résiduel est bien  est_infini(a) ⇒ (a·a ≤ a)  (la direction ≥)."""
    a = cardinal(var("A"))
    aa = produit_cardinal_binaire(a, a)
    assert H.enonce_hard_aa_inf_egal_a() == impl(est_infini(a), inf_egal_card(aa, a))


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT : theorie_ensembles() = 22  (rien postulé)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_inchangee():
    """theorie_ensembles() reste = 22 axiomes : aucun axiome ajouté pour Hessenberg."""
    assert len(E.theorie_ensembles().axiomes) == 22
