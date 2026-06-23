"""Tests de ensembles_iii1_ordre_props.py — transport des axiomes d'ordre §III.1.

  (1) ordre_induit_est_ordre        : est_relation_ordre(R) ⇒ est_relation_ordre(ordre_induit(R,E))
  (2) ordre_produit_est_preordre    : (transitivité ∧ réfl. impl. pointwise de la famille)
                                       ⇒ est_relation_preordre(relation_ordre_produit(Rfam,I))

Vérifie : CLÔTURE (est_clos, 0 hyp), conclusion == énoncé Bourbaki, theorie=22.
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_iii1_ordre_props as P


# Relation ≤ de test : a≤b := (a,b)∈G  (convention graphe, comme le reste du projet)
G = var("G")
def R(a, b):  return appartient(E.couple(a, b), G)

# famille de relations Rfam(ι)(u,v) := (u,v)∈Gfam(ι)  (comme test_ordre_vocab)
Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))


# ════════════════════════════════════════════════════════════════════════════
#  (1) Ordre induit sur une partie est une relation d'ordre (E.III.1.1, Ex. 2)
# ════════════════════════════════════════════════════════════════════════════
def test_ordre_induit_est_ordre_clos():
    t = P.ordre_induit_est_ordre(R)
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_ordre_induit_est_ordre_conclusion():
    t = P.ordre_induit_est_ordre(R)
    R_E = E.ordre_induit(R, var("E"))
    cible = impl(E.est_relation_ordre(R), E.est_relation_ordre(R_E))
    assert t.conclusion == cible


def test_ordre_induit_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  (2) Ordre produit est une relation de préordre (E.III.1.4)
# ════════════════════════════════════════════════════════════════════════════
def test_ordre_produit_est_preordre_clos():
    t = P.ordre_produit_est_preordre(Rfam)
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_ordre_produit_est_preordre_conclusion():
    t = P.ordre_produit_est_preordre(Rfam)
    vI, vi = var("I"), var("i")
    R_i = Rfam(vi)
    htr = pourtout("i", impl(appartient(vi, vI), E.ordre_transitif(R_i, "a", "b", "c")))
    href = pourtout("i", impl(appartient(vi, vI), E.ordre_reflexif_implicite(R_i, "a", "b")))
    ante = et(htr, href)
    Pr = V.relation_ordre_produit(Rfam, "I", "i")
    cons = E.est_relation_preordre(Pr)
    assert t.conclusion == impl(ante, cons)


def test_ordre_produit_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
