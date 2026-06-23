"""Tests — transposition τ (échange de 2 éléments), socle de la Prop 8 (CAS 2).

τ(S,p,q) := (Δ_S privé de {(p,p),(q,q)}) ∪ {(p,q),(q,p)}.  Round 20 a certifié
le lemme de membership + 2 des 4 conjoints (fonctionnel, domaine).  Ce round FINIT
la transposition : injectif, image, valeur(q)=p, et l'EXISTENCE comme bijection
(les 4 conjoints + τ(q)=p assemblés sous p,q∈S, p≠q).
"""
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition import (
    transpo, transpo_membre, transpo_fonctionnel, transpo_domaine,
    transpo_injective, transpo_image, transpo_valeur_q, transposition_existe)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import injective_dans, image, valeur
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import antecedent_consequent
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E


def test_transpo_terme():
    t = transpo(var("S"), var("p"), var("q"))
    assert t.nom == "reunion"            # τ est une réunion (Δ privée ∪ échange)


def test_transpo_membre_clos():
    assert transpo_membre("S", "p", "q", "x", "y").est_clos


def test_transpo_fonctionnel_clos():
    th = transpo_fonctionnel("S", "p", "q")
    assert th.est_clos and th.conclusion.tag == "ou"   # ¬(p=q) ⇒ fonctionnel


def test_transpo_domaine_clos():
    th = transpo_domaine("S", "p", "q")
    assert th.est_clos and th.conclusion.tag == "ou"   # (p∈S et q∈S) ⇒ dom=S


def test_transpo_injective_clos():
    th = transpo_injective("S", "p", "q")
    assert th.est_clos
    _, cons = antecedent_consequent(th.conclusion)     # (p∈S et q∈S et ¬(p=q)) ⇒ injective_dans(τ,S)
    T = transpo(var("S"), var("p"), var("q"))
    assert cons == injective_dans(T, var("S"))


def test_transpo_image_clos():
    th = transpo_image("S", "p", "q")
    assert th.est_clos
    _, cons = antecedent_consequent(th.conclusion)     # ... ⇒ image(τ,S)=S
    T = transpo(var("S"), var("p"), var("q"))
    assert cons == egal(image(T, var("S")), var("S"))


def test_transpo_valeur_q_clos():
    th = transpo_valeur_q("S", "p", "q")
    assert th.est_clos
    _, cons = antecedent_consequent(th.conclusion)     # ... ⇒ τ(q)=p
    T = transpo(var("S"), var("p"), var("q"))
    assert cons == egal(valeur(T, var("q")), var("p"))


def test_transposition_existe_clos():
    th = transposition_existe("S", "p", "q")
    assert th.est_clos
    _, cons = antecedent_consequent(th.conclusion)     # ... ⇒ (∃F)(bij(F,S,S) et F(q)=p)
    assert cons.tag == "exists" and cons.lieur == "F"  # existentiel sur le graphe τ
    # le corps EST (est_bijection_de(F,S,S) et F(q)=p)
    T = transpo(var("S"), var("p"), var("q"))
    matrice = et(est_bijection_de(var("F"), var("S"), var("S")),
                 egal(valeur(var("F"), var("q")), var("p")))
    assert cons.sous[0] == matrice
