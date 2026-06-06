"""Tests — transposition τ (échange de 2 éléments), socle de la Prop 8 (CAS 2).

τ(S,p,q) := (Δ_S privé de {(p,p),(q,q)}) ∪ {(p,q),(q,p)}.  Round 20 a certifié
le lemme de membership + 2 des 4 conjoints de bijection (fonctionnel, domaine),
conditionnels (p≠q ; p,q∈S).  Restent injectif/image/valeur + assemblage (round
suivant).  On certifie ici la CLÔTURE des 3 lemmes acquis.
"""
from bourbaki.cardinaux.arithmetique.ensembles_transposition import (
    transpo, transpo_membre, transpo_fonctionnel, transpo_domaine)
from bourbaki.logique.formule import var
import bourbaki.ensembles.ensembles_abrege as E


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
