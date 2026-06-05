"""Tests V9 — vérificateur de preuve proposée (« brouillon + vérif »), hors-ligne.

On simule l'IA par une fonction qui renvoie un script codé en dur. La propriété
testée : le noyau certifie une bonne preuve et REJETTE une mauvaise (en pointant
la ligne fautive). C'est ce qui rend une IA sûre ici : elle ne peut que proposer.

python -m pytest V9/test_verificateur.py -v
Démo :  python V9/exemples_livre.py
"""
from __future__ import annotations

from assemblage import Assemblage, implication
from notation import lire_formule, afficher
from verificateur_preuve import executer_preuve, prouver_par_llm
from exemples_livre import verifier_tous

A = Assemblage(("=", "a", "b"))


# ── Notation ──────────────────────────────────────────────────────────────────

def test_lire_formule():
    assert lire_formule("(a = b)") == A
    assert lire_formule("((a = b) => (a = b))") == implication(A, A)


def test_afficher():
    assert afficher(A) == "(a = b)"
    assert afficher(implication(A, A)) == "((a = b) ⇒ (a = b))"


# ── Vérification de preuves proposées ─────────────────────────────────────────

SCRIPT_OK = """
t1 := S1 (a = b)
t2 := S4 ((a = b) ou (a = b)) (a = b) (non (a = b))
t3 := MP t1 t2
t4 := S2 (a = b) (a = b)
t5 := MP t4 t3
"""


def test_preuve_correcte_certifiee():
    rap = executer_preuve(SCRIPT_OK, implication(A, A))
    assert rap.succes
    assert rap.theoreme.conclusion == implication(A, A) and rap.theoreme.est_clos


def test_preuve_fausse_rejetee_a_la_bonne_ligne():
    # MP avec des prémisses incohérentes à la ligne 3.
    mauvais = """
    t1 := S1 (a = b)
    t2 := S2 (a = b) (a = b)
    t3 := MP t2 t1
    """
    rap = executer_preuve(mauvais, implication(A, A))
    assert not rap.succes
    assert rap.ligne_echec == 4  # la ligne du MP fautif (lignes 1-based, blanc en tête)


def test_macro_aia_une_ligne():
    rap = executer_preuve("g := aia (a = b)", implication(A, A))
    assert rap.succes and rap.theoreme.conclusion == implication(A, A)


def test_prouver_par_llm_simule():
    # « LLM » simulé : renvoie un script codé en dur quel que soit le but.
    proposeur = lambda but_txt: SCRIPT_OK
    rap = prouver_par_llm(implication(A, A), proposeur)
    assert rap.succes


def test_mauvais_proposeur_ne_peut_pas_mentir():
    # Un proposeur qui renvoie n'importe quoi → échec, jamais un faux théorème.
    rap = prouver_par_llm(implication(A, A), lambda t: "x := S1 (a = b)")
    assert not rap.succes


# ── Le corpus du livre se vérifie intégralement ───────────────────────────────

def test_exemples_du_livre_tous_verifies():
    for titre, rap in verifier_tous():
        assert rap.succes, f"échec sur « {titre} » : {rap}"
