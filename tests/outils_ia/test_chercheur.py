"""Tests V9 — recherche de démonstrations branchée sur le noyau.

Propriété fondamentale (le but de tout V9) : ce que la recherche renvoie est un
`noyau.Theoreme`, donc une preuve VÉRIFIÉE — on ne peut pas en fabriquer
autrement. C'est ce qui manquait à V8.

python -m pytest V9/test_chercheur.py -v
Démo :  python V9/test_chercheur.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import Assemblage, disjonction, implication
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from outils_ia.ia.chercheur import Prouveur, saturer_mp

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))
C = Assemblage(("=", "c", "d"))


def test_resultat_est_un_theoreme_du_noyau():
    """La propriété centrale : la recherche ne renvoie que des Theoreme vérifiés."""
    p = Prouveur()
    th = p.prouver(implication(A, A))
    assert isinstance(th, noyau.Theoreme)        # ⇒ vérifié par construction
    assert th.conclusion == implication(A, A)
    assert th.est_clos


def test_a_implique_a_par_deduction_seule():
    # Sans schémas : trouvé par supposer A / décharger.
    p = Prouveur()
    th = p.prouver(implication(A, A), schemas=False)
    assert th is not None and th.conclusion == implication(A, A) and th.est_clos


def test_a_implique_a_par_schemas_seuls():
    # Sans déduction (profondeur 0) : trouvé par saturation MP des schémas S1–S4.
    p = Prouveur()
    th = p.prouver(implication(A, A), profondeur_max=0, schemas=True)
    assert th is not None and th.conclusion == implication(A, A) and th.est_clos


def test_syllogisme_par_recherche():
    # À partir des implications supposées A⇒B et B⇒C, prouver A⇒C.
    p = Prouveur()
    lemmes = (noyau.assume(implication(A, B)), noyau.assume(implication(B, C)))
    th = p.prouver(implication(A, C), lemmes=lemmes, schemas=False)
    assert th is not None and th.conclusion == implication(A, C)
    # hypothèses = les deux implications supposées (déchargeables ensuite)
    assert th.hypotheses == {implication(A, B), implication(B, C)}


def test_s1_disjonction_par_schemas():
    # ⊢ (A∨A) ⇒ A  doit être trouvé via les instances de schémas.
    p = Prouveur()
    th = p.prouver(implication(disjonction(A, A), A), profondeur_max=0)
    assert th is not None and th.conclusion == implication(disjonction(A, A), A)


def test_echec_rend_none_sans_exception():
    # Un but non démontrable (atome isolé) échoue proprement.
    p = Prouveur()
    th = p.prouver(A, schemas=True, noeuds_max=500)
    assert th is None


def test_memorisation_des_lemmes():
    p = Prouveur()
    p.prouver(implication(A, A))
    assert implication(A, A) in p.base        # lemme clos appris


def test_saturer_mp_chaine():
    # MP enchaîné : de ⊢A, ⊢A⇒B, ⊢B⇒C, saturer produit ⊢C.
    faits, _ = saturer_mp([
        noyau.assume(A),
        noyau.assume(implication(A, B)),
        noyau.assume(implication(B, C)),
    ])
    assert C in faits


if __name__ == "__main__":
    p = Prouveur()
    for nom, but in [("A ⇒ A", implication(A, A)),
                     ("(A∨A) ⇒ A", implication(disjonction(A, A), A))]:
        th = p.prouver(but)
        print(f"{nom:14} →  {th}")
    print(f"\nNœuds explorés : {p.noeuds} ; lemmes appris : {len(p.base)}")
    print("Tous les résultats ci-dessus sont des Theoreme vérifiés par le noyau.")
