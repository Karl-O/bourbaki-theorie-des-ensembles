"""Tests V9 — recherche guidée par priors appris (sur espace vérifié).

python -m pytest V9/test_chercheur_appris.py -v
Benchmark honnête :  python V9/test_chercheur_appris.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import Assemblage, disjonction, implication
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from outils_ia.chercheur_appris import TableProbas, ChercheurAppris, prouver_appris

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))

# Échantillon de buts (fragment propositionnel).
BUTS = [
    implication(A, A),
    implication(disjonction(A, A), A),
    implication(A, disjonction(A, B)),
]
_ROUNDS = 2  # rounds d'entraînement (le benchmark reste rapide)


def test_resultat_est_verifie():
    c = ChercheurAppris()
    res = c.prouver(implication(A, A))
    assert res is not None
    assert isinstance(res.theoreme, noyau.Theoreme)   # vérifié par construction
    assert res.theoreme.conclusion == implication(A, A) and res.theoreme.est_clos


def test_priors_apprennent():
    c = ChercheurAppris()
    avant = dict(c.priors.total)
    for _ in range(_ROUNDS):
        for but in BUTS:
            c.prouver(but)
    # les compteurs ont évolué → apprentissage effectif
    assert c.priors.total != avant
    assert sum(c.priors.succes.values()) > 0


def test_tous_les_buts_prouves():
    c = ChercheurAppris()
    for but in BUTS:
        res = c.prouver(but)
        assert res is not None and res.theoreme.conclusion == but


def test_apprentissage_ne_degrade_pas():
    """Après apprentissage, le total de nœuds ne doit pas augmenter (honnête : ≤)."""
    froid = ChercheurAppris()
    n_froid = sum(froid.prouver(b, apprendre=False).noeuds for b in BUTS)
    chaud = ChercheurAppris()
    for _ in range(_ROUNDS):                       # entraînement
        for b in BUTS:
            chaud.prouver(b)
    n_chaud = sum(prouver_appris(b, chaud.priors).noeuds for b in BUTS)
    assert n_chaud <= n_froid


if __name__ == "__main__":
    froid = ChercheurAppris()
    n_froid = sum(froid.prouver(b, apprendre=False).noeuds for b in BUTS)
    chaud = ChercheurAppris()
    for _ in range(_ROUNDS):
        for b in BUTS:
            chaud.prouver(b)
    n_chaud = sum(prouver_appris(b, chaud.priors).noeuds for b in BUTS)
    print("Nœuds (modus ponens vérifiés) sur les", len(BUTS), "buts :")
    print(f"  à froid (priors uniformes) : {n_froid}")
    print(f"  après apprentissage        : {n_chaud}")
    gain = 0 if n_froid == 0 else round(100 * (n_froid - n_chaud) / n_froid, 1)
    print(f"  gain réel                  : {gain} %")
    print("Priors appris P(famille utile) :")
    for fam in ("S1", "S2", "S3", "S4"):
        print(f"  {fam} : {chaud.priors.prob(fam):.3f}")
    print("\nChaque nœud est un modus ponens VÉRIFIÉ par le noyau (pas une étiquette).")
