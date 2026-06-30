"""§II.3 — Caractérisation au niveau du COUPLE de la diagonale Δ_X (Bourbaki E II.13).

La diagonale Δ_X (graphe de la correspondance identique Id_X = (Δ_X, X, X), Déf. 8)
est, par axiome, Δ_X = { z | (∃u)(u∈X et z=(u,u)) }.  Ce module en donne la forme
APPLIQUÉE À UN COUPLE — l'analogue, pour la diagonale, de `couple_reciproque`
(pour G⁻¹) et `couple_composee` (pour G'∘G) :

  ⊢ ((a,b) ∈ Δ_X) ⇔ (a∈X et a=b).

C'est la brique de base pour raisonner sur Id_X (réciproque, neutre de la
composition, etc.).

STRATÉGIE.  L'axiome `AXIOME_DIAGONALE` instancié en (X, (a,b)) donne
(a,b)∈Δ_X ⇔ (∃u)(u∈X et (a,b)=(u,u)).  Sous le témoin u : la Proposition 1
((a,b)=(u,u) ⇔ a=u et b=u) fournit a=u, b=u, d'où a∈X [Leibniz] et a=b
[transitivité] ; ∃-élim propre (u absent de la conclusion).  Réciproquement
(témoin u:=a) : de a∈X et a=b on a (a,b)=(a,a) [congruence], donc (∃u)(…).

theorie_ensembles() INCHANGÉE (= 22) : AXIOME_DIAGONALE déjà compté.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, appartient, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import proposition_1


def _tc(t):
    return t if isinstance(t, Terme) else var(t)


def _inst_diag(vX, z):
    """⊢ (z∈Δ_X) ⇔ (∃d0)(d0∈X et z=(d0,d0)).   (instance de AXIOME_DIAGONALE.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE)
    return instancie(instancie(ax, vX), z)


# @livre Ch.II §3.3 Def.8 | E II.13 L.18-20 | PDF p.64
def couple_diagonale(a="a", b="b", x="X"):
    """⊢ ((a,b) ∈ Δ_X) ⇔ (a∈X et a=b).   (Bourbaki E II.13, Déf. 8 ; Δ_X = graphe de Id_X.)

    a, b, X : noms OU termes ; doivent être ≠ d0, w (témoin/trou internes)."""
    va, vb, vX = _tc(a), _tc(b), _tc(x)
    vu = var("d0")                                        # liant de l'axiome (témoin diagonal)
    cple = E.couple(va, vb)
    inst = _inst_diag(vX, cple)                           # (a,b)∈Δ_X ⇔ (∃d0)(d0∈X et (a,b)=(d0,d0))
    body = et(appartient(vu, vX), egal(cple, E.couple(vu, vu)))

    # ── ⇒ : (∃d0)body ⇒ (a∈X et a=b) ────────────────────────────────────────────
    hb = N.assume(body)
    u_in_X = conjonction_elim_gauche(hb)                  # d0∈X
    comps = N.modus_ponens(conjonction_elim_droite(hb),
                           equivalence_avant(proposition_1(va, vb, vu, vu)))   # a=d0 et b=d0
    a_eq_u, b_eq_u = conjonction_elim_gauche(comps), conjonction_elim_droite(comps)
    a_in_X = N.modus_ponens(u_in_X, equivalence_arriere(
        N.modus_ponens(a_eq_u, N.s6(va, vu, "w", appartient(var("w"), vX)))))  # a∈X
    a_eq_b = composer_egalites(a_eq_u, N.modus_ponens(b_eq_u, symetrie(vb, vu)))  # a=d0=b ⇒ a=b
    avant = existe_elimination(
        N.loi_deduction(body, conjonction_intro(a_in_X, a_eq_b)), "d0")        # (∃d0)body ⇒ (a∈X et a=b)

    # ── ⇐ : (a∈X et a=b) ⇒ (∃d0)body  (témoin d0 := a) ──────────────────────────
    h2 = N.assume(et(appartient(va, vX), egal(va, vb)))
    a_in, a_b = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)
    cpl_eq = N.modus_ponens(N.modus_ponens(a_b, symetrie(va, vb)),               # b=a
                            congruence_terme(vb, va, E.couple(va, var("w")), w="w"))  # (a,b)=(a,a)
    ex = N.modus_ponens(conjonction_intro(a_in, cpl_eq), N.s5(body, va, "d0"))   # (∃d0)body
    arriere = N.loi_deduction(et(appartient(va, vX), egal(va, vb)), ex)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def couple_diagonale_cible(a="a", b="b", x="X"):
    """Énoncé visé de `couple_diagonale` (vérification stricte)."""
    va, vb, vX = _tc(a), _tc(b), _tc(x)
    return equiv(appartient(E.couple(va, vb), E.diagonale(vX)),
                 et(appartient(va, vX), egal(va, vb)))


__all__ = ["couple_diagonale", "couple_diagonale_cible"]
