"""§II.3.4 — Proposition 4 (E.II.42) : associativité de la composée de graphes.

⊢ (G3∘G2)∘G1 = G3∘(G2∘G1).

Preuve par extensionnalité (A1) sur w : on réduit chaque membre à la MÊME
relation symétrique
    R(w) = (∃p)(∃r)(w=(p,r) et (∃m)(∃y)(((p,m)∈G1 et (m,y)∈G2) et (y,r)∈G3)),
qui exprime « w est un couple (p,r) relié par une chaîne G1→G2→G3 ».

  • Membre gauche  (G3∘G2)∘G1 : l'axiome donne (∃y)((p,y)∈G1 et (y,r)∈G3∘G2)
    [milieu renommé m] ; on déplie (m,r)∈G3∘G2 → (∃y)((m,y)∈G2 et (y,r)∈G3),
    on sort le ∃y (et_existe_droite) puis on réassocie (assoc_et).
  • Membre droit   G3∘(G2∘G1) : l'axiome donne (∃y)((p,y)∈G2∘G1 et (y,r)∈G3) ;
    on déplie (p,y)∈G2∘G1 → (∃m)((p,m)∈G1 et (m,y)∈G2), on sort le ∃m
    (et_existe_gauche), puis on commute les deux ∃ (existe_commute).

Tout est réagencé sous les ∃p,∃r par congruence_existe (outils C33).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, appartient, existe
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (equivalence_transitivite, equivalence_avant,
                               antecedent_consequent, et_congruence_droite,
                               et_congruence_gauche, assoc_et, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (congruence_existe, et_existe_droite,
                                      et_existe_gauche, existe_commute, alpha_existe)
from bourbaki.ensembles.fonctions.ensembles_composee import couple_composee, _inst_composee
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension


def _expand_mid(gpn, gn, t1, t2, mid):
    """⊢ ((t1,t2) ∈ g'∘g) ⇔ (∃mid)((t1,mid)∈g et (mid,t2)∈g').

    Variante de couple_composee acceptant des TERMES t1,t2 quelconques et
    fixant le nom du liant intermédiaire à `mid` (renommage-α si capture)."""
    cc = couple_composee(gpn, gn, "a", "b")                 # coords a,b ≠ p,r,y internes
    gen = N.generalisation("a", N.generalisation("b", cc))
    e = instancie(instancie(gen, t1), t2)
    _, rhs = antecedent_consequent(equivalence_avant(e).conclusion)
    if rhs.lieur == mid:
        return e
    return equivalence_transitivite(e, alpha_existe(rhs.lieur, mid, rhs.sous[0]))


def composee_associative(g1="G1", g2="G2", g3="G3"):
    """⊢ (G3∘G2)∘G1 = G3∘(G2∘G1).   (Proposition 4, E.II.42.)"""
    G1, G2, G3 = var(g1), var(g2), var(g3)
    vp, vr, vm, vy, vw = var("p"), var("r"), var("m"), var("y"), var("w")
    comp_32 = E.composee(G3, G2)
    comp_21 = E.composee(G2, G1)
    left = E.composee(comp_32, G1)
    right = E.composee(G3, comp_21)

    weq = egal(vw, E.couple(vp, vr))
    a_pm1 = appartient(E.couple(vp, vm), G1)               # (p,m)∈G1
    a_my2 = appartient(E.couple(vm, vy), G2)               # (m,y)∈G2
    a_yr3 = appartient(E.couple(vy, vr), G3)               # (y,r)∈G3
    # forme canonique sous (∃p)(∃r) :
    #   (∃m)(∃y)(((p,m)∈G1 et (m,y)∈G2) et (y,r)∈G3)

    # ── membre gauche : (G3∘G2)∘G1 ─────────────────────────────────────────────
    iL = _inst_composee(comp_32, G1, vw)                   # ⇔ (∃p)(∃r)(weq et (∃y)((p,y)∈G1 et (y,r)∈G3∘G2))
    bodyL_y = et(appartient(E.couple(vp, vy), G1), appartient(E.couple(vy, vr), comp_32))
    renL = alpha_existe("y", "m", bodyL_y)                 # milieu y → m
    expL = _expand_mid(g3, g2, vm, vr, "y")                # (m,r)∈G3∘G2 ⇔ (∃y)((m,y)∈G2 et (y,r)∈G3)
    sL1 = et_congruence_droite(a_pm1, expL)
    sL2 = et_existe_droite(a_pm1, "y", et(a_my2, a_yr3))   # sort le ∃y
    sL3 = congruence_existe(assoc_et(a_pm1, a_my2, a_yr3), "y")
    inner_m = equivalence_transitivite(sL1, equivalence_transitivite(sL2, sL3))
    underM = equivalence_transitivite(renL, congruence_existe(inner_m, "m"))
    attachL = et_congruence_droite(weq, underM)
    fullL = equivalence_transitivite(iL, congruence_existe(congruence_existe(attachL, "r"), "p"))
    thmL = N.generalisation("w", fullL)

    # ── membre droit : G3∘(G2∘G1) ──────────────────────────────────────────────
    iR = _inst_composee(G3, comp_21, vw)                   # ⇔ (∃p)(∃r)(weq et (∃y)((p,y)∈G2∘G1 et (y,r)∈G3))
    expR = _expand_mid(g2, g1, vp, vy, "m")                # (p,y)∈G2∘G1 ⇔ (∃m)((p,m)∈G1 et (m,y)∈G2)
    sR1 = et_congruence_gauche(expR, a_yr3)
    sR2 = et_existe_gauche("m", et(a_pm1, a_my2), a_yr3)   # sort le ∃m
    chain_y = equivalence_transitivite(sR1, sR2)
    underY = congruence_existe(chain_y, "y")
    comm = existe_commute("y", "m", et(et(a_pm1, a_my2), a_yr3))   # (∃y)(∃m) ⇔ (∃m)(∃y)
    bodyR = equivalence_transitivite(underY, comm)
    attachR = et_congruence_droite(weq, bodyR)
    fullR = equivalence_transitivite(iR, congruence_existe(congruence_existe(attachR, "r"), "p"))
    thmR = N.generalisation("w", fullR)

    # ── extensionnalité : mêmes éléments ⇒ mêmes graphes ───────────────────────
    return egalite_par_extension(thmL, thmR, left, right)


__all__ = ["composee_associative"]
