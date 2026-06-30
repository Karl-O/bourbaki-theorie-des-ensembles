"""§II.3.3 — MONOTONIE de la composée de graphes (Bourbaki E II.13).

Énoncé Bourbaki verbatim (E II.13, Remarque) :

  « G1 ⊂ G2 et G1' ⊂ G2' entraînent G1'∘G1 ⊂ G2'∘G2. »

(La composition des graphes est croissante pour l'inclusion, en chacun de ses
deux arguments.)

RÉSULTAT (conditionnel HONNÊTE, certifié par le noyau LCF) :

  { G1 ⊂ G2, G1' ⊂ G2' } ⊢ G1'∘G1 ⊂ G2'∘G2.

STRATÉGIE (calquée sur `_involution_incluse` de la réciproque).  Un élément
z ∈ G1'∘G1 est, par l'axiome de composition, un couple z=(p,r) tel que
(∃y)((p,y)∈G1 et (y,r)∈G1').  Les inclusions G1⊂G2, G1'⊂G2' INSTANCIÉES aux
couples (p,y) et (y,r) donnent (p,y)∈G2 et (y,r)∈G2' ; on reconstruit le témoin
(∃y)((p,y)∈G2 et (y,r)∈G2'), d'où z=(p,r)∈G2'∘G2 par le même axiome.  Les
∃-éliminations (y, puis r, p) sont PROPRES : la conclusion z∈G2'∘G2 ne contient
aucune de ces lettres libres.  Les inclusions restent hypothèses honnêtes.

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, appartient, existe, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import _inst_composee


def _tc(t):
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.II §3.3 Rem.- | E II.13 L.3-4 | PDF p.64
def composee_monotone(g1="G1", g1p="G1p", g2="G2", g2p="G2p"):
    """{ G1⊂G2, G1'⊂G2' } ⊢ G1'∘G1 ⊂ G2'∘G2.   (Bourbaki E II.13, Remarque.)

    Monotonie de la composée pour l'inclusion (croissante en ses deux graphes).
    Noms OU termes ; doivent être ≠ p, r, y, z (liants/témoins internes)."""
    vG1, vG1p, vG2, vG2p = _tc(g1), _tc(g1p), _tc(g2), _tc(g2p)
    vz, vp, vr, vy = var("z"), var("p"), var("r"), var("y")
    C1, C2 = E.composee(vG1p, vG1), E.composee(vG2p, vG2)
    h1 = N.assume(inclus(vG1, vG2))            # G1 ⊂ G2  (honnête)
    h1p = N.assume(inclus(vG1p, vG2p))         # G1' ⊂ G2'  (honnête)

    inst1 = _inst_composee(vG1p, vG1, vz)      # z∈C1 ⇔ (∃p)(∃r)(z=(p,r) et (∃y)((p,y)∈G1 et (y,r)∈G1'))
    inst2 = _inst_composee(vG2p, vG2, vz)      # idem pour C2 / G2, G2'

    # ── inner = (p,y)∈G1 et (y,r)∈G1' ⊢ (∃y)((p,y)∈G2 et (y,r)∈G2') ──────────────
    inner = et(appartient(E.couple(vp, vy), vG1), appartient(E.couple(vy, vr), vG1p))
    h_inner = N.assume(inner)
    py_g2 = N.modus_ponens(conjonction_elim_gauche(h_inner),
                           instancie(h1, E.couple(vp, vy)))    # (p,y)∈G2
    yr_g2p = N.modus_ponens(conjonction_elim_droite(h_inner),
                            instancie(h1p, E.couple(vy, vr)))  # (y,r)∈G2'
    phi2_body = et(appartient(E.couple(vp, vy), vG2), appartient(E.couple(vy, vr), vG2p))
    phi2 = N.modus_ponens(conjonction_intro(py_g2, yr_g2p), N.s5(phi2_body, vy, "y"))  # (∃y)phi2_body
    elim_y = existe_elimination(N.loi_deduction(inner, phi2), "y")   # (∃y)inner ⇒ (∃y)phi2_body

    # ── body_pr = (z=(p,r) et (∃y)inner) ⊢ z∈C2 ─────────────────────────────────
    body_pr = et(egal(vz, E.couple(vp, vr)), existe("y", inner))
    h_body = N.assume(body_pr)
    weq = conjonction_elim_gauche(h_body)                    # z=(p,r)
    phi2_ok = N.modus_ponens(conjonction_elim_droite(h_body), elim_y)   # (∃y)phi2_body
    BODY2 = conjonction_intro(weq, phi2_ok)                  # z=(p,r) et (∃y)phi2_body
    body2 = et(egal(vz, E.couple(vp, vr)), existe("y", phi2_body))
    ex_r = N.modus_ponens(BODY2, N.s5(body2, vr, "r"))       # (∃r)body2
    ex_pr2 = N.modus_ponens(ex_r, N.s5(existe("r", body2), vp, "p"))   # (∃p)(∃r)body2
    z_in_C2 = N.modus_ponens(ex_pr2, equivalence_arriere(inst2))       # z∈C2
    # décharger body_pr, ∃-éliminer r puis p (z∈C2 sans p,r libres → propre)
    elim_pr = existe_elimination(existe_elimination(
        N.loi_deduction(body_pr, z_in_C2), "r"), "p")        # (∃p)(∃r)body_pr ⇒ z∈C2

    # ── recoller : z∈C1 ⇒ (∃p)(∃r)body_pr [inst1] ⇒ z∈C2 ────────────────────────
    h_z = N.assume(appartient(vz, C1))
    z_c2 = N.modus_ponens(N.modus_ponens(h_z, equivalence_avant(inst1)), elim_pr)
    imp = N.loi_deduction(appartient(vz, C1), z_c2)          # {h1,h1p} ⊢ (z∈C1 ⇒ z∈C2)
    return N.generalisation("z", imp)                        # {h1,h1p} ⊢ G1'∘G1 ⊂ G2'∘G2


def composee_monotone_cible(g1="G1", g1p="G1p", g2="G2", g2p="G2p"):
    """Énoncé visé : G1'∘G1 ⊂ G2'∘G2  (pour vérification stricte)."""
    vG1, vG1p, vG2, vG2p = _tc(g1), _tc(g1p), _tc(g2), _tc(g2p)
    return inclus(E.composee(vG1p, vG1), E.composee(vG2p, vG2))


__all__ = ["composee_monotone", "composee_monotone_cible"]
