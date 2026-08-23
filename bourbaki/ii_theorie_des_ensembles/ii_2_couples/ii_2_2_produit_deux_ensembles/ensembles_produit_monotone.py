# -*- coding: utf-8 -*-
"""§II.2.2 — MONOTONIE DU PRODUIT POUR L'INCLUSION.

🎯 CIBLE :

    produit_monotone_carre : { A ⊂ B } ⊢ A×A ⊂ B×B

Un point de A×A s'écrit (p,q) avec p, q ∈ A ; l'inclusion les envoie dans B,
et le même couple témoigne alors de l'appartenance à B×B.

Écrit pour la donnée (9) du recollement de Hessenberg — dom(⋃𝔇) ⊂ US×US passe
par pr₁u×pr₁u ⊂ US×US — mais l'énoncé est général et sa place est ici, au
chapitre du produit, non dans la machinerie du §III.6.

⚠️ Les liants « p » et « q » sont LUS sur l'axiome du produit, jamais
reconstruits : c'est la précaution qui protège des renommages (LEÇON 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _membre_produit(vX, vY, vz):
    """⊢ ( z ∈ X×Y ) ⇔ (∃p)(∃q)( (z=(p,q) et p∈X) et q∈Y )."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, vX), vY), vz)


# @livre Ch.II §2.2 Prop.- | E II.33 L.12-16 | PDF p.84  (le produit est croissant pour ⊂)
def produit_monotone_carre(A="Apm", B="Bpm", z="zpm"):
    """🎯 { A ⊂ B } ⊢ A×A ⊂ B×B.   [1 hyp honnête].

    Point à point : z ∈ A×A fournit p, q ∈ A avec z = (p,q) ; l'inclusion les
    place dans B, et le MÊME couple témoigne de z ∈ B×B."""
    vA, vB, vz = _t(A), _t(B), var(z)
    h_inc = N.assume(inclus(vA, vB))

    depart = _membre_produit(vA, vA, vz)
    arrivee = _membre_produit(vB, vB, vz)
    ex_p = N.modus_ponens(N.assume(appartient(vz, E.produit(vA, vA))),
                          equivalence_avant(depart))
    np, corps_p = ex_p.conclusion.lieur, ex_p.conclusion.sous[0]
    nq, corps = corps_p.lieur, corps_p.sous[0]
    vp, vq = var(np), var(nq)

    #  cible : le corps de l'∃∃ du produit sur B, LU sur l'axiome d'arrivée
    but_pp = N.modus_ponens(N.assume(appartient(vz, E.produit(vB, vB))),
                            equivalence_avant(arrivee)).conclusion
    corps_but = but_pp.sous[0].sous[0]

    h = N.assume(corps)
    eq_z = conjonction_elim_gauche(conjonction_elim_gauche(h))     # z = (p,q)
    p_in_B = N.modus_ponens(conjonction_elim_droite(conjonction_elim_gauche(h)),
                            instancie(h_inc, vp))
    q_in_B = N.modus_ponens(conjonction_elim_droite(h), instancie(h_inc, vq))
    refait = conjonction_intro(conjonction_intro(eq_z, p_in_B), q_in_B)
    assert refait.conclusion == corps_but, "produit_monotone_carre : corps cible"

    ex_q_but = N.modus_ponens(refait, N.s5(corps_but, vq, nq))
    ex_pq_but = N.modus_ponens(ex_q_but, N.s5(but_pp.sous[0], vp, np))
    dans_BB = N.modus_ponens(ex_pq_but, equivalence_arriere(arrivee))

    imp_q = existe_elimination(N.loi_deduction(corps, dans_BB), nq)
    etape = N.modus_ponens(N.assume(corps_p), imp_q)
    imp_p = existe_elimination(N.loi_deduction(corps_p, etape), np)
    sortie = N.modus_ponens(ex_p, imp_p)
    res = N.generalisation(z, N.loi_deduction(
        appartient(vz, E.produit(vA, vA)), sortie))

    assert res.conclusion == inclus(E.produit(vA, vA), E.produit(vB, vB), z), \
        "produit_monotone_carre : forme"
    assert list(res.hypotheses) == [inclus(vA, vB)], "produit_monotone_carre : hyps"
    return res


__all__ = ["produit_monotone_carre"]
