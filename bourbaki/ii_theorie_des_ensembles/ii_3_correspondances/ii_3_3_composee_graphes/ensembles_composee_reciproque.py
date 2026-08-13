"""§II.3.3 — Réciproque d'une composée (Proposition 3, E.II.42).

⊢ (Gp∘G)⁻¹ = G⁻¹ ∘ Gp⁻¹  (reciproque(composee(Gp,G)) = composee(reciproque(G), reciproque(Gp))).

Preuve par extensionnalité (A1) : on caractérise les deux membres par la MÊME
relation
    R(w) = (∃a)(∃b)( w=(a,b) et (∃y)((b,y)∈G et (y,a)∈Gp) )
puis on conclut par egalite_par_extension.

Côté gauche  (AXIOME_RECIP + couple_composee) :
    w ∈ (Gp∘G)⁻¹ ⇔ (∃a)(∃b)( w=(a,b) et (b,a)∈Gp∘G )
                 ⇔ (∃a)(∃b)( w=(a,b) et (∃y)((b,y)∈G et (y,a)∈Gp) ) = R(w).
Côté droit  (AXIOME_COMPOSEE sur (G⁻¹, Gp⁻¹) + couple_reciproque ×2 + comm_et) :
    w ∈ G⁻¹∘Gp⁻¹ ⇔ (∃a)(∃b)( w=(a,b) et (∃y)((a,y)∈Gp⁻¹ et (y,b)∈G⁻¹) )
                 ⇔ (∃a)(∃b)( w=(a,b) et (∃y)((y,a)∈Gp et (b,y)∈G) )
                 ⇔ (∃a)(∃b)( w=(a,b) et (∃y)((b,y)∈G et (y,a)∈Gp) ) = R(w).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, existe
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, equivalence_transitivite,
                               et_congruence_droite, et_congruence_gauche, comm_et)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import congruence_existe, alpha_existe
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import couple_composee
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension


def _inst_recip(g, z):
    """⊢ (z ∈ G⁻¹) ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    return instancie(instancie(ax, g), z)


def _inst_composee(gp, g, w):
    """⊢ (w ∈ Gp∘G) ⇔ (∃p)(∃r)(w=(p,r) et (∃y)((p,y)∈G et (y,r)∈Gp))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    return instancie(instancie(instancie(ax, gp), g), w)


# @livre Ch.II §3.3 Prop.3 | E II.12 L.1-2 | PDF p.63
# @livre Ch.R §2 Prop.- | E.R.10 item 11 ((21) (g∘f)⁻¹(Z)=f⁻¹(g⁻¹(Z))) | PDF p.313
# @livre Ch.R §3 Prop.- | E.R.15 item 11 ((31) (B∘A)⁻¹=A⁻¹∘B⁻¹) | PDF p.318
def reciproque_composee(gp="Gp", g="G"):
    """⊢ (Gp∘G)⁻¹ = G⁻¹ ∘ Gp⁻¹.   (Proposition 3, E.II.42 ; SANS hypothèses.)"""
    vGp, vG = var(gp), var(g)
    vz, va, vb, vy = var("z"), var("a"), var("b"), var("y")
    comp = E.composee(vGp, vG)
    Grec, Gprec = E.reciproque(vG), E.reciproque(vGp)
    eq = egal(vz, E.couple(va, vb))                          # z = (a,b)   (coords a,b ≠ binders p,q,r,y)

    # ── char_L : (∀z)(z∈(Gp∘G)⁻¹ ⇔ R(z)) ───────────────────────────────────────
    recL = _inst_recip(comp, vz)                             # ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈Gp∘G)
    recL = equivalence_transitivite(recL,                    # α : p→a
        alpha_existe("p", "a", existe("q",
            et(egal(vz, E.couple(var("p"), var("q"))),
               appartient(E.couple(var("q"), var("p")), comp)))))
    recL = equivalence_transitivite(recL, congruence_existe( # α : q→b (sous a)
        alpha_existe("q", "b", et(egal(vz, E.couple(va, var("q"))),
            appartient(E.couple(var("q"), va), comp))), "a"))
    cc = couple_composee(gp, g, "b", "a")                    # ((b,a)∈Gp∘G) ⇔ (∃y)((b,y)∈G et (y,a)∈Gp)
    bodyL = et_congruence_droite(eq, cc)                     # (eq et (b,a)∈Gp∘G) ⇔ R-corps
    recL = equivalence_transitivite(recL,
        congruence_existe(congruence_existe(bodyL, "b"), "a"))
    char_L = N.generalisation("z", recL)

    # ── char_R : (∀z)(z∈G⁻¹∘Gp⁻¹ ⇔ R(z)) ───────────────────────────────────────
    compR = _inst_composee(Grec, Gprec, vz)                 # ⇔ (∃p)(∃r)(z=(p,r) et (∃y)((p,y)∈Gp⁻¹ et (y,r)∈G⁻¹))
    compR = equivalence_transitivite(compR,                 # α : p→a
        alpha_existe("p", "a", existe("r",
            et(egal(vz, E.couple(var("p"), var("r"))),
               existe("y", et(appartient(E.couple(var("p"), vy), Gprec),
                              appartient(E.couple(vy, var("r")), Grec)))))))
    compR = equivalence_transitivite(compR, congruence_existe(  # α : r→b (sous a)
        alpha_existe("r", "b", et(egal(vz, E.couple(va, var("r"))),
            existe("y", et(appartient(E.couple(va, vy), Gprec),
                           appartient(E.couple(vy, var("r")), Grec))))), "a"))

    # inner : ((a,y)∈Gp⁻¹ et (y,b)∈G⁻¹) ⇔ ((b,y)∈G et (y,a)∈Gp)
    yb_G  = appartient(E.couple(vy, vb), Grec)
    ya_Gp = appartient(E.couple(vy, va), vGp)
    by_G  = appartient(E.couple(vb, vy), vG)
    crL = couple_reciproque(gp, "a", "y")                   # (a,y)∈Gp⁻¹ ⇔ (y,a)∈Gp
    crR = couple_reciproque(g, "y", "b")                    # (y,b)∈G⁻¹ ⇔ (b,y)∈G
    inner = equivalence_transitivite(
        et_congruence_gauche(crL, yb_G),                    # → ((y,a)∈Gp et (y,b)∈G⁻¹)
        equivalence_transitivite(
            et_congruence_droite(ya_Gp, crR),               # → ((y,a)∈Gp et (b,y)∈G)
            comm_et(ya_Gp, by_G)))                          # → ((b,y)∈G et (y,a)∈Gp)
    bodyR = et_congruence_droite(eq, congruence_existe(inner, "y"))
    compR = equivalence_transitivite(compR,
        congruence_existe(congruence_existe(bodyR, "b"), "a"))
    char_R = N.generalisation("z", compR)

    return egalite_par_extension(char_L, char_R, E.reciproque(comp),
                                 E.composee(Grec, Gprec))


__all__ = ["reciproque_composee"]
