"""§II.3.3 — Composée de deux graphes : G'∘G et son théorème caractéristique.

⊢ ((x,z) ∈ G'∘G) ⇔ (∃y)((x,y)∈G et (y,z)∈G')  — base de la composition des
correspondances et des fonctions.
"""
from __future__ import annotations

from formule import var, egal, et, appartient, existe, subst_f
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_transitivite, equivalence_symetrie,
                               assoc_et, et_congruence_droite, et_congruence_gauche, instancie)
from tactiques_abrege_egalite import symetrie
from tactiques_abrege_quantif import (existe_elimination, congruence_existe,
                                      et_existe_droite, et_existe_gauche, existe_commute,
                                      alpha_existe)
from ensembles_couples import couple_egal_implique_composantes
from ensembles_correspondances import _inst_image
from ensembles_theoremes import egalite_par_extension


def _inst_composee(gp, g, w):
    """⊢ (w ∈ G'∘G) ⇔ (∃p)(∃r)(w=(p,r) et (∃y)((p,y)∈G et (y,r)∈G'))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    return instancie(instancie(instancie(ax, gp), g), w)


def couple_composee(gp="Gp", g="G", x="x", z="z"):
    """⊢ ((x,z) ∈ G'∘G) ⇔ (∃y)((x,y)∈G et (y,z)∈G').   (x, z distincts de p, r, y.)"""
    vGp, vG, vx, vz = var(gp), var(g), var(x), var(z)
    vp, vr, vy = var("p"), var("r"), var("y")
    inst = _inst_composee(vGp, vG, E.couple(vx, vz))
    phi = lambda pp, rr: existe("y", et(appartient(E.couple(pp, vy), vG),
                                        appartient(E.couple(vy, rr), vGp)))
    body = et(egal(E.couple(vx, vz), E.couple(vp, vr)), phi(vp, vr))

    # ── ⇒ : (∃p)(∃r)body ⇒ Φ(x,z) ──────────────────────────────────────────────
    hb = N.assume(body)
    comps = N.modus_ponens(conjonction_elim_gauche(hb),
                           couple_egal_implique_composantes(x, z, "p", "r"))   # x=p et z=r
    px = N.modus_ponens(conjonction_elim_gauche(comps), symetrie(vx, vp))      # p=x
    rz = N.modus_ponens(conjonction_elim_droite(comps), symetrie(vz, vr))      # r=z
    phi_xr = N.modus_ponens(conjonction_elim_droite(hb),
                            equivalence_avant(N.modus_ponens(px, N.s6(vp, vx, "p", phi(vp, vr)))))
    phi_xz = N.modus_ponens(phi_xr,
                            equivalence_avant(N.modus_ponens(rz, N.s6(vr, vz, "r", phi(vx, vr)))))
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, phi_xz), "r"), "p")

    # ── ⇐ : Φ(x,z) ⇒ (∃p)(∃r)body ──────────────────────────────────────────────
    h = N.assume(phi(vx, vz))
    wit = conjonction_intro(N.reflexivite(E.couple(vx, vz)), h)   # (x,z)=(x,z) et Φ(x,z)
    gbody = subst_f(vx, "p", body)
    full = N.modus_ponens(N.modus_ponens(wit, N.s5(gbody, vz, "r")),
                          N.s5(existe("r", body), vx, "p"))
    arriere = N.loi_deduction(phi(vx, vz), full)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def image_composee(gp="Gp", g="G", aa="A"):
    """⊢ (G'∘G)⟨A⟩ = G'⟨G⟨A⟩⟩.   (Proposition 5, E.II.42 ; réagencement C33.)

    Le liant interne « x » de l'axiome image est contourné par alpha_existe
    (on renomme l'existentielle externe en « y » avant d'expanser y∈G⟨A⟩)."""
    vGp, vG, vA = var(gp), var(g), var(aa)
    vx, vy, vz = var("x"), var("y"), var("z")
    comp = E.composee(vGp, vG)
    xA = appartient(vx, vA)
    phiG = appartient(E.couple(vx, vy), vG)            # (x,y)∈G
    phiGp = appartient(E.couple(vy, vz), vGp)          # (y,z)∈G'

    # thm_v : z ∈ G'⟨G⟨A⟩⟩ ⇔ R(z),  R(z) = (∃y)((∃x)(x∈A et (x,y)∈G) et (y,z)∈G')
    iv = _inst_image(vGp, E.image(vG, vA), vz)         # ⇔ (∃x)(x∈G⟨A⟩ et (x,z)∈G')   [liant x]
    rn = alpha_existe("x", "y", et(appartient(vx, E.image(vG, vA)),
                                   appartient(E.couple(vx, vz), vGp)))   # renomme x→y
    exp = et_congruence_gauche(_inst_image(vG, vA, vy), phiGp)           # y∈G⟨A⟩ → (∃x)(x∈A et (x,y)∈G)
    ev = equivalence_transitivite(iv, equivalence_transitivite(rn, congruence_existe(exp, "y")))
    thm_v = N.generalisation("z", ev)

    # thm_u : z ∈ (G'∘G)⟨A⟩ ⇔ R(z)
    iu = equivalence_transitivite(
        _inst_image(comp, vA, vz),                     # ⇔ (∃x)(x∈A et (x,z)∈G'∘G)
        congruence_existe(et_congruence_droite(xA, couple_composee(gp, g, "x", "z")), "x"))
    rd = congruence_existe(et_existe_droite(xA, "y", et(phiG, phiGp)), "x")
    ra = congruence_existe(congruence_existe(assoc_et(xA, phiG, phiGp), "y"), "x")
    rc = existe_commute("x", "y", et(et(xA, phiG), phiGp))
    reg = congruence_existe(equivalence_symetrie(et_existe_gauche("x", et(xA, phiG), phiGp)), "y")
    full = equivalence_transitivite(iu, equivalence_transitivite(
        rd, equivalence_transitivite(ra, equivalence_transitivite(rc, reg))))
    thm_u = N.generalisation("z", full)

    return egalite_par_extension(thm_u, thm_v, E.image(comp, vA), E.image(vGp, E.image(vG, vA)))


__all__ = ["couple_composee", "image_composee"]
