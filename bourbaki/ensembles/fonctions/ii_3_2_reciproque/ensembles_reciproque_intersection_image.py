"""Résumé §2 item 7 — Formule (17) : f⁻¹⟨Y⟩ = f⁻¹⟨Y ∩ img f⟩.

Bourbaki (E.R.9) : pour une application f, f⁻¹(Y) = f⁻¹(Y ∩ f(E)).  Ici f⁻¹⟨Y⟩ =
image(reciproque(f), Y) (E.II.41) et img f = pr₂⟨f⟩ = f⟨E⟩ (l'ensemble des valeurs,
= f(E) quand E = dom f).  L'égalité est INCONDITIONNELLE : intersecter par img f ne
retire aucun antécédent, car tout couple (x,z)∈f⁻¹ (i.e. (z,x)∈f) a sa cible x∈img f.

  z∈f⁻¹⟨Y⟩ ⇔ (∃x)(x∈Y et (x,z)∈f⁻¹)                 [membre_image_reciproque]
  (x,z)∈f⁻¹ ⇔ (z,x)∈f  [couple_reciproque]  ⇒  x∈img f  [couple_dans_img]
  donc x∈Y ⇔ x∈Y∩img f (sous (x,z)∈f⁻¹) : les deux réciproques coïncident.

Preuve par double inclusion + extensionnalité (A1).  Rien postulé ;
theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_extensionnalite import couple_dans_dom
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import pr1_reciproque
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image_reciproque)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B).   (instance de AXIOME_INTER.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


# @livre Ch.R §2 Prop.- | E.R.9 item 7 ((17) f⁻¹(Y)=f⁻¹(Y∩f(E))) | PDF p.313
def reciproque_intersection_image(f="f", y="Y"):
    """⊢ f⁻¹⟨Y⟩ = f⁻¹⟨Y ∩ img f⟩.   (formule (17), version img f = f⟨E⟩ ; inconditionnel.)"""
    vf, vY, vz, vx = _t(f), _t(y), var("z"), var("x")
    Recip, imgf = E.reciproque(vf), E.img(vf)
    Yi = E.intersection(vY, imgf)
    frecY, frecYi = E.image(Recip, vY), E.image(Recip, Yi)

    mY = membre_image_reciproque(vf, vY, vz)      # z∈f⁻¹⟨Y⟩ ⇔ (∃x)(x∈Y et (x,z)∈f⁻¹)
    mYi = membre_image_reciproque(vf, Yi, vz)     # z∈f⁻¹⟨Y∩img f⟩ ⇔ (∃x)(x∈Y∩img f et (x,z)∈f⁻¹)
    body_Y = et(appartient(vx, vY), appartient(E.couple(vx, vz), Recip))
    body_Yi = et(appartient(vx, Yi), appartient(E.couple(vx, vz), Recip))

    # ── f⁻¹⟨Y⟩ ⊂ f⁻¹⟨Y∩img f⟩ ──
    hb = N.assume(body_Y)
    xzR = conjonction_elim_droite(hb)             # (x,z)∈f⁻¹
    xdom = N.modus_ponens(xzR, N.loi_deduction(   # x∈dom(f⁻¹)  (1ʳᵉ coord. d'un couple)
        appartient(E.couple(vx, vz), Recip), couple_dans_dom(Recip, vx, vz)))
    leib = N.s6(E.dom(Recip), imgf, "w", appartient(vx, var("w")))   # dom(f⁻¹)=img f ⇒ (x∈dom f⁻¹ ⇔ x∈img f)
    ximg = N.modus_ponens(xdom, equivalence_avant(N.modus_ponens(pr1_reciproque(vf), leib)))  # x∈img f
    xYi = N.modus_ponens(conjonction_intro(conjonction_elim_gauche(hb), ximg),
                         equivalence_arriere(_inst_inter(vY, imgf, vx)))          # x∈Y∩img f
    exi = N.modus_ponens(conjonction_intro(xYi, xzR), N.s5(body_Yi, vx, "x"))
    aYi = N.modus_ponens(exi, equivalence_arriere(mYi))                           # z∈f⁻¹⟨Y∩img f⟩
    elim1 = existe_elimination(N.loi_deduction(body_Y, aYi), "x")
    z_in_Yi = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, frecY)),
                                            equivalence_avant(mY)), elim1)
    incl1 = N.generalisation("z", N.loi_deduction(appartient(vz, frecY), z_in_Yi))

    # ── f⁻¹⟨Y∩img f⟩ ⊂ f⁻¹⟨Y⟩  (Y∩img f ⊂ Y) ──
    hb2 = N.assume(body_Yi)
    xzR2 = conjonction_elim_droite(hb2)           # (x,z)∈f⁻¹
    xY2 = conjonction_elim_gauche(N.modus_ponens(conjonction_elim_gauche(hb2),
                                                 equivalence_avant(_inst_inter(vY, imgf, vx))))  # x∈Y
    exY = N.modus_ponens(conjonction_intro(xY2, xzR2), N.s5(body_Y, vx, "x"))
    aY = N.modus_ponens(exY, equivalence_arriere(mY))                            # z∈f⁻¹⟨Y⟩
    elim2 = existe_elimination(N.loi_deduction(body_Yi, aY), "x")
    z_in_Y = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, frecYi)),
                                           equivalence_avant(mYi)), elim2)
    incl2 = N.generalisation("z", N.loi_deduction(appartient(vz, frecYi), z_in_Y))

    return N.modus_ponens(conjonction_intro(incl1, incl2),
                          extensionnalite_appliquee(frecY, frecYi))


def cible_reciproque_intersection_image(f="f", y="Y"):
    """Conclusion exacte : f⁻¹⟨Y⟩ = f⁻¹⟨Y ∩ img f⟩."""
    vf, vY = _t(f), _t(y)
    Recip = E.reciproque(vf)
    return egal(E.image(Recip, vY),
                E.image(Recip, E.intersection(vY, E.img(vf))))


__all__ = ["reciproque_intersection_image", "cible_reciproque_intersection_image"]
