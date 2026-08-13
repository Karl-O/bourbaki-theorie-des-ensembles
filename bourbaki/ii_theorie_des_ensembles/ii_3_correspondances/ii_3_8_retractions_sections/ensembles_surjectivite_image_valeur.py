"""§II.3 — Pont SURJECTIVITÉ image ↔ valeur :  y∈f⟨A⟩ ⇒ (∃x∈A) y=f(x).

Le « pont surjectivité↔image » signalé REPORTÉ dans plusieurs modules
(`ensembles_retractions_props.theoreme1_d_surjective_valeur`, la construction de
section `section_construite_par_tau` qui consomme la forme VALEUR) : passer de la
surjectivité au niveau IMAGE (f⟨A⟩ = B, i.e. AXIOME_IMAGE) à la forme VALEUR
« tout y de l'image est une valeur f(x) avec x∈A ».  On certifie, pour f fonctionnel :

    ⊢ est_fonctionnel(f) ⇒ (∀y)(y∈f⟨A⟩ ⇒ (∃x)(x∈A et y=f(x))).

PREUVE.  y∈image(f,A) ⇔ (∃x)(x∈A et (x,y)∈f)  [AXIOME_IMAGE, `membre_image`, liant « x »].
Pour un tel x : (x,y)∈f + f fonctionnel ⇒ y=f(x)  [`valeur_caracterisation`, C46 ; on
décharge son hypothèse (∃y)((x,y)∈f) par S5 depuis (x,y)∈f].  D'où (∃x)(x∈A et y=f(x)).
INCONDITIONNEL au-delà de est_fonctionnel(f) (pas besoin de dom f=A : l'appartenance
x∈A vient directement de AXIOME_IMAGE).

C'est la brique qui manquait pour appliquer `section_construite_par_tau` à une f
surjective donnée sous forme image (f⟨A⟩=B).  Rien postulé ; theorie_ensembles
INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, impl, pourtout, existe)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §3.8 Th.1 | E II.19 L.20-21 (pont surjectivité↔image, sens valeur) | PDF p.70
def surjective_image_donne_valeur(f="F", a="A"):
    """⊢ est_fonctionnel(f) ⇒ (∀y)(y∈f⟨A⟩ ⇒ (∃x)(x∈A et y=f(x))).

    Pont image→valeur : tout élément de l'image directe f⟨A⟩ est une valeur f(x)
    d'un x∈A (f fonctionnel).  Décharge le « pont surjectivité↔image » REPORTÉ."""
    vf, vA = _t(f), _t(a)
    vy, vx = var("y"), var("x")
    img = E.image(vf, vA)

    hfunc = N.assume(E.est_fonctionnel(vf))
    hy = N.assume(appartient(vy, img))
    ex = N.modus_ponens(hy, equivalence_avant(membre_image(vf, vA, vy)))  # ∃x(x∈A et (x,y)∈f)

    body_img = et(appartient(vx, vA), appartient(E.couple(vx, vy), vf))
    hb = N.assume(body_img)
    xA = conjonction_elim_gauche(hb)                                       # x∈A
    xy_f = conjonction_elim_droite(hb)                                     # (x,y)∈f

    # y = f(x)  via valeur_caracterisation (décharge son hyp (∃y)((x,y)∈f))
    ex_couple = existe("y", appartient(E.couple(vx, var("y")), vf))
    y_from = N.modus_ponens(xy_f, N.s5(appartient(E.couple(vx, var("y")), vf), vy, "y"))  # ∃y((x,y)∈f)
    y_eq_fx0 = N.modus_ponens(xy_f, equivalence_avant(valeur_caracterisation(vf, vx)))    # y=f(x) {func,∃y}
    y_eq_fx = N.modus_ponens(y_from, N.loi_deduction(ex_couple, y_eq_fx0))                # y=f(x) {func}

    res_body = et(appartient(vx, vA), egal(vy, E.valeur(vf, vx)))
    ex_res = N.modus_ponens(conjonction_intro(xA, y_eq_fx), N.s5(res_body, vx, "x"))      # ∃x(x∈A et y=f(x))
    got = N.modus_ponens(ex, existe_elimination(N.loi_deduction(body_img, ex_res), "x"))
    gen = N.generalisation("y", N.loi_deduction(appartient(vy, img), got))
    return N.loi_deduction(E.est_fonctionnel(vf), gen)


def cible_surjective_image_donne_valeur(f="F", a="A"):
    """Cible exacte : est_fonctionnel(f) ⇒ (∀y)(y∈f⟨A⟩ ⇒ (∃x)(x∈A et y=f(x)))."""
    vf, vA = _t(f), _t(a)
    vy, vx = var("y"), var("x")
    return impl(E.est_fonctionnel(vf),
                pourtout("y", impl(appartient(vy, E.image(vf, vA)),
                                   existe("x", et(appartient(vx, vA), egal(vy, E.valeur(vf, vx)))))))


__all__ = ["surjective_image_donne_valeur", "cible_surjective_image_donne_valeur"]
