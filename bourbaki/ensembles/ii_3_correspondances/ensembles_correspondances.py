"""§II.3 — Correspondances : graphes, projections (domaine/image), image directe.

Termes définis (dom, img, image) avec axiomes caractérisants (légitimés par S8 +
extensionnalité, comme produit). Premiers théorèmes : image croissante (Prop. 2),
G⟨∅⟩=∅, G⟨X⟩ ⊂ pr₂G.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, non, impl, appartient, existe, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, instancie, contraposition,
                               projection_gauche, projection_droite, dni)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import monotonie_existe, existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import vide_sans_element, appartient_singleton
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _inst_img(g, y):
    """⊢ (y ∈ pr₂G) ⇔ (∃x)((x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


# @livre Ch.II §3.1 Prop.2 | E II.10 L.38-39 | PDF p.61
def image_croissante(g="G", xx="X", yy="Y"):
    """⊢ (X ⊂ Y) ⇒ (G⟨X⟩ ⊂ G⟨Y⟩).   (Proposition 2, E.II.40.)"""
    vG, vX, vY, vx, vz = var(g), var(xx), var(yy), var("x"), var("z")
    h = N.assume(inclus(vX, vY))
    xX_xY = instancie(h, vx)                                  # x∈X ⇒ x∈Y
    ante = et(appartient(vx, vX), appartient(E.couple(vx, vz), vG))
    ha = N.assume(ante)
    conc = conjonction_intro(N.modus_ponens(conjonction_elim_gauche(ha), xX_xY),
                             conjonction_elim_droite(ha))      # x∈Y et (x,z)∈G
    inner = N.loi_deduction(ante, conc)
    mono = monotonie_existe(inner, "x")                       # (∃x …X) ⇒ (∃x …Y)
    z_imp = syllogisme(equivalence_avant(_inst_image(vG, vX, vz)),
                       syllogisme(mono, equivalence_arriere(_inst_image(vG, vY, vz))))
    return N.loi_deduction(inclus(vX, vY), N.generalisation("z", z_imp))


# @livre Ch.II §3.1 Rem.- | E II.10 L.34-35 | PDF p.61
def image_dans_img(g="G", xx="X"):
    """⊢ G⟨X⟩ ⊂ pr₂G.   (toute image directe est incluse dans l'ensemble des valeurs.)"""
    vG, vX, vx, vz = var(g), var(xx), var("x"), var("z")
    proj = projection_droite(appartient(vx, vX), appartient(E.couple(vx, vz), vG))  # (x∈X et (x,z)∈G)⇒(x,z)∈G
    mono = monotonie_existe(proj, "x")                        # (∃x …X) ⇒ (∃x (x,z)∈G)
    z_imp = syllogisme(equivalence_avant(_inst_image(vG, vX, vz)),
                       syllogisme(mono, equivalence_arriere(_inst_img(vG, vz))))
    return N.generalisation("z", z_imp)                       # G⟨X⟩ ⊂ pr₂G


# @livre Ch.II §3.1 Rem.- | E II.10 L.36 | PDF p.61
def image_vide(g="G"):
    """⊢ G⟨∅⟩ = ∅.   (l'image directe de l'ensemble vide est vide.)"""
    vG, vx, vz = var(g), var("x"), var("z")
    r = et(appartient(vx, E.VIDE), appartient(E.couple(vx, vz), vG))   # x∈∅ et (x,z)∈G
    n_r = N.modus_ponens(vide_sans_element("x"),
                         contraposition(projection_gauche(appartient(vx, E.VIDE),
                                                          appartient(E.couple(vx, vz), vG))))  # ¬r
    n_ex = N.modus_ponens(N.generalisation("x", n_r), contraposition(monotonie_existe(dni(r), "x")))
    #   (∀x)¬r = ¬(∃x)¬¬r ;  (∃x)r⇒(∃x)¬¬r (dni) ; contrapose ⇒ ¬(∃x)¬¬r⇒¬(∃x)r ; mp ⇒ ¬(∃x)r
    nz = N.modus_ponens(n_ex, contraposition(equivalence_avant(_inst_image(vG, E.VIDE, vz))))  # ¬(z∈G⟨∅⟩)
    return N.modus_ponens(N.generalisation("z", nz),
                          equivalence_arriere(vide_ssi_sans_element(E.image(vG, E.VIDE))))


# @livre Ch.II §3.1 Def.4 | E II.11 L.2-5 | PDF p.62
def coupe_membre(g="G", a="a"):
    """⊢ (y ∈ G⟨{a}⟩) ⇔ ((a,y) ∈ G).   (coupe suivant a, E.II.40 ; via C43/Leibniz.)"""
    vG, va, vx, vy = var(g), var(a), var("x"), var("y")
    inst = _inst_image(vG, E.singleton(va), vy)              # y∈G⟨{a}⟩ ⇔ (∃x)(x∈{a} et (x,y)∈G)
    body = et(appartient(vx, E.singleton(va)), appartient(E.couple(vx, vy), vG))
    # ── sens ⇒ : (∃x)(x∈{a} et (x,y)∈G) ⇒ (a,y)∈G ─────────────────────────────
    hb = N.assume(body)
    xeqa = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(singleton_membre(vx, va)))  # x=a
    ay_in = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(N.modus_ponens(
        xeqa, N.s6(vx, va, "w", appartient(E.couple(var("w"), vy), vG)))))   # (a,y)∈G
    avant = existe_elimination(N.loi_deduction(body, ay_in), "x")            # (∃x)…⇒(a,y)∈G
    # ── sens ⇐ : (a,y)∈G ⇒ (∃x)(x∈{a} et (x,y)∈G) ─────────────────────────────
    h = N.assume(appartient(E.couple(va, vy), vG))
    wit = conjonction_intro(appartient_singleton(a), h)      # a∈{a} et (a,y)∈G  = (a|x)body
    arriere = N.loi_deduction(appartient(E.couple(va, vy), vG),
                              N.modus_ponens(wit, N.s5(body, va, "x")))      # (a,y)∈G⇒(∃x)…
    eq_ex = conjonction_intro(avant, arriere)                # (∃x)… ⇔ (a,y)∈G
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_transitivite
    return equivalence_transitivite(inst, eq_ex)             # (y∈G⟨{a}⟩) ⇔ ((a,y)∈G)


__all__ = ["image_croissante", "image_dans_img", "image_vide", "coupe_membre"]
