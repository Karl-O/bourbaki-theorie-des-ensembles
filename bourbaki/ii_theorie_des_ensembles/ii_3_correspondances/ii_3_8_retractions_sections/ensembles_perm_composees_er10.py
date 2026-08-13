"""Résumé E.R.10-11 item 12 — permutations composées ⇒ facteurs bijectifs (n°79).

Bourbaki (E.R.10-11, item 12) : « si g∘f est une permutation de E et f∘g une
permutation de F, alors f et g sont bijectives ».  (f : E→F, g : F→E applications.)

ÉNONCÉ DÉRIVÉ (CLOS, 0 hypothèse) :

    ⊢ (  est_application(F,E,Ff) et est_application(G,Ff,E)
         et est_permutation(G∘F, E) et est_permutation(F∘G, Ff)  )
      ⇒ ( est_bijective(F,E,Ff) et est_bijective(G,Ff,E) )

DÉMONSTRATION (assemblage des deux converses de facteur, §II.3.8 valeurs) :
  · f injective  ← g∘f injective [permutation]   via injective_facteur_droit (facteur intérieur) ;
  · f surjective ← f∘g surjective [permutation]   via surjective_facteur_gauche (facteur extérieur) ;
  · g injective  ← f∘g injective [permutation]   via injective_facteur_droit ;
  · g surjective ← g∘f surjective [permutation]  via surjective_facteur_gauche.
Les deux converses ne portent que les deux hypothèses d'application, déchargées ici
depuis l'antécédent.  est_bijective = injective_dans ∧ est_surjective.

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions_complements import est_permutation
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    injective_facteur_droit, surjective_facteur_gauche)


def _cut(thm, preuve_hyp):
    """Décharge de `thm` l'hypothèse H = preuve_hyp.conclusion (coupure)."""
    H = preuve_hyp.conclusion
    return N.modus_ponens(preuve_hyp, N.loi_deduction(H, thm))


def enonce_perm_composees_bijectives(f="F", g="G", e="E", ff="Ff"):
    vf, vg, vE, vFf = var(f), var(g), var(e), var(ff)
    gf, fg = E.composee(vg, vf), E.composee(vf, vg)          # g∘f, f∘g
    ante = et(et(et(est_application(vf, vE, vFf), est_application(vg, vFf, vE)),
                  est_permutation(gf, vE)), est_permutation(fg, vFf))
    cons = et(E.est_bijective(vf, vE, vFf), E.est_bijective(vg, vFf, vE))
    return impl(ante, cons)


# @livre Ch.R §2 Prop.- | E.R.10-11 item 12 | PDF p.313  (g∘f perm E, f∘g perm F ⇒ f,g bijectives)
# @livre Ch.R §2 Demo.- | E.R.10-11 item 12 | PDF p.313  (démo : converses de facteur inj/surj)
def perm_composees_bijectives(f="F", g="G", e="E", ff="Ff"):
    """🎯 ⊢ (g∘f perm E et f∘g perm F) ⇒ (f et g bijectives).   (E.R.10-11 item 12, n°79.)"""
    vf, vg, vE, vFf = var(f), var(g), var(e), var(ff)
    gf, fg = E.composee(vg, vf), E.composee(vf, vg)          # g∘f, f∘g
    ante = et(et(et(est_application(vf, vE, vFf), est_application(vg, vFf, vE)),
                  est_permutation(gf, vE)), est_permutation(fg, vFf))
    h = N.assume(ante)
    appF = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # est_application(F,E,Ff)
    appG = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # est_application(G,Ff,E)
    perm_gf = conjonction_elim_droite(conjonction_elim_gauche(h))       # est_permutation(g∘f,E)
    perm_fg = conjonction_elim_droite(h)                               # est_permutation(f∘g,Ff)

    inj_gf = conjonction_elim_gauche(perm_gf)     # injective_dans(g∘f,E)
    surj_gf = conjonction_elim_droite(perm_gf)    # est_surjective(g∘f,E,E)
    inj_fg = conjonction_elim_gauche(perm_fg)     # injective_dans(f∘g,Ff)
    surj_fg = conjonction_elim_droite(perm_fg)    # est_surjective(f∘g,Ff,Ff)

    # les quatre converses (chacune {est_application(F,E,Ff), est_application(G,Ff,E)})
    f_inj = N.modus_ponens(inj_gf, injective_facteur_droit(g, f, e, ff, e))    # inj(F,E)
    f_surj = N.modus_ponens(surj_fg, surjective_facteur_gauche(f, g, e, ff))   # surj(F,E,Ff)
    g_inj = N.modus_ponens(inj_fg, injective_facteur_droit(f, g, ff, e, ff))   # inj(G,Ff)
    g_surj = N.modus_ponens(surj_gf, surjective_facteur_gauche(g, f, ff, e))   # surj(G,Ff,E)

    cons = conjonction_intro(conjonction_intro(f_inj, f_surj),
                             conjonction_intro(g_inj, g_surj))   # bij(F) et bij(G) ; hyps {h, appF, appG}
    cons = _cut(cons, appF)                                      # décharge est_application(F,E,Ff)
    cons = _cut(cons, appG)                                      # décharge est_application(G,Ff,E)  → {h}
    res = N.loi_deduction(ante, cons)
    assert res.conclusion == enonce_perm_composees_bijectives(f, g, e, ff), \
        "perm_composees_bijectives : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_perm_composees_bijectives", "perm_composees_bijectives"]
