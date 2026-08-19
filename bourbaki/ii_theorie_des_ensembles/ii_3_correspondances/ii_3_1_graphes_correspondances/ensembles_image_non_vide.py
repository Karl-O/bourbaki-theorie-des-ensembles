"""Résumé §2 (E.R.8 item 5b) — X ≠ ∅ ⇔ f⟨X⟩ ≠ ∅. CLOS (1 hypothèse honnête).

Bourbaki (E.R.8, item 5 b) : « La propriété X ≠ ∅ est équivalente à
f(X) ≠ ∅ » — f application de E dans F, X partie de E.

DÉRIVÉ ici :   { X ⊂ dom f }  ⊢  ¬(X = ∅) ⇔ ¬(f⟨X⟩ = ∅)

L'hypothèse honnête est le cœur du « f application de E » du livre : tout
élément de X est dans l'ensemble de définition de f (la fonctionnalité de f
n'est même pas nécessaire pour la non-vacuité).

  (⇐)  CLOS sans hypothèse : (X=∅) ⇒ (f⟨X⟩=∅) par congruence + image_vide,
       puis contraposition.
  (⇒)  X≠∅ donne un témoin z∈X (non_vide_ssi_element) ; z∈dom f (hypothèse) ;
       AXIOME_DOM donne un y avec (z,y)∈f ; AXIOME_IMAGE (sens ⇐, témoin z)
       met y dans f⟨X⟩ ; d'où f⟨X⟩≠∅.  Les témoins sont déchargés par
       existe_elimination (aucune variable libre parasite dans Γ).

theorie_ensembles = 22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal, impl, appartient, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, contraposition, equivalence_avant, equivalence_arriere,
    instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    non_vide_ssi_element)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import (
    image_vide)


def image_non_vide_enonce(x: str = "X", f: str = "f"):
    """L'énoncé-cible :  ¬(X = ∅) ⇔ ¬(f⟨X⟩ = ∅)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vX, vf = var(x), var(f)
    return equiv(non(egal(vX, E.VIDE)), non(egal(E.image(vf, vX), E.VIDE)))


# @livre Ch.R §2 Prop.- | E.R.8 item 5b | PDF p.311  (X≠∅ ⇔ f⟨X⟩≠∅ — DÉRIVÉ, hyp honnête X ⊂ dom f)
# @livre Ch.R §2 Demo.- | E.R.8 item 5b | PDF p.311  (démo : témoin via AXIOME_DOM + AXIOME_IMAGE ; réciproque par congruence + image_vide + contraposition)
# @livre Ch.II §3.1 Prop.- | E II.10 L.37-37 | PDF p.61  (« Si X ⊂ pr₁ G et X ≠ ∅, on a G⟨X⟩ ≠ ∅ » — était marqué SEULEMENT sur le Résumé)
def image_non_vide(x: str = "X", f: str = "f"):
    """🎯 { X ⊂ dom f } ⊢ ¬(X=∅) ⇔ ¬(f⟨X⟩=∅).   [1 hypothèse HONNÊTE]"""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vX, vf = var(x), var(f)
    imgfX = E.image(vf, vX)
    domf = E.dom(vf)

    # ── (⇐) CLOS : (X=∅) ⇒ (f⟨X⟩=∅), puis contraposition ────────────────────
    h0 = N.assume(egal(vX, E.VIDE))
    eq1 = N.modus_ponens(h0, congruence_terme(vX, E.VIDE,
                                              E.image(vf, var("wnv")), "wnv"))
    fXv = composer_egalites(eq1, image_vide(f))          # {X=∅} ⊢ f⟨X⟩=∅
    th_g = N.loi_deduction(egal(vX, E.VIDE), fXv)        # ⊢ (X=∅)⇒(f⟨X⟩=∅)
    contrap_g = contraposition(th_g)                     # ⊢ ¬(f⟨X⟩=∅) ⇒ ¬(X=∅)

    # ── (⇒) { X⊂dom f } : ¬(X=∅) ⇒ ¬(f⟨X⟩=∅) ────────────────────────────────
    hincl = N.assume(inclus(vX, domf))                   # (∀z)((z∈X)⇒(z∈dom f))  [HONNÊTE]
    hne = N.assume(non(egal(vX, E.VIDE)))
    exz = N.modus_ponens(hne, equivalence_avant(non_vide_ssi_element(x)))  # (∃z)(z∈X)

    hz = N.assume(appartient(var("z"), vX))              # témoin z∈X
    zdom = N.modus_ponens(hz, instancie(hincl, var("z")))            # z∈dom f
    ax_dom = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM),
                                 vf), var("z"))          # (z∈dom f) ⇔ (∃y)((z,y)∈f)
    exy = N.modus_ponens(zdom, equivalence_avant(ax_dom))            # (∃y)((z,y)∈f)

    hy = N.assume(appartient(E.couple(var("z"), var("y")), vf))      # témoin (z,y)∈f
    temoin = conjonction_intro(hz, hy)                   # (z∈X) et ((z,y)∈f)
    corps = et(appartient(var("x"), vX),
               appartient(E.couple(var("x"), var("y")), vf))
    exx = N.modus_ponens(temoin, N.s5(corps, var("z"), "x"))         # (∃x)corps
    ax_im = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE), vf), vX), var("y"))
    y_in = N.modus_ponens(exx, equivalence_arriere(ax_im))           # y ∈ f⟨X⟩
    ex_el = N.modus_ponens(y_in, N.s5(appartient(var("z"), imgfX), var("y"), "z"))
    cible = N.modus_ponens(ex_el, equivalence_arriere(non_vide_ssi_element(imgfX)))
    # cible : ¬(f⟨X⟩=∅)   sous {hincl, hne, hz, hy}

    imp_y = N.loi_deduction(appartient(E.couple(var("z"), var("y")), vf), cible)
    c1 = N.modus_ponens(exy, existe_elimination(imp_y, "y"))         # décharge y
    imp_z = N.loi_deduction(appartient(var("z"), vX), c1)
    c2 = N.modus_ponens(exz, existe_elimination(imp_z, "z"))         # décharge z
    th_d = N.loi_deduction(non(egal(vX, E.VIDE)), c2)    # {hincl} ⊢ ¬(X=∅)⇒¬(f⟨X⟩=∅)

    res = conjonction_intro(th_d, contrap_g)             # ⇔
    assert res.conclusion == equiv(non(egal(vX, E.VIDE)),
                                   non(egal(imgfX, E.VIDE))), "5b : conclusion inattendue"
    assert res.hypotheses == frozenset({inclus(vX, domf)}), "5b : hypothèses ≠ {X⊂dom f}"
    return res


__all__ = ["image_non_vide"]
