"""Résumé §3 (E.R.13 item 4) — L'APPLICATION DIAGONALE x ↦ (x,x) : E ≅ Δ_E.

Bourbaki : « l'application diagonale x ↦ (x,x) est une bijection de E sur Δ »
(Δ = la diagonale de E×E).

Le graphe de l'application est D_E := graphe_terme(E, (x,x)) — miroir EXACT du
graphe x↦{x} du fichier Cantor voisin (mêmes lemmes C54, l'injectivité du
SINGLETON étant remplacée par celle du COUPLE, Prop. 1 §2).

DÉRIVÉ ici (theorie==22, rien postulé) :
  • diag_graphe_fonctionnel  : ⊢ D_E fonctionnel                      (CLOS)
  • diag_graphe_domaine      : ⊢ dom D_E = E                          (CLOS)
  • diag_graphe_valeur       : {u∈E} ⊢ D_E(u) = (u,u)
  • diag_graphe_injective    : ⊢ injective_dans(D_E, E)               (CLOS)
La SURJECTIVITÉ sur Δ_E (image(D_E,E) = Δ_E, par double inclusion via
AXIOME_IMAGE / AXIOME_DIAGONALE et egalite_par_extension) est l'étape
restante — consignée dans CAMPAGNE_DEMOS (suite du n°81).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, egal, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _T_diag():
    """Le terme T{x} = (x,x) de l'application diagonale."""
    return E.couple(var("x"), var("x"))


def diagonale_graphe(x="X"):
    """D_X := graphe_terme(X, (x,x)) = {(x,(x,x)) | x∈X}  (graphe de x↦(x,x))."""
    return E.graphe_terme(_t(x), _T_diag(), "x")


# @livre Ch.R §3 Prop.- | E.R.13 item 4 | PDF p.316  (l'application diagonale x↦(x,x) : fonctionnalité, domaine, valeur, INJECTIVITÉ — dérivées ; surjectivité sur Δ en cours)
# @livre Ch.R §3 Demo.- | E.R.13 item 4 | PDF p.316  (démo : lemmes C54 du kit graphe_terme + injectivité du couple, Prop.1 §2)
def diag_graphe_fonctionnel(x: str = "X"):
    """⊢ D_X est fonctionnel.   (cas T=(x,x) de C54.)"""
    return graphe_terme_fonctionnel(_t(x), _T_diag(), "x", "y")


def diag_graphe_domaine(x: str = "X"):
    """⊢ dom(D_X) = X.   (x↦(x,x) est définie sur tout X.)"""
    return graphe_terme_domaine(_t(x), _T_diag(), "x", "y", "z")


def diag_graphe_valeur(x: str = "X", u: str = "u"):
    """{u ∈ X} ⊢ D_X(u) = (u,u)."""
    return graphe_terme_valeur(_t(x), _T_diag(), u, "x", "y")


def diag_graphe_injective(x: str = "X"):
    """⊢ injective_dans(D_X, X).   ((u,u)=(u',u') ⇒ u=u', Prop.1 §2.)

    Miroir de singleton_graphe_injective (Cantor) : D(u)=(u,u) et D(u')=(u',u')
    par la valeur ; l'hypothèse D(u)=D(u') donne (u,u)=(u',u'), d'où u=u' par
    la première composante de couple_egal_implique_composantes."""
    vX, vu, vup = _t(x), var("u"), var("up")
    D = diagonale_graphe(x)
    cu, cup = E.couple(vu, vu), E.couple(vup, vup)
    hyp = et(et(appartient(vu, vX), appartient(vup, vX)),
             egal(E.valeur(D, vu), E.valeur(D, vup)))
    h = N.assume(hyp)
    uinX = conjonction_elim_gauche(conjonction_elim_gauche(h))       # u∈X
    upinX = conjonction_elim_droite(conjonction_elim_gauche(h))      # u'∈X
    val_eq = conjonction_elim_droite(h)                              # D(u)=D(u')
    du = N.modus_ponens(uinX, N.loi_deduction(appartient(vu, vX),
                                              diag_graphe_valeur(x, "u")))     # D(u)=(u,u)
    dup = N.modus_ponens(upinX, N.loi_deduction(appartient(vup, vX),
                                                diag_graphe_valeur(x, "up")))  # D(u')=(u',u')
    cu_du = N.modus_ponens(du, symetrie(E.valeur(D, vu), cu))        # (u,u)=D(u)
    cu_cup = composer_egalites(composer_egalites(cu_du, val_eq), dup)  # (u,u)=(u',u')
    comp = N.modus_ponens(cu_cup,
                          couple_egal_implique_composantes(vu, vu, vup, vup))
    u_up = conjonction_elim_gauche(comp)                             # u=u'
    inner = N.loi_deduction(hyp, u_up)
    res = N.generalisation("u", N.generalisation("up", inner))
    assert res.conclusion == E.injective_dans(D, vX), \
        "diag : conclusion ≠ injective_dans(D_X, X)"
    assert not res.hypotheses, "diag : hypothèses non déchargées"
    return res


def diag_graphe_surjective(x: str = "X"):
    """⊢ image(D_X, X) = Δ_X   (= est_surjective(D_X, X, diagonale(X))). CLOS.

    Double inclusion + extensionnalité A1 :
    ⊂ : z∈image ⇒ témoin u0 (AXIOME_IMAGE, α-renommé) ⇒ z=(u0,u0)
        (membre_graphe_terme) ⇒ z∈Δ (AXIOME_DIAGONALE, témoin u0) ;
    ⊃ : z∈Δ ⇒ témoin d0 ⇒ (d0,(d0,d0))∈D (graphe_terme_couple_dans) ⇒
        (d0,z)∈D (Leibniz z=(d0,d0)) ⇒ z∈image (AXIOME_IMAGE, témoin d0)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        impl, inclus, existe)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, equivalence_avant, equivalence_arriere, instancie)
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        existe_elimination, alpha_existe)
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
        extensionnalite_appliquee)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_couple_dans)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor import (
        ensembles_cantor as _cant)

    vX, vz = _t(x), var("z")
    D = diagonale_graphe(x)
    img = E.image(D, vX)
    Dg = E.diagonale(vX)
    T = _T_diag()

    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import subst_f

    ax_img = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE), D), vX), vz)
    # (z∈image) ⇔ (∃b)(b∈X et (b,z)∈D) — le binder est α-renommé par le noyau
    # (capture évitée : D contient « x » LIBRE comme paramètre C54) : on
    # l'extrait PROGRAMMATIQUEMENT de la conclusion plutôt que de le deviner.
    ax_diag = instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE), vX), vz)
    # (z∈Δ) ⇔ (∃d0)(d0∈X et z=(d0,d0))
    corps_diag_d0 = et(appartient(var("d0"), vX),
                       egal(vz, E.couple(var("d0"), var("d0"))))

    # ── ⊂ : image(D,X) ⊂ Δ_X ────────────────────────────────────────────────
    hz1 = N.assume(appartient(vz, img))
    ex_x = N.modus_ponens(hz1, equivalence_avant(ax_img))            # (∃b)(...)
    binder = ex_x.conclusion.lieur                                   # le binder réel (α)
    corps_b = ex_x.conclusion.sous[0]                                # corps avec var(binder)
    ex_u0 = N.modus_ponens(ex_x, equivalence_avant(
        alpha_existe(binder, "u0", corps_b)))                        # α : ∃u0(...)
    hu0 = N.assume(subst_f(var("u0"), binder, corps_b))
    u0X = conjonction_elim_gauche(hu0)
    u0zD = conjonction_elim_droite(hu0)
    car = _cant.membre_graphe_terme(vX, T, "u0", "v0", "x", "y")     # ((u0,v0)∈D)⇔(u0∈X et v0=(u0,u0))
    car_z = instancie(N.generalisation("v0", car), vz)               # ((u0,z)∈D)⇔(u0∈X et z=(u0,u0))
    z_eq = conjonction_elim_droite(N.modus_ponens(u0zD, equivalence_avant(car_z)))
    temoin_diag = conjonction_intro(u0X, z_eq)                       # u0∈X et z=(u0,u0)
    ex_d0 = N.modus_ponens(temoin_diag, N.s5(corps_diag_d0, var("u0"), "d0"))
    z_in_Dg = N.modus_ponens(ex_d0, equivalence_arriere(ax_diag))    # z∈Δ
    imp1 = N.loi_deduction(subst_f(var("u0"), binder, corps_b), z_in_Dg)
    c1 = N.modus_ponens(ex_u0, existe_elimination(imp1, "u0"))       # z∈Δ  [z∈img]
    incl1 = N.generalisation("z", N.loi_deduction(appartient(vz, img), c1))

    # ── ⊃ : Δ_X ⊂ image(D,X) ────────────────────────────────────────────────
    hz2 = N.assume(appartient(vz, Dg))
    ex_d = N.modus_ponens(hz2, equivalence_avant(ax_diag))           # ∃d0(...)
    hd0 = N.assume(et(appartient(var("d0"), vX),
                      egal(vz, E.couple(var("d0"), var("d0")))))
    d0X = conjonction_elim_gauche(hd0)
    z_eq2 = conjonction_elim_droite(hd0)                             # z=(d0,d0)
    cpl = N.modus_ponens(d0X, N.loi_deduction(appartient(var("d0"), vX),
        graphe_terme_couple_dans(vX, T, "d0", "x", "y")))            # (d0,(d0,d0))∈D
    leib = N.s6(vz, E.couple(var("d0"), var("d0")), "w81",
                appartient(E.couple(var("d0"), var("w81")), D))
    d0z_D = N.modus_ponens(cpl, equivalence_arriere(
        N.modus_ponens(z_eq2, leib)))                                # (d0,z)∈D
    temoin_img = conjonction_intro(d0X, d0z_D)                       # d0∈X et (d0,z)∈D
    ex_x2 = N.modus_ponens(temoin_img, N.s5(corps_b, var("d0"), binder))
    z_in_img = N.modus_ponens(ex_x2, equivalence_arriere(ax_img))    # z∈image
    imp2 = N.loi_deduction(et(appartient(var("d0"), vX),
                              egal(vz, E.couple(var("d0"), var("d0")))), z_in_img)
    c2 = N.modus_ponens(ex_d, existe_elimination(imp2, "d0"))        # z∈img  [z∈Δ]
    incl2 = N.generalisation("z", N.loi_deduction(appartient(vz, Dg), c2))

    # ── extensionnalité A1 ───────────────────────────────────────────────────
    res = N.modus_ponens(conjonction_intro(incl1, incl2),
                         extensionnalite_appliquee(img, Dg))         # image = Δ
    assert res.conclusion == E.est_surjective(D, vX, Dg), \
        "diag : conclusion ≠ est_surjective(D_X, X, Δ_X)"
    assert not res.hypotheses, "diag surjective : hypothèses non déchargées"
    return res


def diag_graphe_bijection(x: str = "X"):
    """🎯 ⊢ est_bijective(D_X, X, Δ_X).   (THÉORÈME CLOS, 0 hyp — E.R.13 item 4 :
    « l'application diagonale x↦(x,x) est une bijection de E sur Δ ».)"""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro)
    res = conjonction_intro(diag_graphe_injective(x), diag_graphe_surjective(x))
    assert res.conclusion == E.est_bijective(diagonale_graphe(x), _t(x),
                                             E.diagonale(_t(x))), \
        "diag : conclusion ≠ est_bijective(D_X, X, Δ_X)"
    assert not res.hypotheses, "diag bijection : hypothèses non déchargées"
    return res


__all__ = ["diagonale_graphe", "diag_graphe_fonctionnel", "diag_graphe_domaine",
           "diag_graphe_valeur", "diag_graphe_injective",
           "diag_graphe_surjective", "diag_graphe_bijection"]
