"""Résumé E.R.10 item 10d (n°77) — f bijective ⇔ f⁻¹∘f=Id_𝔓E et f∘f⁻¹=Id_𝔓F.

Bourbaki (E.R.10 item 10d) : « f est bijective si et seulement si f⁻¹⟨f⟨X⟩⟩=X pour
toute partie X de E ET f⟨f⁻¹⟨Y⟩⟩=Y pour toute partie Y de F ».

ÉNONCÉ VISÉ (CLOS, 0 hyp — f : E→F application est dans l'antécédent) :

    ⊢ est_application(f,E,F) ⇒ (
          ( (∀X)(X⊂E ⇒ f⁻¹⟨f⟨X⟩⟩=X)  et  (∀Y)(Y⊂F ⇒ f⟨f⁻¹⟨Y⟩⟩=Y) )
          ⇔ est_bijective(f,E,F) )

Ce module ASSEMBLE (multi-étapes) à partir de bricks existants :
  · ⇐ inj⇒(∀X) : image_reciproque_image_egal_si_injective (sous {H_app(X,f),
      est_fonctionnel(f⁻¹)}) + ponts H_app←est_application (ce fichier) et
      injective→est_fonctionnel(f⁻¹) (injectif_implique_reciproque_fonctionnel) ;
  · ⇐ surj⇒(∀Y) : image_image_reciproque_egal_si_surjective (sous {est_fonctionnel(f),
      Y⊂f⟨E⟩}) + pont surj⇒(Y⊂F⇒Y⊂f⟨E⟩) ;
  · ⇒ (∀X)⇒inj et (∀Y)⇒surj : converses à bâtir (singletons / Y=F).

ÉTAPE 1 (ce commit) : pont `hyp_applicative_de_application` — {est_application(f,E,F),
X⊂E} ⊢ H_app(X,f) = (∀x)(x∈X ⇒ (x,f(x))∈f).

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, pourtout, inclus, existe, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_prop7_9_ii3 import (
    _graphe_injectif, injectif_implique_reciproque_fonctionnel)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    image_reciproque_image_egal_si_injective, image_image_reciproque_egal_si_surjective,
    image_reciproque_inclus_domaine)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import inclusion_reflexive
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import image_croissante
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import image_incluse_arrivee
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import membre_image, membre_image_reciproque


def _cut(thm, preuve_hyp):
    """Décharge de `thm` l'hypothèse H = preuve_hyp.conclusion (coupure)."""
    H = preuve_hyp.conclusion
    return N.modus_ponens(preuve_hyp, N.loi_deduction(H, thm))


def hyp_applicative(f, x):
    """H_app(X,f) := (∀x)(x∈X ⇒ (x,f(x))∈f)  (hypothèse load-bearing de (18))."""
    vf, vX, vx = _t(f), _t(x), var("x")
    return pourtout("x", impl(appartient(vx, vX),
                              appartient(E.couple(vx, E.valeur(vf, vx)), vf)))


def _t(v):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    return v if isinstance(v, Terme) else var(v)


def enonce_hyp_applicative_de_application(f="f", e="E", ff="F", x="X"):
    vf, vX = var(f), var(x)
    return hyp_applicative(vf, vX)


# @livre Ch.R §2.10 Prop.- | E.R.9 L.31 | PDF p.312  (pont : application ⇒ H_app sur toute partie X⊂E)
def hyp_applicative_de_application(f="f", e="E", ff="F", x="X"):
    """⊢ {est_application(f,E,F), X⊂E}  (∀x)(x∈X ⇒ (x,f(x))∈f).

    x∈X⊂E ⇒ x∈dom f (=E) ⇒ (∃y)(x,y)∈f ⇒ (x,f(x))∈f [valeur_dans_graphe]."""
    vf, vE, vX = var(f), var(e), var(x)
    hF = N.assume(est_application(vf, vE, var(ff)))
    domF_eq = conjonction_elim_droite(conjonction_elim_gauche(hF))  # dom f = E
    hX = N.assume(inclus(vX, vE))                                   # X ⊂ E
    vx = var("x")
    hx = N.assume(appartient(vx, vX))                              # x ∈ X
    xE = N.modus_ponens(hx, instancie(hX, vx))                     # x ∈ E
    s6 = N.s6(E.dom(vf), vE, "w", appartient(vx, var("w")))        # (domf=E)⇒((x∈domf)⇔(x∈E))
    x_domF = N.modus_ponens(xE, equivalence_arriere(N.modus_ponens(domF_eq, s6)))  # x∈dom f
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    membre_dom = instancie(instancie(dom_ax, vf), vx)             # (x∈domf)⇔(∃y)(x,y)∈f
    ex_y = N.modus_ponens(x_domF, equivalence_avant(membre_dom))  # (∃y)(x,y)∈f
    xfx = _cut(valeur_dans_graphe(vf, vx), ex_y)                  # (x,f(x))∈f
    res = N.generalisation("x", N.loi_deduction(appartient(vx, vX), xfx))
    assert res.conclusion == hyp_applicative(vf, vX), \
        "hyp_applicative_de_application : conclusion ≠ H_app attendu"
    return res


def _valeur_de_couple(vf, a, b):
    """{est_fonctionnel(f)} ⊢ (a,b)∈f ⇒ f(a)=b.   (valeur lue depuis un couple du graphe.)"""
    hab = N.assume(appartient(E.couple(a, b), vf))
    ex = N.modus_ponens(hab, N.s5(appartient(E.couple(a, var("y")), vf), b, "y"))  # (∃y)(a,y)∈f
    vc = valeur_caracterisation(vf, a)                    # {f func,(∃y)(a,y)∈f} ((a,y)∈f)⇔(y=f(a))
    vc_b = instancie(N.generalisation("y", vc), b)        # ((a,b)∈f)⇔(b=f(a))
    b_eq = N.modus_ponens(hab, equivalence_avant(vc_b))   # b=f(a)
    fa_eq = N.modus_ponens(b_eq, symetrie(b, E.valeur(vf, a)))            # f(a)=b
    fa_eq = _cut(fa_eq, ex)                               # décharge (∃y)(a,y)∈f
    return N.loi_deduction(appartient(E.couple(a, b), vf), fa_eq)         # {f func} (a,b)∈f⇒f(a)=b


# @livre Ch.R §2.10 Prop.- | E.R.9 L.31 | PDF p.312  (pont value↔graphe de l'injectivité)
def inj_dans_implique_graphe_injectif(f="f", e="E", ff="F"):
    """⊢ {est_application(f,E,F)}  injective_dans(f,E) ⇒ _graphe_injectif(f).

    (v,u),(z,u)∈f ⇒ v,z∈E [f⊂E×F] et f(v)=u=f(z) [f fonctionnel] ⇒ v=z [injective_dans]."""
    vf, vE, vF = var(f), var(e), var(ff)
    hF = N.assume(est_application(vf, vE, vF))
    F_func = conjonction_elim_gauche(conjonction_elim_gauche(hF))   # est_fonctionnel(f)
    F_incl = conjonction_elim_droite(hF)                           # f ⊂ E×F
    hinj = N.assume(E.injective_dans(vf, vE))
    u, v, z = var("u"), var("v"), var("z")
    hvz = N.assume(et(appartient(E.couple(v, u), vf), appartient(E.couple(z, u), vf)))
    vu_f = conjonction_elim_gauche(hvz)
    zu_f = conjonction_elim_droite(hvz)
    vE_ = conjonction_elim_gauche(N.modus_ponens(
        N.modus_ponens(vu_f, instancie(F_incl, E.couple(v, u))),
        equivalence_avant(couple_dans_produit_ssi(v, u, vE, vF))))   # v∈E
    zE_ = conjonction_elim_gauche(N.modus_ponens(
        N.modus_ponens(zu_f, instancie(F_incl, E.couple(z, u))),
        equivalence_avant(couple_dans_produit_ssi(z, u, vE, vF))))   # z∈E
    fv_u = _cut(N.modus_ponens(vu_f, _valeur_de_couple(vf, v, u)), F_func)   # f(v)=u
    fz_u = _cut(N.modus_ponens(zu_f, _valeur_de_couple(vf, z, u)), F_func)   # f(z)=u
    fv_fz = composer_egalites(fv_u, N.modus_ponens(fz_u, symetrie(E.valeur(vf, z), u)))  # f(v)=f(z)
    inj_vz = instancie(instancie(hinj, v), z)             # (v∈E∧z∈E∧f(v)=f(z))⇒v=z
    vz_eq = N.modus_ponens(conjonction_intro(conjonction_intro(vE_, zE_), fv_fz), inj_vz)  # v=z
    imp = N.loi_deduction(hvz.conclusion, vz_eq)
    gen = N.generalisation("u", N.generalisation("v", N.generalisation("z", imp)))
    res = N.loi_deduction(E.injective_dans(vf, vE), gen)
    assert res.conclusion == impl(E.injective_dans(vf, vE), _graphe_injectif(vf)), \
        "inj_dans_implique_graphe_injectif : conclusion ≠ énoncé attendu"
    return res


# @livre Ch.R §2.10 Prop.- | E.R.9 L.31 | PDF p.312  (injective_dans ⇒ f⁻¹ fonctionnel)
def inj_dans_implique_reciproque_fonctionnel(f="f", e="E", ff="F"):
    """⊢ {est_application(f,E,F)}  injective_dans(f,E) ⇒ est_fonctionnel(f⁻¹).

    Compose le pont value↔graphe avec Prop.7 (injectif graphe ⇒ f⁻¹ fonctionnel)."""
    vf = var(f)
    return syllogisme(inj_dans_implique_graphe_injectif(f, e, ff),
                      injectif_implique_reciproque_fonctionnel(f))


def _forall_X_identite(vf, vE):
    vX = var("X")
    return pourtout("X", impl(inclus(vX, vE),
                              egal(E.image(E.reciproque(vf), E.image(vf, vX)), vX)))


def _forall_Y_identite(vf, vF):
    vY = var("Y")
    return pourtout("Y", impl(inclus(vY, vF),
                              egal(E.image(vf, E.image(E.reciproque(vf), vY)), vY)))


def enonce_direction_bijective_vers_identites(f="f", e="E", ff="F"):
    vf, vE, vF = var(f), var(e), var(ff)
    return impl(E.est_bijective(vf, vE, vF),
                et(_forall_X_identite(vf, vE), _forall_Y_identite(vf, vF)))


# @livre Ch.R §2.10 Prop.- | E.R.10 item 10d | PDF p.313  (sens ⇐ : bijective ⇒ les deux identités)
def direction_bijective_vers_identites(f="f", e="E", ff="F"):
    """⊢ {est_application(f,E,F)}  est_bijective(f,E,F) ⇒
          ( (∀X)(X⊂E ⇒ f⁻¹⟨f⟨X⟩⟩=X)  et  (∀Y)(Y⊂F ⇒ f⟨f⁻¹⟨Y⟩⟩=Y) ).

    ⇐-inj : bijective→injective_dans→est_fonctionnel(f⁻¹) ; H_app(X,f) ; brick (18)-égalité.
    ⇐-surj : bijective→surjective→(Y⊂F⇒Y⊂f⟨E⟩) [f⟨E⟩=F] ; f fonctionnel ; brick (19)-égalité."""
    vf, vE, vF = var(f), var(e), var(ff)
    hF = N.assume(est_application(vf, vE, vF))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(hF))   # est_fonctionnel(f)
    hbij = N.assume(E.est_bijective(vf, vE, vF))
    inj = conjonction_elim_gauche(hbij)                            # injective_dans(f,E)
    surj = conjonction_elim_droite(hbij)                          # image(f,E)=F
    frec_func = N.modus_ponens(inj, inj_dans_implique_reciproque_fonctionnel(f, e, ff))  # est_fonctionnel(f⁻¹)

    # ── (∀X)(X⊂E ⇒ f⁻¹⟨f⟨X⟩⟩=X) ──────────────────────────────────────────────
    vX = var("X")
    Happ = hyp_applicative_de_application(f, e, ff, "X")           # {est_app,X⊂E} H_app(X,f)
    eqX_lem = image_reciproque_image_egal_si_injective(f, "X")     # H_app⇒(est_fonct(f⁻¹)⇒ f⁻¹⟨f⟨X⟩⟩=X)
    eqX = N.modus_ponens(frec_func, N.modus_ponens(Happ, eqX_lem)) # f⁻¹⟨f⟨X⟩⟩=X
    genX = N.generalisation("X", N.loi_deduction(inclus(vX, vE), eqX))

    # ── (∀Y)(Y⊂F ⇒ f⟨f⁻¹⟨Y⟩⟩=Y) ──────────────────────────────────────────────
    vY = var("Y")
    hY = N.assume(inclus(vY, vF))
    s6Y = N.s6(E.image(vf, vE), vF, "w", inclus(vY, var("w")))     # (f⟨E⟩=F)⇒((Y⊂f⟨E⟩)⇔(Y⊂F))
    Ysub = N.modus_ponens(hY, equivalence_arriere(N.modus_ponens(surj, s6Y)))  # Y⊂f⟨E⟩
    eqY_lem = image_image_reciproque_egal_si_surjective(f, "Y", e) # est_fonct(f)⇒(Y⊂f⟨E⟩⇒ f⟨f⁻¹⟨Y⟩⟩=Y)
    eqY = N.modus_ponens(Ysub, N.modus_ponens(Ffunc, eqY_lem))     # f⟨f⁻¹⟨Y⟩⟩=Y
    genY = N.generalisation("Y", N.loi_deduction(inclus(vY, vF), eqY))

    cons = conjonction_intro(genX, genY)
    res = N.loi_deduction(E.est_bijective(vf, vE, vF), cons)
    assert res.conclusion == enonce_direction_bijective_vers_identites(f, e, ff), \
        "direction_bijective_vers_identites : conclusion ≠ énoncé attendu"
    return res


def enonce_converse_Y_vers_surjective(f="f", e="E", ff="F"):
    vf, vE, vF = var(f), var(e), var(ff)
    return impl(_forall_Y_identite(vf, vF), E.est_surjective(vf, vE, vF))


# @livre Ch.R §2.10 Prop.- | E.R.10 item 10d | PDF p.313  (converse ⇒-surj : (∀Y…) ⇒ f surjective)
def converse_Y_vers_surjective(f="f", e="E", ff="F"):
    """⊢ {est_application(f,E,F)}  (∀Y)(Y⊂F ⇒ f⟨f⁻¹⟨Y⟩⟩=Y) ⇒ est_surjective(f,E,F).

    Y=F : f⟨f⁻¹⟨F⟩⟩=F [instance] ; f⁻¹⟨F⟩⊂E [image_reciproque_inclus_domaine, domf=E] ⇒
    f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩ [image_croissante] ; d'où F⊂f⟨E⟩, et f⟨E⟩⊂F [image_incluse_arrivee] ⇒ f⟨E⟩=F."""
    vf, vE, vF = var(f), var(e), var(ff)
    hF = N.assume(est_application(vf, vE, vF))
    domF_eq = conjonction_elim_droite(conjonction_elim_gauche(hF))   # dom f = E
    hall = N.assume(_forall_Y_identite(vf, vF))
    imgfE = E.image(vf, vE)                         # f⟨E⟩
    recipF = E.image(E.reciproque(vf), vF)          # f⁻¹⟨F⟩
    fgF = E.image(vf, recipF)                       # f⟨f⁻¹⟨F⟩⟩

    reflF = instancie(N.generalisation("x", inclusion_reflexive("x")), vF)  # F⊂F
    eqF = N.modus_ponens(reflF, instancie(hall, vF))       # f⟨f⁻¹⟨F⟩⟩=F
    recipF_sub_E = N.modus_ponens(domF_eq, image_reciproque_inclus_domaine(f, ff, e))  # f⁻¹⟨F⟩⊂E
    croiss = instancie(instancie(N.generalisation("X", N.generalisation("Y",
                image_croissante(f, "X", "Y"))), recipF), vE)   # (f⁻¹⟨F⟩⊂E)⇒(f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩)
    fgF_sub_fE = N.modus_ponens(recipF_sub_E, croiss)          # f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩
    F_eq_fgF = N.modus_ponens(eqF, symetrie(fgF, vF))          # F=f⟨f⁻¹⟨F⟩⟩
    s6 = N.s6(vF, fgF, "w", inclus(var("w"), imgfE))          # (F=f⟨f⁻¹⟨F⟩⟩)⇒((F⊂f⟨E⟩)⇔(f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩))
    F_sub_fE = N.modus_ponens(fgF_sub_fE, equivalence_arriere(N.modus_ponens(F_eq_fgF, s6)))  # F⊂f⟨E⟩
    fE_sub_F = image_incluse_arrivee(f, e, ff)                # {est_app} f⟨E⟩⊂F
    eq_surj = N.modus_ponens(conjonction_intro(fE_sub_F, F_sub_fE),
                             extensionnalite_appliquee(imgfE, vF))   # f⟨E⟩=F
    res = N.loi_deduction(_forall_Y_identite(vf, vF), eq_surj)
    assert res.conclusion == enonce_converse_Y_vers_surjective(f, e, ff), \
        "converse_Y_vers_surjective : conclusion ≠ énoncé attendu"
    return res


def enonce_converse_X_vers_injective(f="f", e="E", ff="F"):
    vf, vE = var(f), var(e)
    return impl(_forall_X_identite(vf, vE), E.injective_dans(vf, vE))


# @livre Ch.R §2.10 Prop.- | E.R.10 item 10d | PDF p.313  (converse ⇒-inj : (∀X…) ⇒ f injective)
def converse_X_vers_injective(f="f", e="E", ff="F"):
    """⊢ {est_application(f,E,F)}  (∀X)(X⊂E ⇒ f⁻¹⟨f⟨X⟩⟩=X) ⇒ injective_dans(f,E).

    Pour u,u'∈E avec f(u)=f(u') : X={u} ; f⁻¹⟨f⟨{u}⟩⟩={u} [instance] ; f(u')=f(u)∈f⟨{u}⟩
    et (u',f(u'))∈f ⇒ u'∈f⁻¹⟨f⟨{u}⟩⟩={u} ⇒ u'=u [singleton_membre]."""
    vf, vE, vF = var(f), var(e), var(ff)
    hF = N.assume(est_application(vf, vE, vF))
    domF_eq = conjonction_elim_droite(conjonction_elim_gauche(hF))   # dom f = E
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    def _uf_f(a, aE):
        """{hF, aE} ⊢ (a, f(a)) ∈ f   (a∈E ⇒ a∈dom f ⇒ (∃y)(a,y)∈f ⇒ (a,f(a))∈f)."""
        s6a = N.s6(E.dom(vf), vE, "w", appartient(a, var("w")))
        a_dom = N.modus_ponens(aE, equivalence_arriere(N.modus_ponens(domF_eq, s6a)))
        ex = N.modus_ponens(a_dom, equivalence_avant(instancie(instancie(dom_ax, vf), a)))
        return _cut(valeur_dans_graphe(vf, a), ex)

    hall = N.assume(_forall_X_identite(vf, vE))
    u, up = var("u"), var("up")
    h = N.assume(et(et(appartient(u, vE), appartient(up, vE)),
                    egal(E.valeur(vf, u), E.valeur(vf, up))))
    uE = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upE = conjonction_elim_droite(conjonction_elim_gauche(h))
    fu_fup = conjonction_elim_droite(h)                     # f(u)=f(up)
    su = E.singleton(u)                                     # {u}
    fu, fup = E.valeur(vf, u), E.valeur(vf, up)
    img_su = E.image(vf, su)                                # f⟨{u}⟩
    pre = E.image(E.reciproque(vf), img_su)                # f⁻¹⟨f⟨{u}⟩⟩

    # {u} ⊂ E
    z = var("z")
    hz = N.assume(appartient(z, su))
    z_eq_u = N.modus_ponens(hz, equivalence_avant(singleton_membre(z, u)))       # z=u
    zE = N.modus_ponens(uE, equivalence_arriere(N.modus_ponens(z_eq_u,
            N.s6(z, u, "w", appartient(var("w"), vE)))))                          # z∈E
    su_sub_E = N.generalisation("z", N.loi_deduction(appartient(z, su), zE))     # {u}⊂E
    eq_pre = N.modus_ponens(su_sub_E, instancie(hall, su))                       # f⁻¹⟨f⟨{u}⟩⟩={u}

    # f(u) ∈ f⟨{u}⟩  (témoin u : u∈{u} et (u,f(u))∈f)
    u_in_su = N.modus_ponens(N.reflexivite(u), equivalence_arriere(singleton_membre(u, u)))
    uf = _uf_f(u, uE)                                       # (u,f(u))∈f
    body_mi = lambda w: et(appartient(w, su), appartient(E.couple(w, fu), vf))
    ex_mi = N.modus_ponens(conjonction_intro(u_in_su, uf), N.s5(body_mi(var("x")), u, "x"))
    fu_in_img = N.modus_ponens(ex_mi, equivalence_arriere(membre_image(vf, su, fu)))  # f(u)∈f⟨{u}⟩
    # f(up) ∈ f⟨{u}⟩  (Leibniz f(u)=f(up))
    fup_in_img = N.modus_ponens(fu_in_img, equivalence_avant(N.modus_ponens(fu_fup,
            N.s6(fu, fup, "w", appartient(var("w"), img_su)))))                  # f(up)∈f⟨{u}⟩
    # (f(up), up) ∈ f⁻¹  (de (up,f(up))∈f)
    upf = _uf_f(up, upE)                                    # (up,f(up))∈f
    fup_up_rec = N.modus_ponens(upf, equivalence_arriere(couple_reciproque(vf, fup, up)))  # (f(up),up)∈f⁻¹
    # up ∈ f⁻¹⟨f⟨{u}⟩⟩  (témoin x=f(up))
    body_mir = lambda w: et(appartient(w, img_su), appartient(E.couple(w, up), E.reciproque(vf)))
    ex_mir = N.modus_ponens(conjonction_intro(fup_in_img, fup_up_rec), N.s5(body_mir(var("x")), fup, "x"))
    up_in_pre = N.modus_ponens(ex_mir, equivalence_arriere(membre_image_reciproque(vf, img_su, up)))
    # up ∈ {u}  (réécriture f⁻¹⟨f⟨{u}⟩⟩={u})
    up_in_su = N.modus_ponens(up_in_pre, equivalence_avant(N.modus_ponens(eq_pre,
            N.s6(pre, su, "w", appartient(up, var("w"))))))                      # up∈{u}
    up_eq_u = N.modus_ponens(up_in_su, equivalence_avant(singleton_membre(up, u)))   # up=u
    u_eq_up = N.modus_ponens(up_eq_u, symetrie(up, u))     # u=up
    imp = N.loi_deduction(h.conclusion, u_eq_up)
    gen = N.generalisation("u", N.generalisation("up", imp))
    res = N.loi_deduction(_forall_X_identite(vf, vE), gen)
    assert res.conclusion == enonce_converse_X_vers_injective(f, e, ff), \
        "converse_X_vers_injective : conclusion ≠ énoncé attendu"
    return res


def enonce_bijective_ssi_identites(f="f", e="E", ff="F"):
    vf, vE, vF = var(f), var(e), var(ff)
    both = et(_forall_X_identite(vf, vE), _forall_Y_identite(vf, vF))
    return impl(est_application(vf, vE, vF), equiv(both, E.est_bijective(vf, vE, vF)))


# @livre Ch.R §2.10 Prop.- | E.R.10 item 10d | PDF p.313  (f bijective ⇔ f⁻¹∘f=Id_𝔓E et f∘f⁻¹=Id_𝔓F)
# @livre Ch.R §2.10 Demo.- | E.R.10 item 10d | PDF p.313  (démo : ⇐ égalités image/préimage ; ⇒ converses singletons/Y=F)
def bijective_ssi_identites(f="f", e="E", ff="F"):
    """🎯 ⊢ est_application(f,E,F) ⇒
          ( ( (∀X⊂E)(f⁻¹⟨f⟨X⟩⟩=X) et (∀Y⊂F)(f⟨f⁻¹⟨Y⟩⟩=Y) ) ⇔ est_bijective(f,E,F) ).  (n°77.)"""
    vf, vE, vF = var(f), var(e), var(ff)
    both = et(_forall_X_identite(vf, vE), _forall_Y_identite(vf, vF))
    # ⇒ : (∀X…∧∀Y…) ⇒ bijective  (converses)
    hboth = N.assume(both)
    inj = N.modus_ponens(conjonction_elim_gauche(hboth), converse_X_vers_injective(f, e, ff))
    surj = N.modus_ponens(conjonction_elim_droite(hboth), converse_Y_vers_surjective(f, e, ff))
    imp_R = N.loi_deduction(both, conjonction_intro(inj, surj))    # {est_app} both⇒bijective
    # ⇐ : bijective ⇒ (∀X…∧∀Y…)
    imp_L = direction_bijective_vers_identites(f, e, ff)           # {est_app} bijective⇒both
    equiv_thm = conjonction_intro(imp_R, imp_L)                   # {est_app} both⇔bijective
    res = N.loi_deduction(est_application(vf, vE, vF), equiv_thm)
    assert res.conclusion == enonce_bijective_ssi_identites(f, e, ff), \
        "bijective_ssi_identites : conclusion ≠ énoncé attendu"
    return res


__all__ = ["hyp_applicative", "enonce_hyp_applicative_de_application",
           "hyp_applicative_de_application",
           "inj_dans_implique_graphe_injectif", "inj_dans_implique_reciproque_fonctionnel",
           "enonce_direction_bijective_vers_identites", "direction_bijective_vers_identites",
           "enonce_converse_Y_vers_surjective", "converse_Y_vers_surjective",
           "enonce_converse_X_vers_injective", "converse_X_vers_injective",
           "enonce_bijective_ssi_identites", "bijective_ssi_identites"]
