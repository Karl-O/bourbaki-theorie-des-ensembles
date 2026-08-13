"""Résumé §2 (E.R.8 item 7, fin) — surjectivité ⇔ image réciproque non vide.

Bourbaki (E.R.8, dernier §) : « On a de plus f⁻¹(∅)=∅ ; mais ici, on peut avoir
f⁻¹(X)=∅ pour une partie non vide X de F ; pour que X≠∅ entraîne f⁻¹(X)≠∅ [pour
toute partie X de F], il faut et il suffit que f soit une application de E SUR F. »

ÉNONCÉ DÉRIVÉ (f application de E dans F, en hypothèse honnête) :

    ⊢ est_application(f,E,F) ⇒
        ( est_surjective(f,E,F) ⇔ (∀X)( X⊂F ⇒ ( ¬(X=∅) ⇒ ¬(f⁻¹⟨X⟩=∅) ) ) )

  · est_surjective(f,E,F) := image(f,E)=F      (ensembles_abrege, E II.16 Déf.10) ;
  · f⁻¹⟨X⟩ := image(reciproque(f), X)          (image réciproque, E.R.8 item 6) ;
  · ≠∅ := ¬(·=∅)                               (non_vide_ssi_element).

DÉMONSTRATION (bricks tous clos, primitives N.* + axiomes via membre_image /
membre_image_reciproque) :

  (⇒) surj ⇒ prop.  Sous image(f,E)=F : pour X⊂F, X≠∅, on a un témoin z∈X ; z∈F,
      donc z∈image(f,E) [congruence S6 sous image=F] ; membre_image donne un x∈E avec
      (x,z)∈f ; couple_reciproque : (z,x)∈f⁻¹ ; membre_image_reciproque (témoin z∈X)
      met x∈f⁻¹⟨X⟩ ; d'où f⁻¹⟨X⟩≠∅.  N'utilise PAS est_application.

  (⇐) app ∧ prop ⇒ surj.  Extensionnalité image(f,E)=F :
      · image(f,E)⊂F : y∈f⟨E⟩ donne (x,y)∈f⊂E×F [est_application], d'où y∈F
        (couple_dans_produit_ssi) ;
      · F⊂image(f,E) : y∈F donne {y}⊂F [appartient_singleton_inclus] et {y}≠∅ ;
        prop appliqué à X={y} donne f⁻¹⟨{y}⟩≠∅, d'où un témoin m ; m∈f⁻¹⟨{y}⟩ fournit
        w∈{y} avec (w,m)∈f⁻¹ ; w=y [singleton_membre], (m,y)∈f [couple_reciproque] ;
        m∈f⁻¹⟨{y}⟩⊂E [image_reciproque_inclus_domaine + dom f=E] ; donc y∈f⟨E⟩.

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal, appartient, impl, pourtout, inclus, equiv, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import est_surjective
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    appartient_singleton, appartient_singleton_inclus, vide_sans_element,
    extensionnalite_appliquee)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image, membre_image_reciproque)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props import image_reciproque_inclus_domaine


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _prop_body(vf, vF, X):
    """X⊂F ⇒ ( ¬(X=∅) ⇒ ¬(f⁻¹⟨X⟩=∅) )."""
    recipX = E.image(E.reciproque(vf), X)
    return impl(inclus(X, vF),
                impl(non(egal(X, E.VIDE)), non(egal(recipX, E.VIDE))))


def enonce_surjective_ssi_preimage(f="f", e="E", ff="F"):
    """La formule-cible complète (sous est_application)."""
    vf, ve, vF = _t(f), _t(e), _t(ff)
    surj = est_surjective(vf, ve, vF)
    prop = pourtout("X", _prop_body(vf, vF, var("X")))
    return impl(est_application(vf, ve, vF), equiv(surj, prop))


# ── témoin de non-vacuité, capture-safe (liant frais via generalize-instancie) ──
_NV = N.generalisation("SETV", non_vide_ssi_element("SETV"))   # (∀A)( ¬(A=∅) ⇔ (∃z)(z∈A) )


def _temoin_non_vide(S):
    """⊢ ¬(S=∅) ⇔ (∃z)(z∈S)  pour un TERME S quelconque (instancie le keystone _NV,
    le noyau gère la capture du liant « z »)."""
    return instancie(_NV, _t(S))


# ════════════════════════════════════════════════════════════════════════════
#  DIRECTION A :  { surj }  ⊢  prop        (n'utilise PAS est_application)
# ════════════════════════════════════════════════════════════════════════════
def _dir_surj_vers_prop(vf, ve, vF):
    surj = est_surjective(vf, ve, vF)              # image(f,E)=F
    imgE = E.image(vf, ve)
    h_surj = N.assume(surj)
    vX = var("X")
    recipX = E.image(E.reciproque(vf), vX)

    h_sub = N.assume(inclus(vX, vF))               # X ⊂ F
    h_ne = N.assume(non(egal(vX, E.VIDE)))         # X ≠ ∅
    ex_z = N.modus_ponens(h_ne, equivalence_avant(_temoin_non_vide(vX)))   # (∃z)(z∈X)

    vz = var("z")
    hz = N.assume(appartient(vz, vX))              # z ∈ X
    z_F = N.modus_ponens(hz, instancie(h_sub, vz)) # z ∈ F
    cong = N.modus_ponens(h_surj, N.s6(imgE, vF, "w", appartient(vz, var("w"))))  # (z∈imgE)⇔(z∈F)
    z_img = N.modus_ponens(z_F, equivalence_arriere(cong))                 # z ∈ image(f,E)

    mem_img = membre_image(vf, ve, vz)             # z∈f⟨E⟩ ⇔ (∃x)(x∈E et (x,z)∈f)
    body_x = lambda u: et(appartient(u, ve), appartient(E.couple(u, vz), vf))
    ex_x = N.modus_ponens(N.modus_ponens(z_img, equivalence_avant(mem_img)),
                          equivalence_avant(alpha_existe("x", "n", body_x(var("x")))))  # (∃n)body_x(n)
    vn = var("n")
    hbn = N.assume(body_x(vn))                     # n∈E et (n,z)∈f
    nz_f = conjonction_elim_droite(hbn)            # (n,z) ∈ f
    zn_recip = N.modus_ponens(nz_f, equivalence_arriere(couple_reciproque(vf, vz, vn)))  # (z,n)∈f⁻¹

    mem_recip = membre_image_reciproque(vf, vX, vn)   # n∈f⁻¹⟨X⟩ ⇔ (∃x)(x∈X et (x,n)∈f⁻¹)
    body_w = lambda u: et(appartient(u, vX), appartient(E.couple(u, vn), E.reciproque(vf)))
    ex_w = N.modus_ponens(conjonction_intro(hz, zn_recip), N.s5(body_w(var("x")), vz, "x"))
    n_in_recipX = N.modus_ponens(ex_w, equivalence_arriere(mem_recip))     # n ∈ f⁻¹⟨X⟩

    # f⁻¹⟨X⟩ ≠ ∅ : témoin n
    ex_in_recip = N.modus_ponens(n_in_recipX, N.s5(appartient(var("z"), recipX), vn, "z"))  # (∃z)(z∈f⁻¹⟨X⟩)
    ne_recip = N.modus_ponens(ex_in_recip, equivalence_arriere(_temoin_non_vide(recipX)))   # ¬(f⁻¹⟨X⟩=∅)

    imp_n = existe_elimination(N.loi_deduction(body_x(vn), ne_recip), "n")
    ne_under_z = N.modus_ponens(ex_x, imp_n)       # ¬(f⁻¹⟨X⟩=∅)   [sous z∈X]
    imp_z = existe_elimination(N.loi_deduction(appartient(vz, vX), ne_under_z), "z")
    ne_final = N.modus_ponens(ex_z, imp_z)         # ¬(f⁻¹⟨X⟩=∅)   [sous X≠∅, X⊂F, surj]

    inner = N.loi_deduction(non(egal(vX, E.VIDE)), ne_final)
    body = N.loi_deduction(inclus(vX, vF), inner)
    return N.generalisation("X", body)             # {surj} ⊢ prop


# ════════════════════════════════════════════════════════════════════════════
#  DIRECTION B :  { est_application, prop }  ⊢  surj
# ════════════════════════════════════════════════════════════════════════════
def _dir_prop_vers_surj(vf, ve, vF):
    app = est_application(vf, ve, vF)
    h_app = N.assume(app)
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(h_app))   # dom f = E
    f_sub = conjonction_elim_droite(h_app)                            # f ⊂ E×F
    prop = pourtout("X", _prop_body(vf, vF, var("X")))
    h_prop = N.assume(prop)
    imgE = E.image(vf, ve)

    # ── (a)  image(f,E) ⊂ F ───────────────────────────────────────────────────
    vz = var("z")
    hz = N.assume(appartient(vz, imgE))            # z ∈ f⟨E⟩
    mem_imgE = membre_image(vf, ve, vz)            # z∈f⟨E⟩ ⇔ (∃x)(x∈E et (x,z)∈f)
    body_a = lambda u: et(appartient(u, ve), appartient(E.couple(u, vz), vf))
    ex_a = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(mem_imgE)),
                          equivalence_avant(alpha_existe("x", "n", body_a(var("x")))))
    vn = var("n")
    hba = N.assume(body_a(vn))                     # n∈E et (n,z)∈f
    nz_f = conjonction_elim_droite(hba)            # (n,z) ∈ f
    nz_prod = N.modus_ponens(nz_f, instancie(f_sub, E.couple(vn, vz)))   # (n,z) ∈ E×F
    z_F = conjonction_elim_droite(N.modus_ponens(
        nz_prod, equivalence_avant(couple_dans_produit_ssi(vn, vz, ve, vF))))   # z ∈ F
    imp_a = existe_elimination(N.loi_deduction(body_a(vn), z_F), "n")
    z_F_final = N.modus_ponens(ex_a, imp_a)        # z ∈ F   [sous z∈imgE]
    incl_imgE_F = N.generalisation("z", N.loi_deduction(appartient(vz, imgE), z_F_final))  # imgE ⊂ F

    # ── (b)  F ⊂ image(f,E)   (élément « y », témoin « z », inner « k » : anti-collision) ──
    vy = var("y")
    hy = N.assume(appartient(vy, vF))              # y ∈ F
    sy = E.singleton(vy)                           # {y}
    recip_sy = E.image(E.reciproque(vf), sy)       # f⁻¹⟨{y}⟩
    sy_sub_F = N.modus_ponens(hy, equivalence_avant(appartient_singleton_inclus("y", "F")))  # {y}⊂F
    # {y} ≠ ∅  (par l'absurde : y∈{y} et {y}=∅ ⇒ y∈∅, contra AXIOME_VIDE)
    y_in_sy = appartient_singleton("y")            # y ∈ {y}
    h_sy_vide = N.assume(egal(sy, E.VIDE))
    y_in_vide = N.modus_ponens(y_in_sy, equivalence_avant(
        N.modus_ponens(h_sy_vide, N.s6(sy, E.VIDE, "w", appartient(vy, var("w"))))))   # y∈∅  [sous {y}=∅]
    y_notin_vide = vide_sans_element("y")          # ¬(y∈∅)
    falso = N.modus_ponens(y_in_vide, N.modus_ponens(
        y_notin_vide, N.s2(non(appartient(vy, E.VIDE)), non(egal(sy, E.VIDE)))))       # ¬({y}=∅) [sous {y}=∅]
    sy_ne = N.modus_ponens(N.loi_deduction(egal(sy, E.VIDE), falso), N.s1(non(egal(sy, E.VIDE))))  # ¬({y}=∅)

    # prop appliqué à X={y}
    prop_at = instancie(h_prop, sy)                # {y}⊂F ⇒ (¬({y}=∅) ⇒ ¬(f⁻¹⟨{y}⟩=∅))
    recip_ne = N.modus_ponens(sy_ne, N.modus_ponens(sy_sub_F, prop_at))   # ¬(f⁻¹⟨{y}⟩=∅)
    ex_wit = N.modus_ponens(recip_ne, equivalence_avant(_temoin_non_vide(recip_sy)))   # (∃z)(z∈f⁻¹⟨{y}⟩)

    vz = var("z")                                  # témoin (liant « z » de _temoin_non_vide)
    hm = N.assume(appartient(vz, recip_sy))        # z ∈ f⁻¹⟨{y}⟩
    mem_r = membre_image_reciproque(vf, sy, vz)    # z∈f⁻¹⟨{y}⟩ ⇔ (∃x)(x∈{y} et (x,z)∈f⁻¹)
    body_w = lambda u: et(appartient(u, sy), appartient(E.couple(u, vz), E.reciproque(vf)))
    ex_w = N.modus_ponens(N.modus_ponens(hm, equivalence_avant(mem_r)),
                          equivalence_avant(alpha_existe("x", "k", body_w(var("x")))))   # (∃k)body_w(k)
    vk = var("k")
    hbw = N.assume(body_w(vk))                     # k∈{y} et (k,z)∈f⁻¹
    k_in_sy = conjonction_elim_gauche(hbw)         # k ∈ {y}
    k_eq_y = N.modus_ponens(k_in_sy, equivalence_avant(singleton_membre(vk, vy)))   # k = y
    kz_recip = conjonction_elim_droite(hbw)        # (k,z) ∈ f⁻¹
    zk_f = N.modus_ponens(kz_recip, equivalence_avant(couple_reciproque(vf, vk, vz)))   # (z,k) ∈ f
    # (z,y)∈f  via k=y  (Leibniz S6 sur la 2ᵉ coordonnée)
    zy_f = N.modus_ponens(zk_f, equivalence_avant(N.modus_ponens(
        k_eq_y, N.s6(vk, vy, "w", appartient(E.couple(vz, var("w")), vf)))))   # (z,y) ∈ f
    # z ∈ E  via f⁻¹⟨{y}⟩ ⊂ E
    recip_sub_E = N.modus_ponens(dom_eq, image_reciproque_inclus_domaine(vf, sy, ve))   # f⁻¹⟨{y}⟩ ⊂ E
    z_in_E = N.modus_ponens(hm, instancie(recip_sub_E, vz))   # z ∈ E
    # y ∈ f⟨E⟩  via membre_image (témoin z)
    mem_imgE_y = membre_image(vf, ve, vy)          # y∈f⟨E⟩ ⇔ (∃x)(x∈E et (x,y)∈f)
    body_e = lambda u: et(appartient(u, ve), appartient(E.couple(u, vy), vf))
    ex_e = N.modus_ponens(conjonction_intro(z_in_E, zy_f), N.s5(body_e(var("x")), vz, "x"))
    y_in_imgE = N.modus_ponens(ex_e, equivalence_arriere(mem_imgE_y))   # y ∈ f⟨E⟩

    imp_k = existe_elimination(N.loi_deduction(body_w(vk), y_in_imgE), "k")
    y_img_under_wit = N.modus_ponens(ex_w, imp_k)  # y∈f⟨E⟩  [sous z∈recip_sy]
    imp_wit = existe_elimination(N.loi_deduction(appartient(vz, recip_sy), y_img_under_wit), "z")
    y_in_imgE_final = N.modus_ponens(ex_wit, imp_wit)   # y ∈ f⟨E⟩   [sous y∈F]
    incl_F_imgE_y = N.generalisation("y", N.loi_deduction(appartient(vy, vF), y_in_imgE_final))  # ∀y(y∈F⇒y∈imgE)
    # α-conversion « y » → « z »  (liant attendu par extensionnalite_appliquee / A1)
    incl_F_imgE = N.generalisation("z", instancie(incl_F_imgE_y, var("z")))   # inclus(F, imgE)

    eq = N.modus_ponens(conjonction_intro(incl_imgE_F, incl_F_imgE),
                        extensionnalite_appliquee(imgE, vF))   # image(f,E) = F
    return eq                                      # {app, prop} ⊢ surj


# ════════════════════════════════════════════════════════════════════════════
#  🎯  LE THÉORÈME  (équivalence sous est_application)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §2 Prop.- | E.R.8 item 7 | PDF p.311  (surjection ⇔ « X≠∅ ⇒ f⁻¹(X)≠∅ » — DÉRIVÉ)
# @livre Ch.R §2 Demo.- | E.R.8 item 7 | PDF p.311  (démo : ⇒ témoin+couple_reciproque ; ⇐ extensionnalité+singleton)
def surjective_ssi_preimage_non_vide(f="f", e="E", ff="F"):
    """🎯 ⊢ est_application(f,E,F) ⇒
            ( est_surjective(f,E,F) ⇔ (∀X)( X⊂F ⇒ ( ¬(X=∅) ⇒ ¬(f⁻¹⟨X⟩=∅) ) ) ).

    « f surjective de E sur F » ⟺ « toute partie non vide de F a une image réciproque
    non vide » (E.R.8 item 7).  Hypothèse honnête : f application de E dans F."""
    vf, ve, vF = _t(f), _t(e), _t(ff)
    surj = est_surjective(vf, ve, vF)
    prop = pourtout("X", _prop_body(vf, vF, var("X")))

    # ⇒ : surj ⇒ prop   (n'utilise pas est_application)
    sens_avant = N.loi_deduction(surj, _dir_surj_vers_prop(vf, ve, vF))
    # ⇐ : prop ⇒ surj   (sous est_application, déchargé au niveau du théorème)
    sens_arriere = N.loi_deduction(prop, _dir_prop_vers_surj(vf, ve, vF))

    equ = conjonction_intro(sens_avant, sens_arriere)   # surj ⇔ prop   [sous est_application]
    res = N.loi_deduction(est_application(vf, ve, vF), equ)
    assert res.conclusion == enonce_surjective_ssi_preimage(f, e, ff), \
        "surjective_ssi_preimage : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_surjective_ssi_preimage", "surjective_ssi_preimage_non_vide"]
