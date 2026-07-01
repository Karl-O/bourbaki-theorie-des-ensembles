"""§II.3.2 (Résumé E.R.9, §2 item 10) — FIDÉLITÉ : image directe / réciproque.

Les deux inclusions de fidélité reliant image directe f⟨⟩ et image réciproque
f⁻¹⟨⟩, énoncées au Résumé des résultats (E.R.9, §2, item 10), avec X partie de E,
Y partie de F, f application de E dans F :

  (18)  X ⊂ f⁻¹⟨f⟨X⟩⟩        (`inclus_image_reciproque_image`)
  (19)  f⟨f⁻¹⟨Y⟩⟩ ⊂ Y        (`image_image_reciproque_inclus`)

HYPOTHÈSES HONNÊTES (load-bearing minimales — jamais la conclusion en hyp) :
  • (18) demande que f soit APPLICATIVE sur X, i.e. chaque x∈X possède bien le
    couple (x,f(x)) dans le graphe : H_app(X,f) = (∀x)(x∈X ⇒ (x,f(x))∈f).
    C'est exactement « X⊂E et f application de E dans F » restreint à ce qui sert :
    sans elle, un x∈X sans image ne serait pas récupéré dans f⁻¹⟨f⟨X⟩⟩.
  • (19) demande l'UNIVALENCE de f, i.e. est_fonctionnel(f) : un z∈f⟨f⁻¹⟨Y⟩⟩
    provient d'un x∈f⁻¹⟨Y⟩ avec (x,z)∈f ; or x∈f⁻¹⟨Y⟩ fournit un y∈Y avec (x,y)∈f.
    Sans univalence, z et y pourraient différer et z échapper à Y.

PREUVES (pointwise, primitives N.* + axiomes via membre_image / membre_image_recip) :
  AXIOME_IMAGE :     a∈G⟨Z⟩  ⇔ (∃x)(x∈Z et (x,a)∈G)         (G:=f ou G:=f⁻¹)
  couple_reciproque : (u,v)∈f⁻¹ ⇔ (v,u)∈f                    (échange E.II.41)
  est_fonctionnel :  (∀u)(∀v)(∀z)(((u,v)∈f et (u,z)∈f)⇒v=z)  (univalence E.II.43)

theorie_ensembles() inchangée (22 axiomes) : aucun axiome fabriqué, que des N.*.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, et, appartient, impl, pourtout, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image, membre_image_reciproque)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque


def _t(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _hyp_applicative(vf, vx, x="x"):
    """H_app(X,f) := (∀x)(x∈X ⇒ (x,f(x))∈f).

    « f est une application sur X » réduit à ce qui est load-bearing pour (18) :
    chaque antécédent x de X a son couple (x,f(x)) dans le graphe f."""
    vu = var(x)
    return pourtout(x, impl(appartient(vu, vx),
                            appartient(E.couple(vu, E.valeur(vf, vu)), vf)))


# ════════════════════════════════════════════════════════════════════════════
#  (18)  X ⊂ f⁻¹⟨f⟨X⟩⟩   —   sous H_app(X,f)  (E.R.9, §2 item 10).
# ════════════════════════════════════════════════════════════════════════════
def cible_inclus_image_reciproque_image(f="f", x="X"):
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    vf, vx = _t(f), _t(x)
    return inclus(vx, E.image(E.reciproque(vf), E.image(vf, vx)))


# @livre Ch.R §2.10 Prop.- | E.R.9 L.31-31 | PDF p.312
def inclus_image_reciproque_image(f="f", x="X"):
    """⊢ H_app(X,f) ⇒ X ⊂ f⁻¹⟨f⟨X⟩⟩.   (E.R.9, §2 item 10, formule (18).)

    z∈X ⇒ (z,f(z))∈f [H_app] ⇒ f(z)∈f⟨X⟩ [membre_image, témoin x:=z]
        ⇒ (f(z),z)∈f⁻¹ [couple_reciproque] ⇒ z∈f⁻¹⟨f⟨X⟩⟩
        [membre_image_reciproque, témoin x:=f(z)].  generalisation + def inclus."""
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    vf, vx = _t(f), _t(x)
    vz = var("z")
    fz = E.valeur(vf, vz)                                  # f(z) = τy((z,y)∈f)
    imgX = E.image(vf, vx)                                 # f⟨X⟩
    recip_imgX = E.image(E.reciproque(vf), imgX)          # f⁻¹⟨f⟨X⟩⟩

    hyp = _hyp_applicative(vf, vx)
    happ = N.assume(hyp)
    # z∈X ⇒ (z,f(z))∈f  (instance de H_app en z), puis sous z∈X : (z,f(z))∈f
    z_couple_imp = instancie(happ, vz)                     # z∈X ⇒ (z,f(z))∈f
    hzx = N.assume(appartient(vz, vx))                     # z∈X
    z_couple = N.modus_ponens(hzx, z_couple_imp)           # (z,f(z))∈f

    # f(z) ∈ f⟨X⟩  via membre_image, témoin x:=z dans (∃x)(x∈X et (x,f(z))∈f)
    mem_img = membre_image(vf, vx, fz)                     # f(z)∈f⟨X⟩ ⇔ (∃x)(x∈X et (x,f(z))∈f)
    body_img = lambda u: et(appartient(u, vx), appartient(E.couple(u, fz), vf))
    ex_img = N.modus_ponens(conjonction_intro(hzx, z_couple),
                            N.s5(body_img(var("x")), vz, "x"))   # (∃x)(x∈X et (x,f(z))∈f)
    fz_in_imgX = N.modus_ponens(ex_img, equivalence_arriere(mem_img))   # f(z)∈f⟨X⟩

    # (f(z),z)∈f⁻¹  via couple_reciproque : (f(z),z)∈f⁻¹ ⇔ (z,f(z))∈f
    cr = couple_reciproque(vf, fz, vz)                     # (f(z),z)∈f⁻¹ ⇔ (z,f(z))∈f
    fz_z_recip = N.modus_ponens(z_couple, equivalence_arriere(cr))      # (f(z),z)∈f⁻¹

    # z ∈ f⁻¹⟨f⟨X⟩⟩  via membre_image_reciproque, témoin x:=f(z)
    mem_recip = membre_image_reciproque(vf, imgX, vz)      # z∈f⁻¹⟨f⟨X⟩⟩ ⇔ (∃x)(x∈f⟨X⟩ et (x,z)∈f⁻¹)
    body_recip = lambda u: et(appartient(u, imgX),
                              appartient(E.couple(u, vz), E.reciproque(vf)))
    ex_recip = N.modus_ponens(conjonction_intro(fz_in_imgX, fz_z_recip),
                              N.s5(body_recip(var("x")), fz, "x"))      # (∃x)(...)
    z_in = N.modus_ponens(ex_recip, equivalence_arriere(mem_recip))     # z∈f⁻¹⟨f⟨X⟩⟩

    incl = N.generalisation("z", N.loi_deduction(appartient(vz, vx), z_in))
    # incl : ⊢ (∀z)(z∈X ⇒ z∈f⁻¹⟨f⟨X⟩⟩) = X ⊂ f⁻¹⟨f⟨X⟩⟩  (hyp H_app encore présente)
    assert incl.conclusion == inclus(vx, recip_imgX)
    return N.loi_deduction(hyp, incl)


# ════════════════════════════════════════════════════════════════════════════
#  (19)  f⟨f⁻¹⟨Y⟩⟩ ⊂ Y   —   sous est_fonctionnel(f)  (E.R.9, §2 item 10).
# ════════════════════════════════════════════════════════════════════════════
def cible_image_image_reciproque_inclus(f="f", y="Y"):
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    vf, vy = _t(f), _t(y)
    return inclus(E.image(vf, E.image(E.reciproque(vf), vy)), vy)


# @livre Ch.R §2.10 Prop.- | E.R.9 L.32-32 | PDF p.312
def image_image_reciproque_inclus(f="f", y="Y"):
    """⊢ est_fonctionnel(f) ⇒ f⟨f⁻¹⟨Y⟩⟩ ⊂ Y.   (E.R.9, §2 item 10, formule (19).)

    z∈f⟨f⁻¹⟨Y⟩⟩ ⇒ (∃a)(a∈f⁻¹⟨Y⟩ et (a,z)∈f) [membre_image] ; sous a :
    a∈f⁻¹⟨Y⟩ ⇒ (∃b)(b∈Y et (b,a)∈f⁻¹) [membre_image_reciproque] ;
    (b,a)∈f⁻¹ ⇔ (a,b)∈f [couple_reciproque] ; univalence (a,z)∈f & (a,b)∈f ⇒ z=b ;
    donc z=b∈Y [Leibniz s6].  existe_elimination ×2 + def inclus.

    Binders frais a,b (≠ x,y de l'axiome image et du τ-valeur) : aucune capture,
    le quantificateur interne de membre_image_reciproque garde son nom « x »."""
    vf, vy = _t(f), _t(y)
    vz, va, vb = var("z"), var("a"), var("b")
    recipY = E.image(E.reciproque(vf), vy)               # f⁻¹⟨Y⟩
    lhs = E.image(vf, recipY)                             # f⟨f⁻¹⟨Y⟩⟩

    hfunc = N.assume(E.est_fonctionnel(vf))
    h_z = N.assume(appartient(vz, lhs))                   # z∈f⟨f⁻¹⟨Y⟩⟩

    # z∈f⟨f⁻¹⟨Y⟩⟩ ⇒ (∃a)(a∈f⁻¹⟨Y⟩ et (a,z)∈f)   (membre_image, binder interne « x »)
    mem_img = membre_image(vf, recipY, vz)
    body_img = lambda u: et(appartient(u, recipY), appartient(E.couple(u, vz), vf))
    ex_a0 = N.modus_ponens(h_z, equivalence_avant(mem_img))            # (∃x)body_img(x)
    ex_a = N.modus_ponens(ex_a0, equivalence_avant(
        alpha_existe("x", "a", body_img(var("x")))))      # (∃a)body_img(a)

    # sous a : a∈f⁻¹⟨Y⟩ et (a,z)∈f
    hba = N.assume(body_img(va))
    a_in_recipY = conjonction_elim_gauche(hba)            # a∈f⁻¹⟨Y⟩
    az_f = conjonction_elim_droite(hba)                   # (a,z)∈f

    # a∈f⁻¹⟨Y⟩ ⇒ (∃b)(b∈Y et (b,a)∈f⁻¹)   (binder interne « x » α-renommé en « b »)
    mem_recip = membre_image_reciproque(vf, vy, va)       # a∈f⁻¹⟨Y⟩ ⇔ (∃x)(x∈Y et (x,a)∈f⁻¹)
    body_y = lambda u: et(appartient(u, vy),
                          appartient(E.couple(u, va), E.reciproque(vf)))
    ex_b0 = N.modus_ponens(a_in_recipY, equivalence_avant(mem_recip))  # (∃x)body_y(x) [binder « x »]
    ex_b = N.modus_ponens(ex_b0, equivalence_avant(
        alpha_existe("x", "b", body_y(var("x")))))        # (∃b)body_y(b)

    # sous b : b∈Y et (b,a)∈f⁻¹ ; déduire z∈Y
    hbb = N.assume(body_y(vb))
    b_in_Y = conjonction_elim_gauche(hbb)                 # b∈Y
    ba_recip = conjonction_elim_droite(hbb)               # (b,a)∈f⁻¹
    a_b_f = N.modus_ponens(ba_recip, equivalence_avant(
        couple_reciproque(vf, vb, va)))                   # (a,b)∈f
    # univalence : ((a,z)∈f et (a,b)∈f) ⇒ z=b
    univ = instancie(instancie(instancie(hfunc, va), vz), vb)
    z_eq_b = N.modus_ponens(conjonction_intro(az_f, a_b_f), univ)      # z=b
    # z∈Y : b∈Y et z=b ⇒ z∈Y  (Leibniz s6 sur w∈Y)
    z_in_Y = N.modus_ponens(b_in_Y, equivalence_arriere(
        N.modus_ponens(z_eq_b, N.s6(vz, vb, "w", appartient(var("w"), vy)))))

    # décharger b puis a
    imp_b = existe_elimination(N.loi_deduction(body_y(vb), z_in_Y), "b")
    z_in_Y_under_a = N.modus_ponens(ex_b, imp_b)          # z∈Y  (sous body_img(a))
    imp_a = existe_elimination(N.loi_deduction(body_img(va), z_in_Y_under_a), "a")
    z_in_Y_final = N.modus_ponens(ex_a, imp_a)            # z∈Y  (sous z∈lhs, hfunc)

    incl = N.generalisation("z", N.loi_deduction(appartient(vz, lhs), z_in_Y_final))
    return N.loi_deduction(E.est_fonctionnel(vf), incl)


# ════════════════════════════════════════════════════════════════════════════
#  RÉCIPROQUE de (18) sous INJECTIVITÉ : f⁻¹⟨f⟨X⟩⟩ ⊂ X   (⇒ f⁻¹⟨f⟨X⟩⟩ = X).
# ════════════════════════════════════════════════════════════════════════════
def cible_image_reciproque_image_inclus_si_injective(f="f", x="X"):
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    vf, vx = _t(f), _t(x)
    return impl(E.est_fonctionnel(E.reciproque(vf)),
                inclus(E.image(E.reciproque(vf), E.image(vf, vx)), vx))


# @livre Ch.R §2.10 Prop.- | E.R.9 L.31-31 | PDF p.312
def image_reciproque_image_inclus_si_injective(f="f", x="X"):
    """⊢ est_fonctionnel(f⁻¹) ⇒ f⁻¹⟨f⟨X⟩⟩ ⊂ X.   (réciproque de (18) sous f injective.)

    « f injective » = f⁻¹ fonctionnel (univalence de f⁻¹).  z∈f⁻¹⟨f⟨X⟩⟩ ⇒ (∃w)(w∈f⟨X⟩ et
    (w,z)∈f⁻¹) ; w∈f⟨X⟩ ⇒ (∃x')(x'∈X et (x',w)∈f) ⇒ (w,x')∈f⁻¹ [couple_reciproque] ;
    univalence de f⁻¹ : (w,z)∈f⁻¹ et (w,x')∈f⁻¹ ⇒ z=x' ; d'où z=x'∈X.  Miroir de (19)
    sur f⁻¹.  Combinée à (18) [inclus_image_reciproque_image], donne f⁻¹⟨f⟨X⟩⟩ = X."""
    vf, vx = _t(f), _t(x)
    vz, vw, vxp = var("z"), var("m"), var("xp")          # « m » (≠ « w », liant interne de couple_egal_…)
    recipf = E.reciproque(vf)
    imgX = E.image(vf, vx)
    lhs = E.image(recipf, imgX)                          # f⁻¹⟨f⟨X⟩⟩

    hinj = N.assume(E.est_fonctionnel(recipf))           # f injective (f⁻¹ fonctionnel)
    h_z = N.assume(appartient(vz, lhs))                  # z ∈ f⁻¹⟨f⟨X⟩⟩

    mem_recip = membre_image_reciproque(vf, imgX, vz)    # z∈lhs ⇔ (∃x)(x∈f⟨X⟩ et (x,z)∈f⁻¹)
    body_w = lambda u: et(appartient(u, imgX), appartient(E.couple(u, vz), recipf))
    ex_w0 = N.modus_ponens(h_z, equivalence_avant(mem_recip))
    ex_w = N.modus_ponens(ex_w0, equivalence_avant(alpha_existe("x", "m", body_w(var("x")))))

    hbw = N.assume(body_w(vw))
    w_in_imgX = conjonction_elim_gauche(hbw)             # w ∈ f⟨X⟩
    wz_recip = conjonction_elim_droite(hbw)              # (w,z) ∈ f⁻¹

    mem_img = membre_image(vf, vx, vw)                   # w∈f⟨X⟩ ⇔ (∃x)(x∈X et (x,w)∈f)
    body_xp = lambda u: et(appartient(u, vx), appartient(E.couple(u, vw), vf))
    ex_xp0 = N.modus_ponens(w_in_imgX, equivalence_avant(mem_img))
    ex_xp = N.modus_ponens(ex_xp0, equivalence_avant(alpha_existe("x", "xp", body_xp(var("x")))))

    hbxp = N.assume(body_xp(vxp))
    xp_in_X = conjonction_elim_gauche(hbxp)              # x' ∈ X
    xpw_f = conjonction_elim_droite(hbxp)                # (x',w) ∈ f
    wxp_recip = N.modus_ponens(xpw_f, equivalence_arriere(couple_reciproque(vf, vw, vxp)))  # (w,x')∈f⁻¹
    univ = instancie(instancie(instancie(hinj, vw), vz), vxp)   # ((w,z)∈f⁻¹ et (w,x')∈f⁻¹)⇒z=x'
    z_eq_xp = N.modus_ponens(conjonction_intro(wz_recip, wxp_recip), univ)   # z = x'
    z_in_X = N.modus_ponens(xp_in_X, equivalence_arriere(
        N.modus_ponens(z_eq_xp, N.s6(vz, vxp, "ww", appartient(var("ww"), vx)))))   # z ∈ X

    imp_xp = existe_elimination(N.loi_deduction(body_xp(vxp), z_in_X), "xp")
    z_under_w = N.modus_ponens(ex_xp, imp_xp)
    imp_w = existe_elimination(N.loi_deduction(body_w(vw), z_under_w), "m")
    z_final = N.modus_ponens(ex_w, imp_w)

    incl = N.generalisation("z", N.loi_deduction(appartient(vz, lhs), z_final))
    return N.loi_deduction(E.est_fonctionnel(recipf), incl)


__all__ = [
    "inclus_image_reciproque_image", "cible_inclus_image_reciproque_image",
    "image_image_reciproque_inclus", "cible_image_image_reciproque_inclus",
    "image_reciproque_image_inclus_si_injective",
    "cible_image_reciproque_image_inclus_si_injective",
]
