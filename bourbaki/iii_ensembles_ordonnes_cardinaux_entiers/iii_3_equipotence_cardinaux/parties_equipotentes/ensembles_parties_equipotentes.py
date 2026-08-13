"""Résumé §7 item 1 — Eq(E,F) ⇒ Eq(𝔓(E), 𝔓(F))  (THÉORÈME CLOS).

« Si E et F sont équipotents, 𝔓(E) et 𝔓(F) sont équipotents » (E.R.32 item 1).
Stratégie : d'une bijection f : E → F, l'application A ↦ f⟨A⟩ est une bijection de
𝔓(E) sur 𝔓(F).  On la CONSTRUIT comme graphe-terme
    H := graphe_terme(𝔓(E), f⟨Y⟩, 'Y')     (donc H(Y) = image(f, Y) sur 𝔓(E))
et on prouve est_bijection_de(H, 𝔓E, 𝔓F) par les quatre piliers (fonctionnel, domaine,
injectif, image), puis Eq(𝔓E,𝔓F) par ∃-introduction du témoin H et élimination du
témoin f de Eq(E,F).

ÉTAT (2026-07-01) : COMPLET — `equipotent_parties` CLOS (0 hyp, énoncé == Bourbaki,
theorie_ensembles == 22).  Les quatre piliers sont certifiés :
  • H_fonctionnel / H_domaine : inconditionnels (image(·,·) ATOMIQUE ⇒ aucune capture-τ) ;
  • H_injective : f⁻¹∘f = Id sur les parties (image-réciproque-image) + A1 ;
  • H_image : f∘f⁻¹ = Id sur les parties (surjectivité) + A1, témoin Y = f⁻¹⟨Z⟩.
NŒUD DE LIANTS « z » du pilier 4 levé en menant la direction ⊃ avec un élément NEUTRE
« p » (zéro collision), le liant n'étant renommé « z » (imposé par A1) qu'au
generalisation final.  Assemblage : couple_valeur_dans_graphe (H_app) +
reciproque_fonctionnelle (f⁻¹ fonctionnel) + bijection_de_conjoints + S5.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout, inclus, existe)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import image_croissante
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur, graphe_terme_domaine)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
    membre_parties_t, partie_dans_parties)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    image_reciproque_image_egal_si_injective, image_image_reciproque_egal_si_surjective,
    image_reciproque_inclus_domaine)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _mgt(a, t, u_term, v_term, x="Y", y="y"):
    """⊢ ((u,v)∈graphe_terme(a,t,x)) ⇔ (u∈a et v=t[u])  pour des TERMES u, v.
    (membre_graphe_terme n'accepte que des NOMS → généralisation + instanciation.)"""
    base = membre_graphe_terme(a, t, "uu", "vv", x, y)
    g = N.generalisation("uu", N.generalisation("vv", base))
    return instancie(instancie(g, u_term), v_term)


def _recip_inclus_E(vf, Z_term, ve):
    """⊢ dom f = E ⇒ f⁻¹⟨Z⟩ ⊂ E  pour un TERME Z  (évite la collision de liant « z »)."""
    base = image_reciproque_inclus_domaine(vf, var("Zs"), ve)   # SET « Zs » ≠ liant interne « z »
    return instancie(N.generalisation("Zs", base), Z_term)


def _feq_surj(vf, Z_term, ve):
    """⊢ est_fonctionnel(f) ⇒ Z⊂f⟨E⟩ ⇒ f⟨f⁻¹⟨Z⟩⟩=Z  pour un TERME Z  (évite « z »)."""
    base = image_image_reciproque_egal_si_surjective(vf, var("Zs"), ve)
    return instancie(N.generalisation("Zs", base), Z_term)


def _hyp_app(vf, vX):
    """H_app(X,f) := (∀x)(x∈X ⇒ (x,f(x))∈f)   (f applicative sur X)."""
    vx = var("x")
    return pourtout("x", impl(appartient(vx, vX),
                              appartient(E.couple(vx, E.valeur(vf, vx)), vf)))


def _derive_happ(vf, vsub, hAppE_thm, sub_incl_E):
    """{H_app(E,f), sub⊂E} ⊢ H_app(sub,f).   (restriction de l'applicativité.)"""
    vx = var("x")
    hx = N.assume(appartient(vx, vsub))
    x_E = N.modus_ponens(hx, instancie(sub_incl_E, vx))          # x∈E  (sub⊂E)
    xfx_f = N.modus_ponens(x_E, instancie(hAppE_thm, vx))        # (x,f(x))∈f  (H_app(E))
    return N.generalisation("x", N.loi_deduction(appartient(vx, vsub), xfx_f))


def _eq_recip_image(vf, vsub, ve, hAppE_thm, hInjF_thm, sub_PE):
    """{H_app(E,f), f⁻¹ fonctionnel, sub∈𝔓E} ⊢ f⁻¹⟨f⟨sub⟩⟩ = sub."""
    sub_incl_E = N.modus_ponens(sub_PE, equivalence_avant(membre_parties_t(vsub, ve)))  # sub⊂E
    happ_sub = _derive_happ(vf, vsub, hAppE_thm, sub_incl_E)     # H_app(sub,f)
    lemma = image_reciproque_image_egal_si_injective(vf, vsub)   # H_app⇒f⁻¹func⇒ f⁻¹⟨f⟨sub⟩⟩=sub
    return N.modus_ponens(hInjF_thm, N.modus_ponens(happ_sub, lemma))


def graphe_H(f="f", e="E"):
    """H := graphe_terme(𝔓(E), f⟨Y⟩, 'Y')  — graphe de l'application A ↦ f⟨A⟩."""
    return E.graphe_terme(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 1 : H fonctionnel) | PDF p.335
def H_fonctionnel(f="f", e="E"):
    """⊢ est_fonctionnel(H).   (pilier 1 ; automatique par C54.)"""
    return graphe_terme_fonctionnel(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y", "y")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 2 : dom H = 𝔓E) | PDF p.335
def H_domaine(f="f", e="E"):
    """⊢ dom(H) = 𝔓(E).   (pilier 2 ; graphe_terme_domaine.)"""
    return graphe_terme_domaine(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y", "y", "z")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (valeur H(Y)=f⟨Y⟩) | PDF p.335
def H_valeur(f="f", e="E", pt="Y0"):
    """{Y0 ∈ 𝔓(E)} ⊢ H(Y0) = f⟨Y0⟩ = image(f, Y0).   (valeur du témoin ; pt = NOM.)"""
    vf, ve = _t(f), _t(e)
    return graphe_terme_valeur(E.parties(ve), E.image(vf, var("Y")), pt, "Y", "y")


def cible_H_valeur(f="f", e="E", pt="Y0"):
    """Conclusion attendue de H_valeur : H(Y0) = image(f, Y0)."""
    vf, ve, vpt = _t(f), _t(e), var(pt)
    return egal(E.valeur(graphe_H(vf, ve), vpt), E.image(vf, vpt))


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 3 : H injective) | PDF p.335
def H_injective(f="f", e="E"):
    """⊢ H_app(E,f) ⇒ est_fonctionnel(f⁻¹) ⇒ injective_dans(H, 𝔓(E)).   (pilier 3.)

    H(Y)=f⟨Y⟩ ; sous H(Y)=H(Y') : f⟨Y⟩=f⟨Y'⟩ ⇒ f⁻¹⟨f⟨Y⟩⟩=f⁻¹⟨f⟨Y'⟩⟩ [congruence] ;
    or f⁻¹⟨f⟨Y⟩⟩=Y et f⁻¹⟨f⟨Y'⟩⟩=Y' [f injective, f⁻¹∘f=Id sur 𝔓], d'où Y=Y'."""
    vf, ve = _t(f), _t(e)
    PE, recipf, H = E.parties(ve), E.reciproque(vf), graphe_H(vf, ve)
    vu, vup = var("u"), var("up")

    hAppE = N.assume(_hyp_app(vf, ve))                    # f applicative sur E
    hInjF = N.assume(E.est_fonctionnel(recipf))          # f injective (f⁻¹ fonctionnel)

    ant = et(et(appartient(vu, PE), appartient(vup, PE)),
             egal(E.valeur(H, vu), E.valeur(H, vup)))
    hant = N.assume(ant)
    u_PE = conjonction_elim_gauche(conjonction_elim_gauche(hant))     # u∈𝔓E
    up_PE = conjonction_elim_droite(conjonction_elim_gauche(hant))    # u'∈𝔓E
    Hu_Hup = conjonction_elim_droite(hant)                            # H(u)=H(u')

    Hu = N.modus_ponens(u_PE, N.loi_deduction(appartient(vu, PE), H_valeur(vf, ve, "u")))   # H(u)=f⟨u⟩
    Hup = N.modus_ponens(up_PE, N.loi_deduction(appartient(vup, PE), H_valeur(vf, ve, "up")))  # H(u')=f⟨u'⟩
    fu, fup = E.image(vf, vu), E.image(vf, vup)
    # f⟨u⟩ = H(u) = H(u') = f⟨u'⟩
    fu_fup = composer_egalites(composer_egalites(
        N.modus_ponens(Hu, symetrie(E.valeur(H, vu), fu)), Hu_Hup), Hup)
    # congruence f⁻¹⟨·⟩ : f⁻¹⟨f⟨u⟩⟩ = f⁻¹⟨f⟨u'⟩⟩
    cong = N.modus_ponens(fu_fup, congruence_terme(fu, fup, E.image(recipf, var("w"))))
    equ = _eq_recip_image(vf, vu, ve, hAppE, hInjF, u_PE)             # f⁻¹⟨f⟨u⟩⟩=u
    equp = _eq_recip_image(vf, vup, ve, hAppE, hInjF, up_PE)          # f⁻¹⟨f⟨u'⟩⟩=u'
    recFu = E.image(recipf, fu)
    # u = f⁻¹⟨f⟨u⟩⟩ = f⁻¹⟨f⟨u'⟩⟩ = u'
    u_up = composer_egalites(composer_egalites(
        N.modus_ponens(equ, symetrie(recFu, vu)), cong), equp)

    gen = N.generalisation("u", N.generalisation("up", N.loi_deduction(ant, u_up)))
    return N.loi_deduction(_hyp_app(vf, ve),
                           N.loi_deduction(E.est_fonctionnel(recipf), gen))


def cible_H_injective(f="f", e="E"):
    """Conclusion attendue : H_app(E,f) ⇒ est_fonctionnel(f⁻¹) ⇒ injective_dans(H, 𝔓E)."""
    vf, ve = _t(f), _t(e)
    return impl(_hyp_app(vf, ve),
                impl(E.est_fonctionnel(E.reciproque(vf)),
                     E.injective_dans(graphe_H(vf, ve), E.parties(ve))))


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 4 : image(H,𝔓E)=𝔓F) | PDF p.335
def H_image(f="f", e="E", f_set="F"):
    """⊢ est_fonctionnel(f) ⇒ dom f=E ⇒ f⟨E⟩=F ⇒ image(H, 𝔓E) = 𝔓(F).   (pilier 4.)

    ⊂ : Z∈im(H,𝔓E) ⇒ Z=f⟨S⟩ (S⊂E) ⇒ f⟨S⟩⊂f⟨E⟩=F ⇒ Z∈𝔓F.
    ⊃ : Z∈𝔓F ⇒ Z⊂F=f⟨E⟩ ; le témoin S=f⁻¹⟨Z⟩⊂E vérifie f⟨S⟩=Z [f∘f⁻¹=Id], d'où
        (S,Z)∈H et Z∈im(H,𝔓E).  Double inclusion (A1).  (f, e = NOMS.)"""
    vf, ve, vF = _t(f), _t(e), _t(f_set)
    fname = f if isinstance(f, str) else f.nom           # image_croissante n'accepte que des NOMS
    ename = e if isinstance(e, str) else e.nom
    PE, PF, H = E.parties(ve), E.parties(vF), graphe_H(vf, ve)
    imgHPE = E.image(H, PE)
    Tim = E.image(vf, var("Y"))                          # terme définissant H : f⟨Y⟩
    vz = var("z")

    hFunc = N.assume(E.est_fonctionnel(vf))
    hDom = N.assume(egal(E.dom(vf), ve))
    hImg = N.assume(egal(E.image(vf, ve), vF))

    # ── image(H,𝔓E) ⊂ 𝔓F ──
    memH = membre_image(H, PE, vz)                       # z∈im(H,𝔓E) ⇔ (∃x)(x∈𝔓E et (x,z)∈H)
    bodyS = lambda u: et(appartient(u, PE), appartient(E.couple(u, vz), H))
    exS = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, imgHPE)), equivalence_avant(memH)),
                         equivalence_avant(alpha_existe("x", "S", bodyS(var("x")))))
    vS = var("S")
    hbS = N.assume(bodyS(vS))
    S_PE = conjonction_elim_gauche(hbS)                  # S∈𝔓E
    SZ_H = conjonction_elim_droite(hbS)                  # (S,z)∈H
    z_eq_fS = conjonction_elim_droite(N.modus_ponens(SZ_H, equivalence_avant(_mgt(PE, Tim, vS, vz))))
    fS = E.image(vf, vS)
    S_sub_E = N.modus_ponens(S_PE, equivalence_avant(membre_parties_t(vS, ve)))       # S⊂E
    fS_sub_F = N.modus_ponens(N.modus_ponens(S_sub_E, image_croissante(fname, "S", ename)),
        equivalence_avant(N.modus_ponens(hImg, N.s6(E.image(vf, ve), vF, "w", inclus(fS, var("w"))))))
    z_sub_F = N.modus_ponens(fS_sub_F, equivalence_arriere(
        N.modus_ponens(z_eq_fS, N.s6(vz, fS, "w", inclus(var("w"), vF)))))            # z⊂F
    z_PF = N.modus_ponens(z_sub_F, N.loi_deduction(inclus(vz, vF), partie_dans_parties(vz, vF)))
    z_PF_final = N.modus_ponens(exS, existe_elimination(N.loi_deduction(bodyS(vS), z_PF), "S"))
    incl1 = N.generalisation("z", N.loi_deduction(appartient(vz, imgHPE), z_PF_final))

    # ── 𝔓F ⊂ image(H,𝔓E) ──  (élément neutre « p » : « z » collisionne avec est_fonctionnel
    #    et le liant par défaut de inclus ; on renomme le liant en « z » à la toute fin.)
    vp = var("p")
    hpF = N.assume(appartient(vp, PF))
    p_sub_F = N.modus_ponens(hpF, equivalence_avant(membre_parties_t(vp, vF)))        # p⊂F
    Yw = E.image(E.reciproque(vf), vp)                   # témoin S = f⁻¹⟨p⟩
    Yw_PE = N.modus_ponens(N.modus_ponens(hDom, _recip_inclus_E(vf, vp, ve)),
        N.loi_deduction(inclus(Yw, ve), partie_dans_parties(Yw, ve)))                # f⁻¹⟨p⟩ ∈ 𝔓E
    p_sub_imgE = N.modus_ponens(p_sub_F, equivalence_arriere(
        N.modus_ponens(hImg, N.s6(E.image(vf, ve), vF, "w", inclus(vp, var("w"))))))  # p⊂f⟨E⟩
    fYw_eq_p = N.modus_ponens(p_sub_imgE, N.modus_ponens(hFunc,
        _feq_surj(vf, vp, ve)))                                                       # f⟨f⁻¹⟨p⟩⟩=p
    p_eq_fYw = N.modus_ponens(fYw_eq_p, symetrie(E.image(vf, Yw), vp))                # p=f⟨f⁻¹⟨p⟩⟩
    Yp_H = N.modus_ponens(conjonction_intro(Yw_PE, p_eq_fYw),
                          equivalence_arriere(_mgt(PE, Tim, Yw, vp)))                 # (Yw,p)∈H
    p_in_img = N.modus_ponens(N.modus_ponens(conjonction_intro(Yw_PE, Yp_H),
        N.s5(et(appartient(var("x"), PE), appartient(E.couple(var("x"), vp), H)), Yw, "x")),
        equivalence_arriere(membre_image(H, PE, vp)))                                # p∈im(H,𝔓E)
    body_p = N.loi_deduction(appartient(vp, PF), p_in_img)                            # ⊢ p∈PF ⇒ p∈im
    incl2 = N.generalisation("z", instancie(N.generalisation("p", body_p), vz))       # liant → « z »

    eq = N.modus_ponens(conjonction_intro(incl1, incl2), extensionnalite_appliquee(imgHPE, PF))
    return N.loi_deduction(E.est_fonctionnel(vf), N.loi_deduction(egal(E.dom(vf), ve),
        N.loi_deduction(egal(E.image(vf, ve), vF), eq)))


def cible_H_image(f="f", e="E", f_set="F"):
    """Conclusion attendue : est_fonctionnel(f) ⇒ dom f=E ⇒ f⟨E⟩=F ⇒ image(H,𝔓E)=𝔓F."""
    vf, ve, vF = _t(f), _t(e), _t(f_set)
    return impl(E.est_fonctionnel(vf), impl(egal(E.dom(vf), ve), impl(egal(E.image(vf, ve), vF),
               egal(E.image(graphe_H(vf, ve), E.parties(ve)), E.parties(vF)))))


# @livre Ch.R §7 Prop.1 | E R.32 item 1 | PDF p.335
def equipotent_parties(e="E", g_set="G"):
    """⊢ Eq(E, G) ⇒ Eq(𝔓E, 𝔓G).   (Résumé §7, Prop. 1 — ASSEMBLAGE FINAL.)

    D'une bijection f : E→G on fabrique H : A ↦ f⟨A⟩, bijection 𝔓E→𝔓G, attestée
    par les quatre piliers (H_fonctionnel, H_domaine, H_injective, H_image) — les
    deux derniers déchargés par les faits extraits de est_bijection_de(f,E,G) :
      • H_app(E,f) ← couple_valeur_dans_graphe (dom f=E) ;
      • est_fonctionnel(f⁻¹) ← reciproque_fonctionnelle (func f, dom f=E, inj(f,E)).
    Puis Eq(𝔓E,𝔓G) par S5 (témoin H), et décharge du témoin f par existe_elim.

    Le 2ᵉ ensemble est nommé « G » (non « F ») : Eq(X,Y)=(∃F)… lie « F », donc un
    « F » dans le codomaine serait capturé.  On α-renomme aussi le témoin de
    Eq(E,G) en « f » (≠ liant « F ») pour que H = graphe_H(f,E) soit sans « F »."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de, equipotent)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_cloture import (
        bijection_de_conjoints)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
        reciproque_fonctionnelle)
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import (
        couple_valeur_dans_graphe)
    ve, vG = _t(e), _t(g_set)
    PE, PG, vf = E.parties(ve), E.parties(vG), var("f")
    H = graphe_H(vf, ve)

    # Eq(E,G) = (∃F)bij(F,E,G) ; α-renomme F→f pour un témoin sans « F »
    heq = N.assume(equipotent(ve, vG))
    ren = alpha_existe("F", "f", est_bijection_de(var("F"), ve, vG))
    heq_f = N.modus_ponens(heq, equivalence_avant(ren))                     # (∃f)bij(f,E,G)

    hbij = N.assume(est_bijection_de(vf, ve, vG))
    fd, bijv = conjonction_elim_gauche(hbij), conjonction_elim_droite(hbij)
    c1 = conjonction_elim_gauche(fd)                                        # est_fonctionnel(f)
    c2 = conjonction_elim_droite(fd)                                        # dom f = E
    c3 = conjonction_elim_gauche(bijv)                                      # injective_dans(f,E)
    c4 = conjonction_elim_droite(bijv)                                      # image(f,E) = G

    # H_app(E,f)  ←  dom f = E
    vx = var("x")
    happ_dom = N.generalisation("x", N.loi_deduction(appartient(vx, ve),
        couple_valeur_dans_graphe(vf, ve, vx)))                            # {dom f=E} ⊢ H_app
    happ = N.modus_ponens(c2, N.loi_deduction(egal(E.dom(vf), ve), happ_dom))

    # est_fonctionnel(f⁻¹)  ←  {func f, dom f=E, inj(f,E)}
    rf = N.loi_deduction(E.est_fonctionnel(vf), N.loi_deduction(egal(E.dom(vf), ve),
        N.loi_deduction(E.injective_dans(vf, ve), reciproque_fonctionnelle(vf, ve))))
    recfunc = N.modus_ponens(c3, N.modus_ponens(c2, N.modus_ponens(c1, rf)))

    # quatre piliers, tous sous Γ = {bij(f,E,G)}
    inj_H = N.modus_ponens(recfunc, N.modus_ponens(happ, H_injective(vf, ve)))
    img_H = N.modus_ponens(c4, N.modus_ponens(c2, N.modus_ponens(c1, H_image(vf, ve, vG))))
    bijH = bijection_de_conjoints(H_fonctionnel(vf, ve), H_domaine(vf, ve), inj_H, img_H)

    # ∃-intro (témoin H) puis élimination du témoin f
    eqP = N.modus_ponens(bijH, N.s5(est_bijection_de(var("F"), PE, PG), H, "F"))
    concl = N.modus_ponens(heq_f,
        existe_elimination(N.loi_deduction(est_bijection_de(vf, ve, vG), eqP), "f"))
    return N.loi_deduction(equipotent(ve, vG), concl)


def cible_equipotent_parties(e="E", g_set="G"):
    """Conclusion attendue : Eq(E,G) ⇒ Eq(𝔓E, 𝔓G)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
    ve, vG = _t(e), _t(g_set)
    return impl(equipotent(ve, vG), equipotent(E.parties(ve), E.parties(vG)))


__all__ = ["graphe_H", "H_fonctionnel", "H_domaine", "H_valeur", "cible_H_valeur",
           "H_injective", "cible_H_injective", "H_image", "cible_H_image",
           "equipotent_parties", "cible_equipotent_parties"]
