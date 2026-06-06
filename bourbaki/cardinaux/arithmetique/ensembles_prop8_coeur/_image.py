"""CŒUR Prop. 8 — conjoint IMAGE : image(g, A×{0}) = B×{0}   (g = h|(A×{0})).

C'est la partie DURE du CAS 1 (h(*)=*).  On montre l'égalité par extension à
partir de la caractérisation membre

    z ∈ image(g, A×{0})  ⇔  (∃u)(u∈A×{0} et (u,z)∈h)        [AXIOME_IMAGE + membre_g]

et de l'équivalence  (∃u)(u∈A×{0} et (u,z)∈h)  ⇔  z ∈ B×{0} :

  ⇒ (z « atteint » depuis A×{0}) :  z∈image(h,A⊔{∅})=B⊔{∅}, donc z∈B×{0} ou z=* ;
        on EXCLUT z=* car sinon (u,*)∈h avec u∈A×{0}, et (*,*)∈h (h(*)=*) ; par
        injectivité de h (h(u)=*=h(*)), u=*, contredisant u∈A×{0} (*∉A×{0}).
  ⇐ (z∈B×{0}) :  z∈B×{0}⊂B⊔{∅}=image(h,A⊔{∅}), donc (u,z)∈h pour un u∈A⊔{∅} ;
        u∈A×{0} ou u=* ; on EXCLUT u=* car sinon (*,z)∈h et (*,*)∈h (h(*)=*) ⇒
        z=* par fonctionnalité, contredisant z∈B×{0} (*∉B×{0}).  Donc u∈A×{0}.

Hypothèses utilisées (toutes « sur h » + CAS 1) : est_fonctionnel(h),
injective_dans(h,A⊔{∅}), dom h = A⊔{∅}, image(h,A⊔{∅}) = B⊔{∅}, h(*) = *.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, ou, non, appartient, existe, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie, cas, disj_syll_thm)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                                          composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.familles.ensembles_somme_disjointe import ZERO, UN, somme_disjointe
from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_caracterisation, valeur_dans_graphe
from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import somme_un_plus_point
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._g import (
    A0_terme, G_RESTR, membre_g_ssi_t, _cut)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._marqueurs import (
    m_dans_AS, m_hors_A0, mm_dans_h, m_diff_si_A0)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)


def _B0(b):
    return E.produit(var(b) if isinstance(b, str) else b, E.singleton(ZERO))


def _couple_donne_valeur(point, val, h="h"):
    """{(point,val)∈h, est_fonctionnel(h)} ⊢ h(point) = val.

    De (point,val)∈h on a (∃y)((point,y)∈h) (témoin val) ; valeur_caracterisation
    (sens ⇒, y:=val) donne val=h(point), d'où h(point)=val."""
    vh = var(h)
    pv_in = N.assume(appartient(E.couple(point, val), vh))    # (point,val)∈h
    hp = E.valeur(vh, point)
    exy = N.modus_ponens(pv_in, N.s5(appartient(E.couple(point, var("y")), vh), val, "y"))
    vc = valeur_caracterisation(vh, point)                    # {h fonct,(∃y)..}⊢((point,y)∈h)⇔(y=h(point))
    vc_fwd = equivalence_avant(vc)                            # (point,y)∈h ⇒ y=h(point)  [y libre]
    vc_inst = instancie(N.generalisation("y", N.loi_deduction(
        appartient(E.couple(point, var("y")), vh),
        N.modus_ponens(N.assume(appartient(E.couple(point, var("y")), vh)), vc_fwd))), val)
    val_eq_hp = N.modus_ponens(pv_in, vc_inst)                # val=h(point)
    res = N.modus_ponens(val_eq_hp, symetrie(val, hp))        # h(point)=val
    # décharger (∃y)((point,y)∈h) introduite par valeur_caracterisation
    return _cut(existe("y", appartient(E.couple(point, var("y")), vh)), exy, res)


def _membre_image_g(a, z, h="h"):
    """⊢ (z ∈ image(g, A×{0})) ⇔ (∃u)(u∈A×{0} et (u,z)∈h).   (g = h|(A×{0}) ; clos.)

    AXIOME_IMAGE : z∈g⟨A×{0}⟩ ⇔ (∃u)(u∈A×{0} et (u,z)∈g) ; puis (u,z)∈g ⇔
    (u∈A×{0} et (u,z)∈h), et u∈A×{0} ∧ (u∈A×{0} et (u,z)∈h) se réduit à
    (u∈A×{0} et (u,z)∈h)."""
    vh = var(h)
    A0 = A0_terme(a)
    g = G_RESTR(a, h)
    vz = z
    vu = var("u")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, g), A0), vz)   # z∈g⟨A0⟩ ⇔ (∃x)(x∈A0 et (x,z)∈g)
    ren = alpha_existe("x", "u", et(appartient(var("x"), A0),
                                    appartient(E.couple(var("x"), vz), g)))
    img = equivalence_transitivite(img0, ren)   # z∈g⟨A0⟩ ⇔ (∃u)(u∈A0 et (u,z)∈g)

    # inner : (u∈A0 et (u,z)∈g) ⇔ (u∈A0 et (u,z)∈h)
    inL = et(appartient(vu, A0), appartient(E.couple(vu, vz), g))
    inR = et(appartient(vu, A0), appartient(E.couple(vu, vz), vh))
    mss = membre_g_ssi_t(a, vu, vz, h)          # (u,z)∈g ⇔ (u∈A0 et (u,z)∈h)
    # ⇒
    hL = N.assume(inL)
    u_inA0 = conjonction_elim_gauche(hL)
    uz_g = conjonction_elim_droite(hL)
    uz_h = conjonction_elim_droite(N.modus_ponens(uz_g, equivalence_avant(mss)))
    fwd_in = N.loi_deduction(inL, conjonction_intro(u_inA0, uz_h))
    # ⇐
    hR = N.assume(inR)
    u_inA0_r = conjonction_elim_gauche(hR)
    uz_h_r = conjonction_elim_droite(hR)
    uz_g_r = N.modus_ponens(conjonction_intro(u_inA0_r, uz_h_r), equivalence_arriere(mss))
    bwd_in = N.loi_deduction(inR, conjonction_intro(u_inA0_r, uz_g_r))
    inner_equiv = conjonction_intro(fwd_in, bwd_in)            # inL ⇔ inR
    # (∃u)inL ⇔ (∃u)inR
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    ex_equiv = congruence_existe(inner_equiv, "u")
    return equivalence_transitivite(img, ex_equiv)            # z∈g⟨A0⟩ ⇔ (∃u)(u∈A0 et (u,z)∈h)


def _hyps(a, b, h):
    """Les hypothèses « sur h » + CAS 1, comme formules (pour assume/cut)."""
    vh = var(h)
    va = var(a) if isinstance(a, str) else a
    vb = var(b) if isinstance(b, str) else b
    AS = somme_disjointe(va, E.singleton(E.VIDE))    # A⊔{∅}
    BS = somme_disjointe(vb, E.singleton(E.VIDE))    # B⊔{∅}
    return {
        "fun": E.est_fonctionnel(vh),
        "inj": E.injective_dans(vh, AS),
        "dom": egal(E.dom(vh), AS),
        "img": egal(E.image(vh, AS), BS),
        "fix": egal(E.valeur(vh, _STAR), _STAR),
        "AS": AS, "BS": BS, "va": va, "vb": vb, "vh": vh,
    }


def _z_in_image_h(a, b, z, h):
    """{u∈A×{0}, (u,z)∈h, dom h=A⊔{∅}, image h=B⊔{∅} (via img-hyp implicite)}
       ⊢ z ∈ image(h, A⊔{∅}).

    De u∈A×{0}⊂A⊔{∅} et (u,z)∈h, on a z∈image(h, A⊔{∅}) (AXIOME_IMAGE ⇐)."""
    H = _hyps(a, b, h)
    vh, AS = H["vh"], H["AS"]
    A0 = A0_terme(a)
    vu, vz = var("u"), z
    # u∈A⊔{∅}  (A×{0}⊂A⊔{∅})
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._incl import A0_inclus_AS
    u_inAS = N.modus_ponens(N.assume(appartient(vu, A0)), instancie(A0_inclus_AS(a), vu))
    uz_h = N.assume(appartient(E.couple(vu, vz), vh))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, vh), AS), vz)   # z∈h⟨AS⟩ ⇔ (∃x)(x∈AS et (x,z)∈h)
    body = et(appartient(vu, AS), appartient(E.couple(vu, vz), vh))
    ex = N.modus_ponens(conjonction_intro(u_inAS, uz_h),
                        N.s5(et(appartient(var("x"), AS), appartient(E.couple(var("x"), vz), vh)),
                             vu, "x"))                          # (∃x)(x∈AS et (x,z)∈h)
    return N.modus_ponens(ex, equivalence_arriere(car))         # z∈image(h,AS)


def _z_dans_BS(b, z):
    """⊢ (z∈B×{0}) ⇒ z∈B⊔{∅}.   (B×{0} ⊂ B⊔{∅}, instancié au point z ; clos.)"""
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._incl import A0_inclus_AS
    return instancie(A0_inclus_AS(b), z)                       # z∈B×{0} ⇒ z∈B⊔{∅}


def _exclure_z_egal_m(a, b, z, h):
    """Sous {u∈A×{0}, (u,z)∈h} + h-hyps (fun, inj, dom, fix) : ⊢ ¬(z = *).

    Si z=*, alors (u,*)∈h ; h(u)=* (couple_donne_valeur) ; or h(*)=* (fix), donc
    h(u)=h(*) ; injectivité (u,*∈A⊔{∅}) ⇒ u=*, contredisant u∈A×{0} (*∉A×{0})."""
    H = _hyps(a, b, h)
    vh, AS = H["vh"], H["AS"]
    A0 = A0_terme(a)
    vu, vz = var("u"), z
    m = _STAR
    u_inA0 = N.assume(appartient(vu, A0))                      # u∈A×{0}
    uz_h = N.assume(appartient(E.couple(vu, vz), vh))          # (u,z)∈h
    hzm = N.assume(egal(vz, m))                                # z=*
    # (u,*)∈h  (réécrire z→* dans (u,z)∈h)
    um_h = N.modus_ponens(uz_h, equivalence_avant(N.modus_ponens(
        hzm, N.s6(vz, m, "w", appartient(E.couple(vu, var("w")), vh)))))   # (u,*)∈h
    # h(u)=*  via couple_donne_valeur (point=u, val=*)
    hu_eq_m = _decharge_couple_valeur(vu, m, h, um_h)          # h(u)=*  [hyps: (u,*)∈h, fun]
    # h(*)=*  (fix) ; donc h(u)=h(*)
    fix = N.assume(H["fix"])                                   # h(*)=*
    hu_eq_hm = composer_egalites(hu_eq_m, N.modus_ponens(fix, symetrie(E.valeur(vh, m), m)))  # h(u)=h(*)
    # u∈A⊔{∅}, *∈A⊔{∅}
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._incl import A0_inclus_AS
    u_inAS = N.modus_ponens(u_inA0, instancie(A0_inclus_AS(a), vu))   # u∈A⊔{∅}
    m_inAS = m_dans_AS(a)                                      # *∈A⊔{∅}
    hinj = N.assume(H["inj"])                                  # injective_dans(h,A⊔{∅})
    inj_inst = instancie(instancie(hinj, vu), m)              # ((u,*∈AS et h(u)=h(*))⇒u=*)
    u_eq_m = N.modus_ponens(conjonction_intro(
        conjonction_intro(u_inAS, m_inAS), hu_eq_hm), inj_inst)   # u=*
    # contradiction avec ¬(u=*)  (m_diff_si_A0)
    n_u_eq_m = m_diff_si_A0(a, vu)                            # {u∈A×{0}} ⊢ ¬(u=*)
    falso = N.modus_ponens(u_eq_m, N.modus_ponens(n_u_eq_m,
        N.s2(non(egal(vu, m)), non(egal(vz, m)))))            # (u=*)⇒¬(z=*) appliqué
    # falso = ¬(z=*) sous hyp z=* (+ u-hyps) ; collapse
    return N.modus_ponens(N.loi_deduction(egal(vz, m), falso), N.s1(non(egal(vz, m))))


def _decharge_couple_valeur(point, val, h, couple_thm):
    """De couple_thm = Γ ⊢ (point,val)∈h, déduit Γ∪{fun} ⊢ h(point)=val.

    couple_donne_valeur a l'hypothèse (point,val)∈h ; on la remplace par couple_thm."""
    cdv = _couple_donne_valeur(point, val, h)                 # {(point,val)∈h, fun} ⊢ h(point)=val
    return _cut(appartient(E.couple(point, val), var(h)), couple_thm, cdv)


def _z_in_BS_from_image(a, b, z, h):
    """{u∈A×{0}, (u,z)∈h, image h=B⊔{∅}} (+ A0⊂AS clos) ⊢ z ∈ B⊔{∅}.

    z∈image(h,A⊔{∅}) (_z_in_image_h), réécrit par image h=B⊔{∅}."""
    H = _hyps(a, b, h)
    vh, AS, BS = H["vh"], H["AS"], H["BS"]
    vz = z
    z_in_imgh = _z_in_image_h(a, b, z, h)                     # z∈image(h,AS)
    himg = N.assume(H["img"])                                 # image h=B⊔{∅}
    return N.modus_ponens(z_in_imgh, equivalence_avant(N.modus_ponens(
        himg, N.s6(E.image(vh, AS), BS, "w", appartient(vz, var("w"))))))   # z∈B⊔{∅}


def _fwd_image(a, b, z, h):
    """⊢ (∃u)(u∈A×{0} et (u,z)∈h) ⇒ z∈B×{0}   (sous h-hyps + CAS 1).

    Sous le témoin u : z∈B⊔{∅}=(B×{0})⊎{*} ; on exclut z=* (_exclure_z_egal_m),
    donc z∈B×{0}."""
    H = _hyps(a, b, h)
    vh = H["vh"]
    A0 = A0_terme(a)
    B0 = _B0(b)
    vz = z
    vu = var("u")
    m = _STAR
    body = et(appartient(vu, A0), appartient(E.couple(vu, vz), vh))
    hb = N.assume(body)
    u_inA0 = conjonction_elim_gauche(hb)
    uz_h = conjonction_elim_droite(hb)
    # z∈B⊔{∅}
    z_in_BS = _decharge2(a, b, z, h, u_inA0, uz_h,
                         _z_in_BS_from_image(a, b, z, h))
    # z∈B×{0} ∨ z=*
    sup = somme_un_plus_point(b, vz)                          # z∈B⊔{∅} ⇔ (z∈B×{0} ∨ z=*)
    z_or = N.modus_ponens(z_in_BS, equivalence_avant(sup))    # z∈B×{0} ∨ z=*
    # ¬(z=*)
    n_zm = _decharge2(a, b, z, h, u_inA0, uz_h, _exclure_z_egal_m(a, b, z, h))
    # disjonctive : (z∈B0 ∨ z=*) , ¬(z=*) ⊢ z∈B0
    # commuter en (z=* ∨ z∈B0) puis disj_syll_thm(z=*, z∈B0)
    z_or_comm = N.modus_ponens(z_or, N.s3(appartient(vz, B0), egal(vz, m)))   # z=* ∨ z∈B0
    dss = disj_syll_thm(egal(vz, m), appartient(vz, B0))      # (z=*∨z∈B0)⇒(¬(z=*)⇒z∈B0)
    z_in_B0 = N.modus_ponens(n_zm, N.modus_ponens(z_or_comm, dss))   # z∈B×{0}
    inner = N.loi_deduction(body, z_in_B0)
    return existe_elimination(inner, "u")                     # (∃u)body ⇒ z∈B×{0}


def _decharge2(a, b, z, h, u_inA0_thm, uz_h_thm, thm):
    """Remplace dans `thm` les hypothèses u∈A×{0} et (u,z)∈h par les preuves données
    (extraits du corps body) — pour que les hypothèses restantes soient « sur h »."""
    vh = var(h)
    A0 = A0_terme(a)
    vu, vz = var("u"), z
    out = thm
    cu = appartient(vu, A0)
    cz = appartient(E.couple(vu, vz), vh)
    if cu in out.hypotheses:
        out = _cut(cu, u_inA0_thm, out)
    if cz in out.hypotheses:
        out = _cut(cz, uz_h_thm, out)
    return out


def _exclure_u_egal_m_pt(a, b, z, h, point):
    """Sous {(point,z)∈h, z∈B×{0}, dom h=A⊔{∅}, h fonctionnel, h(*)=*} : ⊢ ¬(point=*).

    Si point=*, alors (*,z)∈h ; et (*,*)∈h (mm_dans_h, via h(*)=* et dom h) ; par
    fonctionnalité de h, z=* ; or z∈B×{0} et *∉B×{0} (m_hors_A0 côté B), absurde.
    `point` = le terme antécédent (peut être un nom autre que « u »)."""
    H = _hyps(a, b, h)
    vh, AS = H["vh"], H["AS"]
    B0 = _B0(b)
    vu, vz = point, z
    m = _STAR
    uz_h = N.assume(appartient(E.couple(vu, vz), vh))         # (u,z)∈h
    z_inB0 = N.assume(appartient(vz, B0))                     # z∈B×{0}
    hum = N.assume(egal(vu, m))                               # u=*
    # (*,z)∈h  (réécrire u→* dans (u,z)∈h)
    mz_h = N.modus_ponens(uz_h, equivalence_avant(N.modus_ponens(
        hum, N.s6(vu, m, "w", appartient(E.couple(var("w"), vz), vh)))))    # (*,z)∈h
    # (*,*)∈h  (mm_dans_h : hyps *∈AS, dom h=AS, h(*)=*)
    mm = mm_dans_h(AS, h)                                     # (*,*)∈h
    mm = _cut(appartient(m, AS), m_dans_AS(a), mm)            # décharge *∈AS
    # h fonctionnel : (*,z)∈h et (*,*)∈h ⇒ z=*
    hfun = N.assume(H["fun"])
    fun_inst = instancie(instancie(instancie(hfun, m), vz), m)   # ((*,z)∈h et (*,*)∈h)⇒z=*
    z_eq_m = N.modus_ponens(conjonction_intro(mz_h, mm), fun_inst)   # z=*
    # contradiction : z∈B×{0} et z=* ⇒ *∈B×{0}, mais ¬(*∈B×{0})
    m_inB0 = N.modus_ponens(z_inB0, equivalence_avant(N.modus_ponens(
        z_eq_m, N.s6(vz, m, "w", appartient(var("w"), B0)))))   # *∈B×{0}
    n_m_inB0 = m_hors_A0(b)                                   # ¬(*∈B×{0})
    falso = N.modus_ponens(m_inB0, N.modus_ponens(n_m_inB0,
        N.s2(non(appartient(m, B0)), non(egal(vu, m)))))      # (*∈B0)⇒¬(u=*) appliqué
    return N.modus_ponens(N.loi_deduction(egal(vu, m), falso), N.s1(non(egal(vu, m))))


def _bwd_image(a, b, z, h):
    """⊢ z∈B×{0} ⇒ (∃u)(u∈A×{0} et (u,z)∈h)   (sous h-hyps + CAS 1).

    z∈B×{0}⊂B⊔{∅}=image(h,A⊔{∅}) ⇒ (∃u)(u∈A⊔{∅} et (u,z)∈h) ; on exclut u=*
    (_exclure_u_egal_m) donc u∈A×{0}."""
    H = _hyps(a, b, h)
    vh, AS = H["vh"], H["AS"]
    A0 = A0_terme(a)
    B0 = _B0(b)
    vz = z
    # Témoin AS-side nommé « uu » (le liant interne « u » de somme_un_plus_point
    # capturerait un point nommé « u ») ; on alpha-renomme en « u » à la fin.
    vu = var("uu")
    m = _STAR
    z_inB0 = N.assume(appartient(vz, B0))                     # z∈B×{0}
    # z∈B⊔{∅}
    z_inBS = N.modus_ponens(z_inB0, _z_dans_BS(b, z))         # z∈B⊔{∅}
    # z∈image(h,A⊔{∅})  via image h=B⊔{∅}  (réécrire BS→image h)
    himg = N.assume(H["img"])                                 # image h=B⊔{∅}
    eq_img = N.modus_ponens(himg, symetrie(E.image(vh, AS), H["BS"]))   # B⊔{∅}=image h
    z_in_imgh = N.modus_ponens(z_inBS, equivalence_avant(N.modus_ponens(
        eq_img, N.s6(H["BS"], E.image(vh, AS), "w", appartient(vz, var("w"))))))   # z∈image(h,AS)
    # (∃uu)(uu∈AS et (uu,z)∈h)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, vh), AS), vz)   # z∈h⟨AS⟩ ⇔ (∃x)(x∈AS et (x,z)∈h)
    ren = alpha_existe("x", "uu", et(appartient(var("x"), AS),
                                     appartient(E.couple(var("x"), vz), vh)))
    car_u = equivalence_transitivite(car, ren)               # z∈h⟨AS⟩ ⇔ (∃uu)(uu∈AS et (uu,z)∈h)
    ex_u = N.modus_ponens(z_in_imgh, equivalence_avant(car_u))   # (∃uu)(uu∈AS et (uu,z)∈h)
    # sous le témoin uu : uu∈AS et (uu,z)∈h
    bodyAS = et(appartient(vu, AS), appartient(E.couple(vu, vz), vh))
    hb = N.assume(bodyAS)
    u_inAS = conjonction_elim_gauche(hb)
    uz_h = conjonction_elim_droite(hb)
    # uu∈A×{0} ∨ uu=*
    sup = somme_un_plus_point(a, vu)                          # uu∈A⊔{∅} ⇔ (uu∈A×{0} ∨ uu=*)
    u_or = N.modus_ponens(u_inAS, equivalence_avant(sup))     # uu∈A×{0} ∨ uu=*
    # ¬(uu=*)  (exclusion ; décharge (uu,z)∈h et z∈B×{0})  — _exclure_u_egal_m
    # utilise le point interne « u » ; on l'instancie en remplaçant via generalisation.
    n_um = _exclure_u_egal_m_pt(a, b, z, h, vu)
    n_um = _cut(appartient(E.couple(vu, vz), vh), uz_h, n_um)
    n_um = _cut(appartient(vz, B0), z_inB0, n_um)
    # disj syll : (uu∈A0 ∨ uu=*), ¬(uu=*) ⊢ uu∈A0
    u_or_comm = N.modus_ponens(u_or, N.s3(appartient(vu, A0), egal(vu, m)))   # uu=* ∨ uu∈A0
    dss = disj_syll_thm(egal(vu, m), appartient(vu, A0))
    u_inA0 = N.modus_ponens(n_um, N.modus_ponens(u_or_comm, dss))   # uu∈A×{0}
    # (∃uu)(uu∈A×{0} et (uu,z)∈h)
    wit = conjonction_intro(u_inA0, uz_h)
    targ_body = et(appartient(vu, A0), appartient(E.couple(vu, vz), vh))
    ex_target = N.modus_ponens(wit, N.s5(targ_body, vu, "uu"))   # (∃uu)(uu∈A×{0} et (uu,z)∈h)
    inner = N.loi_deduction(bodyAS, ex_target)
    from_ex = N.modus_ponens(ex_u, existe_elimination(inner, "uu"))   # (∃uu)(...) [sous z∈B0]
    # alpha-rename (∃uu) → (∃u) pour coller à _membre_image_g
    al = alpha_existe("uu", "u", et(appartient(var("uu"), A0),
                                    appartient(E.couple(var("uu"), vz), vh)))
    from_ex = N.modus_ponens(from_ex, equivalence_avant(al))   # (∃u)(u∈A×{0} et (u,z)∈h)
    return N.loi_deduction(appartient(vz, B0), from_ex)       # z∈B×{0} ⇒ (∃u)(u∈A×{0} et (u,z)∈h)


def g_image(a="A", b="B", h="h"):
    """{h fonctionnel, injective_dans(h,A⊔{∅}), dom h=A⊔{∅}, image h=B⊔{∅}, h(*)=*}
                                            ⊢ image(g, A×{0}) = B×{0}.

    Conjoint IMAGE du CAS 1 (g = h|(A×{0})).  Égalité par extension à partir de
    l'équivalence membre  z∈image(g,A×{0}) ⇔ z∈B×{0}  (via _membre_image_g pour
    réduire à (∃u)(u∈A×{0} et (u,z)∈h), puis _fwd_image / _bwd_image)."""
    vh = var(h)
    A0 = A0_terme(a)
    B0 = _B0(b)
    g = G_RESTR(a, h)
    vz = var("z")
    # z∈image(g,A0) ⇔ (∃u)(u∈A0 et (u,z)∈h)
    mem = _membre_image_g(a, vz, h)
    # (∃u)(u∈A0 et (u,z)∈h) ⇔ z∈B0
    eqv = conjonction_intro(_fwd_image(a, b, vz, h), _bwd_image(a, b, vz, h))
    # z∈image(g,A0) ⇔ z∈B0
    z_equiv = equivalence_transitivite(mem, eqv)
    char = N.generalisation("z", z_equiv)                    # (∀z)(z∈image(g,A0) ⇔ z∈B0)
    self_B0 = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, B0)), a_implique_a(appartient(vz, B0))))
    return egalite_par_extension(char, self_B0, E.image(g, A0), B0, "z")


__all__ = ["g_image"]
