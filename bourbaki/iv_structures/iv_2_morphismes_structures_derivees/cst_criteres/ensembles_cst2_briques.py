"""§IV.1.2 — CST2, briques d'étage : bijectivité de l'extension aux parties.

────────────────────────────────────────────────────────────────────────────────
Invariant de récurrence Q(F,X,Y) := ((est_fonctionnel F ∧ dom F = X) ∧
(est_fonctionnel F⁻¹ ∧ F⟨X⟩ = Y)) — la bijectivité au VOCABULAIRE des briques
préimage-image (ii_3_2_reciproque) : « injectif » y est est_fonctionnel(F⁻¹),
pont vers injective_dans/est_bijection_de reporté au sommet du générateur.

Brique d'étage 𝔓 : `ext_parties_bijective_q(g,A,A',xi)` — F = ext_parties_
réelle(g,A,xi) = graphe_terme(𝔓A, g⟨xi⟩) et
    { est_fonctionnel(g), dom g = A, est_fonctionnel(g⁻¹), g⟨A⟩ = A' }
        ⊢  Q(F, 𝔓A, 𝔓A')
(les 4 hyps = exactement Q(g,A,A') moins le conjoint dom, honnêtes, coupées
par l'IH dans le générateur).  Routes : injectivité par f⁻¹⟨f⟨·⟩⟩=Id
(image_reciproque_image_egal_si_injective), surjectivité par le témoin
f⁻¹⟨Z⟩ (image_image_reciproque_egal_si_surjective + inclus_domaine).
⚠️ α-discipline : tout appel de brique sur un objet nommé z/x (liants de
inclus/extension) passe par un RELAIS-α (nom frais Zq/uq/vq/zq, généraliser
puis instancier) — la surface instanciée reste sans capture.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_image_domaine import (
    _image_croissante_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    image_reciproque_image_egal_si_injective, image_image_reciproque_egal_si_surjective,
    image_reciproque_inclus_domaine,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme, graphe_terme_fonctionnel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def bijection_q(F, X, Y):
    """Q(F,X,Y) := ((func F ∧ dom F=X) ∧ (func F⁻¹ ∧ F⟨X⟩=Y))."""
    F, X, Y = _t(F), _t(X), _t(Y)
    return et(et(E.est_fonctionnel(F), egal(E.dom(F), X)),
              et(E.est_fonctionnel(E.reciproque(F)), egal(E.image(F, X), Y)))


def _sub_parties(X_t, A_t):
    """{X ∈ 𝔓A} ⊢ X ⊂ A.   (X sans « z » libre : liant d'inclus préservé.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)
    inst = instancie(instancie(ax, _t(A_t)), _t(X_t))
    return N.modus_ponens(N.assume(appartient(_t(X_t), E.parties(_t(A_t)))),
                          equivalence_avant(inst))


def _happ(g_t, A_t, X_t, incl_thm):
    """{dom g = A} ∪ hyps(incl_thm) ⊢ H_app(X,g) = (∀x)(x∈X ⇒ (x,g(x))∈g).

    incl_thm ⊢ X ⊂ A ; x∈X ⇒ x∈A = dom g ⇒ (∃y)(x,y)∈g ⇒ (x,g(x))∈g."""
    vg, vA, vx = _t(g_t), _t(A_t), var("x")
    hd = N.assume(egal(E.dom(vg), vA))
    hx = N.assume(appartient(vx, _t(X_t)))
    xA = N.modus_ponens(hx, instancie(incl_thm, vx))
    x_dom = N.modus_ponens(xA, equivalence_arriere(N.modus_ponens(
        hd, N.s6(E.dom(vg), vA, "w", appartient(vx, var("w"))))))
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    ex = N.modus_ponens(x_dom, equivalence_avant(
        instancie(instancie(dom_ax, vg), vx)))
    couple = _cut(valeur_dans_graphe(vg, vx), ex)          # (x, g(x)) ∈ g
    return N.generalisation("x", N.loi_deduction(appartient(vx, _t(X_t)), couple))


# @livre Ch.IV §1.2 Crit.CST2 | E IV.2 L.33-34 | PDF p.205  (étage 𝔓 de CST2 : si g est une bijection de A sur A', son extension aux parties est une bijection de 𝔓A sur 𝔓A' — au vocabulaire Q, hyps honnêtes)
def ext_parties_bijective_q(g, a, ap, xi="xg1"):
    """{ func g, dom g=A, func g⁻¹, g⟨A⟩=A' } ⊢ Q(ext_P(g), 𝔓A, 𝔓A').

    F = graphe_terme(𝔓A, g⟨xi⟩, xi).  func et dom : kit C54 (CLOS).
    func F⁻¹ : (u,v),(u,z)∈F⁻¹ ⇒ v,z∈𝔓A ∧ u=g⟨v⟩=g⟨z⟩ ⇒ v=g⁻¹⟨g⟨v⟩⟩=
    g⁻¹⟨g⟨z⟩⟩=z (Id sur les parties si injective).  F⟨𝔓A⟩=𝔓A' : → par
    croissance de l'image + g⟨A⟩=A' ; ← par le témoin g⁻¹⟨Z⟩ (⊂ dom, et
    g⟨g⁻¹⟨Z⟩⟩=Z si surjective).  ⚠️ g, A, A' sans u,v,z,x,y,w,p,q libres."""
    vg, vA, vAp = _t(g), _t(a), _t(ap)
    PA, PAp = E.parties(vA), E.parties(vAp)
    T = E.image(vg, var(xi))
    F = E.graphe_terme(PA, T, xi)
    Hfunc = N.assume(E.est_fonctionnel(vg))
    Hdom = N.assume(egal(E.dom(vg), vA))
    Hrec = N.assume(E.est_fonctionnel(E.reciproque(vg)))
    Himg = N.assume(egal(E.image(vg, vA), vAp))

    c1 = graphe_terme_fonctionnel(PA, T, xi, "y")          # func F        [CLOS]
    c2 = graphe_terme_domaine(PA, T, xi, "y", "z")         # dom F = 𝔓A   [CLOS]

    # ── c3 : func F⁻¹ — cœur aux noms frais uq/vq/zq puis re-liage u/v/z ──────
    def _membre(nu, nv):
        return membre_graphe_terme(PA, T, nu, nv, xi, "y")

    corps3 = et(appartient(E.couple(var("uq"), var("vq")), E.reciproque(F)),
                appartient(E.couple(var("uq"), var("zq")), E.reciproque(F)))
    h3 = N.assume(corps3)
    d1 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_gauche(h3),
        equivalence_avant(couple_reciproque(F, "uq", "vq"))),
        equivalence_avant(_membre("vq", "uq")))            # vq∈𝔓A ∧ uq=g⟨vq⟩
    d2 = N.modus_ponens(N.modus_ponens(
        conjonction_elim_droite(h3),
        equivalence_avant(couple_reciproque(F, "uq", "zq"))),
        equivalence_avant(_membre("zq", "uq")))            # zq∈𝔓A ∧ uq=g⟨zq⟩
    gv_gz = composer_egalites(
        N.modus_ponens(conjonction_elim_droite(d1),
                       symetrie(var("uq"), E.image(vg, var("vq")))),
        conjonction_elim_droite(d2))                       # g⟨vq⟩ = g⟨zq⟩
    cong = N.modus_ponens(gv_gz, congruence_terme(
        E.image(vg, var("vq")), E.image(vg, var("zq")),
        E.image(E.reciproque(vg), var("w"))))              # g⁻¹⟨g⟨vq⟩⟩ = g⁻¹⟨g⟨zq⟩⟩

    def _id_parties(nom, appartenance):                    # g⁻¹⟨g⟨nom⟩⟩ = nom
        incl = _cut(_sub_parties(var(nom), vA), appartenance)
        happ = _happ(vg, vA, var(nom), incl)
        brique = image_reciproque_image_egal_si_injective(vg, var(nom))
        return N.modus_ponens(Hrec, N.modus_ponens(happ, brique))

    eq_v = _id_parties("vq", conjonction_elim_gauche(d1))
    eq_z = _id_parties("zq", conjonction_elim_gauche(d2))
    v_eq_z = composer_egalites(composer_egalites(
        N.modus_ponens(eq_v, symetrie(
            E.image(E.reciproque(vg), E.image(vg, var("vq"))), var("vq"))),
        cong), eq_z)                                       # vq = zq
    core3 = N.loi_deduction(corps3, v_eq_z)
    gen3 = N.generalisation("uq", N.generalisation("vq", N.generalisation("zq", core3)))
    re3 = instancie(instancie(instancie(gen3, var("u")), var("v")), var("z"))
    c3 = N.generalisation("u", N.generalisation("v", N.generalisation("z", re3)))
    assert c3.conclusion == E.est_fonctionnel(E.reciproque(F)), "c3 : ≠ func F⁻¹"

    # ── c4 : F⟨𝔓A⟩ = 𝔓A' — extension au nom frais Zq puis relais-α vers z ────
    Im = E.image(F, PA)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, F), PA), var("Zq"))
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)

    # → : sous le témoin x : x∈𝔓A ∧ (x,Zq)∈F ⇒ Zq∈𝔓A'
    corps4 = et(appartient(var("x"), PA), appartient(E.couple(var("x"), var("Zq")), F))
    hb = N.assume(corps4)
    mx = N.modus_ponens(conjonction_elim_droite(hb),
                        equivalence_avant(_membre("x", "Zq")))
    z_eq = conjonction_elim_droite(mx)                     # Zq = g⟨x⟩
    x_sub = _cut(_sub_parties(var("x"), vA), conjonction_elim_gauche(hb))
    croiss = instancie(N.generalisation(
        "Xq", _image_croissante_terme(vg, var("Xq"), vA)), var("x"))
    gx_gA = N.modus_ponens(x_sub, croiss)                  # g⟨x⟩ ⊂ g⟨A⟩
    gx_Ap = N.modus_ponens(gx_gA, equivalence_avant(N.modus_ponens(
        Himg, N.s6(E.image(vg, vA), vAp, "w",
                   inclus(E.image(vg, var("x")), var("w"))))))   # g⟨x⟩ ⊂ A'
    z_Ap = N.modus_ponens(gx_Ap, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(var("Zq"), E.image(vg, var("x")), "w",
                   inclus(var("w"), vAp)))))               # Zq ⊂ A'
    z_PAp = N.modus_ponens(z_Ap, equivalence_arriere(
        instancie(instancie(ax_p, vAp), var("Zq"))))       # Zq ∈ 𝔓A'
    fwd_imp = existe_elimination(N.loi_deduction(corps4, z_PAp), "x")
    hZi = N.assume(appartient(var("Zq"), Im))
    fwd = N.loi_deduction(appartient(var("Zq"), Im), N.modus_ponens(
        N.modus_ponens(hZi, equivalence_avant(car)), fwd_imp))

    # ← : Zq∈𝔓A' ⇒ témoin wt = g⁻¹⟨Zq⟩ : wt∈𝔓A ∧ Zq=g⟨wt⟩ ⇒ Zq∈Im
    wt = E.image(E.reciproque(vg), var("Zq"))
    hZp = N.assume(appartient(var("Zq"), PAp))
    z_sub_Ap = N.modus_ponens(hZp, equivalence_avant(
        instancie(instancie(ax_p, vAp), var("Zq"))))       # Zq ⊂ A'
    z_sub_gA = N.modus_ponens(z_sub_Ap, equivalence_avant(N.modus_ponens(
        N.modus_ponens(Himg, symetrie(E.image(vg, vA), vAp)),
        N.s6(vAp, E.image(vg, vA), "w", inclus(var("Zq"), var("w"))))))  # Zq ⊂ g⟨A⟩
    wt_sub = N.modus_ponens(Hdom,
                            image_reciproque_inclus_domaine(vg, var("Zq"), vA))
    wt_PA = N.modus_ponens(wt_sub, equivalence_arriere(
        instancie(instancie(ax_p, vA), wt)))               # wt ∈ 𝔓A
    surj = N.modus_ponens(z_sub_gA, N.modus_ponens(
        Hfunc, image_image_reciproque_egal_si_surjective(vg, var("Zq"), vA)))
    z_gwt = N.modus_ponens(surj, symetrie(E.image(vg, wt), var("Zq")))   # Zq = g⟨wt⟩
    mg_wt = instancie(instancie(N.generalisation(
        "uq", N.generalisation("vq", _membre("uq", "vq"))), wt), var("Zq"))
    wtZ_F = N.modus_ponens(conjonction_intro(wt_PA, z_gwt),
                           equivalence_arriere(mg_wt))     # (wt, Zq) ∈ F
    ex = N.modus_ponens(conjonction_intro(wt_PA, wtZ_F), N.s5(corps4, wt, "x"))
    bwd = N.loi_deduction(appartient(var("Zq"), PAp),
                          N.modus_ponens(ex, equivalence_arriere(car)))

    # relais-α Zq → z, puis extension (liant canonique z, A1)
    pair_z = instancie(N.generalisation("Zq", conjonction_intro(fwd, bwd)), var("z"))
    thm_u = N.generalisation("z", pair_z)
    R = appartient(var("z"), PAp)
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    c4 = egalite_par_extension(thm_u, thm_v, Im, PAp, x="z")   # F⟨𝔓A⟩ = 𝔓A'

    res = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))
    assert res.conclusion == bijection_q(F, PA, PAp), "ext_parties : ≠ Q"
    attendu = {Hfunc.conclusion, Hdom.conclusion, Hrec.conclusion, Himg.conclusion}
    assert set(res.hypotheses) <= attendu, "ext_parties : hyps non honnêtes"
    return res


__all__ = ["bijection_q", "ext_parties_bijective_q"]
