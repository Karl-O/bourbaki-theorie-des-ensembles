"""§II.3 — Caractérisation au niveau du COUPLE de la diagonale Δ_X (Bourbaki E II.13).

La diagonale Δ_X (graphe de la correspondance identique Id_X = (Δ_X, X, X), Déf. 8)
est, par axiome, Δ_X = { z | (∃u)(u∈X et z=(u,u)) }.  Ce module en donne la forme
APPLIQUÉE À UN COUPLE — l'analogue, pour la diagonale, de `couple_reciproque`
(pour G⁻¹) et `couple_composee` (pour G'∘G) :

  ⊢ ((a,b) ∈ Δ_X) ⇔ (a∈X et a=b).

C'est la brique de base pour raisonner sur Id_X (réciproque, neutre de la
composition, etc.).

STRATÉGIE.  L'axiome `AXIOME_DIAGONALE` instancié en (X, (a,b)) donne
(a,b)∈Δ_X ⇔ (∃u)(u∈X et (a,b)=(u,u)).  Sous le témoin u : la Proposition 1
((a,b)=(u,u) ⇔ a=u et b=u) fournit a=u, b=u, d'où a∈X [Leibniz] et a=b
[transitivité] ; ∃-élim propre (u absent de la conclusion).  Réciproquement
(témoin u:=a) : de a∈X et a=b on a (a,b)=(a,a) [congruence], donc (∃u)(…).

theorie_ensembles() INCHANGÉE (= 22) : AXIOME_DIAGONALE déjà compté.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, equiv, existe, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    et_congruence_gauche, et_congruence_droite)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import proposition_1
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import couple_composee
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee, egalite_par_extension)


def _tc(t):
    return t if isinstance(t, Terme) else var(t)


def _inst_diag(vX, z):
    """⊢ (z∈Δ_X) ⇔ (∃d0)(d0∈X et z=(d0,d0)).   (instance de AXIOME_DIAGONALE.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE)
    return instancie(instancie(ax, vX), z)


def _inst_recip(vG, z):
    """⊢ (z∈G⁻¹) ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G).   (instance de AXIOME_RECIP.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    return instancie(instancie(ax, vG), z)


def _inst_dom(vG, z):
    """⊢ (z∈pr₁G) ⇔ (∃y)((z,y)∈G).   (instance de AXIOME_DOM ; liant 'y'.)"""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), z)


def _inst_img(vG, z):
    """⊢ (z∈pr₂G) ⇔ (∃x)((x,z)∈G).   (instance de AXIOME_IMG ; liant 'x'.)"""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_IMG), vG), z)


# @livre Ch.II §3.3 Def.8 | E II.13 L.18-20 | PDF p.64
def couple_diagonale(a="a", b="b", x="X"):
    """⊢ ((a,b) ∈ Δ_X) ⇔ (a∈X et a=b).   (Bourbaki E II.13, Déf. 8 ; Δ_X = graphe de Id_X.)

    a, b, X : noms OU termes ; doivent être ≠ d0, w (témoin/trou internes)."""
    va, vb, vX = _tc(a), _tc(b), _tc(x)
    vu = var("d0")                                        # liant de l'axiome (témoin diagonal)
    cple = E.couple(va, vb)
    inst = _inst_diag(vX, cple)                           # (a,b)∈Δ_X ⇔ (∃d0)(d0∈X et (a,b)=(d0,d0))
    body = et(appartient(vu, vX), egal(cple, E.couple(vu, vu)))

    # ── ⇒ : (∃d0)body ⇒ (a∈X et a=b) ────────────────────────────────────────────
    hb = N.assume(body)
    u_in_X = conjonction_elim_gauche(hb)                  # d0∈X
    comps = N.modus_ponens(conjonction_elim_droite(hb),
                           equivalence_avant(proposition_1(va, vb, vu, vu)))   # a=d0 et b=d0
    a_eq_u, b_eq_u = conjonction_elim_gauche(comps), conjonction_elim_droite(comps)
    a_in_X = N.modus_ponens(u_in_X, equivalence_arriere(
        N.modus_ponens(a_eq_u, N.s6(va, vu, "w", appartient(var("w"), vX)))))  # a∈X
    a_eq_b = composer_egalites(a_eq_u, N.modus_ponens(b_eq_u, symetrie(vb, vu)))  # a=d0=b ⇒ a=b
    avant = existe_elimination(
        N.loi_deduction(body, conjonction_intro(a_in_X, a_eq_b)), "d0")        # (∃d0)body ⇒ (a∈X et a=b)

    # ── ⇐ : (a∈X et a=b) ⇒ (∃d0)body  (témoin d0 := a) ──────────────────────────
    h2 = N.assume(et(appartient(va, vX), egal(va, vb)))
    a_in, a_b = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)
    cpl_eq = N.modus_ponens(N.modus_ponens(a_b, symetrie(va, vb)),               # b=a
                            congruence_terme(vb, va, E.couple(va, var("w")), w="w"))  # (a,b)=(a,a)
    ex = N.modus_ponens(conjonction_intro(a_in, cpl_eq), N.s5(body, va, "d0"))   # (∃d0)body
    arriere = N.loi_deduction(et(appartient(va, vX), egal(va, vb)), ex)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def couple_diagonale_cible(a="a", b="b", x="X"):
    """Énoncé visé de `couple_diagonale` (vérification stricte)."""
    va, vb, vX = _tc(a), _tc(b), _tc(x)
    return equiv(appartient(E.couple(va, vb), E.diagonale(vX)),
                 et(appartient(va, vX), egal(va, vb)))


def _diag_recip_incl(vX):
    """⊢ Δ_X⁻¹ ⊂ Δ_X   (INCONDITIONNEL : Δ_X⁻¹ ne contient que des (q,q), q∈X)."""
    vz, vp, vq = var("z"), var("p"), var("q")
    Dr = E.reciproque(E.diagonale(vX))
    rec = _inst_recip(E.diagonale(vX), vz)                # z∈Δ_X⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈Δ_X)
    body = et(egal(vz, E.couple(vp, vq)), appartient(E.couple(vq, vp), E.diagonale(vX)))
    hb = N.assume(body)
    # (q,p)∈Δ_X ⇒ q∈X et q=p :
    qp = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(couple_diagonale(vq, vp, vX)))
    q_in, q_eq_p = conjonction_elim_gauche(qp), conjonction_elim_droite(qp)
    # z = (p,q) = (q,q)   (p=q par symétrie de q=p, congruence sur 1ʳᵉ coord) :
    pq_qq = N.modus_ponens(N.modus_ponens(q_eq_p, symetrie(vq, vp)),           # p=q
                           congruence_terme(vp, vq, E.couple(var("w"), vq), w="w"))  # (p,q)=(q,q)
    z_qq = composer_egalites(conjonction_elim_gauche(hb), pq_qq)               # z=(q,q)
    # (q,q)∈Δ_X  [couple_diagonale ⇐ : q∈X et q=q] :
    qq_in = N.modus_ponens(conjonction_intro(q_in, N.reflexivite(vq)),
                           equivalence_arriere(couple_diagonale(vq, vq, vX)))
    z_in = N.modus_ponens(qq_in, equivalence_arriere(                          # z∈Δ_X
        N.modus_ponens(z_qq, N.s6(vz, E.couple(vq, vq), "w", appartient(var("w"), E.diagonale(vX))))))
    elim = existe_elimination(existe_elimination(N.loi_deduction(body, z_in), "q"), "p")
    z_in2 = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, Dr)), equivalence_avant(rec)), elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, Dr), z_in2))   # Δ_X⁻¹ ⊂ Δ_X


def _diag_recip_contient(vX):
    """⊢ Δ_X ⊂ Δ_X⁻¹   (INCONDITIONNEL : Δ_X ne contient que des (u,u), symétriques)."""
    vz, vu = var("z"), var("u")                          # témoin « u » (≠ d0, w internes de couple_diagonale)
    Dr = E.reciproque(E.diagonale(vX))
    inner_d0 = et(appartient(var("d0"), vX), egal(vz, E.couple(var("d0"), var("d0"))))
    dia = equivalence_transitivite(_inst_diag(vX, vz),    # z∈Δ_X ⇔ (∃u)(u∈X et z=(u,u))
                                   alpha_existe("d0", "u", inner_d0))
    body = et(appartient(vu, vX), egal(vz, E.couple(vu, vu)))
    hb = N.assume(body)
    u_in = conjonction_elim_gauche(hb)
    # (u,u)∈Δ_X  puis (u,u)∈Δ_X⁻¹  [couple_reciproque(Δ_X,u,u) : (u,u)∈Δ_X⁻¹ ⇔ (u,u)∈Δ_X] :
    uu_in_d = N.modus_ponens(conjonction_intro(u_in, N.reflexivite(vu)),
                             equivalence_arriere(couple_diagonale(vu, vu, vX)))   # (u,u)∈Δ_X
    uu_in_r = N.modus_ponens(uu_in_d, equivalence_arriere(couple_reciproque(E.diagonale(vX), "u", "u")))
    z_in = N.modus_ponens(uu_in_r, equivalence_arriere(                          # z∈Δ_X⁻¹
        N.modus_ponens(conjonction_elim_droite(hb),
                       N.s6(vz, E.couple(vu, vu), "w", appartient(var("w"), Dr)))))
    elim = existe_elimination(N.loi_deduction(body, z_in), "u")
    z_in2 = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, E.diagonale(vX))),
                                          equivalence_avant(dia)), elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.diagonale(vX)), z_in2))  # Δ_X ⊂ Δ_X⁻¹


# @livre Ch.II §3.3 Def.8 | E II.13 L.23-24 | PDF p.64
# @livre Ch.R §3 Prop.- | E.R.13 item 4 (la diagonale est symétrique : Δ⁻¹=Δ) | PDF p.316
def diagonale_auto_reciproque(x="X"):
    """⊢ Δ_X⁻¹ = Δ_X.   (Bourbaki E II.13, Déf. 8 : « Id_X est sa propre réciproque ».)

    INCONDITIONNEL : Δ_X⁻¹ et Δ_X ne contiennent que des couples ; double inclusion
    (via `couple_diagonale` / `couple_reciproque`) puis extensionnalité A1."""
    vX = _tc(x)
    ext = extensionnalite_appliquee(E.reciproque(E.diagonale(vX)), E.diagonale(vX))
    return N.modus_ponens(conjonction_intro(_diag_recip_incl(vX), _diag_recip_contient(vX)), ext)


def diagonale_auto_reciproque_cible(x="X"):
    """Énoncé visé : Δ_X⁻¹ = Δ_X."""
    vX = _tc(x)
    return egal(E.reciproque(E.diagonale(vX)), E.diagonale(vX))


# @livre Ch.II §3.3 Def.8 | E II.13 L.21-22 | PDF p.64
def pr1_diagonale(x="X"):
    """⊢ pr₁Δ_X = X.   (Bourbaki E II.13, Déf. 8 : « pr₁Δ_A = pr₂Δ_A = A ».)

    pr₁Δ_X = dom(Δ_X) = { z | (∃y)((z,y)∈Δ_X) } = { z | (∃y)(z∈X et z=y) } = X."""
    vX, vz = _tc(x), var("z")
    # z∈pr₁Δ_X ⇔ (∃y)((z,y)∈Δ_X) ⇔ (∃y)(z∈X et z=y) ⇔ z∈X
    cd = congruence_existe(couple_diagonale(vz, "y", vX), "y")     # (∃y)((z,y)∈Δ_X) ⇔ (∃y)(z∈X et z=y)
    # collapse (∃y)(z∈X et z=y) ⇔ z∈X  (z∈X constant en y ; témoin y:=z) :
    P = appartient(vz, vX)
    body = et(P, egal(vz, var("y")))
    bwd = N.loi_deduction(P, N.modus_ponens(
        conjonction_intro(N.assume(P), N.reflexivite(vz)), N.s5(body, vz, "y")))  # P ⇒ (∃y)body
    fwd = existe_elimination(N.loi_deduction(body, conjonction_elim_gauche(N.assume(body))), "y")
    collapse = conjonction_intro(fwd, bwd)
    char1 = equivalence_transitivite(equivalence_transitivite(_inst_dom(E.diagonale(vX), vz), cd), collapse)
    char_dom = N.generalisation("z", char1)
    char_X = N.generalisation("z", conjonction_intro(N.loi_deduction(P, N.assume(P)),
                                                      N.loi_deduction(P, N.assume(P))))  # (∀z)(z∈X⇔z∈X)
    return egalite_par_extension(char_dom, char_X, E.dom(E.diagonale(vX)), vX)


# @livre Ch.II §3.3 Def.8 | E II.13 L.21-22 | PDF p.64
def pr2_diagonale(x="X"):
    """⊢ pr₂Δ_X = X.   (Bourbaki E II.13, Déf. 8 ; dual de `pr1_diagonale`.)

    pr₂Δ_X = img(Δ_X) = { z | (∃u)((u,z)∈Δ_X) } = { z | (∃u)(u∈X et u=z) } = X."""
    vX, vz = _tc(x), var("z")
    # z∈pr₂Δ_X ⇔ (∃u)((u,z)∈Δ_X) ⇔ (∃u)(u∈X et u=z) ⇔ z∈X
    # liant de AXIOME_IMG = "x" ; on travaille avec « u » (≠ d0, w) par α-renommage.
    img0 = _inst_img(E.diagonale(vX), vz)                          # z∈pr₂Δ_X ⇔ (∃x)((x,z)∈Δ_X)
    img_u = equivalence_transitivite(img0, alpha_existe(
        "x", "u", appartient(E.couple(var("x"), vz), E.diagonale(vX))))   # ⇔ (∃u)((u,z)∈Δ_X)
    cd = congruence_existe(couple_diagonale("u", vz, vX), "u")     # (∃u)((u,z)∈Δ_X) ⇔ (∃u)(u∈X et u=z)
    # collapse (∃u)(u∈X et u=z) ⇔ z∈X  (substitution u:=z, Leibniz sur ∈) :
    body = et(appartient(var("u"), vX), egal(var("u"), vz))
    hb = N.assume(body)
    fwd_body = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(N.modus_ponens(
        conjonction_elim_droite(hb), N.s6(var("u"), vz, "w", appartient(var("w"), vX)))))  # z∈X
    fwd = existe_elimination(N.loi_deduction(body, fwd_body), "u")
    bwd = N.loi_deduction(appartient(vz, vX), N.modus_ponens(
        conjonction_intro(N.assume(appartient(vz, vX)), N.reflexivite(vz)), N.s5(body, vz, "u")))
    collapse = conjonction_intro(fwd, bwd)
    char1 = equivalence_transitivite(equivalence_transitivite(img_u, cd), collapse)
    char_img = N.generalisation("z", char1)
    P = appartient(vz, vX)
    char_X = N.generalisation("z", conjonction_intro(N.loi_deduction(P, N.assume(P)),
                                                     N.loi_deduction(P, N.assume(P))))
    return egalite_par_extension(char_img, char_X, E.img(E.diagonale(vX)), vX)


# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 | PDF p.64
def couple_composee_diagonale(g="G", a="A", x="x", z="z"):
    """⊢ ((x,z) ∈ G∘Δ_A) ⇔ (x∈A et (x,z)∈G).   (E II.13, Déf. 8 ; cœur de Γ∘Id_A=Γ.)

    Composer à droite par l'identité Δ_A = restreindre le domaine de G à A.  Brique
    pour « Γ∘Id_A = Γ » (lorsque A ⊇ pr₁G).  x, z, a, g : noms OU termes (≠ y, d0, w)."""
    vG, vA, vx, vz = _tc(g), _tc(a), _tc(x), _tc(z)
    Gyz = appartient(E.couple(var("y"), vz), vG)
    cc = couple_composee(vG, E.diagonale(vA), vx, vz)    # ((x,z)∈G∘Δ_A) ⇔ (∃y)((x,y)∈Δ_A et (y,z)∈G)
    cong = congruence_existe(et_congruence_gauche(couple_diagonale(vx, "y", vA), Gyz), "y")
    #  ⇔ (∃y)((x∈A et x=y) et (y,z)∈G)
    # collapse (témoin y:=x ; substitution Leibniz sur (·,z)∈G) :
    P, Gxz = appartient(vx, vA), appartient(E.couple(vx, vz), vG)
    body = et(et(P, egal(vx, var("y"))), Gyz)
    hb = N.assume(body)
    left = conjonction_elim_gauche(hb)
    xz = N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(N.modus_ponens(
        conjonction_elim_droite(left), N.s6(vx, var("y"), "w", appartient(E.couple(var("w"), vz), vG)))))
    fwd = existe_elimination(N.loi_deduction(body,
        conjonction_intro(conjonction_elim_gauche(left), xz)), "y")          # (∃y)body ⇒ (x∈A et (x,z)∈G)
    h2 = N.assume(et(P, Gxz))
    ex = N.modus_ponens(conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(h2), N.reflexivite(vx)),
        conjonction_elim_droite(h2)), N.s5(body, vx, "y"))                   # (∃y)body
    bwd = N.loi_deduction(et(P, Gxz), ex)
    collapse = conjonction_intro(fwd, bwd)
    return equivalence_transitivite(equivalence_transitivite(cc, cong), collapse)


def couple_composee_diagonale_cible(g="G", a="A", x="x", z="z"):
    """Énoncé visé : ((x,z)∈G∘Δ_A) ⇔ (x∈A et (x,z)∈G)."""
    vG, vA, vx, vz = _tc(g), _tc(a), _tc(x), _tc(z)
    return equiv(appartient(E.couple(vx, vz), E.composee(vG, E.diagonale(vA))),
                 et(appartient(vx, vA), appartient(E.couple(vx, vz), vG)))


# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 | PDF p.64
def diagonale_composee_couple(g="G", b="B", x="x", z="z"):
    """⊢ ((x,z) ∈ Δ_B∘G) ⇔ ((x,z)∈G et z∈B).   (E II.13, Déf. 8 ; dual : Id à gauche.)

    Composer à gauche par l'identité Δ_B = restreindre l'image de G à B.  Brique
    pour « Id_B∘Γ = Γ » (lorsque B ⊇ pr₂G).  x, z, b, g : noms OU termes (≠ y, d0, w)."""
    vG, vB, vx, vz = _tc(g), _tc(b), _tc(x), _tc(z)
    Gxy = appartient(E.couple(vx, var("y")), vG)
    cc = couple_composee(E.diagonale(vB), vG, vx, vz)    # ((x,z)∈Δ_B∘G) ⇔ (∃y)((x,y)∈G et (y,z)∈Δ_B)
    cong = congruence_existe(et_congruence_droite(Gxy, couple_diagonale(var("y"), vz, vB)), "y")
    #  ⇔ (∃y)((x,y)∈G et (y∈B et y=z))
    # collapse (témoin y:=z ; substitutions Leibniz sur (x,·)∈G et ·∈B) :
    Gxz, zB = appartient(E.couple(vx, vz), vG), appartient(vz, vB)
    body = et(Gxy, et(appartient(var("y"), vB), egal(var("y"), vz)))
    hb = N.assume(body)
    right = conjonction_elim_droite(hb)                 # y∈B et y=z
    y_eq_z = conjonction_elim_droite(right)
    xz = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(N.modus_ponens(
        y_eq_z, N.s6(var("y"), vz, "w", appartient(E.couple(vx, var("w")), vG)))))   # (x,z)∈G
    z_in_B = N.modus_ponens(conjonction_elim_gauche(right), equivalence_avant(N.modus_ponens(
        y_eq_z, N.s6(var("y"), vz, "w", appartient(var("w"), vB)))))                 # z∈B
    fwd = existe_elimination(N.loi_deduction(body, conjonction_intro(xz, z_in_B)), "y")
    h2 = N.assume(et(Gxz, zB))
    ex = N.modus_ponens(conjonction_intro(conjonction_elim_gauche(h2),
        conjonction_intro(conjonction_elim_droite(h2), N.reflexivite(vz))), N.s5(body, vz, "y"))
    bwd = N.loi_deduction(et(Gxz, zB), ex)
    collapse = conjonction_intro(fwd, bwd)
    return equivalence_transitivite(equivalence_transitivite(cc, cong), collapse)


def diagonale_composee_couple_cible(g="G", b="B", x="x", z="z"):
    """Énoncé visé : ((x,z)∈Δ_B∘G) ⇔ ((x,z)∈G et z∈B)."""
    vG, vB, vx, vz = _tc(g), _tc(b), _tc(x), _tc(z)
    return equiv(appartient(E.couple(vx, vz), E.composee(E.diagonale(vB), vG)),
                 et(appartient(E.couple(vx, vz), vG), appartient(vz, vB)))


def pr1_diagonale_cible(x="X"):
    """Énoncé visé : pr₁Δ_X = X."""
    return egal(E.dom(E.diagonale(_tc(x))), _tc(x))


def pr2_diagonale_cible(x="X"):
    """Énoncé visé : pr₂Δ_X = X."""
    return egal(E.img(E.diagonale(_tc(x))), _tc(x))


__all__ = ["couple_diagonale", "couple_diagonale_cible",
           "diagonale_auto_reciproque", "diagonale_auto_reciproque_cible",
           "pr1_diagonale", "pr1_diagonale_cible",
           "pr2_diagonale", "pr2_diagonale_cible",
           "couple_composee_diagonale", "couple_composee_diagonale_cible",
           "diagonale_composee_couple", "diagonale_composee_couple_cible"]
