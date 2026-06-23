"""§II.3.2 — Correspondance réciproque : G⁻¹ et son théorème caractéristique.

⊢ ((x,y) ∈ G⁻¹) ⇔ ((y,x) ∈ G)  — l'échange des coordonnées, base de l'image
réciproque et de la fonction réciproque.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, appartient, existe, subst_f, Terme
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, congruence_existe,
                                      alpha_existe)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _inst_dom(g, x):
    """⊢ (x ∈ pr₁G) ⇔ (∃y)((x,y) ∈ G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, g), x)


def _inst_img(g, y):
    """⊢ (y ∈ pr₂G) ⇔ (∃x)((x,y) ∈ G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


def _inst_recip(g, z):
    """⊢ (z ∈ G⁻¹) ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    return instancie(instancie(ax, g), z)


def couple_reciproque(g="G", u="u", v="v"):
    """⊢ ((u,v) ∈ G⁻¹) ⇔ ((v,u) ∈ G).   (E.II.41 ; u, v noms OU termes, distincts de p, q.)"""
    from bourbaki.logique.formule import Terme
    vG = g if isinstance(g, Terme) else var(g)
    vu = u if isinstance(u, Terme) else var(u)
    vv = v if isinstance(v, Terme) else var(v)
    vp, vq = var("p"), var("q")
    inst = _inst_recip(vG, E.couple(vu, vv))           # (u,v)∈G⁻¹ ⇔ (∃p)(∃q)((u,v)=(p,q) et (q,p)∈G)
    body = et(egal(E.couple(vu, vv), E.couple(vp, vq)), appartient(E.couple(vq, vp), vG))

    # ── ⇒ : (∃p)(∃q)body ⇒ (v,u)∈G ─────────────────────────────────────────────
    hb = N.assume(body)
    comps = N.modus_ponens(conjonction_elim_gauche(hb),
                           couple_egal_implique_composantes(vu, vv, "p", "q"))   # u=p et v=q
    cong = composer_egalites(
        N.modus_ponens(conjonction_elim_droite(comps),                        # v=q
                       congruence_terme(vv, vq, E.couple(var("w"), vu))),      # (v,u)=(q,u)
        N.modus_ponens(conjonction_elim_gauche(comps),                        # u=p
                       congruence_terme(vu, vp, E.couple(vq, var("w")))))      # (q,u)=(q,p)
    vu_in = N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(N.modus_ponens(
        cong, N.s6(E.couple(vv, vu), E.couple(vq, vp), "w", appartient(var("w"), vG)))))  # (v,u)∈G
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, vu_in), "q"), "p")

    # ── ⇐ : (v,u)∈G ⇒ (∃p)(∃q)body ─────────────────────────────────────────────
    h = N.assume(appartient(E.couple(vv, vu), vG))
    wit = conjonction_intro(N.reflexivite(E.couple(vu, vv)), h)    # (u,v)=(u,v) et (v,u)∈G = (u|p)(v|q)body
    gbody = subst_f(vu, "p", body)
    full = N.modus_ponens(N.modus_ponens(wit, N.s5(gbody, vv, "q")),
                          N.s5(existe("q", body), vu, "p"))         # (∃p)(∃q)body
    arriere = N.loi_deduction(appartient(E.couple(vv, vu), vG), full)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def pr1_reciproque(g="G"):
    """⊢ pr₁(G⁻¹) = pr₂G.   (E.II.41 ; dom(G⁻¹) = img(G), SANS hypothèses.)

    z∈dom(G⁻¹) ⇔ (∃t)((t,z)∈G)  (réciproque + couple_reciproque) ;
    z∈img(G)   ⇔ (∃t)((t,z)∈G)  (axiome image pr₂) ; même R → A1."""
    vG = _T(g)
    vz = var("z")
    Grec = E.reciproque(vG)
    # char_dom : (∀z)(z∈dom(G⁻¹) ⇔ (∃t)((t,z)∈G))
    dom_ax = _inst_dom(Grec, vz)                                  # z∈dom(G⁻¹) ⇔ (∃y)((z,y)∈G⁻¹)
    cr = couple_reciproque(g, "z", "t")                           # ((z,t)∈G⁻¹) ⇔ ((t,z)∈G)
    char1 = equivalence_transitivite(dom_ax, alpha_existe("y", "t",
                appartient(E.couple(vz, var("y")), Grec)))        # ⇔ (∃t)((z,t)∈G⁻¹)
    char1 = equivalence_transitivite(char1, congruence_existe(cr, "t"))   # ⇔ (∃t)((t,z)∈G)
    char_dom = N.generalisation("z", char1)
    # char_img : (∀z)(z∈pr₂G ⇔ (∃t)((t,z)∈G))
    img_ax = _inst_img(vG, vz)                                    # z∈pr₂G ⇔ (∃x)((x,z)∈G)
    char2 = equivalence_transitivite(img_ax, alpha_existe("x", "t",
                appartient(E.couple(var("x"), vz), vG)))          # ⇔ (∃t)((t,z)∈G)
    char_img = N.generalisation("z", char2)
    return egalite_par_extension(char_dom, char_img, E.dom(Grec), E.img(vG))


def pr2_reciproque(g="G"):
    """⊢ pr₂(G⁻¹) = pr₁G.   (E.II.41 ; img(G⁻¹) = dom(G), SANS hypothèses.)

    z∈img(G⁻¹) ⇔ (∃t)((z,t)∈G)  (réciproque + couple_reciproque) ;
    z∈dom(G)   ⇔ (∃t)((z,t)∈G)  (axiome domaine pr₁) ; même R → A1."""
    vG = _T(g)
    vz = var("z")
    Grec = E.reciproque(vG)
    # char_img : (∀z)(z∈img(G⁻¹) ⇔ (∃t)((z,t)∈G))
    img_ax = _inst_img(Grec, vz)                                  # z∈img(G⁻¹) ⇔ (∃x)((x,z)∈G⁻¹)
    cr = couple_reciproque(g, "t", "z")                           # ((t,z)∈G⁻¹) ⇔ ((z,t)∈G)
    char1 = equivalence_transitivite(img_ax, alpha_existe("x", "t",
                appartient(E.couple(var("x"), vz), Grec)))        # ⇔ (∃t)((t,z)∈G⁻¹)
    char1 = equivalence_transitivite(char1, congruence_existe(cr, "t"))   # ⇔ (∃t)((z,t)∈G)
    char_img = N.generalisation("z", char1)
    # char_dom : (∀z)(z∈pr₁G ⇔ (∃t)((z,t)∈G))
    dom_ax = _inst_dom(vG, vz)                                    # z∈pr₁G ⇔ (∃y)((z,y)∈G)
    char2 = equivalence_transitivite(dom_ax, alpha_existe("y", "t",
                appartient(E.couple(vz, var("y")), vG)))          # ⇔ (∃t)((z,t)∈G)
    char_dom = N.generalisation("z", char2)
    return egalite_par_extension(char_img, char_dom, E.img(Grec), E.dom(vG))


def _inst_recip_z(g, z):
    """⊢ (z ∈ G⁻¹) ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    return instancie(instancie(ax, g), z)


def _inst_produit(gx, gy, z):
    """⊢ (z ∈ gx×gy) ⇔ (∃p)(∃q)((z=(p,q) et p∈gx) et q∈gy)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, gx), gy), z)


def reciproque_produit(x="X", y="Y"):
    """⊢ (X×Y)⁻¹ = Y×X.   (E.II.41 : « réciproque d'un produit », SANS hypothèses.)

    z∈(X×Y)⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈X×Y) ⇔ (∃p)(∃q)(z=(p,q) et (q∈X et p∈Y)) ;
    z∈Y×X    ⇔ (∃p)(∃q)((z=(p,q) et p∈Y) et q∈X) ⇔ même R ; égalité par A1."""
    from bourbaki.logique.formule import et
    from bourbaki.logique.tactiques.tactiques_abrege2 import (equivalence_symetrie, comm_et, assoc_et,
                                   et_congruence_droite)
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    vX, vY = _T(x), _T(y)
    vz, va, vb = var("z"), var("a"), var("b")
    Grec = E.reciproque(E.produit(vX, vY))
    eq = egal(vz, E.couple(va, vb))                        # coord. a,b (≠ binders p,q des lemmes)
    bX, aY = appartient(vb, vX), appartient(va, vY)
    R = et(eq, et(bX, aY))                                 # z=(a,b) et (b∈X et a∈Y)

    # char_L : (∀z)(z∈(X×Y)⁻¹ ⇔ (∃a)(∃b)R)
    recL0 = _inst_recip_z(E.produit(vX, vY), vz)          # ⇔ (∃p)(∃q)(eq et (q,p)∈X×Y)  [binders p,q]
    recL = equivalence_transitivite(recL0,                # α-renomme p→a puis q→b
        alpha_existe("p", "a", existe("q",
            et(egal(vz, E.couple(var("p"), var("q"))),
               appartient(E.couple(var("q"), var("p")), E.produit(vX, vY))))))
    recL = equivalence_transitivite(recL, congruence_existe(
        alpha_existe("q", "b", et(egal(vz, E.couple(va, var("q"))),
            appartient(E.couple(var("q"), va), E.produit(vX, vY)))), "a"))
    mem = couple_dans_produit_ssi(vb, va, vX, vY)          # ((b,a)∈X×Y) ⇔ (b∈X et a∈Y)
    bodyL = et_congruence_droite(eq, mem)                  # (eq et (b,a)∈X×Y) ⇔ R
    charL = equivalence_transitivite(recL,
        congruence_existe(congruence_existe(bodyL, "b"), "a"))
    char_L = N.generalisation("z", charL)

    # char_R : (∀z)(z∈Y×X ⇔ (∃a)(∃b)R)
    prodR0 = _inst_produit(vY, vX, vz)                   # ⇔ (∃p)(∃q)((eq et p∈Y) et q∈X)  [binders p,q]
    prodR = equivalence_transitivite(prodR0,             # α-renomme p→a puis q→b
        alpha_existe("p", "a", existe("q",
            et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vY)),
               appartient(var("q"), vX)))))
    prodR = equivalence_transitivite(prodR, congruence_existe(
        alpha_existe("q", "b", et(et(egal(vz, E.couple(va, var("q"))), appartient(va, vY)),
            appartient(var("q"), vX))), "a"))
    B0 = et(et(eq, aY), bX)
    rew = equivalence_transitivite(
        equivalence_symetrie(assoc_et(eq, aY, bX)),        # B0 ⇔ (eq et (a∈Y et b∈X))
        et_congruence_droite(eq, comm_et(aY, bX)))         # ⇔ (eq et (b∈X et a∈Y)) = R
    charR = equivalence_transitivite(prodR,
        congruence_existe(congruence_existe(rew, "b"), "a"))
    char_R = N.generalisation("z", charR)

    return egalite_par_extension(char_L, char_R, Grec, E.produit(vY, vX))


__all__ = ["couple_reciproque", "pr1_reciproque", "pr2_reciproque",
           "reciproque_produit"]
