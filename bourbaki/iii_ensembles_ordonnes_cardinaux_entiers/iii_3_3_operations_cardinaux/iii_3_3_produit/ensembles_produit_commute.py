"""§II.2 / §III.3 — Commutativité du produit (équipotence) : Eq(X×Y, Y×X).

L'application témoin est l'ÉCHANGE  s : z ↦ (pr₂z, pr₁z)  de X×Y dans Y×X.  Son
graphe est  S := graphe_terme(X×Y, (pr₂k, pr₁k), "k")  (= {(k,(pr₂k,pr₁k)) | k∈X×Y},
machinerie C54, E.II.46).  On montre que S est :
  • FONCTIONNEL                 (graphe_terme_fonctionnel) ;
  • de DOMAINE X×Y              (swap_graphe_domaine : dom S = X×Y) ;
  • INJECTIF sur X×Y            (swap_graphe_injective : s(u)=s(u') ⇒ u=u' : les
                                 projections se lisent mutuellement, et un élément
                                 du produit se reconstruit u=(pr₁u,pr₂u)) ;
  • d'IMAGE = Y×X              (swap_graphe_image : image(S, X×Y) = Y×X, double
                                 inclusion ; surjectivité : tout w∈Y×X est
                                 s((pr₂w,pr₁w))).
Les quatre conjoints donnent est_bijection_de(S, X×Y, Y×X), d'où (∃F)bij = Eq.

ÉTAT (round 9) — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_produit_commute.py) :
  • swap_graphe_fonctionnel  (clos)         — S fonctionnel ;
  • swap_graphe_domaine      (clos)         — dom S = X×Y ;
  • swap_graphe_valeur       {u∈X×Y}        — S(u) = (pr₂u, pr₁u) ;
  • membre_produit_pr1/pr2   {z∈X×Y}        — pr₁z∈X, pr₂z∈Y ;
  • membre_produit_egal_couple {z∈X×Y}      — z = (pr₁z, pr₂z) ;
  • swap_graphe_injective    (clos)         — injective_dans(S, X×Y) ;
  • swap_graphe_image        (clos)         — image(S, X×Y) = Y×X ;
  • swap_est_bijection       (clos)         — est_bijection_de(S, X×Y, Y×X) ;
  • eq_produit_commute       (clos)         — Eq(X×Y, Y×X).
FIX du désaccord de liants (round 8 → round 9) : toute la preuve d'injectivité ET
d'image est menée en liants UNIFORMES a,b (helpers _projection_*_ab,
_membre_produit_*_ab), de sorte que pr[a,b] de swap_graphe_valeur COÏNCIDE
structurellement avec la reconstruction de u (le noyau ne canonicalise pas α sur les
τ-termes : pr₂u[a,b] ≠ pr₂u[x,y]).  Surjectivité : tout (c,d)∈Y×X a l'antécédent
(d,c)∈X×Y, avec S((d,c))=(pr₂(d,c),pr₁(d,c))=(c,d).

NB BINDERS : les projections du terme T sont écrites pr₂(k,"a","b"), pr₁(k,"a","b")
avec liants internes a,b — DISTINCTS des liants u,v,z de est_fonctionnel, du liant
y de valeur(F,·)=τy((·,y)∈F), et des liants x,y des axiomes dom/img/image — de
sorte qu'aucune capture ne survient lors des substitutions/instanciations.

LEMME-CLÉ réutilisable (reconstruction d'un élément du produit) :
  • membre_produit_pr1/pr2     {z∈X×Y} ⊢ pr₁z∈X,  pr₂z∈Y ;
  • membre_produit_egal_couple {z∈X×Y} ⊢ z = (pr₁z, pr₂z).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, appartient, existe, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (existe_elimination, congruence_existe,
                                      alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import projection_premiere, projection_seconde
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_couple_dans
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_caracterisation
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit, couple_dans_produit_ssi
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_produit(gx, gy, z):
    """⊢ (z ∈ gx×gy) ⇔ (∃p)(∃q)((z=(p,q) et p∈gx) et q∈gy)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, gx), gy), z)


def syllogisme_(thm_ab, thm_bc):
    """⊢ A⇒B, ⊢ B⇒C  ⟹  ⊢ A⇒C  (sans préfixe ; A, C peuvent contenir des hyps)."""
    return syllogisme(thm_ab, thm_bc)


# ── Reconstruction d'un élément du produit : z = (pr₁z, pr₂z) ─────────────────
def membre_produit_pr1(x="X", y="Y", z="z"):
    """{z ∈ X×Y} ⊢ pr₁z ∈ X.   (la 1ʳᵉ projection d'un élément du produit est dans X.)"""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vX, vY, vz)                 # z∈X×Y ⇔ (∃p)(∃q)((z=(p,q) et p∈X) et q∈Y)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    pX = conjonction_elim_droite(conjonction_elim_gauche(hb))    # p∈X
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr1(var("w")))),
        projection_premiere("p", "q"))                          # pr₁z = p
    pr1z_in = N.modus_ponens(pX, equivalence_arriere(
        N.modus_ponens(pr1z_p, N.s6(E.pr1(vz), vp, "w", appartient(var("w"), vX)))))
    inner = N.loi_deduction(body, pr1z_in)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme_(equivalence_avant(inst), chaine))


def membre_produit_pr2(x="X", y="Y", z="z"):
    """{z ∈ X×Y} ⊢ pr₂z ∈ Y.   (la 2ᵉ projection d'un élément du produit est dans Y.)"""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vX, vY, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    qY = conjonction_elim_droite(hb)                            # q∈Y
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr2(var("w")))),
        projection_seconde("p", "q"))                           # pr₂z = q
    pr2z_in = N.modus_ponens(qY, equivalence_arriere(
        N.modus_ponens(pr2z_q, N.s6(E.pr2(vz), vq, "w", appartient(var("w"), vY)))))
    inner = N.loi_deduction(body, pr2z_in)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme_(equivalence_avant(inst), chaine))


def membre_produit_egal_couple(x="X", y="Y", z="z"):
    """{z ∈ X×Y} ⊢ z = (pr₁z, pr₂z).   (un élément du produit se reconstruit de ses projections.)"""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vX, vY, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr1(var("w")))),
        projection_premiere("p", "q"))                          # pr₁z = p
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr2(var("w")))),
        projection_seconde("p", "q"))                           # pr₂z = q
    c1 = N.modus_ponens(pr1z_p, congruence_terme(E.pr1(vz), vp,
                                                 E.couple(var("w"), E.pr2(vz))))   # (pr₁z,pr₂z)=(p,pr₂z)
    c2 = N.modus_ponens(pr2z_q, congruence_terme(E.pr2(vz), vq, E.couple(vp, var("w"))))  # (p,pr₂z)=(p,q)
    pr_eq_pq = composer_egalites(c1, c2)                        # (pr₁z,pr₂z)=(p,q)
    z_eq_pr = composer_egalites(zpq, N.modus_ponens(pr_eq_pq,   # z=(p,q)=(pr₁z,pr₂z)
        symetrie(E.couple(E.pr1(vz), E.pr2(vz)), E.couple(vp, vq))))
    inner = N.loi_deduction(body, z_eq_pr)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme_(equivalence_avant(inst), chaine))


# ── Le graphe d'échange S = graphe_terme(X×Y, (pr₂k, pr₁k), "k") ──────────────
def _swap(k="k"):
    """T = (pr₂k, pr₁k)  (le terme échangeant les coordonnées, liants pr internes a,b)."""
    vk = var(k)
    return E.couple(E.pr2(vk, "a", "b"), E.pr1(vk, "a", "b"))


def _swap_graphe(x, y):
    """S := graphe_terme(X×Y, (pr₂k, pr₁k), "k")  (graphe de z↦(pr₂z,pr₁z))."""
    return E.graphe_terme(E.produit(_t(x), _t(y)), _swap("k"), "k")


def swap_graphe_fonctionnel(x="X", y="Y"):
    """⊢ S est fonctionnel,   S = graphe de z↦(pr₂z,pr₁z).   (cas C54.)"""
    A = E.produit(_t(x), _t(y))
    return graphe_terme_fonctionnel(A, _swap("k"), "k", "t")


def swap_graphe_domaine(x="X", y="Y"):
    """⊢ dom(S) = X×Y.   (z↦(pr₂z,pr₁z) est définie sur tout X×Y.)

    z∈dom S ⇔ (∃m)((z,m)∈S) ⇔ (∃m)(z∈X×Y et m=T[z]) ⇔ z∈X×Y.  Par extension."""
    A = E.produit(_t(x), _t(y))
    swap = _swap("k")
    xb, z = "k", "z"
    G = E.graphe_terme(A, swap, xb)
    vz, vm = var(z), var("m")
    Tz = subst_t(vz, xb, swap)                                  # T[z]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, G), vz)              # z∈dom S ⇔ (∃y)((z,y)∈S)
    ren = alpha_existe("y", "m", appartient(E.couple(vz, var("y")), G))   # ⇔ (∃m)((z,m)∈S)
    dom_car = equivalence_transitivite(dom_car, ren)
    mem = membre_graphe_terme(A, swap, z, "m", xb, "yb")        # ((z,m)∈S) ⇔ (z∈X×Y et m=T[z])
    ex_eq = congruence_existe(mem, "m")
    inA = appartient(vz, A)
    body = et(inA, egal(vm, Tz))
    fwd = existe_elimination(
        N.loi_deduction(body, conjonction_elim_gauche(N.assume(body))), "m")
    h_inA = N.assume(inA)
    wit = conjonction_intro(h_inA, N.reflexivite(Tz))
    bwd = N.loi_deduction(inA, N.modus_ponens(wit, N.s5(body, Tz, "m")))
    ex_inA = conjonction_intro(fwd, bwd)                        # (∃m)(z∈X×Y et m=T[z]) ⇔ z∈X×Y
    chain = equivalence_transitivite(dom_car, equivalence_transitivite(ex_eq, ex_inA))
    selfA = N.generalisation(z, conjonction_intro(a_implique_a(inA), a_implique_a(inA)))
    char_dom = N.generalisation(z, chain)
    return egalite_par_extension(char_dom, selfA, E.dom(G), A)


def swap_graphe_valeur(x="X", y="Y", u="u"):
    """{u ∈ X×Y} ⊢ S(u) = (pr₂u, pr₁u).   (la valeur de l'échange en u.)

    (u,T[u])∈S (couple) → u dans le domaine ; valeur_caracterisation (C46, sous
    « S fonctionnel ») donne T[u]=S(u) ; symétrie conclut.  Recette de
    graphe_terme_valeur, ré-implémentée localement avec les liants a,b de swap."""
    A = E.produit(_t(x), _t(y))
    swap = _swap("k")
    xb = "k"
    F = E.graphe_terme(A, swap, xb)
    vu = _t(u)
    Tu = subst_t(vu, xb, swap)                                 # T[u] = (pr₂u, pr₁u)
    fu = E.valeur(F, vu)                                       # S(u)
    cpl = graphe_terme_couple_dans(A, swap, u, xb, "t")        # {u∈X×Y} ⊢ (u,T[u])∈S
    # u dans le domaine : (∃y)((u,y)∈F), témoin y:=T[u]
    dom_membre = N.modus_ponens(cpl, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))
    vc = valeur_caracterisation(F, vu)                         # y libre
    vc_all = N.generalisation("y", vc)                        # (∀y)(((u,y)∈F)⇔(y=S(u)))
    vc_Tu = instancie(vc_all, Tu)                             # ((u,T[u])∈F) ⇔ (T[u]=S(u))
    Tu_fu = N.modus_ponens(cpl, equivalence_avant(vc_Tu))     # T[u]=S(u)  [hyps S func, u∈X×Y]
    fu_Tu = N.modus_ponens(Tu_fu, symetrie(Tu, fu))          # S(u)=T[u]
    fu_Tu = N.modus_ponens(swap_graphe_fonctionnel(x, y),
                           N.loi_deduction(E.est_fonctionnel(F), fu_Tu))
    fu_Tu = N.modus_ponens(dom_membre,
        N.loi_deduction(existe("y", appartient(E.couple(vu, var("y")), F)), fu_Tu))
    return fu_Tu                                               # {u∈X×Y} ⊢ S(u)=(pr₂u,pr₁u)


# ── Projections en liants UNIFORMES a,b (alignées sur swap_graphe_valeur) ──────
# swap_graphe_valeur sort S(u) = (pr₂u[a,b], pr₁u[a,b]) ; pour que la reconstruction
# de u et la lecture des composantes COÏNCIDENT structurellement (le noyau ne
# canonicalise pas α sur les τ-termes : pr₂u[a,b] ≠ pr₂u[x,y]), tout le raisonnement
# d'injectivité/image est mené en liants a,b.  Versions-locales de projection_*.
def _projection_premiere_ab(u, v, bx="a", by="b"):
    """⊢ pr₁((u,v), bx, by) = u.   (Bourbaki pr₁(u,v)=u, liants bx,by ≠ u,v.)"""
    vu, vv, vbx, vby = _t(u), _t(v), var(bx), var(by)
    cuv = E.couple(vu, vv)
    R = existe(by, egal(cuv, E.couple(vbx, vby)))            # corps de pr₁((u,v)), lié par bx
    dur = couple_egal_implique_composantes(vu, vv, vbx, vby)  # ((u,v)=(bx,by)) ⇒ (u=bx et v=by)
    heq = N.assume(egal(cuv, E.couple(vbx, vby)))
    xu = N.modus_ponens(conjonction_elim_gauche(N.modus_ponens(heq, dur)), symetrie(vu, vbx))
    inner = N.loi_deduction(egal(cuv, E.couple(vbx, vby)), xu)   # ((u,v)=(bx,by)) ⇒ (bx=u)
    F = existe_elimination(inner, by)                          # R ⇒ (bx=u)
    hxu = N.assume(egal(vbx, vu))
    uv_xv = N.modus_ponens(N.modus_ponens(hxu, symetrie(vbx, vu)),
                           congruence_terme(vu, vbx, E.couple(var("w"), vv)))  # (u,v)=(bx,v)
    Rx = N.modus_ponens(uv_xv, N.s5(egal(cuv, E.couple(vbx, vby)), vv, by))    # (∃by)((u,v)=(bx,by))
    B = N.loi_deduction(egal(vbx, vu), Rx)                     # (bx=u) ⇒ R
    gen = N.generalisation(bx, conjonction_intro(F, B))       # (∀bx)(R ⇔ (bx=u))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vbx, vu), bx))  # τbx(R) = τbx(bx=u)
    ex = N.modus_ponens(N.reflexivite(vu), N.s5(egal(vbx, vu), vu, bx))   # (∃bx)(bx=u)
    tau_u = N.modus_ponens(ex, N.existe_temoin(egal(vbx, vu), bx))        # τbx(bx=u)=u
    return composer_egalites(tau_eq, tau_u)                   # pr₁((u,v), bx, by) = u


def _projection_seconde_ab(u, v, bx="a", by="b"):
    """⊢ pr₂((u,v), bx, by) = v.   (Bourbaki pr₂(u,v)=v, liants bx,by ≠ u,v.)"""
    vu, vv, vbx, vby = _t(u), _t(v), var(bx), var(by)
    cuv = E.couple(vu, vv)
    R = existe(bx, egal(cuv, E.couple(vbx, vby)))            # corps de pr₂((u,v)), lié par by
    dur = couple_egal_implique_composantes(vu, vv, vbx, vby)  # ((u,v)=(bx,by)) ⇒ (u=bx et v=by)
    heq = N.assume(egal(cuv, E.couple(vbx, vby)))
    yv = N.modus_ponens(conjonction_elim_droite(N.modus_ponens(heq, dur)), symetrie(vv, vby))
    inner = N.loi_deduction(egal(cuv, E.couple(vbx, vby)), yv)   # ((u,v)=(bx,by)) ⇒ (by=v)
    F = existe_elimination(inner, bx)                          # R ⇒ (by=v)
    hyv = N.assume(egal(vby, vv))
    uv_uy = N.modus_ponens(N.modus_ponens(hyv, symetrie(vby, vv)),
                           congruence_terme(vv, vby, E.couple(vu, var("w"))))  # (u,v)=(u,by)
    Ry = N.modus_ponens(uv_uy, N.s5(egal(cuv, E.couple(vbx, vby)), vu, bx))    # (∃bx)((u,v)=(bx,by))
    B = N.loi_deduction(egal(vby, vv), Ry)                     # (by=v) ⇒ R
    gen = N.generalisation(by, conjonction_intro(F, B))       # (∀by)(R ⇔ (by=v))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vby, vv), by))  # τby(R) = τby(by=v)
    ex = N.modus_ponens(N.reflexivite(vv), N.s5(egal(vby, vv), vv, by))
    tau_v = N.modus_ponens(ex, N.existe_temoin(egal(vby, vv), by))
    return composer_egalites(tau_eq, tau_v)                   # pr₂((u,v), bx, by) = v


def _membre_produit_egal_couple_ab(x, y, z, bx="a", by="b"):
    """{z ∈ X×Y} ⊢ z = (pr₁z[bx,by], pr₂z[bx,by]).   (reconstruction, liants bx,by.)"""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    vp, vq = var("p"), var("q")
    pr1z, pr2z = E.pr1(vz, bx, by), E.pr2(vz, bx, by)
    inst = _inst_produit(vX, vY, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr1(var("w"), bx, by))),
        _projection_premiere_ab("p", "q", bx, by))             # pr₁z = p
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr2(var("w"), bx, by))),
        _projection_seconde_ab("p", "q", bx, by))             # pr₂z = q
    c1 = N.modus_ponens(pr1z_p, congruence_terme(pr1z, vp, E.couple(var("w"), pr2z)))
    c2 = N.modus_ponens(pr2z_q, congruence_terme(pr2z, vq, E.couple(vp, var("w"))))
    pr_eq_pq = composer_egalites(c1, c2)                       # (pr₁z,pr₂z)=(p,q)
    z_eq_pr = composer_egalites(zpq, N.modus_ponens(pr_eq_pq,
        symetrie(E.couple(pr1z, pr2z), E.couple(vp, vq))))
    inner = N.loi_deduction(body, z_eq_pr)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme(equivalence_avant(inst), chaine))


def _membre_produit_pr1_ab(x, y, z, bx="a", by="b"):
    """{z ∈ X×Y} ⊢ pr₁z[bx,by] ∈ X."""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    pr1z = E.pr1(vz, bx, by)
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vX, vY, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    pX = conjonction_elim_droite(conjonction_elim_gauche(hb))    # p∈X
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr1(var("w"), bx, by))),
        _projection_premiere_ab("p", "q", bx, by))             # pr₁z = p
    pr1z_in = N.modus_ponens(pX, equivalence_arriere(
        N.modus_ponens(pr1z_p, N.s6(pr1z, vp, "w", appartient(var("w"), vX)))))
    inner = N.loi_deduction(body, pr1z_in)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme(equivalence_avant(inst), chaine))


def _membre_produit_pr2_ab(x, y, z, bx="a", by="b"):
    """{z ∈ X×Y} ⊢ pr₂z[bx,by] ∈ Y."""
    vX, vY = _t(x), _t(y)
    vz = _t(z)
    pr2z = E.pr2(vz, bx, by)
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vX, vY, vz)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)), appartient(vq, vY))
    hb = N.assume(body)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    qY = conjonction_elim_droite(hb)                            # q∈Y
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr2(var("w"), bx, by))),
        _projection_seconde_ab("p", "q", bx, by))             # pr₂z = q
    pr2z_in = N.modus_ponens(qY, equivalence_arriere(
        N.modus_ponens(pr2z_q, N.s6(pr2z, vq, "w", appartient(var("w"), vY)))))
    inner = N.loi_deduction(body, pr2z_in)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")
    return N.modus_ponens(N.assume(appartient(vz, E.produit(vX, vY))),
                          syllogisme(equivalence_avant(inst), chaine))


def _couple_dans_produit_t(vu, vv, vA, vB):
    """⊢ (u∈A et v∈B) ⇒ ((u,v)∈A×B),  u,v,A,B TERMES (témoins internes p,q)."""
    inst = _inst_produit(vA, vB, E.couple(vu, vv))   # (u,v)∈A×B ⇔ (∃p)(∃q)((u,v)=(p,q) et p∈A) et q∈B
    pinner = et(et(egal(E.couple(vu, vv), E.couple(var("p"), var("q"))),
                   appartient(var("p"), vA)), appartient(var("q"), vB))
    h = N.assume(et(appartient(vu, vA), appartient(vv, vB)))
    temoin = conjonction_intro(conjonction_intro(N.reflexivite(E.couple(vu, vv)),
                                                 conjonction_elim_gauche(h)),
                               conjonction_elim_droite(h))
    gbody = subst_f(vu, "p", pinner)
    qq = N.modus_ponens(temoin, N.s5(gbody, vv, "q"))
    full = N.modus_ponens(qq, N.s5(existe("q", pinner), vu, "p"))
    dans = N.modus_ponens(full, equivalence_arriere(inst))
    return N.loi_deduction(et(appartient(vu, vA), appartient(vv, vB)), dans)


# ── (a) INJECTIVITÉ : injective_dans(S, X×Y) ──────────────────────────────────
def swap_graphe_injective(x="X", y="Y"):
    """⊢ injective_dans(S, X×Y).   (z↦(pr₂z,pr₁z) injective sur X×Y.)

    S(u)=(pr₂u,pr₁u), S(u')=(pr₂u',pr₁u') (swap_graphe_valeur, liants a,b).  Sous
    S(u)=S(u') : (pr₂u,pr₁u)=(pr₂u',pr₁u') ⇒ pr₂u=pr₂u' et pr₁u=pr₁u'
    (couple_egal_implique_composantes).  Or u=(pr₁u,pr₂u) et u'=(pr₁u',pr₂u')
    (reconstruction EN LIANTS a,b) ; deux congruences donnent u=u'.  Tout le
    raisonnement est UNIFORME en liants a,b — fix du désaccord pr[a,b]≠pr[x,y]."""
    vX, vY = _t(x), _t(y)
    A = E.produit(vX, vY)
    S = _swap_graphe(x, y)
    vu, vup = var("u"), var("up")
    su = E.couple(E.pr2(vu, "a", "b"), E.pr1(vu, "a", "b"))     # (pr₂u, pr₁u)  [liants a,b]
    hyp = et(et(appartient(vu, A), appartient(vup, A)),
             egal(E.valeur(S, vu), E.valeur(S, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈X×Y
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈X×Y
    val_eq = conjonction_elim_droite(h)                            # S(u)=S(u')
    su_val = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                  swap_graphe_valeur(x, y, "u")))     # S(u)=(pr₂u,pr₁u)
    sup_val = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                    swap_graphe_valeur(x, y, "up")))  # S(u')=(pr₂u',pr₁u')
    su_eq_Su = N.modus_ponens(su_val, symetrie(E.valeur(S, vu), su))   # (pr₂u,pr₁u)=S(u)
    su_eq_sup = composer_egalites(composer_egalites(su_eq_Su, val_eq), sup_val)  # (pr₂u,pr₁u)=(pr₂u',pr₁u')
    comps = N.modus_ponens(su_eq_sup,
        couple_egal_implique_composantes(E.pr2(vu, "a", "b"), E.pr1(vu, "a", "b"),
                                         E.pr2(vup, "a", "b"), E.pr1(vup, "a", "b")))
    pr2_eq = conjonction_elim_gauche(comps)                        # pr₂u=pr₂u'
    pr1_eq = conjonction_elim_droite(comps)                        # pr₁u=pr₁u'
    u_rec = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                 _membre_produit_egal_couple_ab(x, y, "u")))    # u=(pr₁u,pr₂u)
    up_rec = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                   _membre_produit_egal_couple_ab(x, y, "up")))  # u'=(pr₁u',pr₂u')
    pr1u, pr2u = E.pr1(vu, "a", "b"), E.pr2(vu, "a", "b")
    pr1up, pr2up = E.pr1(vup, "a", "b"), E.pr2(vup, "a", "b")
    c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1u, pr1up, E.couple(var("w"), pr2u)))   # (pr₁u,pr₂u)=(pr₁u',pr₂u)
    c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2u, pr2up, E.couple(pr1up, var("w"))))  # (pr₁u',pr₂u)=(pr₁u',pr₂u')
    rec_eq = composer_egalites(c1, c2)                            # (pr₁u,pr₂u)=(pr₁u',pr₂u')
    u_eq_up = composer_egalites(composer_egalites(u_rec, rec_eq),
                                N.modus_ponens(up_rec, symetrie(vup, E.couple(pr1up, pr2up))))
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(S, X×Y)


# ── (b) IMAGE : image(S, X×Y) = Y×X  (surjectivité) ───────────────────────────
def swap_graphe_image(x="X", y="Y"):
    """⊢ image(S, X×Y) = Y×X.   (z↦(pr₂z,pr₁z) surjective de X×Y sur Y×X.)

    z∈S⟨X×Y⟩ ⇔ (∃t)(t∈X×Y et (t,z)∈S) ⇔[membre_graphe_terme] (∃t)(t∈X×Y et z=T[t]).
    ⇒ : T[t]=(pr₂t,pr₁t)∈Y×X car pr₂t∈Y, pr₁t∈X (liants a,b).  ⇐ : tout z=(c,d)∈Y×X
    a l'antécédent t:=(d,c)∈X×Y avec S((d,c))=(pr₂(d,c),pr₁(d,c))=(c,d)=z."""
    vX, vY = _t(x), _t(y)
    A = E.produit(vX, vY)
    YX = E.produit(vY, vX)
    swap = E.couple(E.pr2(var("k"), "a", "b"), E.pr1(var("k"), "a", "b"))
    S = E.graphe_terme(A, swap, "k")
    vz = var("z")                                              # élément de l'image (liant z, cohérent inclus/A1)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, S), A), vz)
    inner_x = et(appartient(var("x"), A), appartient(E.couple(var("x"), vz), S))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)          # z∈S⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈S)
    vt = var("t")
    Tt = subst_t(vt, "k", swap)                                # T[t] = (pr₂t, pr₁t)
    # ── ⇒ : z∈S⟨A⟩ ⇒ z∈Y×X ──────────────────────────────────────────────────
    bodyR = et(appartient(vt, A), appartient(E.couple(vt, vz), S))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                        # t∈A
    cpl_in = conjonction_elim_droite(hbR)                      # (t,z)∈S
    mem = membre_graphe_terme(A, swap, "t", "z", "k", "yb")    # ((t,z)∈S)⇔(t∈A et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))  # z=T[t]
    pr1t_in = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                   _membre_produit_pr1_ab(x, y, "t")))   # pr₁t∈X
    pr2t_in = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                   _membre_produit_pr2_ab(x, y, "t")))   # pr₂t∈Y
    pr1t, pr2t = E.pr1(vt, "a", "b"), E.pr2(vt, "a", "b")
    Tt_in_YX = N.modus_ponens(conjonction_intro(pr2t_in, pr1t_in),
                              equivalence_arriere(
                                  couple_dans_produit_ssi(pr2t, pr1t, vY, vX)))   # (pr₂t,pr₁t)∈Y×X
    z_in_YX = N.modus_ponens(Tt_in_YX, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), YX)))))
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_YX), "t")   # (∃t)(...) ⇒ z∈Y×X
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)          # z∈S⟨A⟩ ⇒ z∈Y×X
    # ── ⇐ : z∈Y×X ⇒ z∈S⟨A⟩ ──────────────────────────────────────────────────
    # z∈Y×X ⇔ (∃c)(∃d)((z=(c,d) et c∈Y) et d∈X)  (liants c,d ≠ p,q internes)
    prod_car0 = _inst_produit(vY, vX, vz)                          # liants p,q
    inner_q = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vY)),
                 appartient(var("q"), vX))                         # corps sous (∃q)
    ren_q = alpha_existe("q", "d", inner_q)                        # (∃q)…q… ⇔ (∃d)…d…
    ren_q_under_p = congruence_existe(ren_q, "p")                  # (∃p)(∃q)… ⇔ (∃p)(∃d)…
    inner_p_d = et(et(egal(vz, E.couple(var("p"), var("d"))), appartient(var("p"), vY)),
                   appartient(var("d"), vX))                       # corps sous (∃p)
    ren_p = alpha_existe("p", "c", existe("d", inner_p_d))         # (∃p)(∃d)… ⇔ (∃c)(∃d)…
    prod_car = equivalence_transitivite(prod_car0,
                  equivalence_transitivite(ren_q_under_p, ren_p))  # z∈Y×X ⇔ (∃c)(∃d)bodyP
    vc, vd = var("c"), var("d")
    bodyP = et(et(egal(vz, E.couple(vc, vd)), appartient(vc, vY)), appartient(vd, vX))
    hP = N.assume(bodyP)
    z_eq_cd = conjonction_elim_gauche(conjonction_elim_gauche(hP))  # z=(c,d)
    c_in_Y = conjonction_elim_droite(conjonction_elim_gauche(hP))  # c∈Y
    d_in_X = conjonction_elim_droite(hP)                           # d∈X
    t0 = E.couple(vd, vc)                                          # antécédent (d,c)
    t0_in_A = N.modus_ponens(conjonction_intro(d_in_X, c_in_Y),
                             _couple_dans_produit_t(vd, vc, vX, vY))   # (d,c)∈X×Y
    Tt0 = subst_t(t0, "k", swap)                                   # (pr₂(d,c), pr₁(d,c))
    pr2_t0 = _projection_seconde_ab("d", "c", "a", "b")           # pr₂(d,c)=c
    pr1_t0 = _projection_premiere_ab("d", "c", "a", "b")          # pr₁(d,c)=d
    s1 = N.modus_ponens(pr2_t0, congruence_terme(E.pr2(t0, "a", "b"), vc,
                                                 E.couple(var("w"), E.pr1(t0, "a", "b"))))
    s2 = N.modus_ponens(pr1_t0, congruence_terme(E.pr1(t0, "a", "b"), vd,
                                                 E.couple(vc, var("w"))))
    Tt0_eq_cd = composer_egalites(s1, s2)                         # T[(d,c)] = (c,d)
    cd_eq_z = N.modus_ponens(z_eq_cd, symetrie(vz, E.couple(vc, vd)))   # (c,d)=z
    Tt0_eq_z = composer_egalites(Tt0_eq_cd, cd_eq_z)             # T[(d,c)] = z
    # ((d,c), z) ∈ S  directement via l'axiome du graphe (témoins k:=(d,c), yb:=z)
    ax_S = N.axiome(E.theorie_graphe_terme(A, swap, "k", "yb", "zz"),
                    E.axiome_graphe_terme(A, swap, "k", "yb", "zz"))  # (∀zz)(zz∈S ⇔ (∃k)(∃yb)body)
    cpl_z = E.couple(t0, vz)                                      # ((d,c), z)
    car_z = instancie(ax_S, cpl_z)                               # ((d,c),z)∈S ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))), appartient(var("k"), A)),
                 egal(var("yb"), swap))
    z_eq_Tt0 = N.modus_ponens(Tt0_eq_z, symetrie(Tt0, vz))       # z = swap[(d,c)]
    body_k0 = subst_f(t0, "k", gbody_k)                          # (k|→(d,c)) body  (libre yb)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_A), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))      # (∃yb)body[k:=(d,c)]
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))  # (∃k)(∃yb)body
    cpl0_in = N.modus_ponens(ex_kyb, equivalence_arriere(car_z))   # ((d,c),z)∈S
    wit_body = conjonction_intro(t0_in_A, cpl0_in)               # (d,c)∈A et ((d,c),z)∈S
    ex_t = N.modus_ponens(wit_body, N.s5(bodyR, t0, "t"))        # (∃t)(t∈A et (t,z)∈S)
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car)) # z∈S⟨A⟩
    bwd_inner = existe_elimination(existe_elimination(
        N.loi_deduction(bodyP, in_img), "d"), "c")               # (∃c)(∃d)bodyP ⇒ z∈S⟨A⟩
    bwd_full = syllogisme(equivalence_avant(prod_car), bwd_inner)  # z∈Y×X ⇒ z∈S⟨A⟩
    # ── double inclusion (R := z∈Y×X) → egalite_par_extension ────────────────
    equiv_z = conjonction_intro(fwd_full, bwd_full)             # z∈S⟨A⟩ ⇔ z∈Y×X
    char_u = N.generalisation("z", equiv_z)                     # (∀z)(z∈S⟨A⟩ ⇔ z∈Y×X)
    selfYX = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, YX)), a_implique_a(appartient(vz, YX))))
    return egalite_par_extension(char_u, selfYX, E.image(S, A), YX, "z")


# ── Assemblage : est_bijection_de(S, X×Y, Y×X) et Eq(X×Y, Y×X) ────────────────
def swap_est_bijection(x="X", y="Y"):
    """⊢ est_bijection_de(S, X×Y, Y×X).   (S = z↦(pr₂z,pr₁z) bijection X×Y→Y×X.)

    Les 4 conjoints : fonctionnel, domaine X×Y, injectif sur X×Y, image Y×X.
    est_bijection_de = ((func et dom) et (inj et img))."""
    func = swap_graphe_fonctionnel(x, y)        # est_fonctionnel(S)
    dom = swap_graphe_domaine(x, y)             # dom S = X×Y
    inj = swap_graphe_injective(x, y)           # injective_dans(S, X×Y)
    img = swap_graphe_image(x, y)               # image(S, X×Y) = Y×X
    bijective = conjonction_intro(inj, img)     # est_bijective(S, X×Y, Y×X)
    return conjonction_intro(conjonction_intro(func, dom), bijective)


# (support ensembliste de la formule (1) ab = ba : Eq(X×Y, Y×X) par l'échange s ;
#  le livre déduit le corollaire de la Prop.5 a), le projet construit la bijection.
#  Prop. 5 a) cas binaire : invariance du produit par bijection des indices — ici
#  la bijection I={a,b}→{b,a}, réalisée par l'échange des facteurs.)
# @livre Ch.III §3.3 Prop.5 | E III.26 L.13-15 | PDF p.129
# @livre Ch.III §3.3 Demo.5 | E III.26 L.24-27 | PDF p.129
# @livre Ch.III §3.3 Demo.- | E III.27 L.10-11 | PDF p.130
def eq_produit_commute(x="X", y="Y"):
    """⊢ Eq(X×Y, Y×X).   (commutativité du produit à équipotence près, §III.3.)

    Témoin = le graphe d'échange S ; S5 sur est_bijection_de(F,X×Y,Y×X) donne
    (∃F)bij = Eq(X×Y, Y×X)."""
    vX, vY = _t(x), _t(y)
    A = E.produit(vX, vY)
    YX = E.produit(vY, vX)
    S = _swap_graphe(x, y)
    bij = swap_est_bijection(x, y)              # est_bijection_de(S, X×Y, Y×X)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), A, YX), S, "F"))


__all__ = ["membre_produit_pr1", "membre_produit_pr2", "membre_produit_egal_couple",
           "swap_graphe_fonctionnel", "swap_graphe_domaine", "swap_graphe_valeur",
           "swap_graphe_injective", "swap_graphe_image", "swap_est_bijection",
           "eq_produit_commute"]
