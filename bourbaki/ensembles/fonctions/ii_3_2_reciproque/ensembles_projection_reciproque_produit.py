"""Résumé §3 item 3e — pr₁⁻¹(X) = X×F   (image réciproque d'une projection).

E.R.12 (item 3e).  Soit pr₁ : E×F → E la première projection ; pour X ⊂ E,
    pr₁⁻¹(X) = X × F.
On code pr₁ par son GRAPHE fonctionnel sur E×F,
    G := graphe_terme(E×F, pr₁(k), 'k')     (donc G(k) = pr₁(k), z ↦ première coord.),
et l'image réciproque pr₁⁻¹(X) := image(reciproque(G), X) — la convention f⁻¹⟨X⟩ du
projet (E.II.41/AXIOME_IMAGE).  On certifie (double inclusion + extensionnalité A1) :

    {X ⊂ E}  ⊢  image(reciproque(G), X) = X × F.

Caractérisation de l'appartenance (moteur des deux inclusions) :
    t ∈ pr₁⁻¹(X) ⇔ (∃x)(x∈X et (x,t)∈G⁻¹) ⇔ (∃x)(x∈X et (t,x)∈G)
               ⇔ (∃x)(x∈X et t∈E×F et x=pr₁(t)) ⇔ (t∈E×F et pr₁(t)∈X).
Un élément t∈E×F se reconstruit t=(pr₁t,pr₂t) (`_reconstruction_couple`, via AXIOME_PRODUIT
+ projection) ; l'hypothèse X⊂E sert au SEUL sens ⊃ (placer (pr₁t,pr₂t) dans E×F).

HYGIÈNE DE LIANTS (nœud τ).  `membre_image_reciproque` lie son existentiel « x », or
pr₁(k)=τx(∃y(k=(x,y))) lierait AUSSI « x » : collision fatale dans `couple_reciproque`
(et renommage-α impossible, le round-trip x→s→x recapture le τx).  On construit donc pr₁
avec un liant FRAIS « i1 » (`_proj1`, portage binder-configurable de projection_premiere) :
G, `_mgt` et la reconstruction utilisent tous pr₁ à liant « i1 » ≠ « x » — aucune collision,
aucun renommage.  pr₂ garde son liant par défaut (jamais sous l'existentiel).

Rien postulé ; theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, appartient, impl, inclus, existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    membre_image_reciproque)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi)
from bourbaki.ensembles.fonctions.hors_ii_3.ii_2_projections.ensembles_projections import (
    tau_egal, projection_seconde)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    couple_egal_implique_composantes)

I1, J1 = "i1", "j1"                                       # liants FRAIS de pr₁ (≠ « x »)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _pr1(z):
    """pr₁ à liants frais i1,j1 : τi1(∃j1(z=(i1,j1)))  (≠ liant « x » de l'existentiel)."""
    return E.pr1(z, I1, J1)


def _proj1(u, v):
    """⊢ pr₁((u,v)) = u  pour pr₁ à liants i1,j1  (portage binder-configurable ; u,v NOMS)."""
    vu, vv, vx, vy = var(u), var(v), var(I1), var(J1)
    cuv = E.couple(vu, vv)
    R = existe(J1, egal(cuv, E.couple(vx, vy)))            # corps de pr₁((u,v)), lié par i1
    dur = couple_egal_implique_composantes(u, v, I1, J1)   # ((u,v)=(i1,j1)) ⇒ (u=i1 et v=j1)
    heq = N.assume(egal(cuv, E.couple(vx, vy)))
    xu = N.modus_ponens(conjonction_elim_gauche(N.modus_ponens(heq, dur)), symetrie(vu, vx))
    inner = N.loi_deduction(egal(cuv, E.couple(vx, vy)), xu)   # ((u,v)=(i1,j1)) ⇒ (i1=u)
    F = existe_elimination(inner, J1)                        # R ⇒ (i1=u)
    hxu = N.assume(egal(vx, vu))
    uv_xv = N.modus_ponens(N.modus_ponens(hxu, symetrie(vx, vu)),
                           congruence_terme(vu, vx, E.couple(var("w"), vv)))  # (u,v)=(i1,v)
    Rx = N.modus_ponens(uv_xv, N.s5(egal(cuv, E.couple(vx, vy)), vv, J1))     # (∃j1)((u,v)=(i1,j1))
    B = N.loi_deduction(egal(vx, vu), Rx)                     # (i1=u) ⇒ R
    gen = N.generalisation(I1, conjonction_intro(F, B))       # (∀i1)(R ⇔ (i1=u))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vx, vu), I1))   # τi1(R) = τi1(i1=u)
    return composer_egalites(tau_eq, tau_egal(u, I1))         # pr₁((u,v)) = u


def _inst_produit(vA, vB, vz):
    """⊢ (z ∈ A×B) ⇔ (∃p)(∃q)((z=(p,q) et p∈A) et q∈B).   (instance de AXIOME_PRODUIT.)"""
    return instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT), vA), vB), vz)


def _mgt(a, t_term, u_term, v_term, x="k", y="yb"):
    """⊢ ((u,v)∈graphe_terme(a,t,x)) ⇔ (u∈a et v=t[x:=u])  pour des TERMES u, v."""
    base = membre_graphe_terme(a, t_term, "uu", "vv", x, y)
    g = N.generalisation("uu", N.generalisation("vv", base))
    return instancie(instancie(g, u_term), v_term)


def _reconstruction_couple(vt, vA, vB):
    """{t ∈ A×B} ⊢ t = (pr₁t, pr₂t).   (pr₁ à liants i1,j1 ; pr₂ par défaut.)"""
    vp, vq = var("p"), var("q")
    inst = _inst_produit(vA, vB, vt)
    body = et(et(egal(vt, E.couple(vp, vq)), appartient(vp, vA)), appartient(vq, vB))
    hb = N.assume(body)
    t_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))          # t=(p,q)
    pr1_p = composer_egalites(
        N.modus_ponens(t_pq, congruence_terme(vt, E.couple(vp, vq), _pr1(var("w")))),
        _proj1("p", "q"))                                               # pr₁t = p
    pr2_q = composer_egalites(
        N.modus_ponens(t_pq, congruence_terme(vt, E.couple(vp, vq), E.pr2(var("w")))),
        projection_seconde("p", "q"))                                   # pr₂t = q
    c1 = N.modus_ponens(pr1_p, congruence_terme(_pr1(vt), vp, E.couple(var("w"), E.pr2(vt))))
    c2 = N.modus_ponens(pr2_q, congruence_terme(E.pr2(vt), vq, E.couple(vp, var("w"))))
    pr_eq = composer_egalites(c1, c2)                                   # (pr₁t,pr₂t)=(p,q)
    t_eq = composer_egalites(t_pq, N.modus_ponens(pr_eq,                # t=(p,q)=(pr₁t,pr₂t)
        symetrie(E.couple(_pr1(vt), E.pr2(vt)), E.couple(vp, vq))))
    chaine = existe_elimination(existe_elimination(N.loi_deduction(body, t_eq), "q"), "p")
    return N.modus_ponens(N.modus_ponens(N.assume(appartient(vt, E.produit(vA, vB))),
                                         equivalence_avant(inst)), chaine)


# @livre Ch.R §3 Prop.- | E.R.12 item 3e ((24) pr₁⁻¹(X)=X×F, X⊂E) | PDF p.315
def pr1_reciproque_produit(x="X", e="E", f="F"):
    """⊢ X⊂E ⇒ image(reciproque(G), X) = X×F,   G = graphe_terme(E×F, pr₁(k), 'k').

    (pr₁⁻¹(X) = X×F : image réciproque de X⊂E par la première projection E×F→E.)"""
    vX, vE, vF = _t(x), _t(e), _t(f)
    prod = E.produit(vE, vF)
    G = E.graphe_terme(prod, _pr1(var("k")), "k")
    Grec = E.reciproque(G)
    P = E.image(Grec, vX)                                 # pr₁⁻¹(X)
    XF = E.produit(vX, vF)
    vt, vx = var("t"), var("x")
    hXE = N.assume(inclus(vX, vE))                        # X ⊂ E
    pr1t = _pr1(vt)
    body_x = et(appartient(vx, vX), appartient(E.couple(vx, vt), Grec))

    # ── pr₁⁻¹(X) ⊂ X×F ──
    ht = N.assume(appartient(vt, P))
    ex_x = N.modus_ponens(ht, equivalence_avant(membre_image_reciproque(G, vX, vt)))  # ∃x(...)
    hb = N.assume(body_x)
    xX = conjonction_elim_gauche(hb)                                    # x∈X
    tx_G = N.modus_ponens(conjonction_elim_droite(hb),                 # (t,x)∈G
                          equivalence_avant(couple_reciproque(G, "x", "t")))
    conj = N.modus_ponens(tx_G, equivalence_avant(_mgt(prod, _pr1(var("k")), vt, vx)))
    t_EF = conjonction_elim_gauche(conj)                                # t∈E×F
    x_eq_pr1t = conjonction_elim_droite(conj)                           # x = pr₁(t)
    pr1t_X = N.modus_ponens(xX, equivalence_avant(N.modus_ponens(x_eq_pr1t,  # pr₁t ∈ X
        N.s6(vx, pr1t, "w", appartient(var("w"), vX)))))
    t_eq = N.modus_ponens(t_EF, N.loi_deduction(appartient(vt, prod),  # t=(pr₁t,pr₂t) {décharge t∈E×F}
                                                _reconstruction_couple(vt, vE, vF)))
    couple_EF = N.modus_ponens(t_EF, equivalence_avant(                # (pr₁t,pr₂t)∈E×F
        N.modus_ponens(t_eq, N.s6(vt, E.couple(pr1t, E.pr2(vt)), "w", appartient(var("w"), prod)))))
    pr2t_F = conjonction_elim_droite(N.modus_ponens(couple_EF,          # pr₂t ∈ F
        equivalence_avant(couple_dans_produit_ssi(pr1t, E.pr2(vt), vE, vF))))
    couple_XF = N.modus_ponens(conjonction_intro(pr1t_X, pr2t_F),       # (pr₁t,pr₂t)∈X×F
        equivalence_arriere(couple_dans_produit_ssi(pr1t, E.pr2(vt), vX, vF)))
    t_XF = N.modus_ponens(couple_XF, equivalence_arriere(              # t∈X×F
        N.modus_ponens(t_eq, N.s6(vt, E.couple(pr1t, E.pr2(vt)), "w", appartient(var("w"), XF)))))
    elim = existe_elimination(N.loi_deduction(body_x, t_XF), "x")
    incl1 = N.generalisation("t", N.loi_deduction(appartient(vt, P), N.modus_ponens(ex_x, elim)))

    # ── X×F ⊂ pr₁⁻¹(X) ──
    ht2 = N.assume(appartient(vt, XF))
    t_eq2 = _reconstruction_couple(vt, vX, vF)                          # t=(pr₁t,pr₂t)  {t∈X×F}
    couple_XF2 = N.modus_ponens(ht2, equivalence_avant(               # (pr₁t,pr₂t)∈X×F
        N.modus_ponens(t_eq2, N.s6(vt, E.couple(pr1t, E.pr2(vt)), "w", appartient(var("w"), XF)))))
    pq = N.modus_ponens(couple_XF2, equivalence_avant(couple_dans_produit_ssi(pr1t, E.pr2(vt), vX, vF)))
    pr1t_X2 = conjonction_elim_gauche(pq)                              # pr₁t∈X
    pr2t_F2 = conjonction_elim_droite(pq)                             # pr₂t∈F
    pr1t_E = N.modus_ponens(pr1t_X2, instancie(hXE, pr1t))            # pr₁t∈E  (X⊂E)
    couple_EF2 = N.modus_ponens(conjonction_intro(pr1t_E, pr2t_F2),    # (pr₁t,pr₂t)∈E×F
        equivalence_arriere(couple_dans_produit_ssi(pr1t, E.pr2(vt), vE, vF)))
    t_EF2 = N.modus_ponens(couple_EF2, equivalence_arriere(          # t∈E×F
        N.modus_ponens(t_eq2, N.s6(vt, E.couple(pr1t, E.pr2(vt)), "w", appartient(var("w"), prod)))))
    ts_G2 = N.modus_ponens(conjonction_intro(t_EF2, N.reflexivite(pr1t)),  # (t,pr₁t)∈G
        equivalence_arriere(_mgt(prod, _pr1(var("k")), vt, pr1t)))
    tpr1_rec = N.modus_ponens(ts_G2, equivalence_arriere(couple_reciproque(G, pr1t, vt)))  # (pr₁t,t)∈G⁻¹
    ex_x2 = N.modus_ponens(conjonction_intro(pr1t_X2, tpr1_rec),       # ∃x(x∈X et (x,t)∈G⁻¹)
        N.s5(body_x, pr1t, "x"))
    t_in_P = N.modus_ponens(ex_x2, equivalence_arriere(membre_image_reciproque(G, vX, vt)))
    incl2 = N.generalisation("t", N.loi_deduction(appartient(vt, XF), t_in_P))

    # rebinder « t »→« z » (liant imposé par A1/inclus) : membres atomiques ⇒ propre
    incl1_z = N.generalisation("z", instancie(incl1, var("z")))
    incl2_z = N.generalisation("z", instancie(incl2, var("z")))
    eq = N.modus_ponens(conjonction_intro(incl1_z, incl2_z), extensionnalite_appliquee(P, XF))
    return N.loi_deduction(inclus(vX, vE), eq)                          # X⊂E ⇒ pr₁⁻¹(X)=X×F


def cible_pr1_reciproque_produit(x="X", e="E", f="F"):
    """Conclusion exacte : X⊂E ⇒ image(reciproque(graphe_terme(E×F,pr₁(k),'k')), X) = X×F."""
    vX, vE, vF = _t(x), _t(e), _t(f)
    G = E.graphe_terme(E.produit(vE, vF), _pr1(var("k")), "k")
    return impl(inclus(vX, vE), egal(E.image(E.reciproque(G), vX), E.produit(vX, vF)))


__all__ = ["pr1_reciproque_produit", "cible_pr1_reciproque_produit"]
