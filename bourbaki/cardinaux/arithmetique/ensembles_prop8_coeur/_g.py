"""CŒUR Prop. 8 — la RESTRICTION g := h|(A×{0}) et ses briques de base.

g := restriction(h, A×{0}) est le sous-graphe de h obtenu en ne gardant que les
couples dont le premier membre est dans la copie de gauche A×{0}.

Briques certifiées (term-tolérantes : points/valeurs = termes quelconques) :
  • membre_g_ssi_t(point,val) — ((point,val)∈g) ⇔ (point∈A×{0} et (point,val)∈h) ;
  • couple_g_si               — {point∈A×{0}, (point,val)∈h} ⊢ (point,val)∈g ;
  • g_inclus_h                — g ⊂ h ;
  • g_fonctionnel             — {est_fonctionnel(h)} ⊢ est_fonctionnel(g) ;
  • g_egale_h(point)          — {point∈A×{0}, A×{0}⊂dom h, h fonctionnel}
                                  ⊢ g(point) = h(point) ;
  • g_injective               — {injective_dans(h,A⊔{∅}), A×{0}⊂dom h, h fonctionnel,
                                  A×{0}⊂A⊔{∅}} ⊢ injective_dans(g, A×{0}).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, appartient, existe, inclus, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                                          composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.fonctions.ii_3_5_restrictions_prolongements.ensembles_restrictions import restriction_incluse
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(hyp_formule, preuve_hyp, thm):
    """Élimine l'hypothèse `hyp_formule` de `thm` en la prouvant par `preuve_hyp`.

    De  Γ∪{H} ⊢ C  et  Δ ⊢ H,  produit  Γ∪Δ ⊢ C  (coupure : déduction puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp_formule, thm))


_H = "h"


def A0_terme(a):
    """A×{0} — la copie de gauche de A."""
    return E.produit(_t(a), E.singleton(ZERO))


def G_RESTR(a, h=_H):
    """g := h|(A×{0}) = restriction de h à la copie de gauche A×{0}."""
    return E.restriction(var(h), A0_terme(a))


# ── ((point,val)∈g) ⇔ (point∈A×{0} et (point,val)∈h)  — TERM-tolérant ──────────
def membre_g_ssi_t(a, point, val, h=_H):
    """⊢ ((point,val) ∈ g) ⇔ (point ∈ A×{0} et (point,val) ∈ h).

    Réplique de couple_restriction (E.II.45) au niveau des TERMES point, val.
    g = h|(A×{0}), via AXIOME_RESTRICTION instancié au couple z=(point,val)."""
    vh, X0 = var(h), A0_terme(a)
    vp, vq = var("p"), var("q")
    pt, vl = _t(point), _t(val)
    g = E.restriction(vh, X0)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RESTRICTION)
    inst = instancie(instancie(instancie(ax, vh), X0), E.couple(pt, vl))
    body = et(et(egal(E.couple(pt, vl), E.couple(vp, vq)), appartient(vp, X0)),
              appartient(E.couple(vp, vq), vh))
    # ⇒ : (∃p)(∃q)body ⇒ (point∈A×{0} et (point,val)∈h)
    hb = N.assume(body)
    eq_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # (point,val)=(p,q)
    comps = N.modus_ponens(eq_pq, _couple_comps(pt, vl, vp, vq))
    p_eq = conjonction_elim_gauche(comps)                          # point=p
    q_eq = conjonction_elim_droite(comps)                          # val=q
    pX = conjonction_elim_droite(conjonction_elim_gauche(hb))      # p∈A×{0}
    # point∈A×{0} depuis p∈A×{0} et point=p
    pt_inX = N.modus_ponens(pX, equivalence_arriere(N.modus_ponens(
        p_eq, N.s6(pt, vp, "w", appartient(var("w"), X0)))))       # point∈A×{0}
    # (point,val)∈h depuis (p,q)∈h, point=p, val=q
    cong = composer_egalites(
        N.modus_ponens(p_eq, congruence_terme(pt, vp, E.couple(var("w"), vl))),  # (point,val)=(p,val)
        N.modus_ponens(q_eq, congruence_terme(vl, vq, E.couple(vp, var("w")))))  # (p,val)=(p,q)
    pv_in_h = N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(N.modus_ponens(
        cong, N.s6(E.couple(pt, vl), E.couple(vp, vq), "w", appartient(var("w"), vh)))))
    conc = conjonction_intro(pt_inX, pv_in_h)
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, conc), "q"), "p")
    fwd = N.modus_ponens(N.assume(appartient(E.couple(pt, vl), g)), equivalence_avant(inst))
    fwd = N.loi_deduction(appartient(E.couple(pt, vl), g),
                          N.modus_ponens(fwd, avant))             # (point,val)∈g ⇒ (...)
    # ⇐ : (point∈A×{0} et (point,val)∈h) ⇒ (point,val)∈g
    cible = et(appartient(pt, X0), appartient(E.couple(pt, vl), vh))
    hc = N.assume(cible)
    wit = conjonction_intro(
        conjonction_intro(N.reflexivite(E.couple(pt, vl)), conjonction_elim_gauche(hc)),
        conjonction_elim_droite(hc))                             # (p|point)(q|val)body
    gbody = subst_f(pt, "p", body)                               # (p|point)body, lieur q
    full = N.modus_ponens(N.modus_ponens(wit, N.s5(gbody, vl, "q")),
                          N.s5(existe("q", body), pt, "p"))       # (∃p)(∃q)body
    in_g = N.modus_ponens(full, equivalence_arriere(inst))       # (point,val)∈g
    bwd = N.loi_deduction(cible, in_g)
    return conjonction_intro(fwd, bwd)


def _couple_comps(pt, vl, vp, vq):
    """⊢ ((point,val)=(p,q)) ⇒ (point=p et val=q)  pour des TERMES.

    couple_egal_implique_composantes accepte directement des TERMES (via _T)."""
    return couple_egal_implique_composantes(pt, vl, vp, vq)


# ── {point∈A×{0}, (point,val)∈h} ⊢ (point,val)∈g ──────────────────────────────
def couple_g_si(a, point, val, h=_H):
    """{point∈A×{0}, (point,val)∈h} ⊢ (point,val)∈g.   (sens ⇐ de membre_g_ssi_t.)"""
    pt, vl = _t(point), _t(val)
    p_inA0 = N.assume(appartient(pt, A0_terme(a)))
    pv_in_h = N.assume(appartient(E.couple(pt, vl), var(h)))
    ssi = membre_g_ssi_t(a, point, val, h)
    return N.modus_ponens(conjonction_intro(p_inA0, pv_in_h), equivalence_arriere(ssi))


# ── g ⊂ h ─────────────────────────────────────────────────────────────────────
def g_inclus_h(a="A", h=_H):
    """⊢ g ⊂ h.   (la restriction est incluse dans le graphe ; clos.)

    Réplique de restriction_incluse (E.II.45) avec le graphe h et la copie de
    gauche A×{0} comme TERMES (restriction_incluse n'accepte que des noms)."""
    vh, X0 = var(h), A0_terme(a)
    g = E.restriction(vh, X0)
    vz, vp, vq = var("z"), var("p"), var("q")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RESTRICTION)
    inst = instancie(instancie(instancie(ax, vh), X0), vz)   # z∈g ⇔ (∃p)(∃q)body
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, X0)),
              appartient(E.couple(vp, vq), vh))
    hb = N.assume(body)
    eq_z = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    pq_in = conjonction_elim_droite(hb)                          # (p,q)∈h
    z_in = N.modus_ponens(pq_in, equivalence_arriere(N.modus_ponens(
        eq_z, N.s6(vz, E.couple(vp, vq), "w", appartient(var("w"), vh)))))   # z∈h
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, z_in), "q"), "p")
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme as _syll
    z_imp = _syll(equivalence_avant(inst), avant)                # z∈g ⇒ z∈h
    return N.generalisation("z", z_imp)                          # g ⊂ h


# ── {est_fonctionnel(h)} ⊢ est_fonctionnel(g) ─────────────────────────────────
def g_fonctionnel(a="A", h=_H):
    """{est_fonctionnel(h)} ⊢ est_fonctionnel(g).   (sous-graphe d'un fonctionnel.)"""
    vh = var(h)
    g = G_RESTR(a, h)
    vu, vv, vz = var("u"), var("v"), var("z")
    hyp = et(appartient(E.couple(vu, vv), g), appartient(E.couple(vu, vz), g))
    hh = N.assume(hyp)
    incl = g_inclus_h(a, h)                                   # (∀w)(w∈g ⇒ w∈h)
    uv_in_h = N.modus_ponens(conjonction_elim_gauche(hh),
                             instancie(incl, E.couple(vu, vv)))   # (u,v)∈h
    uz_in_h = N.modus_ponens(conjonction_elim_droite(hh),
                             instancie(incl, E.couple(vu, vz)))   # (u,z)∈h
    hfun = N.assume(E.est_fonctionnel(vh))
    inst = instancie(instancie(instancie(hfun, vu), vv), vz)
    v_eq_z = N.modus_ponens(conjonction_intro(uv_in_h, uz_in_h), inst)
    inner = N.loi_deduction(hyp, v_eq_z)
    return N.generalisation("u", N.generalisation("v", N.generalisation("z", inner)))


# ── {point∈A×{0}, A×{0}⊂dom h, h fonctionnel} ⊢ g(point)=h(point) ──────────────
def g_egale_h(a, point, h=_H):
    """{point∈A×{0}, A×{0}⊂dom h, est_fonctionnel(h)} ⊢ g(point) = h(point).

    (point,h(point))∈h (point∈dom h via A×{0}⊂dom h) ; donc (point,h(point))∈g
    (couple_g_si) ; g fonctionnel + (point,h(point))∈g ⇒ g(point)=h(point), càd
    h(point)=g(point)  — via valeur_caracterisation appliquée à g."""
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
    vh = var(h)
    pt = _t(point)
    g = G_RESTR(a, h)
    A0 = A0_terme(a)
    hp = E.valeur(vh, pt)                                     # h(point)
    gp = E.valeur(g, pt)                                      # g(point)
    # point∈dom h  (de A×{0}⊂dom h et point∈A×{0})
    hsub = N.assume(inclus(A0, E.dom(vh)))
    p_inA0 = N.assume(appartient(pt, A0))
    p_in_dom = N.modus_ponens(p_inA0, instancie(hsub, pt))   # point∈dom h
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(ax_dom, vh), pt)           # point∈dom h ⇔ (∃y)((point,y)∈h)
    exy = N.modus_ponens(p_in_dom, equivalence_avant(car_dom))   # (∃y)((point,y)∈h)
    ph_in_h = N.modus_ponens(exy, N.existe_temoin(
        appartient(E.couple(pt, var("y")), vh), "y"))         # (point,h(point))∈h
    # (point,h(point))∈g
    ph_in_g = N.modus_ponens(conjonction_intro(p_inA0, ph_in_h),
                             equivalence_arriere(membre_g_ssi_t(a, pt, hp, h)))  # (point,h(point))∈g
    # g(point)=h(point) :  valeur_caracterisation(g, point) ⇒ : (point,y)∈g ⇒ y=g(point)
    # avec y := h(point) ; il faut g fonctionnel + (∃y)((point,y)∈g).
    vc = valeur_caracterisation(g, pt)                       # {g fonctionnel,(∃y)..} ⊢ ((point,y)∈g)⇔(y=g(point))
    # vc a 2 hyps : est_fonctionnel(g), (∃y)((point,y)∈g) ; on les décharge.
    vc_fwd = equivalence_avant(vc)                           # (point,y)∈g ⇒ y=g(point)  [y libre]
    vc_inst = instancie(N.generalisation("y", N.loi_deduction(
        appartient(E.couple(pt, var("y")), g),
        N.modus_ponens(N.assume(appartient(E.couple(pt, var("y")), g)), vc_fwd))), hp)
    # vc_inst : (point,h(point))∈g ⇒ h(point)=g(point)   [hyps g fonctionnel,(∃y)..]
    y_eq_gp = N.modus_ponens(ph_in_g, vc_inst)              # h(point)=g(point)
    res = N.modus_ponens(y_eq_gp, symetrie(hp, gp))        # g(point)=h(point)
    # Décharger les deux hypothèses introduites par valeur_caracterisation(g, ·) :
    #   est_fonctionnel(g)  — par g_fonctionnel (qui la tire de est_fonctionnel(h)) ;
    #   (∃y)((point,y)∈g)   — par ph_in_g (témoin y:=h(point)).
    ex_g = N.modus_ponens(ph_in_g, N.s5(
        appartient(E.couple(pt, var("y")), g), hp, "y"))    # (∃y)((point,y)∈g)
    res = _cut(existe("y", appartient(E.couple(pt, var("y")), g)), ex_g, res)
    res = _cut(E.est_fonctionnel(g), g_fonctionnel(a, h), res)
    return res


# ── {injective_dans(h,A⊔{∅}), A×{0}⊂dom h, h fonctionnel, A×{0}⊂A⊔{∅}} ─────────
#     ⊢ injective_dans(g, A×{0})
def g_injective(a, b_somme, h=_H):
    """Hérite l'injectivité de h sur la restriction g.   `b_somme` = A⊔{∅}."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de  # noqa
    vh = var(h)
    va = _t(a)
    A0 = A0_terme(a)
    AS = _t(b_somme)
    g = G_RESTR(a, h)
    vu, vup = var("u"), var("up")
    hyp = et(et(appartient(vu, A0), appartient(vup, A0)),
             egal(E.valeur(g, vu), E.valeur(g, vup)))
    hh = N.assume(hyp)
    u_inA0 = conjonction_elim_gauche(conjonction_elim_gauche(hh))
    up_inA0 = conjonction_elim_droite(conjonction_elim_gauche(hh))
    gu_eq_gup = conjonction_elim_droite(hh)                  # g(u)=g(u')
    # g(u)=h(u), g(u')=h(u')
    g_u = g_egale_h(a, vu, h)                                # {u∈A×{0},...} ⊢ g(u)=h(u)
    g_up = g_egale_h(a, vup, h)                              # {u'∈A×{0},...} ⊢ g(u')=h(u')
    # h(u)=h(u') :  h(u)=g(u)=g(u')=h(u')
    hu_eq_gu = N.modus_ponens(g_u, symetrie(E.valeur(g, vu), E.valeur(vh, vu)))  # h(u)=g(u)
    hu_eq_hup = composer_egalites(composer_egalites(hu_eq_gu, gu_eq_gup), g_up)  # h(u)=h(u')
    # u∈A⊔{∅}, u'∈A⊔{∅}  (A×{0}⊂A⊔{∅})
    hsub_S = N.assume(inclus(A0, AS))
    u_inAS = N.modus_ponens(u_inA0, instancie(hsub_S, vu))
    up_inAS = N.modus_ponens(up_inA0, instancie(hsub_S, vup))
    # injective_dans(h, A⊔{∅}) instancié
    hinj = N.assume(E.injective_dans(vh, AS))
    inj_inst = instancie(instancie(hinj, vu), vup)          # ((u,u'∈AS et h(u)=h(u'))⇒u=u')
    u_eq_up = N.modus_ponens(conjonction_intro(
        conjonction_intro(u_inAS, up_inAS), hu_eq_hup), inj_inst)   # u=u'
    # g_egale_h a réintroduit les hypothèses atomiques u∈A×{0}, u'∈A×{0} : on les
    # décharge par les conjoints u_inA0, up_inA0 (qui dépendent encore de hyp, ce
    # qui est sans effet puisque hyp est aussi présente) AVANT de décharger hyp.
    u_eq_up = _cut(appartient(vu, A0), u_inA0, u_eq_up)
    u_eq_up = _cut(appartient(vup, A0), up_inA0, u_eq_up)
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))


__all__ = ["A0_terme", "G_RESTR", "membre_g_ssi_t", "couple_g_si", "g_inclus_h",
           "g_fonctionnel", "g_egale_h", "g_injective"]
