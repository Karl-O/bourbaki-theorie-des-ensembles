"""§II.3.5 — Restrictions et prolongements de fonctions.

Au niveau des GRAPHES (une fonction f=(F,A,B) est représentée par son graphe
fonctionnel F) :

  • restriction f|X : graphe {(x,y) | x∈X et y=f(x)} = F ∩ (X × img(F)),
    caractérisé par  ((u,v)∈f|X) ⇔ (u∈X et (u,v)∈F)  (couple_restriction).
  • prolongement : g prolonge f ⇔ F⊂G  (inclusion des graphes).
  • coïncidence sur E : (∀x)(x∈E ⇒ f(x)=g(x)) avec E⊂dom F et E⊂dom G.

Théorèmes certifiés :
  - couple_restriction        ((u,v)∈f|X) ⇔ (u∈X et (u,v)∈F)
  - restriction_incluse       f|X ⊂ F     (F prolonge f|X — « une fonction est un
                              prolongement d'une quelconque de ses restrictions »)
  - prolongement_reflexif     F ⊂ F       (toute fonction se prolonge elle-même)
  - prolongement_transitif    (F⊂G et G⊂H) ⇒ F⊂H
  - coincidence_meme_graphe   (F=G) ⇒ (∀x)(x∈dom F ⇒ f(x)=g(x))  [même graphe ⇒
                              coïncidence dans l'ensemble de définition]
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, existe, inclus, pourtout, impl, subst_f
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, inclusion_transitive)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import composer_egalites, congruence_terme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes


def _inst_restriction(f, x, z):
    """⊢ (z ∈ f|X) ⇔ (∃p)(∃q)(z=(p,q) et p∈X et (p,q)∈F)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RESTRICTION)
    return instancie(instancie(instancie(ax, f), x), z)


def couple_restriction(f="F", x="X", u="u", v="v"):
    """⊢ ((u,v) ∈ f|X) ⇔ (u∈X et (u,v)∈F).   (E.II.45 ; u, v distincts de p, q.)"""
    vF, vX, vu, vv, vp, vq = var(f), var(x), var(u), var(v), var("p"), var("q")
    inst = _inst_restriction(vF, vX, E.couple(vu, vv))
    # body(p,q) := ((u,v)=(p,q) et p∈X) et (p,q)∈F
    body = et(et(egal(E.couple(vu, vv), E.couple(vp, vq)), appartient(vp, vX)),
              appartient(E.couple(vp, vq), vF))

    # ── ⇒ : (∃p)(∃q)body ⇒ (u∈X et (u,v)∈F) ────────────────────────────────────
    hb = N.assume(body)
    eq_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # (u,v)=(p,q)
    comps = N.modus_ponens(eq_pq, couple_egal_implique_composantes(u, v, "p", "q"))  # u=p et v=q
    uep = conjonction_elim_gauche(comps)                           # u=p
    veq = conjonction_elim_droite(comps)                           # v=q
    # u∈X : depuis p∈X et u=p
    pX = conjonction_elim_droite(conjonction_elim_gauche(hb))      # p∈X
    uX = N.modus_ponens(pX, equivalence_arriere(N.modus_ponens(
        uep, N.s6(vu, vp, "w", appartient(var("w"), vX)))))        # u∈X
    # (u,v)∈F : depuis (p,q)∈F, u=p, v=q  (réécrire (p,q) → (u,v))
    cong = composer_egalites(
        N.modus_ponens(uep, congruence_terme(vu, vp, E.couple(var("w"), vv))),  # (u,v)=(p,v)
        N.modus_ponens(veq, congruence_terme(vv, vq, E.couple(vp, var("w")))))  # (p,v)=(p,q)
    uv_in = N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(N.modus_ponens(
        cong, N.s6(E.couple(vu, vv), E.couple(vp, vq), "w", appartient(var("w"), vF)))))  # (u,v)∈F
    conc = conjonction_intro(uX, uv_in)
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, conc), "q"), "p")

    # ── ⇐ : (u∈X et (u,v)∈F) ⇒ (∃p)(∃q)body ────────────────────────────────────
    cible = et(appartient(vu, vX), appartient(E.couple(vu, vv), vF))
    h = N.assume(cible)
    wit = conjonction_intro(
        conjonction_intro(N.reflexivite(E.couple(vu, vv)), conjonction_elim_gauche(h)),
        conjonction_elim_droite(h))                                # (u|p)(v|q)body
    gbody = subst_f(vu, "p", body)                                 # (u|p)body, lieur q
    full = N.modus_ponens(N.modus_ponens(wit, N.s5(gbody, vv, "q")),
                          N.s5(existe("q", body), vu, "p"))         # (∃p)(∃q)body
    arriere = N.loi_deduction(cible, full)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def restriction_incluse(f="F", x="X"):
    """⊢ f|X ⊂ F.   (Le graphe de la restriction est inclus dans celui de f : F est
    un prolongement de f|X — « une fonction est un prolongement de ses restrictions ».)"""
    vF, vX, vz = var(f), var(x), var("z")
    inst = _inst_restriction(vF, vX, vz)               # z∈f|X ⇔ (∃p)(∃q)body
    vp, vq = var("p"), var("q")
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vX)),
              appartient(E.couple(vp, vq), vF))
    hb = N.assume(body)
    eq_z = conjonction_elim_gauche(conjonction_elim_gauche(hb))    # z=(p,q)
    pq_in = conjonction_elim_droite(hb)                            # (p,q)∈F
    # z∈F par Leibniz : de z=(p,q) et (p,q)∈F
    z_in = N.modus_ponens(pq_in, equivalence_arriere(N.modus_ponens(
        eq_z, N.s6(vz, E.couple(vp, vq), "w", appartient(var("w"), vF)))))   # z∈F
    avant = existe_elimination(existe_elimination(N.loi_deduction(body, z_in), "q"), "p")
    z_imp = syllogisme(equivalence_avant(inst), avant)             # z∈f|X ⇒ z∈F
    return N.generalisation("z", z_imp)                            # f|X ⊂ F


def prolongement_reflexif(f="F"):
    """⊢ F ⊂ F.   (toute fonction est un prolongement d'elle-même.)"""
    vF, vz = var(f), var("z")
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
    return N.generalisation("z", a_implique_a(appartient(vz, vF)))


def prolongement_transitif(f="F", g="G", h="H"):
    """⊢ ((F⊂G) et (G⊂H)) ⇒ (F⊂H).   (le prolongement est transitif.)"""
    return inclusion_transitive(f, g, h)


def coincidence_meme_graphe(f="F", g="G", x="x"):
    """⊢ (F = G) ⇒ (∀x)(x∈dom F ⇒ f(x)=g(x)).

    « Deux fonctions ayant même graphe coïncident dans leur ensemble de
    définition. » Si F=G alors dom F=dom G (mêmes éléments), et f(x)=g(x) car
    f(x)=τy((x,y)∈F), g(x)=τy((x,y)∈G) sont τ d'équivalences déduites de F=G."""
    vF, vG, vx = var(f), var(g), var(x)
    heq = N.assume(egal(vF, vG))                       # F = G
    fx, gx = E.valeur(vF, vx), E.valeur(vG, vx)
    # f(x) = g(x) : congruence du terme f(x) = τy((x,y)∈w) en w, de F=G
    eq_fg = N.modus_ponens(heq, congruence_terme(
        vF, vG, E.valeur(var("w"), vx)))               # f(x) = g(x)  [w-trou dans valeur]
    inner = N.loi_deduction(appartient(vx, E.dom(vF)), eq_fg)   # x∈dom F ⇒ f(x)=g(x)
    gen = N.generalisation(x, inner)                   # (∀x)(x∈dom F ⇒ f(x)=g(x))
    return N.loi_deduction(egal(vF, vG), gen)


__all__ = ["couple_restriction", "restriction_incluse",
           "prolongement_reflexif", "prolongement_transitif",
           "coincidence_meme_graphe"]
