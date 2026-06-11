"""Chapitre III §1-2 — PROPOSITIONS directes d'ordre, treillis, isomorphismes.

Module NEUF (campagne III.1-2 « propositions atteignables »).  Il prouve, dans la
convention « graphe G » de `ensembles_ordre_relation.py` (x≤y := (x,y)∈G) ET dans
la convention « relation R = fonction Python (Terme,Terme)↦Formule » de
`ensembles_ordre_vocab.py` (compatible_ordre, est_isomorphisme_ordre), des
THÉORÈMES DIRECTS de §III.1-2 qui n'étaient pas encore certifiés :

  TREILLIS / borne (E.III.1.9) :
   • borne_inferieure_unique  : la borne inférieure, si elle existe, est unique
     (duale de borne_superieure_unique déjà présente) ;
   • plus_petit_est_borne_inferieure : le plus petit élément de A est sa borne inf.

  MONOTONIE — composée (E.III.1.5) :
   • composee_croissantes_est_croissante : si g:E→E' et g':E'→E'' sont croissantes
     (au sens graphe), alors g'∘g (représentée par h avec h(x)=g'(g(x))) est
     croissante de E dans E'' ;
   • composee_compatibles_est_compatible : composée de deux applications compatibles
     à l'ordre est compatible (cœur de « composée d'isos est iso »).

  ISOMORPHISMES d'ordre (E.III.1.3) :
   • compatible_reciproque : si f est compatible et g est son inverse (f(g(u))=u,
     g(u)∈E sur E'), alors g est compatible (cœur de « réciproque d'un iso est un
     iso ») ;
   • iso_preserve_plus_grand : un iso f:E→E' (compatible + surjectif) envoie le plus
     grand élt de E sur le plus grand élt de E' ;
   • iso_preserve_plus_petit : dual.

  INTERVALLES (E.III.1.13) :
   • axiome_intervalle_ferme / theorie_intervalle_ferme : membership de [a,b] en
     théorie DÉDIÉE (S8+A1) ;
   • intervalle_ferme_a_dans : a∈[a,b] dès que a∈E, a≤a, a≤b ;
   • intervalle_ferme_non_vide_si_a_inf_b : a≤b (a∈E) ⇒ [a,b]≠∅.

  PROPOSITION 11 (E.III.1.12) — monotonie stricte ⇒ injectivité :
   • strictement_croissante_injective_graphe / ..._decroissante_... : sur E
     TOTALEMENT ordonné, toute application strictement croissante (resp. décr.)
     est injective sur E ;
   • strictement_monotone_injective_graphe : monotone strict ⇒ injectif (par cas).

theorie_ensembles INTANGIBLE = 22 : le seul axiome introduit (membership de
[a,b]) vit dans une THÉORIE DÉDIÉE `theorie_intervalle_ferme`, légitimée par S8
(sélection dans E) + A1 (unicité), JAMAIS dans theorie_ensembles.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, cas, tiers_exclu,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ordre.ensembles_ordre_relation import (
    antisymetrie, totalement_ordonne, minorant,
    borne_inferieure, plus_petit_element,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _val(f, x):
    """f(x) au sens Bourbaki, liant frais « yv » (cf. ensembles_ordre_monotone)."""
    return E.valeur(_terme(f), _terme(x), b="yv")


def _strict(t, u, G):
    """Ordre strict « t < u » := (t,u)∈G et t≠u  (E.III.1.3, C58)."""
    vt, vu = _terme(t), _terme(u)
    return et(_couple_dans(vt, vu, G), non(egal(vt, vu)))


def _equiv_intro(ab, ba):
    """De Γ⊢(A⇒B) et Δ⊢(B⇒A) déduit Γ∪Δ⊢(A⇔B).

    equiv(A,B) := (A⇒B) et (B⇒A) (cf. formule.equiv), donc l'intro est exactement
    la conjonction des deux implications."""
    return conjonction_intro(ab, ba)


def _ex_falso(thm_p, thm_np, q):
    """De ⊢ P et ⊢ ¬P déduit ⊢ Q  (ex falso quodlibet ; réexporté de witt_chaine)."""
    p = thm_p.conclusion
    P_imp_Q = N.modus_ponens(thm_np, N.s2(non(p), q))      # ¬P ⇒ (¬P∨Q) = (P⇒Q)
    return N.modus_ponens(thm_p, P_imp_Q)                  # Q


def _neg_sym(thm_neq_xy, vx, vy):
    """De Γ ⊢ ¬(x=y) déduit Γ ⊢ ¬(y=x)  (symétrie de la non-égalité).

    Si y=x alors x=y (symétrie de =), contredisant ¬(x=y).  ¬(y=x) :=
    (y=x ⇒ ⊥) construit par décharge de (y=x) après ex falso vers (y=x⇒¬(y=x))→S1."""
    Hyx = N.assume(egal(vy, vx))                           # y=x
    xy = N.modus_ponens(Hyx, symetrie(vy, vx))             # x=y
    # (y=x) ⊢ ¬(y=x)  via ex falso (x=y et ¬(x=y) ⊢ ¬(y=x)) puis _refute_self
    yx_imp_nyx = N.loi_deduction(egal(vy, vx),
                                 _ex_falso(xy, thm_neq_xy, non(egal(vy, vx))))
    # (y=x ⇒ ¬(y=x)) ⊢ ¬(y=x)   (P⇒¬P ≡ ¬P∨¬P → ¬P par S1)
    return N.modus_ponens(yx_imp_nyx, N.s1(non(egal(vy, vx))))


# Forme « graphe » de croissante (E.III.1.5) ; signature plate.
def croissante_graphe(G, Gp, f, E_set, x="x", y="y"):
    """croissante_graphe(G,G',f,E) :=
        (∀x)(∀y)((x∈E et y∈E et (x,y)∈G) ⇒ (f(x),f(y))∈G').  (E.III.1.5, Déf. 1.)"""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    concl = _couple_dans(_val(f, vx), _val(f, vy), Gp)
    return pourtout(x, pourtout(y, impl(hyp, concl)))


def compatible_graphe(G, Gp, f, E_set, x="x", y="y"):
    """compatible_graphe(G,G',f,E) :=
        (∀x)(∀y)((x∈E et y∈E) ⇒ ((x,y)∈G ⇔ (f(x),f(y))∈G')).

    Variante CAPTURE-SAFE de `compatible_ordre` (ensembles_ordre_vocab) : la valeur
    f(·) utilise le liant frais « yv » (_val), si bien que f(x) et f(y) DÉPENDENT
    réellement de x, y et restent corrects après instanciation des deux quantifs
    (∀x)(∀y) — contrairement à la version vocab dont le τy interne du graphe
    coïncide avec le liant y et fige f(y).  Convention graphe : R{x,y}=(x,y)∈G,
    R'{u,v}=(u,v)∈G'.  Cœur de la Déf. III.1.3 d'isomorphisme d'ordre."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             equiv(_couple_dans(vx, vy, G), _couple_dans(_val(f, vx), _val(f, vy), Gp)))))


# ════════════════════════════════════════════════════════════════════════════
#  TREILLIS / BORNE — borne inférieure unique, plus petit élt = borne inf
#  (E.III.1.9 ; duals des théorèmes borne_superieure_* déjà présents)
# ════════════════════════════════════════════════════════════════════════════
def borne_inferieure_unique(G, A, E_set="E", a="a", b="b", x="x", y="y"):
    """{ antisymetrie(G), a borne inf de A, b borne inf de A } ⊢ a=b.

    La borne inférieure, si elle existe, est UNIQUE.  a et b sont des minorants ;
    a étant le PLUS GRAND minorant, (b,a)∈G ; de même (a,b)∈G ; antisymétrie ⇒ a=b.
    (E.III.1.9, dual de borne_superieure_unique.)"""
    va, vb = _terme(a), _terme(b)
    Has = N.assume(antisymetrie(G, x, y))
    Ha = N.assume(borne_inferieure(G, A, va, E_set, x, y))   # min(a) et (∀y)(min(y)⇒(y,a)∈G)
    Hb = N.assume(borne_inferieure(G, A, vb, E_set, x, y))   # min(b) et (∀y)(min(y)⇒(y,b)∈G)
    a_min = conjonction_elim_gauche(Ha)                   # minorant(G,A,a,E)
    b_min = conjonction_elim_gauche(Hb)                   # minorant(G,A,b,E)
    a_greatest = conjonction_elim_droite(Ha)              # (∀y)(min(y)⇒(y,a)∈G)
    b_greatest = conjonction_elim_droite(Hb)              # (∀y)(min(y)⇒(y,b)∈G)
    ba = N.modus_ponens(b_min, instancie(a_greatest, vb))  # (b,a)∈G   (b minore, a plus grand)
    ab = N.modus_ponens(a_min, instancie(b_greatest, va))  # (a,b)∈G   (a minore, b plus grand)
    antisym_ab = instancie(instancie(Has, va), vb)        # ((a,b)∈G et (b,a)∈G)⇒a=b
    return N.modus_ponens(conjonction_intro(ab, ba), antisym_ab)


def plus_petit_est_borne_inferieure(G, A, E_set="E", m="m", x="x", y="y"):
    """{ A⊂E, m plus petit élt de A } ⊢ borne_inferieure(G,A,m,E).

    Le plus petit élément de A est sa borne inférieure : c'est un minorant et c'est
    le PLUS GRAND des minorants — car si y minore A, alors comme m∈A on a (y,m)∈G.
    (E.III.1.9, dual de plus_grand_est_borne_superieure.)"""
    vm, vA, vE, vy = _terme(m), _terme(A), _terme(E_set), var(y)
    Hsub = N.assume(inclus(vA, vE))
    Hm = N.assume(plus_petit_element(G, A, vm, x))         # m∈A et (∀x)(x∈A⇒(m,x)∈G)
    m_in_A = conjonction_elim_gauche(Hm)                  # m∈A
    m_min_body = conjonction_elim_droite(Hm)              # (∀x)(x∈A⇒(m,x)∈G)
    m_in_E = N.modus_ponens(m_in_A, instancie(Hsub, vm))  # m∈E
    # (1) m est un minorant de A dans E
    minorant_m = conjonction_intro(m_in_E, m_min_body)    # minorant(G,A,m,E)
    # (2) m est le plus grand minorant : (∀y)(minorant(y)⇒(y,m)∈G)
    Hy = N.assume(minorant(G, A, vy, E_set, x))           # y∈E et (∀x)(x∈A⇒(y,x)∈G)
    y_min = conjonction_elim_droite(Hy)                   # (∀x)(x∈A⇒(y,x)∈G)
    ym = N.modus_ponens(m_in_A, instancie(y_min, vm))     # (y,m)∈G    (m∈A)
    body = N.loi_deduction(minorant(G, A, vy, E_set, x), ym)
    plus_grand = N.generalisation(y, body)
    return conjonction_intro(minorant_m, plus_grand)      # borne_inferieure(G,A,m,E)


# ════════════════════════════════════════════════════════════════════════════
#  MONOTONIE — composée de croissantes est croissante  (E.III.1.5)
#  La composée g'∘g est représentée par une application h dont la valeur vérifie
#  h(x)=g'(g(x)) sur E (hypothèse de composition, honnête).
# ════════════════════════════════════════════════════════════════════════════
def _compose_val(h, gp, g, E_set, x="x"):
    """Hypothèse « h représente g'∘g sur E » := (∀x)(x∈E ⇒ h(x)=g'(g(x)))."""
    vx, vE = var(x), _terme(E_set)
    return pourtout(x, impl(appartient(vx, vE), egal(_val(h, vx), _val(gp, _val(g, vx)))))


def composee_croissantes_est_croissante(G="G", Gp="Gp", Gpp="Gpp", g="g", gp="gp",
                                        h="h", E_set="E", Ep_set="Ep",
                                        x="x", y="y", t="t"):
    """{ croissante(G,G',g,E), croissante(G',G'',g',E'),
         (∀t)(t∈E ⇒ g(t)∈E'), (∀x)(x∈E ⇒ h(x)=g'(g(x))) }
        ⊢ croissante_graphe(G,G'',h,E).

    « La composée de deux applications croissantes est croissante » (E.III.1.5).
    Soit x≤y dans E : g croissante donne g(x)≤'g(y) dans E', et g' croissante
    (appliquée à g(x),g(y)∈E') donne g'(g(x))≤''g'(g(y)) ; comme h(x)=g'(g(x)) et
    h(y)=g'(g(y)), on obtient h(x)≤''h(y)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    Hg = N.assume(croissante_graphe(G, Gp, g, E_set, x, y))       # g croissante E→E'
    Hgp = N.assume(croissante_graphe(Gp, Gpp, gp, Ep_set, x, y))  # g' croissante E'→E''
    Hbut = N.assume(pourtout(t, impl(appartient(var(t), vE),
                                     appartient(_val(g, var(t)), _terme(Ep_set)))))  # g(t)∈E'
    Hcomp = N.assume(_compose_val(h, gp, g, E_set, x))            # h(x)=g'(g(x))

    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    Hh = N.assume(hyp)
    x_in = conjonction_elim_gauche(conjonction_elim_gauche(Hh))  # x∈E
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hh))  # y∈E
    xy_in_G = conjonction_elim_droite(Hh)                        # (x,y)∈G

    # (1) g(x)≤'g(y) : g croissante en (x,y)
    g_inst = instancie(instancie(Hg, vx), vy)
    gx_le_gy = N.modus_ponens(conjonction_intro(conjonction_intro(x_in, y_in), xy_in_G),
                              g_inst)                            # (g(x),g(y))∈G'
    # (2) g(x),g(y)∈E'
    gx_in = N.modus_ponens(x_in, instancie(Hbut, vx))           # g(x)∈E'
    gy_in = N.modus_ponens(y_in, instancie(Hbut, vy))           # g(y)∈E'
    # (3) g'(g(x))≤''g'(g(y)) : g' croissante en (g(x),g(y))
    gp_inst = instancie(instancie(Hgp, _val(g, vx)), _val(g, vy))
    h_full = conjonction_intro(conjonction_intro(gx_in, gy_in), gx_le_gy)
    gpgx_le = N.modus_ponens(h_full, gp_inst)                   # (g'(g(x)),g'(g(y)))∈G''
    # (4) transport h(x)=g'(g(x)), h(y)=g'(g(y))  (Leibniz sur chaque coordonnée)
    hx_eq = N.modus_ponens(x_in, instancie(Hcomp, vx))         # h(x)=g'(g(x))
    hy_eq = N.modus_ponens(y_in, instancie(Hcomp, vy))         # h(y)=g'(g(y))
    # remplacer 1re coordonnée : Φ(w)=(w, g'(g(y)))∈G''
    phi1 = _couple_dans(var("w"), _val(gp, _val(g, vy)), Gpp)
    leib1 = N.s6(_val(h, vx), _val(gp, _val(g, vx)), "w", phi1)  # (h(x)=g'(g(x)))⇒(Φ(h(x))⇔Φ(g'(g(x))))
    eqv1 = N.modus_ponens(hx_eq, leib1)
    step1 = N.modus_ponens(gpgx_le, equivalence_arriere(eqv1))  # (h(x), g'(g(y)))∈G''
    # remplacer 2e coordonnée : Ψ(w)=(h(x), w)∈G''
    psi2 = _couple_dans(_val(h, vx), var("w"), Gpp)
    leib2 = N.s6(_val(h, vy), _val(gp, _val(g, vy)), "w", psi2)
    eqv2 = N.modus_ponens(hy_eq, leib2)
    step2 = N.modus_ponens(step1, equivalence_arriere(eqv2))    # (h(x), h(y))∈G''
    body = N.loi_deduction(hyp, step2)
    return N.generalisation(x, N.generalisation(y, body))


def _equiv_replace_rpp(eqv, Rpp, u_old, v_old, u_new, v_new, u_eq, v_eq):
    """De Γ⊢(P ⇔ R''{u_old,v_old}), u_old=u_new, v_old=v_new
       déduit Γ⊢(P ⇔ R''{u_new,v_new})  (Leibniz sur les deux arguments de R'')."""
    # remplace 1re coordonnée : Φ(w)=R''{w, v_old}
    leib1 = N.s6(u_old, u_new, "w", Rpp(var("w"), v_old))   # (u_old=u_new)⇒(R''{u_old,v_old}⇔R''{u_new,v_old})
    e1 = N.modus_ponens(u_eq, leib1)
    step1 = equivalence_transitivite(eqv, e1)             # P ⇔ R''{u_new,v_old}
    # remplace 2e coordonnée : Ψ(w)=R''{u_new, w}
    leib2 = N.s6(v_old, v_new, "w", Rpp(u_new, var("w")))
    e2 = N.modus_ponens(v_eq, leib2)                     # R''{u_new,v_old}⇔R''{u_new,v_new}
    return equivalence_transitivite(step1, e2)           # P ⇔ R''{u_new,v_new}


def composee_compatibles_est_compatible(G="G", Gp="Gp", Gpp="Gpp", f="f", fp="fp",
                                        h="h", e="E", ep="Ep",
                                        x="x", y="y", t="t"):
    """{ compatible_graphe(G,G',f,E), compatible_graphe(G',G'',f',E'),
         (∀t)(t∈E ⇒ f(t)∈E'), (∀x)(x∈E ⇒ h(x)=f'(f(x))) }
        ⊢ compatible_graphe(G,G'',h,E).

    « La composée f'∘f de deux applications compatibles à l'ordre est compatible »
    (cœur de « composée d'isomorphismes est un isomorphisme », E.III.1.3) : pour
    x,y∈E,  x≤y ⇔ f(x)≤'f(y) (f compatible)  ⇔ f'(f(x))≤''f'(f(y)) (f' compatible,
    f(x),f(y)∈E')  ⇔ h(x)≤''h(y) (h(x)=f'(f(x)))."""
    Rpp = lambda u, v: _couple_dans(u, v, Gpp)
    vx, vy, vE, vEp = var(x), var(y), _terme(e), _terme(ep)
    fx, fy = _val(f, vx), _val(f, vy)
    fpfx, fpfy = _val(fp, fx), _val(fp, fy)

    Hf = N.assume(compatible_graphe(G, Gp, f, e, x, y))       # x≤y ⇔ f(x)≤'f(y)
    Hfp = N.assume(compatible_graphe(Gp, Gpp, fp, ep, x, y))  # u≤'v ⇔ f'(u)≤''f'(v)
    Hbut = N.assume(pourtout(t, impl(appartient(var(t), vE),
                                     appartient(_val(f, var(t)), vEp))))   # f(t)∈E'
    Hcomp = N.assume(pourtout(x, impl(appartient(vx, vE),
                                      egal(_val(h, vx), fpfx))))           # h(x)=f'(f(x))

    Hxy = N.assume(et(appartient(vx, vE), appartient(vy, vE)))
    x_in = conjonction_elim_gauche(Hxy)                    # x∈E
    y_in = conjonction_elim_droite(Hxy)                    # y∈E
    # f compatible en (x,y) : (x≤y) ⇔ (f(x)≤'f(y))
    eqv_f = N.modus_ponens(conjonction_intro(x_in, y_in),
                           instancie(instancie(Hf, vx), vy))
    fx_in = N.modus_ponens(x_in, instancie(Hbut, vx))      # f(x)∈E'
    fy_in = N.modus_ponens(y_in, instancie(Hbut, vy))      # f(y)∈E'
    # f' compatible en (f(x),f(y)) : (f(x)≤'f(y)) ⇔ (f'(f(x))≤''f'(f(y)))
    eqv_fp = N.modus_ponens(conjonction_intro(fx_in, fy_in),
                            instancie(instancie(Hfp, fx), fy))
    chained = equivalence_transitivite(eqv_f, eqv_fp)      # (x≤y) ⇔ (f'(f(x))≤''f'(f(y)))
    hx_eq = N.modus_ponens(x_in, instancie(Hcomp, vx))     # h(x)=f'(f(x))
    hy_eq = N.modus_ponens(y_in, instancie(Hcomp, vy))     # h(y)=f'(f(y))
    # on réécrit f'(f(·)) → h(·) dans chained ; il faut l'égalité f'(f(·))=h(·)
    fx_eq_h = N.modus_ponens(hx_eq, symetrie(_val(h, vx), fpfx))   # f'(f(x))=h(x)
    fy_eq_h = N.modus_ponens(hy_eq, symetrie(_val(h, vy), fpfy))   # f'(f(y))=h(y)
    repl = _equiv_replace_rpp(chained, Rpp, fpfx, fpfy,
                              _val(h, vx), _val(h, vy), fx_eq_h, fy_eq_h)   # (x≤y) ⇔ (h(x)≤''h(y))
    body = N.loi_deduction(et(appartient(vx, vE), appartient(vy, vE)), repl)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  ISOMORPHISMES — réciproque compatible, préservation des extrémités  (E.III.1.3)
# ════════════════════════════════════════════════════════════════════════════
def compatible_reciproque(G="G", Gp="Gp", f="f", g="g", e="E", ep="Ep",
                          x="x", y="y", u="u", v="v"):
    """{ compatible_graphe(G,G',f,E),
         (∀u)(u∈E' ⇒ f(g(u))=u),  (∀u)(u∈E' ⇒ g(u)∈E) }
        ⊢ compatible_graphe(G',G,g,E').

    « La réciproque d'un isomorphisme d'ordre est un isomorphisme d'ordre »
    (cœur, E.III.1.3) : pour u,v∈E', g(u),g(v)∈E ; f compatible donne
    g(u)≤g(v) ⇔ f(g(u))≤'f(g(v)) ⇔ u≤'v (car f(g(u))=u, f(g(v))=v).  Donc
    u≤'v ⇔ g(u)≤g(v), c.-à-d. g est compatible (E',G')→(E,G)."""
    vu, vv, vE, vEp = var(u), var(v), _terme(e), _terme(ep)
    gu, gv = _val(g, vu), _val(g, vv)
    fgu, fgv = _val(f, gu), _val(f, gv)

    Hf = N.assume(compatible_graphe(G, Gp, f, e, x, y))    # a≤b ⇔ f(a)≤'f(b)  (a,b∈E)
    Hinv = N.assume(pourtout(u, impl(appartient(vu, vEp), egal(fgu, vu))))   # f(g(u))=u
    Hdom = N.assume(pourtout(u, impl(appartient(vu, vEp), appartient(gu, vE))))  # g(u)∈E

    Huv = N.assume(et(appartient(vu, vEp), appartient(vv, vEp)))
    u_in = conjonction_elim_gauche(Huv)                   # u∈E'
    v_in = conjonction_elim_droite(Huv)                   # v∈E'
    gu_in = N.modus_ponens(u_in, instancie(Hdom, vu))     # g(u)∈E
    gv_in = N.modus_ponens(v_in, instancie(Hdom, vv))     # g(v)∈E
    # f compatible en (g(u),g(v)) : g(u)≤g(v) ⇔ f(g(u))≤'f(g(v))
    eqv_f = N.modus_ponens(conjonction_intro(gu_in, gv_in),
                           instancie(instancie(Hf, gu), gv))
    fgu_eq = N.modus_ponens(u_in, instancie(Hinv, vu))    # f(g(u))=u
    fgv_eq = N.modus_ponens(v_in, instancie(Hinv, vv))    # f(g(v))=v
    # eqv_f : (g(u)≤g(v)) ⇔ R'{f(g(u)),f(g(v))} ; remplacer f(g(·)) par · à droite
    Rgp = lambda s, t: _couple_dans(s, t, Gp)
    repl = _equiv_replace_rpp(eqv_f, Rgp, fgu, fgv, vu, vv, fgu_eq, fgv_eq)
    # repl : (g(u)≤g(v)) ⇔ (u≤'v) ; on veut (u≤'v) ⇔ (g(u)≤g(v))  (symétrie de ⇔)
    sym = _equiv_intro(equivalence_arriere(repl), equivalence_avant(repl))
    body = N.loi_deduction(et(appartient(vu, vEp), appartient(vv, vEp)), sym)
    return N.generalisation(u, N.generalisation(v, body))


def iso_preserve_plus_grand(G="G", Gp="Gp", f="f", e="E", ep="Ep", m="m",
                            x="x", y="y", t="t"):
    """{ compatible_graphe(G,G',f,E),  (∀t)(t∈E ⇒ f(t)∈E'),
         (∀v)(v∈E' ⇒ (∃u)(u∈E et f(u)=v)),
         m∈E et (∀x)(x∈E ⇒ (x,m)∈G) } ⊢ f(m)∈E' et (∀v)(v∈E' ⇒ (v,f(m))∈G').

    « Un isomorphisme d'ordre préserve le plus grand élément » (E.III.1.3) : f(m)∈E'
    et pour tout v∈E', il existe u∈E avec f(u)=v ; comme x≤m pour tout x∈E,
    u≤m vrai, donc f(u)≤'f(m) (compatibilité), i.e. v≤'f(m)."""
    vE, vEp, vm = _terme(e), _terme(ep), _terme(m)
    fm = _val(f, vm)
    vv, vu = var("v"), var("u")
    fu = _val(f, vu)
    Rgp = lambda s, tt: _couple_dans(s, tt, Gp)

    Hf = N.assume(compatible_graphe(G, Gp, f, e, x, y))
    Hbut = N.assume(pourtout(t, impl(appartient(var(t), vE),
                                     appartient(_val(f, var(t)), vEp))))
    surj = pourtout("v", impl(appartient(vv, vEp),
                              existe("u", et(appartient(vu, vE), egal(fu, vv)))))
    Hsur = N.assume(surj)
    pge_E = et(appartient(vm, vE),
               pourtout(x, impl(appartient(var(x), vE), _couple_dans(var(x), vm, G))))
    Hm = N.assume(pge_E)
    m_in = conjonction_elim_gauche(Hm)                    # m∈E
    m_maj = conjonction_elim_droite(Hm)                   # (∀x)(x∈E ⇒ (x,m)∈G)
    fm_in = N.modus_ponens(m_in, instancie(Hbut, vm))     # f(m)∈E'

    # corps « plus grand » : (∀v)(v∈E' ⇒ (v,f(m))∈G')
    Hv = N.assume(appartient(vv, vEp))                    # v∈E'
    ex_u = N.modus_ponens(Hv, instancie(Hsur, vv))        # (∃u)(u∈E et f(u)=v)
    Hu = N.assume(et(appartient(vu, vE), egal(fu, vv)))   # u∈E et f(u)=v   (témoin)
    u_in = conjonction_elim_gauche(Hu)                    # u∈E
    fu_eq_v = conjonction_elim_droite(Hu)                 # f(u)=v
    um = N.modus_ponens(u_in, instancie(m_maj, vu))       # (u,m)∈G
    eqv_um = N.modus_ponens(conjonction_intro(u_in, m_in),
                            instancie(instancie(Hf, vu), vm))   # (u,m)∈G ⇔ (f(u),f(m))∈G'
    fu_le_fm = N.modus_ponens(um, equivalence_avant(eqv_um))    # (f(u),f(m))∈G'
    leib = N.s6(fu, vv, "w", Rgp(var("w"), fm))           # (f(u)=v)⇒((f(u),f(m))∈G'⇔(v,f(m))∈G')
    v_le_fm = N.modus_ponens(fu_le_fm,
                             equivalence_avant(N.modus_ponens(fu_eq_v, leib)))   # (v,f(m))∈G'
    sous_u = N.loi_deduction(et(appartient(vu, vE), egal(fu, vv)), v_le_fm)
    ex_imp = existe_elimination(sous_u, "u")
    v_le_fm2 = N.modus_ponens(ex_u, ex_imp)               # (v,f(m))∈G'
    body = N.loi_deduction(appartient(vv, vEp), v_le_fm2)
    plus_grand_body = N.generalisation("v", body)         # (∀v)(v∈E' ⇒ (v,f(m))∈G')
    return conjonction_intro(fm_in, plus_grand_body)


def iso_preserve_plus_petit(G="G", Gp="Gp", f="f", e="E", ep="Ep", m="m",
                            x="x", y="y", t="t"):
    """Dual de iso_preserve_plus_grand : un iso d'ordre envoie le plus PETIT élt de
    E sur le plus petit élt de E'.  Conclusion : f(m)∈E' et (∀v)(v∈E' ⇒ (f(m),v)∈G').
    (E.III.1.3.)"""
    vE, vEp, vm = _terme(e), _terme(ep), _terme(m)
    fm = _val(f, vm)
    vv, vu = var("v"), var("u")
    fu = _val(f, vu)
    Rgp = lambda s, tt: _couple_dans(s, tt, Gp)

    Hf = N.assume(compatible_graphe(G, Gp, f, e, x, y))
    Hbut = N.assume(pourtout(t, impl(appartient(var(t), vE),
                                     appartient(_val(f, var(t)), vEp))))
    surj = pourtout("v", impl(appartient(vv, vEp),
                              existe("u", et(appartient(vu, vE), egal(fu, vv)))))
    Hsur = N.assume(surj)
    ppe_E = et(appartient(vm, vE),
               pourtout(x, impl(appartient(var(x), vE), _couple_dans(vm, var(x), G))))  # m≤x
    Hm = N.assume(ppe_E)
    m_in = conjonction_elim_gauche(Hm)
    m_min = conjonction_elim_droite(Hm)                   # (∀x)(x∈E ⇒ (m,x)∈G)
    fm_in = N.modus_ponens(m_in, instancie(Hbut, vm))     # f(m)∈E'

    Hv = N.assume(appartient(vv, vEp))
    ex_u = N.modus_ponens(Hv, instancie(Hsur, vv))
    Hu = N.assume(et(appartient(vu, vE), egal(fu, vv)))
    u_in = conjonction_elim_gauche(Hu)
    fu_eq_v = conjonction_elim_droite(Hu)
    mu = N.modus_ponens(u_in, instancie(m_min, vu))       # (m,u)∈G
    eqv_mu = N.modus_ponens(conjonction_intro(m_in, u_in),
                            instancie(instancie(Hf, vm), vu))   # (m,u)∈G ⇔ (f(m),f(u))∈G'
    fm_le_fu = N.modus_ponens(mu, equivalence_avant(eqv_mu))    # (f(m),f(u))∈G'
    leib = N.s6(fu, vv, "w", Rgp(fm, var("w")))           # (f(u)=v)⇒((f(m),f(u))∈G'⇔(f(m),v)∈G')
    fm_le_v = N.modus_ponens(fm_le_fu,
                             equivalence_avant(N.modus_ponens(fu_eq_v, leib)))   # (f(m),v)∈G'
    sous_u = N.loi_deduction(et(appartient(vu, vE), egal(fu, vv)), fm_le_v)
    ex_imp = existe_elimination(sous_u, "u")
    fm_le_v2 = N.modus_ponens(ex_u, ex_imp)
    body = N.loi_deduction(appartient(vv, vEp), fm_le_v2)
    plus_petit_body = N.generalisation("v", body)
    return conjonction_intro(fm_in, plus_petit_body)


# ════════════════════════════════════════════════════════════════════════════
#  INTERVALLES — [a,b] non vide ⇔ a≤b  (E.III.1.13)
#  Le terme E.intervalle_ferme(R,E,a,b) = app("interv_ff",…) n'a PAS d'axiome de
#  membership dans ensembles_abrege ; on en pose un ICI, en théorie DÉDIÉE.
# ════════════════════════════════════════════════════════════════════════════
def _rg(G):
    """Relation Python ≤ associée au graphe G : (u,v) ↦ (u,v)∈G  (signature attendue
    par E.intervalle_ferme, qui ne l'utilise pas dans la NOTATION app('interv_ff',…))."""
    return lambda u, v: appartient(E.couple(u, v), _terme(G))


def axiome_intervalle_ferme(G="G", e="E", a="a", b="b", x="x"):
    """⊢-schéma : (∀E)(∀a)(∀b)(∀x)( x∈[a,b] ⇔ (x∈E et (a,x)∈G et (x,b)∈G) ).
    (E.III.1.13, [a,b]={x∈E | a≤x et x≤b}.)  Légitimé par S8 (sélection dans E)+A1.

    Convention « graphe G » : a≤x := (a,x)∈G ; x≤b := (x,b)∈G."""
    vE, va, vb, vx = var(e), var(a), var(b), var(x)
    return pourtout(e, pourtout(a, pourtout(b, pourtout(x,
        equiv(appartient(vx, E.intervalle_ferme(_rg(G), vE, va, vb)),
              et(et(appartient(vx, vE), _couple_dans(va, vx, G)),
                 _couple_dans(vx, vb, G)))))))


def theorie_intervalle_ferme(G="G", e="E", a="a", b="b", x="x"):
    """Théorie DÉDIÉE portant l'axiome de membership de l'intervalle fermé [a,b]
    (E.III.1.13).  theorie_ensembles INCHANGÉE (= 22 axiomes)."""
    return N.Theorie("IntervalleFerme", axiomes=[axiome_intervalle_ferme(G, e, a, b, x)])


def intervalle_ferme_a_dans(G="G", e="E", a="a", b="b", x="x"):
    """{ a∈E, (a,a)∈G, (a,b)∈G } ⊢ a ∈ [a,b]   (axiome de [a,b] déchargé).

    L'extrémité gauche a appartient à [a,b] dès que a∈E, a≤a et a≤b : par le sens ⇐
    de l'axiome de membership.  (E.III.1.13.)"""
    th = theorie_intervalle_ferme(G, e, a, b, x)
    ax = N.axiome(th, axiome_intervalle_ferme(G, e, a, b, x))
    va, vb, vE = _terme(a), _terme(b), _terme(e)
    # instancier l'axiome en (E,a,b,a)
    ax_inst = instancie(instancie(instancie(instancie(ax, vE), va), vb), va)
    # ax_inst : a∈[a,b] ⇔ (a∈E et (a,a)∈G et (a,b)∈G)
    Ha = N.assume(appartient(va, vE))                     # a∈E
    Haa = N.assume(_couple_dans(va, va, G))               # (a,a)∈G  (réflexivité a≤a)
    Hab = N.assume(_couple_dans(va, vb, G))               # (a,b)∈G  (a≤b)
    rhs = conjonction_intro(conjonction_intro(Ha, Haa), Hab)
    return N.modus_ponens(rhs, equivalence_arriere(ax_inst))   # a∈[a,b]


def intervalle_ferme_non_vide_si_a_inf_b(G="G", e="E", a="a", b="b", x="x", z="z"):
    """{ a∈E, (a,a)∈G, (a,b)∈G } ⊢ ¬([a,b] = ∅).

    « Si a≤b (et a∈E), l'intervalle fermé [a,b] n'est pas vide » (E.III.1.13 : « un
    intervalle fermé n'est jamais vide » lorsque a≤b) : a∈[a,b]
    (intervalle_ferme_a_dans), donc (∃z)(z∈[a,b]), donc [a,b]≠∅
    (non_vide_ssi_element)."""
    va, vE = _terme(a), _terme(e)
    a_dans = intervalle_ferme_a_dans(G, e, a, b, x)       # a∈[a,b]
    ens = E.intervalle_ferme(_rg(G), vE, va, _terme(b))
    # (∃z)(z∈[a,b])  via S5 (témoin a)
    r = appartient(var(z), ens)
    ex_z = N.modus_ponens(a_dans, N.s5(r, va, z))         # (∃z)(z∈[a,b])
    # ¬([a,b]=∅) ⇔ (∃z)(z∈[a,b])  → backward
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    nv = non_vide_ssi_element(ens)                        # ¬(ens=∅) ⇔ (∃z)(z∈ens)
    return N.modus_ponens(ex_z, equivalence_arriere(nv))  # ¬([a,b]=∅)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 11 (E.III.1.12) — strictement monotone ⇒ injective
#  Sur E TOTALEMENT ordonné.  Conclusion : injective sur E au sens
#  (∀x)(∀y)((x∈E et y∈E et f(x)=f(y)) ⇒ x=y).
# ════════════════════════════════════════════════════════════════════════════
def injective_sur(f, E_set, x="x", y="y"):
    """injective_sur(f,E) := (∀x)(∀y)((x∈E et y∈E et f(x)=f(y)) ⇒ x=y).

    Forme GARDÉE par E (« deux éléments de E »), fidèle à E.III.1.12."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), egal(_val(f, vx), _val(f, vy)))
    return pourtout(x, pourtout(y, impl(hyp, egal(vx, vy))))


def _str_cr(G, Gp, f, E_set, x, y):
    """(∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(x)<f(y))  (str. croissante plate)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    return pourtout(x, pourtout(y,
        impl(et(et(appartient(vx, vE), appartient(vy, vE)), _strict(vx, vy, G)),
             _strict(_val(f, vx), _val(f, vy), Gp))))


def _str_dec(G, Gp, f, E_set, x, y):
    """(∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(y)<f(x))  (str. décroissante plate)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    return pourtout(x, pourtout(y,
        impl(et(et(appartient(vx, vE), appartient(vy, vE)), _strict(vx, vy, G)),
             _strict(_val(f, vy), _val(f, vx), Gp))))


def strictement_croissante_injective_graphe(G="G", Gp="Gp", f="f", E_set="E",
                                            x="x", y="y", z="z"):
    """{ totalement_ordonne(G,E), strictement_croissante(G,G',f,E) }
        ⊢ injective_sur(f,E).

    PROPOSITION 11 (E.III.1.12), cas strictement croissant : sur E TOTALEMENT
    ordonné, x≠y entraîne (par totalité) x<y ou y<x, donc f(x)<f(y) ou f(y)<f(x)
    (stricte croissance), donc dans les deux cas f(x)≠f(y).  Contraposée : f(x)=f(y)
    ⇒ x=y."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    Htot = N.assume(totalement_ordonne(G, E_set, x, y, z))
    Hsc = N.assume(_str_cr(G, Gp, f, E_set, x, y))
    comparables = conjonction_elim_droite(Htot)           # (∀x∀y)((x∈E et y∈E)⇒(x≤y ou y≤x))

    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), egal(_val(f, vx), _val(f, vy)))
    Hh = N.assume(hyp)
    x_in = conjonction_elim_gauche(conjonction_elim_gauche(Hh))   # x∈E
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hh))   # y∈E
    fx_eq_fy = conjonction_elim_droite(Hh)                # f(x)=f(y)

    disj_eq = tiers_exclu(egal(vx, vy))
    casA = N.loi_deduction(egal(vx, vy), N.assume(egal(vx, vy)))   # x=y ⇒ x=y
    Hneq = N.assume(non(egal(vx, vy)))                    # x≠y
    comp = N.modus_ponens(conjonction_intro(x_in, y_in),
                          instancie(instancie(comparables, vx), vy))   # (x,y)∈G ou (y,x)∈G
    casB_concl = _prop11_cr_cas_neq(Hsc, x_in, y_in, Hneq, comp, fx_eq_fy, vx, vy, f, G, Gp)
    casB = N.loi_deduction(non(egal(vx, vy)), casB_concl)
    par_cas = cas(disj_eq, casA, casB)                    # x=y
    body = N.loi_deduction(hyp, par_cas)
    return N.generalisation(x, N.generalisation(y, body))


def _prop11_cr_cas_neq(Hsc, x_in, y_in, Hneq, comp_disj, fx_eq_fy, vx, vy, f, G, Gp):
    """Sous { x∈E, y∈E, x≠y, (x,y)∈G ou (y,x)∈G, f(x)=f(y) }, dérive x=y par
    contradiction (les deux branches donnent f(x)≠f(y))  [cas croissant]."""
    but = egal(vx, vy)
    # branche 1 : (x,y)∈G → x<y → f(x)<f(y) → f(x)≠f(y)
    Hxy = N.assume(_couple_dans(vx, vy, G))               # (x,y)∈G
    strict_xy = conjonction_intro(Hxy, Hneq)              # (x,y)∈G et x≠y = x<y
    hyp_sc1 = conjonction_intro(conjonction_intro(x_in, y_in), strict_xy)
    sc1 = N.modus_ponens(hyp_sc1, instancie(instancie(Hsc, vx), vy))   # f(x)<f(y)
    fx_neq_fy = conjonction_elim_droite(sc1)              # f(x)≠f(y)
    concl1 = _ex_falso(fx_eq_fy, fx_neq_fy, but)          # x=y  (contradiction)
    casB1 = N.loi_deduction(_couple_dans(vx, vy, G), concl1)
    # branche 2 : (y,x)∈G → y<x → f(y)<f(x) → f(y)≠f(x) → contredit f(x)=f(y)
    Hyx = N.assume(_couple_dans(vy, vx, G))               # (y,x)∈G
    y_neq_x = _neg_sym(Hneq, vx, vy)                      # y≠x
    strict_yx = conjonction_intro(Hyx, y_neq_x)           # (y,x)∈G et y≠x = y<x
    hyp_sc2 = conjonction_intro(conjonction_intro(y_in, x_in), strict_yx)
    sc2 = N.modus_ponens(hyp_sc2, instancie(instancie(Hsc, vy), vx))   # f(y)<f(x)
    fy_neq_fx = conjonction_elim_droite(sc2)              # f(y)≠f(x)
    fy_eq_fx = N.modus_ponens(fx_eq_fy, symetrie(_val(f, vx), _val(f, vy)))  # f(y)=f(x)
    concl2 = _ex_falso(fy_eq_fx, fy_neq_fx, but)          # x=y
    casB2 = N.loi_deduction(_couple_dans(vy, vx, G), concl2)
    return cas(comp_disj, casB1, casB2)                   # x=y


def strictement_decroissante_injective_graphe(G="G", Gp="Gp", f="f", E_set="E",
                                              x="x", y="y", z="z"):
    """{ totalement_ordonne(G,E), strictement_decroissante(G,G',f,E) }
        ⊢ injective_sur(f,E).

    PROPOSITION 11 (E.III.1.12), cas strictement décroissant : symétrique du cas
    croissant.  x≠y ⇒ x<y ou y<x ; stricte décroissance ⇒ f(y)<f(x) ou f(x)<f(y) ;
    dans les deux cas f(x)≠f(y)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    Htot = N.assume(totalement_ordonne(G, E_set, x, y, z))
    Hsd = N.assume(_str_dec(G, Gp, f, E_set, x, y))
    comparables = conjonction_elim_droite(Htot)

    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), egal(_val(f, vx), _val(f, vy)))
    Hh = N.assume(hyp)
    x_in = conjonction_elim_gauche(conjonction_elim_gauche(Hh))
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hh))
    fx_eq_fy = conjonction_elim_droite(Hh)

    disj_eq = tiers_exclu(egal(vx, vy))
    casA = N.loi_deduction(egal(vx, vy), N.assume(egal(vx, vy)))
    Hneq = N.assume(non(egal(vx, vy)))
    comp = N.modus_ponens(conjonction_intro(x_in, y_in),
                          instancie(instancie(comparables, vx), vy))
    casB_concl = _prop11_dec_cas_neq(Hsd, x_in, y_in, Hneq, comp, fx_eq_fy, vx, vy, f, G, Gp)
    casB = N.loi_deduction(non(egal(vx, vy)), casB_concl)
    par_cas = cas(disj_eq, casA, casB)
    body = N.loi_deduction(hyp, par_cas)
    return N.generalisation(x, N.generalisation(y, body))


def _prop11_dec_cas_neq(Hsd, x_in, y_in, Hneq, comp_disj, fx_eq_fy, vx, vy, f, G, Gp):
    """Cas x≠y, version décroissante : les deux branches donnent f(x)≠f(y)."""
    but = egal(vx, vy)
    # branche 1 : (x,y)∈G → x<y → f(y)<f(x) → f(y)≠f(x) → contredit f(x)=f(y)
    Hxy = N.assume(_couple_dans(vx, vy, G))
    strict_xy = conjonction_intro(Hxy, Hneq)              # x<y
    hyp_sd1 = conjonction_intro(conjonction_intro(x_in, y_in), strict_xy)
    sd1 = N.modus_ponens(hyp_sd1, instancie(instancie(Hsd, vx), vy))   # f(y)<f(x)
    fy_neq_fx = conjonction_elim_droite(sd1)              # f(y)≠f(x)
    fy_eq_fx = N.modus_ponens(fx_eq_fy, symetrie(_val(f, vx), _val(f, vy)))  # f(y)=f(x)
    concl1 = _ex_falso(fy_eq_fx, fy_neq_fx, but)
    casB1 = N.loi_deduction(_couple_dans(vx, vy, G), concl1)
    # branche 2 : (y,x)∈G → y<x → f(x)<f(y) → f(x)≠f(y) → contredit f(x)=f(y)
    Hyx = N.assume(_couple_dans(vy, vx, G))
    y_neq_x = _neg_sym(Hneq, vx, vy)                      # y≠x
    strict_yx = conjonction_intro(Hyx, y_neq_x)           # y<x
    hyp_sd2 = conjonction_intro(conjonction_intro(y_in, x_in), strict_yx)
    sd2 = N.modus_ponens(hyp_sd2, instancie(instancie(Hsd, vy), vx))   # f(x)<f(y)
    fx_neq_fy = conjonction_elim_droite(sd2)              # f(x)≠f(y)
    concl2 = _ex_falso(fx_eq_fy, fx_neq_fy, but)
    casB2 = N.loi_deduction(_couple_dans(vy, vx, G), concl2)
    return cas(comp_disj, casB1, casB2)


def strictement_monotone_injective_graphe(G="G", Gp="Gp", f="f", E_set="E",
                                          x="x", y="y", z="z"):
    """{ totalement_ordonne(G,E),
         strictement_croissante(G,G',f,E) ou strictement_decroissante(G,G',f,E) }
        ⊢ injective_sur(f,E).

    PROPOSITION 11 (E.III.1.12) COMPLÈTE : toute application STRICTEMENT MONOTONE
    d'un ensemble totalement ordonné E dans un ensemble ordonné F est INJECTIVE.
    Preuve par cas sur la disjonction monotone, réduite aux deux cas déjà prouvés."""
    str_cr = _str_cr(G, Gp, f, E_set, x, y)
    str_dec = _str_dec(G, Gp, f, E_set, x, y)
    disj = N.assume(ou(str_cr, str_dec))                  # f strictement monotone
    cr_thm = strictement_croissante_injective_graphe(G, Gp, f, E_set, x, y, z)   # {Htot, str_cr} ⊢ inj
    cr_impl = N.loi_deduction(str_cr, cr_thm)             # {Htot} ⊢ str_cr ⇒ inj
    dec_thm = strictement_decroissante_injective_graphe(G, Gp, f, E_set, x, y, z)
    dec_impl = N.loi_deduction(str_dec, dec_thm)          # {Htot} ⊢ str_dec ⇒ inj
    return cas(disj, cr_impl, dec_impl)                   # {Htot, disj} ⊢ inj


__all__ = [
    # treillis / borne
    "croissante_graphe", "compatible_graphe", "injective_sur",
    "borne_inferieure_unique", "plus_petit_est_borne_inferieure",
    # composée
    "composee_croissantes_est_croissante", "composee_compatibles_est_compatible",
    # isomorphismes
    "compatible_reciproque", "iso_preserve_plus_grand", "iso_preserve_plus_petit",
    # intervalles
    "axiome_intervalle_ferme", "theorie_intervalle_ferme",
    "intervalle_ferme_a_dans", "intervalle_ferme_non_vide_si_a_inf_b",
    # proposition 11
    "strictement_croissante_injective_graphe",
    "strictement_decroissante_injective_graphe",
    "strictement_monotone_injective_graphe",
]
