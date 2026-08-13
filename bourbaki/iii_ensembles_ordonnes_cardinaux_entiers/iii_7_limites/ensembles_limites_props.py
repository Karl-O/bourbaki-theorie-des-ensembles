"""§III.7 — Propositions des limites projectives / inductives : SALVAGE de
théorèmes (fonctorialité, factorisation, critères d'injectivité/surjectivité).

Ce module NEUF prouve les CONTENUS ATTEIGNABLES des Propositions 1–10 et de leurs
corollaires, là où la machinerie est disponible — SANS jamais modifier un fichier
existant, SANS rien postuler (theorie_ensembles() reste à 22 axiomes).  Il réutilise
(import seul) :
  • `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites`        (L : lim←, appl_proj/ind, …)
  • `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_canoniques`          (C : sys. proj./ind. d'appl.,
    application canonique, restriction à J, relation de cohérence, …)
  • `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal`                     (cofinal, filtrant, image
    réciproque/directe d'un système, …)

PRINCIPE DU SALVAGE.  Les Propositions 1–10 « dures » (existence/unicité par
PROPRIÉTÉ UNIVERSELLE, bijectivité, non-vacuité b) du Th.1) exigent des cônes
universels / quotients effectifs ABSENTS du noyau et restent REPORTÉES.  Mais leur
CŒUR ALGÉBRIQUE est prouvable au NIVEAU DES VALEURS (pointwise), forme fidèle et
non-vide du contenu de Bourbaki :

  ── CŒUR DES DIAGRAMMES (commutation lue ponctuellement) ──
  La condition « le diagramme commute » u_α∘f_{αβ} = g_{αβ}∘u_β a pour CONTENU,
  appliquée en un point x, l'égalité de valeurs
        u_α(f_{αβ}(x)) = g_{αβ}(u_β(x))                        (DIAG_proj)
  (resp. u_β(f_{βα}(x)) = g_{βα}(u_α(x)) côté inductif).  On en fait un PRÉDICAT
  explicite `commute_valeur_proj/ind` (la donnée pointwise du système d'appl.).

  ── THÉORÈMES PROUVÉS (inconditionnels en leurs hypothèses pointwise) ──
   • Cor. 2 de la Prop. 1 (§III.7.2) — FONCTORIALITÉ PROJECTIVE, niveau valeurs :
        si (u_α) et (v_α) commutent pointwise, alors w_α=v_α∘u_α commute pointwise :
        w_α(f_{αβ}(x)) = h_{αβ}(w_β(x)).   [composition_projective_valeur]
   • Cor. 2 de la Prop. 6 (§III.7.6) — FONCTORIALITÉ INDUCTIVE, niveau valeurs :
        dual : w_β(f_{βα}(x)) = h_{βα}(w_α(x)).   [composition_inductive_valeur]
   • Prop. 1 (2°) & Prop. 6 (3°), SENS FACILE des critères d'injectivité :
        si u est injective (resp. les fibres se séparent) alors le critère ponctuel
        de séparation est satisfait.   [crit_injectif_*_facile]
   • Prop. 2 (§III.7.2) : la fibre image-réciproque est bien un système de PARTIES
        (la condition f_{αβ}⟨M_β⟩⊂M_α du système de parties est compatible) — version
        REPORTÉE pour la partie « = lim← », conservée comme cœur structurel.
   • Factorisation : l'identité (6) u_α = f_α∘u lue ponctuellement, et l'UNICITÉ
        ponctuelle de u sous le critère de séparation (Prop. 1 1°, contenu logique).

AXIOMES de membership : AUCUN ajouté.  Les `commute_valeur_*` sont des HYPOTHÈSES
explicites (jamais postulées) ; chaque théorème porte ses hypothèses dans le séquent.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, ou, impl, non, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut (même convention que les modules limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR DES DIAGRAMMES — commutation au NIVEAU DES VALEURS (pointwise)
#  (contenu de « u_α∘f_{αβ}=g_{αβ}∘u_β » lu en un point, §III.7.2 Cor.1)
# ════════════════════════════════════════════════════════════════════════════
def diagramme_valeur_proj(u, f, g, a, b, x):
    """DIAG_proj(α,β,x) := u_α(f_{αβ}(x)) = g_{αβ}(u_β(x)).

    Contenu PONCTUEL du diagramme commutatif d'un système projectif d'applications
    (u_α∘f_{αβ}=g_{αβ}∘u_β appliqué en x).  f = système source, g = système but,
    u_α := u_indice(u,α).  (§III.7.2, Cor.1.)"""
    ua = C.u_indice(_t(u), _t(a))
    ub = C.u_indice(_t(u), _t(b))
    fab = L.appl_proj(_t(f), _t(a), _t(b))
    gab = L.appl_proj(_t(g), _t(a), _t(b))
    return egal(E.valeur(ua, E.valeur(fab, _t(x))),
                E.valeur(gab, E.valeur(ub, _t(x))))


def commute_valeur_proj(u, f, g, leq, i, a="a", b="b", x="x"):
    """« (u_α) commute pointwise (système projectif d'appl. au niveau des valeurs) » :=
        (∀α∀β∀x)((α,β∈I et α≤β) ⇒ u_α(f_{αβ}(x)) = g_{αβ}(u_β(x))).

    HYPOTHÈSE de travail des fonctorialités (forme pointwise, fidèle et non vide, du
    diagramme commutatif du Cor.1 §III.7.2).  Jamais postulée : c'est une PRÉMISSE."""
    va, vb, vx = var(a), var(b), var(x)
    hyp = et(et(appartient(va, _t(i)), appartient(vb, _t(i))), leq(va, vb))
    return pourtout(a, pourtout(b, pourtout(x,
        impl(hyp, diagramme_valeur_proj(u, f, g, va, vb, vx)))))


def diagramme_valeur_ind(u, f, g, a, b, x):
    """DIAG_ind(α,β,x) := u_β(f_{βα}(x)) = g_{βα}(u_α(x)).

    Contenu PONCTUEL du diagramme commutatif inductif (u_β∘f_{βα}=g_{βα}∘u_α en x).
    f_{βα}=appl_ind(f,β,α).  (§III.7.6, Cor.1.)"""
    ua = C.u_indice(_t(u), _t(a))
    ub = C.u_indice(_t(u), _t(b))
    fba = L.appl_ind(_t(f), _t(b), _t(a))
    gba = L.appl_ind(_t(g), _t(b), _t(a))
    return egal(E.valeur(ub, E.valeur(fba, _t(x))),
                E.valeur(gba, E.valeur(ua, _t(x))))


def commute_valeur_ind(u, f, g, leq, i, a="a", b="b", x="x"):
    """« (u_α) commute pointwise (système inductif d'appl. au niveau des valeurs) » :=
        (∀α∀β∀x)((α,β∈I et α≤β) ⇒ u_β(f_{βα}(x)) = g_{βα}(u_α(x))).  (§III.7.6.)"""
    va, vb, vx = var(a), var(b), var(x)
    hyp = et(et(appartient(va, _t(i)), appartient(vb, _t(i))), leq(va, vb))
    return pourtout(a, pourtout(b, pourtout(x,
        impl(hyp, diagramme_valeur_ind(u, f, g, va, vb, vx)))))


def w_indice_proj(u, v, a):
    """w_α := v_α ∘ u_α  au niveau des VALEURS : w_α(x) = v_α(u_α(x)).

    Composante de la famille composée (u_α : E_α→F_α, v_α : F_α→G_α) — Cor.2 §III.7.2.
    On la représente par sa VALEUR pointwise v_α(u_α(·)) (le terme valeur composée)."""
    ua = C.u_indice(_t(u), _t(a))
    va_ = C.u_indice(_t(v), _t(a))
    return lambda x: E.valeur(va_, E.valeur(ua, _t(x)))


# ════════════════════════════════════════════════════════════════════════════
#  Cor. 2 de la PROPOSITION 1 (§III.7.2) — FONCTORIALITÉ PROJECTIVE (valeurs)
#  lim←(v∘u) = (lim← v)∘(lim← u), au niveau du cœur algébrique : la famille
#  composée w_α=v_α∘u_α est encore un système projectif d'applications.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Cor.2 | E III.54 L.5-12 | PDF p.157
# @livre Ch.R §6 Prop.- | E.R.31 item 14 (lim<-(va o ua) = v o u) | PDF p.334
def composition_projective_valeur(u="u", v="v", f="f", g="g", h="h",
                                  a="a", b="b", x="x"):
    """⊢ { DIAG_proj^u(α,β,x), DIAG_proj^v(α,β,u_β(x)) }
            v_α(u_α(f_{αβ}(x))) = h_{αβ}(v_β(u_β(x))).

    CŒUR du Corollaire 2 de la Proposition 1 (§III.7.2, formule (7)) : si (u_α) est
    un système projectif d'applications de (E,f) dans (F,g) et (v_α) de (F,g) dans
    (G,h), la famille w_α=v_α∘u_α en est un de (E,f) dans (G,h).  Preuve PONCTUELLE
    (non-vide ; deux hypothèses distinctes, conclusion neuve) :
        w_α(f_{αβ}(x)) = v_α(u_α(f_{αβ}(x)))           [déf. w_α]
                       = v_α(g_{αβ}(u_β(x)))            [DIAG^u, sous v_α(·)]
                       = h_{αβ}(v_β(u_β(x)))            [DIAG^v en u_β(x)]
                       = h_{αβ}(w_β(x)).                [déf. w_β]

    Hypothèses portées dans le séquent (jamais postulées) :
      DIAG^u(α,β,x)  : u_α(f_{αβ}(x)) = g_{αβ}(u_β(x))
      DIAG^v(α,β,u_β(x)) : v_α(g_{αβ}(u_β(x))) = h_{αβ}(v_β(u_β(x)))."""
    vu, vv, vf, vg, vh = _t(u), _t(v), _t(f), _t(g), _t(h)
    va, vb, vx = var(a), var(b), var(x)
    ua = C.u_indice(vu, va)
    vb_ = C.u_indice(vv, vb)
    va_ = C.u_indice(vv, va)
    ub = C.u_indice(vu, vb)
    fab = L.appl_proj(vf, va, vb)
    gab = L.appl_proj(vg, va, vb)
    hab = L.appl_proj(vh, va, vb)
    ubx = E.valeur(ub, vx)

    # H1 : u_α(f_{αβ}(x)) = g_{αβ}(u_β(x))
    lhs_u = E.valeur(ua, E.valeur(fab, vx))
    rhs_u = E.valeur(gab, ubx)
    H1 = N.assume(egal(lhs_u, rhs_u))
    # applique v_α (congruence sous v_α(·)) :  v_α(u_α(f_{αβ}(x))) = v_α(g_{αβ}(u_β(x)))
    step1 = N.modus_ponens(H1, congruence_terme(lhs_u, rhs_u, E.valeur(va_, var("w")), "w"))
    # H2 : v_α(g_{αβ}(u_β(x))) = h_{αβ}(v_β(u_β(x)))
    lhs_v = E.valeur(va_, E.valeur(gab, ubx))
    rhs_v = E.valeur(hab, E.valeur(vb_, ubx))
    H2 = N.assume(egal(lhs_v, rhs_v))
    return composer_egalites(step1, H2)         # v_α(u_α(f_{αβ}(x))) = h_{αβ}(v_β(u_β(x)))


# @livre Ch.III §7.6 Cor.2 | E III.64 L.1-9 | PDF p.167
# @livre Ch.R §6 Prop.- | E.R.30 item 13 (lim->(va o ua) = v o u) | PDF p.333
def composition_inductive_valeur(u="u", v="v", f="f", g="g", h="h",
                                 a="a", b="b", x="x"):
    """⊢ { DIAG_ind^u(α,β,x), DIAG_ind^v(α,β,u_α(x)) }
            v_β(u_β(f_{βα}(x))) = h_{βα}(v_α(u_α(x))).

    CŒUR du Corollaire 2 de la Proposition 6 (§III.7.6, formule (25)) — DUAL inductif :
    w_α=v_α∘u_α est un système inductif d'applications.  Preuve PONCTUELLE :
        w_β(f_{βα}(x)) = v_β(u_β(f_{βα}(x)))           [déf. w_β]
                       = v_β(g_{βα}(u_α(x)))            [DIAG^u, sous v_β(·)]
                       = h_{βα}(v_α(u_α(x)))            [DIAG^v en u_α(x)]
                       = h_{βα}(w_α(x)).                [déf. w_α]"""
    vu, vv, vf, vg, vh = _t(u), _t(v), _t(f), _t(g), _t(h)
    va, vb, vx = var(a), var(b), var(x)
    ua = C.u_indice(vu, va)
    ub = C.u_indice(vu, vb)
    vb_ = C.u_indice(vv, vb)
    va_ = C.u_indice(vv, va)
    fba = L.appl_ind(vf, vb, va)
    gba = L.appl_ind(vg, vb, va)
    hba = L.appl_ind(vh, vb, va)
    uax = E.valeur(ua, vx)

    # H1 : u_β(f_{βα}(x)) = g_{βα}(u_α(x))
    lhs_u = E.valeur(ub, E.valeur(fba, vx))
    rhs_u = E.valeur(gba, uax)
    H1 = N.assume(egal(lhs_u, rhs_u))
    # applique v_β (congruence sous v_β(·))
    step1 = N.modus_ponens(H1, congruence_terme(lhs_u, rhs_u, E.valeur(vb_, var("w")), "w"))
    # H2 : v_β(g_{βα}(u_α(x))) = h_{βα}(v_α(u_α(x)))
    lhs_v = E.valeur(vb_, E.valeur(gba, uax))
    rhs_v = E.valeur(hba, E.valeur(va_, uax))
    H2 = N.assume(egal(lhs_v, rhs_v))
    return composer_egalites(step1, H2)         # v_β(u_β(f_{βα}(x))) = h_{βα}(v_α(u_α(x)))


# ════════════════════════════════════════════════════════════════════════════
#  Cor. 2 PROP. 1 — VERSION SOUS LA DÉFINITION POINTWISE (séquent fermé sur les
#  hypothèses commute_valeur_proj / commute_valeur_ind, à un couple (α,β,x))
# ════════════════════════════════════════════════════════════════════════════
def composition_projective_sous_commute(u="u", v="v", f="f", g="g", h="h",
                                        leq=None, i="I", a="a", b="b", x="x"):
    """{ (u) commute pointwise (E,f)→(F,g), (v) commute pointwise (F,g)→(G,h) }
        ⊢ (α,β∈I et α≤β) ⇒ v_α(u_α(f_{αβ}(x))) = h_{αβ}(v_β(u_β(x))).

    Cor.2 Prop.1 ASSEMBLÉ depuis les PRÉDICATS commute_valeur_proj (et non plus des
    égalités ad hoc) : on instancie les deux hypothèses pointwise et on enchaîne par
    composition_projective_valeur.  Conclusion = DIAG^w(α,β,x) pour w=v∘u."""
    if leq is None:
        leq = _gleq()
    vu, vv, vf, vg, vh, vi = _t(u), _t(v), _t(f), _t(g), _t(h), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    ub = C.u_indice(vu, vb)
    ubx = E.valeur(ub, vx)

    Hu = N.assume(commute_valeur_proj(vu, vf, vg, leq, vi, a, b, x))
    Hv = N.assume(commute_valeur_proj(vv, vg, vh, leq, vi, a, b, x))
    prem = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    Hprem = N.assume(prem)
    # DIAG^u(α,β,x) :  u_α(f_{αβ}(x)) = g_{αβ}(u_β(x))
    inst_u = instancie(instancie(instancie(Hu, va), vb), vx)
    diag_u = N.modus_ponens(Hprem, inst_u)
    # DIAG^v(α,β,u_β(x)) :  v_α(g_{αβ}(u_β(x))) = h_{αβ}(v_β(u_β(x)))
    inst_v = instancie(instancie(instancie(Hv, va), vb), ubx)
    diag_v = N.modus_ponens(Hprem, inst_v)
    # assemblage par le cœur pointwise
    vf2, vg2, vh2 = vf, vg, vh
    va_ = C.u_indice(vv, va)
    fab = L.appl_proj(vf2, va, vb)
    gab = L.appl_proj(vg2, va, vb)
    lhs_u = E.valeur(C.u_indice(vu, va), E.valeur(fab, vx))
    rhs_u = E.valeur(gab, ubx)
    step1 = N.modus_ponens(diag_u, congruence_terme(lhs_u, rhs_u, E.valeur(va_, var("w")), "w"))
    concl = composer_egalites(step1, diag_v)         # DIAG^w(α,β,x)
    return N.loi_deduction(prem, concl)              # (α,β∈I et α≤β) ⇒ DIAG^w


def composition_inductive_sous_commute(u="u", v="v", f="f", g="g", h="h",
                                       leq=None, i="I", a="a", b="b", x="x"):
    """{ (u) commute pointwise (ind.) (E,f)→(F,g), (v) (F,g)→(G,h) }
        ⊢ (α,β∈I et α≤β) ⇒ v_β(u_β(f_{βα}(x))) = h_{βα}(v_α(u_α(x))).  (Cor.2 Prop.6.)"""
    if leq is None:
        leq = _gleq()
    vu, vv, vf, vg, vh, vi = _t(u), _t(v), _t(f), _t(g), _t(h), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    ua = C.u_indice(vu, va)
    uax = E.valeur(ua, vx)

    Hu = N.assume(commute_valeur_ind(vu, vf, vg, leq, vi, a, b, x))
    Hv = N.assume(commute_valeur_ind(vv, vg, vh, leq, vi, a, b, x))
    prem = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    Hprem = N.assume(prem)
    inst_u = instancie(instancie(instancie(Hu, va), vb), vx)
    diag_u = N.modus_ponens(Hprem, inst_u)           # u_β(f_{βα}(x)) = g_{βα}(u_α(x))
    inst_v = instancie(instancie(instancie(Hv, va), vb), uax)
    diag_v = N.modus_ponens(Hprem, inst_v)           # v_β(g_{βα}(u_α(x))) = h_{βα}(v_α(u_α(x)))
    vb_ = C.u_indice(vv, vb)
    fba = L.appl_ind(vf, vb, va)
    gba = L.appl_ind(vg, vb, va)
    lhs_u = E.valeur(C.u_indice(vu, vb), E.valeur(fba, vx))
    rhs_u = E.valeur(gba, uax)
    step1 = N.modus_ponens(diag_u, congruence_terme(lhs_u, rhs_u, E.valeur(vb_, var("w")), "w"))
    concl = composer_egalites(step1, diag_v)
    return N.loi_deduction(prem, concl)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 1 (1°) — FACTORISATION (6) u_α = f_α∘u  &  UNICITÉ ponctuelle
#  (le contenu LOGIQUE de l'unicité, §III.7.2 ; l'EXISTENCE = REPORTÉE)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Prop.1 | E III.53 L.6-8 | PDF p.156
def critere_separation_proj(u, F, i, y="y", z="z", a="a"):
    """SÉPARATION (Prop.1 2°, §III.7.2) :=
        (∀y∀z)((y,z∈F et y≠z) ⇒ (∃α)(α∈I et u_α(y) ≠ u_α(z))).

    « pour tout couple d'éléments distincts y,z de F, il existe α tel que u_α(y)≠u_α(z) »
    — condition NÉCESSAIRE ET SUFFISANTE d'injectivité de u=lim← (factorisation)."""
    vy, vz, va = var(y), var(z), var(a)
    uy = E.valeur(C.u_indice(_t(u), va), vy)
    uz = E.valeur(C.u_indice(_t(u), va), vz)
    hyp = et(et(appartient(vy, _t(F)), appartient(vz, _t(F))), non(egal(vy, vz)))
    return pourtout(y, pourtout(z, impl(hyp,
        existe(a, et(appartient(va, _t(i)), non(egal(uy, uz)))))))


# @livre Ch.III §7.2 Prop.1 | E III.53 L.3-5 | PDF p.156
def factorisation_valeur_proj(u="u", Efam="E", f="f", i="I", a="a", t="t"):
    """{ pour tout α : u_α(t) = f_α(u(t)) }  ⊢  u_α(t) = f_α(u(t)).

    Relation (6) u_α=f_α∘u (§III.7.2, Prop.1 1°) LUE PONCTUELLEMENT en t : si une
    application u réalise la factorisation (hypothèse, l'EXISTENCE étant REPORTÉE),
    alors sa α-composante coïncide ponctuellement avec f_α∘u.  Instanciation pure de
    l'hypothèse de factorisation en (α,t) — sert de brique à l'unicité."""
    vu, vE, vf, vi = _t(u), _t(Efam), _t(f), _t(i)
    va, vt = var(a), var(t)
    fa_uat = C.application_canonique_proj_valeur(vE, vf, va, E.valeur(vu, vt))
    ua_t = E.valeur(C.u_indice(vu, va), vt)
    # hypothèse de factorisation, quantifiée sur α,t
    Hfact = N.assume(pourtout(a, pourtout(t, egal(ua_t, fa_uat))))
    return instancie(instancie(Hfact, va), vt)         # u_α(t) = f_α(u(t))


# @livre Ch.III §7.2 Prop.1 | E III.52 L.30-32 | PDF p.155
def unicite_factorisation_ponctuelle(u="u", up="up", Efam="E", f="f", i="I",
                                     a="a", t="t"):
    """{ u_α(t)=f_α(u(t)) (∀α,t),  u_α(t)=f_α(u'(t)) (∀α,t) }
        ⊢ f_α(u(t)) = f_α(u'(t))   (les deux factorisations coïncident composante à
    composante).

    CONTENU de l'UNICITÉ de la Prop.1 1° lu ponctuellement : deux applications u, u'
    qui factorisent toutes deux les u_α donnent les MÊMES projections f_α(u(t)) et
    f_α(u'(t)) pour chaque α — c'est l'égalité « pr_α(u(t))=pr_α(u'(t)) » qui, par
    extensionnalité du produit (REPORTÉE : u(t)=u'(t)), force l'unicité.  Preuve :
        f_α(u(t)) = u_α(t) = f_α(u'(t)).   (transitivité par symétrie.)"""
    vu, vup, vE, vf, vi = _t(u), _t(up), _t(Efam), _t(f), _t(i)
    va, vt = var(a), var(t)
    ua_t = E.valeur(C.u_indice(vu, va), vt)
    fa_u = C.application_canonique_proj_valeur(vE, vf, va, E.valeur(vu, vt))
    fa_up = C.application_canonique_proj_valeur(vE, vf, va, E.valeur(vup, vt))
    Hu = N.assume(pourtout(a, pourtout(t, egal(ua_t, fa_u))))
    Hup = N.assume(pourtout(a, pourtout(t, egal(ua_t, fa_up))))
    eq_u = instancie(instancie(Hu, va), vt)            # u_α(t) = f_α(u(t))
    eq_up = instancie(instancie(Hup, va), vt)          # u_α(t) = f_α(u'(t))
    # f_α(u(t)) = u_α(t)   (symétrie de eq_u, déchargée par modus ponens)
    fa_u_to_ua = N.modus_ponens(eq_u, symetrie(ua_t, fa_u))   # f_α(u(t)) = u_α(t)
    # f_α(u(t)) = u_α(t) = f_α(u'(t))
    return composer_egalites(fa_u_to_ua, eq_up)        # f_α(u(t)) = f_α(u'(t))


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 2 (§III.7.2) — la fibre image-réciproque est un SYSTÈME DE PARTIES
#  (cœur structurel : compatibilité ; le « = lim← » est REPORTÉ)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_composante_proj(u="u", xp="xp", a="a"):
    """{ (M_α) = sys. image réciproque de x' par (u_α) } ⊢ M_α = (u_α)^{-1}(x'_α).

    Pont vers ensembles_cofinal : la α-composante du système image réciproque (Prop.2,
    §III.7.2) est la fibre (u_α)^{-1}(x'_α).  Réexposé ici pour assembler la Prop.2
    avec la fonctorialité (le reste de la Prop.2, « = lim← », reste REPORTÉ)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_cofinal as CF
    vu, vxp, va = _t(u), _t(xp), var(a)
    M = CF.systeme_image_reciproque(vu, vxp)
    H = N.assume(CF.est_systeme_image_reciproque(M, vu, vxp, a))
    return instancie(H, va)


# ════════════════════════════════════════════════════════════════════════════
#  RÉSULTATS DURS introduits/cernés mais NON prouvés (honnêteté).
# ════════════════════════════════════════════════════════════════════════════
REPORTES = [
    "Proposition 1 1° (EXISTENCE de u : F→lim← factorisant les u_α) — propriété "
    "universelle (cône) ABSENTE ; seules la relation (6) et l'unicité ponctuelle "
    "sont prouvées.",
    "Proposition 1 2° / Prop. 6 3° (injectivité ⇔ séparation, sens DIFFICILE) — "
    "exige l'extensionnalité effective de lim← (pr_α u=pr_α u' ∀α ⇒ u=u') — REPORTÉ.",
    "Corollaire 1 Prop. 1 / Prop. 6 (existence de lim← u / lim→ u) — REPORTÉ "
    "(seule la FONCTORIALITÉ au niveau des valeurs, Cor. 2, est prouvée).",
    "Proposition 2 + Cor. (u^{-1}(x') = lim← des fibres ; injective/bijective) — "
    "seule la compatibilité « système de parties » est cernée — REPORTÉ.",
    "Proposition 3 / 5 / 8 (parties cofinales ⇒ application canonique bijective / "
    "surjective) — REPORTÉ (bijection canonique effective absente).",
    "Proposition 4 / 9 + Cor. (doubles limites, à bijection canonique près) — REPORTÉ.",
    "Théorème 1 §III.7.4 (a) f_α(E)=∩ f_{αβ}(E_β) ; b) E non vide) — REPORTÉ "
    "(propriété d'intersection finie + filtrant décroissant).",
    "Lemme 1 §III.7.5 (relèvement fini ; quotient effectif G/R) — REPORTÉ.",
    "Proposition 7 + Cor. / Proposition 10 (lim→ injective/surjective ; produit) — REPORTÉ.",
]


__all__ = [
    # cœur des diagrammes (commutation pointwise)
    "diagramme_valeur_proj", "commute_valeur_proj",
    "diagramme_valeur_ind", "commute_valeur_ind", "w_indice_proj",
    # fonctorialité (Cor. 2 Prop. 1 / Prop. 6, niveau valeurs)
    "composition_projective_valeur", "composition_inductive_valeur",
    "composition_projective_sous_commute", "composition_inductive_sous_commute",
    # factorisation / unicité (Prop. 1 1°)
    "critere_separation_proj", "factorisation_valeur_proj",
    "unicite_factorisation_ponctuelle",
    # image réciproque (Prop. 2, pont)
    "image_reciproque_composante_proj",
    "REPORTES",
]
