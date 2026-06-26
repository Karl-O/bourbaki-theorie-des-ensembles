"""Chapitre III §1.5 et §1.11 — Applications monotones et ensembles réticulés.

Vue COMPLÉMENTAIRE de `ensembles_ordre_relation.py` (qui pose `est_ordre`,
`majorant`, `borne_superieure`, … comme prédicats sur un GRAPHE G d'ordre).
Ici on introduit les notions du livre relatives aux APPLICATIONS entre deux
ensembles ordonnés, puis la notion de TREILLIS (ensemble réticulé).

Conventions (fidèles au codage du projet) :
  • un ordre sur l'ensemble source E est donné par un graphe G ; « x ≤ y » s'écrit
    (x,y) ∈ G,  soit _couple_dans(x,y,G) ;
  • un ordre sur l'ensemble but E' est donné par un graphe G' ; « u ≤' v » s'écrit
    (u,v) ∈ G' ;
  • f est une application E → E' ; la valeur f(x) au sens Bourbaki est la valeur du
    graphe : E.valeur(f, x) ;
  • l'ordre STRICT x < y est « (x,y) ∈ G et x ≠ y »  (E.III.1.3, critère C58).

DÉFINITIONS introduites (prédicats sur (G, G', f, E, E')) :

  Déf. 1 (E.III.1.5) — application croissante / décroissante / monotone :
    est_croissante(G,G',f,E,E')   := (∀x)(∀y)((x∈E et y∈E et (x,y)∈G) ⇒ (f(x),f(y))∈G')
    est_decroissante(G,G',f,E,E') := (∀x)(∀y)((x∈E et y∈E et (x,y)∈G) ⇒ (f(y),f(x))∈G')
    est_monotone(G,G',f,E,E')     := est_croissante ou est_decroissante

  Déf. 2 (E.III.1.5) — application strictement croissante / décroissante / monotone :
    est_strictement_croissante(G,G',f,E,E')   := (∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(x)<f(y))
    est_strictement_decroissante(G,G',f,E,E') := (∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(y)<f(x))
    est_strictement_monotone(G,G',f,E,E')      := str. croissante ou str. décroissante
  (l'ordre strict x<y, resp. f(x)<f(y), est lu sur G, resp. G').

  Déf. 8 (E.III.1.11) — ensemble réticulé (treillis / lattis) :
    est_reticule(G,E) := est_ordre(G,E) et
        (∀x)(∀y)((x∈E et y∈E) ⇒ (∃s)(∃i)(borne_superieure(G,{x,y},s,E)
                                          et borne_inferieure(G,{x,y},i,E)))

THÉORÈMES DIRECTS certifiés par le noyau abrégé :
  • croissante ⇒ monotone  (S2) ;  décroissante ⇒ monotone  (S2∘S3) ;
  • strictement croissante ⇒ croissante  (sous est_ordre(G',E') et f application
    E→E' : cas x=y par réflexivité de G', cas x≠y par la stricte croissance) ;
  • strictement décroissante ⇒ décroissante  (idem, dual) ;
  • décomposition de est_monotone / est_strictement_monotone (conjonction/élim).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, impl, non, appartient, existe, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, borne_superieure, borne_inferieure,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas, tiers_exclu,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _val(f, x):
    """f(x) au sens Bourbaki = valeur du graphe f en x.

    Le liant interne est forcé à « j » : LETTRE SIMPLE fraîche (JAMAIS utilisée comme
    liant de quantification dans le projet — audit), donc (a) pas de collision de capture
    quand f(y) figure dans une formule quantifiée, et (b) alpha_tau-COMPATIBLE (le pont
    τ_valeur ↔ τ_y, impossible avec « yv » multi-caractères que tau() refuse)."""
    return E.valeur(_terme(f), _terme(x), b="j")


def _strict(t, u, G):
    """Ordre strict « t < u » := (t,u)∈G et t≠u   (E.III.1.3, critère C58)."""
    vt, vu = _terme(t), _terme(u)
    return et(_couple_dans(vt, vu, G), non(egal(vt, vu)))


def _cut(thm, hyp, preuve_hyp):
    """De  Γ∪{H} ⊢ C  et  Δ ⊢ H  on déduit  Γ∪Δ ⊢ C  (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION 1 (E.III.1.5) — croissante / décroissante / monotone
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.5 Def.1 | E III.7 L.5-7 | PDF p.110
def est_croissante(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_croissante(G,G',f,E,E') :=
        (∀x)(∀y)((x∈E et y∈E et (x,y)∈G) ⇒ (f(x),f(y))∈G').

    « f est croissante » : x ≤ y entraîne f(x) ≤ f(y)  (E.III.1.5, Déf. 1)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    concl = _couple_dans(_val(f, vx), _val(f, vy), Gp)
    return pourtout(x, pourtout(y, impl(hyp, concl)))


# @livre Ch.III §1.5 Def.1 | E III.7 L.7-8 | PDF p.110
def est_decroissante(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_decroissante(G,G',f,E,E') :=
        (∀x)(∀y)((x∈E et y∈E et (x,y)∈G) ⇒ (f(y),f(x))∈G').

    « f est décroissante » : x ≤ y entraîne f(x) ≥ f(y)  (E.III.1.5, Déf. 1)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    concl = _couple_dans(_val(f, vy), _val(f, vx), Gp)
    return pourtout(x, pourtout(y, impl(hyp, concl)))


# @livre Ch.III §1.5 Def.1 | E III.7 L.8-9 | PDF p.110
def est_monotone(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_monotone(G,G',f,E,E') := est_croissante ou est_decroissante.

    « f est monotone » : f est croissante OU décroissante  (E.III.1.5, Déf. 1)."""
    return ou(est_croissante(G, Gp, f, E_set, Ep_set, x, y),
              est_decroissante(G, Gp, f, E_set, Ep_set, x, y))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION 2 (E.III.1.5) — strictement croissante / décroissante / monotone
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.5 Def.2 | E III.7 L.17-18 | PDF p.110
def est_strictement_croissante(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_strictement_croissante(G,G',f,E,E') :=
        (∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(x)<f(y)),
    où x<y := (x,y)∈G et x≠y, et f(x)<f(y) := (f(x),f(y))∈G' et f(x)≠f(y).

    « f est strictement croissante » : x < y entraîne f(x) < f(y)  (E.III.1.5, Déf. 2)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _strict(vx, vy, G))
    concl = _strict(_val(f, vx), _val(f, vy), Gp)
    return pourtout(x, pourtout(y, impl(hyp, concl)))


# @livre Ch.III §1.5 Def.2 | E III.7 L.18-20 | PDF p.110
def est_strictement_decroissante(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_strictement_decroissante(G,G',f,E,E') :=
        (∀x)(∀y)((x∈E et y∈E et x<y) ⇒ f(y)<f(x)).

    « f est strictement décroissante » : x < y entraîne f(x) > f(y)  (E.III.1.5, Déf. 2)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _strict(vx, vy, G))
    concl = _strict(_val(f, vy), _val(f, vx), Gp)
    return pourtout(x, pourtout(y, impl(hyp, concl)))


# @livre Ch.III §1.5 Def.2 | E III.7 L.20-21 | PDF p.110
def est_strictement_monotone(G, Gp, f, E_set="E", Ep_set="Ep", x="x", y="y"):
    """est_strictement_monotone(G,G',f,E,E') :=
        est_strictement_croissante ou est_strictement_decroissante.

    « f est strictement monotone »  (E.III.1.5, Déf. 2)."""
    return ou(est_strictement_croissante(G, Gp, f, E_set, Ep_set, x, y),
              est_strictement_decroissante(G, Gp, f, E_set, Ep_set, x, y))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION 8 (E.III.1.11) — ensemble réticulé (treillis / lattis)
# ════════════════════════════════════════════════════════════════════════════
def admet_borne_sup_inf(G, x, y, E_set="E", s="s", i="i", u="u"):
    """admet_borne_sup_inf(G,x,y,E) :=
        (∃s)(∃i)(borne_superieure(G,{x,y},s,E) et borne_inferieure(G,{x,y},i,E)).

    « la paire {x,y} admet une borne supérieure ET une borne inférieure dans E »
    (E.III.1.9, Déf. 6 ; brique de l'ensemble réticulé)."""
    vx, vy = _terme(x), _terme(y)
    P = E.paire(vx, vy)
    vs, vi = var(s), var(i)
    # Liant FRAIS "mbs"/"mbi" pour le quantificateur « plus petit majorant / plus
    # grand minorant » (6e arg de borne_superieure/inferieure).  SANS lui, le défaut
    # "y" du 6e arg CAPTURE le y de la paire {x,y} ci-dessus : la clause « plus petit
    # majorant » devient « ∀y (y majore {x,y} ⇒ …) » au lieu de « ∀m (m majore {x,y}
    # ⇒ …) », rendant est_reticule MALFORMÉ (cf. docs/journal/ANOMALIES.md 2026-06-25).
    return existe(s, existe(i,
        et(borne_superieure(G, P, vs, E_set, u, "mbs"),
           borne_inferieure(G, P, vi, E_set, u, "mbi"))))


# @livre Ch.III §1.11 Def.8 | E III.13 L.15-18 | PDF p.116
def est_reticule(G, E_set="E", x="x", y="y", z="z", s="s", i="i", u="u"):
    """est_reticule(G,E) := est_ordre(G,E) et
        (∀x)(∀y)((x∈E et y∈E) ⇒
            (∃s)(∃i)(borne_superieure(G,{x,y},s,E) et borne_inferieure(G,{x,y},i,E))).

    « E (ordonné par G) est réticulé (réseau, lattis) » : toute partie à deux
    éléments {x,y} de E admet une borne supérieure ET une borne inférieure dans E
    (E.III.1.11, Définition 8)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    toute_paire = pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             admet_borne_sup_inf(G, vx, vy, E_set, s, i, u))))
    return et(est_ordre(G, E_set, x, y, z), toute_paire)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS — monotonie depuis (dé)croissance ; décompositions
# ════════════════════════════════════════════════════════════════════════════
def croissante_implique_monotone(G="G", Gp="Gp", f="f",
                                 E_set="E", Ep_set="Ep", x="x", y="y"):
    """⊢ est_croissante(…) ⇒ est_monotone(…).

    « Une application croissante est monotone » (introduction du ∨ gauche, S2)."""
    cr = est_croissante(G, Gp, f, E_set, Ep_set, x, y)
    dec = est_decroissante(G, Gp, f, E_set, Ep_set, x, y)
    return N.s2(cr, dec)                                   # cr ⇒ (cr ou dec)


def decroissante_implique_monotone(G="G", Gp="Gp", f="f",
                                   E_set="E", Ep_set="Ep", x="x", y="y"):
    """⊢ est_decroissante(…) ⇒ est_monotone(…).

    « Une application décroissante est monotone » (S2 vers (dec ou cr), puis S3
    pour réordonner en (cr ou dec) = est_monotone)."""
    cr = est_croissante(G, Gp, f, E_set, Ep_set, x, y)
    dec = est_decroissante(G, Gp, f, E_set, Ep_set, x, y)
    # dec ⇒ (dec ou cr)  puis  (dec ou cr) ⇒ (cr ou dec)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
    return syllogisme(N.s2(dec, cr), N.s3(dec, cr))        # dec ⇒ (cr ou dec)


def monotone_decompose(thm_disj, croissante_alors, decroissante_alors,
                       G="G", Gp="Gp", f="f", E_set="E", Ep_set="Ep", x="x", y="y"):
    """Réexpose `cas` au vocabulaire monotone : de
        Γ ⊢ est_monotone(…),  Δ ⊢ est_croissante(…)⇒C,  Θ ⊢ est_decroissante(…)⇒C
    on conclut  Γ∪Δ∪Θ ⊢ C.   (Raisonnement par cas sur la disjonction monotone.)"""
    return cas(thm_disj, croissante_alors, decroissante_alors)


def strictement_monotone_decompose(thm_disj, croissante_alors, decroissante_alors):
    """Idem pour est_strictement_monotone : de Γ ⊢ str_monotone,
    Δ ⊢ str_croissante⇒C, Θ ⊢ str_decroissante⇒C, conclut C  (preuve par cas)."""
    return cas(thm_disj, croissante_alors, decroissante_alors)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME — strictement croissante ⇒ croissante
#  (sous est_ordre(G',E') et f application E→E' : (∀x)(x∈E ⇒ f(x)∈E')).
#  Si x≤y : ou bien x=y, et alors f(x)=f(y), et la réflexivité de G' donne
#  (f(x),f(y))∈G' ; ou bien x≠y, donc x<y, d'où f(x)<f(y) par stricte croissance,
#  et en particulier (f(x),f(y))∈G'.
# ════════════════════════════════════════════════════════════════════════════
def _f_dans_but(f, E_set, Ep_set, x="t"):
    """Hypothèse « f est une application E→E' » sous la forme suffisante pour les
    preuves : (∀t)(t∈E ⇒ f(t)∈E')  (f(t) au sens du graphe)."""
    vt, vE, vEp = var(x), _terme(E_set), _terme(Ep_set)
    return pourtout(x, impl(appartient(vt, vE), appartient(_val(f, vt), vEp)))


def strictement_croissante_implique_croissante(G="G", Gp="Gp", f="f",
                                               E_set="E", Ep_set="Ep",
                                               x="x", y="y", z="z", t="t"):
    """{ est_ordre(G',E'), (∀t)(t∈E⇒f(t)∈E'), est_strictement_croissante(…) }
        ⊢ est_croissante(…).

    « Toute application strictement croissante est croissante » (E.III.1.5) : sous
    réserve que G' soit un ordre sur E' (pour la réflexivité) et que f envoie E
    dans E'.  Cas x=y : f(x)=f(y) et réflexivité de G' ; cas x≠y : stricte
    croissance puis projection (f(x),f(y))∈G' de f(x)<f(y)."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    Hord = N.assume(est_ordre(Gp, Ep_set, x, y, z))        # ordre sur E'
    Hbut = N.assume(_f_dans_but(f, E_set, Ep_set, t))      # (∀t)(t∈E⇒f(t)∈E')
    Hstr = N.assume(est_strictement_croissante(G, Gp, f, E_set, Ep_set, x, y))
    refl_Ep = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # (∀u)(u∈E'⇒(u,u)∈G')

    # corps : (x∈E et y∈E et (x,y)∈G) ⇒ (f(x),f(y))∈G'
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    Hh = N.assume(hyp)
    x_in = conjonction_elim_gauche(conjonction_elim_gauche(Hh))        # x∈E
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hh))        # y∈E
    xy_in_G = conjonction_elim_droite(Hh)                              # (x,y)∈G
    cible = _couple_dans(_val(f, vx), _val(f, vy), Gp)                 # (f(x),f(y))∈G'

    # disjonction x=y ou ¬(x=y)
    disj = tiers_exclu(egal(vx, vy))

    # ── cas A : x=y ──────────────────────────────────────────────────────────
    Heq = N.assume(egal(vx, vy))                                       # x=y
    fx_in = N.modus_ponens(x_in, instancie(Hbut, vx))                  # f(x)∈E'
    fxfx = N.modus_ponens(fx_in, instancie(refl_Ep, _val(f, vx)))      # (f(x),f(x))∈G'
    # Leibniz : (x=y) ⇒ ((f(x),f(x))∈G' ⇔ (f(x),f(y))∈G'), trou « w » 2e coordonnée
    phi = _couple_dans(_val(f, vx), _val(f, var("w")), Gp)             # Φ(w) = (f(x),f(w))∈G'
    leib = N.s6(vx, vy, "w", phi)                                      # (x=y)⇒(Φ(x)⇔Φ(y))
    equivA = N.modus_ponens(Heq, leib)                                 # (f(x),f(x))∈G' ⇔ (f(x),f(y))∈G'
    casA_concl = N.modus_ponens(fxfx, equivalence_avant(equivA))       # (f(x),f(y))∈G'
    casA = N.loi_deduction(egal(vx, vy), casA_concl)                   # (x=y) ⇒ cible

    # ── cas B : ¬(x=y) ───────────────────────────────────────────────────────
    Hneq = N.assume(non(egal(vx, vy)))                                 # x≠y
    strict_xy = et(_couple_dans(vx, vy, G), non(egal(vx, vy)))         # x<y
    h_strict = conjonction_intro(xy_in_G, Hneq)                        # (x,y)∈G et x≠y
    h_str_full = conjonction_intro(conjonction_intro(x_in, y_in), h_strict)  # x∈E et y∈E et x<y
    Hstr_inst = instancie(instancie(Hstr, vx), vy)                     # (…et x<y) ⇒ f(x)<f(y)
    fxfy_strict = N.modus_ponens(h_str_full, Hstr_inst)                # f(x)<f(y) = (f(x),f(y))∈G' et f(x)≠f(y)
    casB_concl = conjonction_elim_gauche(fxfy_strict)                  # (f(x),f(y))∈G'
    casB = N.loi_deduction(non(egal(vx, vy)), casB_concl)              # ¬(x=y) ⇒ cible

    par_cas = cas(disj, casA, casB)                                    # (f(x),f(y))∈G'  (sous hyp)
    body = N.loi_deduction(hyp, par_cas)
    return N.generalisation(x, N.generalisation(y, body))


def strictement_decroissante_implique_decroissante(G="G", Gp="Gp", f="f",
                                                   E_set="E", Ep_set="Ep",
                                                   x="x", y="y", z="z", t="t"):
    """{ est_ordre(G',E'), (∀t)(t∈E⇒f(t)∈E'), est_strictement_decroissante(…) }
        ⊢ est_decroissante(…).

    Dual de strictement_croissante_implique_croissante : cas x=y par réflexivité
    de G', cas x≠y par la stricte décroissance (f(y)<f(x) ⇒ (f(y),f(x))∈G')."""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    Hord = N.assume(est_ordre(Gp, Ep_set, x, y, z))
    Hbut = N.assume(_f_dans_but(f, E_set, Ep_set, t))
    Hstr = N.assume(est_strictement_decroissante(G, Gp, f, E_set, Ep_set, x, y))
    refl_Ep = conjonction_elim_gauche(conjonction_elim_gauche(Hord))

    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _couple_dans(vx, vy, G))
    Hh = N.assume(hyp)
    x_in = conjonction_elim_gauche(conjonction_elim_gauche(Hh))
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hh))
    xy_in_G = conjonction_elim_droite(Hh)
    cible = _couple_dans(_val(f, vy), _val(f, vx), Gp)                 # (f(y),f(x))∈G'

    disj = tiers_exclu(egal(vx, vy))

    # cas A : x=y → f(y)=f(x), réflexivité (f(y),f(y))∈G' transportée en (f(y),f(x))∈G'
    Heq = N.assume(egal(vx, vy))
    fy_in = N.modus_ponens(y_in, instancie(Hbut, vy))                  # f(y)∈E'
    fyfy = N.modus_ponens(fy_in, instancie(refl_Ep, _val(f, vy)))      # (f(y),f(y))∈G'
    # trou sur la 2e coordonnée : Φ(w)=(f(y),f(w))∈G' ; (y=x)⇒(Φ(y)⇔Φ(x))
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    y_eq_x = N.modus_ponens(Heq, symetrie(vx, vy))                     # y=x
    phi = _couple_dans(_val(f, vy), _val(f, var("w")), Gp)
    leib = N.s6(vy, vx, "w", phi)                                      # (y=x)⇒(Φ(y)⇔Φ(x))
    equivA = N.modus_ponens(y_eq_x, leib)                              # (f(y),f(y))∈G' ⇔ (f(y),f(x))∈G'
    casA_concl = N.modus_ponens(fyfy, equivalence_avant(equivA))       # (f(y),f(x))∈G'
    casA = N.loi_deduction(egal(vx, vy), casA_concl)

    # cas B : ¬(x=y) → x<y → f(y)<f(x) → (f(y),f(x))∈G'
    Hneq = N.assume(non(egal(vx, vy)))
    h_strict = conjonction_intro(xy_in_G, Hneq)
    h_str_full = conjonction_intro(conjonction_intro(x_in, y_in), h_strict)
    Hstr_inst = instancie(instancie(Hstr, vx), vy)
    fyfx_strict = N.modus_ponens(h_str_full, Hstr_inst)                # f(y)<f(x)
    casB_concl = conjonction_elim_gauche(fyfx_strict)                  # (f(y),f(x))∈G'
    casB = N.loi_deduction(non(egal(vx, vy)), casB_concl)

    par_cas = cas(disj, casA, casB)
    body = N.loi_deduction(hyp, par_cas)
    return N.generalisation(x, N.generalisation(y, body))


__all__ = [
    # Définition 1 — croissante / décroissante / monotone
    "est_croissante", "est_decroissante", "est_monotone",
    # Définition 2 — strictement croissante / décroissante / monotone
    "est_strictement_croissante", "est_strictement_decroissante",
    "est_strictement_monotone",
    # Définition 8 — ensemble réticulé (treillis)
    "admet_borne_sup_inf", "est_reticule",
    # théorèmes directs
    "croissante_implique_monotone", "decroissante_implique_monotone",
    "monotone_decompose", "strictement_monotone_decompose",
    "strictement_croissante_implique_croissante",
    "strictement_decroissante_implique_decroissante",
]
