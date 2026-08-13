"""§III.1 & §III.7 — NOTIONS résiduelles : cofinal / coinitial, parties
filtrantes, ensemble ordonné filtrant, systèmes projectifs/inductifs relatifs à
un ensemble d'indices FILTRANT, images réciproque / directe d'un système.

AUDIT FINAL de complétude.  Ce module NEUF n'introduit QUE des notions qui
n'étaient PAS encore couvertes — il ne duplique RIEN.  Couvertes ailleurs (et
réutilisées ici, AUCUNE modification d'un fichier existant) :

  • `bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege` : est_cofinale, est_coinitiale,
    est_filtrant_droite, est_filtrant_gauche, est_relation_ordre_dans,
    est_relation_preordre, ordre_induit, est_plus_grand_element / petit ;
  • `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites` : est_systeme_projectif,
    est_systeme_inductif, appl_proj, appl_ind, lim_proj ;
  • `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_canoniques` : est_systeme_projectif_parties,
    est_systeme_inductif_parties, M_indice, u_indice, lim_proj_parties, etc.

NOTIONS INTRODUITES ICI (énoncés VERBATIM Bourbaki, §III.1.8/1.10 et §III.7) :

  (III.1) PARTIES COFINALES / COINITIALES & FILTRANTES
   • est_cofinale_dans / est_coinitiale_dans : A ⊂ E cofinale (resp. coinitiale)
     à un ensemble ORDONNÉ E (forme « partie cofinale dans un ensemble ordonné »,
     E.III.1.8) — wrappers explicitant l'inclusion A⊂E, alias fidèles des
     prédicats de base.
   • est_partie_filtrante_droite / _gauche : une PARTIE A d'un ensemble préordonné
     E est filtrante à droite (resp. à gauche) pour l'ordre INDUIT, i.e. toute
     paire d'éléments de A est majorée (resp. minorée) PAR UN ÉLÉMENT DE A
     (E.III.1.10 appliqué à la partie A munie de l'ordre induit).
   • est_filtrant : E préordonné est filtrant := filtrant à droite OU à gauche
     (« filtrant pour la relation ≤ », E.III.1.10).
   • est_ensemble_ordonne_filtrant_droite / _gauche : E est un ENSEMBLE ORDONNÉ
     filtrant à droite (resp. à gauche) := E ordonné par ≤ ET filtrant à droite
     (resp. à gauche)  (conjonction nommée, base de la Prop. 10 §III.1.10).
   • est_filtrant_inclusion : une famille (X_α) d'ensembles est « filtrante pour la
     relation ⊂ » := (∀α∀β)(∃γ)(X_α⊂X_γ et X_β⊂X_γ)  (Lemme 1, §III.5.1).

  (III.7) SYSTÈMES RELATIFS À UN ENSEMBLE D'INDICES FILTRANT
   • est_systeme_projectif_filtrant : (E_α,f_{αβ}) système projectif relatif à un
     I FILTRANT à droite (hypothèse explicitée des Prop. 5 / Th. 1, §III.7.4).
   • est_systeme_inductif_filtrant : redondant avec est_systeme_inductif (qui exige
     déjà I filtrant à droite) — fourni comme ALIAS NOMMÉ explicite (E.III.7.5).

  (III.7.2) IMAGE RÉCIPROQUE / DIRECTE D'UN SYSTÈME (les NOTIONS, Prop. 2)
   • image_reciproque_indice : (u_α)^{-1}(x'_α) := u_α^{-1}⟨{x'_α}⟩, la fibre de
     u_α au-dessus de x'_α (codée image(reciproque(u_α), {x'_α})).
   • systeme_image_reciproque : la donnée des fibres ((u_α)^{-1}(x'_α))_α — système
     de PARTIES des E_α associé à un système projectif d'applications (u_α) et à un
     point x'=(x'_α)  (Prop. 2, §III.7.2 : « les (u_α)^{-1}(x'_α) forment un système
     projectif de parties »).
   • est_systeme_image_reciproque : prédicat « (M_α) EST le système image réciproque
     de x' par (u_α) » (∀α : M_α = (u_α)^{-1}(x'_α)).
   • image_directe_indice / systeme_image_directe / est_systeme_image_directe :
     duals — u_α⟨M_α⟩ et la donnée (u_α⟨M_α⟩)_α (système inductif de parties image
     directe d'un système inductif de parties par un système inductif d'appl.).

THÉORÈMES DURS (existence/unicité, « forment un système », bijections canoniques :
Prop. 2, Th. 1, Prop. 10 §III.1.10, Lemme 1 §III.5.1, Prop. 3/5/8 cofinales) :
REPORTÉS honnêtement (champ REPORTES).  On INTRODUIT les NOTIONS ; rien n'est
postulé comme théorème.  AXIOMES de membership : AUCUN ajouté ici (toutes les
notions sont des prédicats/termes construits sur l'existant) — theorie_ensembles()
reste à 22.  LEMMES DIRECTS en bonus (décompositions / instanciations, certifiés
par le noyau).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, ou, impl, non, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_canoniques import (
    M_indice,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (III.1.8) PARTIES COFINALES / COINITIALES dans un ensemble ORDONNÉ
#  Wrappers fidèles : explicitent A⊂E (« partie » de E) + la condition de base.
# ════════════════════════════════════════════════════════════════════════════
def est_cofinale_dans(R, A, e, x="x", y="y"):
    """« A est une partie cofinale dans l'ensemble ordonné E » (E.III.1.8) :=
        A ⊂ E  ET  (∀x)(x∈E ⇒ (∃y)(y∈A et x≤y)).

    DÉFINITION VERBATIM E.III.1.8 : « une partie A d'un ensemble préordonné E est
    cofinale à E si, pour tout x∈E, il existe y∈A tel que x≤y. »  Forme explicitant
    que A est une PARTIE (A⊂E) ; le cœur réutilise est_cofinale (AUCUNE redéf.)."""
    return et(inclus(_t(A), _t(e)), E.est_cofinale(R, _t(A), _t(e), x, y))


def est_coinitiale_dans(R, A, e, x="x", y="y"):
    """« A est une partie coinitiale dans l'ensemble ordonné E » (E.III.1.8) :=
        A ⊂ E  ET  (∀x)(x∈E ⇒ (∃y)(y∈A et y≤x)).

    Dual de est_cofinale_dans (E.III.1.8 : « ...il existe y∈A tel que y≤x »)."""
    return et(inclus(_t(A), _t(e)), E.est_coinitiale(R, _t(A), _t(e), x, y))


# ════════════════════════════════════════════════════════════════════════════
#  (III.1.10) PARTIE FILTRANTE à droite / à gauche
#  Une PARTIE A de E préordonné, filtrante pour l'ordre induit : la majoration
#  (resp. minoration) de toute paire d'éléments de A se fait PAR UN ÉLÉMENT DE A.
# ════════════════════════════════════════════════════════════════════════════
def est_partie_filtrante_droite(R, A, e, x="x", y="y", z="z"):
    """« A (partie de E préordonné) est filtrante à droite » (E.III.1.10 appliqué à
    la partie A munie de l'ordre induit) :=
        A ⊂ E  ET  (∀x)(∀y)((x∈A et y∈A) ⇒ (∃z)(z∈A et x≤z et y≤z)).

    « toute partie à deux éléments de A est majorée DANS A » (Déf. 7, E.III.1.10,
    lue pour la partie A et l'ordre induit : le majorant z est exigé DANS A)."""
    vA, vx, vy, vz = _t(A), var(x), var(y), var(z)
    return et(inclus(vA, _t(e)),
              pourtout(x, pourtout(y, impl(et(appartient(vx, vA), appartient(vy, vA)),
                  existe(z, et(et(appartient(vz, vA), R(vx, vz)), R(vy, vz)))))))


def est_partie_filtrante_gauche(R, A, e, x="x", y="y", z="z"):
    """« A (partie de E préordonné) est filtrante à gauche » (E.III.1.10) :=
        A ⊂ E  ET  (∀x)(∀y)((x∈A et y∈A) ⇒ (∃z)(z∈A et z≤x et z≤y)).

    Dual : « toute partie à deux éléments de A est minorée DANS A » (Déf. 7)."""
    vA, vx, vy, vz = _t(A), var(x), var(y), var(z)
    return et(inclus(vA, _t(e)),
              pourtout(x, pourtout(y, impl(et(appartient(vx, vA), appartient(vy, vA)),
                  existe(z, et(et(appartient(vz, vA), R(vz, vx)), R(vz, vy)))))))


# ════════════════════════════════════════════════════════════════════════════
#  (III.1.10) ENSEMBLE PRÉORDONNÉ / ORDONNÉ FILTRANT
# ════════════════════════════════════════════════════════════════════════════
def est_filtrant(R, e, x="x", y="y", z="z"):
    """« E préordonné est filtrant » := filtrant à droite OU filtrant à gauche
    (E.III.1.10 : « filtrant pour la relation ≤ »).

    Bourbaki dit « filtrant croissant » (à droite) / « décroissant » (à gauche) ;
    le terme nu « filtrant » recouvre l'un ou l'autre."""
    return ou(E.est_filtrant_droite(R, _t(e), x, y, z),
              E.est_filtrant_gauche(R, _t(e), x, y, z))


def est_ensemble_ordonne_filtrant_droite(R, e, x="x", y="y", z="z"):
    """« E est un ensemble ORDONNÉ filtrant à droite » (E.III.1.10) :=
        E est ordonné par ≤  ET  E est filtrant à droite.

    Conjonction nommée (hypothèse de la Proposition 10, §III.1.10 : « dans un
    ensemble ordonné filtrant à droite, un élément maximal est le plus grand »)."""
    return et(E.est_relation_ordre_dans(R, _t(e), x, y, z),
              E.est_filtrant_droite(R, _t(e), x, y, z))


def est_ensemble_ordonne_filtrant_gauche(R, e, x="x", y="y", z="z"):
    """« E est un ensemble ORDONNÉ filtrant à gauche » (E.III.1.10) :=
        E ordonné par ≤  ET  E filtrant à gauche.  (Dual.)"""
    return et(E.est_relation_ordre_dans(R, _t(e), x, y, z),
              E.est_filtrant_gauche(R, _t(e), x, y, z))


# ── (III.5.1, Lemme 1) Famille FILTRANTE pour l'inclusion ⊂ ───────────────────
def est_filtrant_inclusion(Xfam, A, a="a", b="b", g="g"):
    """« la famille (X_α)_{α∈A} est filtrante pour la relation ⊂ » (Lemme 1, §III.5.1)
        := (∀α)(∀β)((α∈A et β∈A) ⇒ (∃γ)(γ∈A et X_α⊂X_γ et X_β⊂X_γ)).

    DÉFINITION VERBATIM (Lemme 1) : « pour tout couple d'indices (α,β) il existe un
    indice γ tel que X_α⊂X_γ et X_β⊂X_γ ».  Xfam = famille α↦X_α (X_α = valeur de la
    famille en α) ; A = ensemble d'indices."""
    va, vb, vg = var(a), var(b), var(g)
    Xa = E.valeur_famille(_t(Xfam), va)
    Xb = E.valeur_famille(_t(Xfam), vb)
    Xg = E.valeur_famille(_t(Xfam), vg)
    return pourtout(a, pourtout(b, impl(et(appartient(va, _t(A)), appartient(vb, _t(A))),
        existe(g, et(et(appartient(vg, _t(A)), inclus(Xa, Xg)), inclus(Xb, Xg))))))


# ════════════════════════════════════════════════════════════════════════════
#  (III.7) SYSTÈMES relatifs à un ensemble d'indices FILTRANT
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.4 Prop.5 | E III.58 L.1-3 | PDF p.161
#   (HYPOTHÈSE seule de la Prop. 5 : « (E_α,f_αβ) système projectif relatif à un
#    ensemble préordonné filtrant I, qui admet une partie cofinale dénombrable, les
#    f_αβ surjectives » — la conclusion (f_α surjective, L.3-4) et la démonstration
#    (L.5-14) restent REPORTÉES, cf. REPORTES)
def est_systeme_projectif_filtrant(Efam, f, leq, i, a="a", b="b", g="g",
                                   x="x", y="y", z="z", zt="zt"):
    """« (E_α,f_{αβ}) est un système projectif relatif à un I FILTRANT à droite »
        := I est filtrant à droite (pour ≤)  ET  (E_α,f_{αβ}) est un système
           projectif d'ensembles relatif à I.

    Hypothèse explicitée des Prop. 5 et Théorème 1, §III.7.4 (« I filtrant »).  On
    réutilise est_systeme_projectif (LP_I/LP_II) sans le redéfinir.  Les liants x,y,z
    distincts servent au préordre filtrant (x,y,z) et au cocycle (a,b,g)."""
    return et(E.est_filtrant_droite(leq, _t(i), x, y, z),
              L.est_systeme_projectif(_t(Efam), _t(f), leq, _t(i), a, b, g, x, zt))


def est_systeme_inductif_filtrant(f, leq, i, a="a", b="b", g="g", x="x"):
    """« (E_α,f_{βα}) est un système inductif relatif à I filtrant à droite »
        := est_systeme_inductif(f, ≤, I)  (qui exige DÉJÀ I filtrant à droite,
           E.III.7.5).

    ALIAS NOMMÉ explicite : la définition Bourbaki d'un système inductif impose
    déjà « I préordonné filtrant à droite » ; ce prédicat rend cette hypothèse
    visible dans les énoncés (Prop. 6/8/9, §III.7.6-7) sans rien redéfinir."""
    return L.est_systeme_inductif(_t(f), leq, _t(i), a, b, g, x)


# ════════════════════════════════════════════════════════════════════════════
#  (III.7.2, Prop. 2) IMAGE RÉCIPROQUE d'un système — la NOTION
#  Les (u_α)^{-1}(x'_α) forment un système projectif de PARTIES des E_α.
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_indice(u, a, xp):
    """(u_α)^{-1}(x'_α) := u_α^{-1}⟨{x'_α}⟩  (fibre de u_α au-dessus de x'_α).

    u_α := u_indice(u,α) = app("u_indice",u,α) (composante du système d'appl.),
    x'_α := pr_α(x') = projection_indice(x',α).  L'image réciproque d'un singleton
    {x'_α} par u_α : codée image(reciproque(u_α), {x'_α})  (G⁻¹⟨X⟩, E.II.41/39)."""
    ua = app("u_indice", _t(u), _t(a))
    xpa = E.projection_indice(_t(xp), _t(a))
    return E.image(E.reciproque(ua), E.singleton(xpa))


# @livre Ch.III §7.2 Prop.2 | E III.54 L.28-31 | PDF p.157
def systeme_image_reciproque(u, xp):
    """((u_α)^{-1}(x'_α))_α : la donnée du système de PARTIES image réciproque de
    x'=(x'_α) par le système projectif d'applications (u_α)  (Prop. 2, §III.7.2).

    Terme opaque représentant la FAMILLE α ↦ (u_α)^{-1}(x'_α) (donnée « M » au sens
    de est_systeme_projectif_parties / M_indice de ensembles_limites_canoniques).
    Bourbaki : « les (u_α)^{-1}(x'_α) forment un système projectif de parties des
    E_α ».  La caractérisation de ses composantes est est_systeme_image_reciproque."""
    return app("sys_img_recip", _t(u), _t(xp))


def est_systeme_image_reciproque(M, u, xp, a="a"):
    """« (M_α) EST le système image réciproque de x' par (u_α) » :=
        (∀α)( M_α = (u_α)^{-1}(x'_α) ).

    Caractérise la donnée M (M_α := M_indice(M,α), la VALEUR de la famille) comme la
    famille des fibres.  C'est cette famille qui, par la Prop. 2 (REPORTÉE), est un
    système projectif de parties et dont la limite est u^{-1}(x').  (§III.7.2.)"""
    va = var(a)
    Ma = M_indice(_t(M), va)
    return pourtout(a, egal(Ma, image_reciproque_indice(u, va, xp)))


# ════════════════════════════════════════════════════════════════════════════
#  (III.7.6, dual) IMAGE DIRECTE d'un système — la NOTION
#  u_α⟨M_α⟩ : système inductif de parties image directe par (u_α).
# ════════════════════════════════════════════════════════════════════════════
def image_directe_indice(u, a, M):
    """u_α⟨M_α⟩ := image directe de M_α par u_α  (G⟨X⟩, E.II.39).

    u_α := u_indice(u,α) ; M_α := M_indice(M,α).  Composante du système image
    directe d'un système (inductif) de parties (M_α) par un système d'appl. (u_α)."""
    ua = app("u_indice", _t(u), _t(a))
    Ma = M_indice(_t(M), _t(a))
    return E.image(ua, Ma)


# @livre Ch.III §7.6 Cor.- | E III.64 L.22-26 | PDF p.167
# @livre Ch.III §7.6 Cor.- | E III.65 L.1-8 | PDF p.168
#   (suite de l'énoncé du corollaire de la Prop. 7 : (i) (u_α(M_α)) système inductif
#    de parties et (26) lim→ u_α(M_α) = u(lim→ M_α) ; (ii) les fibres u_α^{-1}(a'_α)
#    système inductif de parties et (27) lim→ u_α^{-1}(a'_α) = u^{-1}(a') — identités
#    (26)/(27) REPORTÉES ; seule la NOTION image directe/réciproque est posée ici)
def systeme_image_directe(u, M):
    """(u_α⟨M_α⟩)_α : la donnée du système de PARTIES image directe du système de
    parties (M_α) par le système d'applications (u_α).

    Terme opaque représentant la famille α ↦ u_α⟨M_α⟩.  Caractérisation de ses
    composantes : est_systeme_image_directe.  (§III.7.6, dual de la Prop. 2.)"""
    return app("sys_img_directe", _t(u), _t(M))


def est_systeme_image_directe(Mp, u, M, a="a"):
    """« (M'_α) EST le système image directe de (M_α) par (u_α) » :=
        (∀α)( M'_α = u_α⟨M_α⟩ ).

    M'_α := M_indice(Mp,α) ; caractérise M' comme la famille des images directes.
    (§III.7.6 ; dual de est_systeme_image_reciproque.)"""
    va = var(a)
    Mpa = M_indice(_t(Mp), va)
    return pourtout(a, egal(Mpa, image_directe_indice(u, va, M)))


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS (bonus) — décompositions / instanciations, certifiés noyau.
#  Aucun théorème dur n'est prouvé ; uniquement de la logique pure sur les défs.
# ════════════════════════════════════════════════════════════════════════════
def _R_defaut():
    return lambda u, v: appartient(E.couple(u, v), var("G"))


def cofinale_dans_inclusion(R=None, A="A", e="E", x="x", y="y"):
    """{ A cofinale DANS E } ⊢ A ⊂ E.   (projection gauche de est_cofinale_dans.)"""
    if R is None:
        R = _R_defaut()
    H = N.assume(est_cofinale_dans(R, A, e, x, y))
    return conjonction_elim_gauche(H)


def cofinale_dans_condition(R=None, A="A", e="E", x="x", y="y"):
    """{ A cofinale DANS E } ⊢ (∀x)(x∈E ⇒ (∃y)(y∈A et x≤y)).
    (projection droite de est_cofinale_dans : la condition de cofinalité.)"""
    if R is None:
        R = _R_defaut()
    H = N.assume(est_cofinale_dans(R, A, e, x, y))
    return conjonction_elim_droite(H)


def partie_filtrante_droite_inclusion(R=None, A="A", e="E", x="x", y="y", z="z"):
    """{ A partie filtrante à droite de E } ⊢ A ⊂ E.
    (une partie filtrante de E est, en particulier, une partie de E.)"""
    if R is None:
        R = _R_defaut()
    H = N.assume(est_partie_filtrante_droite(R, A, e, x, y, z))
    return conjonction_elim_gauche(H)


def ensemble_ordonne_filtrant_droite_est_ordre(R=None, e="E", x="x", y="y", z="z"):
    """{ E ordonné filtrant à droite } ⊢ est_relation_ordre_dans(R,E).
    (un ensemble ordonné filtrant est, en particulier, ordonné.)"""
    if R is None:
        R = _R_defaut()
    H = N.assume(est_ensemble_ordonne_filtrant_droite(R, e, x, y, z))
    return conjonction_elim_gauche(H)


def ensemble_ordonne_filtrant_droite_est_filtrant(R=None, e="E", x="x", y="y", z="z"):
    """{ E ordonné filtrant à droite } ⊢ est_filtrant_droite(R,E).
    (projection droite : la propriété de filtration à droite.)"""
    if R is None:
        R = _R_defaut()
    H = N.assume(est_ensemble_ordonne_filtrant_droite(R, e, x, y, z))
    return conjonction_elim_droite(H)


def systeme_projectif_filtrant_est_systeme(f="f", leq=None, i="I",
                                           a="a", b="b", g="g", x="x", y="y",
                                           z="z", Efam="E", zt="zt"):
    """{ (E_α,f_{αβ}) sys. projectif relatif à I filtrant } ⊢ est_systeme_projectif(f,≤,I).
    (projection droite : oublier l'hypothèse « I filtrant » redonne un système projectif.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    H = N.assume(est_systeme_projectif_filtrant(
        _t(Efam), _t(f), leq, _t(i), a, b, g, x, y, z, zt))
    return conjonction_elim_droite(H)


def systeme_projectif_filtrant_indices_filtrants(f="f", leq=None, i="I",
                                                 a="a", b="b", g="g", x="x",
                                                 y="y", z="z", Efam="E",
                                                 zt="zt"):
    """{ (E_α,f_{αβ}) sys. projectif relatif à I filtrant } ⊢ est_filtrant_droite(≤,I).
    (projection gauche : l'ensemble d'indices I est filtrant à droite.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    H = N.assume(est_systeme_projectif_filtrant(
        _t(Efam), _t(f), leq, _t(i), a, b, g, x, y, z, zt))
    return conjonction_elim_gauche(H)


def image_reciproque_indice_composante(u="u", a="a", xp="xp"):
    """{ (M_α) = sys. image réciproque de x' par (u_α) } ⊢ M_α = (u_α)^{-1}(x'_α).

    Instanciation de est_systeme_image_reciproque en l'indice α : la α-composante
    du système image réciproque est bien la fibre (u_α)^{-1}(x'_α).  (Prop. 2.)"""
    vu, va, vxp = _t(u), var(a), _t(xp)
    M = systeme_image_reciproque(vu, vxp)
    H = N.assume(est_systeme_image_reciproque(M, vu, vxp, a))
    return instancie(H, va)                          # M_α = (u_α)^{-1}(x'_α)


def image_directe_indice_composante(u="u", a="a", M="M"):
    """{ (M'_α) = sys. image directe de (M_α) par (u_α) } ⊢ M'_α = u_α⟨M_α⟩.
    (instanciation de est_systeme_image_directe ; dual.)"""
    vu, va, vM = _t(u), var(a), _t(M)
    Mp = systeme_image_directe(vu, vM)
    H = N.assume(est_systeme_image_directe(Mp, vu, vM, a))
    return instancie(H, va)                          # M'_α = u_α⟨M_α⟩


# Résultats DURS introduits (notions définies) mais NON prouvés — honnêteté.
REPORTES = [
    "Proposition 10 (§III.1.10) : élément maximal d'un filtrant à droite = plus grand "
    "— ✅ FAIT dans `iii_1_relations_ordre/iii_1_8_filtrants/"
    "ensembles_prop10_maximal_filtrant.maximal_filtrant_est_plus_grand` (3 hyps "
    "honnêtes) ; ce report était PÉRIMÉ (corrigé le 4 août 2026, vérifié en code).",
    "Lemme 1 (§III.5.1) : famille filtrante pour ⊂ ⇒ existence et unicité d'un "
    "ordre induisant chaque ordre donné — REPORTÉ.",
    "Proposition 2 (§III.7.2) : les (u_α)^{-1}(x'_α) FORMENT un système projectif "
    "de parties et u^{-1}(x') = lim← (u_α)^{-1}(x'_α) — REPORTÉ (limite effective).",
    "Propositions 3/5/8 (§III.7) : parties cofinales ⇒ applications canoniques "
    "bijectives / surjectives — REPORTÉ.",
    "« (M_α) image directe forme un système inductif de parties » (§III.7.6) — REPORTÉ.",
]


__all__ = [
    # III.1 — cofinal / coinitial dans un ensemble ordonné
    "est_cofinale_dans", "est_coinitiale_dans",
    # III.1 — parties filtrantes / ensemble ordonné filtrant
    "est_partie_filtrante_droite", "est_partie_filtrante_gauche",
    "est_filtrant",
    "est_ensemble_ordonne_filtrant_droite", "est_ensemble_ordonne_filtrant_gauche",
    "est_filtrant_inclusion",
    # III.7 — systèmes relatifs à un ensemble d'indices filtrant
    "est_systeme_projectif_filtrant", "est_systeme_inductif_filtrant",
    # III.7.2 — image réciproque d'un système
    "image_reciproque_indice", "systeme_image_reciproque", "est_systeme_image_reciproque",
    # III.7.6 — image directe d'un système
    "image_directe_indice", "systeme_image_directe", "est_systeme_image_directe",
    # lemmes directs
    "cofinale_dans_inclusion", "cofinale_dans_condition",
    "partie_filtrante_droite_inclusion",
    "ensemble_ordonne_filtrant_droite_est_ordre",
    "ensemble_ordonne_filtrant_droite_est_filtrant",
    "systeme_projectif_filtrant_est_systeme",
    "systeme_projectif_filtrant_indices_filtrants",
    "image_reciproque_indice_composante", "image_directe_indice_composante",
    "REPORTES",
]
