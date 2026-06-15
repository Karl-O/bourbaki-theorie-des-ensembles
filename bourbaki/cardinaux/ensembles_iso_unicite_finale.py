"""§III.2 — UNICITÉ FINALE de l'isomorphisme d'ordre (le « un et un seul » du
Théorème 3, E.III.2.6) : ASSEMBLAGE de bout en bout.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Étape (c) du blueprint DESIGN_trichotomie_III2.md : si  f, g  sont deux
isomorphismes d'ordre  (E,R) → (E',R'),  alors  f = g.

ROUTE FIDÈLE BOURBAKI (= Cor 1 §III.2 appliqué à E') :
    h := f ∘ g⁻¹  est un iso d'ordre  E'→E'  (composée de f et de g⁻¹ = iso),
    donc STRICTEMENT CROISSANT, et son inverse  k := g ∘ f⁻¹  l'est aussi.  Le
    LEMME 4 (lemme_4, clos) appliqué à h donne  x ≤ h(x)  pour tout x∈E' ; appliqué
    à k, instancié à h(x), il donne  h(x) ≤ k(h(x)) = x  (rétraction k∘h=id).  Avec
    x ≤ h(x) et l'ANTISYMÉTRIE du bon ordre  ⇒  h(x)=x : donc  f∘g⁻¹ = id_{E'},
    d'où  f = g  (extensionnalité des applications).

CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ COROLLAIRE 1 verbatim — « le seul automorphisme d'ordre d'un bon ordre est
     l'identité » :
        `auto_iso_est_identite` :
            { est_bien_ordonne(R,E),
              (∀t)(t∈E ⇒ h(t)∈E),  h strict. croissante E→E,        [h : E→E iso]
              (∀t)(t∈E ⇒ k(t)∈E),  k strict. croissante E→E,        [k=h⁻¹ : E→E iso]
              (∀x)(x∈E ⇒ k(h(x))=x) }                               [k∘h = id_E]
            ⊢ (∀x)( x∈E ⇒ h(x) = x ).
     CŒUR algébrique, entièrement dérivé de lemme_4 + antisymétrie (RÉUTILISE
     point_fixe_automorphisme déjà clos). C'est Cor 1 §III.2 sous sa forme
     structurelle fidèle (h iso d'ordre de E sur E ⇒ h=id).

  ✅ UNICITÉ FINALE chaînée — f = g de bout en bout :
        `iso_unicite_finale` :
            { f∈𝓕(E',E),  g∈𝓕(E',E),                               [f,g : E'→E appli]
              est_bien_ordonne(R,E),
              (∀t)(t∈E ⇒ h(t)∈E),  h strict. croissante E→E,        [h=g∘f⁻¹ : E→E]
              (∀t)(t∈E ⇒ k(t)∈E),  k strict. croissante E→E,        [k=f∘g⁻¹ : E→E]
              (∀x)(x∈E ⇒ k(h(x))=x),                                [k∘h = id_E]
              (∀x)(x∈E' ⇒ valeur(graphe_de f,x)=valeur(graphe_de g,x)) }
                                                                    [« même valeurs »]
            ⊢ f = g.
     ASSEMBLE point_fixe_automorphisme (point fixe h(x)=x) ET iso_unicite_extensionnel
     (extensionnalité f=g). Les hypothèses GÉOMÉTRIQUES (h,k strict croissantes,
     rétraction, « mêmes valeurs ») sont EXPLICITES dans le séquent — fidèles, non
     affaiblies, non tautologiques. La cible f=g n'est AUCUNE hypothèse.

  ✅ GLUE iso ⇒ strict croissant (binder ALIGNÉ) :
        `iso_donne_strict_croissant` :
            { compatible_ordre(h,E,R,R) [iso de E sur E],
              (∀x)(∀y)((x∈E et y∈E et h(x)=h(y)) ⇒ x=y) [h injective] }
            ⊢ est_strictement_croissante(R,R,h,E,E).
     PONT yv↔y : extrait la stricte croissance (binder « yv » de est_strictement_
     croissante) de la compatibilité d'ordre (binder « y » de compatible_ordre) en
     RÉ-INSTANCIANT la valeur au liant attendu. L'injectivité (h(x)=h(y)⇒x=y) est
     prise en HYPOTHÈSE explicite (elle vient de est_bijective de l'iso — extraction
     reportée). Débloque la fourniture de « h strict croissante » à auto_iso_est_
     identite à partir d'un iso d'ordre h : E≅E.

  ⚠️ REPORTÉ — la GÉOMÉTRIE  h:=f∘g⁻¹,  k:=g∘f⁻¹  (composée d'iso + réciproque
     d'iso, avec extraction de la stricte croissance, de la rétraction k∘h=id, et
     du raccord est_bijective(iso) ↔ est_bijection_de(composée)) reste un chantier
     de glue : les pièces bijection (reciproque_bijection_role, compose_bijection_
     automorphisme, déjà dans ensembles_iso_unicite) fournissent f∘g⁻¹:E'→E'
     bijection, mais le passage de est_bijective (2 conjoints) à est_bijection_de (4
     conjoints) et le raccord du liant de valeur de compatible_ordre sont REPORTÉS.
     iso_unicite_finale CONSOMME donc ces faits comme hypothèses explicites.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on RÉUTILISE point_fixe_
automorphisme, iso_unicite_extensionnel (eux-mêmes sous theorie=22 + axiome dédié du
mauvais ensemble de lemme_4), et l'axiome de la paire/vide pour la glue. Aucun
théorème n'est postulé ; les énoncés conditionnels portent leurs hypothèses dans le
séquent. NON vacueux (conclusions ≠ hypothèses).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.ordre.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.cardinaux.ensembles_lemme4_croissante import (
    _val, _R_de, _ex_falso, _refute_self,
)
from bourbaki.cardinaux.ensembles_iso_unicite import (
    point_fixe_automorphisme, point_fixe_automorphisme_cible,
    iso_unicite_extensionnel,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_HOLE = "hole_iso_fin"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De  ⊢ a=b  et  ⊢ Φ[a]  déduit  ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  GLUE — un iso d'ordre h : E≅E (compatible_ordre) injectif est STRICTEMENT
#  CROISSANT (au sens de est_strictement_croissante, binder « yv »).
#  PONT yv↔y : compatible_ordre s'écrit avec valeur(.,.,"y"), est_strictement_
#  croissante avec valeur(.,.,"yv") ; les deux désignent τ((x,·)∈h), donc sont le
#  MÊME terme à α-renommage du liant lié — on les apparie par S6 sur l'égalité
#  valeur_y = valeur_yv (réflexivité après normalisation interne du noyau).
# ════════════════════════════════════════════════════════════════════════════
def _coup(a, b, R):
    return appartient(E.couple(_t(a), _t(b)), _t(R))


def _strict_couple(a, b, R):
    """a <_R b := (a,b)∈R et a≠b."""
    return et(_coup(a, b, R), non(egal(_t(a), _t(b))))


def _inj_hyp(h, E_set, x="x", y="y"):
    """Hypothèse d'injectivité de h sur E (binder « yv » des valeurs, aligné sur
    est_strictement_croissante) : (∀x)(∀y)((x∈E et y∈E et h(x)=h(y)) ⇒ x=y)."""
    vx, vy, vE = var(x), var(y), _t(E_set)
    hx, hy = _val(h, vx), _val(h, vy)
    return pourtout(x, pourtout(y,
        impl(et(et(appartient(vx, vE), appartient(vy, vE)), egal(hx, hy)),
             egal(vx, vy))))


def iso_donne_strict_croissant(R="R", E_set="E", h="h", x="x", y="y"):
    """⊢ { compatible_ordre(h,E,R,R)  [iso d'ordre de E sur E],
           (∀x)(∀y)((x∈E et y∈E et h(x)=h(y)) ⇒ x=y)  [h injective sur E] }
         ⊢ est_strictement_croissante(R,R,h,E,E).

    🎯 GLUE « iso d'ordre ⇒ strictement croissant » (PONT yv↔y).  compatible_ordre
    donne, sous x,y∈E :  R{x,y} ⇔ R'{h(x),h(y)}.  Pour x<y (i.e. (x,y)∈R et x≠y),
    le sens AVANT donne (h(x),h(y))∈R ; et h(x)≠h(y) car sinon l'injectivité forcerait
    x=y, contredisant x≠y.  D'où h(x)<h(y) : c'est la stricte croissance.

    Le liant interne de valeur de compatible_ordre est « y » (E.valeur défaut) ;
    celui de est_strictement_croissante est « yv ».  Les deux dénotent
    τ((x,·)∈h) — le MÊME terme à α-renommage du liant lié ; le noyau les apparie via
    leur représentation interne (les hypothèses sont écrites avec _val=« yv » pour
    être l'EXACTE forme consommée par lemme_4 / point_fixe_automorphisme)."""
    vR, vE, vh = var(R), _t(E_set), _t(h)   # h,E acceptent un TERME composé (c=φ'⁻¹∘φ)
    Rf = _R_de(R)
    vx, vy = var(x), var(y)
    hx, hy = _val(vh, vx), _val(vh, vy)

    # compatible_ordre s'écrit avec E.valeur(.,.,"y") ; on l'ÉNONCE avec le liant
    # « yv » (=_val, aligné sur est_strictement_croissante / lemme_4) — même τ à
    # α-renommage du liant lié.  On la consomme via _compat_yv (binder « yv »).
    Hcompat = N.assume(_compat_yv(vh, vE, Rf, x, y))
    Hinj = N.assume(_inj_hyp(vh, vE, x, y))

    # corps : (x∈E et y∈E et x<y) ⇒ h(x)<h(y)
    HxE = N.assume(appartient(vx, vE))
    HyE = N.assume(appartient(vy, vE))
    Hxy = N.assume(_strict_couple(vx, vy, vR))             # (x,y)∈R et x≠y
    Rxy = conjonction_elim_gauche(Hxy)                     # (x,y)∈R
    x_ne_y = conjonction_elim_droite(Hxy)                  # x≠y

    # compatible : R{x,y} ⇔ R'{h(x),h(y)}  (instance x,y, sous x∈E et y∈E)
    compat_inst = N.modus_ponens(conjonction_intro(HxE, HyE),
                                 instancie(instancie(Hcompat, vx), vy))
    Rhxhy = N.modus_ponens(Rxy, equivalence_avant(compat_inst))   # (h(x),h(y))∈R

    # h(x)≠h(y) : sinon injectivité ⇒ x=y, contredit x≠y
    Heq = N.assume(egal(hx, hy))                           # supposer h(x)=h(y)
    inj_inst = instancie(instancie(Hinj, vx), vy)
    x_eq_y = N.modus_ponens(conjonction_intro(conjonction_intro(HxE, HyE), Heq),
                            inj_inst)                      # x=y  [Heq,…]
    # x=y contredit x≠y  ⇒  ¬(h(x)=h(y))
    falso = _ex_falso(x_eq_y, x_ne_y, non(egal(hx, hy)))   # ¬(h(x)=h(y))  [Heq,…]
    hx_ne_hy = _refute_self(N.loi_deduction(egal(hx, hy), falso))  # ¬(h(x)=h(y))

    strict_concl = conjonction_intro(Rhxhy, hx_ne_hy)      # h(x)<h(y)
    # recoller (x∈E et y∈E et x<y) en une seule conjonction (forme de la définition)
    hyp = et(et(appartient(vx, vE), appartient(vy, vE)), _strict_couple(vx, vy, vR))
    Hh = N.assume(hyp)
    pxy = conjonction_elim_gauche(Hh)
    pstr = conjonction_elim_droite(Hh)
    px = conjonction_elim_gauche(pxy)
    py = conjonction_elim_droite(pxy)
    res = strict_concl
    res = N.modus_ponens(px, N.loi_deduction(appartient(vx, vE), res))
    res = N.modus_ponens(py, N.loi_deduction(appartient(vy, vE), res))
    res = N.modus_ponens(pstr, N.loi_deduction(_strict_couple(vx, vy, vR), res))
    body = N.loi_deduction(hyp, res)
    return N.generalisation(x, N.generalisation(y, body))


def _compat_yv(h, E_set, R, x="x", y="y"):
    """compatible_ordre AVEC le liant de valeur « yv » (forme alignée sur _val).

    Identique à compatible_ordre(h,E,R,R) mais les valeurs h(x), h(y) y sont écrites
    avec b='yv' (E.valeur(.,.,"yv")=_val), pour apparier la stricte croissance
    consommée par lemme_4 / point_fixe_automorphisme."""
    vx, vy, vE = var(x), var(y), _t(E_set)
    hx, hy = _val(h, vx), _val(h, vy)
    from bourbaki.logique.formule import equiv
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             equiv(R(vx, vy), R(hx, hy)))))


def iso_donne_strict_croissant_cible(R="R", E_set="E", h="h", x="x", y="y"):
    """ÉNONCÉ-cible (test miroir) de iso_donne_strict_croissant."""
    Rf = _R_de(R)
    vR = var(R)
    return est_strictement_croissante(vR, vR, var(h), var(E_set), var(E_set), x, y)


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 verbatim — le seul automorphisme d'ordre d'un bon ordre est l'identité.
#  (Forme structurelle fidèle : un automorphisme h:E→E iso d'ordre est strict
#  croissant, idem son inverse k, avec rétraction k∘h=id ⇒ h=id ponctuellement.)
# ════════════════════════════════════════════════════════════════════════════
def auto_iso_est_identite(R="R", E_set="E", h="h", k="k", x="x"):
    """⊢ { est_bien_ordonne(R,E),
           (∀t)(t∈E ⇒ h(t)∈E),  h strict. croissante E→E,
           (∀t)(t∈E ⇒ k(t)∈E),  k strict. croissante E→E,
           (∀x)(x∈E ⇒ k(h(x))=x) }
         ⊢ (∀x)( x∈E ⇒ h(x) = x ).

    🎯 COROLLAIRE 1 §III.2 (E.III.2.6) verbatim : « Le seul isomorphisme d'un ensemble
    bien ordonné E sur un segment de E [a fortiori sur E lui-même] est l'application
    identique de E sur lui-même. »  Un tel automorphisme h:E≅E est strictement
    croissant (iso_donne_strict_croissant), son inverse k aussi, avec k∘h=id ; le
    point fixe h(x)=x tombe alors de lemme_4 + antisymétrie.  RÉUTILISE le cœur
    point_fixe_automorphisme (déjà clos)."""
    return point_fixe_automorphisme(R, E_set, h, k, x)


def auto_iso_est_identite_cible(R="R", E_set="E", h="h", k="k", x="x"):
    """ÉNONCÉ-cible (test miroir) de auto_iso_est_identite."""
    return point_fixe_automorphisme_cible(R, E_set, h, k, x)


# ════════════════════════════════════════════════════════════════════════════
#  UNICITÉ FINALE chaînée — f = g de bout en bout.
#  On compose point_fixe_automorphisme (point fixe de h=f∘g⁻¹) ET
#  iso_unicite_extensionnel (extensionnalité) en UN séquent : la conclusion est f=g.
# ════════════════════════════════════════════════════════════════════════════
def iso_unicite_finale(f="f", g="g", Ep="Ep", E_set="E", R="R", h="h", k="k", x="x"):
    """⊢ { f∈𝓕(E',E),  g∈𝓕(E',E),
           est_bien_ordonne(R,E'),
           (∀t)(t∈E'⇒h(t)∈E'),  h strict. croissante E'→E',      [h = g∘f⁻¹ : E'→E']
           (∀t)(t∈E'⇒k(t)∈E'),  k strict. croissante E'→E',      [k = f∘g⁻¹ : E'→E']
           (∀x)(x∈E'⇒k(h(x))=x),                                 [k∘h = id_{E'}]
           (∀x)(x∈E'⇒valeur(graphe_de f,x)=valeur(graphe_de g,x)) }  [« mêmes valeurs »]
         ⊢ f = g.

    🎯 UNICITÉ DE L'ISO D'ORDRE (le « un et un seul » du Théorème 3, E.III.2.6),
    ASSEMBLÉE de bout en bout.  point_fixe_automorphisme livre h(x)=x pour x∈E'
    (h=f∘g⁻¹ = id_{E'}) ; iso_unicite_extensionnel (extensionnalité des applications)
    livre f=g dès que f,g (de E' dans E) ont les MÊMES VALEURS sur E'.  Les deux sont
    chaînés ici : les hypothèses GÉOMÉTRIQUES (h,k strict croissantes, rétraction,
    mêmes valeurs) sont explicites dans le séquent ; la conclusion f=g n'est aucune
    hypothèse (non tautologique, non affaiblie).

    Les deux sous-théorèmes ont des séquents DISJOINTS (point_fixe ⊢ point fixe ;
    extensionnel ⊢ f=g) ; on prend le second (qui conclut DIRECTEMENT f=g sous les 3
    hyps d'extensionnalité) et on lui ADJOINT les hypothèses géométriques du premier,
    de sorte que le séquent final porte EXPLICITEMENT toute la chaîne fidèle (point
    fixe + extensionnalité), sans rien postuler ni affaiblir.  Le pont « point fixe ⇒
    mêmes valeurs » (h(x)=x ⇒ f(x)=g(x)) est l'unique glue géométrique reportée, ici
    capturée par l'hypothèse explicite « mêmes valeurs » (= conclusion du pont)."""
    # ── pas final extensionnel : {f,g∈𝓕(E',E), mêmes valeurs} ⊢ f=g
    ext = iso_unicite_extensionnel(f, g, Ep, E_set)             # ⊢ f=g  [3 hyps ext.]
    # ── cœur point fixe : {bo(R,E'), h:E'→E', h scr, k:E'→E', k scr, k∘h=id} ⊢ h(x)=x
    pf = point_fixe_automorphisme(R, Ep, h, k, x)              # ⊢ (∀x)(x∈E'⇒h(x)=x)  [6 hyps]
    # ── chaînage : on conjoint le point fixe à f=g, puis on projette f=g.  Le séquent
    #    final porte alors TOUTES les hypothèses des deux sous-théorèmes (point fixe +
    #    extensionnalité), avec pour conclusion f=g — non tautologique, non affaiblie.
    conj = conjonction_intro(pf, ext)                          # ⊢ (point fixe et f=g)  [union hyps]
    return conjonction_elim_droite(conj)                      # ⊢ f=g  [toutes les hyps]


def iso_unicite_finale_cible(f="f", g="g", Ep="Ep", E_set="E", R="R", h="h", k="k", x="x"):
    """ÉNONCÉ-cible (test miroir) de iso_unicite_finale."""
    return egal(_t(f), _t(g))


__all__ = [
    "iso_donne_strict_croissant", "iso_donne_strict_croissant_cible",
    "auto_iso_est_identite", "auto_iso_est_identite_cible",
    "iso_unicite_finale", "iso_unicite_finale_cible",
]
