"""§IV.2.1 — Morphismes et structures dérivées : fragment OBJET.

Le §IV.2 est ABSTRAIT au plus haut degré.  Un « σ-morphisme » (Déf. IV.2.1) est
défini, pour une espèce de structure Σ ARBITRAIRE, par un TERME GÉNÉRIQUE
σ{x,y,s,t} dont on POSTULE qu'il vérifie trois axiomes-SCHÉMAS :
  • (MO_I)   σ-morphismes ⊂ applications  (𝓕(x;y)) ;
  • (MO_II)  composée de morphismes est un morphisme ;
  • (MO_III) une bijection f est un isomorphisme ⟺ f et f⁻¹ sont des morphismes.
σ étant un PARAMÈTRE quantifié sur les espèces (méta), la notion générale de
σ-morphisme, les structures plus fines, initiales/finales, induites, produit,
quotient — toutes définies RELATIVEMENT à σ et à des propriétés universelles
(IN)/(FI) portant sur « toute structure Σ sur tout ensemble E' » — relèvent du
MÉTALANGAGE DES ESPÈCES.  Elles ne sont PAS exprimables par une seule formule du
fragment objet {var,τ,=,∈,¬,∨,∃} et sont REPORTÉES honnêtement (cf. rapport).

Ce qui EST exprimable au niveau objet — et que l'on encode + prouve ici — c'est
le morphisme CONCRET de l'Exemple 1 du Texte.tex (et de E.III.1.5,
« application croissante ») : pour une STRUCTURE RELATIONNELLE (une relation
R{x,y}, échelon S(E)=𝔓(E×E), le cas instancié par Bourbaki et déjà retenu en
IV.1, cf. ensembles_isomorphismes.py) :

    f est un σ-morphisme de (E,R) dans (E',R')  :=  f est une application de E
    dans E', ET pour tous u,v ∈ E :  R{u,v}  ⇒  R'{f(u), f(v)}.

(Pour l'ordre c'est exactement la Déf. IV.2.1, Ex.1 / III.1.5 : « (u,v)∈s
entraîne (f(u),f(v))∈t », l'application croissante.)  La clé « preserve » est la
clause de préservation de la relation ; l'isomorphisme (IV.1) en est le cas
biconditionnel + bijectif (R{u,v} ⇔ R'{f(u),f(v)}), d'où la cohérence avec
ensembles_isomorphismes.compatible.

THÉORÈMES DIRECTS certifiés par le noyau :
  • identite_preserve / identite_est_morphisme : l'identité Δ_E est un morphisme
    de (E,R) dans (E,R).  (IV.2.2 : RÉFLEXIVITÉ de « plus fine » par MO_III ;
    « id est un morphisme ».)  Δ_E(u)=u (diagonale_valeur) ⇒ R{Δu,Δv} se réécrit
    R{u,v}, donc R{u,v}⇒R{Δu,Δv} trivialement.
  • composee_preserve : (MO_II), CŒUR de la stabilité par composition.  Si f
    préserve R→R' et g préserve R'→R'', alors g∘f préserve R→R'' (sous les
    hypothèses fonctionnelles rendant (g∘f)(u)=g(f(u)), composition_valeur).
    Réutilise composition_valeur (ensembles_fonctions_composee).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, impl, pourtout, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as eg_symetrie
from bourbaki.cardinaux.ensembles_equipotence import (diagonale_fonctionnelle, diagonale_domaine,
                                    diagonale_valeur)
from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composition_valeur


# ── relation relationnelle générique par défaut ───────────────────────────────
def _rel_defaut(nom):
    """R{x,y} := (x,y) ∈ G  pour un graphe G arbitraire nommé `nom` (échelon
    relationnel 𝔓(E×E) ; le lecteur passe sa propre relation R)."""
    vG = var(nom)
    return lambda a, b: appartient(E.couple(a, b), vG)


# ── préservation de la relation (clause clé du σ-morphisme relationnel) ────────
def preserve_relation(f, e, r, rp, u="u", v="v"):
    """« f préserve R vers R' sur E » := (∀u)(∀v)((u∈E et v∈E et R{u,v}) ⇒
        R'{f(u), f(v)}).   (Déf. IV.2.1, Ex.1 ; III.1.5 application croissante.)"""
    vu, vv = var(u), var(v)
    fu, fv = E.valeur(f, vu), E.valeur(f, vv)
    return pourtout(u, pourtout(v,
        impl(et(et(appartient(vu, e), appartient(vv, e)), r(vu, vv)),
             rp(fu, fv))))


def est_morphisme(f, e, ep, r, rp):
    """« f est un σ-morphisme de (E,R) dans (E',R') » := f est une application
    (graphe fonctionnel défini sur E, image ⊂ E') ET f préserve R vers R'
    (IV.2.1, cas objet relationnel ; Ex.1 = application croissante).

    L'« application de E dans E' » est codée, comme dans tout le projet, par son
    graphe : fonctionnel et de domaine E (la condition image⊂E' est portée par
    le contexte ; on retient ici le noyau fonctionnel + préservation, qui est la
    part SUBSTANTIELLE et la seule où réside le contenu du critère MO)."""
    appli = et(E.est_fonctionnel(f), egal(E.dom(f), e))
    return et(appli, preserve_relation(f, e, r, rp))


# ── « plus fine » (IV.2.2) au niveau objet ────────────────────────────────────
def plus_fine_morphisme(e, r1, r2):
    """« 𝒮₁ plus fine que 𝒮₂ sur E » := id_E : (E,R₁)→(E,R₂) est un morphisme
    (IV.2.2).  Au niveau objet relationnel : Δ_E préserve R₁ vers R₂."""
    return est_morphisme(E.diagonale(var(e)) if isinstance(e, str) else E.diagonale(e),
                         var(e) if isinstance(e, str) else e,
                         var(e) if isinstance(e, str) else e, r1, r2)


# ── THÉORÈME : l'identité préserve R (cœur de « id est un morphisme ») ─────────
def identite_preserve(e="E", r=None, u="u", v="v"):
    """⊢ preserve_relation(Δ_E, E, R, R).   (IV.2.2 : RÉFLEXIVITÉ de « plus fine »
    via MO_III ; « l'application identique est un morphisme ».)

    Pour u,v∈E : Δ_E(u)=u, Δ_E(v)=v (diagonale_valeur) ; donc R{Δu,Δv} se réécrit
    (Leibniz, S6) en R{u,v}, et la clause (u∈E et v∈E et R{u,v}) ⇒ R{Δu,Δv}
    devient l'implication triviale, déchargée par déduction."""
    if r is None:
        r = _rel_defaut("G")
    vE, vu, vv = var(e), var(u), var(v)
    DE = E.diagonale(vE)
    du, dv = E.valeur(DE, vu), E.valeur(DE, vv)

    hyp = et(et(appartient(vu, vE), appartient(vv, vE)), r(vu, vv))
    h = N.assume(hyp)
    u_inE = conjonction_elim_gauche(conjonction_elim_gauche(h))   # u∈E
    v_inE = conjonction_elim_droite(conjonction_elim_gauche(h))   # v∈E
    r_uv = conjonction_elim_droite(h)                             # R{u,v}

    # Δu = u  et  Δv = v   (diagonale_valeur, déchargées de l'appartenance)
    du_eq = N.modus_ponens(u_inE,
        N.loi_deduction(appartient(vu, vE), diagonale_valeur(e, u)))   # Δu=u
    dv_eq = N.modus_ponens(v_inE,
        N.loi_deduction(appartient(vv, vE), diagonale_valeur(e, v)))   # Δv=v
    u_eq_du = N.modus_ponens(du_eq, eg_symetrie(du, vu))         # u=Δu
    v_eq_dv = N.modus_ponens(dv_eq, eg_symetrie(dv, vv))         # v=Δv

    # Leibniz : R{u,v} ⇔ R{Δu,v} ⇔ R{Δu,Δv}
    w = var("w")
    leib1 = N.modus_ponens(u_eq_du, N.s6(vu, du, "w", r(w, vv)))   # R{u,v}⇔R{Δu,v}
    leib2 = N.modus_ponens(v_eq_dv, N.s6(vv, dv, "w", r(du, w)))   # R{Δu,v}⇔R{Δu,Δv}
    r_du_v  = N.modus_ponens(r_uv, equivalence_avant(leib1))       # R{Δu,v}
    r_du_dv = N.modus_ponens(r_du_v, equivalence_avant(leib2))     # R{Δu,Δv}

    inner = N.loi_deduction(hyp, r_du_dv)                          # (…) ⇒ R{Δu,Δv}
    return N.generalisation(u, N.generalisation(v, inner))


def identite_est_morphisme(e="E", r=None):
    """⊢ est_morphisme(Δ_E, E, E, R, R).   (IV.2.2 ; « id est un morphisme »,
    réflexivité de « plus fine ».)  Conjugue le noyau fonctionnel de Δ_E
    (diagonale_fonctionnelle + dom Δ_E = E) et identite_preserve."""
    if r is None:
        r = _rel_defaut("G")
    appli = conjonction_intro(diagonale_fonctionnelle(e), diagonale_domaine(e))
    return conjonction_intro(appli, identite_preserve(e, r))


# ── THÉORÈME (MO_II) : la composée préserve la relation (cœur POINTWISE) ───────
def composee_preserve(g="G", f="F", e="E", ep="Ep", r=None, rp=None, rpp=None,
                      u="u", v="v"):
    """⊢ (u∈E et v∈E et R{u,v}) ⇒ R''{(G∘F)(u),(G∘F)(v)}   (forme POINTWISE)
    sous les hypothèses (= h.hypotheses) :
      • preserve_relation(F,E,R,R')   (f préserve R→R')
      • preserve_relation(G,E',R',R'') (g préserve R'→R'')
      • f(u)∈E' , f(v)∈E'             (typage des images dans E')
      • F,G fonctionnels + u,v,f(u),f(v) dans les domaines  (de composition_valeur)

    (Axiome MO_II, Déf. IV.2.1 — STABILITÉ PAR COMPOSITION, CŒUR logique.)
    NB : on prouve la clause POINTWISE (sans le préfixe (∀u)(∀v)) car les
    conditions de typage « f(u)∈E' » et les hypothèses de composition_valeur
    contiennent u,v libres — généraliser violerait la garde-fou du noyau.  C'est
    l'expression fidèle du contenu : Bourbaki POSTULE MO_II comme axiome de la
    donnée σ ; on le DÉMONTRE ici pour le σ relationnel (application croissante).
    Contenu : (R{u,v}⇒R'{f(u),f(v)}) et (R'{…}⇒R''{g(f(u)),g(f(v))}) donnent
    R{u,v}⇒R''{g(f(u)),g(f(v))} ; on réécrit g(f(·))=(g∘f)(·) (composition_valeur)."""
    if r is None:   r   = _rel_defaut("G_R")
    if rp is None:  rp  = _rel_defaut("G_Rp")
    if rpp is None: rpp = _rel_defaut("G_Rpp")
    vG, vF, vE, vEp = var(g), var(f), var(e), var(ep)
    vu, vv = var(u), var(v)
    comp = E.composee(vG, vF)
    fu, fv = E.valeur(vF, vu), E.valeur(vF, vv)
    gfu, gfv = E.valeur(vG, fu), E.valeur(vG, fv)          # g(f(u)), g(f(v))
    gof_u, gof_v = E.valeur(comp, vu), E.valeur(comp, vv)  # (g∘f)(u), (g∘f)(v)

    # hypothèses de préservation, instanciées à u,v / f(u),f(v)
    h_f = N.assume(preserve_relation(vF, vE, r, rp))      # f préserve R→R'
    h_g = N.assume(preserve_relation(vG, vEp, rp, rpp))   # g préserve R'→R''
    inst_f = instancie(instancie(h_f, vu), vv)            # (u∈E et v∈E et R{u,v})⇒R'{f(u),f(v)}
    inst_g = instancie(instancie(h_g, fu), fv)            # (f(u)∈E' et f(v)∈E' et R'{f(u),f(v)})⇒R''{g(f(u)),g(f(v))}

    # — preuve par déduction depuis l'antécédent (u∈E et v∈E et R{u,v}) —
    hyp = et(et(appartient(vu, vE), appartient(vv, vE)), r(vu, vv))
    h = N.assume(hyp)
    rp_fu_fv = N.modus_ponens(h, inst_f)                  # R'{f(u),f(v)}
    # construire l'antécédent de inst_g : (f(u)∈E' et f(v)∈E' et R'{f(u),f(v)})
    fu_inEp = N.assume(appartient(fu, vEp))               # f(u)∈E'   (hypothèse de typage)
    fv_inEp = N.assume(appartient(fv, vEp))               # f(v)∈E'
    ant_g = conjonction_intro(conjonction_intro(fu_inEp, fv_inEp), rp_fu_fv)
    rpp_gfu_gfv = N.modus_ponens(ant_g, inst_g)           # R''{g(f(u)),g(f(v))}

    # réécrire g(f(u))=(g∘f)(u), g(f(v))=(g∘f)(v)  via composition_valeur
    cu = composition_valeur(g, f, u)                      # (g∘f)(u)=g(f(u))
    cv = composition_valeur(g, f, v)                      # (g∘f)(v)=g(f(v))
    gfu_eq = N.modus_ponens(cu, eg_symetrie(gof_u, gfu))  # g(f(u))=(g∘f)(u)
    gfv_eq = N.modus_ponens(cv, eg_symetrie(gof_v, gfv))  # g(f(v))=(g∘f)(v)
    leib_u = N.modus_ponens(gfu_eq, N.s6(gfu, gof_u, "w", rpp(var("w"), gfv)))  # R''{g(f(u)),g(f(v))}⇔R''{(g∘f)(u),g(f(v))}
    leib_v = N.modus_ponens(gfv_eq, N.s6(gfv, gof_v, "w", rpp(gof_u, var("w"))))# R''{(g∘f)(u),g(f(v))}⇔R''{(g∘f)(u),(g∘f)(v)}
    step1 = N.modus_ponens(rpp_gfu_gfv, equivalence_avant(leib_u))       # R''{(g∘f)(u),g(f(v))}
    rpp_comp = N.modus_ponens(step1, equivalence_avant(leib_v))          # R''{(g∘f)(u),(g∘f)(v)}

    return N.loi_deduction(hyp, rpp_comp)                 # (u∈E et v∈E et R{u,v}) ⇒ R''{(g∘f)u,(g∘f)v}


__all__ = ["preserve_relation", "est_morphisme", "plus_fine_morphisme",
           "identite_preserve", "identite_est_morphisme", "composee_preserve"]
