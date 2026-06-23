"""§II.6 — Compléments sur les relations d'équivalence (notions à DÉFINIR).

Fichier NEUF, distinct de `ensembles_decomposition_quotient.py` (R_f, surjection /
injection canoniques, bijection_induite, décomposition canonique, quotient R/S) et
de `ensembles_abrege` (est_relation_equivalence, classe, quotient, est_compatible,
est_compatible_application, est_saturee, sature, classe_objets, …).  Il INTRODUIT
(définitions fidèles VERBATIM) les notions complémentaires de §II.6 qui n'étaient
encore définies nulle part :

  • **Système de représentants** des classes suivant R  (E.II.6.2, Déf.) :
        – `est_systeme_representants(S, g, e)`  : une partie S de E que l'injection
          canonique met en bijection avec E/R  (S ↔ E/R) ;
        – `injection_representants(r, g, e)`    : une injection r : E/R → E dont
          l'image est un système de représentants  (toute section convient) ;

  • **Application compatible avec R et S**  (E.II.6.5, Déf.) :
        – `est_compatible_RS(f, R, S)`           : x ≡ x' (R) ⇒ f(x) ≡ f(x') (S) ;
        – `application_deduite_quotient(f, p, h)`: prédicat « f = h ∘ p » (application
          déduite de f par passage au quotient suivant R) ;
        – `application_deduite_quotients(f, u, v, h)` : prédicat « v ∘ f = h ∘ u »
          (application déduite par passage aux quotients suivant R ET S) ;

  • **Relation induite R_A**  (E.II.6.6, Déf.) :
        – `relation_induite(R, a)`               : R_A{x,y} := x∈A et y∈A et R{x,y} ;

  • **Image réciproque d'une relation par une application**  (E.II.6.6, Déf.) :
        – `image_reciproque_relation(S, phi)`    : (S∘φ){x,y} := S{φ(x), φ(y)} ;
        – `image_reciproque_relation_dans(S, phi, e)` : forme gardée par E (x,y∈E) ;
        – `graphe_image_reciproque_relation(S, phi, e)` : graphe {(x,y)∈E×E | S{φx,φy}} ;

  • **Ensemble des classes d'objets équivalents**  (E.II.6.9, Déf.) :
        – `ensemble_classes_objets(R, T)` (= E_R) : terme {z | ∃x(x∈T et R{x,x} et
          z = θ{x})}, défini par axiome de membership dédié (S8+A1, paramétré ; T =
          transversal complet) — `theorie_ensembles` INCHANGÉE (axiome en théorie
          DÉDIÉE, jamais dans theorie_ensembles).

LEMMES DIRECTS PROUVÉS (noyau abrégé, clos) :
  • `relation_induite_implique(R, a)` : R_A{x,y} ⇒ R{x,y}  (instance directe) ;
  • `relation_induite_symetrique`     : R symétrique ⇒ R_A symétrique  (clos mod. hyp.) ;
  • `image_reciproque_symetrique`     : S symétrique ⇒ (S∘φ) symétrique  (clos mod. hyp.) ;
  • `image_reciproque_transitive`     : S transitive ⇒ (S∘φ) transitive  (clos mod. hyp.) ;
  • `classe_objets_unicite`           : x ≡ y (R) ⇒ θ{x}=θ{y}  (E.II.6.9 ; clos mod. hyp.) ;
  • `compatible_RS_via_v`             : f compat. R,S ⇒ v∘f compat. R  (lecture, mod. hyp.).

REPORTÉ (théorèmes durs) : bijectivité effective S↔E/R d'un système de
représentants, existence/unicité de l'application déduite (h), que les classes de
R_A sont les traces sur A.  Les NOTIONS sont DÉFINIES, seules leurs preuves dures
sont reportées (jamais postulées).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, egal, et, impl, equiv,
                                       appartient, existe, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)


def _tv(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
# 1.  Système de représentants des classes suivant R  (E.II.6.2, Déf.)
# ════════════════════════════════════════════════════════════════════════════
def est_systeme_representants(S, g, e):
    """« S est un système de représentants des classes suivant R »  (E.II.6.2).

    Bourbaki : « Toute partie S de E que l'on peut mettre en bijection avec E/R
    par l'injection canonique suivant R s'appelle un système de représentants des
    classes d'équivalence suivant R. »  On code donc :

        S ⊂ E  ET  l'application canonique p = (x ↦ Cl_R(x)) restreinte à S est
        une bijection de S sur E/R.

    g : graphe de R ; e = E ; S : la partie de E.  La restriction p|S a pour graphe
    `restriction(application_canonique(g,e), S)` ; sa bijectivité de S sur E/R est
    `est_bijective(p|S, S, E/R)`  (E.II.49)."""
    vS, vg, ve = _tv(S), _tv(g), _tv(e)
    p = E.application_canonique(vg, ve)              # graphe de p : E → E/R
    p_S = E.restriction(p, vS)                       # graphe de p|S
    return et(E.inclus(vS, ve),
              E.est_bijective(p_S, vS, E.quotient(vg, ve)))


def injection_representants(r, g, e):
    """« r est un système de représentants (forme injection r : E/R → E) »  (E.II.6.2).

    Bourbaki : « On désigne aussi sous ce nom toute injection r de E/R dans E telle
    que l'image de E/R par cette injection soit un système de représentants des
    classes d'équivalence suivant R. »  Codé par :

        r injective ET son image r⟨E/R⟩ est un système de représentants.

    r : graphe de l'injection ; g : graphe de R ; e = E.  (Toute section associée à
    l'application canonique p répond à la définition.)"""
    vr, vg, ve = _tv(r), _tv(g), _tv(e)
    quot = E.quotient(vg, ve)
    return et(E.injective_dans(vr, quot),
              est_systeme_representants(E.image(vr, quot), vg, ve))


# ════════════════════════════════════════════════════════════════════════════
# 2.  Application compatible avec R et S ; applications déduites  (E.II.6.5)
# ════════════════════════════════════════════════════════════════════════════
def est_compatible_RS(f, R, S, x="x", xp="xp"):
    """« f compatible avec les relations d'équivalence R et S »  (E.II.6.5, Déf.).

    f : E → F, R équivalence dans E, S équivalence dans F.  Bourbaki : « cela
    signifie que x ≡ x' (mod R) entraîne f(x) ≡ f(x') (mod S) ».  Codé :

        (∀x)(∀x')( R{x,x'} ⇒ S{f(x), f(x')} ).

    f : terme (application) ; R, S : relations (fonctions (Terme,Terme)→Formule)."""
    vf = _tv(f)
    vx, vxp = var(x), var(xp)
    return pourtout(x, pourtout(xp,
        impl(R(vx, vxp), S(E.valeur(vf, vx), E.valeur(vf, vxp)))))


def application_deduite_quotient(f, p, h):
    """« h est déduite de f par passage au quotient suivant R » := f = h ∘ p  (E.II.6.5).

    Lorsque f (de E dans F) est compatible avec R, on la met sous la forme h ∘ g,
    g = p étant l'application canonique de E sur E/R, h : E/R → F uniquement
    déterminée.  PRÉDICAT (égalité des graphes) : F = H ∘ P (composée Bourbaki :
    H∘P applique d'abord p puis h).  f, p, h sont les GRAPHES.  L'existence/unicité
    effective de h (h = f∘s) est REPORTÉE (Critère C57)."""
    return egal(_tv(f), E.composee(_tv(h), _tv(p)))


def application_deduite_quotients(f, u, v, h):
    """« h est déduite de f par passage aux quotients suivant R et S » := v∘f = h∘u
    (E.II.6.5, Déf.).

    f : E → F, u : E → E/R, v : F → F/S applications canoniques, h : E/R → F/S.
    Bourbaki : h « est caractérisée par v ∘ f = h ∘ u ».  PRÉDICAT (égalité des
    graphes) : V∘F = H∘U  (composées Bourbaki).  f, u, v, h sont les GRAPHES."""
    vf, vu, vv, vh = _tv(f), _tv(u), _tv(v), _tv(h)
    return egal(E.composee(vv, vf), E.composee(vh, vu))


def compatible_RS_via_v(f="f", R=None, S=None, v="v", x="x", xp="xp"):
    """{f compat. R,S} ⊢ (∀x)(∀x')(R{x,x'} ⇒ (S∘v applied) …)  — lecture « v∘f compat. R ».

    Bourbaki définit « f compatible avec R et S » comme « v∘f compatible avec R »,
    c'est-à-dire (∀x)(∀x')(R{x,x'} ⇒ v(f(x)) ≡ v(f(x')) (mod S')) ; sous l'angle des
    valeurs, la compatibilité R,S de f donne directement S{f(x),f(x')} pour tout
    couple R-équivalent.  On atteste ici l'instance : sous l'hypothèse de
    compatibilité R,S, R{x,x'} ⇒ S{f(x),f(x')}  (cœur de « v∘f compatible avec R »).

    R, S relations à graphe par défaut.  Théorème clos modulo l'hypothèse de
    compatibilité (hypothèses = {est_compatible_RS(f,R,S)})."""
    if R is None:
        R = E.rel_graphe("GR")
    if S is None:
        S = E.rel_graphe("GS")
    vf = _tv(f)
    vx, vxp = var(x), var(xp)
    hyp = est_compatible_RS(vf, R, S, x, xp)
    h = N.assume(hyp)                                # (∀x)(∀x')(R{x,x'}⇒S{f(x),f(x')})
    return instancie(instancie(h, vx), vxp)          # R{x,x'} ⇒ S{f(x),f(x')}


# ════════════════════════════════════════════════════════════════════════════
# 3.  Relation induite R_A sur une partie A de E  (E.II.6.6, Déf.)
# ════════════════════════════════════════════════════════════════════════════
def relation_induite(R, a):
    """R_A{x,y} := (x∈A et y∈A et R{x,y})  (relation d'équivalence induite par R
    dans A, E.II.6.6, Déf.).

    Image réciproque de R par l'injection canonique j : A ↪ E.  Renvoie une
    fonction (Terme, Terme) → Formule.  R : relation (fonction) ; a : terme A."""
    va = _tv(a)

    def rel(x, y):
        return et(et(appartient(x, va), appartient(y, va)), R(x, y))
    return rel


def relation_induite_implique(R=None, a="A", x="x", y="y"):
    """⊢ (∀x)(∀y)(R_A{x,y} ⇒ R{x,y})  (la relation induite est plus fine que R ; clos).

    R_A est le graphe de R restreint à A×A : R_A{x,y} entraîne immédiatement R{x,y}
    (3e conjonct).  R relation à graphe par défaut ; A terme."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _tv(a)
    vx, vy = var(x), var(y)
    RA = relation_induite(R, va)
    h = N.assume(RA(vx, vy))                          # (x∈A et y∈A) et R{x,y}
    concl = conjonction_elim_droite(h)                # R{x,y}
    imp = N.loi_deduction(RA(vx, vy), concl)
    return N.generalisation(x, N.generalisation(y, imp))


def relation_induite_symetrique(R=None, a="A", x="x", y="y"):
    """{R symétrique} ⊢ (∀x)(∀y)(R_A{x,y} ⇒ R_A{y,x})  (R_A symétrique ; clos mod. hyp.).

    De « x∈A et y∈A et R{x,y} » : on commute les appartenances et, par symétrie de R
    (hypothèse), R{x,y} ⇒ R{y,x}, d'où « y∈A et x∈A et R{y,x} » = R_A{y,x}."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _tv(a)
    vx, vy = var(x), var(y)
    RA = relation_induite(R, va)
    hsym = N.assume(E.est_symetrique(R, x, y))        # (∀x)(∀y)(R{x,y}⇒R{y,x})
    h = N.assume(RA(vx, vy))                          # (x∈A et y∈A) et R{x,y}
    appart = conjonction_elim_gauche(h)               # x∈A et y∈A
    hx = conjonction_elim_gauche(appart)              # x∈A
    hy = conjonction_elim_droite(appart)              # y∈A
    rxy = conjonction_elim_droite(h)                  # R{x,y}
    imp_sym = instancie(instancie(hsym, vx), vy)      # R{x,y} ⇒ R{y,x}
    ryx = N.modus_ponens(rxy, imp_sym)                # R{y,x}
    but = conjonction_intro(conjonction_intro(hy, hx), ryx)   # R_A{y,x}
    imp = N.loi_deduction(RA(vx, vy), but)
    return N.generalisation(x, N.generalisation(y, imp))


# ════════════════════════════════════════════════════════════════════════════
# 4.  Image réciproque d'une relation par une application  (E.II.6.6, Déf.)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_relation(S, phi):
    """(S∘φ){x,y} := S{φ(x), φ(y)}  (image réciproque de S par φ, E.II.6.6, Déf.).

    φ : E → F application, S relation d'équivalence dans F.  Bourbaki : « la relation
    d'équivalence associée à l'application u∘φ … s'appelle l'image réciproque de S
    par φ, et se note S{φ(x), φ(y)} ».  Renvoie une fonction (Terme,Terme)→Formule.
    S : relation (fonction) ; phi : terme (graphe de l'application)."""
    vphi = _tv(phi)

    def rel(x, y):
        return S(E.valeur(vphi, x), E.valeur(vphi, y))
    return rel


def image_reciproque_relation_dans(S, phi, e):
    """Forme gardée par E : (S∘φ){x,y} := (x∈E et y∈E et S{φ(x),φ(y)})  (E.II.6.6).

    Variante « relation d'équivalence DANS E » : la relation associée à u∘φ
    (E.II.6.2) est réflexive dans E = dom φ.  e = E.  Renvoie (Terme,Terme)→Formule."""
    vphi, ve = _tv(phi), _tv(e)

    def rel(x, y):
        return et(et(appartient(x, ve), appartient(y, ve)),
                  S(E.valeur(vphi, x), E.valeur(vphi, y)))
    return rel


def graphe_image_reciproque_relation(S, phi, e):
    """Graphe S∘φ := {(x,y)∈E×E | S{φ(x),φ(y)}}  (codage, E.II.6.6).

    Terme défini par axiome de membership dédié (S8+A1, paramétré).  S est ici
    donnée par son GRAPHE gS (Cl_S = G_S⟨{·}⟩) : S{a,b} := (a,b)∈gS.  phi : graphe
    de φ ; e = E.  Caractérisé par `axiome_graphe_image_reciproque`."""
    return app("img_recip_rel", _tv(S), _tv(phi), _tv(e))


def axiome_graphe_image_reciproque(gS="GS", phi="phi", e="E", w="w", x="x", y="y"):
    """⊢-schéma : (∀w)(w∈(S∘φ) ⇔ ∃x∃y(x∈E et y∈E et w=(x,y) et (φ(x),φ(y))∈gS))
    (membership de S∘φ, S8+A1 ; clos comme axiome de sa théorie dédiée).

    gS : graphe de S ; phi : graphe de φ ; e = E.  PARAMÈTRES."""
    vgS, vphi, ve = _tv(gS), _tv(phi), _tv(e)
    vw, vx, vy = var(w), var(x), var(y)
    corps = existe(x, existe(y,
        et(et(et(appartient(vx, ve), appartient(vy, ve)),
               egal(vw, E.couple(vx, vy))),
           appartient(E.couple(E.valeur(vphi, vx), E.valeur(vphi, vy)), vgS))))
    return pourtout(w, equiv(
        appartient(vw, graphe_image_reciproque_relation(vgS, vphi, ve)), corps))


def theorie_graphe_image_reciproque(gS="GS", phi="phi", e="E", w="w", x="x", y="y"):
    """Théorie ne contenant que l'instance de l'axiome de membership de S∘φ."""
    return N.Theorie("Image-réciproque-relation",
                     [axiome_graphe_image_reciproque(gS, phi, e, w, x, y)])


def membre_graphe_image_reciproque(gS="GS", phi="phi", e="E", w="w", x="x", y="y"):
    """⊢ (w∈(S∘φ)) ⇔ ∃x∃y(…)  (instance de l'axiome de membership ; clos).

    Sort clos de la théorie dédiée — `theorie_ensembles` reste à 22 axiomes."""
    vw = var(w)
    ax = N.axiome(theorie_graphe_image_reciproque(gS, phi, e, w, x, y),
                  axiome_graphe_image_reciproque(gS, phi, e, w, x, y))
    return instancie(ax, vw)


def image_reciproque_symetrique(S=None, phi="phi", x="x", y="y"):
    """{S symétrique} ⊢ (∀x)(∀y)((S∘φ){x,y} ⇒ (S∘φ){y,x})  ((S∘φ) symétrique ; clos mod. hyp.).

    (S∘φ){x,y} = S{φx,φy} ; par symétrie de S, S{φx,φy} ⇒ S{φy,φx} = (S∘φ){y,x}.
    L'image réciproque hérite de la symétrie de S."""
    if S is None:
        S = E.rel_graphe("GS")
    vphi = _tv(phi)
    vx, vy = var(x), var(y)
    SP = image_reciproque_relation(S, vphi)
    hsym = N.assume(E.est_symetrique(S, "a", "b"))    # (∀a)(∀b)(S{a,b}⇒S{b,a})
    h = N.assume(SP(vx, vy))                          # S{φx,φy}
    # instancier la symétrie de S en (φx, φy)
    imp = instancie(instancie(hsym, E.valeur(vphi, vx)), E.valeur(vphi, vy))  # S{φx,φy}⇒S{φy,φx}
    concl = N.modus_ponens(h, imp)                    # S{φy,φx} = (S∘φ){y,x}
    dimp = N.loi_deduction(SP(vx, vy), concl)
    return N.generalisation(x, N.generalisation(y, dimp))


def image_reciproque_transitive(S=None, phi="phi", x="x", y="y", z="z"):
    """{S transitive} ⊢ (∀x)(∀y)(∀z)(((S∘φ){x,y} et (S∘φ){y,z}) ⇒ (S∘φ){x,z})
    ((S∘φ) transitive ; clos mod. hyp.).

    (S∘φ){x,y} et (S∘φ){y,z} = S{φx,φy} et S{φy,φz} ; transitivité de S en
    (φx,φy,φz) donne S{φx,φz} = (S∘φ){x,z}."""
    if S is None:
        S = E.rel_graphe("GS")
    vphi = _tv(phi)
    vx, vy, vz = var(x), var(y), var(z)
    SP = image_reciproque_relation(S, vphi)
    htr = N.assume(E.est_transitive(S, "a", "b", "c"))   # (∀a)(∀b)(∀c)((S{a,b}et S{b,c})⇒S{a,c})
    h = N.assume(et(SP(vx, vy), SP(vy, vz)))             # S{φx,φy} et S{φy,φz}
    imp = instancie(instancie(instancie(htr,
            E.valeur(vphi, vx)), E.valeur(vphi, vy)), E.valeur(vphi, vz))
    concl = N.modus_ponens(h, imp)                       # S{φx,φz} = (S∘φ){x,z}
    dimp = N.loi_deduction(et(SP(vx, vy), SP(vy, vz)), concl)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, dimp)))


# ════════════════════════════════════════════════════════════════════════════
# 5.  Ensemble des classes d'objets équivalents  E_R  (E.II.6.9, Déf.)
# ════════════════════════════════════════════════════════════════════════════
def classe_objets(R, x, y="y"):
    """θ{x} := τ_y(R{x,y})  (classe d'objets équivalents à x, E.II.6.9 ; R sans graphe).

    Alias documenté de `E.classe_objets` (la NOTION du TERME θ existe déjà en
    abrégé) — réexposé ici pour la lisibilité du module E_R bâti dessus."""
    return E.classe_objets(R, x, y)


def ensemble_classes_objets(R, T):
    """E_R := { z | (∃x)(x∈T et R{x,x} et z = θ{x}) }  (ensemble des classes d'objets
    équivalents, E.II.6.9, Déf.).

    R relation (sans graphe nécessairement) ; T = transversal complet (terme ne
    contenant pas x, tel que (∀y)(R{y,y} ⇒ (∃x)(x∈T et R{x,y}))).  Terme défini par
    son axiome de membership dédié (S8+A1, paramétré) — `theorie_ensembles` reste à
    22 axiomes.  Caractérisé par `axiome_ensemble_classes_objets`.

    R est passée comme fonction (Terme,Terme)→Formule ; le nom du terme dépend du
    nom de T uniquement (R est fixée par le contexte de la théorie dédiée)."""
    return app("ens_classes_obj", _tv(T))


def axiome_ensemble_classes_objets(R, T="T", z="z", x="x"):
    """⊢-schéma : (∀z)(z∈E_R ⇔ (∃x)(x∈T et R{x,x} et z = θ{x}))  (membership, S8+A1).

    Caractérise E_R = ensemble_classes_objets(R, T).  R : relation (fonction) ;
    T : terme transversal.  PARAMÈTRES (T)."""
    vT, vz, vx = _tv(T), var(z), var(x)
    corps = existe(x, et(et(appartient(vx, vT), R(vx, vx)),
                         egal(vz, classe_objets(R, vx, y="_yθ"))))
    return pourtout(z, equiv(appartient(vz, ensemble_classes_objets(R, vT)), corps))


def theorie_ensemble_classes_objets(R, T="T", z="z", x="x"):
    """Théorie ne contenant que l'instance de l'axiome de membership de E_R."""
    return N.Theorie("Ensemble-classes-objets",
                     [axiome_ensemble_classes_objets(R, T, z, x)])


def membre_ensemble_classes_objets(R, T="T", z="z", x="x"):
    """⊢ (z∈E_R) ⇔ (∃x)(x∈T et R{x,x} et z=θ{x})  (instance de l'axiome ; clos).

    Théorème de membership de E_R (sort clos de sa théorie dédiée — theorie_ensembles
    inchangée = 22)."""
    vz = var(z)
    ax = N.axiome(theorie_ensemble_classes_objets(R, T, z, x),
                  axiome_ensemble_classes_objets(R, T, z, x))
    return instancie(ax, vz)


def classe_objets_unicite(R=None, x="x", xp="xp", y="y"):
    """{R relation d'équivalence (sym.+trans.)} ⊢ R{x,x'} ⇒ θ{x}=θ{x'}  (E.II.6.9 ; clos mod. hyp.).

    Bourbaki : « On a R{x,x'} ⇒ θ{x} = θ{x'} ».  Sous l'hypothèse R{x,x'}, R{x,·} et
    R{x',·} sont équivalentes (par symétrie+transitivité), donc (∀y)(R{x,y} ⇔ R{x',y}),
    d'où par S7 (extensionnalité du τ) τ_y(R{x,y}) = τ_y(R{x',y}), soit θ{x}=θ{x'}.

    Le liant du τ est « y » (= liant par défaut de θ = classe_objets), si bien que
    la conclusion est littéralement « R{x,x'} ⇒ classe_objets(R,x)=classe_objets(R,x') ».
    R relation à graphe par défaut ; clos modulo {R symétrique, R transitive, R{x,x'}}."""
    if R is None:
        R = E.rel_graphe("GR")
    vx, vxp = var(x), var(xp)
    vy = var(y)
    # hypothèses : symétrie, transitivité de R, et R{x,x'}
    hsym = N.assume(E.est_symetrique(R, "a", "b"))       # (∀a)(∀b)(R{a,b}⇒R{b,a})
    htr = N.assume(E.est_transitive(R, "a", "b", "c"))   # transitivité
    hxxp = N.assume(R(vx, vxp))                          # R{x,x'}
    hxpx = N.modus_ponens(hxxp, instancie(instancie(hsym, vx), vxp))  # R{x',x}
    # ⇒ : R{x,y} ⇒ R{x',y}  via  R{x',x} et R{x,y} ⇒ R{x',y}
    h_xy = N.assume(R(vx, vy))
    tr_a = instancie(instancie(instancie(htr, vxp), vx), vy)   # (R{x',x}et R{x,y})⇒R{x',y}
    r_xpy = N.modus_ponens(conjonction_intro(hxpx, h_xy), tr_a)
    imp_fwd = N.loi_deduction(R(vx, vy), r_xpy)          # R{x,y} ⇒ R{x',y}
    # ⇐ : R{x',y} ⇒ R{x,y}  via  R{x,x'} et R{x',y} ⇒ R{x,y}
    h_xpy = N.assume(R(vxp, vy))
    tr_b = instancie(instancie(instancie(htr, vx), vxp), vy)   # (R{x,x'}et R{x',y})⇒R{x,y}
    r_xy = N.modus_ponens(conjonction_intro(hxxp, h_xpy), tr_b)
    imp_bwd = N.loi_deduction(R(vxp, vy), r_xy)          # R{x',y} ⇒ R{x,y}
    eqv = conjonction_intro(imp_fwd, imp_bwd)            # R{x,y} ⇔ R{x',y}
    gen = N.generalisation(y, eqv)                       # (∀y)(R{x,y} ⇔ R{x',y})
    # S7 : (∀y)(R{x,y}⇔R{x',y}) ⇒ τ_y R{x,y} = τ_y R{x',y}
    s7 = N.s7(R(vx, vy), R(vxp, vy), y)
    eq_theta = N.modus_ponens(gen, s7)                   # θ{x} = θ{x'}
    return N.loi_deduction(R(vx, vxp), eq_theta)         # {sym,trans} ⊢ R{x,x'} ⇒ θ{x}=θ{x'}


__all__ = [
    # 1. système de représentants
    "est_systeme_representants", "injection_representants",
    # 2. compatible R et S, applications déduites
    "est_compatible_RS", "application_deduite_quotient",
    "application_deduite_quotients", "compatible_RS_via_v",
    # 3. relation induite R_A
    "relation_induite", "relation_induite_implique", "relation_induite_symetrique",
    # 4. image réciproque d'une relation
    "image_reciproque_relation", "image_reciproque_relation_dans",
    "graphe_image_reciproque_relation", "axiome_graphe_image_reciproque",
    "theorie_graphe_image_reciproque", "membre_graphe_image_reciproque",
    "image_reciproque_symetrique", "image_reciproque_transitive",
    # 5. ensemble des classes d'objets équivalents
    "classe_objets", "ensemble_classes_objets", "axiome_ensemble_classes_objets",
    "theorie_ensemble_classes_objets", "membre_ensemble_classes_objets",
    "classe_objets_unicite",
]
