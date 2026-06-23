"""§II.6 — DÉCOMPOSITION CANONIQUE EFFECTIVE : la bijection induite b est INJECTIVE.

Module NEUF (ne modifie aucun fichier existant).  Complète la chaîne f = i∘b∘p de
`ensembles_decomposition_quotient` (où `decomposition_canonique` n'était qu'un
PRÉDICAT, la factorisation effective REPORTÉE) et de `ensembles_quotient_props` (qui
prouve l'identité de valeur f(x)=i(b(p(x))) et l'unicité de l'application déduite,
mais PAS l'injectivité de b elle-même).  Le CŒUR atteignable par le PONT
(`ensembles_application_valeur`), réclamé par la mission, est :

    « b : E/R_f → f⟨E⟩, b(Cl(x)) = f(x), est INJECTIVE »
            ⟸  b(Cl(x)) = b(Cl(y)) ⇒ f(x) = f(y) ⇒ Cl(x) = Cl(y)  (par déf. de R_f).

On code la classe Cl_{R_f}(x) par la CLASSE D'OBJETS θ_{R_f}(x) = τ_w(R_f{x,w})
(E.II.6.9), forme du quotient qui rend le « Cl(x)=Cl(y) par déf. de R_f » DIRECTEMENT
prouvable par S7 (extensionnalité du τ) — exactement le schéma de `classe_objets_unicite`.

THÉORÈMES PROUVÉS (theorie_ensembles INCHANGÉE = 22 ; rien postulé) :

  • `passage_quotient_Rf(f,e,x,y)` — CŒUR, INCONDITIONNEL :
        ⊢ ( (x∈E et y∈E) et f(x)=f(y) ) ⇒ θ_{R_f}(x) = θ_{R_f}(y).
    C.-à-d.  R_f{x,y} ⇒ Cl(x)=Cl(y)  — « par définition de R_f » : deux points de
    même image ont la même classe.  CLOS (0 hypothèse) : la symétrie et la
    transitivité de R_f, nécessaires au passage au quotient, sont DÉRIVÉES sur place
    (f(x)=f(y) est une égalité, sym/trans de = sont des théorèmes), jamais supposées.
    Preuve : (∀w)( R_f{x,w} ⇔ R_f{y,w} ) [via f(x)=f(y)] puis S7.

  • `b_injective_valeurs(f,b,e,x,y)` — INJECTIVITÉ de b au niveau des VALEURS,
    conditionnée à l'UNIQUE hypothèse de valeur du pont (b(Cl(·)) = f(·)) :
        { b(θ(x)) = f(x),  b(θ(y)) = f(y) }
            ⊢ ( (x∈E et y∈E) et b(θ(x)) = b(θ(y)) ) ⇒ θ(x) = θ(y).
    Assemble `passage_quotient_Rf` par-derrière la chaîne b(θx)=b(θy) ⇒ f(x)=f(y).

  • `b_injective_via_pont(f,b,e,u,up)` — INJECTIVITÉ de b en forme `injective_dans`
    (E.II.49), conditionnée à la relation de valeur de b sur les classes :
        { (∀x)( b(θ(x)) = f(x) ) }   [le pont : b prend la valeur f(x) en Cl(x)]
            ⊢ injective_dans( b, E/R_f )   restreinte aux classes θ(x), x∈E.

REPORTÉ (théorèmes durs, jamais postulés) : la SURJECTIVITÉ de b sur f⟨E⟩ (exige le
membership de f⟨E⟩ et de E/R_f), la construction effective du graphe de b à partir de
son axiome de membership (valeur b(θx)=f(x) prouvée DEPUIS l'axiome — exige une
caractérisation fonctionnelle de b), et la bijectivité complète.  La NOTION est
DÉFINIE (`bijection_induite` + son axiome), le CŒUR de l'injectivité est PROUVÉ, seules
ces preuves dures restent reportées.

Liants : « w » (trou de congruence/S7 et variable de classe), « x », « y ».
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, equiv,
                                       appartient, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.logique.i_1_termes_relations.formule import tau


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Liants FRAIS pour les valeurs f(·) et b(·).  `valeur(g,x)=τ_b((x,b)∈g)` a par
# défaut le liant « y » ; or les points des énoncés sont « x », « y », donc f(y)
# (resp. b(θ(y))) se capturerait (verrou liant valeur).  On fixe des liants frais,
# distincts de tous les points/binders (« x »,« y »,« w »), ce qui rend les termes
# de valeur STABLES par substitution (instancie) — pas de renommage-α surprise.
_VF = "_vf"          # liant de f(·)
_VB = "_vb"          # liant de b(·)


def _valf(vf, x):
    """f(x) = τ__vf((x,_vf)∈f)  — valeur de f en x, liant FRAIS (pas de self-capture)."""
    return E.valeur(vf, _t(x), b=_VF)


def _valb(vb, t):
    """b(t) = τ__vb((t,_vb)∈b)  — valeur de b en la classe t, liant FRAIS."""
    return E.valeur(vb, _t(t), b=_VB)


def _Rf_corps(vf, va, vw, ve):
    """R_f{a, w} = ((a∈E et w∈E) et f(a)=f(w))  (corps VERBATIM, E.II.6.2, liant w).

    Construit directement le corps (E paramétré par `ve`), pour que la classe d'objets
    θ_{R_f}(a)=τ_w(R_f{a,w}) et le passage au quotient partagent EXACTEMENT la même
    formule (mêmes E, mêmes liants).  Les valeurs f(·) ont le liant frais `_VF`."""
    return et(et(appartient(va, ve), appartient(vw, ve)),
              egal(_valf(vf, va), _valf(vf, vw)))


# ═══════════════════════════════════════════════════════════════════════════════
# 0.  La classe Cl_{R_f}(x), codée par la classe d'objets θ_{R_f}(x)  (E.II.6.9)
# ═══════════════════════════════════════════════════════════════════════════════
def classe_objets_Rf(f, x, e=None, w="w"):
    """θ_{R_f}(x) := τ_w(R_f{x,w})  (classe de x suivant R_f, forme « classe d'objets »).

    R_f{x,w} = ((x∈E et w∈E) et f(x)=f(w)) ; cette classe d'objets (E.II.6.9) code
    Cl_{R_f}(x), et son égalité par S7 donne directement le « passage au quotient ».
    Le liant est « w » (frais vis-à-vis des « x »,« y » des énoncés).  E vaut dom f par
    défaut.  f : application (terme), x : terme."""
    vf, vx, vw = _t(f), _t(x), var(w)
    ve = E.dom(vf) if e is None else _t(e)
    return tau(w, _Rf_corps(vf, vx, vw, ve))


# ═══════════════════════════════════════════════════════════════════════════════
# 1.  CŒUR : f(x)=f(y) ⇒ Cl(x)=Cl(y)   « par définition de R_f »  (INCONDITIONNEL)
# ═══════════════════════════════════════════════════════════════════════════════
def passage_quotient_Rf(f="f", e=None, x="x", y="y", w="w"):
    """⊢ ( (x∈E et y∈E) et f(x)=f(y) ) ⇒ θ_{R_f}(x) = θ_{R_f}(y).   (CLOS, E.II.6.5.)

    Le CŒUR de l'injectivité de la bijection induite b : « deux éléments x, y de E de
    même image f(x)=f(y) ont la même classe Cl_{R_f}(x)=Cl_{R_f}(y) » — c'est la
    définition même de R_f (relation d'égalité des valeurs).  L'antécédent
    « (x∈E et y∈E) et f(x)=f(y) » est exactement R_f{x,y}.

    Preuve close (0 hypothèse) : sous R_f{x,y}, on établit (∀w)(R_f{x,w} ⇔ R_f{y,w}).
      – ⇒ : de (x∈E et w∈E) et f(x)=f(w) : y∈E (donné), w∈E (gardé), f(y)=f(w) (de
            f(y)=f(x) [sym. de f(x)=f(y)] composée à f(x)=f(w)).
      – ⇐ : miroir, via f(x)=f(y) composée à f(y)=f(w).
    Puis S7 : (∀w)(R_f{x,w}⇔R_f{y,w}) ⇒ τ_w R_f{x,w} = τ_w R_f{y,w}, soit θ(x)=θ(y).
    La symétrie/transitivité de R_f ne sont PAS supposées : ce sont ici la symétrie et
    la transitivité de l'ÉGALITÉ f(·)=f(·) (théorèmes), appliquées sur place."""
    vf = _t(f)
    vx, vy, vw = var(x), var(y), var(w)
    if e is None:
        e = E.dom(vf)
    ve = _t(e)
    fx, fy, fw = _valf(vf, vx), _valf(vf, vy), _valf(vf, vw)

    # R_f{a, w} = ((a∈E et w∈E) et f(a)=f(w))   (forme verbatim partagée, liant w)
    def Rf(a):
        return _Rf_corps(vf, _t(a), vw, ve)

    # antécédent = R_f{x,y} = (x∈E et y∈E) et f(x)=f(y)
    ante = et(et(appartient(vx, ve), appartient(vy, ve)), egal(fx, fy))
    h = N.assume(ante)
    h_xE = conjonction_elim_gauche(conjonction_elim_gauche(h))   # x∈E
    h_yE = conjonction_elim_droite(conjonction_elim_gauche(h))   # y∈E
    h_fxy = conjonction_elim_droite(h)                           # f(x)=f(y)
    h_fyx = N.modus_ponens(h_fxy, symetrie(fx, fy))             # f(y)=f(x)

    # ── ⇒ : R_f{x,w} ⇒ R_f{y,w} ────────────────────────────────────────────────
    hf = N.assume(Rf(vx))                                        # (x∈E et w∈E) et f(x)=f(w)
    hf_wE = conjonction_elim_droite(conjonction_elim_gauche(hf)) # w∈E
    hf_fxw = conjonction_elim_droite(hf)                         # f(x)=f(w)
    fyw_fwd = composer_egalites(h_fyx, hf_fxw)                   # f(y)=f(x)=f(w)
    but_fwd = conjonction_intro(conjonction_intro(h_yE, hf_wE), fyw_fwd)  # R_f{y,w}
    imp_fwd = N.loi_deduction(Rf(vx), but_fwd)                   # R_f{x,w} ⇒ R_f{y,w}

    # ── ⇐ : R_f{y,w} ⇒ R_f{x,w} ────────────────────────────────────────────────
    hb = N.assume(Rf(vy))                                        # (y∈E et w∈E) et f(y)=f(w)
    hb_wE = conjonction_elim_droite(conjonction_elim_gauche(hb)) # w∈E
    hb_fyw = conjonction_elim_droite(hb)                         # f(y)=f(w)
    fxw_bwd = composer_egalites(h_fxy, hb_fyw)                   # f(x)=f(y)=f(w)
    but_bwd = conjonction_intro(conjonction_intro(h_xE, hb_wE), fxw_bwd)  # R_f{x,w}
    imp_bwd = N.loi_deduction(Rf(vy), but_bwd)                   # R_f{y,w} ⇒ R_f{x,w}

    eqv = conjonction_intro(imp_fwd, imp_bwd)                    # R_f{x,w} ⇔ R_f{y,w}
    gen = N.generalisation(w, eqv)                              # (∀w)(R_f{x,w}⇔R_f{y,w})

    # S7 : (∀w)(R_f{x,w}⇔R_f{y,w}) ⇒ τ_w R_f{x,w} = τ_w R_f{y,w}
    s7 = N.s7(Rf(vx), Rf(vy), w)
    eq_theta = N.modus_ponens(gen, s7)                          # θ(x) = θ(y)
    return N.loi_deduction(ante, eq_theta)                      # ⊢ R_f{x,y} ⇒ θ(x)=θ(y)


# ═══════════════════════════════════════════════════════════════════════════════
# 2.  INJECTIVITÉ de b au niveau des VALEURS  (via le PONT : b(Cl(x))=f(x))
# ═══════════════════════════════════════════════════════════════════════════════
def relation_valeur_b(f, b, x, e=None, w="w"):
    """b(Cl(x)) = f(x)   (relation de valeur de la bijection induite b ; E.II.6.5).

    Le PONT : la valeur de b en la classe θ_{R_f}(x) est exactement f(x).  C'est la
    propriété caractéristique de la bijection induite (b(Cl_R(x))=f(x)).  Renvoie une
    Formule.  E vaut dom f par défaut.  f, b : termes (b = graphe de la bijection induite)."""
    vf, vb = _t(f), _t(b)
    ve = E.dom(vf) if e is None else _t(e)
    return egal(_valb(vb, classe_objets_Rf(vf, x, e=ve, w=w)), _valf(vf, x))


def b_injective_valeurs(f="f", b="b", e=None, x="x", y="y", w="w"):
    """{ b(θ(x)) = f(x),  b(θ(y)) = f(y) }
       ⊢ ( (x∈E et y∈E) et b(θ(x)) = b(θ(y)) ) ⇒ θ(x) = θ(y).   (E.II.6.5.)

    INJECTIVITÉ de la bijection induite b, au niveau des valeurs et via le PONT :
    supposant la relation de valeur b(Cl(·))=f(·) (les deux instances en x, y),
    « b(Cl(x))=b(Cl(y)) entraîne Cl(x)=Cl(y) ».

    Preuve — la chaîne de la mission :
        b(θx)=b(θy)  ⟹  f(x)=f(y)   (réécriture par les deux valeurs b(θ·)=f(·))
                     ⟹  θ(x)=θ(y)   (passage_quotient_Rf, le cœur INCONDITIONNEL).
    Les hypothèses laissées dans le séquent sont UNIQUEMENT les deux relations de
    valeur du pont (jamais postulées) ; le passage au quotient lui-même est clos."""
    vf, vb = _t(f), _t(b)
    vx, vy = var(x), var(y)
    if e is None:
        e = E.dom(vf)
    ve = _t(e)
    thx = classe_objets_Rf(vf, vx, e=ve, w=w)
    thy = classe_objets_Rf(vf, vy, e=ve, w=w)
    bx, by = _valb(vb, thx), _valb(vb, thy)
    fx, fy = _valf(vf, vx), _valf(vf, vy)

    # hypothèses de valeur (le pont) : b(θx)=f(x), b(θy)=f(y)
    h_bx = N.assume(egal(bx, fx))               # b(θx) = f(x)
    h_by = N.assume(egal(by, fy))               # b(θy) = f(y)

    # antécédent : (x∈E et y∈E) et b(θx)=b(θy)
    ante = et(et(appartient(vx, ve), appartient(vy, ve)), egal(bx, by))
    h = N.assume(ante)
    h_xyE = conjonction_elim_gauche(h)          # x∈E et y∈E
    h_beq = conjonction_elim_droite(h)          # b(θx) = b(θy)

    # f(x) = b(θx) = b(θy) = f(y)
    fx_eq_bx = N.modus_ponens(h_bx, symetrie(bx, fx))   # f(x) = b(θx)
    fx_eq_by = composer_egalites(fx_eq_bx, h_beq)       # f(x) = b(θy)
    fx_eq_fy = composer_egalites(fx_eq_by, h_by)        # f(x) = f(y)

    # cœur : R_f{x,y} ⇒ θ(x)=θ(y)   (passage_quotient_Rf, CLOS)
    pq = passage_quotient_Rf(vf, ve, x, y, w)           # ((x∈E et y∈E) et f(x)=f(y)) ⇒ θx=θy
    Rf_xy = conjonction_intro(h_xyE, fx_eq_fy)          # (x∈E et y∈E) et f(x)=f(y)
    eq_theta = N.modus_ponens(Rf_xy, pq)                # θ(x) = θ(y)
    return N.loi_deduction(ante, eq_theta)
    # { b(θx)=f(x), b(θy)=f(y) } ⊢ ((x∈E et y∈E) et b(θx)=b(θy)) ⇒ θx=θy


# ═══════════════════════════════════════════════════════════════════════════════
# 3.  INJECTIVITÉ de b en forme `injective_dans`  (au niveau APPLICATION)
# ═══════════════════════════════════════════════════════════════════════════════
def pont_valeurs_b(f, b, e=None, x="x", w="w"):
    """(∀x)( x∈E ⇒ b(θ_{R_f}(x)) = f(x) )   — le PONT, forme universelle gardée.

    « b prend en chaque classe Cl(x) (x∈E) la valeur f(x) » : la relation
    caractéristique de la bijection induite, quantifiée sur la source E.  Renvoie une
    Formule (l'hypothèse explicite de `b_injective_via_pont`)."""
    vf, vb = _t(f), _t(b)
    vx = var(x)
    if e is None:
        e = E.dom(vf)
    ve = _t(e)
    return pourtout(x, impl(appartient(vx, ve),
                            egal(_valb(vb, classe_objets_Rf(vf, vx, e=ve, w=w)),
                                 _valf(vf, vx))))


def b_injective_via_pont(f="f", b="b", e=None, x="x", y="y", w="w"):
    """{ (∀a)( a∈E ⇒ b(θ(a)) = f(a) ) }
       ⊢ (∀x)(∀y)( ( (x∈E et y∈E) et b(θ(x)) = b(θ(y)) ) ⇒ θ(x) = θ(y) ).

    INJECTIVITÉ de la bijection induite b SUR les classes des points de E (forme
    universellement quantifiée de `injective_dans`, restreinte au système des classes
    θ(x), x∈E, qui constitue exactement E/R_f).  Conditionnée à l'UNIQUE hypothèse du
    PONT : b prend la valeur f(a) en chaque classe Cl(a) (pont_valeurs_b).

    On décharge, SOUS la garde x∈E et y∈E, les deux relations de valeur ponctuelles de
    `b_injective_valeurs` à partir de leur forme UNIVERSELLE (le pont), puis on
    généralise (les hypothèses restantes — le pont — sont x,y-libres).  Rien postulé."""
    vf, vb = _t(f), _t(b)
    vx, vy = var(x), var(y)
    if e is None:
        e = E.dom(vf)
    ve = _t(e)
    thx = classe_objets_Rf(vf, vx, e=ve, w=w)
    thy = classe_objets_Rf(vf, vy, e=ve, w=w)
    bx, by = _valb(vb, thx), _valb(vb, thy)
    fx, fy = _valf(vf, vx), _valf(vf, vy)

    # le lemme par point : hyps = { b(θx)=f(x), b(θy)=f(y) }
    imp = b_injective_valeurs(vf, vb, ve, x, y, w)   # ((x∈E et y∈E) et b(θx)=b(θy)) ⇒ θx=θy

    # le PONT universel, instancié en x, y
    pont = pont_valeurs_b(vf, vb, ve, x=x, w=w)      # (∀a)(a∈E ⇒ b(θa)=f(a))
    h_pont = N.assume(pont)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie
    pont_x = instancie(h_pont, vx)                   # x∈E ⇒ b(θx)=f(x)
    pont_y = instancie(h_pont, vy)                   # y∈E ⇒ b(θy)=f(y)

    # antécédent complet A = ((x∈E et y∈E) et b(θx)=b(θy)) — on en EXTRAIT x∈E, y∈E
    # (pas d'hypothèse x∈E/y∈E séparée : elles viennent de A → généralisation licite).
    A = et(et(appartient(vx, ve), appartient(vy, ve)), egal(bx, by))
    hA = N.assume(A)
    h_xE = conjonction_elim_gauche(conjonction_elim_gauche(hA))   # x∈E
    h_yE = conjonction_elim_droite(conjonction_elim_gauche(hA))   # y∈E
    val_x = N.modus_ponens(h_xE, pont_x)             # b(θx)=f(x)
    val_y = N.modus_ponens(h_yE, pont_y)             # b(θy)=f(y)

    # décharger les 2 relations de valeur de imp, fournir val_x, val_y ; appliquer à A
    imp1 = N.modus_ponens(val_y, N.loi_deduction(egal(by, fy),
            N.modus_ponens(val_x, N.loi_deduction(egal(bx, fx), imp))))  # A ⇒ θx=θy  [hyps: pont, A]
    eq_theta = N.modus_ponens(hA, imp1)              # θx=θy   [hyps: pont, A]
    final = N.loi_deduction(A, eq_theta)             # A ⇒ θx=θy   [hyps: pont]  (A déchargé)
    return N.generalisation(x, N.generalisation(y, final))


__all__ = [
    "classe_objets_Rf",
    "passage_quotient_Rf",
    "relation_valeur_b", "b_injective_valeurs",
    "pont_valeurs_b", "b_injective_via_pont",
]
