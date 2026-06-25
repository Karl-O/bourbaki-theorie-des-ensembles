"""Chapitre III §1.10 — PROPOSITION 10 (E.III.1.10) : dans un ensemble ordonné
FILTRANT À DROITE, tout élément MAXIMAL est le PLUS GRAND élément.

Convention « graphe G » de `ensembles_ordre_relation.py` : x≤y := (x,y)∈G.  Un
ensemble E est filtrant à droite (E.III.1.10, Déf. 7) lorsque deux éléments
quelconques admettent un majorant commun :

    filtrant_droite_G(G,E) := est_filtrant_droite(λu,v.(u,v)∈G, E)
        = (∀x)(∀y)((x∈E et y∈E) ⇒ (∃z)(z∈E et (x,z)∈G et (y,z)∈G)).

THÉORÈME (forme « ensemble », CLOS) — `maximal_filtrant_est_plus_grand` :

  { est_ordre(G,E),  filtrant_droite_G(G,E),  element_maximal(G,E,a) }
        ⊢ plus_grand_element(G,E,a).

  « Soit E un ensemble ordonné filtrant à droite, et a un élément maximal de E.
  Alors a est le plus grand élément de E. »

  PREUVE (order-théorique, rapide).  Soit x∈E.  Comme E est filtrant à droite,
  x et a admettent un majorant commun z∈E : (x,z)∈G et (a,z)∈G.  Mais a est
  maximal et (a,z)∈G avec z∈E, donc z=a.  Transportant (x,z)∈G par z=a (Leibniz
  S6, 2e coordonnée) on obtient (x,a)∈G.  Ainsi a majore tout x∈E, et comme a∈E
  (maximalité), a est le plus grand élément de E.

  Le rôle de `est_ordre(G,E)` : sa RÉFLEXIVITÉ fournit (a,a)∈G, valeur du corps
  « plus grand » au point a lui-même — étape transportée par Leibniz, exactement
  comme dans le patron `maximal_est_plus_grand_si_total` (E.III.1.12).

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ (primitives N.* du noyau LCF),
aucun axiome nouveau.  (E.III.1.10, Proposition 10.)
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, existe,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, element_maximal, plus_grand_element, _couple_dans,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# liants internes FIXÉS (évitent toute capture du point courant x) ──────────────
_ZPG = "zpg10"   # liant de plus_grand_element ici
_XFD, _YFD, _ZFD = "xfd10", "yfd10", "zfd10"   # liants du filtrant ici


def _pge(G, A, m):
    """plus_grand_element(G,A,m) avec liant interne FIXÉ à _ZPG."""
    return plus_grand_element(G, _t(A), _t(m), x=_ZPG)


def _filtrant_droite_G(G, E_set):
    """filtrant_droite_G(G,E) := est_filtrant_droite(λu,v.(u,v)∈G, E).

    Réutilise le helper `_filtrant_droite_G` de §III.4 (même encodage) : la
    relation de graphe R(u,v):=(u,v)∈G filtrée à droite sur E.  (E.III.1.10.)"""
    R = lambda u, v: _couple_dans(u, v, G)
    return E.est_filtrant_droite(R, _t(E_set), _XFD, _YFD, _ZFD)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 10 (E.III.1.10) — maximal + filtrant à droite ⇒ plus grand
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.10 Prop.10 | E III.13 L.6-9 | PDF p.116
def maximal_filtrant_est_plus_grand(G="Gmf", E_set="Emf", a="amf",
                                     x="xmf", y="ymf", z="zmf"):
    """🎯 { est_ordre(G,E), filtrant_droite_G(G,E), element_maximal(G,E,a) }
            ⊢ plus_grand_element(G,E,a).

    PROPOSITION 10 : dans un ensemble ordonné FILTRANT À DROITE, tout élément
    MAXIMAL a est le PLUS GRAND élément.  Pour x∈E, le filtrant donne un majorant
    commun z de x et a (z∈E, (x,z)∈G, (a,z)∈G) ; la maximalité de a appliquée à
    z (avec (a,z)∈G) force z=a ; on transporte (x,z)∈G en (x,a)∈G (Leibniz S6,
    z=a).  Donc a majore E, et a∈E (maximalité) : a est le plus grand.  (E.III.1.10.)
    """
    vG, vE, va = _t(G), _t(E_set), _t(a)
    vx = var(x)

    # ── les TROIS hypothèses HONNÊTES ─────────────────────────────────────────
    Hord = N.assume(est_ordre(G, E_set, x, y, z))         # (refl_E et antisym) et trans
    Hfilt = N.assume(_filtrant_droite_G(G, E_set))         # filtrant à droite
    Hmax = N.assume(element_maximal(G, E_set, va, _ZPG))   # a∈E et (∀t)((t∈E et (a,t)∈G)⇒t=a)

    # ── extraction des prédicats ──────────────────────────────────────────────
    a_in_E = conjonction_elim_gauche(Hmax)                # a∈E
    max_body = conjonction_elim_droite(Hmax)              # (∀t)((t∈E et (a,t)∈G)⇒t=a)
    # est_ordre = (reflexivite_sur et antisymetrie) et transitivite ; on en tire
    # la RÉFLEXIVITÉ et la TRANSITIVITÉ (toutes deux load-bearing ci-dessous).
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # (∀t)(t∈E⇒(t,t)∈G)
    trans = conjonction_elim_droite(Hord)                 # (∀u∀v∀w)(((u,v)∈G et (v,w)∈G)⇒(u,w)∈G)
    aa_G = N.modus_ponens(a_in_E, instancie(refl_E, va))  # (a,a)∈G   (réflexivité au point a)

    # ── corps du « plus grand » : x∈E ⇒ (x,a)∈G ───────────────────────────────
    Hx = N.assume(appartient(vx, vE))                      # x∈E
    # filtrant en (x,a) : (x∈E et a∈E) ⇒ (∃z)(z∈E et (x,z)∈G et (a,z)∈G)
    filt_xa = instancie(instancie(Hfilt, vx), va)
    ex_z = N.modus_ponens(conjonction_intro(Hx, a_in_E), filt_xa)     # (∃z)(...)

    # sous le témoin z=_ZFD : extraire (x,z)∈G, (a,z)∈G, z∈E ; maximalité ⇒ z=a
    vz = var(_ZFD)
    Hz = N.assume(et(et(appartient(vz, vE), _couple_dans(vx, vz, G)),
                     _couple_dans(va, vz, G)))
    z_in_E = conjonction_elim_gauche(conjonction_elim_gauche(Hz))     # z∈E
    xz_G = conjonction_elim_droite(conjonction_elim_gauche(Hz))       # (x,z)∈G
    az_G = conjonction_elim_droite(Hz)                                # (a,z)∈G
    # maximalité en z : (z∈E et (a,z)∈G) ⇒ z=a
    max_z = instancie(max_body, vz)
    z_eq_a = N.modus_ponens(conjonction_intro(z_in_E, az_G), max_z)   # z=a
    a_eq_z = N.modus_ponens(z_eq_a, symetrie(vz, va))     # a=z

    # (z,a)∈G : transport de la RÉFLEXIVITÉ (a,a)∈G par a=z sur la 1re coordonnée
    # (Leibniz S6, trou « w » en position gauche).  C'est ici que (a,a)∈G — donc
    # est_ordre — devient load-bearing (patron `maximal_est_plus_grand_si_total`).
    phi_g = _couple_dans(var("wmf"), va, G)               # Φ(w) = (w,a)∈G
    leib_g = N.s6(va, vz, "wmf", phi_g)                   # (a=z)⇒((a,a)∈G ⇔ (z,a)∈G)
    za_G = N.modus_ponens(aa_G, equivalence_avant(N.modus_ponens(a_eq_z, leib_g)))   # (z,a)∈G

    # (x,a)∈G par TRANSITIVITÉ en (x,z,a) : ((x,z)∈G et (z,a)∈G) ⇒ (x,a)∈G
    trans_xza = instancie(instancie(instancie(trans, vx), vz), va)
    xa_G = N.modus_ponens(conjonction_intro(xz_G, za_G), trans_xza)   # (x,a)∈G   (sous témoin z)

    # décharge du témoin z : (z∈E et (x,z)∈G et (a,z)∈G) ⇒ (x,a)∈G  puis (∃z)(...) ⇒ (x,a)∈G
    imp_z = N.loi_deduction(et(et(appartient(vz, vE), _couple_dans(vx, vz, G)),
                               _couple_dans(va, vz, G)), xa_G)
    xa_from_ex = N.modus_ponens(ex_z, existe_elimination(imp_z, _ZFD))   # (x,a)∈G   (sous x∈E)

    # généralise en x : (∀zpg)(zpg∈E ⇒ (zpg,a)∈G)  (corps du plus grand élément)
    body = N.loi_deduction(appartient(vx, vE), xa_from_ex)              # x∈E ⇒ (x,a)∈G
    maj_a = N.generalisation(_ZPG, _alpha_corps(body, x))

    res = conjonction_intro(a_in_E, maj_a)                # plus_grand_element(G,E,a)
    assert res.conclusion == _cible(G, E_set, a), "conclusion ≠ cible plus_grand_element"
    return res


def _alpha_corps(body_thm, x):
    """Renomme le liant du corps « x∈E ⇒ (x,a)∈G » de x vers _ZPG via S5/généralisation.

    Le corps est prouvé avec la lettre `x` ; le prédicat `plus_grand_element`
    quantifie sous le liant `_ZPG`.  On REPROUVE le corps littéralement sous `_ZPG`
    en renommant la variable libre, sans hypothèse résiduelle (généralisation +
    instanciation).  Ici `x` n'est libre dans aucune hypothèse honnête, donc la
    généralisation puis l'instanciation en var(_ZPG) sont licites."""
    g = N.generalisation(x, body_thm)            # (∀x)(x∈E ⇒ (x,a)∈G)
    return instancie(g, var(_ZPG))               # (zpg∈E ⇒ (zpg,a)∈G)  [forme attendue]


# cible : plus_grand_element(G,E,a)  sous { est_ordre(G,E),
#         filtrant_droite_G(G,E), element_maximal(G,E,a) }
def _cible(G="Gmf", E_set="Emf", a="amf"):
    """Conclusion attendue de `maximal_filtrant_est_plus_grand` : plus_grand_element(G,E,a)."""
    return _pge(G, E_set, _t(a))


__all__ = ["maximal_filtrant_est_plus_grand"]
