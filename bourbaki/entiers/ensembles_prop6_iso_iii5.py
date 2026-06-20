"""§III.5 — PROPOSITION 6 (E III.38) : iso d'ordre de E sur l'intervalle.

🎯 ÉNONCÉ Bourbaki (E III.38, Prop. 6) :
    « Pour tout ensemble fini E, totalement ordonné, ayant n éléments (n ≥ 1),
      il existe un isomorphisme et un seul de E sur l'intervalle [1,n]. »
    PREUVE Bourbaki : « Comme E et [1,n] sont bien ordonnés (III, p.34, cor.1),
    et ont même nombre d'éléments (prop.5), la proposition résulte de
    III, p.21, th.3 et p.31, cor.2. »

C'est EXACTEMENT cette route qu'on assemble ici : Théorème 3 §III.2 (trichotomie
des ordinaux) + Proposition 1 §III.3 (Card égaux ⇔ équipotents).

────────────────────────────────────────────────────────────────────────────────
INGRÉDIENTS PRÊTS (assemblés) :

  • THÉORÈME 3 §III.2  — `trichotomie_ordinaux_canon_close_v3()` (CLOS, 0 résidu de
    preuve, sous EXACTEMENT { bo(R,E), bo(Rp,F) }) :
        { est_bien_ordonne(R,E), est_bien_ordonne(Rp,F) }
          ⊢ ( ordinal_inf_canon(E,R,F,Rp)  OU  ordinal_inf_canon(F,Rp,E,R) ),
    c.-à-d. « E iso à un SEGMENT de F, OU F iso à un SEGMENT de E ».

  • PROPOSITION 1 §III.3 (sens réciproque) — `equipotent_si_cardinal_egal(E,F)`
    (CLOS, 0 hyp) :  ( Card E = Card F ) ⇒ equipotent(E, F).

────────────────────────────────────────────────────────────────────────────────
⚠️ NOTE D'HONNÊTETÉ — LE RÉSIDU SUBSTANTIEL (jamais postulé, rapporté EXPLICITEMENT).

Le Théorème 3 livre la DISJONCTION « segment-réalisation » :
    ordinal_inf_canon(E,R,F,Rp)  OU  ordinal_inf_canon(F,Rp,E,R).
Pour CONCLURE un iso PLEIN E ≅ F (= `sont_isomorphes_ordre_canon(E,F,R,Rp)`), il faut
RÉSOUDRE la disjonction : montrer que, E et F étant ÉQUIPOTENTS et FINIS, le segment
réalisé est l'ensemble TOUT entier (un segment PROPRE d'un fini bien ordonné a un
cardinal STRICTEMENT plus petit — E.III.4, donc ne peut être équipotent au tout).
Ce pas — « segment équipotent au tout d'un fini ⇒ segment = tout » — est un CONTENU
COMBINATOIRE §III.4-5 qui n'est PAS encore prouvé dans le dépôt.  Il est donc PRIS
EN HYPOTHÈSE EXPLICITE, sous sa forme la plus fidèle :

    resolution_trichotomie(E,R,F,Rp) :=
        ( equipotent(E,F)  ET  trichotomie_ordinaux_canon(E,R,F,Rp) )
          ⇒  sont_isomorphes_ordre_canon(E,F,R,Rp).

La conclusion `sont_isomorphes_ordre_canon(E,F,R,Rp)` n'est AUCUNE hypothèse du
séquent (NON vacueux).  Th 3 et Prop 1 sont, eux, du MACHINISME RÉEL et CLOS.

theorie=22, rien postulé.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro, instancie
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
from bourbaki.ordre.ensembles_iso_ordre_canon import (
    sont_isomorphes_ordre_canon, trichotomie_ordinaux_canon,
)
from bourbaki.cardinaux import ensembles_h_est_graphe as HG


# Noms ambiants CANONIQUES exigés par Th 3 (close_v3) : E, F, R, Rp.
_E, _F, _R, _Rp = "E", "F", "R", "Rp"


def _trich():
    """Th 3 §III.2 CLOS sous { bo(R,E), bo(Rp,F) } : la disjonction segment."""
    return HG.trichotomie_ordinaux_canon_close_v3(_E, _R, _F, _Rp)


def _R_de(R):
    # close_v3 utilise la relation-graphe R_de(var(R)) ; on reproduit sa forme
    from bourbaki.ordre.ensembles_zermelo import R_de
    return R_de(var(R))


def _pieces():
    """Construit, en UNE SOURCE DE VÉRITÉ, les théorèmes-machinerie + le résidu :
       • eq_EF   : ⊢ equipotent(E,F)            (sous [Card E = Card F], Prop 1)
       • trich   : ⊢ trichotomie_…(E,R,F,Rp)    (sous {bo,bo}, Th 3 close_v3)
       • residu  : ( eq_EF.concl ET trich.concl ) ⇒ sont_isomorphes_ordre_canon(E,F,R,Rp)
                   bâti à partir des CONCLUSIONS EXACTES (α-renommage inclus) pour que
                   le modus ponens final s'apparie STRUCTURELLEMENT."""
    vE, vF = var(_E), var(_F)
    Rf, Rpf = _R_de(_R), _R_de(_Rp)
    # Th 3 §III.2 (CLOS sous {bo,bo}).
    trich = _trich()
    # Prop 1 §III.3 : (Card E=Card F) ⇒ equipotent(E,F) (généralise-instancie aux termes).
    prop1g = N.generalisation("X", N.generalisation("Y",
                              equipotent_si_cardinal_egal("X", "Y")))
    prop1 = instancie(instancie(prop1g, vE), vF)
    ante_card = prop1.conclusion.sous[0].sous[0]                  # = (Card E = Card F)
    hcard = N.assume(ante_card)
    eq_EF = N.modus_ponens(hcard, prop1)                         # ⊢ equipotent(E,F)
    # Résidu honnête bâti des conclusions EXACTES.
    premisse = et(eq_EF.conclusion, trich.conclusion)
    conclu = sont_isomorphes_ordre_canon(vE, vF, Rf, Rpf)
    residu = impl(premisse, conclu)
    return eq_EF, trich, ante_card, residu


def resolution_trichotomie_enonce():
    """RÉSIDU HONNÊTE (forme exacte) :
        ( equipotent(E,F) ET trichotomie_ordinaux_canon(E,R,F,Rp) )
          ⇒ sont_isomorphes_ordre_canon(E,F,R,Rp).
    « Pour des FINIS équipotents, la disjonction segment se résout en iso PLEIN. »
    Contenu combinatoire §III.4-5 (segment propre d'un fini : cardinal strict)."""
    return _pieces()[3]


def prop6_iso_existe():
    """🎯 PROPOSITION 6 §III.5 — iso existence, route Bourbaki Th3 + Prop1.

    ⊢  { est_bien_ordonne(R,E),  est_bien_ordonne(Rp,F),
          Card E = Card F,
          resolution_trichotomie(E,R,F,Rp) }
        ⊢  sont_isomorphes_ordre_canon(E, F, R, Rp)      [= (∃f) iso d'ordre E ≅ F].

    ASSEMBLAGE :
      1. Th 3 §III.2 (close_v3) : {bo,bo} ⊢ trichotomie_ordinaux_canon(E,R,F,Rp).
      2. Prop 1 §III.3 : (Card E = Card F) ⇒ equipotent(E,F)  [CLOS, modus ponens].
      3. equipotent ET trichotomie ⊢ premisse du résidu ; modus ponens avec le
         résidu honnête ⊢ sont_isomorphes_ordre_canon(E,F,R,Rp).

    Th 3 (étape 1) et Prop 1 (étape 2) sont du MACHINISME CLOS.  Le SEUL report est le
    résidu de résolution (étape 3), pris en hypothèse EXPLICITE.  La conclusion n'est
    AUCUNE hypothèse (NON vacueux).  theorie=22, rien postulé."""
    eq_EF, trich, _ante, residu = _pieces()
    premisse = conjonction_intro(eq_EF, trich)                   # ⊢ Eq ET trich
    hres = N.assume(residu)                                       # [résidu honnête]
    iso = N.modus_ponens(premisse, hres)                         # ⊢ sont_isomorphes_ordre_canon
    return iso


def prop6_iso_existe_cible():
    """ÉNONCÉ-cible (test miroir) : sont_isomorphes_ordre_canon(E,F,R,Rp)."""
    vE, vF = var(_E), var(_F)
    Rf, Rpf = _R_de(_R), _R_de(_Rp)
    return sont_isomorphes_ordre_canon(vE, vF, Rf, Rpf)


def prop6_iso_existe_hypotheses():
    """Les 4 HYPOTHÈSES HONNÊTES SURVIVANTES (documentation / test miroir) :
       { bo(R,E), bo(Rp,F), Card E = Card F, resolution_trichotomie(E,R,F,Rp) }."""
    bo_hyps = list(HG.trichotomie_ordinaux_canon_close_v3_hypotheses(_E, _R, _F, _Rp))
    _eq, _trich, ante_card, residu = _pieces()
    return bo_hyps + [ante_card, residu]


__all__ = [
    "resolution_trichotomie_enonce",
    "prop6_iso_existe", "prop6_iso_existe_cible", "prop6_iso_existe_hypotheses",
]
