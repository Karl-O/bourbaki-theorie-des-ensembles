# -*- coding: utf-8 -*-
"""§III.2.2 — R1' : le prédicat d'ESSAI RÉCURSIF (l'équation lit la restriction).

🎯 DÉFINITIONS (formules, aucun théorème ici) :

    est_essai_rec(p, T, R, E, x) :=
        est_fonctionnel(p)
        ∧ dom(p) = seg(R,E,x) ∪ {x}
        ∧ (∀z)( z ∈ dom(p) ⇒ valeur(p, z) = T{ p|seg(R,E,z) } )

    couvert_essai_rec(x) := (∃p)( est_essai_rec(p, x) )

C'est le prédicat d'essai de C60 (E III.18) avec la VRAIE équation de
récursion : la règle T (callable Terme→Terme) reçoit la RESTRICTION de p au
segment ouvert en z — et non le point z (la forme déposée, une tabulation).
Bourbaki : « p(j) = T{p|seg(j)} sur tout le domaine ».

LIEUR « zesr » (frais) : la règle T peut lier en interne u/v/y/z (règles à
τ-cardinaux) — quantifier sur un nom que T lie capturerait la variable à la
construction (leçon des liants exotiques zfgl/fglb du capstone C62).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome, aucun théorème.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def restriction_seg(p, G, e, z):
    """p|seg(R,E,z) — la restriction de l'essai au segment OUVERT en z."""
    return E.restriction(_t(p), E.segment_extremite(_t(G), _t(e), _t(z)))


def est_essai_rec(p, vh, G, e, x, z="zesr"):
    """Prédicat « p est un ESSAI RÉCURSIF en x » (équation-restriction).

    p : Terme (le graphe-essai) ; vh : Terme→Terme (la règle, qui reçoit la
    RESTRICTION p|seg(R,E,z)) ; R = l'ordre porté par le graphe G ; E l'ensemble
    bien ordonné ; x le point.  L'équation vaut sur TOUT le domaine de p."""
    vp = _t(p)
    vz = var(z)
    eq = pourtout(z, impl(
        appartient(vz, E.dom(vp)),
        egal(E.valeur(vp, vz), vh(restriction_seg(vp, G, e, vz)))))
    return et(et(E.est_fonctionnel(vp), egal(E.dom(vp), dom_essai(G, e, x))), eq)


def couvert_essai_rec(vh, G, e, p="pesr", z="zesr"):
    """Prédicat de couverture  couvert_rec(x) := (∃p)( est_essai_rec(p, x) )."""
    return lambda x: existe(p, est_essai_rec(var(p), vh, G, e, x, z))


__all__ = ["restriction_seg", "est_essai_rec", "couvert_essai_rec"]
