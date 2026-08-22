# -*- coding: utf-8 -*-
"""§III.2.2 — R5'b : LA FAMILLE S8 DES ESSAIS RÉCURSIFS.

🎯 DÉFINITION (sélection S8 dans l'existant 𝔓(E×V), motif Dfam_real/Ncol) :

    Dfam_rec(G,E,x,V) := { p ∈ 𝔓(E×V) | (∃y)( y∈seg(G,E,x) ∧ est_essai_rec(p,y) ) }

La famille des essais RÉCURSIFS des points y < x.  Sa réunion ⋃Dfam_rec(x)
sera l'essai-sur-seg du recollement (R5'c) : domaine seg(x) (chaque z<x est
dans le dom_essai de son propre essai — sous l'antécédent d'induction), valeurs
cohérentes (coincidence_essais_rec, R5'a), équation héritée des membres.

LÉGALITÉ S8 : le sélecteur (« p est un essai récursif d'un y<x ») ne mentionne
JAMAIS le terme défini rec_Dfam — aucune auto-référence, sélection dans un
contenant EXISTANT (A3 + produit).  Théorie DÉDIÉE : theorie_ensembles()
reste à 22.

⚠️ AMÉLIORATION sur le patron c60 (leçon de la migration seg_ext) : le terme
rec_Dfam PORTE LE GRAPHE G — deux ordres distincts donnent des termes
DISTINCTS, donc jamais deux axiomes incompatibles sur un même terme.  La règle
vh (callable Python, méta-paramètre) reste capturée dans l'axiome : deux
règles distinctes partagent le terme — LIMITE DOCUMENTÉE, ne jamais mélanger
dans une même preuve des théorèmes issus de theorie_Dfam_rec de deux vh
différents (même discipline que Dfam_real, où G ET vh étaient capturés).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, et, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def Dfam_rec(G, e, x, V="Vval"):
    """Le TERME de la famille { p∈𝔓(E×V) | (∃y∈seg(G,E,x)) est_essai_rec(p,y) }.

    Porte G, E, x, V (G inclus — leçon seg_ext) ; vh est capturée par l'axiome."""
    return app("rec_Dfam", _t(G), _t(e), _t(x), _t(V))


def _corps_Dfam_rec(vh, G, e, x, p, V="Vval", y="yDr"):
    """Le corps en p :  p∈𝔓(E×V)  ∧  (∃y)( y∈seg(G,E,x) ∧ est_essai_rec(p,y) )."""
    vp, vy = _t(p), var(y)
    seg = E.segment_extremite(_t(G), _t(e), _t(x))
    amb = appartient(vp, ambiant(e, V))
    sel = existe(y, et(appartient(vy, seg), est_essai_rec(vp, vh, _t(G), _t(e), vy)))
    return et(amb, sel)


def axiome_Dfam_rec(vh, G="Gsr", e="Esr", x="xsr", V="Vval", p="pDr", y="yDr"):
    """Schéma définitionnel S8 :
    (∀x)(∀p)( p∈Dfam_rec(G,E,x,V) ⇔ ( p∈𝔓(E×V) ∧ (∃y∈seg)( est_essai_rec(p,y) ) ) )."""
    vx, vp = var(x), var(p)
    return pourtout(x, pourtout(p,
        equiv(appartient(vp, Dfam_rec(G, e, vx, V)),
              _corps_Dfam_rec(vh, G, e, vx, vp, V, y))))


def theorie_Dfam_rec(vh, G="Gsr", e="Esr", x="xsr", V="Vval", p="pDr", y="yDr"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Dfam_rec (S8, R5'b).

    JAMAIS dans theorie_ensembles() (=22) — même schéma que Dfam_real/Ncol."""
    return N.Theorie("Dfam-rec-R5", [axiome_Dfam_rec(vh, G, e, x, V, p, y)])


def membre_Dfam_rec(vh, G="Gsr", e="Esr", x="xsr", p="pDr", V="Vval", y="yDr"):
    """⊢ ( p∈Dfam_rec(x) ) ⇔ ( p∈𝔓(E×V) ∧ (∃y∈seg(G,E,x))( est_essai_rec(p,y) ) ).

    L'axiome instancié en (x, p) — x et p acceptent noms OU termes."""
    ax = N.axiome(theorie_Dfam_rec(vh, G, e, V=V, p=p, y=y),
                  axiome_Dfam_rec(vh, G, e, V=V, p=p, y=y))
    return instancie(instancie(ax, _t(x)), _t(p))


__all__ = ["Dfam_rec", "axiome_Dfam_rec", "theorie_Dfam_rec", "membre_Dfam_rec"]
