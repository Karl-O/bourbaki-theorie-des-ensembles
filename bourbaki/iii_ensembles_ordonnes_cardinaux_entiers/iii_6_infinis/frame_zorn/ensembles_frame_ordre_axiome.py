"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : AXIOME DÉFINITIONNEL du
GRAPHE D'ORDRE Γ𝔉(E) de l'EXTENSION sur le poset 𝔉 des couples-bijections.

CONTEXTE.  `frame_ordre(E)` (`ensembles_hessenberg_hard.py`) est le terme OPAQUE
`E.app("hessenberg_frame_ordre", E)` SANS axiome — c'était l'OBSTRUCTION B de
`frame_inductif_chaine` : (x,m)∈Γ𝔉 n'était PAS établissable, donc la moitié
« ordre » du majorant de chaîne restait hors d'atteinte.

Ce module fournit l'`axiome_frame_ordre` MANQUANT, calqué EXACTEMENT sur
`axiome_frame` (motif de SÉLECTION S8+A1, en théorie DÉDIÉE) :

    (p,q) ∈ Γ𝔉(E)  ⟺  ( p∈𝔉(E) et q∈𝔉(E) et pr₁(p)⊂pr₁(q) et pr₂(p)⊂pr₂(q) )

c.-à-d. l'ordre d'extension de Bourbaki « X⊂X' et ψ' prolonge ψ » porté au niveau
des couples p=(S_p,φ_p), q=(S_q,φ_q) : S_p⊂S_q (pr₁) et φ_p⊂φ_q (pr₂).

  • `axiome_frame_ordre`  : le ⊢-schéma (∀E p q)( (p,q)∈Γ𝔉 ⇔ <corps> ).
  • `theorie_frame_ordre` : théorie DÉDIÉE ne contenant QUE cet axiome (motif
                            `theorie_frame`).  theorie_ensembles() reste = 22.
  • `frame_ordre_membre`  : l'axiome INSTANCIÉ (motif `frame_membre`)
                            ⊢ ( (p,q)∈Γ𝔉(E) ) ⇔ <corps>.

Avec lui, la moitié « ordre » du majorant ((S_i,φ_i)≤(⋃S,⋃φ)) devient
ÉTABLISSABLE dès qu'on a S_i⊂⋃S et φ_i⊂⋃φ (inclusions de membre à réunion).
Obstruction B RÉSOLUE au niveau définitionnel.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome dans theorie_ensembles ;
le nouvel axiome vit dans `theorie_frame_ordre` (dédiée).  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, pourtout, appartient, equiv, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  CORPS de Γ𝔉 :  ordre d'extension sur les couples p,q ∈ 𝔉(E).
# ════════════════════════════════════════════════════════════════════════════
def _corps_frame_ordre(E_set, p, q):
    """Corps de Γ𝔉 :
        ( p∈𝔉(E) et q∈𝔉(E) et pr₁(p)⊂pr₁(q) et pr₂(p)⊂pr₂(q) ).

    L'ordre d'extension de Bourbaki (E.III.48, « X⊂X' et ψ' prolonge ψ ») porté
    au niveau des couples : S_p=pr₁(p)⊂pr₁(q)=S_q et φ_p=pr₂(p)⊂pr₂(q)=φ_q."""
    vE, vp, vq = _t(E_set), _t(p), _t(q)
    Fr = frame_pair(vE)
    return et(et(et(appartient(vp, Fr), appartient(vq, Fr)),
                 inclus(E.pr1(vp), E.pr1(vq))),
              inclus(E.pr2(vp), E.pr2(vq)))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-23 | PDF p.151  (« X ⊂ X′ et ψ′ est un prolongement de ψ » : axiome définitionnel de l'ordre Γ𝔐)
def axiome_frame_ordre(E_set="E", p="p", q="q"):
    """⊢-schéma (∀E p q)( (p,q)∈Γ𝔉(E) ⇔ corps_frame_ordre ).

    Axiome DÉFINITIONNEL du graphe d'ordre Γ𝔉 (sélection S8+A1, motif
    `axiome_frame`).  N'altère PAS theorie_ensembles()."""
    vE, vp, vq = var(E_set), var(p), var(q)
    return pourtout(E_set, pourtout(p, pourtout(q,
        equiv(appartient(E.couple(vp, vq), frame_ordre(vE)),
              _corps_frame_ordre(vE, vp, vq)))))


def theorie_frame_ordre(E_set="E", p="p", q="q"):
    """Théorie DÉDIÉE ne contenant QUE l'axiome de Γ𝔉 (E.III.6, Hessenberg, Zorn).

    Motif `theorie_frame` : un axiome définitionnel isolé, HORS theorie_ensembles."""
    return N.Theorie("Frame-Ordre-Hessenberg",
                     [axiome_frame_ordre(E_set, p, q)])


# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-23 | PDF p.151  (caractérisation instanciée de (p,q)∈Γ𝔐)
def frame_ordre_membre(E_set="E", p="p", q="q"):
    """⊢ ( (p,q)∈Γ𝔉(E) ) ⇔ corps_frame_ordre(E,p,q).   (axiome instancié.)

    Motif `frame_membre` : l'axiome généralisé instancié en E, p, q."""
    ax = N.axiome(theorie_frame_ordre(), axiome_frame_ordre())
    return instancie(instancie(instancie(ax, var(E_set)), var(p)), var(q))


def frame_ordre_membre_t(vE, vp, vq):
    """Version TERME capture-safe de `frame_ordre_membre` (instanciation aux
    TERMES vE, vp, vq plutôt qu'aux variables homonymes)."""
    ax = N.axiome(theorie_frame_ordre(), axiome_frame_ordre())
    return instancie(instancie(instancie(ax, _t(vE)), _t(vp)), _t(vq))


__all__ = [
    "axiome_frame_ordre",
    "theorie_frame_ordre",
    "frame_ordre_membre",
    "frame_ordre_membre_t",
]
