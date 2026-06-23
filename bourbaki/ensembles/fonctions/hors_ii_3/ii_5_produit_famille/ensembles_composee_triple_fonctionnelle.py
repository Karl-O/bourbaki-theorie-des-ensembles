"""§II.5 Prop 2 (cœur) — Fonctionnalité de la composée de TROIS fonctions.

Bourbaki §II.5 Prop 2 (E.II.31) : si u : A→A', v : B→B' sont des applications, alors
g ↦ v∘g∘u est une application de 𝓕(A';B) dans 𝓕(A;B').  Le verrou de bien-définition
(« v∘g∘u EST bien une application ») se ramène à : la composée de trois graphes
FONCTIONNELS est fonctionnelle.

Ce module CLÔT ce cœur :

    ⊢ ( F fonctionnel et G fonctionnel et H fonctionnel ) ⇒ ( (H∘(G∘F)) fonctionnel ).

INCONDITIONNEL (0 hyp), par double application de la Proposition 6 §II.3.7
(`composee_fonctionnelle`, déjà close 0-hyp).  Capture-safe : `composee_fonctionnelle`
est généralisée sur ses deux variables de graphe (G,F) puis ré-instanciée aux TERMES
composés — motif `_prop1_direct_t` de la mémoire projet (les témoins-graphes internes
u,v,z,y,yp de la Prop 6 ne capturent donc pas les arguments composés).

Noyau INCHANGÉ (theorie = 22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, et, Terme
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_fonctionnelle


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _composee_fonctionnelle_t(tG, tF):
    """⊢ ( F fonctionnel et G fonctionnel ) ⇒ ( (G∘F) fonctionnel ), instancié aux TERMES tG, tF.

    Version capture-safe de `composee_fonctionnelle` : on généralise la Prop 6 sur ses
    deux variables de graphe « G » et « F » (libres dans aucune hypothèse — le théorème
    est clos), puis on instancie aux termes voulus.  Sûr même quand tG/tF sont composés."""
    base = composee_fonctionnelle("G", "F")                 # clos, 0 hyp
    gen = N.generalisation("G", N.generalisation("F", base))
    return instancie(instancie(gen, tG), tF)               # ordre : G d'abord (extérieur), puis F


def composee_triple_fonctionnelle(f="F", g="G", h="H"):
    """⊢ ( F fonctionnel et G fonctionnel et H fonctionnel ) ⇒ ( (H∘(G∘F)) fonctionnel ).

    Cœur de bien-définition de §II.5 Prop 2 (E.II.31) : v∘g∘u est une application.
    INCONDITIONNEL (0 hyp)."""
    vF, vG, vH = _t(f), _t(g), _t(h)
    GF = E.composee(vG, vF)                                # G∘F

    hyp = et(E.est_fonctionnel(vF),
             et(E.est_fonctionnel(vG), E.est_fonctionnel(vH)))
    H = N.assume(hyp)
    hF = conjonction_elim_gauche(H)                        # F fonctionnel
    hGH = conjonction_elim_droite(H)
    hG = conjonction_elim_gauche(hGH)                      # G fonctionnel
    hH = conjonction_elim_droite(hGH)                      # H fonctionnel

    # 1) G∘F fonctionnel  (Prop 6 sur F,G)
    gf_func = N.modus_ponens(conjonction_intro(hF, hG),
                             _composee_fonctionnelle_t(vG, vF))
    # 2) H∘(G∘F) fonctionnel  (Prop 6 sur (G∘F), H)
    hgf_func = N.modus_ponens(conjonction_intro(gf_func, hH),
                              _composee_fonctionnelle_t(vH, GF))

    return N.loi_deduction(hyp, hgf_func)


def composee_triple_fonctionnelle_cible(f="F", g="G", h="H"):
    """L'énoncé visé, reproductible : ( F func et G func et H func ) ⇒ ( (H∘(G∘F)) func )."""
    vF, vG, vH = _t(f), _t(g), _t(h)
    GF = E.composee(vG, vF)
    HGF = E.composee(vH, GF)
    hyp = et(E.est_fonctionnel(vF),
             et(E.est_fonctionnel(vG), E.est_fonctionnel(vH)))
    from bourbaki.logique.formule import impl
    return impl(hyp, E.est_fonctionnel(HGF))


__all__ = ["composee_triple_fonctionnelle", "composee_triple_fonctionnelle_cible"]
