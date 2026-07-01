"""Résumé §7 item 1 — Eq(E,F) ⇒ Eq(𝔓(E), 𝔓(F))  (EN CONSTRUCTION).

« Si E et F sont équipotents, 𝔓(E) et 𝔓(F) sont équipotents » (E.R.32 item 1).
Stratégie : d'une bijection f : E → F, l'application A ↦ f⟨A⟩ est une bijection de
𝔓(E) sur 𝔓(F).  On la CONSTRUIT comme graphe-terme
    H := graphe_terme(𝔓(E), f⟨Y⟩, 'Y')     (donc H(Y) = image(f, Y) sur 𝔓(E))
et on prouve est_bijection_de(H, 𝔓E, 𝔓F) par les quatre piliers (fonctionnel, domaine,
injectif, image), puis Eq(𝔓E,𝔓F) par ∃-introduction du témoin H et élimination du
témoin f de Eq(E,F).

ÉTAT (2026-07-01) : FONDATION posée et CERTIFIÉE — le témoin H, sa fonctionnalité
(pilier 1), son domaine 𝔓(E) (pilier 2) et sa valeur H(Y)=f⟨Y⟩ sont clos (image(·,·)
est un terme ATOMIQUE, donc AUCUNE capture-τ dans graphe_terme, contrairement à valeur).
RESTENT à assembler : pilier 3 (injectivité : f injective ⇒ f⟨Y⟩=f⟨Y'⟩ ⇒ Y=Y', par
image-injective + A1) et pilier 4 (image : f surjective ⇒ ∀Z⊂F ∃Y⊂E f⟨Y⟩=Z, par
sélection S8 Y={x∈E | f(x)∈Z} + double inclusion) — cœur d'algèbre d'image (liants
AXIOME_IMAGE « x »).  Rien postulé ; theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur, graphe_terme_domaine)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def graphe_H(f="f", e="E"):
    """H := graphe_terme(𝔓(E), f⟨Y⟩, 'Y')  — graphe de l'application A ↦ f⟨A⟩."""
    return E.graphe_terme(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 1 : H fonctionnel) | PDF p.335
def H_fonctionnel(f="f", e="E"):
    """⊢ est_fonctionnel(H).   (pilier 1 ; automatique par C54.)"""
    return graphe_terme_fonctionnel(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y", "y")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (pilier 2 : dom H = 𝔓E) | PDF p.335
def H_domaine(f="f", e="E"):
    """⊢ dom(H) = 𝔓(E).   (pilier 2 ; graphe_terme_domaine.)"""
    return graphe_terme_domaine(E.parties(_t(e)), E.image(_t(f), var("Y")), "Y", "y", "z")


# @livre Ch.R §7 Prop.1 | E R.32 item 1 (valeur H(Y)=f⟨Y⟩) | PDF p.335
def H_valeur(f="f", e="E", pt="Y0"):
    """{Y0 ∈ 𝔓(E)} ⊢ H(Y0) = f⟨Y0⟩ = image(f, Y0).   (valeur du témoin ; pt = NOM.)"""
    vf, ve = _t(f), _t(e)
    return graphe_terme_valeur(E.parties(ve), E.image(vf, var("Y")), pt, "Y", "y")


def cible_H_valeur(f="f", e="E", pt="Y0"):
    """Conclusion attendue de H_valeur : H(Y0) = image(f, Y0)."""
    vf, ve, vpt = _t(f), _t(e), var(pt)
    return egal(E.valeur(graphe_H(vf, ve), vpt), E.image(vf, vpt))


__all__ = ["graphe_H", "H_fonctionnel", "H_domaine", "H_valeur", "cible_H_valeur"]
