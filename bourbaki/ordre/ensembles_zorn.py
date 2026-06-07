"""Chapitre III §2 — Vocabulaire et premiers lemmes pour le Théorème de Zorn.

GROUNDWORK (E.III.2).  On RELÈVE le vocabulaire fidèle de Bourbaki §III.2 et on
prouve les lemmes DIRECTS atteignables ; on NE prouve PAS Zorn en entier (gros
chantier multi-rounds reposant in fine sur le signe τ / l'axiome du choix).

Énoncés Bourbaki VERBATIM (E.III.2) repris ici :

  • Définition 3 — Ensemble inductif :
      « On dit qu'un ensemble ordonné E est inductif si toute partie totalement
        ordonnée de E possède un majorant dans E. »
  • Théorème 2 (Zorn) :
      « Tout ensemble ordonné inductif possède un élément maximal. »
  • Proposition 4 :
      « Soit E un ensemble ordonné dont toute partie bien ordonnée soit majorée ;
        alors E admet un élément maximal. »
  • Corollaire 1 (de la Proposition 4 / Théorème 2) :
      « Soient E un ensemble ordonné inductif, et a un élément de E ; il existe un
        élément maximal m de E tel que m ≥ a. »
  • Corollaire 2 (de la Proposition 4 / Théorème 2) :
      « Soit 𝔉 un ensemble de parties d'un ensemble E tel que, pour tout
        sous-ensemble 𝔊 de 𝔉, totalement ordonné par inclusion, la réunion (resp.
        l'intersection) des ensembles de 𝔊 appartienne à 𝔉 ; alors 𝔉 possède un
        élément maximal (resp. minimal). »

On réutilise INTÉGRALEMENT `ensembles_ordre_relation` (round 10) : est_ordre,
totalement_ordonne, majorant, element_maximal, plus_grand_element, et le lemme
DÉJÀ certifié `plus_grand_est_maximal` (le plus grand élément est maximal).

DÉFINITIONS posées ici (formes fidèles, graphe G d'ordre sur E) :
  chaine(G,E,C)        := (C⊂E) et totalement_ordonne(G,C)
  est_inductif(G,E)    := est_ordre(G,E) et (∀C)(chaine(G,E,C) ⇒ (∃m) majorant(G,C,m,E))
  enonce_non_vide(E)   := (∃x)(x∈E)
  zorn(G,E)            := (est_ordre(G,E) et est_inductif(G,E) et E≠∅)
                            ⇒ (∃m) element_maximal(G,E,m)
                          [DÉFINITION DE L'ÉNONCÉ — pas une preuve.]

LEMMES DIRECTS certifiés par le noyau abrégé (type Theoreme opaque) :
  chaine_est_partie, chaine_est_totalement_ordonnee,
  inductif_est_ordre, inductif_chaine_majoree,
  plus_grand_donne_maximal_existe (∃ d'élément maximal à partir d'un plus grand
  élément — instance close de l'énoncé de Zorn quand E a un plus grand élément),
  zorn_si_plus_grand_element (l'énoncé de Zorn est vérifié sous l'hypothèse
  supplémentaire « E a un plus grand élément », via plus_grand_est_maximal).

PLAN POUR LA SUITE (non fait, multi-rounds) :
  • Lemme 3 §III.2 (Bourbaki-Witt / Knaster-Tarski, synergie phi_point_fixe) :
    construire M⊂E et un bon ordre Γ via p(X)=majorant strict ; le τ fournit p.
  • Proposition 4 ⇒ Théorème 2 (toute partie bien ordonnée majorée ⇒ maximal).
  • Corollaire 1 (maximal ≥ a) puis Corollaire 2 (𝔉 ⊂ 𝔓(E), ordre ⊂).
  Ces étapes exigent la récurrence transfinie (C59/C60) et le signe τ ; à poser
  une fois ce socle disponible.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, impl, appartient, pourtout, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.ordre.ensembles_ordre_relation import (
    est_ordre, totalement_ordonne, majorant, element_maximal, plus_grand_element,
    plus_grand_est_maximal,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De  Γ∪{H} ⊢ C  et  Δ ⊢ H  on déduit  Γ∪Δ ⊢ C  (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS — chaîne, ensemble inductif, énoncé de Zorn  (E.III.2)
# ════════════════════════════════════════════════════════════════════════════
def chaine(G, E_set, C, x="x", y="y", z="z"):
    """chaine(G,E,C) := (C⊂E) et totalement_ordonne(G,C).

    « C est une CHAÎNE de E » : une partie de E totalement ordonnée par G.
    (E.III.2, terminologie de la Définition 3 — « partie totalement ordonnée ».)"""
    vC, vE = _terme(C), _terme(E_set)
    return et(inclus(vC, vE), totalement_ordonne(G, vC, x, y, z))


def est_inductif(G, E_set, C="C", m="m", x="x", y="y", z="z"):
    """est_inductif(G,E) := est_ordre(G,E)
        et (∀C)(chaine(G,E,C) ⇒ (∃m) majorant(G,C,m,E)).

    DÉFINITION 3 §III.2 VERBATIM : « un ensemble ordonné E est inductif si toute
    partie totalement ordonnée de E possède un majorant dans E »."""
    vC = var(C)
    corps = impl(chaine(G, E_set, vC, x, y, z),
                 existe(m, majorant(G, vC, var(m), E_set, x)))
    return et(est_ordre(G, E_set, x, y, z), pourtout(C, corps))


def enonce_non_vide(E_set, x="x"):
    """enonce_non_vide(E) := (∃x)(x∈E).   « E ≠ ∅ »  (forme existentielle fidèle)."""
    return existe(x, appartient(var(x), _terme(E_set)))


def zorn(G, E_set, m="m", C="C", x="x", y="y", z="z"):
    """zorn(G,E) := (est_ordre(G,E) et est_inductif(G,E) et E≠∅)
        ⇒ (∃m) element_maximal(G,E,m).

    ÉNONCÉ du THÉORÈME 2 (Zorn) §III.2 : « Tout ensemble ordonné inductif possède
    un élément maximal. »  (Bourbaki suppose E ordonné inductif ; on explicite en
    outre E≠∅, sinon « possède » est vide.)

    ⚠ C'est la DÉFINITION de l'énoncé — PAS une preuve.  Zorn requiert in fine la
    récurrence transfinie et le signe τ (axiome du choix) ; chantier multi-rounds."""
    vE = _terme(E_set)
    hyp = et(et(est_ordre(G, vE, x, y, z), est_inductif(G, vE, C, m, x, y, z)),
             enonce_non_vide(vE, x))
    return impl(hyp, existe(m, element_maximal(G, vE, var(m), x)))


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS — décomposition des définitions  (certifiés noyau abrégé)
# ════════════════════════════════════════════════════════════════════════════
def chaine_est_partie(G, E_set="E", C="C", x="x", y="y", z="z"):
    """{ chaine(G,E,C) } ⊢ C⊂E.   (Une chaîne de E est une partie de E.)"""
    H = N.assume(chaine(G, E_set, C, x, y, z))
    return conjonction_elim_gauche(H)


def chaine_est_totalement_ordonnee(G, E_set="E", C="C", x="x", y="y", z="z"):
    """{ chaine(G,E,C) } ⊢ totalement_ordonne(G,C).

    Une chaîne est, par définition, totalement ordonnée par G."""
    H = N.assume(chaine(G, E_set, C, x, y, z))
    return conjonction_elim_droite(H)


def inductif_est_ordre(G, E_set="E", C="C", m="m", x="x", y="y", z="z"):
    """{ est_inductif(G,E) } ⊢ est_ordre(G,E).

    Un ensemble inductif est en particulier ordonné (Définition 3 : « ordonné »)."""
    H = N.assume(est_inductif(G, E_set, C, m, x, y, z))
    return conjonction_elim_gauche(H)


def inductif_chaine_majoree(G, E_set="E", C="C", m="m", x="x", y="y", z="z"):
    """{ est_inductif(G,E) } ⊢ chaine(G,E,C) ⇒ (∃m) majorant(G,C,m,E).

    Extrait la propriété caractéristique de l'inductivité pour la chaîne C :
    « toute partie totalement ordonnée de E possède un majorant dans E »
    (Définition 3, instanciée en C)."""
    vC = var(C)
    H = N.assume(est_inductif(G, E_set, C, m, x, y, z))
    quant = conjonction_elim_droite(H)                  # (∀C)(chaine ⇒ (∃m)majorant)
    return instancie(quant, vC)                         # chaine(G,E,C) ⇒ (∃m)majorant(G,C,m,E)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME DIRECT — cas tractable de Zorn : E a un PLUS GRAND ÉLÉMENT
#  Dans ce cas l'élément maximal existe SANS récurrence transfinie ni τ :
#  c'est le plus grand élément lui-même (plus_grand_est_maximal, round 10).
# ════════════════════════════════════════════════════════════════════════════
def plus_grand_donne_maximal_existe(G, E_set="E", m="m", x="x", y="y"):
    """{ antisymetrie(G), plus_grand_element(G,E,m) } ⊢ (∃m) element_maximal(G,E,m).

    Si E possède un plus grand élément m, alors E possède un élément MAXIMAL : m
    lui-même est maximal (plus_grand_est_maximal, E.III.1.6-1.7), donc on conclut
    par S5 (introduction de ∃ avec le témoin m).  C'est la conclusion de Zorn
    obtenue directement dès qu'un plus grand élément existe — aucun choix requis."""
    vm = _terme(m)
    # m est maximal (sous {antisymetrie(G), plus_grand_element(G,E,m)})
    max_m = plus_grand_est_maximal(G, E_set, m, x, y)        # ⊢ element_maximal(G,E,m)
    # (∃m) element_maximal(G,E,m) via S5 avec le témoin m  (subst m|m = element_maximal(G,E,m))
    R = element_maximal(G, E_set, var(m), x)                  # corps avec la variable liée m
    s5 = N.s5(R, vm, m)                                       # ⊢ (m|m)R ⇒ (∃m)R = element_maximal(G,E,m)⇒(∃m)…
    return N.modus_ponens(max_m, s5)


def zorn_si_plus_grand_element(G, E_set="E", m="m", x="x", y="y"):
    """{ antisymetrie(G), plus_grand_element(G,E,m) } ⊢ (∃m) element_maximal(G,E,m).

    Forme « Zorn sous hypothèse forte » : si E a un plus grand élément, la
    conclusion de Zorn (existence d'un maximal) est ATTEIGNABLE directement.
    Alias documentaire de plus_grand_donne_maximal_existe — montre que la partie
    non triviale de Zorn est exactement de produire la chaîne maximale / le τ ;
    le cas « plus grand élément déjà là » est gratuit."""
    return plus_grand_donne_maximal_existe(G, E_set, m, x, y)


__all__ = [
    # définitions fidèles §III.2
    "chaine", "est_inductif", "enonce_non_vide", "zorn",
    # lemmes directs de décomposition
    "chaine_est_partie", "chaine_est_totalement_ordonnee",
    "inductif_est_ordre", "inductif_chaine_majoree",
    # cas tractable : plus grand élément ⇒ maximal existe (conclusion de Zorn)
    "plus_grand_donne_maximal_existe", "zorn_si_plus_grand_element",
]
