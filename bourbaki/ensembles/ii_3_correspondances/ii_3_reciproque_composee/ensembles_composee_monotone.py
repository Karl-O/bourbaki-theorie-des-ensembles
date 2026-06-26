"""§II.3.3 — Monotonie de la composée de deux graphes (E II.13, Remarque).

⊢ { G₁ ⊂ G₂, G₁' ⊂ G₂' }  ⊢  G₁'∘G₁ ⊂ G₂'∘G₂

Énoncé (Bourbaki, E II.13) : « Il est clair que si G₁, G₂, G₁', G₂' sont des
graphes, les relations G₁ ⊂ G₂ et G₁' ⊂ G₂' entraînent G₁'∘G₁ ⊂ G₂'∘G₂. »

STRATÉGIE (calque exact de `image_croissante`, §II.3.1 Prop.2 — transport d'une
inclusion à travers un opérateur de graphe défini par son axiome d'appartenance).

Le passage « w générique → couple (p,r) » est traité SANS aucune machinerie « tout
élément est un couple » : on n'utilise PAS `couple_composee` (qui ne caractérise que
l'appartenance d'un couple), mais l'axiome AXIOME_COMPOSEE lui-même, instancié sur un
w GÉNÉRIQUE :

    w ∈ G'∘G  ⇔  (∃p)(∃r)( w=(p,r)  et  (∃y)((p,y)∈G et (y,r)∈G') ).

L'inclusion `inclus(A,B)` quantifie justement sur ce w générique : But = (∀w)(w∈G₁'∘G₁ ⇒
w∈G₂'∘G₂). Pour un w fixé on transporte le NOYAU EXISTENTIEL de l'axiome (la clause de
tête w=(p,r) est laissée intacte) :
  - (p,y)∈G₁ ⇒ (p,y)∈G₂  [hyp inclus(G₁,G₂) instanciée au couple (p,y)] ;
  - (y,r)∈G₁' ⇒ (y,r)∈G₂' [hyp inclus(G₁',G₂') instanciée au couple (y,r)] ;
  d'où (p,y)∈G₁ et (y,r)∈G₁'  ⇒  (p,y)∈G₂ et (y,r)∈G₂' (conjonction_intro) ;
  monotonie_existe sur « y » ; puis on garde w=(p,r) à gauche et on transporte le
  conjonct droit (implication sur le et, loi_deduction) ; monotonie_existe sur « r »
  puis « p ». Le syllogisme avant→arrière via les deux instances de l'axiome (sens ⇒
  pour G₁'∘G₁, sens ⇐ pour G₂'∘G₂) donne w∈G₁'∘G₁ ⇒ w∈G₂'∘G₂ ; généralisation sur w =
  inclus(G₁'∘G₁, G₂'∘G₂).

C'est EXACTEMENT l'inclusion de Bourbaki (élément générique), pas une variante
couple-à-couple : l'axiome fournit lui-même la clause w=(p,r), donc aucun w non-couple
ne peut peupler une composée et la preuve reste close sur le w générique.

INVARIANTS : est_clos == False ; hypotheses == { inclus(G₁,G₂), inclus(G₁',G₂') }
exactement (2) ; conclusion == inclus(composee(G₁',G₁), composee(G₂',G₂)) ∉ hypotheses.
Contenu non-trivial : les deux inclusions transportent le noyau existentiel — sans
elles l'implication w∈G₁'∘G₁ ⇒ w∈G₂'∘G₂ ne tient pas (pas de tautologie déguisée).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, existe, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import monotonie_existe


def _inst_composee(gp, g, w):
    """⊢ (w ∈ G'∘G) ⇔ (∃p)(∃r)(w=(p,r) et (∃y)((p,y)∈G et (y,r)∈G')).

    Instance directe de AXIOME_COMPOSEE sur un w GÉNÉRIQUE (binders internes p,r,y)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    return instancie(instancie(instancie(ax, gp), g), w)


# @livre Ch.II §3.3 Rem.- | E II.13 L.3-5 | PDF p.64
def composee_monotone(g1="G1", g2="G2", g1p="G1p", g2p="G2p"):
    """⊢ { G₁⊂G₂, G₁'⊂G₂' } ⊢ G₁'∘G₁ ⊂ G₂'∘G₂.   (E II.13, Remarque, monotonie de ∘.)

    Hypothèses non déchargées (volontaire — théorème ouvert, est_clos==False) :
    inclus(G₁,G₂) et inclus(G₁',G₂'). Conclusion = inclus(composee(G₁',G₁),
    composee(G₂',G₂)), strictement hors des hypothèses (cf. docstring module)."""
    vG1, vG2, vG1p, vG2p = var(g1), var(g2), var(g1p), var(g2p)
    # Variable d'élément GÉNÉRIQUE nommée « z » : c'est le liant par défaut de
    # inclus(A,B) = (∀z)(z∈A ⇒ z∈B) (z non libre dans les composées), de sorte que
    # la conclusion généralisée coïncide STRUCTURELLEMENT avec inclus(G₁'∘G₁, G₂'∘G₂).
    vw, vp, vr, vy = var("z"), var("p"), var("r"), var("y")

    # Hypothèses ouvertes : les deux inclusions.
    h_g = N.assume(inclus(vG1, vG2))     # (∀z)((z∈G₁) ⇒ (z∈G₂))
    h_gp = N.assume(inclus(vG1p, vG2p))  # (∀z)((z∈G₁') ⇒ (z∈G₂'))

    # Transport au niveau des couples : inclusions instanciées en (p,y) et (y,r).
    py1_py2 = instancie(h_g, E.couple(vp, vy))     # (p,y)∈G₁ ⇒ (p,y)∈G₂
    yr1_yr2 = instancie(h_gp, E.couple(vy, vr))    # (y,r)∈G₁' ⇒ (y,r)∈G₂'

    # Noyau : (p,y)∈G₁ et (y,r)∈G₁'  ⇒  (p,y)∈G₂ et (y,r)∈G₂'.
    noyau1 = et(appartient(E.couple(vp, vy), vG1), appartient(E.couple(vy, vr), vG1p))
    noyau2 = et(appartient(E.couple(vp, vy), vG2), appartient(E.couple(vy, vr), vG2p))
    ha = N.assume(noyau1)
    conc = conjonction_intro(N.modus_ponens(conjonction_elim_gauche(ha), py1_py2),
                             N.modus_ponens(conjonction_elim_droite(ha), yr1_yr2))
    inner = N.loi_deduction(noyau1, conc)          # noyau₁ ⇒ noyau₂
    mono_y = monotonie_existe(inner, "y")          # (∃y)noyau₁ ⇒ (∃y)noyau₂

    # Préserver la clause de tête w=(p,r) en transportant uniquement le conjonct droit :
    #   (w=(p,r) et (∃y)noyau₁) ⇒ (w=(p,r) et (∃y)noyau₂).
    eqw = egal(vw, E.couple(vp, vr))
    body1 = et(eqw, existe("y", noyau1))
    hbody = N.assume(body1)
    body_imp = N.loi_deduction(body1, conjonction_intro(
        conjonction_elim_gauche(hbody),
        N.modus_ponens(conjonction_elim_droite(hbody), mono_y)))   # body₁ ⇒ body₂

    # Existentiels externes r puis p (binders de l'axiome).
    mono_r = monotonie_existe(body_imp, "r")       # (∃r)body₁ ⇒ (∃r)body₂
    mono_p = monotonie_existe(mono_r, "p")         # (∃p)(∃r)body₁ ⇒ (∃p)(∃r)body₂

    # Repli : w∈G₁'∘G₁ ⇒ (∃p)(∃r)body₁ ⇒ (∃p)(∃r)body₂ ⇒ w∈G₂'∘G₂.
    w_imp = syllogisme(equivalence_avant(_inst_composee(vG1p, vG1, vw)),
                       syllogisme(mono_p, equivalence_arriere(_inst_composee(vG2p, vG2, vw))))
    return N.generalisation("z", w_imp)            # inclus(G₁'∘G₁, G₂'∘G₂), hyps présentes


__all__ = ["composee_monotone"]
