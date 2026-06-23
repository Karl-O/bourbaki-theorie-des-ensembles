"""Chapitre III §1 — PROPOSITION 4 (E.III.9) : inf A ≤ sup A pour A non vide.

Convention « graphe G » de `ensembles_ordre_relation.py` : x≤y := (x,y)∈G,
inf A = plus grand des minorants (`borne_inferieure(G,A,i,E)`), sup A = plus
petit des majorants (`borne_superieure(G,A,s,E)`).  Les hypothèses d'EXISTENCE
des bornes (« i = inf A », « s = sup A ») sont posées comme hypothèses HONNÊTES,
exactement comme dans Bourbaki (« lorsque les bornes existent »).

THÉORÈME (forme « ensemble ») :

  • PROPOSITION 4 (E.III.9) — `inf_le_sup` :
      { transitivite_rel(G),  (∃z)(z∈A),
        borne_inferieure(G,A,i,E),  borne_superieure(G,A,s,E) } ⊢ (i,s)∈G.

    Soit A⊂E admettant inf A = i et sup A = s.  Si A≠∅ — c.-à-d. (∃z)(z∈A) —,
    alors inf A ≤ sup A.  En effet, soit a∈A un témoin : i minore A donc i≤a, et
    s majore A donc a≤s ; la TRANSITIVITÉ donne i≤s, i.e. (i,s)∈G.

    L'hypothèse A≠∅ est ESSENTIELLE : pour A=∅ tout élément est à la fois minorant
    et majorant, et l'on aurait sup ∅ ≤ inf ∅ (l'inégalité s'inverse).  Le témoin
    a∈A sert exactement de « pont » entre les deux bornes.

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ de la logique pure du « plus
grand minorant / plus petit majorant » et de la transitivité, aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, et, impl, appartient, existe,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    transitivite_rel, borne_inferieure, borne_superieure,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 4 (E.III.9) — A ≠ ∅ ⇒ inf A ≤ sup A
# ════════════════════════════════════════════════════════════════════════════
def inf_le_sup(G="G", A="A", E_set="E", i="i", s="s", a="a",
               x="x", y="y", t="t", u="u", w="w"):
    """{ transitivite_rel(G),  (∃z)(z∈A),
         borne_inferieure(G,A,i,E),  borne_superieure(G,A,s,E) } ⊢ (i,s)∈G.

    PROPOSITION 4 : si A≠∅ admet une borne inférieure i et une borne supérieure s,
    alors i ≤ s.  Témoin a∈A (existe car A≠∅) ; i minore A donc (i,a)∈G ; s majore
    A donc (a,s)∈G ; la transitivité en (i,a,s) conclut (i,s)∈G.  (E.III.9.)

    Le témoin a est éliminé en fin de preuve (existe_elimination) : la conclusion
    (i,s)∈G ne contient pas a libre, donc l'hypothèse honnête est exactement
    (∃z)(z∈A) — pas le témoin.
    """
    vi, vs, va, vA = _terme(i), _terme(s), _terme(a), _terme(A)

    # ── les quatre hypothèses HONNÊTES ────────────────────────────────────────
    Htr = N.assume(transitivite_rel(G, x, y, t))          # (∀x∀y∀t)(((x,y)∈G et (y,t)∈G)⇒(x,t)∈G)
    Hexists = N.assume(existe(a, appartient(va, vA)))      # (∃a)(a∈A)   [A ≠ ∅]
    Hinf = N.assume(borne_inferieure(G, A, vi, E_set, x, y))   # i = inf A
    Hsup = N.assume(borne_superieure(G, A, vs, E_set, x, y))   # s = sup A

    # ── extraction des prédicats ──────────────────────────────────────────────
    # borne_inferieure(G,A,i,E) = minorant(G,A,i,E) et (∀y)(minorant(y)⇒(y,i)∈G)
    i_minorant = conjonction_elim_gauche(Hinf)            # minorant(G,A,i,E)
    # minorant(G,A,i,E) = i∈E et (∀x)(x∈A⇒(i,x)∈G)
    i_minore = conjonction_elim_droite(i_minorant)        # (∀x)(x∈A⇒(i,x)∈G)
    # borne_superieure(G,A,s,E) = majorant(G,A,s,E) et (∀y)(majorant(y)⇒(s,y)∈G)
    s_majorant = conjonction_elim_gauche(Hsup)            # majorant(G,A,s,E)
    # majorant(G,A,s,E) = s∈E et (∀x)(x∈A⇒(x,s)∈G)
    s_majore = conjonction_elim_droite(s_majorant)        # (∀x)(x∈A⇒(x,s)∈G)

    # ── corps sous le témoin a∈A : dériver (i,s)∈G ────────────────────────────
    Ha = N.assume(appartient(va, vA))                      # a∈A   (témoin)
    ia = N.modus_ponens(Ha, instancie(i_minore, va))       # (i,a)∈G   (i minore A)
    as_ = N.modus_ponens(Ha, instancie(s_majore, va))      # (a,s)∈G   (s majore A)
    # transitivité en (i,a,s) : ((i,a)∈G et (a,s)∈G) ⇒ (i,s)∈G
    tr_ias = instancie(instancie(instancie(Htr, vi), va), vs)
    is_ = N.modus_ponens(conjonction_intro(ia, as_), tr_ias)   # (i,s)∈G   (sous {a∈A, …})

    # ── décharge du témoin : (a∈A) ⇒ (i,s)∈G  puis  (∃a)(a∈A) ⇒ (i,s)∈G ───────
    sous_a = N.loi_deduction(appartient(va, vA), is_)      # (a∈A) ⇒ (i,s)∈G
    ex_imp = existe_elimination(sous_a, a)                 # (∃a)(a∈A) ⇒ (i,s)∈G
    return N.modus_ponens(Hexists, ex_imp)                 # (i,s)∈G   (sous les 4 honnêtes)


# cible : (i,s)∈G  sous { transitivite_rel(G), (∃a)(a∈A),
#                         borne_inferieure(G,A,i,E), borne_superieure(G,A,s,E) }
def _cible(G="G", i="i", s="s"):
    """Conclusion attendue de `inf_le_sup` : (i,s)∈G."""
    return _couple_dans(i, s, G)


__all__ = ["inf_le_sup"]
