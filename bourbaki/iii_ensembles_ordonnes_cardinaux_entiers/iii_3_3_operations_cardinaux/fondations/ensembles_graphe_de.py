"""§II.3.1 — GRAPHE d'une application :  gr(f) := pr₁(pr₁ f).

Une application f = ((G, E), F) du projet est le TRIPLE couple(couple(G,E),F).
Son GRAPHE est la 1ʳᵉ composante interne G = pr₁(pr₁ f) (E.II.3.1).  C'est la pièce
qui RELIE une application à son graphe sous-jacent : f(x), entendu au sens de
Bourbaki comme G(x), se calcule sur gr(f) — et c'est gr(f), pas le triple f, qui
alimente le pont `valeur_dans_codomaine`.

  • graphe_de(f)          : le TERME pr₁(pr₁ f) ;
  • graphe_de_triple(G,E,F): ⊢ gr(((G,E),F)) = G   (extraction, pure algèbre pr₁).

Aucun axiome ajouté : deux applications de pr₁((u,v))=u (E.II.31) + congruence.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
    _projection_premiere_ab)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# (Def.2 du livre : une correspondance est un TRIPLET Gamma=(G,A,B) et « G est le
#  graphe de Gamma » — gr(f)=pr1(pr1 f) extrait ce G du triple ((G,E),F) du projet.)
# @livre Ch.II §3.1 Def.2 | E II.10 L.6-8 | PDF p.61
def graphe_de(f, x="a", y="b"):
    """gr(f) := pr₁(pr₁ f)   (le graphe de l'application f=((G,E),F), terme).

    Liants pr₁ « a », « b » (≠ x,y des machineries graphe-terme) aux DEUX niveaux ;
    indépendants car bornés dans chaque pr₁."""
    vf = _t(f)
    return E.pr1(E.pr1(vf, x, y), x, y)


# @livre Ch.II §3.1 Def.2 | E II.10 L.6-8 | PDF p.61
def graphe_de_triple(g="G", e="E", f="F"):
    """⊢ gr(((G,E),F)) = G.   (le graphe d'une application-triple est G.)

    pr₁(((G,E),F)) = (G,E) puis pr₁((G,E)) = G  (_projection_premiere_ab, E.II.31),
    reliées par congruence (trou « w » au 1ᵉʳ pr₁)."""
    vG, vE, vF = _t(g), _t(e), _t(f)
    GE = E.couple(vG, vE)                 # (G, E)
    triple = E.couple(GE, vF)             # ((G, E), F)
    pr1_triple = E.pr1(triple, "a", "b")  # pr₁(((G,E),F), a, b)
    step1 = _projection_premiere_ab(GE, vF, "a", "b")   # pr₁(((G,E),F),a,b) = (G,E)
    step2 = _projection_premiere_ab(vG, vE, "a", "b")   # pr₁((G,E),a,b) = G
    # congruence : pr₁(pr₁(triple,a,b),a,b) = pr₁((G,E),a,b)
    cong = N.modus_ponens(step1,
        congruence_terme(pr1_triple, GE, E.pr1(var("w"), "a", "b")))
    return composer_egalites(cong, step2)   # gr(triple) = G


__all__ = ["graphe_de", "graphe_de_triple"]
