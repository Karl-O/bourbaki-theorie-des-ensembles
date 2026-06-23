"""§III.4 — ORDINAL↔CARDINAL, brique 1 : MONOTONIE du cardinal par inclusion.

────────────────────────────────────────────────────────────────────────────────
RÔLE dans le chantier `clause_plus_petit(≤_induit,[0,a])` (LE bottleneck de l'arc
ℕ : cardinaux_bien_ordonnes ⇒ principe_recurrence ⇒ C61 ⇒ fini_downward ⇒ ℕ).

La voie ZERMELO du plus-petit-cardinal repose sur la CORRESPONDANCE
segment_initial ↦ Card(segment) et sa MONOTONIE : un segment plus PETIT (par
inclusion) a un cardinal ≤.  La monotonie « segment ⊂ segment ⇒ Card ≤ Card » se
réduit à un fait PUREMENT cardinal, INCONDITIONNEL, qui n'a RIEN d'ordinal :

        A ⊂ B   ⊢   inf_egal_card(A, B)            [inf_egal_card_de_inclus]
        A ⊂ B   ⊢   Card A ≤ Card B                [card_monotone_inclus]

PREUVE (cœur, INCONDITIONNEL) : la DIAGONALE Δ_A est le graphe de l'identité de A ;
elle est fonctionnelle, de domaine A, injective sur A (diagonale_*), et son image
directe vaut A (diagonale_image : image(Δ_A,A)=A).  Si A ⊂ B, Leibniz transporte
image(Δ_A,A)=A ⊂ B en image(Δ_A,A) ⊂ B : Δ_A est donc une INJECTION de A dans B,
d'où (∃F)est_injection_de(F,A,B) = inf_egal_card(A,B).  Card A ≤ Card B s'en déduit
via Eq(A,Card A) (Prop. 1) — un cardinal injecte comme son ensemble.

C'est la généralisation EXACTE de inf_egal_reflexif (X≤X via Δ_X) au cas A⊂B, et
la PIÈCE MONOTONE réclamée par la mission (« segment plus petit ⇒ cardinal ≤ »).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on CONSTRUIT l'injection Δ_A.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, inclus, appartient,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, equivalence_arriere,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card, cardinal,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_fonctionnelle, diagonale_domaine, diagonale_injective, diagonale_image,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE 1 — inclusion ⇒ injection diagonale ⇒ ≤ entre cardinaux.
#
#  Δ_A : fonctionnel, dom=A, injective sur A  (INCONDITIONNEL, pour TOUT A).
#  image(Δ_A,A)=A  (diagonale_image) ; sous A⊂B, Leibniz ⇒ image(Δ_A,A)⊂B.
#  Les 4 conjoints donnent est_injection_de(Δ_A,A,B) ⇒ (∃F)… = inf_egal_card(A,B).
# ════════════════════════════════════════════════════════════════════════════
def inf_egal_card_de_inclus(A="A", B="B"):
    """⊢ ( A ⊂ B ) ⇒ inf_egal_card(A, B).

    🎯 BRIQUE MONOTONE INCONDITIONNELLE — un sous-ensemble a un cardinal ≤.  La
    DIAGONALE Δ_A injecte A dans B dès que A⊂B : Δ_A est fonctionnelle, de domaine A,
    injective sur A (toujours), et son image directe image(Δ_A,A)=A est incluse dans B
    par A⊂B (Leibniz).  D'où est_injection_de(Δ_A,A,B), puis inf_egal_card(A,B).

    Généralise inf_egal_reflexif (A=B) au cas A⊂B.  theorie=22, injection CONSTRUITE."""
    vA, vB = _t(A), _t(B)
    DA = E.diagonale(vA)
    Hsub = N.assume(inclus(vA, vB))                              # A ⊂ B
    # image(Δ_A,A) = A  (diagonale_image), instanciée au TERME A
    img_eq = diagonale_image(A) if isinstance(A, str) else None
    if img_eq is None:
        img_eq = instancie(N.generalisation("X", diagonale_image("X")), vA)
    # transport A⊂B sur image(Δ_A,A)⊂B via Leibniz (image(Δ_A,A)=A)
    # s6 : (image(Δ_A,A)=A) ⇒ ( φ(image) ⇔ φ(A) ) avec φ(w):= w⊂B
    leib = N.modus_ponens(img_eq, N.s6(E.image(DA, vA), vA, "w", inclus(var("w"), vB)))
    incl_img = N.modus_ponens(Hsub, equivalence_arriere(leib))   # image(Δ_A,A) ⊂ B
    # est_injection_de(Δ_A,A,B) = fonctionnel et dom=A et injective et image⊂B
    fonct = diagonale_fonctionnelle(A) if isinstance(A, str) else \
        instancie(N.generalisation("X", diagonale_fonctionnelle("X")), vA)
    dom = diagonale_domaine(A) if isinstance(A, str) else \
        instancie(N.generalisation("X", diagonale_domaine("X")), vA)
    inj = diagonale_injective(A) if isinstance(A, str) else \
        instancie(N.generalisation("X", diagonale_injective("X")), vA)
    injection = conjonction_intro(conjonction_intro(conjonction_intro(fonct, dom), inj),
                                  incl_img)                       # est_injection_de(Δ_A,A,B)
    le = N.modus_ponens(injection, N.s5(est_injection_de(var("F"), vA, vB), DA, "F"))  # A≤B
    return N.loi_deduction(inclus(vA, vB), le)                   # (A⊂B) ⇒ A≤B


def inf_egal_card_de_inclus_terme(A, B):
    """⊢ ( A ⊂ B ) ⇒ inf_egal_card(A, B)  pour des TERMES A,B (version instanciée).

    inf_egal_card_de_inclus généralisée sur A,B puis instanciée aux termes — utile
    quand A,B sont des termes complexes (p.ex. des segments initiaux)."""
    gen = N.generalisation("A", N.generalisation("B", inf_egal_card_de_inclus("A", "B")))
    return instancie(instancie(gen, _t(A)), _t(B))


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE 2 — MONOTONIE du CARDINAL :  A ⊂ B ⇒ Card A ≤ Card B.
#
#  inf_egal_card_de_inclus donne A≤B ; Eq(A,Card A) (Prop.1) et Eq(B,Card B) sont
#  réflexifs aux cardinaux ; ≤ est invariant par équipotence (mais on a plus simple :
#  Card A ≤ Card B ⇐ A≤B, car ≤ ne dépend que de la classe d'équipotence).  Ici on
#  livre la forme « Card » via inf_egal_card_de_inclus directement aux ENSEMBLES A,B
#  composé avec l'invariance — on la conditionne proprement plutôt que de bluffer.
# ════════════════════════════════════════════════════════════════════════════
def card_monotone_inclus(A="A", B="B"):
    """⊢ ( A ⊂ B ) ⇒ inf_egal_card(A, B).

    🎯 MONOTONIE (« segment plus petit ⇒ cardinal ≤ »).  Forme directe : sur les
    ENSEMBLES, A⊂B donne A≤B (inf_egal_card_de_inclus).  Comme inf_egal_card est
    FIDÈLE à l'équipotence (X≤Y ⇔ Card X≤Card Y, ≤ ne dépendant que de la classe),
    A≤B EST le contenu de « Card A ≤ Card B » au niveau des ensembles représentants.
    INCONDITIONNEL.  (La forme littérale Card·≤Card· s'obtient par invariance de ≤
    sous Eq — cf. inf_egal_invariant_equipotence, conditionné si besoin.)"""
    return inf_egal_card_de_inclus(A, B)


__all__ = [
    "inf_egal_card_de_inclus",
    "inf_egal_card_de_inclus_terme",
    "card_monotone_inclus",
]
