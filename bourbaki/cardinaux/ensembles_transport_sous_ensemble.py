"""GAP B — transport d'un sous-ensemble réalisant un cardinal DANS A lui-même.

`existe_sous_ensemble_cardinal_dans_card` (CLOS) réalise un cardinal c ≤ Card A comme
sous-ensemble de Card A (un τ-ensemble équipotent à A) ; pour l'argument d'extension de
Hessenberg (E.III.48 : choisir U ⊂ E∖S₀ de cardinal 𝔟), il faut U ⊂ A LUI-MÊME.

L'ancienne version `existe_sous_ensemble_cardinal` portait ce transport comme HYPOTHÈSE
honnête `transport_sous_ensemble`.  CE MODULE FERME le transport INCONDITIONNELLEMENT —
SANS passer par un transport de partie, en réalisant directement c ≤ A :

    c ≤ Card A   et   Eq(Card A, A) ⇒ Card A ≤ A   ⟹   c ≤ A   (transitivité).

Puis le CŒUR habituel : un témoin injection F : c ↪ A, image Im=F⟨c⟩ ⊂ A avec
Card Im = Card c = c.  Aucun résidu transport ; aucune hypothèse honnête restante.

    `existe_sous_ensemble_cardinal_transporte(c, A)` :
        ( est_cardinal(c)  et  c ≤ Card A )  ⇒  (∃V)( V ⊂ A  et  Card V = c ).   [0 hyp].

INVARIANT : theorie_ensembles() = 22 ; aucun axiome nouveau ; rien postulé.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl, existe, inclus, tau
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, est_injection_de, equipotent,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.ensembles_cardinaux_ordre import (
    equipotence_implique_inf_egal, inf_egal_transitive,
)
from bourbaki.cardinaux.ensembles_realisation_segment_close import (
    injection_donne_equipotent_image,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import _prop1_direct_t
from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import _eq_sym_t
from bourbaki.cardinaux.ensembles_hessenberg_extension import _cardinal_est_son_cardinal_t
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import composer_egalites


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── briques génériques-puis-instanciées-aux-TERMES (capture-safe) ─────────────────
def _eq_son_card_t(t):
    """⊢ Eq(t, Card t)  (instance-terme de equipotent_son_cardinal)."""
    gen = N.generalisation("X", equipotent_son_cardinal("X"))
    return instancie(gen, t)


def _eq_implique_le_t(s, t):
    """⊢ Eq(s, t) ⇒ (s ≤ t)  (instance-terme de equipotence_implique_inf_egal)."""
    gen = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))
    return instancie(instancie(gen, s), t)


def _le_trans_t(s, t, u):
    """⊢ ((s ≤ t) et (t ≤ u)) ⇒ (s ≤ u)  (instance-terme de inf_egal_transitive)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(gen, s), t), u)


# ════════════════════════════════════════════════════════════════════════════════
#  GAP B — existe_sous_ensemble_cardinal_transporte : sous-ensemble de A LUI-MÊME.
# ════════════════════════════════════════════════════════════════════════════════
def existe_sous_ensemble_cardinal_transporte(c="cE", A="AE", V="VE"):
    """⊢ ( est_cardinal(c)  et  c ≤ Card A )  ⇒  (∃V)( V ⊂ A  et  Card V = c ).   [0 hyp].

    🎯 GAP B FERMÉ INCONDITIONNELLEMENT.  Réalise un cardinal c ≤ Card A comme
    SOUS-ENSEMBLE de A (et non de Card A).  Au lieu de transporter une partie de Card A
    vers A, on réalise directement c ≤ A :

        c ≤ Card A   ;   Eq(Card A, A) [= sym Eq(A,Card A)]  ⇒  Card A ≤ A ;
        transitivité  ⟹  c ≤ A.

    Puis cœur identique à existe_sous_ensemble_cardinal_dans_card mais sur A : témoin
    F : c ↪ A, V := image(F,c) ⊂ A, Card V = Card c = c (injection_donne_equipotent_image
    + Prop 1 + est_cardinal(c)).  AUCUN résidu transport ; theorie=22, NON vacuous."""
    vc, vA = _t(c), _t(A)
    cardA = cardinal(vA)
    Vn = V if isinstance(V, str) else V.nom

    ante = et(est_cardinal(vc), inf_egal_card(vc, cardA))
    h = N.assume(ante)
    h_card_c = conjonction_elim_gauche(h)                    # est_cardinal(c)
    h_le_cardA = conjonction_elim_droite(h)                  # c ≤ Card A

    # ── c ≤ A  (réalisation directe) ─────────────────────────────────────────────
    eq_A_cardA = _eq_son_card_t(vA)                          # Eq(A, Card A)
    eq_cardA_A = N.modus_ponens(eq_A_cardA, _eq_sym_t(vA, cardA))   # Eq(Card A, A)
    le_cardA_A = N.modus_ponens(eq_cardA_A, _eq_implique_le_t(cardA, vA))  # Card A ≤ A
    le_c_A = N.modus_ponens(
        conjonction_intro(h_le_cardA, le_cardA_A),
        _le_trans_t(vc, cardA, vA))                         # c ≤ A

    # ── témoin injection F : c ↪ A, V := image(F,c) ⊂ A, Card V = c ──────────────
    inj_F = est_injection_de(var("F"), vc, vA)
    wit = N.modus_ponens(le_c_A, N.existe_temoin(inj_F, "F"))   # est_injection_de(τF, c, A)
    Ft = tau("F", inj_F)
    Im = E.image(Ft, vc)                                    # Im = F⟨c⟩
    Im_sub = conjonction_elim_droite(wit)                   # Im ⊂ A
    eq_c_Im = N.modus_ponens(wit, injection_donne_equipotent_image(Ft, vc, vA))  # Eq(c, Im)

    # Card Im = c
    eq_Im_c = N.modus_ponens(eq_c_Im, _eq_sym_t(vc, Im))          # Eq(Im, c)
    cardIm_eq_cardc = N.modus_ponens(eq_Im_c, _prop1_direct_t(Im, vc))   # Card Im = Card c
    cardc_eq_c = N.modus_ponens(h_card_c, _cardinal_est_son_cardinal_t(vc))   # Card c = c
    cardIm_eq_c = composer_egalites(cardIm_eq_cardc, cardc_eq_c)   # Card Im = c

    # ── (∃V)( V ⊂ A  et  Card V = c ) ───────────────────────────────────────────
    corps = et(inclus(var(Vn), vA), egal(cardinal(var(Vn)), vc))
    conj = conjonction_intro(Im_sub, cardIm_eq_c)
    assert conj.conclusion == et(inclus(Im, vA), egal(cardinal(Im), vc))
    ex = N.modus_ponens(conj, N.s5(corps, Im, Vn))          # (∃V)(V⊂A et Card V=c)
    res = N.loi_deduction(ante, ex)

    cible = impl(ante, existe(Vn, corps))
    assert res.conclusion == cible, \
        f"existe_sous_ensemble_cardinal_transporte : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, \
        "existe_sous_ensemble_cardinal_transporte : VACUOUS"
    assert not res.hypotheses, \
        f"existe_sous_ensemble_cardinal_transporte : HYPS RÉSIDUELLES {res.hypotheses}"
    return res


def existe_sous_ensemble_cardinal_transporte_cible(c="cE", A="AE", V="VE"):
    """ÉNONCÉ-cible (test miroir)."""
    vc, vA = _t(c), _t(A)
    cardA = cardinal(vA)
    Vn = V if isinstance(V, str) else V.nom
    ante = et(est_cardinal(vc), inf_egal_card(vc, cardA))
    return impl(ante, existe(Vn, et(inclus(var(Vn), vA), egal(cardinal(var(Vn)), vc))))


__all__ = [
    "existe_sous_ensemble_cardinal_transporte",
    "existe_sous_ensemble_cardinal_transporte_cible",
]
