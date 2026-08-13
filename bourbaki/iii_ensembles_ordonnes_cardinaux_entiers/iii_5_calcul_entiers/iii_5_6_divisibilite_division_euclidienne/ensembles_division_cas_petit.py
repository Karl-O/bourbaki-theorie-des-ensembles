# -*- coding: utf-8 -*-
"""Division euclidienne (E III.5.6, Th.1) — CAS PETIT : si Card(a) < b alors (q,r) = (0, Card a).

Première pièce de la campagne « division euclidienne » (le principal trou nommé restant) : le cas
a < b de l'EXISTENCE, énoncé avec les VRAIES opérations cardinales (pas les symboles opaques
plus_ent/prod_ent) :   b·q + r  :=  Card( Card(B×q) ⊔ r ).

    ⊢  (Card a < b)  ⇒  (∃q)(∃r)( b·q + r = Card a   et   r < b )

Stratégie (chaîne d'égalités + double S5) :
    b·0 + Card a = Card(Card(B×∅) ⊔ Card a)          [q := ∅ = 0]
                 = Card(Card(∅) ⊔ Card a)             produit_cardinal_zero + congruence
                 = Card(∅ ⊔ Card a)                   cardinal_vide_egale_vide + congruence
                 = Card(Card a)                       somme_cardinale_zero_neutre (B := Card a)
                 = Card a                             idempotence de Card
puis conjonction avec l'hypothèse Card a < b, S5 (témoin r := Card a), S5 (témoin q := ∅),
loi de déduction. CLOS (0 hypothèse). Frontière : primitives noyau seules, theorie == 22.

NB fidélité : lemme de la DÉMONSTRATION du Th.1 (le cas r<b) ; @livre posé (campagne 2026-07) :
Th.1 = E III.39 L.10-11, démo L.12-19 (PDF p.142). Cas PARTIEL — le Th.1 général reste ouvert.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, existe
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_zero)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_zero_neutre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
    _cardinal_idempotent_t)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    cardinal_vide_egale_vide)

_Q, _R = "qDE", "rDE"                                  # liants frais (jamais libres dans a, b)


def _phi(vb, va, q_term, r_term):
    """b·q + r = Card a  et  r < b   (la condition de division, opérations RÉELLES)."""
    bq_plus_r = somme_cardinale_binaire(produit_cardinal_binaire(vb, q_term), r_term)
    return et(egal(bq_plus_r, cardinal(va)), inf_strict_card(r_term, vb))


def division_cas_petit_cible(a="a", b="b"):
    """(Card a < b) ⇒ (∃q)(∃r)(b·q + r = Card a  et  r < b)."""
    va, vb = var(a), var(b)
    corps = existe(_Q, existe(_R, _phi(vb, va, var(_Q), var(_R))))
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    return impl(inf_strict_card(cardinal(va), vb), corps)


# @livre Ch.III §5.6 Th.1 | E III.39 L.10-11 | PDF p.142
# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142
def division_cas_petit(a="a", b="b"):
    """⊢ (Card a < b) ⇒ (∃q)(∃r)(b·q + r = Card a et r < b).   (Th.1, cas a<b, CLOS.)"""
    va, vb = var(a), var(b)
    ca = cardinal(va)                                   # Card a  (le « r » témoin)
    vide = E.VIDE                                       # ∅ = 0   (le « q » témoin)

    # ── chaîne d'égalités : b·0 + Card a = Card a ────────────────────────────────
    e1 = produit_cardinal_zero(b)                       # ⊢ Card(B×∅) = Card(∅)
    V1 = somme_cardinale_binaire(var("w"), ca)          # contexte  Card( w ⊔ Card a )
    c1 = N.modus_ponens(e1, congruence_terme(
        cardinal(E.produit(vb, vide)), cardinal(vide), V1))
    e2 = cardinal_vide_egale_vide()                     # ⊢ Card(∅) = ∅
    c2 = N.modus_ponens(e2, congruence_terme(cardinal(vide), vide, V1))
    e3 = instancie(N.generalisation("B", somme_cardinale_zero_neutre("B")), ca)
    e4 = _cardinal_idempotent_t(va)                     # ⊢ Card(Card a) = Card a
    eq = composer_egalites(composer_egalites(composer_egalites(c1, c2), e3), e4)
    #    ⊢ Card( Card(B×∅) ⊔ Card a ) = Card a   —  c.-à-d.  b·0 + Card a = Card a

    # ── conjonction avec l'ordre, puis les deux S5 (r := Card a, q := ∅) ─────────
    H = inf_strict_card(ca, vb)
    conj = conjonction_intro(eq, N.assume(H))           # {H} ⊢ (b·0 + Card a = Card a) et (Card a < b)
    Rr = _phi(vb, va, vide, var(_R))
    exr = N.modus_ponens(conj, N.s5(Rr, ca, _R))        # {H} ⊢ (∃r) φ(∅, r)
    Rq = existe(_R, _phi(vb, va, var(_Q), var(_R)))
    exq = N.modus_ponens(exr, N.s5(Rq, vide, _Q))       # {H} ⊢ (∃q)(∃r) φ(q, r)
    return N.loi_deduction(H, exq)                      # ⊢ H ⇒ (∃q)(∃r) φ   (CLOS)


__all__ = ["division_cas_petit", "division_cas_petit_cible"]
