"""§III.6.1 (E.III.45, remarque Déf. 1) — « TOUT CARDINAL FINI EST ≤ TOUT CARDINAL
INFINI ».  La clé manquante des descentes de Hessenberg (2𝔟≤𝔟, 3𝔟≤𝔟).

🎯 CIBLES :

  (1) fini_inf_egal_infini(n,b) :
        ( Fini(n) et est_cardinal(n) et est_cardinal(𝔟) et est_infini(𝔟) )
        ⇒  n ≤ 𝔟.
      « Tout cardinal FINI est ≤ tout cardinal INFINI » (E.III.45).  INCONDITIONNEL.

  (2) deux_inf_egal_infini(b) :  ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ 2 ≤ 𝔟
      trois_inf_egal_infini(b) : ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ 3 ≤ 𝔟
      (instances n=2=Fini(2), n=3=Fini(3) — le verrou EXACT des descentes Hessenberg).

ROUTE (anti-vacuous, rien postulé).  Par COMPARABILITÉ DES CARDINAUX
(`comparabilite_cardinaux`, ZORN, inconditionnel) : n ≤ 𝔟  OU  𝔟 ≤ n.
  • si n ≤ 𝔟 : c'est la conclusion ;
  • si 𝔟 ≤ n : 𝔟 ≤ n cardinal FINI ⇒ 𝔟 FINI (`fini_downward_garde_thm`, la
    downward-closure de Fini, pfu déchargée par `predecesseur_fini_universel_preuve`,
    garde est_cardinal(𝔟) = l'hypothèse) — ce qui CONTREDIT est_infini(𝔟)=¬Fini(𝔟).
    Explosion (de Fini 𝔟 et ¬Fini 𝔟, via S2) ⇒ n ≤ 𝔟.
Élimination de ∨ par `cas`.

INVARIANT : theorie_ensembles() = 22.  Aucun axiome nouveau.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, ou, non, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, est_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini

from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import fini_downward_garde_thm
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import fini_downward
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_comparabilite import comparabilite_cardinaux

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — la descente : { est_cardinal(𝔟) } ⊢ (𝔟 ≤ n et Fini n) ⇒ Fini 𝔟.
#  (downward-closure de Fini pour le cardinal 𝔟, pfu déchargée — CLOSE sauf garde.)
# ════════════════════════════════════════════════════════════════════════════
def _descente_fini(vb, vn):
    """{ est_cardinal(𝔟) } ⊢ fini_downward(𝔟, n) = ( 𝔟 ≤ n et Fini n ) ⇒ Fini 𝔟.

    fini_downward_garde_thm(𝔟) ⊢ (∀x)fini_downward(𝔟,x) [pfu, est_cardinal(𝔟)] ;
    pfu déchargé par predecesseur_fini_universel_preuve() ; instancié à x:=n.
    SEULE hyp survivante : est_cardinal(𝔟)."""
    fdg = fini_downward_garde_thm(vb)                  # (∀x)fini_downward(𝔟,x) [pfu, est_card(𝔟)]
    fdg = _cut(fdg, predecesseur_fini_universel_preuve().conclusion,
               predecesseur_fini_universel_preuve())   # pfu déchargé
    reste = list(fdg.hypotheses)
    assert len(reste) == 1 and reste[0] == est_cardinal(vb), \
        f"_descente_fini : hyps résiduelles inattendues : {reste}"
    fd_at_n = instancie(fdg, vn)                       # fini_downward(𝔟,n)
    assert fd_at_n.conclusion == fini_downward(vb, vn), \
        "_descente_fini : instanciation ≠ fini_downward(𝔟,n)"
    return fd_at_n


# ════════════════════════════════════════════════════════════════════════════
#  (1)  fini_inf_egal_infini :  tout cardinal FINI ≤ tout cardinal INFINI.
# ════════════════════════════════════════════════════════════════════════════
def fini_inf_egal_infini_enonce(n="n", b="b"):
    vn, vb = _t(n), _t(b)
    hyp = et(et(et(est_fini(vn), est_cardinal(vn)), est_cardinal(vb)), est_infini(vb))
    return impl(hyp, inf_egal_card(vn, vb))


def fini_inf_egal_infini(n="n", b="b"):
    """🎯 ⊢ ( Fini(n) et est_cardinal(n) et est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ n ≤ 𝔟.

    « Tout cardinal fini est ≤ tout cardinal infini » (E.III.45).  INCONDITIONNEL.
    Route comparabilité (n≤𝔟 OU 𝔟≤n) + descente (𝔟≤n cardinal fini ⇒ Fini 𝔟,
    contredisant est_infini 𝔟).  theorie=22 ; conclusion ∉ hyps."""
    vn, vb = _t(n), _t(b)
    cible = inf_egal_card(vn, vb)                       # n ≤ 𝔟
    le_nb = inf_egal_card(vn, vb)
    le_bn = inf_egal_card(vb, vn)

    hyp = et(et(et(est_fini(vn), est_cardinal(vn)), est_cardinal(vb)), est_infini(vb))
    H = N.assume(hyp)
    h_fini_n = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(H)))  # Fini n
    h_card_b = conjonction_elim_droite(conjonction_elim_gauche(H))   # est_cardinal(𝔟)
    h_inf_b = conjonction_elim_droite(H)                            # est_infini(𝔟) = ¬Fini(𝔟)
    assert h_inf_b.conclusion == est_infini(vb)
    notfini_b = h_inf_b                                              # ¬Fini(𝔟)

    # disjonction de comparabilité : n ≤ 𝔟  OU  𝔟 ≤ n   (CLOS, ZORN).
    # Construite sur des noms d'ensembles SÛRS (≠ binders internes de Zorn), puis
    # TRANSPORTÉE aux termes vn,vb (généralisation + instanciation — capture-safe).
    disj_raw = comparabilite_cardinaux("Xcmp", "Ycmp")
    assert disj_raw.est_clos, "comparabilité non close"
    disj_gen = N.generalisation("Xcmp", N.generalisation("Ycmp", disj_raw))
    disj = instancie(instancie(disj_gen, vn), vb)
    assert disj.conclusion == ou(le_nb, le_bn), \
        f"comparabilité : disjonction inattendue\n{disj.conclusion}\nvs\n{ou(le_nb, le_bn)}"

    # branche A : n ≤ 𝔟 ⇒ n ≤ 𝔟  (trivial)
    brA = N.loi_deduction(le_nb, N.assume(le_nb))

    # branche B : 𝔟 ≤ n ⇒ n ≤ 𝔟  (par explosion)
    h_le_bn = N.assume(le_bn)                                       # 𝔟 ≤ n
    desc = _descente_fini(vb, vn)                                   # (𝔟≤n et Fini n)⇒Fini 𝔟 [est_card(𝔟)]
    desc = _cut(desc, est_cardinal(vb), h_card_b)                   # garde est_card(𝔟) déchargée par hyp
    fini_b = N.modus_ponens(conjonction_intro(h_le_bn, h_fini_n), desc)   # Fini 𝔟
    assert fini_b.conclusion == est_fini(vb)
    # explosion : de ¬Fini(𝔟) et Fini(𝔟) déduire n ≤ 𝔟.
    #   S2(¬Fini 𝔟, n≤𝔟) : ¬Fini 𝔟 ⇒ (¬Fini 𝔟 ∨ (n≤𝔟)) = (Fini 𝔟 ⇒ n≤𝔟)
    imp_fini_cible = N.modus_ponens(notfini_b, N.s2(non(est_fini(vb)), cible))  # Fini 𝔟 ⇒ n≤𝔟
    assert imp_fini_cible.conclusion == impl(est_fini(vb), cible)
    cible_B = N.modus_ponens(fini_b, imp_fini_cible)               # n ≤ 𝔟
    assert cible_B.conclusion == cible
    brB = N.loi_deduction(le_bn, cible_B)                          # 𝔟≤n ⇒ n≤𝔟

    res_cible = cas(disj, brA, brB)                               # n ≤ 𝔟  [hyp + est_card(𝔟)]
    assert res_cible.conclusion == cible

    res = N.loi_deduction(hyp, res_cible)
    assert res.conclusion == fini_inf_egal_infini_enonce(n, b), "conclusion ≠ énoncé"
    assert res.conclusion not in res.hypotheses, "fini_inf_egal_infini : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2)  Instances n=2, n=3 : 2 ≤ 𝔟 et 3 ≤ 𝔟 pour 𝔟 infini.
# ════════════════════════════════════════════════════════════════════════════
def _instance_n(fini_n_thm, valeur_terme, b="b"):
    """De ⊢ Fini(n_0) (terme concret n_0) déduit
       ⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ n_0 ≤ 𝔟.

    Fini(n_0) = est_fini(n_0) = ( est_cardinal(n_0) et n_0≠n_0+1 ) fournit le 1er ET
    le 2e conjoint de l'antécédent général ; les 3e/4e (est_cardinal 𝔟, est_infini 𝔟)
    sont l'hypothèse honnête."""
    vb = _t(b)
    n0 = valeur_terme
    assert fini_n_thm.conclusion == est_fini(n0), "Fini(n_0) : forme inattendue"
    card_n0 = conjonction_elim_gauche(fini_n_thm)        # est_cardinal(n_0)

    gen = fini_inf_egal_infini(n0, vb)                   # (Fini n0 et card n0 et card 𝔟 et inf 𝔟)⇒n0≤𝔟
    hyp2 = et(est_cardinal(vb), est_infini(vb))
    H = N.assume(hyp2)
    card_b = conjonction_elim_gauche(H)
    inf_b = conjonction_elim_droite(H)
    ante = conjonction_intro(conjonction_intro(conjonction_intro(
        fini_n_thm, card_n0), card_b), inf_b)
    le = N.modus_ponens(ante, gen)                       # n0 ≤ 𝔟
    assert le.conclusion == inf_egal_card(n0, vb)
    res = N.loi_deduction(hyp2, le)
    assert res.conclusion == impl(hyp2, inf_egal_card(n0, vb))
    assert res.conclusion not in res.hypotheses, "_instance_n : VACUOUS"
    return res


def deux_inf_egal_infini(b="b"):
    """🎯 ⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ 2 ≤ 𝔟.   (n=2, Fini(2).)"""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import fini_deux
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import DEUX
    return _instance_n(fini_deux(), DEUX, b)


def trois_inf_egal_infini(b="b"):
    """🎯 ⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ 3 ≤ 𝔟.   (n=3, Fini(3).)"""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_trois_quatre import fini_trois
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import TROIS
    return _instance_n(fini_trois(), TROIS, b)


__all__ = [
    "fini_inf_egal_infini_enonce", "fini_inf_egal_infini",
    "deux_inf_egal_infini", "trois_inf_egal_infini",
]
