"""§III.3 / §III.6.3 — PONT couple→valeur :  injectif_graphe → injective_dans.

CONTEXTE.  L'inductivité de Hessenberg/Zorn (`union_chaine_est_bijection`,
`ensembles_chaine_frame_membership.py`) ne livre, EN AMONT, que la forme
COUPLE-NATIVE `injectif_graphe(F) = (∀a,b,c)((a,c),(b,c)∈F ⇒ a=b)`
(`ensembles_recollement_famille_injectif.py`), alors que `est_bijection_de`
exige le conjoint VALEUR-NIVEAU
`injective_dans(F,A) = (∀u,u')((u∈A et u'∈A et F(u)=F(u')) ⇒ u=u')`.  Le pont
couple→valeur manquait (porté en hypothèse honnête) — c'était l'obstruction
« couple→valeur » signalée dans les docstrings amont.

Ce module FERME ce pont via le chunk déjà clos `couple_donne_valeur`
(`ensembles_c60_final.py`) : { est_fonctionnel(p), (a,b)∈p } ⊢ b=valeur(p,a).
Aucun mur de capture de τ-valeur : on ne CONSTRUIT jamais la valeur, on l'IDENTIFIE
à un témoin de couple.

ROUTE (sur le DOMAINE A=dom F) :
  Soit u,u'∈dom F avec F(u)=F(u').  Par AXIOME_DOM (sens avant) :
    (∃v)(u,v)∈F  et  (∃v')(u',v')∈F.  On élimine les témoins v, v'.
  `couple_donne_valeur` (sous est_fonctionnel F) : v=F(u), v'=F(u').  Avec
  F(u)=F(u') on a v=v'.  Donc (u,v)∈F et (u',v)∈F (même image v).  Enfin
  `injectif_graphe(F)` instancié en (u,u',v) donne u=u'.  ∎

THÉORÈME (CLOS, hyps HONNÊTES ; theorie=22) :
  • injectif_graphe_implique_injective_dans
      { est_fonctionnel(F), injectif_graphe(F) } ⊢ injective_dans(F, dom F).

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final import couple_donne_valeur
from bourbaki.cardinaux.ensembles_recollement_famille_injectif import injectif_graphe


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _u_dans_dom_avant(vF, vu, ywit):
    """De ⊢ u∈dom F [hyp] déduit ⊢ (∃ywit)((u,ywit)∈F) (AXIOME_DOM sens avant +
    α-renomme le binder 'y' canonique vers un témoin frais)."""
    h = N.assume(appartient(vu, E.dom(vF)))                    # u∈dom F   [HONNÊTE]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vF), vu)                 # u∈dom F ⇔ (∃y)((u,y)∈F)
    ex0 = N.modus_ponens(h, equivalence_avant(car))            # (∃y)((u,y)∈F)
    ex = N.modus_ponens(ex0, equivalence_avant(alpha_existe(
        "y", ywit, appartient(E.couple(vu, var("y")), vF))))   # (∃ywit)((u,ywit)∈F)
    return ex


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PONT couple→valeur — injectif_graphe(F) ⇒ injective_dans(F, dom F).
# ════════════════════════════════════════════════════════════════════════════
def injectif_graphe_implique_injective_dans(F="Fpont"):
    """{ est_fonctionnel(F), injectif_graphe(F) } ⊢ injective_dans(F, dom F).
                                                          [2 hyps HONNÊTES].

    🎯 Le PONT couple→valeur.  La forme COUPLE-NATIVE `injectif_graphe` (deux
    antécédents d'une même image c coïncident) implique la forme VALEUR-NIVEAU
    `injective_dans` (deux antécédents de même valeur coïncident), SUR LE DOMAINE.
    Via `couple_donne_valeur` (identification valeur=témoin de couple), sans aucun
    mur de capture de τ-valeur.

    Les deux hypothèses sont HONNÊTES (jamais postulées vraies ; conclusion ∉ hyps ;
    theorie=22), déchargées par loi_deduction."""
    vF = _t(F)
    A = E.dom(vF)
    vu, vup = var("u"), var("up")

    h_fonc = N.assume(E.est_fonctionnel(vF))                   # est_fonctionnel(F) [HONNÊTE]
    h_inj = N.assume(injectif_graphe(vF))                      # injectif_graphe(F) [HONNÊTE]

    # prémisse de injective_dans : (u∈A et u'∈A) et F(u)=F(u')
    prem = et(et(appartient(vu, A), appartient(vup, A)),
              egal(E.valeur(vF, vu), E.valeur(vF, vup)))
    hyp = N.assume(prem)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(hyp))   # u∈dom F
    up_in = conjonction_elim_droite(conjonction_elim_gauche(hyp))  # u'∈dom F
    val_eq = conjonction_elim_droite(hyp)                          # F(u)=F(u')
    cible = egal(vu, vup)

    # (∃v)(u,v)∈F  et  (∃v')(u',v')∈F  (témoins frais distincts)
    # on doit RE-déduire les appartenances au dom à partir de hyp (non d'assume neuf)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_u = instancie(instancie(ax_dom, vF), vu)
    ex_u0 = N.modus_ponens(u_in, equivalence_avant(car_u))         # (∃y)((u,y)∈F)
    ex_u = N.modus_ponens(ex_u0, equivalence_avant(alpha_existe(
        "y", "vpont", appartient(E.couple(vu, var("y")), vF))))    # (∃v)((u,v)∈F)
    car_up = instancie(instancie(ax_dom, vF), vup)
    ex_up0 = N.modus_ponens(up_in, equivalence_avant(car_up))      # (∃y)((u',y)∈F)
    ex_up = N.modus_ponens(ex_up0, equivalence_avant(alpha_existe(
        "y", "vppont", appartient(E.couple(vup, var("y")), vF))))  # (∃v')((u',v')∈F)

    vv, vvp = var("vpont"), var("vppont")
    cuv = E.couple(vu, vv)                                         # (u,v)
    cupvp = E.couple(vup, vvp)                                     # (u',v')

    # ── corps des témoins v, v' ──────────────────────────────────────────────
    Hv = N.assume(appartient(cuv, vF))                            # (u,v)∈F
    Hvp = N.assume(appartient(cupvp, vF))                          # (u',v')∈F

    # couple_donne_valeur : sous {func F, (u,v)∈F} ⊢ v=F(u) ; idem v'=F(u')
    cdv_u = couple_donne_valeur(vF, vu, vv)                        # v=valeur(F,u)
    cdv_up = couple_donne_valeur(vF, vup, vvp)                     # v'=valeur(F,u')

    # v = F(u) = F(u') = v'  → v=v'
    Fu, Fup = E.valeur(vF, vu), E.valeur(vF, vup)
    v_eq_Fup = composer_egalites(cdv_u, val_eq)                   # v=F(u') (de v=F(u), F(u)=F(u'))
    # F(u')=v' (sym de cdv_up : v'=F(u'))
    Fup_eq_vp = N.modus_ponens(cdv_up, symetrie(vvp, Fup))        # F(u')=v'
    v_eq_vp = composer_egalites(v_eq_Fup, Fup_eq_vp)             # v=v'

    # (u',v')∈F  ⇒  (u',v)∈F  :  réécrit v' en v dans l'appartenance via S6.
    # R{w} := (u',w)∈F ;  de v=v' on tire ((u',v)∈F) ⇔ ((u',v')∈F).
    s6_mem = N.modus_ponens(
        v_eq_vp, N.s6(vv, vvp, "w", appartient(E.couple(vup, var("w")), vF)))
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    upv_in = N.modus_ponens(Hvp, equivalence_arriere(s6_mem))     # (u',v)∈F
    # injectif_graphe(F) instancié en (a:=u, b:=u', c:=v) : ((u,v)∈F et (u',v)∈F) ⇒ u=u'
    inj_uuv = instancie(instancie(instancie(h_inj, vu), vup), vv)
    u_eq_up = N.modus_ponens(conjonction_intro(Hv, upv_in), inj_uuv)  # u=u'  [Hv,Hvp,hyp,...]

    # ── élimine les témoins v', v ────────────────────────────────────────────
    wit_vp = N.loi_deduction(appartient(cupvp, vF), u_eq_up)      # (u',v')∈F ⇒ u=u'
    after_vp = N.modus_ponens(ex_up, existe_elimination(wit_vp, "vppont"))  # u=u'  [Hv,hyp,...]
    wit_v = N.loi_deduction(appartient(cuv, vF), after_vp)        # (u,v)∈F ⇒ u=u'
    after_v = N.modus_ponens(ex_u, existe_elimination(wit_v, "vpont"))   # u=u'  [hyp,...]

    impl_uup = N.loi_deduction(prem, after_v)                    # prem ⇒ u=u'
    res = N.generalisation("u", N.generalisation("up", impl_uup))

    cible_th = E.injective_dans(vF, A)
    assert res.conclusion == cible_th, "injectif_graphe_implique_injective_dans : ≠ injective_dans(F,dom F)"
    assert E.est_fonctionnel(vF) in res.hypotheses, "pont : est_fonctionnel absente"
    assert injectif_graphe(vF) in res.hypotheses, "pont : injectif_graphe absente"
    assert res.conclusion not in res.hypotheses, "pont : VACUOUS"
    return res


__all__ = ["injectif_graphe_implique_injective_dans"]
