"""§II.4 — Proposition 1 (E.II.4.1), DUAL INTERSECTION du reparamétrage surjectif.

La version RÉUNION  ⋃_{κ∈K} X_{φ(κ)} = ⋃_{ι∈I} X_ι  (sous φ:K→I surjective) est
déjà close dans `ensembles_chap2_props_restantes` (`reparam_reunion_egal_si_surjectif`).
Ici on ferme son DUAL pour l'INTERSECTION :

    ⋂_{κ∈K} X_{φ(κ)} = ⋂_{ι∈I} X_ι        (E.II.4, Prop. 1, formule duale)

sous les deux hypothèses FIDÈLES :
  • domaine     :  (∀κ)(κ∈K ⇒ φ(κ)∈I)
  • surjectivité:  (∀ι)(ι∈I ⇒ (∃κ)(κ∈K et φ(κ)=ι))

Caractérisation utilisée (AXIOME_INTER_FAM) : z∈⋂_{ι∈I}X_ι ⇔ (∀i)(i∈I⇒z∈X_i).

  • Sens ⊃ (⋂X_ι ⊂ ⋂Y_κ)  — n'utilise QUE le domaine :  z∈⋂X_ι donne, pour tout
    κ∈K, φ(κ)∈I donc z∈X_{φ(κ)}=Y_κ, d'où z∈⋂Y_κ.
  • Sens ⊂ (⋂Y_κ ⊂ ⋂X_ι)  — utilise la SURJECTIVITÉ : z∈⋂Y_κ ; pour ι∈I, ι=φ(κ)
    par surjectivité, donc z∈Y_κ=X_{φ(κ)}=X_ι ; d'où z∈⋂X_ι.

theorie_ensembles() INCHANGÉE (22 ax.). On réutilise l'infra `famille_reparam` /
`_val_reparam` du module union (mêmes familles reparamétrées, C54).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl,
                                       appartient, existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg,
    conjonction_elim_droite as cd, equivalence_avant, equivalence_arriere,
    instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee

from bourbaki.ensembles.ii_4_reunion_intersection.ensembles_chap2_props_restantes import (
    famille_reparam, _val_reparam, _inst_inter, _membre_eq, _sym)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §4.1 Prop.1 | E II.23 L.28-50 | PDF p.74
def reparam_inter_incluse(f="X", phi="phi", i="I", k="K"):
    """⊢ (∀κ)(κ∈K⇒φ(κ)∈I)  ⇒  ( ⋂_{ι∈I} X_ι ⊂ ⋂_{κ∈K} X_{φ(κ)} ).
       (E.II.4, Prop. 1 dual — sens « ⊃ », n'utilise QUE le domaine.)   [domaine]

    z∈⋂X_ι = (∀i)(i∈I⇒z∈X_i).  À κ fixé avec κ∈K, le domaine donne φ(κ)∈I, donc
    z∈X_{φ(κ)} (instance), et Y_κ=X_{φ(κ)} (déf. famille reparam) donne z∈Y_κ.
    D'où (∀κ)(κ∈K⇒z∈Y_κ) = z∈⋂Y_κ.  Inclusion repliée sur le liant FRESH « z »."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vz, vi = var("z"), var("i")
    fam_r = famille_reparam(vf, vphi)
    phii = E.valeur(vphi, vi)
    Yi = E.valeur_famille(fam_r, vi)
    Xphii = E.valeur_famille(vf, phii)
    interY = E.inter_famille(fam_r, vK)
    interX = E.inter_famille(vf, vI)

    # domaine fidèle (∀k)(k∈K⇒φ(k)∈I) ; on aligne le binder sur « i » (axiome INTER)
    dom_hyp = pourtout("k", impl(appartient(var("k"), vK),
                                 appartient(E.valeur(vphi, var("k")), vI)))
    hH = N.assume(dom_hyp)

    hL = N.assume(appartient(vz, interX))
    forall_iX = N.modus_ponens(hL, equivalence_avant(_inst_inter(vf, vI, vz)))  # (∀i)(i∈I⇒z∈X_i)
    # but : (∀i)(i∈K ⇒ z∈Y_i)   (binder « i » de l'axiome INTER sur ⋂Y_κ)
    hi = N.assume(appartient(vi, vK))                             # i∈K
    phii_in_I = N.modus_ponens(hi, instancie(hH, vi))            # φ(i)∈I
    z_Xphii = N.modus_ponens(phii_in_I, instancie(forall_iX, phii))  # z∈X_{φ(i)}
    # z∈X_{φ(i)} = z∈Y_i  (déf. famille reparam : Y_i=X_{φ(i)})
    z_Yi = N.modus_ponens(z_Xphii, equivalence_arriere(
        _membre_eq(Yi, Xphii, _val_reparam(vf, vphi, vi), vz)))   # z∈Y_i
    imp_i = N.loi_deduction(appartient(vi, vK), z_Yi)           # i∈K ⇒ z∈Y_i
    forall_kY = N.generalisation("i", imp_i)                    # (∀i)(i∈K⇒z∈Y_i)
    z_interY = N.modus_ponens(forall_kY, equivalence_arriere(_inst_inter(fam_r, vK, vz)))
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, interX), z_interY))
    return N.loi_deduction(dom_hyp, incl)


def _cible(f="X", phi="phi", i="I", k="K"):
    """L'énoncé visé :
       (domaine et surjectivité) ⇒ ⋂_{κ∈K}X_{φ(κ)} = ⋂_{ι∈I}X_ι."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vk, vi = var("k"), var("i")
    phik = E.valeur(vphi, vk)
    fam_r = famille_reparam(vf, vphi)
    interY = E.inter_famille(fam_r, vK)
    interX = E.inter_famille(vf, vI)
    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    return impl(et(dom_hyp, surj_hyp), egal(interY, interX))


# @livre Ch.II §4.1 Prop.1 | E II.23 L.28-50 | PDF p.74
def reparam_inter_egal_si_surjectif(f="X", phi="phi", i="I", k="K"):
    """{φ : K→I (∀κ∈K φ(κ)∈I)  et  φ surjective sur I (∀ι∈I ∃κ∈K φ(κ)=ι)}
        ⊢  ⋂_{κ∈K} X_{φ(κ)} = ⋂_{ι∈I} X_ι.   (E.II.4, Prop. 1 dual VERBATIM.)

    Le sens ⊃ est inconditionnel modulo le domaine (`reparam_inter_incluse`).
    Le sens ⊂ exige la SURJECTIVITÉ : z∈⋂Y_κ = (∀k)(k∈K⇒z∈Y_k) ; pour ι∈I,
    ι=φ(κ) pour un κ∈K (surjectivité), donc z∈Y_κ=X_{φ(κ)}=X_ι, d'où
    (∀i)(i∈I⇒z∈X_i)=z∈⋂X_ι.  CONDITIONNÉ aux deux hypothèses FIDÈLES, jamais
    postulé.  Sans surjectivité l'égalité est FAUSSE."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vz, vk, vi = var("z"), var("k"), var("i")
    fam_r = famille_reparam(vf, vphi)
    phik = E.valeur(vphi, vk)
    Yk = E.valeur_famille(fam_r, vk)
    Xphik = E.valeur_famille(vf, phik)
    Xi = E.valeur_famille(vf, vi)
    interY = E.inter_famille(fam_r, vK)
    interX = E.inter_famille(vf, vI)

    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    hyp = et(dom_hyp, surj_hyp)
    hH = N.assume(hyp)
    h_dom = cg(hH)
    h_surj = cd(hH)

    # ── ⊃ : ⋂X_ι ⊂ ⋂Y_κ  (décharge le domaine de reparam_inter_incluse) ──────
    incl_RL = N.modus_ponens(h_dom, reparam_inter_incluse(vf, vphi, vI, vK))

    # ── ⊂ : ⋂Y_κ ⊂ ⋂X_ι ─────────────────────────────────────────────────────
    hL = N.assume(appartient(vz, interY))
    forall_k = N.modus_ponens(hL, equivalence_avant(_inst_inter(fam_r, vK, vz)))  # (∀k)(k∈K⇒z∈Y_k)
    # but : (∀i)(i∈I ⇒ z∈X_i)
    hi = N.assume(appartient(vi, vI))                             # i∈I
    exk = N.modus_ponens(hi, instancie(h_surj, vi))             # (∃k)(k∈K et φ(k)=ι)
    bodyk = et(appartient(vk, vK), egal(phik, vi))
    hbk = N.assume(bodyk)
    k_in = cg(hbk)
    phik_eq_i = cd(hbk)                                          # φ(κ)=ι
    z_Yk = N.modus_ponens(k_in, instancie(forall_k, vk))         # z∈Y_κ
    # z∈Y_κ = z∈X_{φ(κ)}  (déf. famille reparam)
    z_Xphik = N.modus_ponens(z_Yk, equivalence_avant(
        _membre_eq(Yk, Xphik, _val_reparam(vf, vphi, vk), vz)))  # z∈X_{φ(κ)}
    # φ(κ)=ι  donne X_{φ(κ)}=X_ι  (Leibniz sur w ↦ z∈X_w)
    leibniz = N.modus_ponens(phik_eq_i, N.s6(phik, vi, "w",
                     appartient(vz, E.valeur_famille(vf, var("w")))))  # (z∈X_{φ(κ)})⇔(z∈X_ι)
    z_Xi = N.modus_ponens(z_Xphik, equivalence_avant(leibniz))   # z∈X_ι
    # éliminer le témoin κ (k non libre dans z∈X_ι : terme clos en i)
    imp_k = existe_elimination(N.loi_deduction(bodyk, z_Xi), "k")
    z_Xi_final = N.modus_ponens(exk, imp_k)                      # z∈X_ι  (hyps {surj, z∈⋂Y, i∈I})
    imp_i = N.loi_deduction(appartient(vi, vI), z_Xi_final)     # i∈I ⇒ z∈X_i
    forall_i = N.generalisation("i", imp_i)                     # (∀i)(i∈I⇒z∈X_i)
    z_interX = N.modus_ponens(forall_i, equivalence_arriere(_inst_inter(vf, vI, vz)))
    incl_LR = N.generalisation("z", N.loi_deduction(appartient(vz, interY), z_interX))

    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(interY, interX))
    return N.loi_deduction(hyp, egal_th)


__all__ = ["reparam_inter_incluse", "reparam_inter_egal_si_surjectif", "_cible"]
