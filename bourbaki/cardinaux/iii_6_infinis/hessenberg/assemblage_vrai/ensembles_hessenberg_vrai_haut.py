"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : ASSEMBLAGE HAUT (« vrai »),
montage final NON vacuous au-dessus de la CHAÎNE D'EXTENSION VRAIE
(`ensembles_hessenberg_chaine_vraie`) qui DÉRIVE le lock Z=S₀ par maximalité.

TASK B-finish — `phi1_bijection_moins` : prend `phi1_bijection_derivee` (6 hyps) et
DÉCHARGE les résidus MÉCANIQUES dischargeables depuis les deux hyps-bijection
HONNÊTES (bij0 = est_bijection_de(φ₀,S₀²,S₀), bijp = est_bijection_de(ψ,F,U)) :
  • hyp `imgφ₀∪imgψ = Z` (= S₀∪U) — image(φ₀,domφ₀)=S₀ (bij0) + image(ψ,domψ)=U
    (bijp) + réflexivité S₀∪U=Z, congruence de la réunion.

RESTENT (résidus GÉNUINEMENT géométriques, jamais postulés, lock ABSENT) :
  • bij0, bijp (les deux bijections honnêtes — bijp sera réalisée par cadre_bijection),
  • dom-disjointness (dom φ₀ ∩ dom ψ = ∅),
  • image-disjointness (img φ₀ ∩ img ψ = ∅),
  • la SET-IDENTITY domaine `(S₀×S₀) ∪ F⊔ = Z²` où F⊔ = cadre_ensemble en
    SOMME-DISJOINTE (≠ réunion).  ⚠️ BLOCKER ARCHITECTURAL documenté : cette identité
    N'EST PAS égale à la forme réunion prouvée close par `s0sq_cadre_reunion_egale_carre`
    (somme_disjointe(A,B)=(A×{0})∪(B×{1}) ≠ reunion(A,B)) ; la décharger demande de
    RE-CÂBLER ψ pour domaine = frame en RÉUNION (changement d'architecture de
    `cadre_ensemble`/`phi_etendue_bijection`), HORS scope mécanique.

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; le lock
`reunion(S₀,U)=S₀` n'est JAMAIS une hypothèse.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, non, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.cardinaux.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import phi1_bijection_derivee
from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import cadre_ensemble


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _image_sur_dom(bij, vF, src, tgt):
    """{ est_bijection_de(F,src,tgt) } ⊢ image(F, dom F) = tgt.

    De bij : dom(F)=src [gauche-droite] et image(F,src)=tgt [droite-droite].
    On réécrit src → dom F dans image(F,src)=tgt via S6 (src=dom F symétrisé)."""
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(bij))   # dom F = src
    img_eq = conjonction_elim_droite(conjonction_elim_droite(bij))   # image(F,src) = tgt
    src_eq_dom = N.modus_ponens(dom_eq, symetrie(E.dom(vF), src))    # src = dom F
    s6 = N.s6(src, E.dom(vF), "wimgd", egal(E.image(vF, var("wimgd")), tgt))
    return N.modus_ponens(img_eq, equivalence_avant(
        N.modus_ponens(src_eq_dom, s6)))                            # image(F,domF) = tgt


def phi1_bijection_moins(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """phi1_bijection_derivee, hyp `imgφ₀∪imgψ=Z` DÉCHARGÉE depuis bij0/bijp.

    ⊢ est_bijection_de(φ₀∪ψ, Z×Z, Z) sous les RÉSIDUS HONNÊTES restants (bij0, bijp,
    dom/img disjointness, set-identity domaine).  Le lock reste ABSENT.  theorie=22."""
    vphi0, vpsi, vS, vU = _t(phi0), _t(psi), _t(S), _t(U)
    SxS = E.produit(vS, vS)
    F = cadre_ensemble(S, U)
    Z = E.reunion(vS, vU)

    base = phi1_bijection_derivee(E_set, phi0, psi, S, U)

    # les deux bijections honnêtes (déjà hyps de base)
    bij0 = N.assume(est_bijection_de(vphi0, SxS, vS))
    bijp = N.assume(est_bijection_de(vpsi, F, vU))

    # image(φ₀,domφ₀)=S₀ ; image(ψ,domψ)=U
    imgphi_eq = _image_sur_dom(bij0, vphi0, SxS, vS)         # image(φ₀,domφ₀)=S₀
    imgpsi_eq = _image_sur_dom(bijp, vpsi, F, vU)            # image(ψ,domψ)=U

    imgG = E.image(vphi0, E.dom(vphi0))
    imgH = E.image(vpsi, E.dom(vpsi))
    # imgG∪imgH = S₀∪imgH  (réécrire gauche)  puis = S₀∪U  (réécrire droite)
    cong_g = N.modus_ponens(imgphi_eq, congruence_terme(
        imgG, vS, E.reunion(var("w"), imgH)))               # imgG∪imgH = S₀∪imgH
    cong_d = N.modus_ponens(imgpsi_eq, congruence_terme(
        imgH, vU, E.reunion(vS, var("w"))))                 # S₀∪imgH = S₀∪U
    img_union_eq = composer_egalites(cong_g, cong_d)        # imgG∪imgH = S₀∪U = Z
    assert img_union_eq.conclusion == egal(E.reunion(imgG, imgH), Z), \
        f"phi1_bijection_moins : img-union forme inattendue\n{img_union_eq.conclusion}"

    hyp5 = egal(E.reunion(imgG, imgH), Z)
    assert hyp5 in base.hypotheses, "phi1_bijection_moins : hyp5 absente de base"
    res = N.modus_ponens(img_union_eq, N.loi_deduction(hyp5, base))

    cible = est_bijection_de(E.reunion(vphi0, vpsi), E.produit(Z, Z), Z)
    assert res.conclusion == cible, \
        f"phi1_bijection_moins : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert egal(Z, vS) not in res.hypotheses, "phi1_bijection_moins : LOCK présent !"
    assert res.conclusion not in res.hypotheses, "phi1_bijection_moins : VACUOUS"
    # hyp5 effectivement déchargée
    assert hyp5 not in res.hypotheses, "phi1_bijection_moins : hyp5 NON déchargée"
    return res


__all__ = ["phi1_bijection_moins"]
