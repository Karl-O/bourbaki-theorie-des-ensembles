"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : ÉCHELLE FINALE d'élimination des
témoins de la chaîne de contradiction PLATE (`chaine_falsum_plat`), jusqu'au théorème
a²=a GÉNUINEMENT NON-VACUUX, conclusion E-SEULE.

🎯 CONTEXTE.  Le MUR architectural est TOMBÉ : `chaine_falsum_plat`
(`ensembles_cadre_plat.py`) ⊢ ¬(uwit∈Ucadre) sous 11 hyps HONNÊTES (la set-identity
domaine `S₀²∪F=Z²` DÉCHARGÉE par s0sq, le lock reunion(S₀,U)=S₀ ABSENT), avec uwit∈Ucadre
parmi les hyps (= ⊥).  Variables libres ⊂ {E,S0,Ucadre,phi0,psi,uwit}.  Il ne reste que
l'échelle d'élimination des témoins ψ, uwit, Ucadre, puis le branchement maximal :

  P5a `negation_strict_sous_temoins_UF_plat`  — ÉLIMINE ψ et uwit (miroir EXACT de
      `negation_strict_sous_temoins_UF`, B1, mais sur le cadre PLAT F_plain).  Le ∃ψ est
      déchargé par `cadre_plat_bijection` (P3), le ∃u par `U_non_vide`.  ⊢ marqueur
      FALSUM ψ/uwit-FREE (¬(E=E)) sous hyps honnêtes sans ψ ni uwit.

  P5b `negation_strict_sous_maximal`  — ÉLIMINE Ucadre (DÉBLOQUÉ : la set-identity
      domaine GONE) via `existe_sous_ensemble_cardinal_transporte` (∃Ucadre⊂E∖S₀,
      Card Ucadre=Card S₀).  ⊢ ¬(Card S₀<Card E) sous la SEULE maximal-data (+ résidus
      arithmétiques honnêtes E-niveau).

  P5c `hessenberg_a_carre_egal_a_REEL`  — branche P5b + `card_inclus_inf_egal` (S₀⊂E ⇒
      Card S₀≤Card E) + `hessenberg_a_carre_egal_a` (Card S₀=Card E ⇒ a²=a) DANS la portée
      du maximal, puis `unpack_maximal` ⇒ conclusion E-SEULE == enonce_hessenberg(E).

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; lock ABSENT ; les
hyps résiduelles restent HONNÊTES (satisfiables, vraies dans l'argument de Zorn E.III.48).
Noyau INTACT ; NOUVEAU module.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, appartient, inclus,
    libres_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, est_bijection_de, inf_egal_card, inf_strict_card,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _marqueur_faux(E_set="E"):
    """Marqueur FALSUM ψ/uwit/Ucadre-FREE : ¬(E=E) (cible ex falso)."""
    vE = _t(E_set)
    return non(egal(vE, vE))


def _falsum_vers_marqueur(chaine, E_set, U, u):
    """De `chaine` ⊢ ¬(u∈U) avec u∈U ∈ hyps, déduit ⊢ ¬(E=E) (ex falso), mêmes hyps."""
    vU, vu, vE = _t(U), _t(u), _t(E_set)
    u_in_U = appartient(vu, vU)
    assert chaine.conclusion == non(u_in_U)
    assert u_in_U in chaine.hypotheses
    marqueur = _marqueur_faux(E_set)
    # ex falso : ¬(u∈U) ∨ marqueur (= u∈U ⇒ marqueur), puis mp(u∈U).
    h_u = N.assume(u_in_U)
    disj = N.modus_ponens(chaine, N.s2(non(u_in_U), marqueur))  # ¬(u∈U) ∨ marqueur
    faux = N.modus_ponens(h_u, disj)                            # marqueur
    assert faux.conclusion == marqueur
    return faux


# ════════════════════════════════════════════════════════════════════════════
#  P5a — élimine ψ puis uwit de la chaîne PLATE (miroir de B1).
# ════════════════════════════════════════════════════════════════════════════
def negation_strict_sous_temoins_UF_plat(E_set="E", phi0="phi0", psi="psi", S="S0",
                                         U="Ucadre", u="uwit"):
    """P5a — ψ et uwit ÉLIMINÉS de la chaîne PLATE (`chaine_falsum_plat`).

    ⊢ ¬(E=E)  (marqueur FALSUM, ψ/uwit-FREE)  sous hyps HONNÊTES sans ψ ni uwit.

    🎯 Miroir EXACT de `negation_strict_sous_temoins_UF` (B1) mais sur le cadre PLAT
    F_plain = cadre_plat(S₀,U) (et non cadre_ensemble taggé).  On part de
    `chaine_falsum_plat` (⊢ ¬(uwit∈Ucadre) sous uwit∈Ucadre = ⊥), on en tire le marqueur
    ¬(E=E) (ex falso), puis :
      • on rend les 3 résidus ψ-géométriques (img-disj, img-cov, dom-disj) ψ-FREE sous
        l'hyp [bij]=est_bijection_de(ψ,F_plain,U) (réutilise `_bij_dom_image`,
        `_prouver_residu_depuis_psifree` de stepb2) ;
      • ψ : loi_deduction([bij]) + existe_elimination(·,"psi"), le ∃ψ déchargé par
        `cadre_plat_bijection` (P3, equipotent(F_plain,U)=(∃ψ)bij), α-renommé (∃F)→(∃ψ) ;
      • uwit : loi_deduction(u∈U) + existe_elimination(·,"uwit"), le ∃u déchargé par
        `U_non_vide` (Card U≠0 ⇒ U≠∅ ⇒ (∃u)u∈U).
    Aucune hyp résiduelle ne mentionne ψ ni uwit (ACCEPTANCE).  Lock ABSENT.  theorie=22.
    """
    from bourbaki.cardinaux.ensembles_cadre_plat import chaine_falsum_plat, cadre_plat
    from bourbaki.cardinaux.ensembles_cadre_plat import cadre_plat_bijection
    from bourbaki.cardinaux.ensembles_hessenberg_stepb2 import (
        _bij_dom_image, _prouver_residu_depuis_psifree, _non_vide_existe_element,
    )
    from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import U_non_vide

    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU, vu = _t(S), _t(U), _t(u)
    F = cadre_plat(S, U)                                   # F_plain (réunion PLATE)
    marqueur = _marqueur_faux(E_set)

    # ── 0. chaîne PLATE ⊢ ¬(uwit∈Ucadre) ⇒ marqueur ¬(E=E) (ex falso) ─────────
    chaine = chaine_falsum_plat(E_set, phi0, S, U, psi, u)
    cur = _falsum_vers_marqueur(chaine, E_set, U, u)       # ⊢ marqueur (mêmes hyps)
    assert cur.conclusion == marqueur

    # ── 1. résidus ψ rendus ψ-free sous [bij] ────────────────────────────────
    h_bij, dom_eq_F, img_dom_eq_U = _bij_dom_image(vpsi, F, vU)
    bij = h_bij.conclusion
    assert bij == est_bijection_de(vpsi, F, vU)
    domphi0 = E.dom(vphi0)
    imgphi0 = E.image(vphi0, domphi0)
    img_psi = E.image(vpsi, E.dom(vpsi))
    Z = E.reunion(vS, vU)
    uu = var("u")

    residu_imgdisj = egal(E.intersection(imgphi0, img_psi), E.VIDE)
    residu_imgcov = egal(E.reunion(imgphi0, img_psi), Z)
    residu_domdisj = pourtout("u", non(et(appartient(uu, domphi0),
                                          appartient(uu, E.dom(vpsi)))))
    pr_imgdisj = _prouver_residu_depuis_psifree(residu_imgdisj, [img_dom_eq_U])
    pr_imgcov = _prouver_residu_depuis_psifree(residu_imgcov, [img_dom_eq_U])
    pr_domdisj = _prouver_residu_depuis_psifree(residu_domdisj, [dom_eq_F])

    for pr in (pr_imgdisj, pr_imgcov, pr_domdisj):
        c = pr.conclusion
        assert c in cur.hypotheses, f"P5a : résidu ψ absent des hyps\n{c}"
        cur = N.modus_ponens(pr, N.loi_deduction(c, cur))

    # ── 2. élimine ψ : (∃ψ)bij ⇒ marqueur,  ∃ψ fourni par cadre_plat_bijection (P3) ──
    assert psi not in libres_f(marqueur)
    assert bij in cur.hypotheses, "P5a : [bij] absent avant élim ψ"
    imp_bij = N.loi_deduction(bij, cur)                   # bij(ψ,F,U) ⇒ marqueur
    imp_expsi = existe_elimination(imp_bij, psi)          # (∃ψ)bij ⇒ marqueur
    # cadre_plat_bijection : {5 gardes honnêtes} ⊢ equipotent(F,U) = (∃F)bij(F,F_plain,U).
    p3 = cadre_plat_bijection(S, U)                       # ⊢ (∃F)bij
    body_F = est_bijection_de(var("F"), F, vU)
    aeq = alpha_existe("F", psi, body_F)                  # (∃F)bij ⇔ (∃ψ)bij
    ex_psi = N.modus_ponens(p3, equivalence_avant(aeq))   # ⊢ (∃ψ)bij
    cur = N.modus_ponens(ex_psi, imp_expsi)               # ⊢ marqueur (ψ déchargé)

    # ── 3. élimine uwit : (∃u)u∈U ⇒ marqueur,  ∃u fourni par U_non_vide ──────
    u_in_U = appartient(vu, vU)
    assert u not in libres_f(marqueur)
    assert u_in_U in cur.hypotheses, "P5a : témoin u∈U absent avant élim uwit"
    imp_u = N.loi_deduction(u_in_U, cur)                  # u∈U ⇒ marqueur
    imp_exu = existe_elimination(imp_u, u)                # (∃u)u∈U ⇒ marqueur
    ex_u = _non_vide_existe_element(vU, u)                # U≠∅ ⇒ (∃u)(u∈U)
    nv = U_non_vide(U)                                    # {Card U≠Card∅} ⊢ U≠∅
    ex_u_thm = N.modus_ponens(nv, ex_u)                   # {Card U≠Card∅} ⊢ (∃u)u∈U
    cur = N.modus_ponens(ex_u_thm, imp_exu)               # ⊢ marqueur (uwit déchargé)

    # ── ACCEPTANCE : aucune hyp ne mentionne ψ ni uwit ───────────────────────
    for h in cur.hypotheses:
        bad = ({psi, u} & set(libres_f(h)))
        assert not bad, f"P5a : hyp mentionne {bad}\n{h}"
    lock = egal(E.reunion(vS, vU), vS)
    assert lock not in cur.hypotheses, "P5a : LOCK présent !"
    assert cur.conclusion == marqueur, "P5a : conclusion ≠ marqueur"
    return cur


__all__ = [
    "negation_strict_sous_temoins_UF_plat",
]
