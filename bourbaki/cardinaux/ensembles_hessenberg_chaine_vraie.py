"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : la CHAÎNE D'EXTENSION VRAIE
(NON vacuous) qui DÉRIVE le lock Z=S₀ via la maximalité, au lieu de le SUPPOSER.

🔴 MOTIVATION.  Le montage final on-main (`hessenberg_a_carre_egal_a`) est VACUUX :
il ASSUME le lock `reunion(S₀,U)=S₀` et le porte comme hypothèse contradictoire (avec
u∈U, U∩S₀=∅).  Ici on ASSEMBLE les pièces SAINES de `ensembles_frame_extension_finale`
(toutes individuellement closes, hyps satisfiables) dans le SENS de l'argument de
Bourbaki, de sorte que `extension_force_egalite` DÉRIVE Z=S₀ depuis la maximalité — il
n'est JAMAIS assumé.

Étapes (cf. RAPPORT de mission, bottom-up) :

  STEP 1 `phi1_bijection_derivee` — discharge des hyps MÉCANIQUES de
         `phi_etendue_bijection` (fonctionnalité/injectivité/dom/image de φ₀ et ψ
         depuis DEUX bijection-hyps ; disjointness des images depuis S₀∩U=∅).
         ⊢ est_bijection_de(φ₀∪ψ, Z×Z, Z) sous résidus HONNÊTES géométriques
         (S₀²∪F=Z×Z, S₀²∩F=∅, S₀∪U=Z, S₀∩U=∅) jamais postulés.

INVARIANT : theorie_ensembles()=22 ; aucun axiome nouveau ; rien postulé ; le lock
`reunion(S₀,U)=S₀` n'est JAMAIS dans les hypothèses (acceptance test).  Noyau INTACT.
NE PAS importer/réutiliser `ensembles_hessenberg_vrai.py` (tentative cassée).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.ensembles_frame_extension_finale import (
    cadre_ensemble, phi_etendue_bijection,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _reecrire_domaine_injectif(inj_thm, F_terme, dom_terme, vphi):
    """{ injective_dans(φ, F), F = dom(φ) } ⊢ injective_dans(φ, dom(φ)).

    Réécrit le DOMAINE d'une injectivité par S6 (F → dom(φ)).  inj_thm ⊢
    injective_dans(φ, F) ; on a F=dom(φ) (de dom(φ)=F symétrisé)."""
    s6 = N.s6(F_terme, dom_terme, "wdi", E.injective_dans(vphi, var("wdi")))
    F_eq_dom = N.assume(egal(F_terme, dom_terme))     # F = dom(φ)
    return N.modus_ponens(inj_thm, equivalence_avant(
        N.modus_ponens(F_eq_dom, s6))), F_eq_dom


# ════════════════════════════════════════════════════════════════════════════
#  STEP 1 — est_bijection_de(φ₀∪ψ, Z×Z, Z), hyps mécaniques DÉCHARGÉES.
# ════════════════════════════════════════════════════════════════════════════
def phi1_bijection_derivee(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ est_bijection_de(φ₀, S₀×S₀, S₀)      [maximal-data],
         est_bijection_de(ψ, F, U)           [cadre-data, F=cadre],
         + résidus géométriques HONNÊTES (S₀²∪F=Z×Z, S₀²∩F=∅, S₀∪U=Z, S₀∩U=∅) }
       ⊢ est_bijection_de(φ₀∪ψ, Z×Z, Z),  Z=S₀∪U.            [hyps HONNÊTES].

    🎯 STEP 1 : on prend `phi_etendue_bijection` (12 hyps honnêtes) et on DÉCHARGE les
    hyps MÉCANIQUES (fonctionnalité, injectivité, dom, image de φ₀ et ψ) depuis DEUX
    hypothèses-bijection HONNÊTES — `est_bijection_de(φ₀,S₀²,S₀)` (= maximal-data,
    contenu de (S₀,φ₀)∈𝔉) et `est_bijection_de(ψ,F,U)` (= cadre_bijection réalisé).
    est_bijection_de(F,X,Y) = ((fonctionnel ∧ dom=X) ∧ (injective ∧ image=Y)).

    Restent en HYPOTHÈSES HONNÊTES les résidus PUREMENT GÉOMÉTRIQUES de
    phi_etendue_bijection (S₀²∪F=Z×Z, S₀²∩F=∅, imgφ₀∪imgψ=Z, imgφ₀∩imgψ=∅) : les
    identités d'ensembles dont l'extensionnalité+∃-pushing reste reportée dans le
    dépôt.  Le lock `reunion(S₀,U)=S₀` n'apparaît JAMAIS.  theorie=22 ; non vacuous."""
    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    SxS = E.produit(vS, vS)
    F = cadre_ensemble(S, U)                                 # le cadre (somme disjointe)

    base = phi_etendue_bijection(phi0, psi, S, U)            # 12 hyps honnêtes ⊢ bij(φ₁,Z²,Z)

    # ── deux bijections HONNÊTES ────────────────────────────────────────────
    bij0 = N.assume(est_bijection_de(vphi0, SxS, vS))        # φ₀ : S₀² → S₀     [maximal]
    bijp = N.assume(est_bijection_de(vpsi, F, vU))           # ψ  : F → U        [cadre]

    # ── décharge depuis bij0 : est_fonctionnel(φ₀), dom φ₀=S₀², inj(φ₀,S₀²), img(φ₀,S₀²)=S₀
    func0 = conjonction_elim_gauche(conjonction_elim_gauche(bij0))   # est_fonctionnel(φ₀)
    dom0 = conjonction_elim_droite(conjonction_elim_gauche(bij0))    # dom φ₀=S₀²
    inj0_SxS = conjonction_elim_gauche(conjonction_elim_droite(bij0))  # injective_dans(φ₀,S₀²)
    img0 = conjonction_elim_droite(conjonction_elim_droite(bij0))    # image(φ₀,S₀²)=S₀

    # ── décharge depuis bijp : est_fonctionnel(ψ), dom ψ=F, inj(ψ,F), img(ψ,F)=U
    funcp = conjonction_elim_gauche(conjonction_elim_gauche(bijp))
    domp = conjonction_elim_droite(conjonction_elim_gauche(bijp))    # dom ψ=F
    injp_F = conjonction_elim_gauche(conjonction_elim_droite(bijp))  # injective_dans(ψ,F)
    imgp = conjonction_elim_droite(conjonction_elim_droite(bijp))    # image(ψ,F)=U

    # ── réécrire les injectivités sur dom(φ) (les hyps de base utilisent dom(φ₀)/dom(ψ))
    # dom φ₀=S₀² ⇒ injective_dans(φ₀,dom φ₀) depuis injective_dans(φ₀,S₀²).
    dom0_sym = N.modus_ponens(dom0, symetrie(E.dom(vphi0), SxS))     # S₀²=dom φ₀
    s6i0 = N.s6(SxS, E.dom(vphi0), "wi0", E.injective_dans(vphi0, var("wi0")))
    inj0 = N.modus_ponens(inj0_SxS, equivalence_avant(N.modus_ponens(dom0_sym, s6i0)))
    domp_sym = N.modus_ponens(domp, symetrie(E.dom(vpsi), F))        # F=dom ψ
    s6ip = N.s6(F, E.dom(vpsi), "wip", E.injective_dans(vpsi, var("wip")))
    injp = N.modus_ponens(injp_F, equivalence_avant(N.modus_ponens(domp_sym, s6ip)))

    # On a maintenant déchargé : func0, funcp, inj0, injp, dom0.
    # Restent en hyps honnêtes de base : dom ψ=F (= domp, derivable mais base attend la
    # forme F=cadre ; on la décharge aussi), les deux img=img réflexives (triviales),
    # disjointness domaines/images, S₀²∪F=Z², imgφ₀∪imgψ=Z.
    # (fonctionnel ∧ dom=X) conjonctions, directement les conjoints gauches des bijections
    fd0 = conjonction_elim_gauche(bij0)                     # (est_fonctionnel(φ₀) ∧ dom φ₀=S₀²)
    fdp = conjonction_elim_gauche(bijp)                     # (est_fonctionnel(ψ)  ∧ dom ψ=F)
    # images réflexives (triviales)
    refl_img0 = N.reflexivite(E.image(vphi0, E.dom(vphi0)))  # image(φ₀,domφ₀)=image(φ₀,domφ₀)
    refl_imgp = N.reflexivite(E.image(vpsi, E.dom(vpsi)))

    cur = base
    # décharge tous les théorèmes mécaniques dont la conclusion apparie une hyp de base.
    for thm in (func0, funcp, inj0, injp, dom0, domp, fd0, fdp, refl_img0, refl_imgp):
        c = thm.conclusion
        if c in cur.hypotheses:
            cur = N.modus_ponens(thm, N.loi_deduction(c, cur))

    Z = E.reunion(vS, vU)
    ZxZ = E.produit(Z, Z)
    phi1 = E.reunion(vphi0, vpsi)
    cible = est_bijection_de(phi1, ZxZ, Z)
    assert cur.conclusion == cible, \
        f"phi1_bijection_derivee : conclusion inattendue\n{cur.conclusion}\nvs\n{cible}"
    # ACCEPTANCE : le lock reunion(S₀,U)=S₀ ne DOIT PAS être une hypothèse.
    lock = egal(Z, vS)
    assert lock not in cur.hypotheses, "phi1_bijection_derivee : LOCK reunion(S₀,U)=S₀ présent !"
    assert cur.conclusion not in cur.hypotheses, "phi1_bijection_derivee : VACUOUS"
    return cur


__all__ = [
    "phi1_bijection_derivee",
]
