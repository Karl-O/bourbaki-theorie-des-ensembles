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

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, pourtout, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import (
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


def _inclusion_reunion_gauche_t(ta, tb):
    """⊢ a ⊂ (a∪b)  pour des TERMES a,b (capture-safe via généralisation/instanciation)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import inclusion_reunion_gauche
    base = inclusion_reunion_gauche("ar", "br")
    gen = N.generalisation("ar", N.generalisation("br", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


# ════════════════════════════════════════════════════════════════════════════
#  STEP 2 — (Z,φ₁) ∈ 𝔉(E).   STEP 1 décharge la bijection ; Z⊂E, Z infini honnêtes.
# ════════════════════════════════════════════════════════════════════════════
def extension_dans_frame_chainee(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ 2 bijections + géométrie [STEP 1],  Z⊂E,  Z infini } ⊢ (Z,φ₁)∈𝔉(E).

    🎯 STEP 2 : chaîne STEP 1 (`phi1_bijection_derivee`, ⊢ bij(φ₁,Z²,Z)) dans
    `extension_dans_frame` en DÉCHARGEANT son hyp-bijection.  Restent Z⊂E et Z infini
    (honnêtes, dérivables de S₀⊂E+U⊂E∖S₀ et S₀⊂Z+S₀ infini ; portées en prémisses),
    plus les 6 résidus de STEP 1.  Le lock reste ABSENT.  theorie=22 ; non vacuous."""
    from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import extension_dans_frame
    vphi0, vpsi, vS, vU = _t(phi0), _t(psi), _t(S), _t(U)
    Z = E.reunion(vS, vU)
    bij = est_bijection_de(E.reunion(vphi0, vpsi), E.produit(Z, Z), Z)
    edf = extension_dans_frame(E_set, phi0, psi, S, U)      # {bij,Z⊂E,Z∞} ⊢ (Z,φ₁)∈𝔉
    assert bij in edf.hypotheses, "STEP2 : hyp bijection absente de extension_dans_frame"
    step1 = phi1_bijection_derivee(E_set, phi0, psi, S, U)  # ⊢ bij
    res = N.modus_ponens(step1, N.loi_deduction(bij, edf))  # bijection déchargée
    assert egal(Z, vS) not in res.hypotheses, "STEP2 : LOCK présent !"
    assert res.conclusion == edf.conclusion
    assert res.conclusion not in res.hypotheses, "STEP2 : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  STEP 3 — ordre.  STEP 2 décharge (Z,φ₁)∈𝔉 ; (S₀,φ₀)∈𝔉, S₀⊂Z, φ₀⊂φ₁ honnêtes.
# ════════════════════════════════════════════════════════════════════════════
def extension_ordre_chainee(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ … [STEP 2], (S₀,φ₀)∈𝔉, S₀⊂Z, φ₀⊂φ₁ } ⊢ ((S₀,φ₀),(Z,φ₁))∈Γ𝔉(E).

    🎯 STEP 3 : chaîne STEP 2 (⊢ (Z,φ₁)∈𝔉) dans `extension_ordre` en DÉCHARGEANT son
    hyp-membership (Z,φ₁)∈𝔉.  Restent (S₀,φ₀)∈𝔉, S₀⊂Z, φ₀⊂φ₁ (honnêtes : la première
    = maximal-data, les deux inclusions = prolongement géométrique S₀⊂S₀∪U, φ₀⊂φ₀∪ψ).
    Le lock reste ABSENT.  theorie=22 ; non vacuous."""
    from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import extension_ordre
    from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair
    vphi0, vpsi, vS, vU, vE = _t(phi0), _t(psi), _t(S), _t(U), _t(E_set)
    Z = E.reunion(vS, vU)
    phi1 = E.reunion(vphi0, vpsi)
    q = E.couple(Z, phi1)
    q_in = appartient(q, frame_pair(vE))
    eo = extension_ordre(E_set, phi0, psi, S, U)            # {(Z,φ₁)∈𝔉,(S₀,φ₀)∈𝔉,…} ⊢ ordre
    assert q_in in eo.hypotheses, "STEP3 : hyp (Z,φ₁)∈𝔉 absente"
    step2 = extension_dans_frame_chainee(E_set, phi0, psi, S, U)  # ⊢ (Z,φ₁)∈𝔉
    res = N.modus_ponens(step2, N.loi_deduction(q_in, eo))
    # décharge les deux INCLUSIONS de prolongement S₀⊂Z et φ₀⊂φ₁ (A⊂A∪B, trivial).
    inclL = _inclusion_reunion_gauche_t
    for (a, b) in ((vS, vU), (vphi0, vpsi)):
        thm = inclL(a, b)                                   # ⊢ a⊂(a∪b)
        c = thm.conclusion
        if c in res.hypotheses:
            res = N.modus_ponens(thm, N.loi_deduction(c, res))
    assert egal(Z, vS) not in res.hypotheses, "STEP3 : LOCK présent !"
    assert res.conclusion == eo.conclusion
    assert res.conclusion not in res.hypotheses, "STEP3 : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  STEP 4 — Z=S₀ DÉRIVÉ via la maximalité (extension_force_egalite).
#  STEP 2 décharge (Z,φ₁)∈𝔉 ; STEP 3 décharge l'ordre ; reste element_maximal honnête.
# ════════════════════════════════════════════════════════════════════════════
def extension_force_egalite_chainee(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre"):
    """{ element_maximal(Γ𝔉,𝔉,(S₀,φ₀))  [maximal-data],  … [STEP 2+3] } ⊢ Z = S₀.

    🎯 STEP 4 — LE CŒUR : la maximalité de (S₀,φ₀) appliquée à l'extension (Z,φ₁)
    [∈𝔉 par STEP 2, ≥(S₀,φ₀) par STEP 3] DÉRIVE Z=S₀.  Le lock n'est PAS supposé : il
    est PRODUIT par `extension_force_egalite` en déchargeant ses hyps (Z,φ₁)∈𝔉 et
    ((S₀,φ₀),(Z,φ₁))∈Γ𝔉 par STEP 2/3.  Reste `element_maximal(Γ𝔉,𝔉,(S₀,φ₀))` honnête
    (fourni par `frame_a_maximal` + réalisation du maximal en (S₀,φ₀)) + les résidus
    géométriques.  Conclusion = (reunion(S₀,U)=S₀) PROUVÉE, jamais assumée.
    theorie=22 ; non vacuous."""
    from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import extension_force_egalite
    from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
    vphi0, vpsi, vS, vU, vE = _t(phi0), _t(psi), _t(S), _t(U), _t(E_set)
    Z = E.reunion(vS, vU)
    phi1 = E.reunion(vphi0, vpsi)
    p = E.couple(vS, vphi0)
    q = E.couple(Z, phi1)
    q_in = appartient(q, frame_pair(vE))                    # (Z,φ₁)∈𝔉
    pq_in = appartient(E.couple(p, q), frame_ordre(vE))     # ((S₀,φ₀),(Z,φ₁))∈Γ𝔉

    efe = extension_force_egalite(E_set, phi0, psi, S, U)   # {max,(Z,φ₁)∈𝔉,ordre} ⊢ Z=S₀
    assert q_in in efe.hypotheses and pq_in in efe.hypotheses

    step2 = extension_dans_frame_chainee(E_set, phi0, psi, S, U)   # ⊢ (Z,φ₁)∈𝔉
    step3 = extension_ordre_chainee(E_set, phi0, psi, S, U)        # ⊢ ((S₀,φ₀),(Z,φ₁))∈Γ𝔉
    res = N.modus_ponens(step2, N.loi_deduction(q_in, efe))       # (Z,φ₁)∈𝔉 déchargée
    res = N.modus_ponens(step3, N.loi_deduction(pq_in, res))      # ordre déchargé

    assert res.conclusion == egal(Z, vS), \
        f"STEP4 : conclusion inattendue\n{res.conclusion}\nvs\n{egal(Z, vS)}"
    # le lock est la CONCLUSION (prouvée), pas une hypothèse :
    assert egal(Z, vS) not in res.hypotheses, "STEP4 : LOCK supposé (vacuous) !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  STEP 5 — ABSURDITÉ : Z=S₀ DÉRIVÉ (STEP 4) + u∈U + U∩S₀=∅ ⇒ ⊥ (¬(u∈U)).
# ════════════════════════════════════════════════════════════════════════════
def extension_absurde_chainee(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre",
                              u="uwit"):
    """{ u∈U,  (∀z)(z∈U⇒¬z∈S₀)  [U∩S₀=∅],  … [STEP 4, dont element_maximal] }
        ⊢ ¬(u∈U)   — i.e. CONTRADICTION (u∈U ∧ ¬(u∈U)).

    🎯 STEP 5 — la CONTRADICTION FINALE de Bourbaki (E.III.48), avec le lock Z=S₀
    GENUINEMENT DÉRIVÉ (STEP 4) et NON supposé.  `extension_absurde` conclut ¬(u∈U)
    sous {Z=S₀, u∈U, U∩S₀=∅} ; STEP 4 DÉCHARGE Z=S₀ (le force par maximalité).  On
    obtient alors ¬(u∈U) sous {u∈U, U∩S₀=∅} + les résidus honnêtes de STEP 4
    (element_maximal, bijections, géométrie) — le témoin u∈U et ¬(u∈U) ensemble = ⊥.

    ⚠️ Le lock `reunion(S₀,U)=S₀` n'est JAMAIS une hypothèse (ACCEPTANCE) : il est
    PROUVÉ par STEP 4 et consommé.  Ce qui RESTE sont les U-data honnêtes (u∈U,
    U∩S₀=∅, qui dans l'argument complet proviennent de 𝔟<a + complement_grand) et les
    résidus géométriques/maximalité — tous SATISFIABLES.  theorie=22 ; non vacuous."""
    from bourbaki.cardinaux.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import extension_absurde
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    h_Zlock = egal(Z, vS)

    ea = extension_absurde(E_set, phi0, psi, S, U, u)      # {Z=S₀,u∈U,U∩S₀=∅} ⊢ ¬(u∈U)
    assert h_Zlock in ea.hypotheses, "STEP5 : hyp Z=S₀ absente de extension_absurde"
    step4 = extension_force_egalite_chainee(E_set, phi0, psi, S, U)   # ⊢ Z=S₀
    res = N.modus_ponens(step4, N.loi_deduction(h_Zlock, ea))         # Z=S₀ DÉCHARGÉE

    assert res.conclusion == non(appartient(var(u), vU)), \
        f"STEP5 : conclusion inattendue\n{res.conclusion}"
    # ACCEPTANCE : le lock n'est PAS une hypothèse (il a été dérivé puis consommé).
    assert h_Zlock not in res.hypotheses, "STEP5 : LOCK supposé (vacuous) !"
    # le témoin u∈U est présent → avec ¬(u∈U) c'est bien la contradiction.
    assert appartient(var(u), vU) in res.hypotheses, "STEP5 : témoin u∈U absent"
    return res


__all__ = [
    "phi1_bijection_derivee",
    "extension_dans_frame_chainee",
    "extension_ordre_chainee",
    "extension_force_egalite_chainee",
    "extension_absurde_chainee",
]
