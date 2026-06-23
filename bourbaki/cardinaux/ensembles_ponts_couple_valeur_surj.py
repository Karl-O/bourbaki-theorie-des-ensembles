"""§III.6.3 — PONTS couple→ensemble :  surjectivité/domaine COUPLE-NATIFS → ÉGALITÉ
D'ENSEMBLES (`image(F,D)=T`, `dom(F)=D`).

CONTEXTE.  `union_chaine_est_bijection` (`ensembles_chaine_frame_membership.py`)
porte EN HYPOTHÈSE HONNÊTE les égalités d'ensembles `image(⋃φ,US×US)=US` et
`dom(⋃φ)=US×US` exigées par `est_bijection_de`, parce que les formes COUPLE-NATIVES
amont (`union_chaine_surjective`/`union_chaine_dom`) ne livrent que la surjectivité /
couverture de domaine AU NIVEAU COUPLE — (∀w∈T)(∃a)((a,w)∈F) et (∀ab∈D)(∃w)((ab,w)∈F).

Ce module FERME le pont couple→égalité-d'ensembles, en miroir de
`injectif_graphe_implique_injective_dans` (`ensembles_injectif_graphe_pont.py`) :
on n'invoque que les axiomes de membership AXIOME_IMAGE / AXIOME_DOM et l'antisymétrie
de ⊂ (= extensionnalité A1) — JAMAIS de matérialisation de τ-valeur, aucun mur de capture.

THÉORÈMES (CLOS, hyps HONNÊTES ; theorie=22) :
  • couple_surjectif_implique_image_egale
      { (∀w)(w∈T ⇒ (∃a)(a∈D et (a,w)∈F)),  image(F,D)⊂T } ⊢ image(F,D) = T.
        — direction ⊃ : AXIOME_IMAGE (sens arrière) sur la surjectivité couple-niveau ;
        — direction ⊂ : hyp honnête image(F,D)⊂T ;
        — égalité : inclusion_antisymetrique (A1).
  • couple_domaine_implique_dom_egale
      { (∀ab)(ab∈D ⇒ (∃w)((ab,w)∈F)),  dom(F)⊂D } ⊢ dom(F) = D.
        — direction ⊃ : AXIOME_DOM (sens arrière) sur la couverture couple-niveau ;
        — direction ⊂ : hyp honnête dom(F)⊂D ;
        — égalité : inclusion_antisymetrique (A1).

⚠️ NOTE sur la forme de la surjectivité.  `union_chaine_surjective` livre
(∀w)(w∈T ⇒ (∃a)((a,w)∈F)) (sans la conjonction « a∈D et »).  AXIOME_IMAGE exige le
témoin sous la forme (∃a)(a∈D et (a,w)∈F).  Le présent lemme prend donc la forme
RICHE (avec a∈D) ; le pont depuis la forme amont nécessite, en plus, que le témoin a
soit dans D — porté ici comme part de l'hypothèse honnête (couverture par D), ce que
le recollement fournit (l'antécédent vit dans un morceau S_i ⊂ ⋃S = D).

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
conclusion ∉ hyps (non vacuous).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Prédicats honnêtes (surjectivité / couverture du domaine, niveau COUPLE).
# ════════════════════════════════════════════════════════════════════════════
def surjectif_couple_riche(F, D, T, w="wsr", a="asr"):
    """(∀w)( w∈T ⇒ (∃a)( a∈D et (a,w)∈F ) )  — surjectivité couple-niveau RICHE
    (témoin a explicitement dans D, forme exigée par AXIOME_IMAGE)."""
    vF, vD, vT = _t(F), _t(D), _t(T)
    vw, va = var(w), var(a)
    return pourtout(w, impl(appartient(vw, vT),
        existe(a, et(appartient(va, vD), appartient(E.couple(va, vw), vF)))))


def domaine_couple(F, D, ab="abdc", w="wdc"):
    """(∀ab)( ab∈D ⇒ (∃w)( (ab,w)∈F ) )  — couverture du domaine au niveau COUPLE
    (forme exigée par AXIOME_DOM)."""
    vF, vD = _t(F), _t(D)
    vab, vw = var(ab), var(w)
    return pourtout(ab, impl(appartient(vab, vD),
        existe(w, appartient(E.couple(vab, vw), vF))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PONT 1 — surjectivité couple-niveau  ⇒  image(F,D) = T.
# ════════════════════════════════════════════════════════════════════════════
def couple_surjectif_implique_image_egale(F="Fsr", D="Dsr", T="Tsr"):
    """{ surjectif_couple_riche(F,D,T), image(F,D)⊂T } ⊢ image(F,D) = T.
                                                          [2 hyps HONNÊTES].

    🎯 Le PONT couple→égalité-d'ensembles pour la SURJECTIVITÉ.  La surjectivité
    couple-niveau (tout w∈T a un antécédent a∈D avec (a,w)∈F) donne T⊂image(F,D) via
    AXIOME_IMAGE (sens arrière) ; avec l'inclusion honnête image(F,D)⊂T, l'antisymétrie
    de ⊂ (A1) conclut image(F,D)=T (= `est_surjective(F,D,T)`).  Aucune τ-valeur."""
    vF, vD, vT = _t(F), _t(D), _t(T)
    img = E.image(vF, vD)
    vw, va = var("z"), var("asr")

    h_surj = N.assume(surjectif_couple_riche(vF, vD, vT))      # [HONNÊTE]
    h_inc = N.assume(inclus(img, vT))                          # image(F,D)⊂T [HONNÊTE]

    # ── direction ⊃ :  T ⊂ image(F,D)  (chaque w∈T est dans l'image) ─────────
    h_w = N.assume(appartient(vw, vT))                         # w∈T
    surj_w = N.modus_ponens(h_w, instancie(h_surj, vw))        # (∃a)(a∈D et (a,w)∈F)

    # AXIOME_IMAGE : (∀G)(∀X)(∀y)(y∈G⟨X⟩ ⇔ (∃x)(x∈X et (x,y)∈G))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, vF), vD), vw)  # w∈image(F,D) ⇔ (∃x)(x∈D et (x,w)∈F)
    # surj_w est en "asr" (forme RICHE) ; AXIOME_IMAGE produit le binder "x".
    # On renomme (∃asr)... ⇐⇒ (∃x)... pour appliquer le sens arrière de car.
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    surj_w_x = N.modus_ponens(surj_w, equivalence_avant(alpha_existe(
        "asr", "x", et(appartient(va, vD), appartient(E.couple(va, vw), vF)))))  # (∃x)(x∈D et (x,w)∈F)
    w_in_img = N.modus_ponens(surj_w_x, equivalence_arriere(car))   # w∈image(F,D)

    impl_w = N.loi_deduction(appartient(vw, vT), w_in_img)     # w∈T ⇒ w∈image(F,D)
    T_inc_img = N.generalisation("z", impl_w)                 # T⊂image(F,D)

    # ── antisymétrie : (image⊂T et T⊂image) ⇒ image=T ──────────────────────
    conj = conjonction_intro(h_inc, T_inc_img)                # image⊂T et T⊂image
    anti = inclusion_antisymetrique(img, vT)                  # (image⊂T et T⊂image) ⇒ image=T
    res = N.modus_ponens(conj, anti)                          # image(F,D)=T

    cible = egal(img, vT)
    assert res.conclusion == cible, "couple_surjectif_implique_image_egale : conclusion ≠ image=T"
    assert surjectif_couple_riche(vF, vD, vT) in res.hypotheses, "surj hyp absente"
    assert inclus(img, vT) in res.hypotheses, "inclus image⊂T absente"
    assert res.conclusion not in res.hypotheses, "couple_surjectif_implique_image_egale : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PONT 2 — couverture du domaine couple-niveau  ⇒  dom(F) = D.
# ════════════════════════════════════════════════════════════════════════════
def couple_domaine_implique_dom_egale(F="Fdc", D="Ddc"):
    """{ domaine_couple(F,D), dom(F)⊂D } ⊢ dom(F) = D.   [2 hyps HONNÊTES].

    🎯 Le PONT couple→égalité-d'ensembles pour le DOMAINE.  La couverture
    couple-niveau (tout ab∈D a une valeur : (∃w)((ab,w)∈F)) donne D⊂dom(F) via
    AXIOME_DOM (sens arrière) ; avec l'inclusion honnête dom(F)⊂D, l'antisymétrie
    de ⊂ (A1) conclut dom(F)=D.  Aucune τ-valeur."""
    vF, vD = _t(F), _t(D)
    dm = E.dom(vF)
    vab, vw = var("z"), var("wdc")

    h_dom = N.assume(domaine_couple(vF, vD))                   # [HONNÊTE]
    h_inc = N.assume(inclus(dm, vD))                           # dom(F)⊂D [HONNÊTE]

    # ── direction ⊃ :  D ⊂ dom(F) ───────────────────────────────────────────
    h_ab = N.assume(appartient(vab, vD))                      # ab∈D
    dom_ab = N.modus_ponens(h_ab, instancie(h_dom, vab))      # (∃w)((ab,w)∈F)

    # AXIOME_DOM : (∀G)(∀x)(x∈dom G ⇔ (∃y)((x,y)∈G))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vF), vab)              # ab∈dom F ⇔ (∃y)((ab,y)∈F)
    # binder canonique "y" → on renomme la couverture "wdc" vers "y" pour matcher
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    dom_ab_y = N.modus_ponens(dom_ab, equivalence_avant(alpha_existe(
        "wdc", "y", appartient(E.couple(vab, vw), vF))))     # (∃y)((ab,y)∈F)
    ab_in_dom = N.modus_ponens(dom_ab_y, equivalence_arriere(car))   # ab∈dom F

    impl_ab = N.loi_deduction(appartient(vab, vD), ab_in_dom)  # ab∈D ⇒ ab∈dom F
    D_inc_dom = N.generalisation("z", impl_ab)               # D⊂dom F

    # ── antisymétrie ────────────────────────────────────────────────────────
    conj = conjonction_intro(h_inc, D_inc_dom)               # dom⊂D et D⊂dom
    anti = inclusion_antisymetrique(dm, vD)                  # (dom⊂D et D⊂dom) ⇒ dom=D
    res = N.modus_ponens(conj, anti)                         # dom(F)=D

    cible = egal(dm, vD)
    assert res.conclusion == cible, "couple_domaine_implique_dom_egale : conclusion ≠ dom=D"
    assert domaine_couple(vF, vD) in res.hypotheses, "domaine hyp absente"
    assert inclus(dm, vD) in res.hypotheses, "inclus dom⊂D absente"
    assert res.conclusion not in res.hypotheses, "couple_domaine_implique_dom_egale : VACUOUS"
    return res


__all__ = [
    "surjectif_couple_riche", "domaine_couple",
    "couple_surjectif_implique_image_egale", "couple_domaine_implique_dom_egale",
]
