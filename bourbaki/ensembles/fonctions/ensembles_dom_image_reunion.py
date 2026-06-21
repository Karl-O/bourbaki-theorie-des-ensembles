"""GAP A — pont couple→ÉGALITÉ-D'ENSEMBLES pour dom/image d'une réunion de graphes,
spécialisé aux formes CONCRÈTES de l'extension de Hessenberg (E.III.48).

Les LEMMES GÉNÉRAUX set-equality existent déjà dans le dépôt :
  • `dom_reunion_graphes(G,H)`        ⊢ dom(G∪H) = dom G ∪ dom H
        (ensembles_restriction_somme, double inclusion + A1),
  • `image_reunion_graphes(G,H)`      ⊢ image(G∪H, domG∪domH) = image(G,domG) ∪ image(H,domH)
        (ensembles_recollement_bijection, double inclusion + A1).

CE MODULE en tire les COROLLAIRES qui apparient EXACTEMENT les conjoints
VALEUR-D'ENSEMBLES portés en hypothèses honnêtes par `phi_etendue_bijection`
(frame_extension_finale) et `union_chaine_est_bijection` (chaine_frame_membership) :

  • `dom_reunion_egale_cible(G,H, DG,DH, W)` :
        { dom G = DG,  dom H = DH,  DG ∪ DH = W }  ⊢  dom(G∪H) = W.

  • `image_reunion_egale_cible(G,H, IG,IH, T)` :
        { image(G,domG) = IG,  image(H,domH) = IH,  IG ∪ IH = T }
          ⊢  image(G∪H, domG∪domH) = T.

Ces corollaires REMPLACENT les hyps couple→ensemble globales `dom(φ₁)=Z×Z` /
`image(φ₁,Z×Z)=Z` par les hyps STRUCTURELLES plus primitives sur les témoins
(dom φ₀=S₀², dom ψ=F, S₀²∪F=Z²  ;  image φ₀=S₀, image ψ=…, …∪…=Z) — exactement
le motif que `phi_etendue_bijection` documentait comme « absent du dépôt ».

INVARIANT : theorie_ensembles() = 22 ; aucun axiome ; rien postulé.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)

# ré-export des lemmes généraux (un seul point d'import pour l'appelant)
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import (
    dom_reunion_graphes,
)
from bourbaki.ensembles.fonctions.ensembles_recollement_bijection import (
    image_reunion_graphes,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _reunion_congru(eqG, eqH):
    """Γ⊢(P=DG), Δ⊢(Q=DH) ⟹ Γ∪Δ ⊢ (P∪Q) = (DG∪DH).

    Réécrit les DEUX membres d'une réunion par congruence (S6 via congruence_terme),
    capture-safe (le trou « w » de congruence_terme n'apparaît pas dans les termes)."""
    P, DG = eqG.conclusion.termes
    Q, DH = eqH.conclusion.termes
    # P∪Q = DG∪Q  (réécrire le membre GAUCHE)
    cong_g = N.modus_ponens(eqG, congruence_terme(P, DG, E.reunion(var("w"), Q)))
    # DG∪Q = DG∪DH  (réécrire le membre DROIT)
    cong_h = N.modus_ponens(eqH, congruence_terme(Q, DH, E.reunion(DG, var("w"))))
    return composer_egalites(cong_g, cong_h)              # P∪Q = DG∪DH


# ════════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE dom — dom(G∪H) = W  sous  domG=DG, domH=DH, DG∪DH=W.
# ════════════════════════════════════════════════════════════════════════════════
def dom_reunion_egale_cible(g="G", h="H", DG="DG", DH="DH", W="W"):
    """{ dom G = DG,  dom H = DH,  DG ∪ DH = W }  ⊢  dom(G∪H) = W.

    🎯 GAP A (dom).  dom_reunion_graphes donne dom(G∪H)=domG∪domH [CLOS] ; les deux
    premières hyps réécrivent domG∪domH = DG∪DH (congruence), la troisième = W.
    Composition d'égalités.  Apparie `dom(φ₁)=Z×Z` via DG:=S₀², DH:=F, W:=Z×Z.
    theorie=22, NON vacuous."""
    vg, vh = _t(g), _t(h)
    vDG, vDH, vW = _t(DG), _t(DH), _t(W)
    domG, domH = E.dom(vg), E.dom(vh)
    GuH = E.reunion(vg, vh)

    base = dom_reunion_graphes(vg, vh)                    # dom(G∪H) = domG∪domH   [CLOS]
    assert base.conclusion == egal(E.dom(GuH), E.reunion(domG, domH))

    h_dg = N.assume(egal(domG, vDG))                     # dom G = DG          [HYP]
    h_dh = N.assume(egal(domH, vDH))                     # dom H = DH          [HYP]
    h_w = N.assume(egal(E.reunion(vDG, vDH), vW))        # DG∪DH = W           [HYP]

    cong = _reunion_congru(h_dg, h_dh)                   # domG∪domH = DG∪DH
    step = composer_egalites(base, cong)                 # dom(G∪H) = DG∪DH
    res = composer_egalites(step, h_w)                   # dom(G∪H) = W

    cible = egal(E.dom(GuH), vW)
    assert res.conclusion == cible, \
        f"dom_reunion_egale_cible : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "dom_reunion_egale_cible : VACUOUS"
    return res


def dom_reunion_egale_cible_enonce(g="G", h="H", W="W"):
    """ÉNONCÉ-cible (test miroir)."""
    vg, vh, vW = _t(g), _t(h), _t(W)
    return egal(E.dom(E.reunion(vg, vh)), vW)


# ════════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE image — image(G∪H, domG∪domH) = T  sous img-hyps + IG∪IH=T.
# ════════════════════════════════════════════════════════════════════════════════
def image_reunion_egale_cible(g="G", h="H", IG="IG", IH="IH", T="T"):
    """{ image(G,domG) = IG,  image(H,domH) = IH,  IG ∪ IH = T }
        ⊢  image(G∪H, domG∪domH) = T.

    🎯 GAP A (image).  image_reunion_graphes donne
        image(G∪H, domG∪domH) = image(G,domG)∪image(H,domH)  [CLOS] ;
    les deux premières hyps réécrivent ce membre droit = IG∪IH (congruence), la
    troisième = T.  Apparie `image(φ₁,Z×Z)=Z` (après réécriture du domaine en Z×Z par
    le corollaire dom).  theorie=22, NON vacuous."""
    vg, vh = _t(g), _t(h)
    vIG, vIH, vT = _t(IG), _t(IH), _t(T)
    domG, domH = E.dom(vg), E.dom(vh)
    GuH = E.reunion(vg, vh)
    domR = E.reunion(domG, domH)
    imgG, imgH = E.image(vg, domG), E.image(vh, domH)

    base = image_reunion_graphes(vg, vh)                 # image(G∪H,domR) = imgG∪imgH [CLOS]
    assert base.conclusion == egal(E.image(GuH, domR), E.reunion(imgG, imgH))

    h_ig = N.assume(egal(imgG, vIG))                     # image(G,domG) = IG  [HYP]
    h_ih = N.assume(egal(imgH, vIH))                     # image(H,domH) = IH  [HYP]
    h_t = N.assume(egal(E.reunion(vIG, vIH), vT))        # IG∪IH = T           [HYP]

    cong = _reunion_congru(h_ig, h_ih)                   # imgG∪imgH = IG∪IH
    step = composer_egalites(base, cong)                 # image(G∪H,domR) = IG∪IH
    res = composer_egalites(step, h_t)                   # image(G∪H,domR) = T

    cible = egal(E.image(GuH, domR), vT)
    assert res.conclusion == cible, \
        f"image_reunion_egale_cible : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "image_reunion_egale_cible : VACUOUS"
    return res


def image_reunion_egale_cible_enonce(g="G", h="H", T="T"):
    """ÉNONCÉ-cible (test miroir)."""
    vg, vh, vT = _t(g), _t(h), _t(T)
    domR = E.reunion(E.dom(vg), E.dom(vh))
    return egal(E.image(E.reunion(vg, vh), domR), vT)


__all__ = [
    "dom_reunion_graphes",
    "image_reunion_graphes",
    "dom_reunion_egale_cible",
    "dom_reunion_egale_cible_enonce",
    "image_reunion_egale_cible",
    "image_reunion_egale_cible_enonce",
]
