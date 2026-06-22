"""§II.4 (E.II.27) — ALGÈBRE BINAIRE DE L'IMAGE DIRECTE / RÉCIPROQUE.

Complète, à DEUX ensembles, les formules de l'§II.4 sur ∪ / ∩ / ∖ pour
l'image directe f⟨⟩ et l'image réciproque f⁻¹⟨⟩ (E.II.25–27 ; Prop. 3, 4, 6).

INCONDITIONNELLES (correspondance f quelconque) :
  • image_reunion_binaire        ⊢ f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩          (Prop. 3, 1re formule)

CONDITIONNELLES (honnête hyp `est_fonctionnel(f)`, i.e. f application) :
  • image_inter_binaire          ⊢ est_fonctionnel(f) ⇒ f⟨B∩Y⟩ = f⟨B⟩ ∩ f⟨Y⟩
  • image_reciproque_inter_binaire ⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∩Y⟩ = f⁻¹⟨B⟩ ∩ f⁻¹⟨Y⟩
  • image_reciproque_difference  ⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩

Pour l'image RÉCIPROQUE, Bourbaki (E.II.27) écrit f⁻¹⟨A∩B⟩=f⁻¹⟨A⟩∩f⁻¹⟨B⟩
« en vertu de la prop. 4 », i.e. pour une APPLICATION f.  Le sens ⊆ est toujours
vrai, mais le sens ⊇ (un même antécédent x atteint A et B → atteint A∩B) exige
l'UNIVALENCE : si f(x)∈A et f(x)∈B alors f(x)∈A∩B, ce qui demande que x ait UNE
valeur.  Idem pour la différence (Prop. 6).  D'où l'hypothèse honnête.

Preuve : tout est pointwise (A1 + AXIOME_IMAGE + AXIOME_INTER/DIFF/REUNION).
AXIOME_IMAGE : y∈G⟨X⟩ ⇔ (∃x)(x∈X et (x,y)∈G).  Pour l'image directe G:=f, pour la
réciproque G:=f⁻¹ (couple (x,a)∈f⁻¹).  theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    var, egal, et, ou, non, appartient, existe, impl, Terme)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
    instancie, equivalence_transitivite as etr, equivalence_symetrie as esym,
    et_congruence_gauche, et_congruence_droite, comm_et, et_ou_distrib,
    ou_congruence, assoc_et, cas)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.ensembles_produit_union_carre import existe_ou


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Membres élémentaires (instances directes des axiomes).
# ════════════════════════════════════════════════════════════════════════════
def membre_image(f, Z, a):
    """⊢ a ∈ f⟨Z⟩ ⇔ (∃x)(x∈Z et (x,a)∈f).

    Instance directe de AXIOME_IMAGE (G:=f, X:=Z, y:=a).  Liant interne « x »."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, f), Z), a)


def membre_image_reciproque(f, Z, a):
    """⊢ a ∈ f⁻¹⟨Z⟩ ⇔ (∃x)(x∈Z et (x,a)∈f⁻¹).  (G:=reciproque(f).)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, E.reciproque(f)), Z), a)


def _instance_reunion(a, b, z):
    """⊢ (z ∈ a∪b) ⇔ (z∈a ou z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_inter(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_diff(a, b, z):
    """⊢ (z ∈ a∖b) ⇔ (z∈a et ¬(z∈b))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, a), b), z)


# ════════════════════════════════════════════════════════════════════════════
#  1. IMAGE DIRECTE D'UNE RÉUNION — INCONDITIONNEL  (E.II.27, Prop. 3).
#     f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩
# ════════════════════════════════════════════════════════════════════════════
def cible_image_reunion_binaire(f="f", b="B", y="Y"):
    vf, vb, vy = _t(f), _t(b), _t(y)
    gauche = E.image(vf, E.reunion(vb, vy))
    droite = E.reunion(E.image(vf, vb), E.image(vf, vy))
    return egal(gauche, droite)


def image_reunion_binaire(f="f", b="B", y="Y"):
    """⊢ f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩.   (E.II.27 binaire — CLOS, 0 hyp, INCOND.)"""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx = var("a"), var("x")
    reun = E.reunion(vb, vy)
    couple = appartient(E.couple(vx, va), vf)          # (x,a)∈f  (corps AXIOME_IMAGE, G:=f)
    inB = appartient(vx, vb)
    inY = appartient(vx, vy)

    # ── membre gauche : a∈f⟨B∪Y⟩ ⇔ (∃x)Bx ∨ (∃x)Yx ─────────────────────────
    L = membre_image(vf, reun, va)                     # ⇔ (∃x)(x∈B∪Y et (x,a)∈f)
    reun_x = _instance_reunion(vb, vy, vx)             # x∈B∪Y ⇔ (x∈B ∨ x∈Y)
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, couple), "x"))
    #     ⇔ (∃x)((x∈B ∨ x∈Y) et (x,a)∈f)
    commute = comm_et(ou(inB, inY), couple)
    distrib = et_ou_distrib(couple, inB, inY)
    recommute = ou_congruence(comm_et(couple, inB), comm_et(couple, inY))
    corps = etr(etr(commute, distrib), recommute)      # ((x∈B∨x∈Y) et (x,a)∈f) ⇔ (Bx ∨ Yx)
    Bx = et(inB, couple)
    Yx = et(inY, couple)
    L3 = etr(L2, congruence_existe(corps, "x"))         # ⇔ (∃x)(Bx ∨ Yx)
    L4 = etr(L3, existe_ou("x", Bx, Yx))                # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_L = N.generalisation("a", L4)

    # ── membre droit : a∈f⟨B⟩∪f⟨Y⟩ ⇔ (∃x)Bx ∨ (∃x)Yx ──────────────────────
    R = _instance_reunion(E.image(vf, vb), E.image(vf, vy), va)
    mB = membre_image(vf, vb, va)                      # a∈f⟨B⟩ ⇔ (∃x)Bx
    mY = membre_image(vf, vy, va)                      # a∈f⟨Y⟩ ⇔ (∃x)Yx
    R2 = etr(R, ou_congruence(mB, mY))                 # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_R = N.generalisation("a", R2)

    return egalite_par_extension(
        char_L, char_R,
        E.image(vf, reun),
        E.reunion(E.image(vf, vb), E.image(vf, vy)))


__all__ = [
    "membre_image", "membre_image_reciproque",
    "image_reunion_binaire", "cible_image_reunion_binaire",
]
