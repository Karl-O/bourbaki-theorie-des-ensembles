"""§II.4 (E.II.25–27) — IMAGE RÉCIPROQUE D'UNE RÉUNION BINAIRE.

Prop. 4 / 3e formule de l'§II.4 (cas binaire, énoncée E.II.27 pour les
correspondances), forme INCONDITIONNELLE :

        f⁻¹⟨ B ∪ Y ⟩  =  f⁻¹⟨B⟩ ∪ f⁻¹⟨Y⟩ .

Contrairement à f⁻¹⟨B∩Y⟩ / f⁻¹⟨B−Y⟩ (qui exigent l'univalence de f pour le sens
⊇), l'image réciproque d'une RÉUNION commute TOUJOURS avec ⋃, pour une
correspondance QUELCONQUE f.  C'est le cas binaire de `image_reciproque_reunion_
famille` (E.II.4, Prop. 4, 1re formule), mais livré comme énoncé à DEUX ensembles,
directement réutilisable dans la suite (E.II.27, formules sur ∪ / ∩ / complément).

f⁻¹⟨Z⟩ := image(reciproque(f), Z).  Preuve purement pointwise (A1 + AXIOME_IMAGE
+ AXIOME_REUNION), 0 hypothèse, theorie_ensembles() inchangée (22 axiomes).

  a∈f⁻¹⟨B∪Y⟩ ⇔ (∃x)(x∈B∪Y et (a,x)∈f)
             ⇔ (∃x)((x∈B ∨ x∈Y) et (a,x)∈f)
             ⇔ (∃x)((x∈B et (a,x)∈f) ∨ (x∈Y et (a,x)∈f))
             ⇔ (∃x)(x∈B et (a,x)∈f) ∨ (∃x)(x∈Y et (a,x)∈f)
             ⇔ a∈f⁻¹⟨B⟩ ∨ a∈f⁻¹⟨Y⟩  ⇔  a∈ f⁻¹⟨B⟩∪f⁻¹⟨Y⟩ .
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, appartient, existe, Terme
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
    equivalence_transitivite as etr, equivalence_symetrie as esym,
    et_congruence_gauche, comm_et, et_ou_distrib, ou_congruence)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.ensembles_produit_union_carre import existe_ou


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def membre_image_reciproque(f, Z, a):
    """⊢ a ∈ f⁻¹⟨Z⟩ ⇔ (∃x)(x∈Z et (a,x)∈f).

    Instance directe de AXIOME_IMAGE (image(G,X) avec G:=reciproque(f), X:=Z, y:=a)
    — le liant interne de l'axiome est « x », réutilisé tel quel."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, E.reciproque(f)), Z), a)


def _instance_reunion(a, b, z):
    """⊢ (z ∈ a∪b) ⇔ (z∈a ou z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def cible_image_reciproque_reunion_binaire(f="f", b="B", y="Y"):
    """Cible EXACTE : f⁻¹⟨B∪Y⟩ = f⁻¹⟨B⟩ ∪ f⁻¹⟨Y⟩."""
    vf, vb, vy = _t(f), _t(b), _t(y)
    gauche = E.image(E.reciproque(vf), E.reunion(vb, vy))
    droite = E.reunion(E.image(E.reciproque(vf), vb),
                       E.image(E.reciproque(vf), vy))
    return egal(gauche, droite)


def image_reciproque_reunion_binaire(f="f", b="B", y="Y"):
    """⊢ f⁻¹⟨B∪Y⟩ = f⁻¹⟨B⟩ ∪ f⁻¹⟨Y⟩.   (E.II.27 binaire — CLOS, 0 hyp, INCOND.)"""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx = var("a"), var("x")
    reun = E.reunion(vb, vy)
    couple = appartient(E.couple(vx, va), E.reciproque(vf))   # (x,a)∈f⁻¹  (corps AXIOME_IMAGE)
    inB = appartient(vx, vb)
    inY = appartient(vx, vy)

    # ── membre gauche : a∈f⁻¹⟨B∪Y⟩ ⇔ (∃x)(x∈B et (a,x)∈f) ∨ (∃x)(x∈Y et (a,x)∈f)
    L = membre_image_reciproque(vf, reun, va)           # ⇔ (∃x)(x∈B∪Y et (a,x)∈f)
    reun_x = _instance_reunion(vb, vy, vx)              # x∈B∪Y ⇔ (x∈B ∨ x∈Y)
    # remplacer x∈B∪Y par (x∈B∨x∈Y) sous ∃x dans le membre gauche du « et »
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, couple), "x"))
    #     ⇔ (∃x)((x∈B ∨ x∈Y) et (a,x)∈f)
    # distribution de « et » sur « ∨ » :
    #   ((x∈B ∨ x∈Y) et (a,x)∈f) ⇔ ((x∈B et (a,x)∈f) ∨ (x∈Y et (a,x)∈f))
    # et_ou_distrib donne (P et (Q∨R)) ⇔ ((P et Q)∨(P et R)) ; ici P=(a,x)∈f à droite,
    # on passe donc par commutation.
    P_QorR = et(ou(inB, inY), couple)                   # (x∈B∨x∈Y) et (a,x)∈f
    # (P_QorR) ⇔ ((a,x)∈f et (x∈B∨x∈Y))
    commute = comm_et(ou(inB, inY), couple)
    distrib = et_ou_distrib(couple, inB, inY)           # ((a,x)∈f et (x∈B∨x∈Y)) ⇔ (((a,x)∈f et x∈B) ∨ ((a,x)∈f et x∈Y))
    # ramener chaque disjonct à (x∈B et (a,x)∈f) / (x∈Y et (a,x)∈f)
    recommute = ou_congruence(comm_et(couple, inB), comm_et(couple, inY))
    #   (((a,x)∈f et x∈B) ∨ ((a,x)∈f et x∈Y)) ⇔ ((x∈B et (a,x)∈f) ∨ (x∈Y et (a,x)∈f))
    corps = etr(etr(commute, distrib), recommute)       # P_QorR ⇔ (Bx ∨ Yx)
    Bx = et(inB, couple)
    Yx = et(inY, couple)
    L3 = etr(L2, congruence_existe(corps, "x"))         # ⇔ (∃x)(Bx ∨ Yx)
    L4 = etr(L3, existe_ou("x", Bx, Yx))                # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_L = N.generalisation("a", L4)

    # ── membre droit : a∈f⁻¹⟨B⟩∪f⁻¹⟨Y⟩ ⇔ (∃x)Bx ∨ (∃x)Yx ────────────────────────
    R = _instance_reunion(E.image(E.reciproque(vf), vb),
                          E.image(E.reciproque(vf), vy), va)   # ⇔ a∈f⁻¹⟨B⟩ ∨ a∈f⁻¹⟨Y⟩
    mB = membre_image_reciproque(vf, vb, va)            # a∈f⁻¹⟨B⟩ ⇔ (∃x)Bx
    mY = membre_image_reciproque(vf, vy, va)            # a∈f⁻¹⟨Y⟩ ⇔ (∃x)Yx
    R2 = etr(R, ou_congruence(mB, mY))                  # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_R = N.generalisation("a", R2)

    return egalite_par_extension(
        char_L, char_R,
        E.image(E.reciproque(vf), reun),
        E.reunion(E.image(E.reciproque(vf), vb), E.image(E.reciproque(vf), vy)))


__all__ = ["image_reciproque_reunion_binaire",
           "cible_image_reciproque_reunion_binaire",
           "membre_image_reciproque"]
