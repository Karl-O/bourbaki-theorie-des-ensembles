"""Chapitre III §2 — Une partie d'un ensemble bien ordonné est bien ordonnée.

THÉORÈME (E.III.2.1, conséquence immédiate de la Définition 1) :

    { est_bien_ordonne(R, E),  inclus(S, E) }  ⊢  est_bien_ordonne(R_S, S)

où R_S = ordre_induit(R, S) est l'ordre que R INDUIT sur S, c.-à-d.
    R_S{x,y} := (R{x,y} et x∈S et y∈S)        (E.III.1.1, Exemple 2).

──────────────────────────────────────────────────────────────────────────────
POURQUOI L'ORDRE INDUIT, ET NON R LUI-MÊME (honnêteté du noyau)
──────────────────────────────────────────────────────────────────────────────
La cible naïve « est_bien_ordonne(R, S) » (MÊME relation R) n'est PAS un théorème
sous la seule hypothèse S⊂E — elle est même FAUSSE en général.  En effet
`est_bien_ordonne` exige `est_relation_ordre_dans(R, S)`, qui contient le facteur
`est_reflexive_dans_ordre(R, S)` = (∀x)(R{x,x} ⇔ x∈S).  Le SENS RETOUR de cette
équivalence, R{x,x} ⇒ x∈S, est indérivable de `est_reflexive_dans_ordre(R, E)`
(qui ne donne que R{x,x} ⇒ x∈E) et de S⊂E (qui ne donne que x∈S ⇒ x∈E, jamais la
réciproque x∈E ⇒ x∈S) : un point de E∖S vérifie encore R{x,x} sans être dans S.

La formulation FIDÈLE de Bourbaki (« la relation induite par R sur S est un bon
ordre ») est donc avec R_S.  Pour R_S, le sens retour devient PROUVABLE :
R_S{x,x} = (R{x,x} et x∈S et x∈S) donne x∈S directement, et réciproquement x∈S
entraîne x∈E (par S⊂E) puis R{x,x} (réflexivité de R dans E).  C'est le présent
théorème, entièrement clos par le noyau (theorie_ensembles inchangé = 22 axiomes).

Tout est CERTIFIÉ par le noyau abrégé (type Theoreme opaque).  R{x,y} = fonction
Python (Terme, Terme) → Formule (pattern §II.6 / §III.1).  R notée ≤.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, et, ou, non, egal, impl, appartient,
                                       inclus, pourtout, existe)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_abrege import VIDE
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, inclusion_transitive)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe)


def _terme(t):
    from bourbaki.logique.formule import Terme
    return t if isinstance(t, Terme) else var(t)


def sous_ensemble_bien_ordonne(R, E_="E", S="S",
                               x="x", y="y", z="z", X="X", a="a", w="w"):
    """⊢ { est_bien_ordonne(R, E),  inclus(S, E) }  ⊢  est_bien_ordonne(R_S, S),
    où R_S = ordre_induit(R, S) (ordre induit par R sur la partie S).

    Une partie S⊂E d'un ensemble bien ordonné (E, R) est bien ordonnée par
    l'ordre que R induit sur S (E.III.2.1, Définition 1)."""
    ve, vS = _terme(E_), _terme(S)
    vx, vy, vz = var(x), var(y), var(z)
    vX, va, vw = var(X), var(a), var(w)

    # Relation induite  R_S{u,v} = (R{u,v} et u∈S et v∈S)   (= ordre_induit(R,S))
    def RS(u, v):
        return E.ordre_induit(R, vS)(u, v)

    # ── Hypothèses ────────────────────────────────────────────────────────────
    hyp_bo = E.est_bien_ordonne(R, ve, x, y, z, X, a, w)   # E bien ordonné par R
    hyp_inc = inclus(vS, ve)                               # S ⊂ E
    Hbo = N.assume(hyp_bo)
    Hinc = N.assume(hyp_inc)

    # composants du bon ordre de E
    ord_E = conjonction_elim_gauche(Hbo)                   # est_relation_ordre_dans(R,E)
    min_E = conjonction_elim_droite(Hbo)                   # (∀X)((X⊂E et X≠∅) ⇒ ∃a …)

    ro_E = conjonction_elim_gauche(ord_E)                  # est_relation_ordre(R)
    refl_E = conjonction_elim_droite(ord_E)                # est_reflexive_dans_ordre(R,E)
    trans_et_antisym = conjonction_elim_gauche(ro_E)       # (transitif et antisym)
    trans_E = conjonction_elim_gauche(trans_et_antisym)    # ordre_transitif(R)
    antisym_E = conjonction_elim_droite(trans_et_antisym)  # ordre_antisymetrique(R)
    reflimpl_E = conjonction_elim_droite(ro_E)             # ordre_reflexif_implicite(R)

    # ════════════════════════════════════════════════════════════════════════
    # PARTIE 1 — est_relation_ordre_dans(R_S, S)
    # ════════════════════════════════════════════════════════════════════════

    # ── 1a. transitivité de R_S : (∀x)(∀y)(∀z)((R_S{x,y} et R_S{y,z}) ⇒ R_S{x,z})
    prem_t = et(RS(vx, vy), RS(vy, vz))
    Ht = N.assume(prem_t)
    rsxy = conjonction_elim_gauche(Ht)                     # R_S{x,y}
    rsyz = conjonction_elim_droite(Ht)                     # R_S{y,z}
    # R{x,y}, x∈S  (depuis R_S{x,y} = (R{x,y} et x∈S) et y∈S)
    rxy = conjonction_elim_gauche(conjonction_elim_gauche(rsxy))   # R{x,y}
    x_in_S = conjonction_elim_droite(conjonction_elim_gauche(rsxy))  # x∈S
    ryz = conjonction_elim_gauche(conjonction_elim_gauche(rsyz))   # R{y,z}
    z_in_S = conjonction_elim_droite(rsyz)                          # z∈S
    # R transitive : ((R{x,y} et R{y,z}) ⇒ R{x,z})
    trans_inst = instancie(instancie(instancie(trans_E, vx), vy), vz)
    rxz = N.modus_ponens(conjonction_intro(rxy, ryz), trans_inst)   # R{x,z}
    rs_xz = conjonction_intro(conjonction_intro(rxz, x_in_S), z_in_S)  # R_S{x,z}
    body_t = N.loi_deduction(prem_t, rs_xz)
    trans_S = N.generalisation(x, N.generalisation(y, N.generalisation(z, body_t)))

    # ── 1b. antisymétrie de R_S : (∀x)(∀y)((R_S{x,y} et R_S{y,x}) ⇒ x=y)
    prem_a = et(RS(vx, vy), RS(vy, vx))
    Ha = N.assume(prem_a)
    rsxy2 = conjonction_elim_gauche(Ha)
    rsyx2 = conjonction_elim_droite(Ha)
    rxy2 = conjonction_elim_gauche(conjonction_elim_gauche(rsxy2))  # R{x,y}
    ryx2 = conjonction_elim_gauche(conjonction_elim_gauche(rsyx2))  # R{y,x}
    antisym_inst = instancie(instancie(antisym_E, vx), vy)          # ((R{x,y} et R{y,x})⇒x=y)
    xeqy = N.modus_ponens(conjonction_intro(rxy2, ryx2), antisym_inst)
    body_a = N.loi_deduction(prem_a, xeqy)
    antisym_S = N.generalisation(x, N.generalisation(y, body_a))

    # ── 1c. réflexivité implicite de R_S : (∀x)(∀y)(R_S{x,y} ⇒ (R_S{x,x} et R_S{y,y}))
    Hr = N.assume(RS(vx, vy))
    rxy3 = conjonction_elim_gauche(conjonction_elim_gauche(Hr))     # R{x,y}
    x_in_S3 = conjonction_elim_droite(conjonction_elim_gauche(Hr))  # x∈S
    y_in_S3 = conjonction_elim_droite(Hr)                           # y∈S
    reflimpl_inst = instancie(instancie(reflimpl_E, vx), vy)        # R{x,y}⇒(R{x,x} et R{y,y})
    rxx_ryy = N.modus_ponens(rxy3, reflimpl_inst)                   # R{x,x} et R{y,y}
    rxx = conjonction_elim_gauche(rxx_ryy)                          # R{x,x}
    ryy = conjonction_elim_droite(rxx_ryy)                          # R{y,y}
    rs_xx = conjonction_intro(conjonction_intro(rxx, x_in_S3), x_in_S3)  # R_S{x,x}
    rs_yy = conjonction_intro(conjonction_intro(ryy, y_in_S3), y_in_S3)  # R_S{y,y}
    body_r = N.loi_deduction(RS(vx, vy), conjonction_intro(rs_xx, rs_yy))
    reflimpl_S = N.generalisation(x, N.generalisation(y, body_r))

    # est_relation_ordre(R_S) = ((transitif et antisym) et reflimpl)
    ro_S = conjonction_intro(conjonction_intro(trans_S, antisym_S), reflimpl_S)

    # ── 1d. R_S réflexive dans S : (∀x)(R_S{x,x} ⇔ x∈S)
    # sens AVANT : R_S{x,x} ⇒ x∈S  (deuxième composante de R_S{x,x})
    Hf = N.assume(RS(vx, vx))
    x_in_S_fwd = conjonction_elim_droite(Hf)                        # x∈S
    fwd = N.loi_deduction(RS(vx, vx), x_in_S_fwd)                   # R_S{x,x} ⇒ x∈S
    # sens ARRIÈRE : x∈S ⇒ R_S{x,x}.  x∈S ⇒ x∈E (S⊂E) ⇒ R{x,x} (réfl. de R dans E).
    Hb = N.assume(appartient(vx, vS))                               # x∈S
    inc_inst = instancie(Hinc, vx)                                  # x∈S ⇒ x∈E
    x_in_E = N.modus_ponens(Hb, inc_inst)                           # x∈E
    refl_inst = instancie(refl_E, vx)                               # R{x,x} ⇔ x∈E
    rxx_b = N.modus_ponens(x_in_E, equivalence_arriere(refl_inst))  # R{x,x}
    rs_xx_b = conjonction_intro(conjonction_intro(rxx_b, Hb), Hb)   # R_S{x,x}
    bwd = N.loi_deduction(appartient(vx, vS), rs_xx_b)              # x∈S ⇒ R_S{x,x}
    equiv_x = conjonction_intro(fwd, bwd)                           # R_S{x,x} ⇔ x∈S
    refl_S = N.generalisation(x, equiv_x)                          # (∀x)(R_S{x,x} ⇔ x∈S)

    ord_S = conjonction_intro(ro_S, refl_S)   # est_relation_ordre_dans(R_S, S)

    # ════════════════════════════════════════════════════════════════════════
    # PARTIE 2 — toute partie non vide de S a un plus petit élément (pour R_S)
    #   (∀X)((X⊂S et X≠∅) ⇒ (∃a)(a∈X et (∀w)(w∈X ⇒ R_S{a,w})))
    # ════════════════════════════════════════════════════════════════════════
    prem_min = et(inclus(vX, vS), non(egal(vX, VIDE)))
    Hm = N.assume(prem_min)
    X_inc_S = conjonction_elim_gauche(Hm)                           # X⊂S
    X_nonvide = conjonction_elim_droite(Hm)                         # X≠∅

    # X⊂E par transitivité de l'inclusion : (X⊂S et S⊂E) ⇒ X⊂E
    trans_incl = inclusion_transitive(X, S, E_)
    X_inc_E = N.modus_ponens(conjonction_intro(X_inc_S, Hinc), trans_incl)

    # déclenche le minimum de E sur X : ((X⊂E et X≠∅) ⇒ ∃a(a∈X et ∀w(w∈X ⇒ R{a,w})))
    min_E_inst = instancie(min_E, vX)
    min_prem_E = conjonction_intro(X_inc_E, X_nonvide)
    exists_min_R = N.modus_ponens(min_prem_E, min_E_inst)
    #   = (∃a)(a∈X et (∀w)(w∈X ⇒ R{a,w}))

    # On veut (∃a)(a∈X et (∀w)(w∈X ⇒ R_S{a,w})).  On transforme le CORPS sous le ∃a.
    # Corps actuel : a∈X et (∀w)(w∈X ⇒ R{a,w})
    corps_R = et(appartient(va, vX),
                 pourtout(w, impl(appartient(vw, vX), R(va, vw))))
    Hc = N.assume(corps_R)
    a_in_X = conjonction_elim_gauche(Hc)                            # a∈X
    forall_w_R = conjonction_elim_droite(Hc)                        # (∀w)(w∈X ⇒ R{a,w})
    # a∈S : a∈X ⇒ a∈S (X⊂S)
    a_in_S = N.modus_ponens(a_in_X, instancie(X_inc_S, va))         # a∈S
    # construire (∀w)(w∈X ⇒ R_S{a,w})
    Hw = N.assume(appartient(vw, vX))                               # w∈X
    w_imp_R = instancie(forall_w_R, vw)                             # w∈X ⇒ R{a,w}
    raw = N.modus_ponens(Hw, w_imp_R)                               # R{a,w}
    w_in_S = N.modus_ponens(Hw, instancie(X_inc_S, vw))            # w∈S
    rs_aw = conjonction_intro(conjonction_intro(raw, a_in_S), w_in_S)  # R_S{a,w}
    body_w = N.loi_deduction(appartient(vw, vX), rs_aw)            # w∈X ⇒ R_S{a,w}
    forall_w_RS = N.generalisation(w, body_w)                      # (∀w)(w∈X ⇒ R_S{a,w})
    corps_RS = conjonction_intro(a_in_X, forall_w_RS)             # a∈X et (∀w)(…R_S…)
    # corps_R ⇒ corps_RS  (sous H), puis ∃a corps_R ⇒ ∃a corps_RS (monotonie de ∃).
    # 'a' n'est libre ni dans hyp_bo, hyp_inc, ni dans prem_min — monotonie licite.
    corps_impl = N.loi_deduction(corps_R, corps_RS)
    ex_to_ex = monotonie_existe(corps_impl, a)        # (∃a)corps_R ⇒ (∃a)corps_RS
    exists_min_RS = N.modus_ponens(exists_min_R, ex_to_ex)
    body_min = N.loi_deduction(prem_min, exists_min_RS)
    min_S = N.generalisation(X, body_min)

    # ════════════════════════════════════════════════════════════════════════
    # CONCLUSION — est_bien_ordonne(R_S, S) = (ord_S et min_S)
    # ════════════════════════════════════════════════════════════════════════
    return conjonction_intro(ord_S, min_S)


__all__ = ["sous_ensemble_bien_ordonne"]
