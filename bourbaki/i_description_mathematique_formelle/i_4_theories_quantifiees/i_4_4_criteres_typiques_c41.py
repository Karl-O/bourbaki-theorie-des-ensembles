"""Critère C41 des quantificateurs TYPIQUES (Bourbaki §I.4.4, E I.37).

Énoncé Bourbaki verbatim (C41) :

  « Soient A, R et S des relations de 𝒯, et x une lettre qui ne figure pas dans R.
    Les relations
        (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S)
        (∃_A x)(R et S) ⇔ (R et (∃_A x)S)
    sont des théorèmes de 𝒯. »

(C'est l'extraction d'un facteur R indépendant de x hors du quantificateur
typique : ou-distribution pour ∀, et-distribution pour ∃.)

Quantificateurs typiques (mêmes nœuds que `criteres_typiques_c39_c42`) :
    (∃_A x)R := (∃x)(A et R)            `existe_typique`
    (∀_A x)R := ¬(∃x)(A et ¬R)         `pourtout_typique`

RÉSULTATS (CLOS — théorèmes purs, certifiés par le noyau LCF) :
    ⊢ (∃_A x)(R et S) ⇔ (R et (∃_A x)S)      `c41_existe_typique`
    ⊢ (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S)      `c41_pourtout_typique`

STRATÉGIE (tout dérivé des primitives N.* via tactiques déjà certifiées) :
  ∃ : (∃x)(A et (R et S)) ⇔ (∃x)(R et (A et S))  [réarrangement de et sous ∃]
      ⇔ (R et (∃x)(A et S))                       [C33 `et_existe_droite`, x∉R].
  ∀ : DUAL du cas ∃ sur ¬R, ¬S.  ¬(R ou S) ⇔ (¬R et ¬S) [De Morgan], puis C41-∃
      donne (∃x)(A et (¬R et ¬S)) ⇔ (¬R et (∃x)(A et ¬S)) ; on NÉGUE
      (`equiv_neg`) et on retombe par De Morgan ¬(¬R et P) ⇔ (R ou ¬P) [+ ¬¬R⇔R],
      où ¬P = ¬(∃x)(A et ¬S) = (∀_A x)S.

INVARIANT : C41 est CLOS (0 hypothèse) ; condition de fraîcheur x∉R imposée (sinon
`ValueError`). Aucune tautologie déguisée ; theorie == 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, et, ou, equiv, existe, libres_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_transitivite, equivalence_symetrie, et_congruence_droite,
    ou_congruence, demorgan_ou, demorgan_et, dne, dni, equiv_neg)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    congruence_existe, et_existe_droite)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_4_criteres_typiques_c39_c42 import (
    existe_typique, pourtout_typique)


def _equiv_refl(f):
    """⊢ F ⇔ F  (identité, pour `ou_congruence` sur un membre inchangé)."""
    imp = N.loi_deduction(f, N.assume(f))
    return conjonction_intro(imp, imp)


def _et_rearrange(a, r, s):
    """⊢ (A et (R et S)) ⇔ (R et (A et S))   (commutation/associativité de et)."""
    h = N.assume(et(a, et(r, s)))
    va = conjonction_elim_gauche(h)
    vrs = conjonction_elim_droite(h)
    vr, vs = conjonction_elim_gauche(vrs), conjonction_elim_droite(vrs)
    fwd = N.loi_deduction(et(a, et(r, s)), conjonction_intro(vr, conjonction_intro(va, vs)))
    h2 = N.assume(et(r, et(a, s)))
    wr = conjonction_elim_gauche(h2)
    was = conjonction_elim_droite(h2)
    wa, ws = conjonction_elim_gauche(was), conjonction_elim_droite(was)
    bwd = N.loi_deduction(et(r, et(a, s)), conjonction_intro(wa, conjonction_intro(wr, ws)))
    return conjonction_intro(fwd, bwd)


# @livre Ch.I §4.4 Crit.41 | E I.37 L.43-46 | PDF p.37
def c41_existe_typique(a, r, s, x):
    """⊢ (∃_A x)(R et S) ⇔ (R et (∃_A x)S).   (C41, 2ᵉ relation ; x ∉ R.)"""
    if x in libres_f(r):
        raise ValueError(f"C41 : la lettre {x!r} doit ne PAS figurer dans R")
    p1 = _et_rearrange(a, r, s)                          # (A et (R et S)) ⇔ (R et (A et S))
    lift = congruence_existe(p1, x)                      # (∃x)(A et(R et S)) ⇔ (∃x)(R et(A et S))
    ee = et_existe_droite(r, x, et(a, s))               # (R et (∃x)(A et S)) ⇔ (∃x)(R et(A et S))
    return equivalence_transitivite(lift, equivalence_symetrie(ee))


def c41_existe_typique_cible(a, r, s, x):
    """Énoncé visé de `c41_existe_typique` (vérification stricte)."""
    return equiv(existe_typique(a, x, et(r, s)), et(r, existe_typique(a, x, s)))


# @livre Ch.I §4.4 Crit.41 | E I.37 L.43-46 | PDF p.37
def c41_pourtout_typique(a, r, s, x):
    """⊢ (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S).   (C41, 1ʳᵉ relation ; x ∉ R.)"""
    if x in libres_f(r):
        raise ValueError(f"C41 : la lettre {x!r} doit ne PAS figurer dans R")
    P = existe(x, et(a, non(s)))                         # (∃x)(A et ¬S)  (= (∃_A x)¬S)
    # (A et ¬(R ou S)) ⇔ (A et (¬R et ¬S)), lifté sous ∃x :
    innerA = et_congruence_droite(a, demorgan_ou(r, s))  # (A et ¬(RouS)) ⇔ (A et (¬R et ¬S))
    liftA = congruence_existe(innerA, x)
    c41e = c41_existe_typique(a, non(r), non(s), x)      # (∃x)(A et(¬R et ¬S)) ⇔ (¬R et P)
    chainB = equivalence_transitivite(liftA, c41e)       # (∃x)(A et ¬(RouS)) ⇔ (¬R et P)
    negC = equiv_neg(chainB)                             # ¬(∃x)(A et ¬(RouS)) ⇔ ¬(¬R et P)
    # ¬(¬R et P) ⇔ (R ou ¬P) :
    dmE = demorgan_et(non(r), P)                         # ¬(¬R et P) ⇔ (¬¬R ou ¬P)
    congrD = ou_congruence(conjonction_intro(dne(r), dni(r)), _equiv_refl(non(P)))
    stepD = equivalence_transitivite(dmE, congrD)        # ¬(¬R et P) ⇔ (R ou ¬P)
    return equivalence_transitivite(negC, stepD)


def c41_pourtout_typique_cible(a, r, s, x):
    """Énoncé visé de `c41_pourtout_typique` (vérification stricte)."""
    return equiv(pourtout_typique(a, x, ou(r, s)), ou(r, pourtout_typique(a, x, s)))


__all__ = ["c41_existe_typique", "c41_existe_typique_cible",
           "c41_pourtout_typique", "c41_pourtout_typique_cible"]
