"""§II.3.8 — Théorème 1 f) : descente d'injectivité de f'' vers f, et rétraction
de f'' au niveau VALEURS.  Dual EXACT de e)/a) avec les rôles f ↔ f'' inversés.

Bourbaki, Théorème 1 f) : « Si f'' = f'∘f est une injection (resp. admet une
rétraction r''), alors f en hérite. »  On livre ici les DEUX briques load-bearing,
au sens VALEURS (encodage matriciel du projet, Déf. 11) :

  • theoreme1_f_injective_valeur — descente d'injectivité de f'' = f'∘f sur A :
        ⊢  injective_dans(F'', A)
            ⇒ (∀x)(∀x')( (x∈A ∧ x'∈A ∧ f''(x) = f''(x'))  ⇒  x = x' ),
    avec F'' = E.composee(F', F).  C'est l'INSTANCIATION de l'injectivité gardée de
    f'' au couple (x, x')∈A² — strictement le DUAL de la forme repliée de
    theoreme1_c, avec f remplacé par f''.  FORME REPLIÉE pure (antécédent f''(x)=
    f''(x'), c.-à-d. (f'∘f)(x)=(f'∘f)(x')) : le pont déplié↔replié vers f'(f(x))
    via composition_valeur_t alourdirait le séquent de 4 hyps C46 structurelles
    (dom F=A, dom F'=B, happlique, f'' fonctionnel — cf. _cv_point de
    ensembles_retractions_props.py).  On livre donc la forme repliée, CLOSE
    (est_clos) : injective_dans(F'', A) est l'unique hyp, déchargée dans
    l'implication externe.

  • theoreme1_f_retraction_valeur — rétraction de f'' propagée sur f :
        ⊢_{R'' rétraction de F'' sur A}  (x∈A) ⇒ f(r''(f''(x))) = f(x),
    avec F'' = E.composee(F', F).  Calque LIGNE À LIGNE
    theoreme1_a_retraction_valeur : instanciation de est_retraction(R'',F'',A) au
    point x (donne r''(f''(x))=x sous x∈A), puis congruence sous f(·) :
    f(r''(f''(x))) = f(x).  FORME REPLIÉE (f''(x) = valeur(comp, x)) : le passage à
    la forme dépliée f(r''(f'(f(x)))) via composition_valeur_t en un point qui est
    lui-même une valeur τ déclenche la capture de liant documentée dans
    composee_associee_droite_valeur ; on garde la forme repliée, capture-saine.
    Hypothèse laissée explicite (jamais postulée, déchargée dans l'externe) :
    est_retraction(R'', F'', A) [(∀x∈A) r''(f''(x))=x].

Primitives N.* uniquement (aucun Theoreme fabriqué).  Calqué sur
`theoreme1_e_injective_valeur` (patron gardes + loi_deduction + generalisation ×2)
et `theoreme1_a_retraction_valeur` (patron rétraction-congruence) de §II.3.8.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient,
                                       impl, pourtout, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import congruence_terme


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


# ── THÉORÈME 1 f) — descente d'injectivité de f'' = f'∘f vers f (VALEURS) ──────
# @livre Ch.II §3.8 Th.1 | E II.19 L.24-25 | PDF p.70
def theoreme1_f_injective_valeur(f="F", fp="Fp", a="A"):
    """⊢  injective_dans(F'', A) ⇒
            (∀x)(∀x')( (x∈A ∧ x'∈A ∧ f''(x) = f''(x'))  ⇒  x = x' ),
    où F'' = E.composee(F', F).

    THÉORÈME 1 f), brique « f'' injective ⇒ … (au sens valeurs sur A) ».  DUAL EXACT
    de la forme repliée de theoreme1_c (f ↔ f'') : on instancie l'injectivité gardée
    de f'' au couple (x, x')∈A² — injective_dans(F'',A) est exactement
    (∀x,x')((x∈A ∧ x'∈A ∧ f''(x)=f''(x')) ⇒ x=x') — puis on referme.  FORME REPLIÉE
    (antécédent f''(x)=f''(x') ; déplié : (f'∘f)(x)=(f'∘f)(x')) : la conversion vers
    f'(f(x)) via composition_valeur_t introduirait 4 hyps C46 ; on s'en abstient.
    CLOSE (est_clos) : injective_dans(F'',A) est la SEULE hyp, déchargée dans
    l'implication externe — rien de libre en x, x', d'où la généralisation ×2."""
    vF, vFp, vA = _T(f), _T(fp), _T(a)
    vx, vxp = var("x"), var("xp")
    comp = E.composee(vFp, vF)                              # f'' = f'∘f
    fppx, fppxp = E.valeur(comp, vx), E.valeur(comp, vxp)   # f''(x), f''(x')

    # injective_dans(F'',A) : (∀u)(∀u')((u∈A ∧ u'∈A ∧ F''(u)=F''(u')) ⇒ u=u')
    hinj = N.assume(E.injective_dans(comp, vA))
    # instancie au couple (x, x') :
    #   (x∈A ∧ x'∈A ∧ F''(x)=F''(x')) ⇒ x=x'
    inst = instancie(instancie(hinj, vx), vxp)

    # antécédent interne (gardé) : (x∈A ∧ x'∈A) ∧ f''(x)=f''(x')
    eq_hyp = egal(fppx, fppxp)                              # f''(x) = f''(x')
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), eq_hyp)
    h = N.assume(ante)
    x_inA = conjonction_elim_gauche(conjonction_elim_gauche(h))   # x ∈ A
    xp_inA = conjonction_elim_droite(conjonction_elim_gauche(h))  # x' ∈ A
    heq = conjonction_elim_droite(h)                             # f''(x)=f''(x')

    # antécédent de l'instance d'injectivité de f'' : (x∈A ∧ x'∈A) ∧ f''(x)=f''(x')
    ante_inj = conjonction_intro(conjonction_intro(x_inA, xp_inA), heq)
    x_eq = N.modus_ponens(ante_inj, inst)                       # x = x'

    # referme l'implication interne (gardée), généralise sur x' puis x
    inner = N.loi_deduction(ante, x_eq)
    gen = N.generalisation("x", N.generalisation("xp", inner))
    return N.loi_deduction(E.injective_dans(comp, vA), gen)


def cible_theoreme1_f_injective_valeur(f="F", fp="Fp", a="A"):
    """Cible exacte : injective_dans(F'',A) ⇒
       (∀x,x')((x∈A ∧ x'∈A ∧ f''(x)=f''(x')) ⇒ x=x'),  F''=composee(F',F)."""
    vF, vFp, vA = _T(f), _T(fp), _T(a)
    vx, vxp = var("x"), var("xp")
    comp = E.composee(vFp, vF)
    fppx, fppxp = E.valeur(comp, vx), E.valeur(comp, vxp)
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), egal(fppx, fppxp))
    inner = impl(ante, egal(vx, vxp))
    return impl(E.injective_dans(comp, vA),
                pourtout("x", pourtout("xp", inner)))


def hypotheses_theoreme1_f_injective_valeur():
    """Hypothèses résiduelles EXACTES : ∅ (théorème CLOS).

    injective_dans(F'',A) est déchargée dans l'implication externe ; la conclusion
    est close en (x,x').  Aucune hyp résiduelle (forme repliée, sans pont C46)."""
    return set()


# ── THÉORÈME 1 f) — rétraction de f'' = f'∘f propagée sur f (VALEURS) ──────────
# @livre Ch.II §3.8 Th.1 | E II.19 L.24-25 | PDF p.70
def theoreme1_f_retraction_valeur(r="Rpp", f="F", fp="Fp", a="A"):
    """⊢_{R'' rétraction de F'' sur A}  (x∈A) ⇒ f(r''(f''(x))) = f(x),
    où F'' = E.composee(F', F).

    THÉORÈME 1 f), brique « r'' rétraction de f'' ⇒ identité propagée sous f(·) ».
    Calque LIGNE À LIGNE theoreme1_a_retraction_valeur : R'' rétraction de F'' sur A
    [est_retraction(R'',F'',A) : (∀x∈A) r''(f''(x))=x] donne, instanciée au point x
    sous x∈A, r''(f''(x))=x ; par congruence sous f(·) on conclut
        f(r''(f''(x))) = f(x).
    FORME REPLIÉE (f''(x) = valeur(comp, x)) : la forme dépliée f(r''(f'(f(x))))
    exigerait composition_valeur_t en un point τ (capture du liant, cf.
    composee_associee_droite_valeur) ; on garde la forme repliée, capture-saine.
    Hypothèse laissée explicite (jamais postulée) : est_retraction(R'',F'',A),
    DÉCHARGÉE dans l'implication externe."""
    vR, vF, vFp, vA = _T(r), _T(f), _T(fp), _T(a)
    vx = var("x")
    comp = E.composee(vFp, vF)                              # f'' = f'∘f
    fppx = E.valeur(comp, vx)                               # f''(x)
    hxA = N.assume(appartient(vx, vA))                      # x∈A
    # r''(f''(x)) = x       [R'' rétraction de F'' sur A, au point x∈A]
    hret = N.assume(E.est_retraction(vR, comp, vA))        # (∀x∈A) r''(f''(x))=x
    inst = instancie(hret, vx)                              # x∈A ⇒ r''(f''(x))=x
    r_eq = N.modus_ponens(hxA, inst)                        # r''(f''(x)) = x
    # f(r''(f''(x))) = f(x)                                  (congruence sous f(·))
    rfppx = E.valeur(vR, fppx)                              # r''(f''(x))
    f_cong = N.modus_ponens(r_eq, congruence_terme(
        rfppx, vx, E.valeur(vF, var("w")), "w"))           # f(r''(f''(x))) = f(x)
    inner = N.loi_deduction(appartient(vx, vA), f_cong)    # (x∈A) ⇒ f(r''(f''(x)))=f(x)
    return N.loi_deduction(E.est_retraction(vR, comp, vA), inner)


def cible_theoreme1_f_retraction_valeur(r="Rpp", f="F", fp="Fp", a="A"):
    """Cible exacte : est_retraction(R'',F'',A) ⇒
       ((x∈A) ⇒ f(r''(f''(x))) = f(x)),  F''=composee(F',F)."""
    vR, vF, vFp, vA = _T(r), _T(f), _T(fp), _T(a)
    vx = var("x")
    comp = E.composee(vFp, vF)
    fppx = E.valeur(comp, vx)
    lhs = E.valeur(vF, E.valeur(vR, fppx))                 # f(r''(f''(x)))
    inner = impl(appartient(vx, vA), egal(lhs, E.valeur(vF, vx)))
    return impl(E.est_retraction(vR, comp, vA), inner)


def hypotheses_theoreme1_f_retraction_valeur():
    """Hypothèses résiduelles EXACTES : ∅ (théorème CLOS).

    est_retraction(R'',F'',A) est déchargée dans l'implication externe ; x∈A l'est
    dans l'implication interne.  Aucune hyp résiduelle."""
    return set()


__all__ = ["theoreme1_f_injective_valeur",
           "cible_theoreme1_f_injective_valeur",
           "hypotheses_theoreme1_f_injective_valeur",
           "theoreme1_f_retraction_valeur",
           "cible_theoreme1_f_retraction_valeur",
           "hypotheses_theoreme1_f_retraction_valeur"]
