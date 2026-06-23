"""§II.3.8 — Théorème 1 e) : descente d'injectivité de f' vers f (forme VALEURS).

Bourbaki, Théorème 1 e) : « Si f'' = f'∘f est une surjection et f' une injection,
alors f est une surjection » — la preuve COMPLÈTE de e) passe par f' bijection +
réciproque f'⁻¹ et est LOURDE (pont valeurs↔graphe sur f'⁻¹).  On livre ici la
BRIQUE EXPLOITABLE et fidèle qui en est la composante load-bearing : la descente
d'injectivité de f' vers f, au sens VALEURS.

    ⊢_{(∀v)(v∈A ⇒ f(v)∈B)}  injective_dans(F', B)
        ⇒ (∀x)(∀x')( (x∈A ∧ x'∈A ∧ f'(f(x)) = f'(f(x')))  ⇒  f(x) = f(x') ).

Lue : « f'∘f injective au sens VALEURS (sur A) découle de l'injectivité de f' »,
via l'instanciation de l'injectivité GARDÉE de f' au couple (f(x), f(x'))∈B² :
c'est exactement la descente « f'(u)=f'(u') ⇒ u=u' » appliquée à u=f(x), u'=f(x').
C'est la composante « f' injective ⇒ (f'∘f injective ⇒ f injective au sens valeurs) »
de e), couplée à f'∘f injective ⇒ f injective (Théorème 1 c) déjà clos).

Hypothèse de typage C46 HONNÊTE (jamais postulée, laissée explicite comme SÉQUENT) :
    happlique := (∀v)(v∈A ⇒ f(v)∈B)   [« f applique A dans B »].
C'est exactement la donnée « f : A→B » du Théorème 1.  Les gardes ponctuelles
f(x)∈B, f(x')∈B — requises par l'injectivité gardée de f' (injective_dans impose
u∈B) — en sont DÉRIVÉES inline sous x∈A, x'∈A (motif _cv_point de theoreme1_c),
ce qui permet la généralisation sur x, x' : la conclusion est CLOSE dans (x,x') et
n'a pour hypothèse résiduelle que happlique (rien de libre en x, x').

injective_dans(F',B) est DÉCHARGÉE dans l'implication externe.  Calqué sur
`theoreme1_c_injective` (gardes d'appartenance dérivées de happlique + instanciation
de l'injectivité gardée) et `theoreme1_d_surjective_valeur` (loi_deduction +
generalisation ×2) de ensembles_retractions_props.py.  Primitives N.* uniquement.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient,
                                       impl, pourtout, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite)


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


# ── THÉORÈME 1 e) — descente d'injectivité de f' vers f (niveau VALEURS) ──────
def theoreme1_e_injective_valeur(f="F", fp="Fp", a="A", b="B"):
    """⊢_{(∀v)(v∈A ⇒ f(v)∈B)}  injective_dans(F', B) ⇒
            (∀x)(∀x')( (x∈A ∧ x'∈A ∧ f'(f(x)) = f'(f(x')))  ⇒  f(x) = f(x') ).

    THÉORÈME 1 e), brique « f' injective ⇒ f'∘f injective au sens valeurs (sur A) ».
    Si f' est injective sur B [injective_dans(F',B) : (∀u,u'∈B)(F'(u)=F'(u') ⇒ u=u')],
    alors, dès que x,x'∈A et f'(f(x))=f'(f(x')), on dérive f(x)∈B, f(x')∈B de
    happlique, puis on instancie l'injectivité de f' au couple (f(x), f(x'))∈B²
    pour conclure f(x)=f(x').

    Hypothèse de typage C46 HONNÊTE laissée explicite (SÉQUENT, jamais postulée) :
        happlique := (∀v)(v∈A ⇒ f(v)∈B)   [« f applique A dans B »].
    injective_dans(F',B) est DÉCHARGÉE dans l'implication externe.  La conclusion est
    CLOSE dans (x,x') : happlique est la SEULE hypothèse résiduelle (rien de libre en
    x, x'), ce qui légitime la généralisation ×2."""
    vF, vFp, vA, vB = _T(f), _T(fp), _T(a), _T(b)
    vx, vxp, vv = var("x"), var("xp"), var("v")
    fx, fxp = E.valeur(vF, vx), E.valeur(vF, vxp)        # f(x), f(x')
    fpfx, fpfxp = E.valeur(vFp, fx), E.valeur(vFp, fxp)  # f'(f(x)), f'(f(x'))

    # injective_dans(F',B) : (∀u)(∀u')((u∈B ∧ u'∈B ∧ F'(u)=F'(u')) ⇒ u=u')
    hinj = N.assume(E.injective_dans(vFp, vB))
    # instancie au couple (f(x), f(x')) :
    #   (f(x)∈B ∧ f(x')∈B ∧ F'(f(x))=F'(f(x'))) ⇒ f(x)=f(x')
    inst = instancie(instancie(hinj, fx), fxp)

    # happlique : (∀v)(v∈A ⇒ f(v)∈B)  — donnée « f : A→B » (honnête, explicite)
    happlique = N.assume(pourtout("v", impl(appartient(vv, vA),
                                  appartient(E.valeur(vF, vv), vB))))

    # antécédent interne (gardé) : (x∈A ∧ x'∈A) ∧ f'(f(x))=f'(f(x'))
    eq_hyp = egal(fpfx, fpfxp)                           # f'(f(x)) = f'(f(x'))
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), eq_hyp)
    h = N.assume(ante)
    x_inA = conjonction_elim_gauche(conjonction_elim_gauche(h))   # x ∈ A
    xp_inA = conjonction_elim_droite(conjonction_elim_gauche(h))  # x' ∈ A
    heq = conjonction_elim_droite(h)                              # f'(f(x))=f'(f(x'))

    # f(x)∈B, f(x')∈B  dérivés de happlique sous x∈A, x'∈A  (motif _cv_point)
    fx_inB = N.modus_ponens(x_inA, instancie(happlique, vx))      # f(x) ∈ B
    fxp_inB = N.modus_ponens(xp_inA, instancie(happlique, vxp))   # f(x') ∈ B

    # antécédent de l'instance d'injectivité de f' : (f(x)∈B ∧ f(x')∈B) ∧ F'(f(x))=F'(f(x'))
    ante_inj = conjonction_intro(conjonction_intro(fx_inB, fxp_inB), heq)
    fx_eq = N.modus_ponens(ante_inj, inst)                        # f(x) = f(x')

    # referme l'implication interne (gardée), généralise sur x' puis x
    inner = N.loi_deduction(ante, fx_eq)
    gen = N.generalisation("x", N.generalisation("xp", inner))
    return N.loi_deduction(E.injective_dans(vFp, vB), gen)


def cible_theoreme1_e_injective_valeur(f="F", fp="Fp", a="A", b="B"):
    """Cible exacte : injective_dans(F',B) ⇒
       (∀x,x')((x∈A ∧ x'∈A ∧ f'(f(x))=f'(f(x'))) ⇒ f(x)=f(x'))."""
    vF, vFp, vA, vB = _T(f), _T(fp), _T(a), _T(b)
    vx, vxp = var("x"), var("xp")
    fx, fxp = E.valeur(vF, vx), E.valeur(vF, vxp)
    fpfx, fpfxp = E.valeur(vFp, fx), E.valeur(vFp, fxp)
    ante = et(et(appartient(vx, vA), appartient(vxp, vA)), egal(fpfx, fpfxp))
    inner = impl(ante, egal(fx, fxp))
    return impl(E.injective_dans(vFp, vB),
                pourtout("x", pourtout("xp", inner)))


def hypotheses_theoreme1_e_injective_valeur(f="F", a="A", b="B"):
    """Hypothèse C46 HONNÊTE résiduelle EXACTE : {(∀v)(v∈A ⇒ f(v)∈B)} (tests).

    happlique « f applique A dans B » — donnée « f : A→B » du Théorème 1.  CLOSE
    en (x,x') : c'est la seule hyp non déchargée (injective_dans(F',B) est, elle,
    déchargée dans l'implication externe)."""
    vF, vA, vB = _T(f), _T(a), _T(b)
    vv = var("v")
    return {pourtout("v", impl(appartient(vv, vA),
                               appartient(E.valeur(vF, vv), vB)))}


__all__ = ["theoreme1_e_injective_valeur",
           "cible_theoreme1_e_injective_valeur",
           "hypotheses_theoreme1_e_injective_valeur"]
