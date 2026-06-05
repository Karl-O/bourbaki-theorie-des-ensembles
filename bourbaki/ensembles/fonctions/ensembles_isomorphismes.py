"""§IV.1.5 — Structures et isomorphismes : fragment OBJET.

Le chapitre IV est ABSTRAIT : un isomorphisme y est défini (Déf. IV.1.5) par
l'égalité ⟨f₁,…,fₙ,Id,…⟩^S(U) = U' où ⟨…⟩^S est l'EXTENSION CANONIQUE de schéma
S — une RÉCURSION MÉTA sur un schéma d'échelon S (suite de couples d'entiers).
Cette extension, les échelons S(E₁,…,Eₙ), les typifications, la transportabilité
et les espèces de structure relèvent du MÉTALANGAGE DES ESPÈCES (schémas sur n
ensembles de base) ; ils ne sont PAS exprimables par une seule formule du fragment
objet et sont REPORTÉS honnêtement (voir le rapport / le module couverture).

Ce qui EST exprimable au niveau objet, et que l'on encode + prouve ici, c'est le
cas concret — celui des exemples de Bourbaki (IV.1) et de l'isomorphisme
d'ensembles ORDONNÉS (E.III.1.3) — d'une STRUCTURE RELATIONNELLE : la structure
sur E est une relation R{x,y} (le plus simple échelon non trivial, S(E)=𝔓(E×E)).
Conformément à la définition générale « isomorphisme = bijection compatible avec
la structure » :

  • est_isomorphisme(F, E, E', R, R')  :=  F est le graphe d'une bijection de E
    sur E', ET pour tous x,y ∈ E :  R{x,y} ⇔ R'{f(x), f(y)}   (compatibilité,
    c'est exactement (4) de IV.1.5 spécialisée à un échelon relationnel ; pour un
    ordre c'est la Déf. III.1.3 : « x ≤ y et f(x) ≤ f(y) sont équivalentes »).

  • structure_transportee(F, R)  :  R'{u,v} := R{f⁻¹(u), f⁻¹(v)} — la structure
    transportée par la bijection F (Déf. IV.1.5, transport de structure ; ici au
    niveau objet pour l'échelon relationnel).  La structure transportée est
    DÉFINIE de sorte que F soit un isomorphisme (cf. CST5, cas objet).

  • sont_isomorphes(E, E', R, R')  :=  (∃F) est_isomorphisme(F, E, E', R, R').
    « (E,R) et (E',R') sont isomorphes » (relation entre structures, IV.1.5).

THÉORÈMES DIRECTS certifiés par le noyau :
  • identite_est_isomorphisme(E, R) :  l'identité Δ_E est un isomorphisme de (E,R)
    sur (E,R).  (IV.1.5 : un automorphisme ; cas objet du « Id est un
    isomorphisme ».)  Réutilise diagonale_* / diagonale_valeur (Δ_E bijection de E
    sur E, et Δ_E(x)=x pour x∈E ⇒ la compatibilité est R{x,y}⇔R{x,y}).
  • isomorphes_reflexive(E, R) :  (E,R) est isomorphe à lui-même.  RÉFLEXIVITÉ de
    la relation « isomorphe », par ∃-introduction (témoin Δ_E) sur le théorème
    précédent — analogue structurel de equipotence_reflexive.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, existe, pourtout, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_transitivite,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as eg_symetrie
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.ensembles_equipotence import (diagonale_fonctionnelle, diagonale_domaine,
                                    diagonale_injective, diagonale_image,
                                    diagonale_valeur)


# ── Compatibilité d'une bijection avec deux relations ─────────────────────────
def compatible(f, e, r, rp, x="a", y="b"):
    """« f compatible avec R, R' sur E » := (∀x)(∀y)((x∈E et y∈E) ⇒
        (R{x,y} ⇔ R'{f(x), f(y)})).   (clause (4) de IV.1.5, cas relationnel ;
    Déf. III.1.3 pour un ordre : x≤y et f(x)≤f(y) équivalentes.)"""
    vx, vy = var(x), var(y)
    fx, fy = E.valeur(f, vx), E.valeur(f, vy)
    from bourbaki.logique.formule import impl, equiv
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, e), appartient(vy, e)),
             equiv(r(vx, vy), rp(fx, fy)))))


def est_isomorphisme(f, e, ep, r, rp):
    """« (f) est un isomorphisme de (E,R) sur (E',R') » := F est le graphe d'une
    bijection de E sur E', ET f est compatible avec R, R'   (IV.1.5, cas objet
    relationnel ; généralise l'isomorphisme d'ensembles ordonnés E.III.1.3)."""
    return et(est_bijection_de(f, e, ep), compatible(f, e, r, rp))


def structure_transportee(f, r, u="u", v="v"):
    """R'{u,v} := R{f⁻¹(u), f⁻¹(v)} — structure relationnelle TRANSPORTÉE par la
    bijection de graphe F (IV.1.5, transport de structure ; cas objet).

    Renvoie une « relation R'{u,v} » (fonction (Terme,Terme)→Formule), prête à
    être passée à est_isomorphisme / sont_isomorphes."""
    finv = E.reciproque(f)
    return lambda tu, tv: r(E.valeur(finv, tu), E.valeur(finv, tv))


def sont_isomorphes(e, ep, r, rp, f="F"):
    """« (E,R) et (E',R') sont isomorphes » := (∃F) est_isomorphisme(F,E,E',R,R')
    (IV.1.5).  Relation entre structures — réflexive (cf. isomorphes_reflexive)."""
    return existe(f, est_isomorphisme(var(f), e, ep, r, rp))


# ── A ⇔ A (réflexivité de l'équivalence), réutilisée plus bas ──────────────────
def _equiv_reflexive(p):
    """⊢ P ⇔ P."""
    return conjonction_intro(a_implique_a(p), a_implique_a(p))


# ── Théorème : l'identité Δ_E est un isomorphisme de (E,R) sur (E,R) ───────────
def identite_est_isomorphisme(e="E", r=None, x="a", y="b"):
    """⊢ est_isomorphisme(Δ_E, E, E, R, R).   (IV.1.5 : Δ_E est un automorphisme ;
    cas objet du « l'application identique est un isomorphisme ».)

    Δ_E est une bijection de E sur E (diagonale_fonctionnelle / _domaine /
    _injective / _image = est_bijection_de(Δ_E,E,E), cf. equipotence_reflexive).
    Compatibilité : pour x,y∈E on a Δ_E(x)=x et Δ_E(y)=y (diagonale_valeur), donc
    R{Δ_E(x),Δ_E(y)} se réécrit (Leibniz, S6) en R{x,y} ; la clause devient
    R{x,y} ⇔ R{x,y}, vraie.  R par défaut = appartenance au couple dans un graphe
    générique G (relation relationnelle arbitraire ; le lecteur passe la sienne)."""
    if r is None:
        # relation relationnelle générique R{x,y} := (x,y) ∈ G  (graphe G arbitraire)
        vG = var("G")
        r = lambda a, b: appartient(E.couple(a, b), vG)
    vE, vx, vy = var(e), var(x), var(y)
    DE = E.diagonale(vE)

    # — partie « bijection » : est_bijection_de(Δ_E, E, E) —
    bij = conjonction_intro(
        conjonction_intro(diagonale_fonctionnelle(e), diagonale_domaine(e)),
        conjonction_intro(diagonale_injective(e), diagonale_image(e)))

    # — partie « compatibilité » : (x∈E et y∈E) ⇒ (R{x,y} ⇔ R{Δx, Δy}) —
    dx, dy = E.valeur(DE, vx), E.valeur(DE, vy)
    hyp = et(appartient(vx, vE), appartient(vy, vE))
    h = N.assume(hyp)
    x_inE = conjonction_elim_gauche(h)                       # x∈E
    y_inE = conjonction_elim_droite(h)                       # y∈E
    # Δx = x  et  Δy = y   (diagonale_valeur, déchargées de l'hyp d'appartenance)
    dvx = N.modus_ponens(x_inE,
        N.loi_deduction(appartient(vx, vE), diagonale_valeur(e, x)))     # Δx=x
    dvy = N.modus_ponens(y_inE,
        N.loi_deduction(appartient(vy, vE), diagonale_valeur(e, y)))     # Δy=y
    x_eq_dx = N.modus_ponens(dvx, eg_symetrie(dx, vx))      # x=Δx
    y_eq_dy = N.modus_ponens(dvy, eg_symetrie(dy, vy))      # y=Δy
    # Leibniz 1 : (x=Δx) ⇒ (R{x,y} ⇔ R{Δx, y})   [trou w en 1ʳᵉ place de R]
    w = var("w")
    leib1 = N.modus_ponens(x_eq_dx, N.s6(vx, dx, "w", r(w, vy)))   # R{x,y}⇔R{Δx,y}
    # Leibniz 2 : (y=Δy) ⇒ (R{Δx,y} ⇔ R{Δx, Δy})  [trou w en 2ᵉ place de R]
    leib2 = N.modus_ponens(y_eq_dy, N.s6(vy, dy, "w", r(dx, w)))   # R{Δx,y}⇔R{Δx,Δy}
    compat_eq = equivalence_transitivite(leib1, leib2)      # R{x,y} ⇔ R{Δx,Δy}
    compat_inner = N.loi_deduction(hyp, compat_eq)          # (x∈E et y∈E)⇒(R{x,y}⇔R{Δx,Δy})
    compat = N.generalisation(x, N.generalisation(y, compat_inner))

    return conjonction_intro(bij, compat)


# ── Théorème : réflexivité de « isomorphe » ───────────────────────────────────
def isomorphes_reflexive(e="E", r=None):
    """⊢ sont_isomorphes(E, E, R, R).   (RÉFLEXIVITÉ de la relation « isomorphe »,
    IV.1.5 — toute structure est isomorphe à elle-même via l'identité Δ_E.)

    ∃-introduction (S5, témoin Δ_E) sur identite_est_isomorphisme."""
    if r is None:
        vG = var("G")
        r = lambda a, b: appartient(E.couple(a, b), vG)
    vE = var(e)
    DE = E.diagonale(vE)
    iso_id = identite_est_isomorphisme(e, r)               # est_isomorphisme(Δ_E,E,E,R,R)
    corps = est_isomorphisme(var("F"), vE, vE, r, r)
    return N.modus_ponens(iso_id, N.s5(corps, DE, "F"))    # (∃F)… = sont_isomorphes(E,E,R,R)


__all__ = ["compatible", "est_isomorphisme", "structure_transportee",
           "sont_isomorphes", "identite_est_isomorphisme", "isomorphes_reflexive"]
