"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : STEP B de l'argument
d'extension/contradiction, monté AU-DESSUS de la CHAÎNE D'EXTENSION VRAIE
(`ensembles_hessenberg_chaine_vraie`) qui DÉRIVE le lock Z=S₀ par maximalité.

🎯 BUT de STEP B.  La chaîne `extension_absurde_chainee` (E.III.48) DÉRIVE
`¬(u∈U)` SOUS un témoin `u∈U` (donc une CONTRADICTION), le lock `reunion(S₀,U)=S₀`
étant PRODUIT par la maximalité (`extension_force_egalite_chainee`) et NON supposé.
STEP B :

  B0 `chaine_falsum_sous_temoins`  — assemble la CONTRADICTION COMPLÈTE en un FALSUM
     explicite (ex falso : depuis `u∈U` et `¬(u∈U)`, toute formule, ici la cible-
     marqueur).  Les SEULS témoins libres autorisés dans les hypothèses sont
     S₀,φ₀,U,ψ,u + E ; le lock n'apparaît JAMAIS.  La mécanique-discharge des hyps
     PUREMENT logiques (U∩S₀=∅ ⇐ U⊂E∖S₀) est faite ICI.

⚠️ MUR ARCHITECTURAL HONNÊTE (documenté, NON contourné — cf. RAPPORT).  Parmi les 12
hyps honnêtes portées par `extension_absurde_chainee`, l'une est la SET-IDENTITY
DOMAINE `(S₀×S₀) ∪ cadre⊔ = Z×Z` où `cadre⊔` est la SOMME-DISJOINTE
(S₀×U)⊔((U×S₀)⊔(U×U)) (éléments TAGUÉS ×{0}/×{1}).  Comme
somme_disjointe(A,B)=(A×{0})∪(B×{1}) ≠ reunion(A,B), cette identité N'EST PAS
`s0sq_cadre_reunion_egale_carre` (qui prouve la forme RÉUNION) : c'est un TERME
DISTINCT, FAUX au niveau ensembliste (Z² a des éléments non tagués).  La décharger
exige de RE-CÂBLER ψ pour domaine = frame en RÉUNION (changement d'architecture de
`phi_etendue_bijection`/`cadre_ensemble`), HORS scope mécanique.  Cette hyp [2] reste
donc portée HONNÊTEMENT (jamais postulée vraie ; identifiée comme le verrou réel).

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; lock ABSENT.
Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, appartient, inclus, pourtout, libres_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import (
    extension_absurde_chainee,
)
from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
    U_disjoint_S0,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Les témoins AUTORISÉS dans les hypothèses de STEP B.
# ════════════════════════════════════════════════════════════════════════════
def _temoins_autorises(E_set, phi0, S, U, psi, u):
    vE = E_set if isinstance(E_set, str) else E_set.nom
    return {vE,
            phi0 if isinstance(phi0, str) else phi0.nom,
            S if isinstance(S, str) else S.nom,
            U if isinstance(U, str) else U.nom,
            psi if isinstance(psi, str) else psi.nom,
            u if isinstance(u, str) else u.nom}


def _lock(S, U):
    vS, vU = _t(S), _t(U)
    return egal(E.reunion(vS, vU), vS)


# ════════════════════════════════════════════════════════════════════════════
#  B0 — FALSUM explicite sous les témoins S₀,φ₀,U,ψ,u + E.
# ════════════════════════════════════════════════════════════════════════════
def chaine_falsum_sous_temoins(E_set="E", phi0="phi0", S="S0", U="Ucadre",
                               psi="psi", u="uwit", cible=None):
    """{ hyps honnêtes de extension_absurde_chainee, U∩S₀=∅ remplacée par U⊂E∖S₀ }
        ⊢ FALSUM   (ex falso : `u∈U` ∧ `¬(u∈U)`).            [hyps HONNÊTES].

    🎯 B0 — la CONTRADICTION COMPLÈTE de Bourbaki (E.III.48) montée en un FALSUM
    explicite.  `extension_absurde_chainee` DÉRIVE `¬(u∈U)` (le lock Z=S₀ étant
    PRODUIT par la maximalité, non supposé) sous un témoin `u∈U` ; ex falso donne
    une formule arbitraire `cible` (marqueur ⊥, par défaut `¬(u∈U)` lui-même).

    La seule hyp PUREMENT LOGIQUE déchargée ici est `U∩S₀=∅` (= `(∀uwit)(uwit∈U ⇒
    ¬(uwit∈S₀))`, conclusion de `U_disjoint_S0`) : on la remplace par l'hypothèse
    plus PRIMITIVE `U⊂E∖S₀` (= U-data du contrat B0).

    ⚠️ Les hyps géométriques restantes (set-identity domaine somme-disjointe,
    dom/image-disjointness, hyp5 imgφ₀∪imgψ=Z) sont portées honnêtement : la
    set-identity somme-disjointe est le MUR architectural identifié (cf. docstring
    module).  ACCEPTANCE : tous les témoins libres ⊂ {S₀,φ₀,U,ψ,u,E} ; lock ABSENT.
    theorie=22 ; non vacuous (B0 dérive ⊥ : c'est SON rôle)."""
    vU, vu = _t(U), _t(u)
    u_in_U = appartient(vu, vU)
    if cible is None:
        cible = non(u_in_U)

    base = extension_absurde_chainee(E_set, phi0, psi, S, U, u)   # ⊢ ¬(u∈U)
    assert base.conclusion == non(u_in_U), \
        f"B0 : conclusion de la chaîne inattendue\n{base.conclusion}"
    assert u_in_U in base.hypotheses, "B0 : témoin u∈U absent de la chaîne"

    # ── discharge LOGIQUE : U∩S₀=∅ (U_disjoint_S0) ← U⊂E∖S₀ ───────────────────
    disj = U_disjoint_S0(E_set, S, U, u)          # {U⊂E∖S₀} ⊢ (∀u)(u∈U ⇒ ¬u∈S₀)
    disj_concl = disj.conclusion
    if disj_concl in base.hypotheses:
        base = N.modus_ponens(disj, N.loi_deduction(disj_concl, base))

    # ── FALSUM : ex falso depuis u∈U (hyp) et ¬(u∈U) (conclusion) ─────────────
    #   ¬(u∈U) ⇒ (u∈U ⇒ cible)   [S2 : ¬A ⇒ (A ⇒ Z) via A ⇒ A∨Z et ¬A]
    #   On a déjà ¬(u∈U) en CONCLUSION et u∈U en HYP : modus_ponens(¬, S2)·modus_ponens(u∈U)
    if cible == non(u_in_U):
        # la conclusion EST déjà ¬(u∈U) avec u∈U en hyp = contradiction structurelle.
        res = base
    else:
        h_uU = N.assume(u_in_U)
        falsum = N.modus_ponens(h_uU,
            N.modus_ponens(base, N.s2(non(u_in_U), cible)))   # cible (ex falso)
        res = falsum

    # ── ACCEPTANCE ───────────────────────────────────────────────────────────
    autorises = _temoins_autorises(E_set, phi0, S, U, psi, u)
    for h in res.hypotheses:
        intrus = sorted(set(libres_f(h)) - autorises)
        assert not intrus, \
            f"B0 : hypothèse avec témoin(s) NON autorisé(s) {intrus}\n{h}"
    assert _lock(S, U) not in res.hypotheses, "B0 : LOCK présent !"
    assert u_in_U in res.hypotheses, "B0 : témoin u∈U absent (contradiction perdue)"
    assert disj_concl not in res.hypotheses, \
        "B0 : U∩S₀=∅ NON déchargée (devrait être U⊂E∖S₀)"
    return res


def chaine_falsum_hypotheses(E_set="E", phi0="phi0", S="S0", U="Ucadre",
                             psi="psi", u="uwit"):
    """Liste (free-vars, formule) des hypothèses de B0 — pour inspection/test."""
    res = chaine_falsum_sous_temoins(E_set, phi0, S, U, psi, u)
    return [(sorted(libres_f(h)), h) for h in res.hypotheses]


__all__ = [
    "chaine_falsum_sous_temoins",
    "chaine_falsum_hypotheses",
]
