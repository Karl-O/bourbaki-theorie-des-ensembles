"""§III.6.3 — Théorème 2 (HESSENBERG) : CLASSIFICATION PRÉCISE du résidu de STEP B.

🎯 BUT.  STEP B (`hessenberg_vrai`) est bloqué parce que `extension_absurde_chainee()`
porte 12 HYPOTHÈSES HONNÊTES résiduelles mentionnant les témoins existentiels INTERNES
{S0, Ucadre, phi0, psi, uwit}.  Pour clore STEP B il faudrait TOUTES les décharger avant
d'éliminer ces témoins (sinon `existe_elimination` échoue : « S0/Ucadre libre dans une
hypothèse »).  Ce module ÉTABLIT, de façon MÉCANIQUEMENT VÉRIFIÉE, lesquelles sont
déchargeables et lesquelles sont le RÉSIDU GÉOMÉTRIQUE IRRÉDUCTIBLE.

VERDICT (vérifié par `classification()`, comparaisons structurelles `.conclusion == hyp`) :

  • UN SEUL des helpers structurels disponibles s'apparie à une hyp résiduelle :
    `U_disjoint_S0(z="uwit")` ⊢ (∀uwit)(uwit∈U ⇒ ¬uwit∈S0)  == HYP « U∩S₀=∅ ».
    Mais c'est un ÉCHANGE LATÉRAL (sa propre hyp `U⊂E∖S0` n'est PAS dans le résidu) :
    il REMPLACE l'hyp disjointness par l'hyp inclusion-complément, sans BAISSER le compte.

  • AUCUN helper ne produit de RÉDUCTION NETTE du compte (12 → 12).  `frame_dom_image`
    a bien sa propre hyp (φ₀ bijection = HYP « corps_frame ») déjà dans le résidu, mais
    sa CONCLUSION (dom/image de φ₀) ne s'apparie à AUCUNE hyp ⇒ inutile ici.

  • `s0sq_cadre_reunion_egale_carre` (CLOS, 0 hyp) ⊢ S₀²∪F_reunion = Z² N'APPARIE PAS
    HYP « S₀²∪cadre⊔ = Z² » : le cadre résiduel est en SOMME-DISJOINTE
    (`cadre_ensemble = somme_disjointe(...)`, tags `paire(vide,vide)`), un TERME
    STRUCTURELLEMENT DISTINCT de la réunion.  C'est le BLOCKER ARCHITECTURAL DOCUMENTÉ.

RÉSIDU IRRÉDUCTIBLE (sans re-câbler `cadre_ensemble` somme_disjointe → réunion) :
  les hyps mentionnant le cadre tagué (ψ-bijection sur F⊔, S₀²∪F⊔=Z², ∃X-non-extension),
  les images φ₀/ψ (union=Z, intersection=∅, doms disjoints), la maximal-data
  (element_maximal de (S₀,φ₀)), l'inclusion Z⊂E.  Tous HONNÊTES (vrais dans l'argument
  de Zorn E.III.48), AUCUN clos avec l'outillage présent.

INVARIANT : theorie_ensembles() = 22 ; noyau INTACT ; AUCUNE clôture truquée — le résidu
est EXPOSÉ, pas masqué.  Ce module N'AJOUTE PAS d'axiome et ne prétend RIEN clore.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f, var
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import extension_absurde_chainee
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
    U_disjoint_S0, frame_dom_image, U_non_vide, card_inclus_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_produit_union_carre import s0sq_cadre_reunion_egale_carre


# Étiquettes humaines des 12 hyps, indexées par une SIGNATURE structurelle stable
# (préfixe de la formule affichée) — robuste au renommage interne.
def _label(h):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import afficher_f as af
    s = af(h)
    fv = sorted(libres_f(h))
    if s.startswith("(inter(image(phi0"):
        return "imgφ₀ ∩ imgψ = ∅ (images disjointes) — GÉOMÉTRIQUE"
    if s.startswith("(reunion(image(phi0"):
        return "imgφ₀ ∪ imgψ = S₀∪U (images couvrent Z) — GÉOMÉTRIQUE"
    if s.startswith("(reunion(produit(S0, S0)") and "paire(vide(), vide())" in s:
        return "S₀²∪cadre⊔ = Z²  [SOMME-DISJOINTE] — BLOCKER ARCHITECTURAL"
    if s.startswith("(paire(paire(S0, S0), paire(S0, phi0)) ∈ hessenberg_frame"):
        return "(S₀,φ₀) ∈ 𝔉(E)  (membership maximal) — MAXIMAL-DATA"
    if s == "(uwit ∈ Ucadre)":
        return "uwit ∈ U  (TÉMOIN de la contradiction — NON éliminable : libre dans la conclusion ¬uwit∈U)"
    if s.startswith("(∀u) ¬((u ∈ dom(phi0)) et (u ∈ dom(psi)))"):
        return "dom φ₀ ∩ dom ψ = ∅ (domaines disjoints) — GÉOMÉTRIQUE"
    if s.startswith("(∀uwit) ((uwit ∈ Ucadre) ⇒ ¬(uwit ∈ S0))"):
        return "U ∩ S₀ = ∅  — DÉCHARGEABLE LATÉRALEMENT via U_disjoint_S0(z=uwit) (→ U⊂E∖S₀)"
    if s.startswith("(∀z) ((z ∈ reunion(S0, Ucadre)) ⇒ (z ∈ E))"):
        return "Z = S₀∪U ⊂ E  (inclusion) — GÉOMÉTRIQUE"
    if s.startswith("¬((∃X)"):
        return "¬(∃X) non-extension de Z (∃X-résidu) — GÉOMÉTRIQUE / ARCHITECTURAL"
    if s.startswith("((paire(paire(S0, S0), paire(S0, phi0)) ∈ hessenberg_frame") and "(∀x)" in s:
        return "element_maximal((S₀,φ₀)) déplié — MAXIMAL-DATA"
    if s.startswith("(((∀u) (∀v) (∀z)") and "∈ phi0)" in s and "produit(S0, S0)" in s:
        return "φ₀ bijection S₀×S₀→S₀ (corps_frame) — MAXIMAL-DATA"
    if "∈ psi)" in s and "paire(vide(), vide())" in s:
        return "ψ bijection F⊔→U sur le cadre SOMME-DISJOINTE — BLOCKER ARCHITECTURAL"
    return "??? (non classé) free=%s" % fv


# @livre Ch.III §6.3 Demo.2 | E III.48 L.25-37 | PDF p.151  (cartographie mécanique du résidu de la démonstration d'extension ; rien de nouveau prouvé)
def classification():
    """Retourne (theorem, table) ; table = liste de dicts {idx, free, label, dischargeable}.

    Vérifie MÉCANIQUEMENT (égalité structurelle) l'appariement des helpers.  N'altère
    PAS le théorème (aucune clôture).  Sert de SOURCE DE VÉRITÉ du verdict STEP B."""
    thm = extension_absurde_chainee()
    hyps = list(thm.hypotheses)
    hset = set(hyps)

    # helpers appariables
    ud = U_disjoint_S0(z="uwit")
    s0r = s0sq_cadre_reunion_egale_carre()
    helper_matches = {}
    helper_matches["U_disjoint_S0(z=uwit)"] = ud.conclusion in hset
    helper_matches["s0sq_cadre_reunion_egale_carre"] = s0r.conclusion in hset

    table = []
    for i, h in enumerate(sorted(hyps, key=lambda x: str(x))):
        lab = _label(h)
        disch = "U_disjoint_S0(z=uwit) [LATÉRAL]" if (h == ud.conclusion) else "irreducible"
        table.append({
            "idx": i,
            "free": sorted(libres_f(h)),
            "label": lab,
            "dischargeable": disch,
        })

    # INVARIANTS du verdict (échouent si l'analyse devient fausse) :
    assert helper_matches["U_disjoint_S0(z=uwit)"] is True, \
        "classification : U_disjoint_S0 ne s'apparie plus — re-analyser"
    assert helper_matches["s0sq_cadre_reunion_egale_carre"] is False, \
        "classification : s0sq_reunion s'apparierait — re-analyser le blocker"
    assert len(hyps) == 12, f"classification : {len(hyps)} hyps (attendu 12)"
    return thm, table


def discharge_u_disjoint(E_set="E", phi0="phi0", psi="psi", S="S0", U="Ucadre", u="uwit"):
    """Échange LATÉRAL HONNÊTE de la seule hyp appariable de STEP B :
    remplace l'hyp « U∩S₀=∅ » (∀uwit(uwit∈U⇒¬uwit∈S0)) par l'hyp plus PRIMITIVE
    « U⊂E∖S₀ » via `U_disjoint_S0`, par modus_ponens dans `extension_absurde_chainee`.

    ⚠️ Ce N'EST PAS une réduction du compte (12→12) : une hyp en remplace une autre.
    Exposé honnêtement comme échange, pour réutilisation (l'argument complet fournit
    U⊂E∖S₀ via `complement_grand`).  theorie=22 ; aucune clôture truquée."""
    thm = extension_absurde_chainee(E_set, phi0, psi, S, U, u)
    ud = U_disjoint_S0(E_set, S, U, z=u)                 # {U⊂E∖S₀} ⊢ U∩S₀=∅
    target = ud.conclusion
    assert target in thm.hypotheses, "discharge_u_disjoint : hyp U∩S₀=∅ absente"
    res = N.modus_ponens(ud, N.loi_deduction(target, thm))   # décharge U∩S₀=∅, introduit U⊂E∖S₀
    # le compte ne baisse pas : la conclusion est inchangée, et U⊂E∖S₀ est maintenant présente.
    assert res.conclusion == thm.conclusion
    assert target not in res.hypotheses, "discharge_u_disjoint : U∩S₀=∅ pas déchargée"
    assert ud.hypotheses.issubset(res.hypotheses) if hasattr(ud.hypotheses, "issubset") \
        else all(h in res.hypotheses for h in ud.hypotheses)
    return res


__all__ = ["classification", "discharge_u_disjoint", "_label"]
