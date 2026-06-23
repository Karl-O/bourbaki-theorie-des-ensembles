"""§IV.1.5 / IV.1.2 — TRANSPORT DE STRUCTURE & ISOMORPHISMES (niveau ESPÈCE Σ).
Propositions/critères « logiquement directs » NON encore traités.   REPRÉSENTATIONNEL.

Module NEUF (campagne « complétude chap. IV », vague II-E).  Il COMPLÈTE les modules
déjà faits — `ensembles_especes` (transport, est_isomorphisme, structure_transportee,
sont_isomorphes, est_automorphisme, transport_donne_isomorphisme),
`ensembles_structures_props` (CST4 composition d'isos, identité iso, CST8),
`ensembles_CST_criteres` (CST5 unicité du transport au niveau du terme opaque
extension_echelon, CST9/CST18), `ensembles_chap4_props_restantes` (CST3 réciproque de
la bijection transportée ; réciproque d'un iso au niveau du PRÉDICAT abstrait `morph`).

⚠️ NIVEAU DISTINCT, PAS DE DOUBLON.  Tous les théorèmes de ce module travaillent au
niveau de la notion `ensembles_especes.est_isomorphisme(Σ, f, E, E', U, U')` — VERBATIM
IV.1.5, relation (4) : « (f) est un isomorphisme = (f bijection) ET ⟨f,Id⟩^S(U)=U' » —
c.-à-d. avec la STRUCTURE TRANSPORTÉE EXPLICITE `structure_transportee` (extension
canonique d'échelon ⟨f⟩^S réellement construite, IV.1.2) et la BIJECTION
`est_bijection_de` (E.III.3.1).  C'est un autre objet que :
  • le `morph(e1,s1,e2,s2,f)` ABSTRAIT (prédicat opaque) de
    `chap4_props_restantes.reciproque_iso_est_iso` / `CST_criteres` — où « iso » = (morph f
    ∧ morph f⁻¹) ; ici « iso » = (BIJECTION ∧ ÉGALITÉ de transport) ;
  • le terme OPAQUE `extension_echelon(S,f,U)` de `CST_criteres.cst5_unicite_transport`
    (chaîne d'égalités nues) — ici on EXTRAIT les égalités des isomorphismes eux-mêmes.

CE QUI EST PROUVÉ ICI (NOUVEAU, fidèle IV.1.5/IV.1.2 ; vérifié « membres distincts /
conclusion ∉ hypothèses ») :

  1. RÉCIPROQUE D'UN ISOMORPHISME D'ESPÈCE EST UN ISOMORPHISME (IV.1.5) —
     `reciproque_isomorphisme_espece` : de est_isomorphisme(Σ,(f),E,E',U,U') on conclut
     est_isomorphisme(Σ,(f⁻¹),E',E,U',U).  Clause (4) ⟨f⁻¹⟩^S(U')=U DÉRIVÉE de ⟨f⟩^S(U)=U'
     (extraite de l'iso) + CST3 (⟨f⁻¹⟩^S(⟨f⟩^S(U))=U, hyp. explicite) par réécriture S6 ;
     partie « bijection de f⁻¹ » en hypothèse explicite (fait ensembliste E.II.6.3, conditionnel).

  2. « SONT ISOMORPHES » EST RÉFLEXIVE (IV.1.5) — `sont_isomorphes_reflexive_espece` :
     (E,U) est isomorphe à (E,U) (l'identité (Δ_E) est un témoin).  Introduction
     existentielle (S5) sur l'isomorphisme identité ; bijection de Δ_E INCONDITIONNELLE
     (les quatre paliers diagonale_*), clause (4) ⟨Δ_E⟩^S(U)=U en hyp. explicite (CST1-id).

  3. L'IDENTITÉ EST UN AUTOMORPHISME (IV.1.5) — `automorphisme_identite_espece` :
     est_automorphisme(Σ,(Δ_E),E,U) (cas E=E', U=U' de l'isomorphisme identité).  Distinct
     de `structures_props.identite_est_isomorphisme_espece` : conclut la notion NOMMÉE
     `est_automorphisme` (IV.1.5, « automorphisme de E »), pas est_isomorphisme.

  4. UNICITÉ DE LA STRUCTURE TRANSPORTÉE (IV.1.5, « il existe … et UNE SEULE … ») —
     `transporte_unique_espece` : si (f) est un isomorphisme de (E,U) sur (E',V) ET sur
     (E',V'), alors V=V'.  Les deux clauses (4) ⟨f⟩^S(U)=V et ⟨f⟩^S(U)=V' (extraites des
     isos) donnent V=V' par transitivité de =.  C'est l'UNICITÉ de CST5 au niveau de
     est_isomorphisme (l'EXISTENCE — que ⟨f⟩^S(U) vérifie R — reste REPORTÉE).

  5. UN SCHÉMA D'ÉCHELON APPLIQUÉ À DES IDENTITÉS DONNE UNE BIJECTION (IV.1.2, CST2 à
     l'identité) — `echelon_identite_bijection` : ⟨Δ_E⟩^S est une bijection de S(E) sur
     S(E).  DÉRIVÉE de la bijection de Δ_{S(E)} (hyp. explicite, S(E) étant un terme
     composé) + CST1-identité ⟨Δ_E⟩^S = Δ_{S(E)} (hyp. explicite) par réécriture S6.
     NON VACUEUX : pour un schéma non trivial (p.ex. S(E)=𝔓(E)), ⟨Δ_E⟩^S = ext_parties(Δ_E)
     DIFFÈRE LITTÉRALEMENT de Δ_{S(E)} ; on certifie la bijectivité du TERME ⟨Δ_E⟩^S.

  6. UN ISOMORPHISME DONNE L'ÉGALITÉ DE TRANSPORT (IV.1.5, relation (4)) —
     `isomorphisme_donne_transport_eq` : de est_isomorphisme(Σ,(f),E,E',U,U') on extrait
     ⟨f⟩^S(U)=U' (clause (4)).  Projection droite de la conjonction définissant l'iso ;
     conclusion (une ÉGALITÉ) ≠ hypothèse (la CONJONCTION bijection∧égalité) — non vacueux.

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé.  Tout est soit LOGIQUE PUR
(réflexivité, conjonction, modus ponens, S5/S6/Leibniz, projection ∧), soit CONDITIONNEL
à des hypothèses EXPLICITES = les axiomes-schémas CST1/CST2/CST3 de Bourbaki (IV.1.2,
fonctorialité/bijectivité de l'extension d'échelon ⟨·⟩^S — preuve par récurrence sur le
schéma, REPORTÉE) et des faits ensemblistes (bijection de f⁻¹, E.II) INSTANCIÉS, fournis
comme PRÉMISSES des théorèmes — JAMAIS postulés vrais dans la théorie.

REPORTÉ honnêtement (méta / lourd, hors fragment) : la PREUVE de CST1/CST2/CST3
(récurrence sur le schéma S), la TRANSPORTABILITÉ de R (donc l'EXISTENCE — la validité
R{…} — de la structure transportée), l'EXISTENCE effective des structures.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, subst_f
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.ensembles_equipotence import (
    diagonale_fonctionnelle, diagonale_domaine, diagonale_injective,
    diagonale_image)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes import (
    Espece, structure_transportee, est_isomorphisme, sont_isomorphes,
    est_automorphisme)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    echelon, extension_canonique)


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes
# ════════════════════════════════════════════════════════════════════════════
def _t(x):
    """Coercion nom→Terme (accepte un Terme ou un nom de variable)."""
    return x if not isinstance(x, str) else var(x)


def _diagonale_bijection_nom(nom):
    """⊢ est_bijection_de(Δ_E, E, E)  — CLOS, INCONDITIONNEL (E=var(nom)).

    Assemble les quatre paliers certifiés diagonale_fonctionnelle/_domaine/_injective/
    _image dans la structure ((func,dom),(inj,img)) de est_bijection_de.  Identique au
    helper `_diagonale_bijection` de `ensembles_structures_props` (réutilisé tel quel)."""
    return conjonction_intro(
        conjonction_intro(diagonale_fonctionnelle(nom), diagonale_domaine(nom)),
        conjonction_intro(diagonale_injective(nom), diagonale_image(nom)))


# ════════════════════════════════════════════════════════════════════════════
#  1.  RÉCIPROQUE D'UN ISOMORPHISME D'ESPÈCE EST UN ISOMORPHISME  (IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def reciproque_isomorphisme_espece(sigma: Espece, e="E", ep="Ep", u="U", up="Up",
                                   f="f"):
    """{ est_isomorphisme(Σ, (f), E, E', U, U'),
         est_bijection_de(f⁻¹, E', E),                  (f⁻¹ bijection — E.II, conditionnel),
         ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U                          (CST3 appliqué à U, hyp. explicite) }
        ⊢  est_isomorphisme(Σ, (f⁻¹), E', E, U', U).

    « LA RÉCIPROQUE D'UN ISOMORPHISME EST UN ISOMORPHISME » (IV.1.5 — IV.1.5 pose le
    transport au moyen de bijections f_i et IV.1.2/CST3 fournit la réciproque ⟨f⁻¹⟩^S de
    ⟨f⟩^S).  est_isomorphisme(Σ,(f⁻¹),E',E,U',U) = (1) « f⁻¹ bijection de E' sur E » ∧
    (2) la clause (4) « ⟨f⁻¹⟩^S(U') = U ».

    PREUVE :
      (1) bijection de f⁻¹ : hypothèse EXPLICITE (réciproque d'une bijection est une
          bijection, E.II.6.3 — fournie en prémisse, non postulée en théorie) ;
      (2) clause (4) : de l'iso donné on EXTRAIT la clause (4) de f : ⟨f⟩^S(U) = U'
          (projection droite).  Par CST3 (hyp. explicite) ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U ; on
          réécrit ⟨f⟩^S(U) ↦ U' (S6, via ⟨f⟩^S(U)=U') DANS le membre gauche, obtenant
          ⟨f⁻¹⟩^S(U') = U.
    Recollement par conjonction.  Hypothèses EXPLICITES (l'iso donné + bij(f⁻¹) + CST3),
    AUCUN axiome de théorie ajouté ; purement logique (projection ∧, S6/Leibniz)."""
    ve, vep, vu, vup, vf = map(_t, (e, ep, u, up, f))
    finv = E.reciproque(vf)                                  # f⁻¹

    # — iso donné, extraction de la clause (4) de f —
    iso = est_isomorphisme(sigma, [vf], [ve], [vep], vu, vup)
    h_iso = N.assume(iso)
    eq4_f = conjonction_elim_droite(h_iso)                  # ⟨f⟩^S(U) = U'

    tr_f_U = structure_transportee(sigma, [vf], vu)         # ⟨f⟩^S(U)
    tr_finv_Up = structure_transportee(sigma, [finv], vup)  # ⟨f⁻¹⟩^S(U')   (cible.lhs)
    tr_finv_of_tr_f = structure_transportee(sigma, [finv], tr_f_U)  # ⟨f⁻¹⟩^S(⟨f⟩^S(U))

    # — CST3 : ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U  (hyp. explicite) —
    cst3 = egal(tr_finv_of_tr_f, vu)
    h_cst3 = N.assume(cst3)
    # réécrit ⟨f⟩^S(U) ↦ U' dans ⟨f⁻¹⟩^S(·)=U via eq4_f.
    #   S6(tr_f_U, U', w, ⟨f⁻¹⟩^S(w)=U) :
    #   (⟨f⟩^S(U)=U') ⇒ ( ⟨f⁻¹⟩^S(⟨f⟩^S(U))=U  ⇔  ⟨f⁻¹⟩^S(U')=U )
    w = "w_recip_iso"
    motif = egal(structure_transportee(sigma, [finv], var(w)), vu)
    s6 = N.s6(tr_f_U, vup, w, motif)
    eqv = N.modus_ponens(eq4_f, s6)
    eq4_finv = N.modus_ponens(h_cst3, equivalence_avant(eqv))   # ⟨f⁻¹⟩^S(U') = U

    # — bijection de f⁻¹ : hyp. explicite —
    bij_finv = est_bijection_de(finv, vep, ve)
    h_bij_finv = N.assume(bij_finv)

    res = conjonction_intro(h_bij_finv, eq4_finv)
    cible = est_isomorphisme(sigma, [finv], [vep], [ve], vup, vu)
    assert res.conclusion == cible, "conclusion ≠ est_isomorphisme(Σ,(f⁻¹),E',E,U',U)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  2.  « SONT ISOMORPHES » EST RÉFLEXIVE  (IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def sont_isomorphes_reflexive_espece(sigma: Espece, e="E", u="U"):
    """{ ⟨Δ_E⟩^S(U) = U   (CST1 à l'identité, hyp. explicite) }
        ⊢  sont_isomorphes(Σ, [E], [E], U, U).

    « (E,U) EST ISOMORPHE À (E,U) » — RÉFLEXIVITÉ de la relation « sont isomorphes »
    (IV.1.5 : l'identité est un isomorphisme, donc tout ensemble structuré est isomorphe
    à lui-même).  sont_isomorphes(Σ,[E],[E],U,U) = (∃f₁) est_isomorphisme(Σ,(f₁),E,E,U,U).

    PREUVE : on exhibe le TÉMOIN f₁ := Δ_E.  L'isomorphisme identité
    est_isomorphisme(Σ,(Δ_E),E,E,U,U) = « Δ_E bijection de E sur E » (INCONDITIONNEL, les
    quatre paliers diagonale_*) ∧ « ⟨Δ_E⟩^S(U) = U » (clause (4) = CST1 à l'identité, hyp.
    explicite).  Par INTRODUCTION EXISTENTIELLE (S5 : (Δ_E|f₁)R ⇒ (∃f₁)R), on conclut
    sont_isomorphes.  UNIQUE hypothèse = la clause (4) à l'identité ; la bijection de Δ_E
    est inconditionnelle (théorème clos absorbé).  Purement logique (S5 + conjonction)."""
    ve, vu = _t(e), _t(u)
    DE = E.diagonale(ve)
    nom = ve.nom

    # isomorphisme identité (témoin) :
    bij_thm = _diagonale_bijection_nom(nom)                 # ⊢ bij(Δ_E,E,E)  (clos)
    eq4_id = egal(structure_transportee(sigma, [DE], vu), vu)   # ⟨Δ_E⟩^S(U) = U
    h_eq4 = N.assume(eq4_id)
    iso_id = conjonction_intro(bij_thm, h_eq4)             # est_isomorphisme(Σ,(Δ_E),E,E,U,U)

    # existentielle : sont_isomorphes = (∃f₁) est_isomorphisme(Σ,(f₁),E,E,U,U)
    cible = sont_isomorphes(sigma, [ve], [ve], vu, vu)
    body = cible.sous[0]                                    # matrice sous (∃f₁)
    # contrôle : la matrice instanciée en Δ_E EST l'iso identité
    assert subst_f(DE, cible.lieur, body) == iso_id.conclusion, \
        "le témoin Δ_E n'instancie pas la matrice de sont_isomorphes"
    s5 = N.s5(body, DE, cible.lieur)                        # (Δ_E|f₁)R ⇒ (∃f₁)R
    res = N.modus_ponens(iso_id, s5)
    assert res.conclusion == cible, "conclusion ≠ sont_isomorphes(Σ,[E],[E],U,U)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  3.  L'IDENTITÉ EST UN AUTOMORPHISME  (IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def automorphisme_identite_espece(sigma: Espece, e="E", u="U"):
    """{ ⟨Δ_E⟩^S(U) = U   (CST1 à l'identité, hyp. explicite) }
        ⊢  est_automorphisme(Σ, (Δ_E), [E], U).

    « L'APPLICATION IDENTIQUE Δ_E EST UN AUTOMORPHISME de E (muni de U) » (IV.1.5 :
    « un isomorphisme de E₁,…,Eₙ sur E₁,…,Eₙ pour la même structure est un automorphisme »).
    est_automorphisme(Σ,(Δ_E),[E],U) est, PAR DÉFINITION (IV.1.5), le cas E=E', U=U' de
    est_isomorphisme : « Δ_E bijection de E sur E » (INCONDITIONNEL, les quatre paliers
    diagonale_*) ∧ « ⟨Δ_E⟩^S(U) = U » (clause (4) = CST1 à l'identité, hyp. explicite).

    Distinct de `ensembles_structures_props.identite_est_isomorphisme_espece` : on conclut
    ici la notion NOMMÉE `est_automorphisme` de IV.1.5 (et non est_isomorphisme).  UNIQUE
    hypothèse = clause (4) ; bijection inconditionnelle.  Conjonction (∧)."""
    ve, vu = _t(e), _t(u)
    DE = E.diagonale(ve)
    nom = ve.nom

    bij_thm = _diagonale_bijection_nom(nom)                 # ⊢ bij(Δ_E,E,E)  (clos)
    eq4_id = egal(structure_transportee(sigma, [DE], vu), vu)   # ⟨Δ_E⟩^S(U) = U
    h_eq4 = N.assume(eq4_id)
    res = conjonction_intro(bij_thm, h_eq4)
    cible = est_automorphisme(sigma, [DE], [ve], vu)
    assert res.conclusion == cible, "conclusion ≠ est_automorphisme(Σ,(Δ_E),[E],U)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  4.  UNICITÉ DE LA STRUCTURE TRANSPORTÉE  (IV.1.5 ; cœur CST5)
# ════════════════════════════════════════════════════════════════════════════
def transporte_unique_espece(sigma: Espece, e="E", ep="Ep", u="U", v="V", v2="V2",
                             f="f"):
    """{ est_isomorphisme(Σ, (f), E, E', U, V),
         est_isomorphisme(Σ, (f), E, E', U, V') }
        ⊢  V = V'.

    « IL EXISTE SUR E' UNE STRUCTURE … ET UNE SEULE telle que (f) soit un isomorphisme
    de (E,U) sur (E',·) » (IV.1.5 — UNICITÉ ; cœur de CST5).  Si (f) est un isomorphisme
    de (E,U) sur (E',V) ET sur (E',V'), alors V = V'.

    PREUVE : de chaque iso on EXTRAIT sa clause (4) (projection droite) : ⟨f⟩^S(U) = V et
    ⟨f⟩^S(U) = V'.  Le membre de gauche commun ⟨f⟩^S(U) (= la structure transportée
    `structure_transportee(Σ,(f),U)`) force V = V' par transitivité de = (S6/Leibniz).
    C'est l'UNICITÉ de CST5 au niveau de est_isomorphisme — DISTINCT de
    `ensembles_CST_criteres.cst5_unicite_transport` qui prend les égalités NUES sur le
    terme opaque `extension_echelon` ; ici on les TIRE des isomorphismes eux-mêmes.

    L'EXISTENCE (que ⟨f⟩^S(U) vérifie R, transportabilité) est REPORTÉE.  Hypothèses = les
    deux isomorphismes donnés ; AUCUN axiome de théorie ajouté ; purement logique."""
    ve, vep, vu, vv, vv2, vf = map(_t, (e, ep, u, v, v2, f))

    isoV = est_isomorphisme(sigma, [vf], [ve], [vep], vu, vv)
    isoV2 = est_isomorphisme(sigma, [vf], [ve], [vep], vu, vv2)
    hV, hV2 = N.assume(isoV), N.assume(isoV2)
    eqV = conjonction_elim_droite(hV)                       # ⟨f⟩^S(U) = V
    eqV2 = conjonction_elim_droite(hV2)                     # ⟨f⟩^S(U) = V'

    T = structure_transportee(sigma, [vf], vu)             # ⟨f⟩^S(U)
    # de (T=V) et (T=V') conclure V=V'  :
    #   S6(T, V, x, x=V') : (T=V) ⇒ ((T=V') ⇔ (V=V'))
    x = "x_uniq_transp"
    s6 = N.s6(T, vv, x, egal(var(x), vv2))
    eqv = N.modus_ponens(eqV, s6)                          # (T=V') ⇔ (V=V')
    res = N.modus_ponens(eqV2, equivalence_avant(eqv))     # V = V'
    assert res.conclusion == egal(vv, vv2), "conclusion ≠ (V = V')"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  5.  ÉCHELON D'IDENTITÉS DONNE UNE BIJECTION  (IV.1.2 ; CST2 à l'identité)
# ════════════════════════════════════════════════════════════════════════════
def echelon_identite_bijection(sigma: Espece, e="E"):
    """{ est_bijection_de(Δ_{S(E)}, S(E), S(E))         (bijection de l'identité de l'échelon),
         ⟨Δ_E⟩^S = Δ_{S(E)}                              (CST1 à l'identité, hyp. explicite) }
        ⊢  est_bijection_de(⟨Δ_E⟩^S, S(E), S(E)).

    « UN SCHÉMA D'ÉCHELON APPLIQUÉ À DES BIJECTIONS DONNE UNE BIJECTION » (IV.1.2, CST2),
    ICI à l'identité : l'extension canonique ⟨Δ_E⟩^S de l'identité est une bijection de
    l'échelon S(E) sur lui-même.

    PREUVE : Δ_{S(E)} (l'identité de l'échelon S(E)) est une bijection de S(E) sur S(E)
    (hyp. explicite — S(E) est un TERME COMPOSÉ, p.ex. 𝔓(E)×E, donc les paliers
    diagonale_* en nom de variable ne s'appliquent pas ; on fournit le fait en prémisse).
    Par CST1 à l'identité (IV.1.2 : l'extension de l'identité est l'identité de l'échelon),
    ⟨Δ_E⟩^S = Δ_{S(E)} (hyp. explicite) ; on réécrit Δ_{S(E)} ↦ ⟨Δ_E⟩^S (S6/Leibniz) dans
    l'énoncé de bijectivité, concluant que ⟨Δ_E⟩^S est une bijection de S(E) sur S(E).

    NON VACUEUX : pour un schéma NON TRIVIAL, ⟨Δ_E⟩^S (= ext_parties(Δ_E), produit_app, …)
    DIFFÈRE LITTÉRALEMENT de Δ_{S(E)} ; la conclusion porte sur ⟨Δ_E⟩^S, l'hypothèse sur
    Δ_{S(E)}.  Hypothèses EXPLICITES (CST2-id + CST1-id), AUCUN axiome de théorie ; logique
    pure (S6).  La PREUVE de CST1/CST2 (récurrence sur le schéma) est REPORTÉE."""
    ve = _t(e)
    DE = E.diagonale(ve)                                    # Δ_E
    SE = echelon(sigma.schema, [ve])                       # S(E)  (terme composé)
    DSE = E.diagonale(SE)                                  # Δ_{S(E)}
    extDE = extension_canonique(sigma.schema, [DE])        # ⟨Δ_E⟩^S

    # — hypothèses —
    bij_DSE = est_bijection_de(DSE, SE, SE)               # Δ_{S(E)} bijection  (CST2-id)
    cst1id = egal(extDE, DSE)                             # ⟨Δ_E⟩^S = Δ_{S(E)}  (CST1-id)
    h_bij, h_cst1 = N.assume(bij_DSE), N.assume(cst1id)

    # réécrit Δ_{S(E)} ↦ ⟨Δ_E⟩^S via cst1id (⟨Δ_E⟩^S = Δ_{S(E)}) : S6 sens arrière.
    #   S6(extDE, DSE, t, bij(t,S(E),S(E))) :
    #   (⟨Δ_E⟩^S = Δ_{S(E)}) ⇒ ( bij(⟨Δ_E⟩^S,…) ⇔ bij(Δ_{S(E)},…) )
    t = "t_echelon_id"
    motif = est_bijection_de(var(t), SE, SE)
    s6 = N.s6(extDE, DSE, t, motif)
    eqv = N.modus_ponens(h_cst1, s6)                      # bij(⟨Δ_E⟩^S) ⇔ bij(Δ_{S(E)})
    res = N.modus_ponens(h_bij, equivalence_arriere(eqv)) # bij(⟨Δ_E⟩^S, S(E), S(E))
    cible = est_bijection_de(extDE, SE, SE)
    assert res.conclusion == cible, "conclusion ≠ bij(⟨Δ_E⟩^S, S(E), S(E))"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  6.  UN ISOMORPHISME DONNE L'ÉGALITÉ DE TRANSPORT  (IV.1.5, relation (4))
# ════════════════════════════════════════════════════════════════════════════
def isomorphisme_donne_transport_eq(sigma: Espece, e="E", ep="Ep", u="U", up="Up",
                                    f="f"):
    """{ est_isomorphisme(Σ, (f), E, E', U, U') }  ⊢  ⟨f⟩^S(U) = U'.

    « SI (f) EST UN ISOMORPHISME DE (E,U) SUR (E',U'), ALORS LA STRUCTURE TRANSPORTÉE
    ⟨f⟩^S(U) ÉGALE U' » — c'est la relation (4) de IV.1.5, extraite de la définition de
    l'isomorphisme.  PREUVE : est_isomorphisme = (bijection) ∧ (⟨f⟩^S(U) = U') ; on prend
    la PROJECTION DROITE de la conjonction.  Purement logique.

    NON VACUEUX : la conclusion est l'ÉGALITÉ ⟨f⟩^S(U)=U', tandis que l'UNIQUE hypothèse
    est la CONJONCTION (bijection ∧ égalité) — formules LITTÉRALEMENT distinctes (la
    conclusion est un conjoint strict, pas la conjonction)."""
    ve, vep, vu, vup, vf = map(_t, (e, ep, u, up, f))
    iso = est_isomorphisme(sigma, [vf], [ve], [vep], vu, vup)
    h = N.assume(iso)
    res = conjonction_elim_droite(h)                       # ⟨f⟩^S(U) = U'
    cible = egal(structure_transportee(sigma, [vf], vu), vup)
    assert res.conclusion == cible, "conclusion ≠ (⟨f⟩^S(U) = U')"
    return res


__all__ = [
    "reciproque_isomorphisme_espece",         # 1 — réciproque d'iso est iso
    "sont_isomorphes_reflexive_espece",       # 2 — « sont isomorphes » réflexive
    "automorphisme_identite_espece",          # 3 — identité est automorphisme
    "transporte_unique_espece",               # 4 — unicité de la structure transportée
    "echelon_identite_bijection",             # 5 — échelon d'identités = bijection
    "isomorphisme_donne_transport_eq",        # 6 — iso ⇒ égalité de transport (4)
]
