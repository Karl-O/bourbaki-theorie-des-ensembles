"""§III.6.3 — Théorème 2 (HESSENBERG) : ASSEMBLAGE du majorant-recollement de chaîne
en BIJECTION et sa FRAME-MEMBERSHIP (⋃S,⋃φ)∈𝔉(E), pivot de l'inductivité de Zorn.

Suite finale du recollement de chaîne (E.III.48).  Les composants COUPLE-NATIFS du
recollement sont clos en amont :
  • fonctionnalité + injectivité-couple    — `union_chaine_bijection_graphe`,
  • surjectivité-couple + couverture-dom   — `union_chaine_surjective`/`union_chaine_dom`.

Ce module ASSEMBLE :

  (1) `union_chaine_est_bijection` ⊢ est_bijection_de(⋃φ, US×US, US).
      est_bijection_de = ((est_fonctionnel ∧ dom=src) ∧ (injective_dans ∧ image=tgt)).
      La FONCTIONNALITÉ est GENUINEMENT DÉRIVÉE de `union_chaine_bijection_graphe`
      (conjonction_elim_gauche).  Les TROIS autres conjoints sont en forme
      VALEUR/ÉGALITÉ-D'ENSEMBLES (`dom(⋃φ)=US×US`, `injective_dans(⋃φ,US×US)`,
      `image(⋃φ,US×US)=US`), tandis que l'amont ne livre que les formes COUPLE-NATIVES
      (`injectif_graphe`, surjectivité/domaine couple-niveau).  Le PONT couple→valeur /
      couple→égalité-d'ensembles N'EXISTE PAS dans le dépôt (cf. docstrings amont) : ces
      trois conjoints sont donc portés en HYPOTHÈSES HONNÊTES (jamais postulées vraies ;
      la conclusion est_bijection_de ∉ hyps ; theorie=22).  C'est l'OBSTRUCTION EXACTE.

  (2) `union_chaine_dans_frame` ⊢ (US,⋃φ) ∈ 𝔉(E).
      Via l'axiome OPAQUE `axiome_frame` (`frame_membre`) et le corps existentiel
      _corps_frame : on fournit S:=US, φ:=⋃φ par double S5 (existe-intro), avec les
      quatre conjoints  p=(US,⋃φ) [réflexivité], US⊂E [hyp honnête], US infini [hyp
      honnête], ⋃φ bij. de US×US sur US [= étape (1)].

  (3) `enonce_chaine_majoree_preuve` / `frame_inductif_chaine` : NON assemblés
      INCONDITIONNELLEMENT — l'énoncé `enonce_chaine_majoree` quantifie sur TOUTE chaîne
      C et exige le MAJORANT (`majorant(Γ𝔉,C,m,𝔉)`), donnée d'ordre (S_i⊂US, φ_i⊂⋃φ)
      non produite par les briques couple-natives.  REPORTÉ ; obstruction détaillée en
      docstring de `frame_inductif_chaine`.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, equivalence_arriere,
)

from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.entiers.ensembles_infinis import est_infini_ensemble
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
from bourbaki.cardinaux.ensembles_union_chaine_bijection import (
    union_chaine_bijection_graphe,
)
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (1) ASSEMBLAGE en BIJECTION COMPLÈTE est_bijection_de(⋃φ, US×US, US).
#      Fonctionnalité DÉRIVÉE ; dom/injective/image portés en hyps honnêtes
#      (pont couple→valeur absent du dépôt — obstruction exacte).
# ════════════════════════════════════════════════════════════════════════════
def union_chaine_est_bijection(D="Dchaine", US="USchaine"):
    """{ famille_compatible(𝔇), famille_dirigee(𝔇), membres_injectifs(𝔇),
         dom(⋃𝔇)=US×US, injective_dans(⋃𝔇,US×US), image(⋃𝔇,US×US)=US }
       ⊢ est_bijection_de( ⋃𝔇, US×US, US ).                  [CLOS, hyps HONNÊTES].

    🎯 La BIJECTION-recollement de chaîne.  est_bijection_de =
        ((est_fonctionnel ∧ dom=src) ∧ (injective_dans ∧ image=tgt)).
    La FONCTIONNALITÉ est GENUINEMENT DÉRIVÉE (conjonction_elim_gauche de
    `union_chaine_bijection_graphe`) ; les trois conjoints VALEUR/ÉGALITÉ-D'ENSEMBLES
    (dom=src, injective_dans, image=tgt) sont portés en HYPOTHÈSES HONNÊTES faute du
    pont couple→valeur dans le dépôt (l'amont ne donne que injectif_graphe et la
    surjectivité/domaine couple-niveau).  Jamais postulées vraies ; conclusion ∉ hyps ;
    theorie=22."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)                                   # ⋃φ
    Prod = E.produit(vUS, vUS)                              # US×US

    # FONCTIONNALITÉ — genuinement dérivée du graphe-niveau amont.
    th_graphe = union_chaine_bijection_graphe(vD)           # est_fonctionnel(⋃φ) et injectif_graphe(⋃φ)
    th_fonc = conjonction_elim_gauche(th_graphe)            # est_fonctionnel(⋃φ)

    # Les trois conjoints valeur/égalité — hyps HONNÊTES (pont couple→valeur absent).
    h_dom = N.assume(egal(E.dom(U), Prod))                  # dom(⋃φ)=US×US
    h_inj = N.assume(E.injective_dans(U, Prod))             # injective_dans(⋃φ,US×US)
    h_img = N.assume(E.est_surjective(U, Prod, vUS))        # image(⋃φ,US×US)=US

    # est_bijection_de = ((fonctionnel ∧ dom=src) ∧ (injective_dans ∧ image=tgt))
    gauche = conjonction_intro(th_fonc, h_dom)
    droite = conjonction_intro(h_inj, h_img)
    res = conjonction_intro(gauche, droite)

    cible = est_bijection_de(U, Prod, vUS)
    assert res.conclusion == cible, "union_chaine_est_bijection : ≠ est_bijection_de"
    assert res.conclusion not in res.hypotheses, "union_chaine_est_bijection : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2) FRAME-MEMBERSHIP (US,⋃φ) ∈ 𝔉(E) via l'axiome OPAQUE axiome_frame.
#      Double S5 (existe-intro) avec S:=US, φ:=⋃φ sur le corps _corps_frame.
# ════════════════════════════════════════════════════════════════════════════
def union_chaine_dans_frame(E_set="E", D="Dchaine", US="USchaine"):
    """{ hyps de union_chaine_est_bijection, US⊂E, US infini }
       ⊢ (US,⋃𝔇) ∈ 𝔉(E).                                   [CLOS, hyps HONNÊTES].

    🎯 Le couple-recollement (⋃S,⋃φ) est une FRAME-PAIR (E.III.48).  Le corps de 𝔉,
    _corps_frame(E,p) = (∃S)(∃φ)( p=(S,φ) et S⊂E et S infini et φ bij. de S×S sur S ),
    est instancié par S:=US, φ:=⋃φ (double existe-intro S5).  Les quatre conjoints du
    témoin :
        • p=(US,⋃φ)         — réflexivité de l'égalité (p est PRÉCISÉMENT (US,⋃φ)) ;
        • US⊂E              — hyp HONNÊTE (chaque S_i⊂E ⇒ union⊂E) ;
        • US infini         — hyp HONNÊTE (chaîne d'union infinie) ;
        • ⋃φ bij. US×US→US  — = `union_chaine_est_bijection`.
    Puis `frame_membre` (axiome instancié) ⇐ pour conclure p∈𝔉(E).  Jamais postulé ;
    conclusion ∉ hyps ; theorie=22."""
    vE, vD, vUS = _t(E_set), _t(D), _t(US)
    U = union_famille(vD)                                   # ⋃φ
    Prod = E.produit(vUS, vUS)                              # US×US
    p = E.couple(vUS, U)                                    # (US,⋃φ)  — le témoin couple

    # les quatre conjoints du corps, témoin SUBSTITUÉ (S:=US, φ:=⋃φ) :
    th_bij = union_chaine_est_bijection(vD, vUS)            # ⋃φ bij. US×US→US
    h_incl = N.assume(inclus(vUS, vE))                      # US⊂E         [HONNÊTE]
    h_inf = N.assume(est_infini_ensemble(vUS))             # US infini     [HONNÊTE]
    refl = N.reflexivite(p)                                 # p=(US,⋃φ)  (réflexivité)

    # corps-témoin substitué :  (((p=(US,⋃φ) et US⊂E) et US infini) et bij)
    corps_sub = et(et(et(egal(p, p), inclus(vUS, vE)), est_infini_ensemble(vUS)),
                   est_bijection_de(U, Prod, vUS))
    th_corps = conjonction_intro(
        conjonction_intro(conjonction_intro(refl, h_incl), h_inf), th_bij)
    assert th_corps.conclusion == corps_sub, "frame : corps-témoin ≠ attendu"

    # ── existe-intro INTÉRIEUR (φ:=⋃φ) puis EXTÉRIEUR (S:=US) — motif _corps_frame.
    vS, vphi = var("S"), var("phi")
    SxS = E.produit(vS, vS)
    # corps interne (S=US fixé, φ liant) :  (∃phi)( (US,phi) et US⊂E et US infini et phi:US×US→US )
    R_interne = et(et(et(egal(p, E.couple(vUS, vphi)),
                         inclus(vUS, vE)), est_infini_ensemble(vUS)),
                   est_bijection_de(vphi, Prod, vUS))
    th_ex_phi = N.modus_ponens(th_corps, N.s5(R_interne, U, "phi"))   # (∃phi)R_interne

    # corps externe (S liant) :  (∃phi)( (S,phi) et S⊂E et S infini et phi:S×S→S )
    R_externe = existe("phi",
        et(et(et(egal(p, E.couple(vS, vphi)), inclus(vS, vE)),
               est_infini_ensemble(vS)),
           est_bijection_de(vphi, SxS, vS)))
    th_ex_S = N.modus_ponens(th_ex_phi, N.s5(R_externe, vUS, "S"))    # (∃S)(∃phi)... = corps_frame(E,p)

    # axiome_frame : (p∈𝔉(E)) ⇔ corps_frame(E,p).   ⇐ pour conclure (au TERME couple p).
    eq_p = _instancie_membre(vE, p)
    res = N.modus_ponens(th_ex_S, equivalence_arriere(eq_p))          # p∈𝔉(E)

    cible = appartient(p, frame_pair(vE))
    assert res.conclusion == cible, "union_chaine_dans_frame : ≠ (US,⋃φ)∈𝔉(E)"
    assert res.conclusion not in res.hypotheses, "union_chaine_dans_frame : VACUOUS"
    return res


def _instancie_membre(vE, p_term):
    """frame_membre instancié au TERME couple p=(US,⋃φ) (pas à la variable 'p')."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    from bourbaki.cardinaux.ensembles_hessenberg_hard import (
        theorie_frame, axiome_frame,
    )
    ax = N.axiome(theorie_frame(), axiome_frame())
    return instancie(instancie(ax, vE), p_term)


# ════════════════════════════════════════════════════════════════════════════
#  (3) FRAME-INDUCTIF (chaîne) — re-export du `frame_inductif` clos, AVEC le
#      diagnostic EXACT de l'obstruction qui empêche de décharger
#      `enonce_chaine_majoree` inconditionnellement.
# ════════════════════════════════════════════════════════════════════════════
def frame_inductif_chaine(E_set="E", C="C", m="m", x="x", y="y", z="z"):
    """{ est_ordre(Γ𝔉,𝔉), enonce_chaine_majoree(Γ𝔉,𝔉) } ⊢ est_inductif(Γ𝔉,𝔉).

    = `frame_inductif` (déjà clos en amont) — RE-EXPORTÉ tel quel.  L'hypothèse
    HONNÊTE `enonce_chaine_majoree` N'EST PAS déchargée par ce module ; voici
    l'OBSTRUCTION EXACTE (REPORTÉE, jamais postulée vraie) :

      enonce_chaine_majoree(Γ𝔉,𝔉) = (∀C)( chaine(Γ𝔉,𝔉,C) ⇒ (∃m) majorant(Γ𝔉,C,m,𝔉) ),
      majorant(Γ𝔉,C,m,𝔉) = ( m∈𝔉 et (∀x)(x∈C ⇒ (x,m)∈Γ𝔉) ),  témoin m=(⋃S,⋃φ).

      • OBSTRUCTION A (témoin abstrait) : C est quantifié UNIVERSELLEMENT, donc
        ⋃S=⋃pr₁(C) et ⋃φ=⋃pr₂(C) sont des FONCTIONS de C ; produire le couple-témoin
        m exige d'EXTRAIRE de chaque membre (S_i,φ_i)∈C ses projections et de les
        unionner.  Cette construction (familles indexées par les membres de C) n'est
        PAS disponible.  De surcroît la frame-membership `union_chaine_dans_frame`
        ci-dessus est sous hyps HONNÊTES (compat/dirigée/injectifs + dom/inj/img-valeur
        + ⋃S⊂E + ⋃S infini), elles-mêmes non déchargées pour une chaîne abstraite.

      • OBSTRUCTION B (ordre opaque) : le second conjoint (∀x)(x∈C ⇒ (x,m)∈Γ𝔉)
        exige (S_i,φ_i) ≤ (⋃S,⋃φ) dans `frame_ordre`.  Or `frame_ordre` est un TERME
        OPAQUE (`E.app("hessenberg_frame_ordre",·)`) SANS aucun axiome définissant
        l'appartenance (x,m)∈Γ𝔉 — il n'existe PAS d'`axiome_frame_ordre` dans le
        dépôt (à la différence de `axiome_frame` pour 𝔉).  Donc (x,m)∈Γ𝔉 n'est PAS
        établissable : la moitié « ordre » du majorant est hors d'atteinte.

    Ce module ferme donc l'ASSEMBLAGE bijection (étape 1, fonctionnalité dérivée) et
    la FRAME-MEMBERSHIP (étape 2, via l'axiome opaque 𝔉) ; la décharge de
    `enonce_chaine_majoree` reste bloquée par A+B.  `frame_inductif` (et donc
    `frame_inductif_chaine`) demeure CLOS sous ses deux hyps honnêtes ; conclusion ∉
    hyps ; theorie=22."""
    from bourbaki.cardinaux.ensembles_hessenberg_inductivite import frame_inductif
    return frame_inductif(E_set, C, m, x, y, z)


__all__ = [
    "union_chaine_est_bijection",
    "union_chaine_dans_frame",
    "frame_inductif_chaine",
]
