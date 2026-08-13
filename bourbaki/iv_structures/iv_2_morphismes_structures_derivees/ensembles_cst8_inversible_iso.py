"""§IV.2.1 — CRITÈRE CST8 : « un morphisme inversible est un isomorphisme ».

Module NEUF (campagne « fidélité chap. IV »).  Il formalise le critère CST8 TEL
QU'IL EST ÉNONCÉ DANS LE LIVRE (E IV.12, §IV.2.1), c'est-à-dire au niveau des
σ-MORPHISMES (et NON le critère IV.3.1 « unicité de la solution universelle à un
isomorphisme unique près », qui porte aussi par erreur le nom CST8 dans
`ensembles_structures_props.solution_universelle_iso_unique` et
`ensembles_structures_complements.solution_isomorphisme_unique` — voir ANOMALIES).

ÉNONCÉ DE BOURBAKI (E IV.12, verbatim) :

  « CST8.  Soient E, E' deux ensembles munis chacun d'une structure d'espèce Σ.
    Soit f un σ-morphisme de E dans E', g un σ-morphisme de E' dans E.  Si g∘f est
    l'application identique de E sur lui-même, et f∘g l'application identique de E'
    sur lui-même, f est un isomorphisme de E sur E', et g est l'isomorphisme
    réciproque. »

  Bourbaki : « La condition (MO_III) et la caractérisation des bijections (II, p. 18,
  corollaire) entraînent le critère suivant ».

CE QU'ON FORMALISE.  Le prédicat d'ISOMORPHISME au niveau morphisme est
`est_iso_morph(E,𝒮,E',𝒮',f) := morph(E,𝒮,E',𝒮',f) ET morph(E',𝒮',E,𝒮,f⁻¹)`
(membre de droite de l'équivalence (MO_III), IV.2.1 ; défini dans
`cst_criteres.ensembles_chap4_props_restantes`).  On certifie :

  { morph(E,𝒮,E',𝒮',f),            (f σ-morphisme de E dans E')
    morph(E',𝒮',E,𝒮,g),            (g σ-morphisme de E' dans E)
    g = f⁻¹ }                       (corollaire II p.18 : g∘f=Id et f∘g=Id ⟹ g=f⁻¹)
      ⊢  est_iso_morph(E,𝒮,E',𝒮',f).

La clause d'inversibilité bilatère « g∘f = Id_E et f∘g = Id_E' » N'EST PAS exprimable
au niveau du fragment σ-abstrait sans la caractérisation des bijections (II.18) ; on la
résume FIDÈLEMENT par son CONSÉQUENT « g = f⁻¹ » (le contenu exact que le corollaire
II.18 extrait de l'inversibilité bilatère : l'inverse bilatère d'une application EST sa
bijection réciproque), fourni en HYPOTHÈSE EXPLICITE — exactement comme CST3/CST12/CST20
fournissent leurs briques ensemblistes/d'unicité (réciproque du transport, égalités de
composées) en prémisses.  La PREUVE de II.18 (caractérisation des bijections par inverse
bilatère) est faite ailleurs (chap. II) et REPORTÉE ici sous forme d'égalité g = f⁻¹.

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé.  Tout est logique pur
(conjonction, S6/Leibniz, modus ponens) ou conditionnel à des hypothèses EXPLICITES :
les deux σ-morphismes (donnée de CST8) et l'égalité g = f⁻¹ (corollaire II.18 instancié,
prémisse — jamais postulée vraie dans la théorie).

CONVENTION DE PARAMÉTRAGE identique au reste du chap. IV (cf.
`ensembles_universel_morphismes`) : la donnée méta (Σ, σ) est portée par le prédicat
callable `morph(e1,s1,e2,s2,f) -> Formule`.  Le théorème ne dépend que de la STRUCTURE
LOGIQUE (∧, =, ⇔) — valable quelle que soit la donnée σ.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    est_morphisme, _morph_defaut, _t)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_chap4_props_restantes import (
    est_iso_morph)


def _morph(morph):
    return morph if morph is not None else _morph_defaut()


# @livre Ch.IV §2.1 Crit.CST8 | E IV.12 L.20-26 | PDF p.215
def cst8_morphisme_inversible_est_iso(e="E", s="S", ep="Ep", sp="Sp",
                                      f="f", g="g", morph=None):
    """CST8 (IV.2.1) — « UN MORPHISME INVERSIBLE EST UN ISOMORPHISME ».

    { morph(E,𝒮,E',𝒮', f),     (f est un σ-morphisme de E dans E')
      morph(E',𝒮',E,𝒮, g),     (g est un σ-morphisme de E' dans E)
      g = f⁻¹ }                 (corollaire II p.18 : g∘f=Id_E ∧ f∘g=Id_E' ⟹ g=f⁻¹)
        ⊢  est_iso_morph(E,𝒮,E',𝒮', f)  =  morph(E,𝒮,E',𝒮',f) ET morph(E',𝒮',E,𝒮,f⁻¹).

    « Soit f un σ-morphisme de E dans E', g un σ-morphisme de E' dans E.  Si g∘f est
    l'application identique de E et f∘g celle de E', f est un isomorphisme de E sur E',
    et g est l'isomorphisme réciproque. »  (E IV.12, CST8.)

    PREUVE (la « démonstration » de Bourbaki : (MO_III) + caractérisation des bijections) :
      • La caractérisation des bijections (II, p. 18, corollaire) fait de l'hypothèse
        d'inversibilité bilatère g∘f = Id_E et f∘g = Id_E' l'égalité g = f⁻¹ (g EST la
        bijection réciproque de f).  Cette égalité est fournie en HYPOTHÈSE EXPLICITE
        (II.18, reporté — comme toute brique ensembliste du chap. IV).
      • est_iso_morph(E,𝒮,E',𝒮',f) = morph(E,𝒮,E',𝒮',f) ET morph(E',𝒮',E,𝒮,f⁻¹)
        (caractérisation (MO_III) des isomorphismes, IV.2.1).
          – 1ʳᵉ clause morph(E,𝒮,E',𝒮',f) : hypothèse (f σ-morphisme de E dans E').
          – 2ᵉ clause morph(E',𝒮',E,𝒮,f⁻¹) : l'hypothèse morph(E',𝒮',E,𝒮,g) réécrite par
            g = f⁻¹ (S6/Leibniz) — c'est « g est l'isomorphisme réciproque ».
      • Recollement par conjonction = est_iso_morph(E,𝒮,E',𝒮',f).

    Hypothèses EXPLICITES : les deux σ-morphismes (donnée de CST8) + g = f⁻¹ (II.18).
    AUCUN axiome créé.  CONCLUSION == est_iso_morph(E,𝒮,E',𝒮',f) LITTÉRALEMENT (pas de
    tautologie : f ≠ f⁻¹, et la 2ᵉ clause utilise effectivement g = f⁻¹)."""
    morph = _morph(morph)
    ve, vs, vep, vsp, vf, vg = map(_t, (e, s, ep, sp, f, g))
    finv = E.reciproque(vf)                              # f⁻¹

    # — hypothèses (donnée de CST8) —
    morph_f = est_morphisme(ve, vs, vep, vsp, vf, morph)    # f : (E,𝒮) → (E',𝒮')
    morph_g = est_morphisme(vep, vsp, ve, vs, vg, morph)    # g : (E',𝒮') → (E,𝒮)
    h_f = N.assume(morph_f)                                 # 1ʳᵉ clause de l'iso
    h_g = N.assume(morph_g)

    # — caractérisation des bijections (II, p.18) : g = f⁻¹ (hyp explicite, reportée) —
    g_eq_finv = egal(vg, finv)                             # g = f⁻¹
    h_geq = N.assume(g_eq_finv)

    # — 2ᵉ clause morph(E',𝒮',E,𝒮, f⁻¹) : réécrire g ↦ f⁻¹ dans morph(E',𝒮',E,𝒮, g) —
    #   S6(g, f⁻¹, t, morph(E',𝒮',E,𝒮, t)) : (g = f⁻¹) ⇒ (morph(…,g) ⇔ morph(…,f⁻¹))
    t = "t_cst8"
    motif = est_morphisme(vep, vsp, ve, vs, var(t), morph)
    s6_rw = N.s6(vg, finv, t, motif)                       # (g=f⁻¹) ⇒ (morph(…,g) ⇔ morph(…,f⁻¹))
    eqv = N.modus_ponens(h_geq, s6_rw)                     # morph(…,g) ⇔ morph(…,f⁻¹)
    morph_finv = N.modus_ponens(h_g, equivalence_avant(eqv))   # morph(E',𝒮',E,𝒮, f⁻¹)

    # — recollement : conjonction (morph f ∧ morph f⁻¹) = est_iso_morph —
    iso = conjonction_intro(h_f, morph_finv)
    cible = est_iso_morph(ve, vs, vep, vsp, vf, morph)
    assert iso.conclusion == cible, "conclusion ≠ est_iso_morph(E,𝒮,E',𝒮',f) attendu"
    return iso


__all__ = ["cst8_morphisme_inversible_est_iso"]
