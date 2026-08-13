"""§IV.2 (suite) — Structures FINALES : représentation OBJET paramétrée.

DUAL de la structure initiale (`ensembles_universel_morphismes`).  Introduit :
  • structure finale, propriété (FI) ;
  • image directe d'une structure (cas |I| = 1) ;
  • structure quotient (image directe par l'application canonique A → A/R).

Même convention de paramétrage que le module morphismes : prédicat abstrait
`morph(e1,s1,e2,s2,f)` (callable → Formule), structures = termes opaques, familles
= callables indexés af(ι)/sf(ι)/gf(ι).  Les DÉFINITIONS sont verbatim au Texte.tex ;
le THÉORÈME prouvé est le sens facile de (FI) (chaque g_ι est un morphisme dans la
structure finale), purement logique.

REPORTÉ : existence de la structure finale (CST22 dual), CST18 (unicité comme plus
fine), CST19 (transitivité), CST20 (passage des morphismes aux quotients),
décomposition canonique d'un morphisme.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, et, impl, equiv, pourtout, appartient,
                                       app)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    est_morphisme, _morph_defaut, _t)


# ════════════════════════════════════════════════════════════════════════════
#  STRUCTURE FINALE — propriété (FI)
# ════════════════════════════════════════════════════════════════════════════
#
#  Donnée : famille (A_ι, 𝒮_ι, g_ι)_{ι∈I}, ensemble E, g_ι : A_ι → E.
#
# @livre Ch.IV §2.5 Def.- | E IV.19 L.12-19 | PDF p.222
def propriete_FI(e, struct_F, i, af, sf, gf, ep="Ep", sp="Sp", f="f",
                 morph=None, iota="iota"):
    """(FI) — propriété caractéristique de la structure finale 𝓕 sur E (IV.2) :

      Quels que soient l'ensemble E', la structure 𝒮' d'espèce Σ sur E', et
      l'application f de E dans E', la relation « f est un morphisme de (E,𝓕) dans
      (E',𝒮') » est ÉQUIVALENTE à « quel que soit ι ∈ I, f ∘ g_ι est un morphisme
      de (A_ι,𝒮_ι) dans (E',𝒮') ».

    Codé (∀E')(∀𝒮')(∀f)[ morph(E,𝓕,E',𝒮',f) ⇔ (∀ι)(ι∈I ⇒ morph(A_ι,𝒮_ι,E',𝒮', f∘g_ι)) ].
    `struct_F` = la structure 𝓕 candidate ; gf(ι) = g_ι : A_ι → E."""
    vEp, vSp, vf, viota = var(ep), var(sp), var(f), var(iota)
    ve = _t(e)
    lhs = est_morphisme(ve, struct_F, vEp, vSp, vf, morph)
    comp = E.composee(vf, gf(viota))                      # f ∘ g_ι
    rhs_inner = impl(appartient(viota, i),
                     est_morphisme(af(viota), sf(viota), vEp, vSp, comp, morph))
    rhs = pourtout(iota, rhs_inner)
    return pourtout(ep, pourtout(sp, pourtout(f, equiv(lhs, rhs))))


# @livre Ch.IV §2.5 Def.- | E IV.19 L.6-11 | PDF p.222
def est_structure_finale(e, struct_F, i, af, sf, gf, morph=None):
    """« 𝓕 est structure finale pour la famille (A_ι, 𝒮_ι, g_ι)_{ι∈I} » := 𝓕 est
    une structure d'espèce Σ sur E vérifiant (FI)  (Déf. IV.2, structure finale)."""
    return propriete_FI(e, struct_F, i, af, sf, gf, morph=morph)


# @livre Ch.IV §2.5 Crit.CST18 | E IV.19 L.20-25 | PDF p.222
def chaque_g_iota_morphisme(e, struct_F, i, af, sf, gf, morph=None, iota="iota"):
    """« chaque g_ι est un morphisme de (A_ι,𝒮_ι) dans (E,𝓕) »  (la propriété dont
    CST18 affirme que la finale est la PLUS FINE).  Codé
    (∀ι)(ι∈I ⇒ morph(A_ι,𝒮_ι,E,𝓕, g_ι))."""
    viota = var(iota)
    ve = _t(e)
    return pourtout(iota, impl(appartient(viota, i),
        est_morphisme(af(viota), sf(viota), ve, struct_F, gf(viota), morph)))


# ── THÉORÈME (cœur de FI, sens facile, DUAL de l'initiale) ─────────────────────
# @livre Ch.IV §2.5 Crit.CST18 | E IV.19 L.26-35 | PDF p.222
def finale_implique_g_iota_morphisme(e="E", struct_F="F", i="I0",
                                     af=None, sf=None, gf=None, morph=None,
                                     iota="iota"):
    """{(FI) pour 𝓕}  ⊢  (∀ι)(ι∈I ⇒ g_ι∘Δ ... morphisme).

    Sens « facile » de (FI) : en prenant E'=E, 𝒮'=𝓕 et f=id_E=Δ_E, le membre de
    gauche « id_E est un morphisme de (E,𝓕) dans (E,𝓕) » est vrai (MO_III), d'où le
    membre de droite « (∀ι) id_E∘g_ι morphisme ».  Démontré logiquement : on assume
    (FI) et « id est morphisme », on instancie E'/𝒮'/f puis equivalence_avant.

    Renvoie le conditionnel ; hypothèses = {(FI), « id_E morphisme »}.  Forme avec
    Δ_E∘g_ι (le lemme Δ_E∘g_ι = g_ι est reporté avec la composition)."""
    struct_F = _t(struct_F)
    ve, vi = var(e), var(i)
    if af is None:
        af = lambda t: app("A", t)
    if sf is None:
        sf = lambda t: app("Sig", t)
    if gf is None:
        gf = lambda t: app("g", t)
    if morph is None:
        morph = _morph_defaut()

    fi = propriete_FI(e, struct_F, vi, af, sf, gf, morph=morph)
    h_fi = N.assume(fi)
    DE = E.diagonale(ve)
    inst = instancie(instancie(instancie(h_fi, ve), struct_F), DE)  # equiv lhs ⇔ rhs
    idm = est_morphisme(ve, struct_F, ve, struct_F, DE, morph)      # « id_E morphisme » (MO_III)
    h_id = N.assume(idm)
    return N.modus_ponens(h_id, equivalence_avant(inst))            # (∀ι)(ι∈I ⇒ Δ_E∘g_ι morphisme)


# ── image directe (cas |I| = 1) ───────────────────────────────────────────────
def _struct_image_directe(a, s, f):
    """Terme (opaque) de la structure image directe f(𝒮) — construction reportée."""
    return app("image_directe_struct", a, s, f)


# @livre Ch.IV §2.6 Def.- | E IV.21 L.5-8 | PDF p.224
def image_directe_structure(a, s, f, e, ep="Ep", sp="Sp", g="g", morph=None):
    """« structure image directe par f de 𝒮 » (IV.2) : structure finale pour le SEUL
    triplet (A, 𝒮, f) avec f : A → E (cas I singleton).  Caractérisée par (FI) à un
    indice : pour tout (E',𝒮',h),
        morph(E,𝓕,E',𝒮',h) ⇔ morph(A,𝒮,E',𝒮', h∘f).
    Renvoie cette caractérisation (∀E')(∀𝒮')(∀h)(…)."""
    vEp, vSp, vg = var(ep), var(sp), var(g)
    ve = _t(e)
    struct_F = _struct_image_directe(a, s, f)
    lhs = est_morphisme(ve, struct_F, vEp, vSp, vg, morph)
    rhs = est_morphisme(a, s, vEp, vSp, E.composee(vg, f), morph)
    return pourtout(ep, pourtout(sp, pourtout(g, equiv(lhs, rhs))))


# ── structure quotient ────────────────────────────────────────────────────────
# @livre Ch.IV §2.6 Def.- | E IV.21 L.9-15 | PDF p.224
def structure_quotient(a, s, R, morph=None):
    """« structure quotient de 𝒮 par la relation d'équivalence R » (IV.2) := image
    directe de 𝒮 par l'application canonique φ : A → A/R = E.

    `R` = le GRAPHE de la relation d'équivalence (terme).  E = A/R = quotient(R, A) ;
    φ = application canonique x ↦ Cl_R(x).  On prend φ = correspondance canonique
    (terme opaque application_canonique).  Renvoie la caractérisation (image directe)."""
    va = _t(a)
    e = E.quotient(R, va)                       # A/R
    phi = E.application_canonique(R, va)        # application canonique A → A/R
    return image_directe_structure(va, s, phi, e, morph=morph)


__all__ = [
    "propriete_FI", "est_structure_finale", "chaque_g_iota_morphisme",
    "finale_implique_g_iota_morphisme",
    "image_directe_structure", "structure_quotient",
]
