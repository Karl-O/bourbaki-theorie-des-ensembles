"""§III.6.3 — Théorème 2 (HESSENBERG), DIRECTION PROFONDE :  𝔞·𝔞 ≤ 𝔞  pour 𝔞 INFINI.

« THÉORÈME 2 (E.III.6.3) : pour tout cardinal infini 𝔞, on a 𝔞² = 𝔞. »

La direction FACILE (𝔞 ≤ 𝔞·𝔞, diagonale) et la réduction Cantor–Bernstein sont
CLOSES dans `bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg` (`cardinal_inf_egal_carre`,
`carre_inf_egal_si_hard`, `hessenberg_si_hard`, `hessenberg_depuis_hard`).  Ce
module attaque la direction PROFONDE 𝔞·𝔞 ≤ 𝔞 par l'argument de ZORN de Bourbaki
(E.III.48, lu sur le PDF source) — Zorn EST disponible (`zorn_theoreme`).

────────────────────────────────────────────────────────────────────────────────
PREUVE DE BOURBAKI (E.III.48, VERBATIM du raisonnement) :

  Soit E un ensemble tel que Card(E)=𝔞 (𝔞 infini).  Soit D ⊂ E équipotent à ℕ
  (Lemme 1).  Il existe ψ₀ : D→D×D bijective (Lemme 2, ℕ×ℕ ≈ ℕ).  Soit 𝔐
  l'ensemble des couples (X,ψ), X ⊂ E contenant D et ψ : X→X×X bijective
  prolongeant ψ₀.  On ordonne 𝔐 par

      (X,ψ) ≤ (X',ψ')  ⟺  X ⊂ X'  et  ψ' prolonge ψ.

  On vérifie aussitôt que 𝔐 est INDUCTIF (réunion d'une chaîne : union des X,
  union des ψ — recollement de bijections à domaines emboîtés).  Par ZORN, 𝔐 a
  un élément MAXIMAL (F,f), f : F→F×F bijective, donc Card(F)² = Card(F).

  CLAIM : Card(F) = 𝔞.  Sinon 𝔟 := Card(F) < 𝔞.  Comme 𝔟 = 𝔟² et 𝔟 infini, on a
  𝔟 ≤ 2𝔟 ≤ 3𝔟 ≤ 𝔟² = 𝔟 (III p.30 prop.14), donc 2𝔟 = 𝔟 et 3𝔟 = 𝔟.  Comme
  𝔟 < 𝔞 = Card(E) et 𝔞 infini, Card(E∖F) > 𝔟 ; on prend Y ⊂ E∖F équipotent à F,
  Z = F ∪ Y.  Alors
      Z×Z = (F×F) ∪ (F×Y) ∪ (Y×F) ∪ (Y×Y)   (réunion DISJOINTE),
  et Card((F×Y)∪(Y×F)∪(Y×Y)) = 3𝔟 = 𝔟 = Card(Y), d'où une bijection f₁ de Y sur
  ce « cadre » ; g := f ∪ f₁ : Z→Z×Z bijective PROLONGE f — contredit la
  maximalité.  Donc Card(F)=𝔞 et 𝔞² = Card(F)² = Card(F) = 𝔞.

────────────────────────────────────────────────────────────────────────────────
ÉTAT (HONNÊTE — ce module).  Le SQUELETTE Zorn est posé fidèlement :

  • `frame_pair`            — le poset 𝔉 des couples (S,φ), φ:S×S→S BIJECTIVE,
                              S ⊂ E infini ; TERME opaque + axiome DÉFINITIONNEL
                              (motif axiome_M, S8+A1) ;  theorie_ensembles() = 22.
  • `maximal_pair_existe`   ⊢ ( est_ordre(Γ𝔉,𝔉) et est_inductif(Γ𝔉,𝔉) et 𝔉≠∅ )
                              ⇒ (∃m) element_maximal(Γ𝔉,𝔉,m).
                              CLOS — application DIRECTE de `zorn_theoreme`
                              (les trois hyps de Zorn sont l'antécédent, jamais
                              supposées vraies : elles sont transportées).
  • `enonce_hard_aa_inf_egal_a` (RÉ-EXPORTÉ de ensembles_hessenberg) — la cible ≥.
  • `hessenberg_carre`      ⊢ ( est_infini(a) ⇒ a·a≤a ) ⇒ ( est_infini(a) ⇒ a·a=a ).
                              = `hessenberg_depuis_hard` (le PONT), CLOS, qui livre
                              le THÉORÈME COMPLET dès que le ≥ dur tombe.

RÉSIDU HONNÊTE (le SEUL verrou, JAMAIS postulé vrai) :
  `enonce_hard_aa_inf_egal_a` :  est_infini(Card A) ⇒ (Card A · Card A ≤ Card A).
La construction interne de 𝔉 (inductivité = recollement de bijections d'une
chaîne, et surtout l'extension du maximal via 3𝔟=𝔟) n'est PAS assemblée : ni
l'inductivité de 𝔉 ni le « maximal ⇒ Card(F)=𝔞 » ne sont prouvés.  Ils restent à
construire ; ce module fournit l'ÉCHAFAUDAGE Zorn + le branchement sur le pont.

INVARIANT : theorie_ensembles() reste = 22.  Rien n'est postulé ; a²=a n'est JAMAIS
supposé, le ≥ dur n'est JAMAIS supposé vrai (toujours en antécédent).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, equiv, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, est_bijection_de, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini, est_infini_ensemble
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre, element_maximal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif, enonce_non_vide
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import zorn_theoreme

# Le PONT FINAL + l'énoncé-frontière sont DÉJÀ clos dans ensembles_hessenberg ; on
# les RÉ-EXPORTE pour offrir Hessenberg complet « dès que le ≥ tombe ».
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    hessenberg_depuis_hard, enonce_hard_aa_inf_egal_a, enonce_hessenberg,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  LE POSET 𝔉 DES COUPLES (S, φ),  φ : S×S → S BIJECTIVE,  S ⊂ E infini.
#  TERME opaque + axiome DÉFINITIONNEL (motif axiome_M, S8+A1).
#  theorie_ensembles() reste INCHANGÉE = 22 (axiome en théorie DÉDIÉE).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.19-21 | PDF p.151  (« Soit 𝔐 l'ensemble des couples (X,ψ), où X est une partie de E contenant D… »)
def frame_pair(E_set):
    """𝔉(E) := { p | (∃S)(∃φ)( p=(S,φ) et S⊂E et S infini et φ bij. de S×S sur S ) }.

    L'ensemble des couples (S,φ) de l'argument de Zorn de Bourbaki (E.III.48).
    Terme OPAQUE : sa caractérisation est portée par l'axiome `axiome_frame`."""
    return E.app("hessenberg_frame", _t(E_set))


def _corps_frame(E_set, p, S="S", phi="phi"):
    """Corps de 𝔉 :  (∃S)(∃φ)( p=(S,φ) et S⊂E et S infini et φ:S×S→S bijective )."""
    vS, vphi = var(S), var(phi)
    SxS = E.produit(vS, vS)
    return existe(S, existe(phi,
        et(et(et(egal(_t(p), E.couple(vS, vphi)), inclus(vS, _t(E_set))),
               est_infini_ensemble(vS)),
           est_bijection_de(vphi, SxS, vS))))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.19-21 | PDF p.151  (axiome définitionnel du poset 𝔐, théorie dédiée)
def axiome_frame(E_set="E", p="p", S="S", phi="phi"):
    """⊢-schéma (∀E p)( p∈𝔉(E) ⇔ corps_frame ).

    Axiome DÉFINITIONNEL du poset des couples-bijections (sélection S8+A1, motif
    axiome_M).  N'altère PAS theorie_ensembles()."""
    vE, vp = var(E_set), var(p)
    return pourtout(E_set, pourtout(p,
        equiv(appartient(vp, frame_pair(vE)), _corps_frame(vE, vp, S, phi))))


def theorie_frame(E_set="E", p="p", S="S", phi="phi"):
    """Théorie DÉDIÉE ne contenant que l'axiome de 𝔉 (E.III.6, Hessenberg, Zorn)."""
    return N.Theorie("Frame-Hessenberg", [axiome_frame(E_set, p, S, phi)])


def frame_membre(E_set="E", p="p"):
    """⊢ ( p∈𝔉(E) ) ⇔ corps_frame(E,p).   (axiome instancié.)"""
    ax = N.axiome(theorie_frame(), axiome_frame())
    return instancie(instancie(ax, var(E_set)), var(p))


# ════════════════════════════════════════════════════════════════════════════
#  Le GRAPHE D'ORDRE Γ𝔉 sur 𝔉 : extension ((S,φ) ≤ (S',φ') ⟺ S⊂S' et φ'⊃φ).
#  Terme opaque + axiome DÉFINITIONNEL.   theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-23 | PDF p.151  (le graphe d'ordre Γ𝔐 de l'extension « X⊂X′ et ψ′ prolonge ψ »)
def frame_ordre(E_set):
    """Γ𝔉(E) := { (p,q) | p∈𝔉 et q∈𝔉 et S_p⊂S_q et φ_q prolonge φ_p }.

    Graphe d'ordre de l'EXTENSION sur 𝔉 (Bourbaki : « X⊂X' et ψ' prolonge ψ »).
    Terme OPAQUE."""
    return E.app("hessenberg_frame_ordre", _t(E_set))


# ════════════════════════════════════════════════════════════════════════════
#  EXTRACTION DU MAXIMAL — application DIRECTE de ZORN.   CLOS.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151  (application de Zorn : 𝔐 inductif ⇒ élément maximal (F,f))
def maximal_pair_existe(E_set="E"):
    """⊢ ( est_ordre(Γ𝔉,𝔉) et est_inductif(Γ𝔉,𝔉) et 𝔉≠∅ )
         ⇒ (∃m) element_maximal(Γ𝔉,𝔉,m).

    Application DIRECTE du THÉORÈME DE ZORN (`zorn_theoreme`) au poset (Γ𝔉,𝔉) des
    couples-bijections.  CLOS : les trois hypothèses de Zorn sont EXACTEMENT
    l'antécédent ici (jamais supposées vraies ; transportées).  C'est le pivot de
    l'argument de Bourbaki E.III.48 : « il existe donc dans 𝔐 un élément maximal
    (F,f), en vertu du th. 2 [Zorn] »."""
    vE = _t(E_set)
    Gam = frame_ordre(vE)                                 # Γ𝔉
    Fr = frame_pair(vE)                                   # 𝔉
    # zorn_theoreme : ( est_ordre(G,E) et est_inductif(G,E) et E≠∅ )
    #                    ⇒ (∃m) element_maximal(G,E,m).
    # On le GÉNÉRALISE en (G,E) puis on l'INSTANCIE à (Γ𝔉,𝔉) — motif prop9/prop10,
    # pour éviter la capture des noms internes du noyau de Zorn.
    zt = zorn_theoreme("G", "E", "m", "C", "x", "y", "z")
    zt_gen = N.generalisation("G", N.generalisation("E", zt))
    return instancie(instancie(zt_gen, Gam), Fr)          # (hyps@Γ𝔉,𝔉) ⇒ (∃m)maximal


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS-FRONTIÈRE et PONT FINAL — re-export du chantier Hessenberg.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150  (le théorème complet dès que la direction dure a·a≤a tombe)
def hessenberg_carre(a="A"):
    """⊢ ( est_infini(a) ⇒ a·a≤a ) ⇒ ( est_infini(a) ⇒ a·a=a ),   a := Card A.

    PONT FINAL (= `hessenberg_depuis_hard`).  Avec la direction PROFONDE (sous
    est_infini), la diagonale + Cantor–Bernstein referment Hessenberg COMPLET.
    CLOS — l'unique hypothèse est EXACTEMENT `enonce_hard_aa_inf_egal_a` (le ≥
    dur), JAMAIS supposée vraie, seulement transportée.  Donne le THÉORÈME
    COMPLET (est_infini(a) ⇒ a²=a) dès que le ≥ dur est fourni."""
    return hessenberg_depuis_hard(a)


__all__ = [
    # poset de Zorn 𝔉
    "frame_pair", "axiome_frame", "theorie_frame", "frame_membre", "frame_ordre",
    # extraction du maximal (CLOS, via Zorn)
    "maximal_pair_existe",
    # pont final + énoncés-frontière (re-export)
    "hessenberg_carre", "hessenberg_depuis_hard",
    "enonce_hard_aa_inf_egal_a", "enonce_hessenberg",
]
