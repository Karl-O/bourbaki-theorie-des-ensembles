"""§IV.1.5 — Automorphisme-identité RÉEL : (S(E), U) est isomorphe à lui-même.

────────────────────────────────────────────────────────────────────────────────
  automorphisme_identite_reel :  { U ∈ S(E) }  ⊢
      est_bijection_de(⟨Δ_E⟩^S, S(E), S(E))  ∧  ⟨Δ_E⟩^S(U) = U
  (bijectivité = T5 réel CLOS ; valeur = congruence CST1-identité + Δ(U)=U) ;
  sont_isomorphes_reel : l'existentielle (∃g0)(bij(g0) ∧ g0(U)=U) par le
  témoin ⟨Δ_E⟩^S (S5) — la réflexivité de « sont isomorphes » au niveau réel.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_valeur,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_identite import (
    cst1_identite_prouve,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_echelon_identite_reelle import (
    echelon_identite_bijection_reelle,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.IV §1.5 Prop.- | E IV.6 L.19-23 | PDF p.209  (l'identité est un automorphisme — VERSION RÉELLE : bijectivité T5 + transport de structure trivial, 1 seule hypothèse U∈S(E))
def automorphisme_identite_reel(s: Schema, bases: Sequence, u: str = "U",
                                xg: str = "xg"):
    """{ U ∈ S(E) } ⊢ est_bijection_de(⟨Δ⟩^S, S(E), S(E)) ∧ ⟨Δ⟩^S(U) = U."""
    A = construction_echelon(s, [_t(b) for b in bases])
    SE, vU = A[-1], _t(u)
    diags = [E.diagonale(_t(b)) for b in bases]
    GD = extension_canonique_reelle(s, diags, bases, xg)[-1]
    bij = echelon_identite_bijection_reelle(s, bases, xg)  # CLOS
    #   ⟨Δ⟩^S(U) = Δ_{S(E)}(U) = U
    c1 = cst1_identite_prouve(s, bases, xg)                # ⟨Δ⟩^S = Δ_{S(E)}, CLOS
    e1 = N.modus_ponens(c1, congruence_terme(
        GD, E.diagonale(SE), E.valeur(var("w"), vU)))
    hU = N.assume(appartient(vU, SE))
    dv = diagonale_valeur("Xdv", "udv")
    imp = N.loi_deduction(appartient(var("udv"), var("Xdv")), dv)
    gen = N.generalisation("Xdv", N.generalisation("udv", imp))
    e2 = N.modus_ponens(hU, instancie(instancie(gen, SE), vU))   # Δ_{S(E)}(U)=U
    res = conjonction_intro(bij, composer_egalites(e1, e2))
    cible = et(est_bijection_de(GD, SE, SE), egal(E.valeur(GD, vU), vU))
    assert res.conclusion == cible, "automorphisme_identite_reel : ≠ cible"
    assert set(res.hypotheses) <= {hU.conclusion}, "automorphisme : hyps"
    return res


# @livre Ch.IV §1.5 Prop.- | E IV.6 L.19-23 | PDF p.209  (« sont isomorphes » est réflexive — VERSION RÉELLE, témoin ⟨Δ⟩^S)
def sont_isomorphes_reel(s: Schema, bases: Sequence, u: str = "U",
                         xg: str = "xg"):
    """{ U∈S(E) } ⊢ (∃g0)( est_bijection_de(g0, S(E), S(E)) ∧ g0(U)=U )."""
    A = construction_echelon(s, [_t(b) for b in bases])
    SE, vU = A[-1], _t(u)
    diags = [E.diagonale(_t(b)) for b in bases]
    GD = extension_canonique_reelle(s, diags, bases, xg)[-1]
    corps = et(est_bijection_de(var("g0"), SE, SE),
               egal(E.valeur(var("g0"), vU), vU))
    temoin = automorphisme_identite_reel(s, bases, u, xg)
    res = N.modus_ponens(temoin, N.s5(corps, GD, "g0"))
    assert res.conclusion == existe("g0", corps), "sont_isomorphes_reel : ≠"
    return res


__all__ = ["automorphisme_identite_reel", "sont_isomorphes_reel"]
