"""§IV.1.2 — T5 RÉEL : ⟨Δ_{E₁},…⟩^S_réel est une bijection de S(E) sur S(E).

────────────────────────────────────────────────────────────────────────────────
Le consommateur RÉEL d'`echelon_identite_bijection` (transport_iso_props:286) :
l'opaque garde ses 2 hypothèses EXPLICITES (bij(Δ_{S(E)}) et CST1-identité sur
le terme `extension_canonique` opaque) ; la version réelle les DÉCHARGE toutes
deux et conclut CLOS (0 hyp) :

  • bij(Δ_{S(E)}, S(E), S(E)) — les 4 paliers diagonale_* (equipotence,
    noms-seulement, CLOS) assemblés en ((func,dom),(inj,img)) puis généralisés
    et instanciés au TERME S(E) (l'obstacle « S(E) est un terme composé » de
    l'opaque tombe : les paliers clos se généralisent) ;
  • ⟨Δ⟩^S_réel = Δ_{S(E)} — le générateur `cst1_identite_prouve` (CLOS).
La réécriture finale est le même S6 arrière que l'opaque.  L'opaque RESTE pour
ses consommateurs (kwarg-gating inutile : fonction sœur, rien ne casse).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_fonctionnelle, diagonale_domaine, diagonale_injective, diagonale_image,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_identite import (
    cst1_identite_prouve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _bij_diagonale_t(set_t):
    """⊢ est_bijection_de(Δ_X, X, X), X TERME.                    [CLOS, 0 hyp].

    Les 4 paliers diagonale_* au nom « Xdb » (clos), généralisés-instanciés."""
    nom = "Xdb"
    bij = conjonction_intro(
        conjonction_intro(diagonale_fonctionnelle(nom), diagonale_domaine(nom)),
        conjonction_intro(diagonale_injective(nom), diagonale_image(nom)))
    res = instancie(N.generalisation(nom, bij), _t(set_t))
    assert res.conclusion == est_bijection_de(
        E.diagonale(_t(set_t)), _t(set_t), _t(set_t)), "_bij_diagonale_t : ≠ cible"
    return res


# @livre Ch.IV §1.2 Crit.CST2 | E IV.2 L.33-34 | PDF p.205
# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (T5 réel : l'extension canonique de la famille des identités est une bijection de l'échelon sur lui-même — les 2 hyps de l'opaque DÉCHARGÉES)
def echelon_identite_bijection_reelle(s: Schema, bases: Sequence, xg: str = "xg"):
    """⊢ est_bijection_de(⟨Δ_{E₁},…⟩^S_réel, S(E), S(E)).          [CLOS, 0 hyp]."""
    diags = [E.diagonale(_t(b)) for b in bases]
    SE = echelon(s, [_t(b) for b in bases])
    ext = extension_canonique_reelle(s, diags, bases, xg)[-1]

    bij_DSE = _bij_diagonale_t(SE)                 # bij(Δ_{S(E)}, S(E), S(E))
    cst1 = cst1_identite_prouve(s, bases, xg)      # ⟨Δ⟩^S_réel = Δ_{S(E)}
    motif = est_bijection_de(var("t_echelon_id"), SE, SE)
    eqv = N.modus_ponens(cst1, N.s6(ext, E.diagonale(SE), "t_echelon_id", motif))
    res = N.modus_ponens(bij_DSE, equivalence_arriere(eqv))
    cible = est_bijection_de(ext, SE, SE)
    assert res.conclusion == cible, "echelon_identite_bijection_reelle : ≠ cible"
    assert not res.hypotheses, "echelon_identite_bijection_reelle : NON clos"
    return res


__all__ = ["echelon_identite_bijection_reelle"]
