# -*- coding: utf-8 -*-
"""§III.6.3 — H2 (pas 3a) : L'INDUCTIVITÉ ET ZORN SUR LE RÉSIDU GARDÉ.

🎯 CIBLES (rebranchement de la chaîne de Zorn sur la version gardée) :

    frame_inductif_garde :
        { m_dans_frame_garde(E),  (∃x)(x∈𝔉(E)) }  ⊢  est_inductif(Γ𝔉, 𝔉)

    frame_a_maximal_garde :
        { m_dans_frame_garde(E),  (∃x)(x∈𝔉(E)) }  ⊢  (∃m) element_maximal(Γ𝔉,𝔉,m)

Ce sont `frame_inductif_clean` et `frame_a_maximal` avec l'ancien résidu
∀C-nu (insatisfiable en C=∅) remplacé par le résidu GARDÉ, la chaîne vide
étant majorée par le témoin de H1.  Remarque qui économise une hypothèse :
`enonce_non_vide(𝔉(E))` et `residu_H1(E)` sont la MÊME formule — le témoin
de H1 sert donc deux fois (chaîne vide majorée, et poset non vide).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    est_inductif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre, maximal_pair_existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    enonce_chaine_majoree, frame_inductif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import (
    _frame_ordre_xyz_named, _frame_ordre_xyz,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_h2_garde import (
    m_dans_frame_garde, enonce_chaine_majoree_garde,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def frame_inductif_garde(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """🎯 { m_dans_frame_garde(E), (∃x)(x∈𝔉(E)) } ⊢ est_inductif(Γ𝔉,𝔉)  [2 hyps].

    `frame_inductif` (est_ordre ∧ enonce_chaine_majoree) avec l'ordre déchargé
    par frame_ordre_est_ordre (CLOS) et l'énoncé de chaîne majorée par sa
    version gardée."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    fi = frame_inductif(E_set, C, m, x, y, z)               # {est_ordre, ecm}
    ordre = _frame_ordre_xyz_named(E_set, x, y, z)          # CLOS
    hyp_ord = est_ordre(Gam, Fr, x, y, z)
    fi = N.modus_ponens(ordre, N.loi_deduction(hyp_ord, fi))
    ecm = enonce_chaine_majoree_garde(E_set, C, m, x, y, z)  # {garde, H1}
    hyp_ecm = enonce_chaine_majoree(Gam, Fr, C, m, x, y, z)
    assert hyp_ecm in fi.hypotheses, "frame_inductif_garde : ecm absente"
    res = N.modus_ponens(ecm, N.loi_deduction(hyp_ecm, fi))
    assert res.conclusion == est_inductif(Gam, Fr, C, m, x, y, z), \
        "frame_inductif_garde : ≠ est_inductif"
    assert set(res.hypotheses) == {m_dans_frame_garde(E_set, C, x, y, z),
                                   residu_H1(E_set)}, \
        "frame_inductif_garde : hyps ≠ {garde, H1}"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151  (« il existe dans 𝔐
#   un élément maximal (F,f) » — Zorn, ici sous le résidu gardé + H1)
def frame_a_maximal_garde(E_set="E"):
    """🎯 { m_dans_frame_garde(E), (∃x)(x∈𝔉(E)) }
       ⊢ (∃m) element_maximal(Γ𝔉(E), 𝔉(E), m)   [2 hyps].

    Zorn (`maximal_pair_existe`) exige (est_ordre ∧ est_inductif ∧ 𝔉≠∅) :
    l'ordre est CLOS, l'inductivité vient de la version gardée, et « 𝔉≠∅ »
    EST le résidu H1 (même formule) — d'où deux hypothèses seulement."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    mpe = maximal_pair_existe(E_set)
    ordre = _frame_ordre_xyz(E_set)                         # est_ordre(...,x,y,z)
    #   τ-hygiène : construire l'inductivité au binder SÛR « xmaj », puis α-pont
    induct_safe = frame_inductif_garde(E_set, "C", "m", "xmaj", "y", "z")
    induct = alpha_bridge(induct_safe,
                          est_inductif(Gam, Fr, "C", "m", "x", "y", "z"))
    h_nv = N.assume(residu_H1(E_set))                       # 𝔉(E)≠∅ = H1
    res = N.modus_ponens(conjonction_intro(
        conjonction_intro(ordre, induct), h_nv), mpe)
    assert res.conclusion == existe("m", element_maximal(Gam, Fr, var("m"), "x")), \
        "frame_a_maximal_garde : forme"
    assert set(res.hypotheses) == {m_dans_frame_garde(E_set), residu_H1(E_set)}, \
        "frame_a_maximal_garde : hyps ≠ {garde, H1}"
    return res


__all__ = ["frame_inductif_garde", "frame_a_maximal_garde"]
