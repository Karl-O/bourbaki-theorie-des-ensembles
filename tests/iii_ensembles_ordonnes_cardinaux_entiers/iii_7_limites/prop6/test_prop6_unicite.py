# -*- coding: utf-8 -*-
"""Tests — Prop. 6 1° §III.7.6 : UNICITÉ de u : lim→ E_α → F.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_unicite import (
    coincidence_limite_inductive, prop6_unicite,
)


def test_coincidence_limite_inductive():
    """{(24)×2, E=∪f_a⟨E_a⟩} ⊢ u et u' ont les mêmes valeurs sur E — 3 hyps."""
    th = coincidence_limite_inductive("u", "up", "E", "f", "I", "uf")
    assert len(th.hypotheses) == 3


def test_prop6_unicite():
    """🎯 « une application u ET UNE SEULE » (E III.62) : ⊢ u = u', 5 hyps."""
    th = prop6_unicite()
    assert th.conclusion == egal(var("u"), var("up"))
    assert len(th.hypotheses) == 5
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop6_surjectif():
    """🎯 Prop. 6 2° : u surjective ⇔ F = ∪ u_α⟨E_α⟩ — LES DEUX SENS, 3 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_surjectif import (
        prop6_surjectif,
    )
    th = prop6_surjectif()
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop6_injectif():
    """🎯🎯 Prop. 6 3° : u injective ⇔ (∀α)(u_α(x)=u_α(y) ⇒ ∃β≥α, f_βα(x)=f_βα(y))."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_injectif import (
        prop6_injectif,
    )
    th = prop6_injectif()
    assert len(th.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22


def test_compatible_v_coherence():
    """🏆 Cœur du 1° : (23) ⊢ v compatible avec R (R explicite) — 5 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_compatible import (
        compatible_v_coherence,
    )
    th = compatible_v_coherence()
    assert len(th.hypotheses) == 5
    assert len(E.theorie_ensembles().axiomes) == 22


def test_relation_24_modulo_c57():
    """👑 1° assemblage : v=h∘p ⊢ h(f_α(x))=u_α(x) — (24), CLOS modulo C57."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_assemblage import (
        relation_24_modulo_c57,
    )
    th = relation_24_modulo_c57()
    assert len(th.hypotheses) == 9
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop6_existence():
    """👑👑 Prop. 6 1° EXISTENCE : H(f_α(x)) = u_α(x), H construit via C57 — 8 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_existence import (
        prop6_existence,
    )
    th = prop6_existence()
    assert len(th.hypotheses) == 8
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cor1_relation_23():
    """🎯 Cor. 1 : la famille (g_α∘u_α) vérifie (23) — la Prop. 6 s'y applique."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_cor1_inductif import (
        cor1_relation_23,
    )
    th = cor1_relation_23()
    assert len(th.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22
