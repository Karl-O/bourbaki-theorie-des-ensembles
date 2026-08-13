# -*- coding: utf-8 -*-
"""Tests — surjectivité de g : G⟨lim←_I⟩ ⊂ lim←_J (§III.7.2).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, libres_f,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
    graphe_g,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_restriction_systeme import (
    restriction_construite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_g_surjection import (
    condition_1_de_la_valeur, valeur_dans_limite_restreinte,
    image_incluse_dans_limite, REPORTES,
)


def test_condition_1_quantifiee():
    """La condition (1) restreinte à J, quantifiée sur les DEUX indices — 2 hyps.

    Le piège franchi : la relation (2) porte ((α∈I et β∈I) et α≤β) comme UNE
    hypothèse composite ; la couper conjoint par conjoint ne suffit pas."""
    th = condition_1_de_la_valeur()
    assert len(th.hypotheses) == 2
    assert all("a" not in libres_f(h) and "b" not in libres_f(h)
               for h in th.hypotheses)


def test_inclusion_directe_ponctuelle():
    """👑👑 g(x) ∈ lim←_J — l'inclusion directe, ponctuelle, 2 hyps.

    Sur un lim←_J dont on peut parler (système restreint CONSTRUIT), là où le
    terme opaque du dépôt rendait l'énoncé indémontrable."""
    th = valeur_dans_limite_restreinte()
    assert th.conclusion == appartient(
        E.valeur(graphe_g(pt="s", idx="t"), var("d")),
        L.lim_proj(restriction_construite(), var("f")))
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_image_incluse_dans_limite():
    """👑👑👑 G⟨lim←_I⟩ ⊂ lim←_J — une MOITIÉ ENTIÈRE de la surjectivité, et
    sous forme d'inclusion (plus ponctuelle), avec UNE seule hypothèse : la
    cofinalité de J, c'est-à-dire l'hypothèse même de la Proposition 3."""
    th = image_incluse_dans_limite()
    assert th.conclusion == E.inclus(
        E.image(graphe_g(pt="s", idx="t"), L.lim_proj(var("E"), var("f"))),
        L.lim_proj(restriction_construite(), var("f")))
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reports_honnetes():
    """🔴 Le blocage `restriction_systeme_indices` et l'inclusion réciproque —
    seule pièce encore manquante de la Prop. 3 — sont consignés."""
    assert len(REPORTES) == 2
    assert "restriction_systeme_indices" in REPORTES[0]
    assert "INCLUSION RÉCIPROQUE" in REPORTES[1]
