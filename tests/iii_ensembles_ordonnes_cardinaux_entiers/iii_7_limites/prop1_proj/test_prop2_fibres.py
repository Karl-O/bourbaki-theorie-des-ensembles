# -*- coding: utf-8 -*-
"""Tests — chaînon des fibres (Prop. 2 §III.7.2).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
    membre_fibre, REPORTES,
)


def test_membre_fibre():
    """🎯 {u fonctionnel, u total} ⊢ (z ∈ u⁻¹⟨{b}⟩ ⇔ u(z)=b) — 2 hyps."""
    th = membre_fibre()
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reports_honnetes():
    """Seule la 2e assertion de la Prop. 2 reste reportée (la 1re est prouvée)."""
    assert len(REPORTES) == 1


def test_membre_fibre_aux_termes():
    """🎯 Relais noms→termes : membre_fibre s'applique aux familles indexées.

    Vérifie aussi le piège de collision : la famille ne doit pas être notée
    « u » (liant de est_fonctionnel) — voir la docstring de membre_fibre_t."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        membre_fibre_t,
    )
    ub = C.u_indice(var("uf"), var("b"))
    th = membre_fibre_t(ub, E.valeur(var("xp"), var("b")), var("x"))
    assert len(th.hypotheses) == 2


def test_fibres_systeme_projectif():
    """👑 Prop. 2 1ʳᵉ assertion : f_αβ⟨M_β⟩ ⊂ M_α — 8 hyps honnêtes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        fibres_systeme_projectif,
    )
    th = fibres_systeme_projectif()
    assert len(th.hypotheses) == 8
    assert len(E.theorie_ensembles().axiomes) == 22


def test_famille_fibres_construite_et_son_pont():
    """👑 DÉBLOCAGE Prop. 2, 2ᵉ assertion : la famille des fibres est CONSTRUITE
    et sa composante se calcule.

    `M_indice` était un accesseur OPAQUE sans axiome — rien n'était démontrable
    sur les M_α, donc « u⁻¹(x') = lim← M_α » était hors d'atteinte par
    construction.  Rendu transparent (une famille EST une fonction), la famille
    peut être construite et le pont sort avec UNE hypothèse."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, appartient,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        famille_fibres, fibre_composante,
    )
    th = fibre_composante()
    va = var("a")
    assert th.conclusion == egal(
        C.M_indice(famille_fibres(), va),
        E.image(E.reciproque(C.u_indice(var("uf"), va)),
                E.singleton(E.valeur(var("xp"), va))))
    assert th.hypotheses == frozenset({appartient(va, var("I"))})
    assert len(E.theorie_ensembles().axiomes) == 22


def test_M_indice_est_transparent():
    """⚠️ Fige la transparence : M_α EST la valeur de la famille en α.

    Si quelqu'un le redéfinissait en `app("M_indice", …)` opaque, ce test
    mordrait — et la 2ᵉ assertion redeviendrait indémontrable."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    assert C.M_indice(var("M"), var("a")) == E.valeur_famille(var("M"), var("a"))


def test_coordonnee_dans_fibre():
    """👑👑 LE CHAÎNON de la 2ᵉ assertion : « pr_α z ∈ M_α » ⇔ « u_α(pr_α z)=x'_α ».

    C'est ce qui traduit l'appartenance à lim← M_α (côté gauche) en l'égalité
    u(z)=x' lue coordonnée par coordonnée (côté droit).  Trois hypothèses, toutes
    honnêtes : u_α fonctionnel, u_α total, α ∈ I."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, equiv, appartient,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        coordonnee_dans_fibre, famille_fibres,
    )
    th = coordonnee_dans_fibre()
    va, vz = var("a"), var("zf")
    ua = C.u_indice(var("uf"), va)
    pra = E.projection_indice(vz, va)
    assert th.conclusion == equiv(
        appartient(pra, C.M_indice(famille_fibres(), va)),
        egal(E.valeur(ua, pra), E.valeur(var("xp"), va)))
    assert len(th.hypotheses) == 3
    assert appartient(va, var("I")) in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_coordonnee_de_u_dans_fibre():
    """Le chaînon exprimé du côté de u(z) — la forme dont les DEUX côtés de la
    2ᵉ assertion ont besoin.  4 hypothèses."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        coordonnee_de_u_dans_fibre,
    )
    assert len(coordonnee_de_u_dans_fibre().hypotheses) == 4


def test_fibres_partout():
    """👑👑 LE CŒUR de la 2ᵉ assertion, QUANTIFIÉ — 2 hypothèses seulement.

    ⊢ ( (∀α)(α∈I ⇒ pr_α z ∈ M_α) ⇔ (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) )
    sous { famille des u_α fonctionnels et totaux, z ∈ lim←_I }.

    Le membre gauche est ce que réclame l'appartenance à lim← M_α ; le droit est
    ce que donne « u(z) = x' ».  Les relier, c'est relier les deux ensembles de
    l'identité u⁻¹(x') = lim← M_α.  Les hypothèses ponctuelles sont devenues une
    hypothèse de FAMILLE — c'est ce qui rend la généralisation licite."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, appartient, libres_f,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
        fibres_partout,
    )
    th = fibres_partout()
    assert len(th.hypotheses) == 2
    # la généralisation n'est licite que si α ne reste libre dans aucune hypothèse
    assert all("a" not in libres_f(h) for h in th.hypotheses)
    assert appartient(var("zf"), var("E")) not in th.hypotheses   # anti-tautologie
    assert len(E.theorie_ensembles().axiomes) == 22
