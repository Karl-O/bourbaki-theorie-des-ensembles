# -*- coding: utf-8 -*-
"""§III.6.3 — LES DONNÉES ÉLÉMENTAIRES DE U (extension, E.III.48).

🎯 CIBLES — deux des douze hypothèses de STEP 5 (`extension_absurde_chainee`),
celles qui découlent DIRECTEMENT de « U ⊂ E∖S₀ » :

    u_disjoint_S     : { U ⊂ E∖S₀ }        ⊢ (∀u)( u∈U ⇒ ¬(u∈S₀) )    [U∩S₀=∅]
    reunion_inclus_E : { S₀⊂E, U ⊂ E∖S₀ }  ⊢ S₀∪U ⊂ E

Bourbaki les passe sous silence (« Y ⊂ E∖F ») ; formellement elles sont les
deux conséquences immédiates du choix de U dans le COMPLÉMENT : ce qui est
hors de S₀ ne rencontre pas S₀, et ce qui vient de E∖S₀ reste dans E.

Les dériver ici retire deux hypothèses du paquet à quantifier sur U dans
l'assemblage final : seules restent la géométrie du carré et le paquet ψ.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, non, appartient, inclus, pourtout, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
    instancie, cas,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _membre_difference(e, x, z):
    """⊢ (z ∈ e∖x) ⇔ ( z∈e et ¬(z∈x) )   (instance de l'axiome de différence)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _membre_reunion(a, b, z):
    """⊢ (z ∈ a∪b) ⇔ ( z∈a ou z∈b )   (instance de l'axiome de réunion)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.29-30 | PDF p.151  (« une partie Y ⊂ E∖F » : Y∩F=∅)
def u_disjoint_S(E_set="E", S="S0", U="Ucadre", u="uwit"):
    """{ U ⊂ E∖S₀ } ⊢ (∀u)( u∈U ⇒ ¬(u∈S₀) ).      [U ∩ S₀ = ∅]

    Un point de U est dans E∖S₀, dont le second conjoint EST ¬(u∈S₀)."""
    vE, vS, vU, vu = _t(E_set), _t(S), _t(U), var(u)
    R = E.difference(vE, vS)
    h_inc = N.assume(inclus(vU, R))                          # (∀z)(z∈U ⇒ z∈E∖S₀)
    h_u = N.assume(appartient(vu, vU))
    dans_R = N.modus_ponens(h_u, instancie(h_inc, vu))       # u ∈ E∖S₀
    conj = N.modus_ponens(dans_R,
                          equivalence_avant(_membre_difference(vE, vS, vu)))
    res = N.generalisation(u, N.loi_deduction(appartient(vu, vU),
                                              conjonction_elim_droite(conj)))

    cible = pourtout(u, impl(appartient(vu, vU), non(appartient(vu, vS))))
    assert res.conclusion == cible, "u_disjoint_S : forme"
    assert list(res.hypotheses) == [inclus(vU, R)], "u_disjoint_S : hyps"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.30-31 | PDF p.151  (F∪Y reste une partie de E)
def reunion_inclus_E(E_set="E", S="S0", U="Ucadre", z="z"):
    """{ S₀⊂E, U ⊂ E∖S₀ } ⊢ S₀∪U ⊂ E.

    Disjonction sur l'appartenance à la réunion : le côté S₀ par S₀⊂E, le
    côté U par U⊂E∖S₀ puis le PREMIER conjoint de la différence."""
    vE, vS, vU, vz = _t(E_set), _t(S), _t(U), var(z)
    R = E.difference(vE, vS)
    h_S = N.assume(inclus(vS, vE))
    h_U = N.assume(inclus(vU, R))

    par_S = N.loi_deduction(appartient(vz, vS), N.modus_ponens(
        N.assume(appartient(vz, vS)), instancie(h_S, vz)))    # z∈S₀ ⇒ z∈E
    dans_R = N.modus_ponens(N.assume(appartient(vz, vU)), instancie(h_U, vz))
    conj_R = N.modus_ponens(dans_R,
                            equivalence_avant(_membre_difference(vE, vS, vz)))
    par_U = N.loi_deduction(appartient(vz, vU),
                            conjonction_elim_gauche(conj_R))  # z∈U ⇒ z∈E

    disj = N.modus_ponens(N.assume(appartient(vz, E.reunion(vS, vU))),
                          equivalence_avant(_membre_reunion(vS, vU, vz)))
    but = cas(disj, par_S, par_U)                             # z ∈ E
    res = N.generalisation(z, N.loi_deduction(
        appartient(vz, E.reunion(vS, vU)), but))

    assert res.conclusion == inclus(E.reunion(vS, vU), vE, z), \
        "reunion_inclus_E : forme"
    assert len(res.hypotheses) == 2, "reunion_inclus_E : hyps ≠ 2"
    return res


__all__ = ["u_disjoint_S", "reunion_inclus_E"]
