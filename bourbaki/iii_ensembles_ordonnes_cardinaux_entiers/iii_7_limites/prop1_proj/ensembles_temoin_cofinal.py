"""§III.1.8 / §III.7.2 — le TÉMOIN COFINAL CANONIQUE, sans axiome du choix.

────────────────────────────────────────────────────────────────────────────────
Toute la Prop. 3 (§III.7.2 : une partie cofinale J donne une canonique
g : lim←_I → lim←_J BIJECTIVE) repose, côté SURJECTIVITÉ, sur le prolongement
d'un point de lim←_J à tout I : pour α∈I, il faut CHOISIR β∈J avec α≤β.

Ce module fournit ce choix SANS axiome du choix, par le témoin canonique τ de
Bourbaki (même motif que `section_construite_par_tau` E II.18 et que la
section de C57) :

    beta(α)  :=  τ_y( y ∈ J  et  α ≤ y )

  { J cofinale dans I,  α ∈ I }  ⊢  ( beta(α) ∈ J  et  α ≤ beta(α) )

— la cofinalité donne (∃y)(y∈J et α≤y), donc le témoin CANONIQUE satisfait la
relation (existe_temoin) : β(α) est un majorant de α DANS J, choisi
uniformément.  C'est le chaînon qui manquait pour attaquer la surjectivité.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, tau, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, conjonction_intro, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal import (
    est_cofinale_dans, est_partie_filtrante_droite,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _R_gleq():
    """Le préordre par défaut du chapitre (lu sur le graphe Gleq)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# @livre Ch.III §1.8 Def.- | E III.11 L.20-24 | PDF p.118  (le majorant canonique dans une partie cofinale : β(α) := τ_y(y∈J et α≤y))
def beta_cofinal(jj, a, R=None, y="y"):
    """beta(α) := τ_y( y∈J et α≤y )  — le majorant canonique de α dans J."""
    if R is None:
        R = _R_gleq()
    vJ, va = _t(jj), _t(a)
    return tau(y, et(appartient(var(y), vJ), R(va, var(y))))


# @livre Ch.III §1.8 Prop.- | E III.11 L.20-24 | PDF p.118  (le témoin canonique d'un majorant cofinal EST un majorant dans J — sans axiome du choix)
def temoin_cofinal(jj="J", i="I", a="ai", R=None, x="x", y="y"):
    """{ J cofinale dans I, α∈I } ⊢ ( beta(α) ∈ J  et  α ≤ beta(α) ).  [2 hyps].

    La cofinalité, instanciée en α, donne (∃y)(y∈J et α≤y) ; `existe_temoin`
    transfère la relation au témoin CANONIQUE τ_y — d'où un majorant de α dans
    J, défini uniformément en α, sans aucun choix."""
    if R is None:
        R = _R_gleq()
    vJ, vi, va = _t(jj), _t(i), _t(a)
    h_cof = N.assume(est_cofinale_dans(R, vJ, vi, x, y))
    h_a = N.assume(appartient(va, vi))
    coeur = conjonction_elim_droite(h_cof)          # (∀x)(x∈I ⇒ (∃y)(y∈J et x≤y))
    ex = N.modus_ponens(h_a, instancie(coeur, va))  # (∃y)(y∈J et α≤y)
    corps = et(appartient(var(y), vJ), R(va, var(y)))
    res = N.modus_ponens(ex, N.existe_temoin(corps, y))
    assert res.conclusion == et(appartient(beta_cofinal(vJ, va, R, y), vJ),
                                R(va, beta_cofinal(vJ, va, R, y))), \
        "temoin_cofinal : ≠ (β(α)∈J et α≤β(α))"
    assert set(res.hypotheses) == {h_cof.conclusion, h_a.conclusion}, \
        "temoin_cofinal : hyps ≠ 2"
    return res


# @livre Ch.III §1.10 Def.7 | E III.13 L.9-13 | PDF p.120  (le majorant commun canonique dans une partie filtrante : ν(λ,μ) := τ_z(z∈J et λ≤z et μ≤z))
def nu_majorant_commun(jj, a, b, R=None, z="z"):
    """ν(λ,μ) := τ_z( (z∈J et λ≤z) et μ≤z )  — le majorant commun canonique.

    Le pendant de `beta_cofinal` pour la FILTRANCE : là où la cofinalité donne un
    majorant d'UN élément, la filtrance en donne un de DEUX.  Même construction —
    le τ de la relation — donc même absence d'axiome du choix."""
    if R is None:
        R = _R_gleq()
    vJ, va, vb = _t(jj), _t(a), _t(b)
    vz = var(z)
    return tau(z, et(et(appartient(vz, vJ), R(va, vz)), R(vb, vz)))


# @livre Ch.III §1.10 Def.7 | E III.13 L.9-13 | PDF p.120  (le témoin canonique du majorant commun EST un majorant des deux, dans J — sans axiome du choix)
def temoin_majorant_commun(jj="J", i="I", a="ai", b="bi", R=None,
                           x="x", y="y", z="z"):
    """{ J filtrante à droite dans I, λ∈J, μ∈J }
        ⊢ ( (ν(λ,μ) ∈ J et λ ≤ ν(λ,μ)) et μ ≤ ν(λ,μ) ).              [3 hyps].

    C'est le δ que réclame `prolongement_bien_defini` : le majorant COMMUN de
    deux indices, dont Bourbaki dit « il existe une valeur commune ν telle que
    ν ≥ λ et ν ≥ μ » (E III.55, démonstration de la Prop. 3).  Tant qu'il reste
    une variable libre, les dix hypothèses du prolongement qui le mentionnent ne
    peuvent pas être déchargées ; sous forme de témoin CANONIQUE, elles le
    peuvent.

    Même schéma que `temoin_cofinal` : la filtrance instanciée en (λ,μ) donne
    l'existentielle, `existe_temoin` la transfère au τ."""
    if R is None:
        R = _R_gleq()
    vJ, vi = _t(jj), _t(i)
    va, vb = _t(a), _t(b)
    h_filt = N.assume(est_partie_filtrante_droite(R, vJ, vi, x, y, z))
    h_a = N.assume(appartient(va, vJ))
    h_b = N.assume(appartient(vb, vJ))
    coeur = conjonction_elim_droite(h_filt)      # (∀x)(∀y)((x,y∈J) ⇒ (∃z)(…))
    ex = N.modus_ponens(conjonction_intro(h_a, h_b),
                        instancie(instancie(coeur, va), vb))
    vz = var(z)
    corps = et(et(appartient(vz, vJ), R(va, vz)), R(vb, vz))
    res = N.modus_ponens(ex, N.existe_temoin(corps, z))
    nu = nu_majorant_commun(vJ, va, vb, R, z)
    assert res.conclusion == et(et(appartient(nu, vJ), R(va, nu)), R(vb, nu)), \
        "temoin_majorant_commun : ≠ ((ν∈J et λ≤ν) et μ≤ν)"
    assert len(res.hypotheses) == 3, \
        f"temoin_majorant_commun : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


__all__ = ["beta_cofinal", "temoin_cofinal", "nu_majorant_commun",
           "temoin_majorant_commun"]
