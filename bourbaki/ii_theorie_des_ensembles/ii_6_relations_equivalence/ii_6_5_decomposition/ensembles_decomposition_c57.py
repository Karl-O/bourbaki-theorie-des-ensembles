"""§II.6.5 — TOUTE application se factorise par son quotient (C57 appliqué à R_f).

────────────────────────────────────────────────────────────────────────────────
Conséquence immédiate de C57 (ensembles_c57_passage_quotient) une fois pris
pour R la relation associée à f elle-même :

    R_f{x,y}  :=  (x∈E et y∈E) et f(x) = f(y)

  • `compatible_avec_R_associee` ⊢ f est compatible avec R_f          [CLOS]
    — c'est une TAUTOLOGIE (R_f contient déjà l'égalité des valeurs), et
    c'est ce qui rend la décomposition canonique inconditionnelle ;
  • `factorisation_universelle` { p caractérise R_f SUR E, x∈E, p(x)∈Q }
        ⊢ H( p(x) ) = f(x),   H = graphe_deduit(f, p, Q, E)   [3 hyps]
    — « toute application f se factorise à travers le quotient de E par la
    relation qu'elle induit », avec H CONSTRUIT (pas postulé).

C'est le pont réclamé par `ensembles_decomposition_effective` :
b_injective_via_pont conditionne l'injectivité de b à « b(Cl(x)) = f(x) » —
hypothèse fournie par la conclusion ci-dessus (avec b := H), MODULO le liant
de valeur (_vb/_vf y sont α-distincts de « y », cf. PASSATION).
⚠️ TOUTES les hypothèses de quotient sont GARDÉES PAR E depuis le 4 août 2026 :
sans garde, « p(x)=p(y) ⇔ R{x,y} » est INSATISFIABLE (hors du domaine, S7
identifie tous les p(x)) et rendrait ces théorèmes VACUEUX.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_c57_passage_quotient import (
    hyp_compatible, c57_application_deduite, graphe_deduit,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.II §6.5 Def.- | E II.44 L.28-32 | PDF p.95  (relation associée à f : « x ≡ y » ⇔ f(x)=f(y), sur E)
def R_associee(f, e):
    """R_f{x,y} := (x∈E et y∈E) et f(x)=f(y)  — la relation induite par f."""
    vf, vE = _t(f), _t(e)
    return lambda x, y: et(et(appartient(x, vE), appartient(y, vE)),
                           egal(E.valeur(vf, x), E.valeur(vf, y)))


# @livre Ch.II §6.5 Prop.- | E II.44 L.28-32 | PDF p.95  (f est compatible avec la relation qu'elle induit — tautologie, mais c'est elle qui rend la décomposition canonique inconditionnelle)
def compatible_avec_R_associee(f="f", e="Eq", x="xq", y="yq"):
    """⊢ f est compatible avec R_f.                              [CLOS, 0 hyp]."""
    vf, vE = _t(f), _t(e)
    R = R_associee(vf, vE)
    vx, vy = var(x), var(y)
    h = N.assume(R(vx, vy))
    res = N.generalisation(x, N.generalisation(
        y, N.loi_deduction(R(vx, vy), conjonction_elim_droite(h))))
    assert res.conclusion == hyp_compatible(vf, R, x, y), \
        "compatible_avec_R_associee : ≠ hyp_compatible"
    assert not res.hypotheses, "compatible_avec_R_associee : NON clos"
    return res


# @livre Ch.II §6.5 Crit.C57 | E II.44 L.22-27 | PDF p.95  (toute application se factorise à travers le quotient par la relation qu'elle induit — C57 + compatibilité tautologique)
def factorisation_universelle(f="f", p="P", e="Eq", quot="Q", x="xq",
                              t="t", z="zq"):
    """{ p caractérise R_f SUR E, x∈E, p(x)∈Q } ⊢ H( p(x) ) = f(x).   [3 hyps].

    La compatibilité, 3ᵉ hypothèse de C57, est ICI DÉCHARGÉE (tautologique
    pour R_f) : toute application se factorise par son quotient, H étant le
    graphe CONSTRUIT par le témoin canonique."""
    vf, vp, vE, vQ = _t(f), _t(p), _t(e), _t(quot)
    R = R_associee(vf, vE)
    res = _cut(c57_application_deduite(vf, vp, vQ, vE, R, x, t, z),
               compatible_avec_R_associee(vf, vE, x, "yq"))
    cible = egal(E.valeur(graphe_deduit(vf, vp, vQ, vE, t, z),
                          E.valeur(vp, var(x))), E.valeur(vf, var(x)))
    assert res.conclusion == cible, "factorisation_universelle : ≠ H(p(x))=f(x)"
    assert len(res.hypotheses) == 3, "factorisation_universelle : hyps ≠ 3"
    return res


__all__ = ["R_associee", "compatible_avec_R_associee", "factorisation_universelle"]
