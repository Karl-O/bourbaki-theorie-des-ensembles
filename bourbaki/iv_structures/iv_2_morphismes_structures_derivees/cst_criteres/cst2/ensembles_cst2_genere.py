"""§IV.1.2 — CST2 GÉNÉRÉ : ⟨f₁,…⟩^S_réel est une bijection de S(E) sur S(E').

────────────────────────────────────────────────────────────────────────────────
LE MÉTATHÉORÈME (générateur Python, jamais un Theoreme du schéma-en-général) :
pour chaque schéma concret S et familles f_i, si chaque f_i est une bijection
de E_i sur E'_i (au vocabulaire Q, hypothèses honnêtes), alors

    cst2_prouve(s, fs, bases, bases_p)  ⊢  Q(⟨f⟩^S_réel, S(E), S(E'))

par récurrence sur les couples de S : (0,b) = l'hypothèse Q(f_b) ; (a,0) =
ext_parties_bijective_q coupée par l'IH ; (a,b) = produit_app_bijective_q
coupée par les 2 IH.  Les seules hypothèses résiduelles = les n Q(f_i).
`pont_bijection_de` traduit Q au vocabulaire du livre (E III.3.1 Déf. 1) :
est_bijection_de(F,X,Y), l'injectivité gardée dérivée de func F⁻¹ + dom.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst2_briques import (
    bijection_q, ext_parties_bijective_q,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_etage_produit import (
    produit_app_bijective_q, _inj_point,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _q_conjoints(thm_q):
    """Les 4 conjoints (func, dom, func⁻¹, img) d'un thm ⊢ Q(F,X,Y)."""
    c12, c34 = conjonction_elim_gauche(thm_q), conjonction_elim_droite(thm_q)
    return (conjonction_elim_gauche(c12), conjonction_elim_droite(c12),
            conjonction_elim_gauche(c34), conjonction_elim_droite(c34))


# @livre Ch.IV §1.2 Crit.CST2 | E IV.2 L.33-34 | PDF p.205  (CST2 : un schéma d'échelon appliqué à des bijections donne une bijection — GÉNÉRÉ par récurrence sur le schéma concret)
def cst2_prouve(s: Schema, fs: Sequence, bases: Sequence, bases_p: Sequence,
                xg: str = "xg"):
    """(thm, hyps) : thm ⊢ Q(⟨f⟩^S_réel, S(E), S(E')) ; hyps = les n Q(f_i)."""
    fs_t = [_t(x) for x in fs]
    A = construction_echelon(s, [_t(b) for b in bases])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    G = extension_canonique_reelle(s, fs_t, bases, xg)

    thms: list = []
    hyps: list = []
    for i, (a, b) in enumerate(s.couples):
        xi = f"{xg}{i + 1}"
        if a == 0:
            q = bijection_q(fs_t[b - 1], _t(bases[b - 1]), _t(bases_p[b - 1]))
            hyps.append(q)
            thms.append(N.assume(q))
        elif b == 0:
            ih = thms[a - 1]
            etage = ext_parties_bijective_q(G[a - 1], A[a - 1], Ap[a - 1], xi)
            thms.append(_cut(etage, *_q_conjoints(ih)))
        else:
            ih_a, ih_b = thms[a - 1], thms[b - 1]
            etage = produit_app_bijective_q(G[a - 1], G[b - 1],
                                            A[a - 1], A[b - 1],
                                            Ap[a - 1], Ap[b - 1], xi)
            thms.append(_cut(etage, *_q_conjoints(ih_a), *_q_conjoints(ih_b)))
    res = thms[-1]
    assert res.conclusion == bijection_q(G[-1], A[-1], Ap[-1]), \
        "cst2_prouve : conclusion ≠ Q(⟨f⟩^S, S(E), S(E'))"
    assert set(res.hypotheses) <= set(hyps), "cst2_prouve : hyps non répertoriées"
    return res, sorted(set(hyps), key=str)


# @livre Ch.III §3.1 Def.1 | E III.23 L.15-17 | PDF p.126  (pont Q → est_bijection_de : l'injectivité gardée dérivée de « F⁻¹ fonctionnel » + dom)
def pont_bijection_de(thm_q, F, X, Y):
    """De thm ⊢ Q(F,X,Y), déduire ⊢ est_bijection_de(F,X,Y) (mêmes hyps).

    injective_dans(F,X) : u,u'∈X ∧ F(u)=F(u') ⇒ u=u' par _inj_point (couples
    (u,F(u))∈F depuis dom, univalence de F⁻¹) — cœur aux noms ub/wb puis
    re-liage u/up (relais-α)."""
    F, X, Y = _t(F), _t(X), _t(Y)
    func, dom, rec, img = _q_conjoints(thm_q)
    corps = et(et(appartient(var("ub"), X), appartient(var("wb"), X)),
               egal(E.valeur(F, var("ub")), E.valeur(F, var("wb"))))
    h = N.assume(corps)
    u_X = conjonction_elim_gauche(conjonction_elim_gauche(h))
    w_X = conjonction_elim_droite(conjonction_elim_gauche(h))
    eq = conjonction_elim_droite(h)
    u_eq_w = _inj_point(F, X, dom, rec, u_X, w_X, eq, var("ub"), var("wb"))
    core = N.loi_deduction(corps, u_eq_w)
    gen = N.generalisation("ub", N.generalisation("wb", core))
    re = instancie(instancie(gen, var("u")), var("up"))
    inj = N.generalisation("u", N.generalisation("up", re))
    assert inj.conclusion == E.injective_dans(F, X), "pont : ≠ injective_dans"
    res = conjonction_intro(conjonction_intro(func, dom),
                            conjonction_intro(inj, img))
    assert res.conclusion == est_bijection_de(F, X, Y), "pont : ≠ est_bijection_de"
    return res


__all__ = ["cst2_prouve", "pont_bijection_de"]
