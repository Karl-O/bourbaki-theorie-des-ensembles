"""§IV.1.2 — CST3 GÉNÉRÉ : la réciproque de l'extension canonique.

────────────────────────────────────────────────────────────────────────────────
LE MÉTATHÉORÈME (générateur Python) : pour chaque schéma concret S, si chaque
f_i est une bijection de E_i sur E'_i (vocabulaire Q, hyps honnêtes), alors

    cst3_prouve(s, fs, bases, bases_p)
        ⊢  reciproque(⟨f₁,…⟩^S_réel)  =  ⟨f₁⁻¹,…⟩^S_réel

(l'extension des réciproques est construite SUR LES BASES D'ARRIVÉE E'_i).
Récurrence à DOUBLE FIL : qs[i] ⊢ Q(G_i, A_i, A'_i) (comme cst2_prouve, les
étages coupés par l'IH-Q) et rs[i] ⊢ reciproque(G_i) = G'_i (étages
reciproque_ext_parties / reciproque_produit_app coupés par l'IH-Q, puis
congruence-IH-dans-trou comme cst1 pour remplacer reciproque(G_a) par G'_a
DANS le terme de l'étage suivant).  Hyps résiduelles = les n Q(f_i).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
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
    produit_app_bijective_q,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_genere import (
    _q_conjoints,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_parties import (
    reciproque_ext_parties,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_produit import (
    reciproque_produit_app,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.IV §1.2 Crit.CST3 | E IV.2 L.35-37 | PDF p.205  (CST3 : la réciproque de l'extension canonique de bijections est l'extension canonique des réciproques — GÉNÉRÉ par récurrence sur le schéma concret)
def cst3_prouve(s: Schema, fs: Sequence, bases: Sequence, bases_p: Sequence,
                xg: str = "xg"):
    """(thm, hyps) : thm ⊢ reciproque(⟨f⟩^S) = ⟨f⁻¹⟩^S ; hyps = les n Q(f_i)."""
    fs_t = [_t(x) for x in fs]
    fsp = [E.reciproque(f) for f in fs_t]
    A = construction_echelon(s, [_t(b) for b in bases])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    G = extension_canonique_reelle(s, fs_t, bases, xg)
    Gp = extension_canonique_reelle(s, fsp, bases_p, xg)

    qs: list = []
    rs: list = []
    hyps: list = []
    for i, (a, b) in enumerate(s.couples):
        xi = f"{xg}{i + 1}"
        if a == 0:
            q = bijection_q(fs_t[b - 1], _t(bases[b - 1]), _t(bases_p[b - 1]))
            hyps.append(q)
            qs.append(N.assume(q))
            rs.append(N.reflexivite(E.reciproque(fs_t[b - 1])))
        elif b == 0:
            ihq = _q_conjoints(qs[a - 1])
            qs.append(_cut(ext_parties_bijective_q(
                G[a - 1], A[a - 1], Ap[a - 1], xi), *ihq))
            st = _cut(reciproque_ext_parties(
                G[a - 1], A[a - 1], Ap[a - 1], xi), *ihq)
            trou = E.graphe_terme(E.parties(Ap[a - 1]),
                                  E.image(var("w"), var(xi)), xi)
            cong = N.modus_ponens(rs[a - 1], congruence_terme(
                E.reciproque(G[a - 1]), Gp[a - 1], trou))
            rs.append(composer_egalites(st, cong))
        else:
            ihq = (*_q_conjoints(qs[a - 1]), *_q_conjoints(qs[b - 1]))
            qs.append(_cut(produit_app_bijective_q(
                G[a - 1], G[b - 1], A[a - 1], A[b - 1],
                Ap[a - 1], Ap[b - 1], xi), *ihq))
            st = _cut(reciproque_produit_app(
                G[a - 1], G[b - 1], A[a - 1], A[b - 1],
                Ap[a - 1], Ap[b - 1], xi), *ihq)
            ApxBp = E.produit(Ap[a - 1], Ap[b - 1])
            trou_a = E.graphe_terme(ApxBp, E.couple(
                E.valeur(var("w"), E.pr1(var(xi))),
                E.valeur(E.reciproque(G[b - 1]), E.pr2(var(xi)))), xi)
            cong_a = N.modus_ponens(rs[a - 1], congruence_terme(
                E.reciproque(G[a - 1]), Gp[a - 1], trou_a))
            trou_b = E.graphe_terme(ApxBp, E.couple(
                E.valeur(Gp[a - 1], E.pr1(var(xi))),
                E.valeur(var("w"), E.pr2(var(xi)))), xi)
            cong_b = N.modus_ponens(rs[b - 1], congruence_terme(
                E.reciproque(G[b - 1]), Gp[b - 1], trou_b))
            rs.append(composer_egalites(st,
                                        composer_egalites(cong_a, cong_b)))
    res = rs[-1]
    cible = egal(E.reciproque(G[-1]), Gp[-1])
    assert res.conclusion == cible, "cst3_prouve : ≠ reciproque(⟨f⟩^S)=⟨f⁻¹⟩^S"
    assert set(res.hypotheses) <= set(hyps), "cst3_prouve : hyps non répertoriées"
    return res, sorted(set(hyps), key=str)


__all__ = ["cst3_prouve"]
