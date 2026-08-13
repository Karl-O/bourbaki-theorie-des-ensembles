"""§IV.1.2 — CST1 GÉNÉRÉ : la fonctorialité de l'extension canonique, PAR SCHÉMA.

────────────────────────────────────────────────────────────────────────────────
LE MÉTATHÉORÈME (au sens du projet : un GÉNÉRATEUR Python, jamais un Theoreme
du schéma-en-général).  Pour CHAQUE schéma concret S (objet méta `Schema`,
especes_echelon) et familles f_i : E_i→E'_i, g_i : E'_i→E''_i, le générateur
produit le Theoreme noyau :

    ⟨g₁∘f₁,…⟩^S_réel  =  ⟨g₁,…⟩^S_réel ∘ ⟨f₁,…⟩^S_réel      (CST1, E IV.2)

par récurrence Python sur les couples de S :
  • cas (0,b) : les deux membres sont LITTÉRALEMENT g_b∘f_b — réflexivité ;
  • cas (a,0) : congruence de l'IH dans l'argument du graphe (trou w DANS le
    terme image(·,xg)) puis fonctorialite_parties_termes (B3) ;
  • cas (a,b) : deux congruences (arguments gauche/droit) puis
    fonctorialite_produit_termes (F2-termes).
Les hypothèses honnêtes s'ACCUMULENT par étage (bornes-image des cas 𝔓,
est_application des cas ×) et sont RETOURNÉES listées : (thm, hyps).
`extension_canonique_reelle` est la récurrence-miroir d'especes_echelon sur les
constructions RÉELLES (T1) — les domaines par étage viennent de
construction_echelon.  INVARIANT : theorie_ensembles()=22 ; rien postulé.
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
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    ext_parties_reelle, produit_app_reelle,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
    fonctorialite_parties_termes,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonctorialite_produit_termes import (
    fonctorialite_produit_termes,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.IV §1.2 Def.- | E IV.2 L.13-28 | PDF p.205  (extension canonique ⟨f₁,…,fₙ⟩^S — récurrence RÉELLE, briques T1 non opaques)
def extension_canonique_reelle(s: Schema, applis: Sequence, bases: Sequence,
                               xg: str = "xg") -> list:
    """La liste [G_1,…,G_m] des extensions RÉELLES par étage (IV.1.2, briques T1).

    `bases` = les ensembles de DÉPART E_i (les domaines par étage viennent de
    construction_echelon(s, bases))."""
    A = construction_echelon(s, [_t(b) for b in bases])
    G: list = []
    for i, (a, b) in enumerate(s.couples, start=1):
        xi = f"{xg}{i}"          # UNE variable-convention PAR ÉTAGE (les graphes
        if a == 0:               # imbriqués partagent sinon xg et la substitution
            G.append(_t(applis[b - 1]))      # externe corromprait les internes)
        elif b == 0:
            G.append(ext_parties_reelle(G[a - 1], A[a - 1], xi))
        else:
            G.append(produit_app_reelle(G[a - 1], G[b - 1],
                                        A[a - 1], A[b - 1], xi))
    if not G:
        raise ValueError("schéma vide")
    return G


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (CST1 : ⟨g∘f⟩^S = ⟨g⟩^S ∘ ⟨f⟩^S — GÉNÉRÉ par récurrence sur le schéma concret, un Theoreme noyau par instance)
def cst1_termes_prouve(s: Schema, fs: Sequence, gs: Sequence,
                       bases: Sequence, bases_p: Sequence, bases_pp: Sequence,
                       xg: str = "xg"):
    """(thm, hyps) : thm ⊢ C_m = composee(Gg_m, Gf_m) pour le schéma CONCRET s,
    où C/Gf/Gg = extensions réelles des familles (g∘f)/f/g ; hyps = les
    hypothèses honnêtes ACCUMULÉES (bornes-image 𝔓, est_application ×)."""
    fs_t = [_t(x) for x in fs]
    gs_t = [_t(x) for x in gs]
    comps = [E.composee(g, f) for g, f in zip(gs_t, fs_t)]
    A = construction_echelon(s, [_t(b) for b in bases])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    App = construction_echelon(s, [_t(b) for b in bases_pp])
    C = extension_canonique_reelle(s, comps, bases, xg)
    Gf = extension_canonique_reelle(s, fs_t, bases, xg)
    Gg = extension_canonique_reelle(s, gs_t, bases_p, xg)

    thms: list = []          # thms[i] ⊢ C[i] = composee(Gg[i], Gf[i])
    hyps: list = []
    for i, (a, b) in enumerate(s.couples):
        xi = f"{xg}{i + 1}"                  # la variable-convention de CET étage
        if a == 0:
            # C[i] = composee(g_b, f_b) LITTÉRAL = composee(Gg[i], Gf[i]).
            thms.append(N.reflexivite(C[i]))
        elif b == 0:
            ih = thms[a - 1]
            K = E.composee(Gg[a - 1], Gf[a - 1])
            # congruence de l'IH DANS l'argument du graphe (trou w dans le terme)
            trou = E.graphe_terme(E.parties(A[a - 1]),
                                  E.image(var("w"), var(xi)), xi)
            cong = N.modus_ponens(ih, congruence_terme(C[a - 1], K, trou))
            #    ext_P(C_a) = ext_P(K)
            f1t = fonctorialite_parties_termes(Gf[a - 1], Gg[a - 1],
                                               A[a - 1], Ap[a - 1], xi)
            #    ext_P(K) = composee(ext_P(Gg_a), ext_P(Gf_a)) = composee(Gg[i], Gf[i])
            hyps.extend(f1t.hypotheses)
            thms.append(composer_egalites(cong, f1t))
        else:
            ih_a, ih_b = thms[a - 1], thms[b - 1]
            Ka = E.composee(Gg[a - 1], Gf[a - 1])
            Kb = E.composee(Gg[b - 1], Gf[b - 1])
            AxB = E.produit(A[a - 1], A[b - 1])
            trou_a = E.graphe_terme(AxB, E.couple(
                E.valeur(var("w"), E.pr1(var(xi))),
                E.valeur(C[b - 1], E.pr2(var(xi)))), xi)
            cong_a = N.modus_ponens(ih_a, congruence_terme(C[a - 1], Ka, trou_a))
            trou_b = E.graphe_terme(AxB, E.couple(
                E.valeur(Ka, E.pr1(var(xi))),
                E.valeur(var("w"), E.pr2(var(xi)))), xi)
            cong_b = N.modus_ponens(ih_b, congruence_terme(C[b - 1], Kb, trou_b))
            cong = composer_egalites(cong_a, cong_b)
            #    prod(C_a, C_b) = prod(Ka, Kb)
            f2t = fonctorialite_produit_termes(
                Gf[a - 1], Gg[a - 1], Gf[b - 1], Gg[b - 1],
                A[a - 1], Ap[a - 1], App[a - 1],
                A[b - 1], Ap[b - 1], App[b - 1], xi)
            hyps.extend(f2t.hypotheses)
            thms.append(composer_egalites(cong, f2t))
    res = thms[-1]
    cible = egal(C[-1], E.composee(Gg[-1], Gf[-1]))
    assert res.conclusion == cible, "cst1_termes_prouve : conclusion ≠ CST1(s)"
    assert set(res.hypotheses) <= set(hyps) | set(), \
        "cst1_termes_prouve : hypothèses non répertoriées"
    return res, sorted(set(hyps), key=str)


__all__ = ["extension_canonique_reelle", "cst1_termes_prouve"]
