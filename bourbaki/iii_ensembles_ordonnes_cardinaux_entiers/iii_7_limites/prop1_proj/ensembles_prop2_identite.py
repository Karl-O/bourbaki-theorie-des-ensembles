"""§III.7.2 Prop. 2, 2ᵉ assertion — vers l'identité u⁻¹(x') = lim← M_α.

────────────────────────────────────────────────────────────────────────────────
`ensembles_prop2_fibres` a livré le CŒUR : `fibres_partout` établit

    (∀α)(α∈I ⇒ pr_α z ∈ M_α)   ⇔   (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α)

sous deux hypothèses de contexte.  Ce module transforme le membre GAUCHE en une
appartenance d'ensemble — « z ∈ lim← M_α » — ce qui est la moitié de l'identité
visée.

LE POINT QUI FAIT TOUT.  La condition (1) d'une limite projective ne dépend que
de **f, ≤ et I** — jamais de la famille d'ensembles.  Les deux membres de
l'identité vivent donc au-dessus de LA MÊME condition (1), et il n'y a pas à la
démontrer deux fois : elle se lit une fois sur « z ∈ lim←_I » et se réutilise
telle quelle pour « z ∈ lim← M_α ».  C'est ce qui rend l'assemblage court.

CE QUI EST GRATUIT, ET CE QUI NE L'EST PAS.  L'appartenance au produit des
fibres demande quatre clauses.  Trois se lisent sur z ∈ lim←_I sans rien coûter :
`est_un_graphe` (par `point_limite_est_graphe`), `est_fonctionnel` et
`dom z = I` (par la caractérisation du produit sur E).  ⚠️ Contrairement aux
chantiers voisins, **z n'est pas un objet CONSTRUIT** : ces trois clauses ne sont
donc pas closes, elles sont *déduites* de l'appartenance à la limite — ce qui
revient au même ici, mais pour une raison différente.  Seule la quatrième, la
clause des VALEURS, porte le contenu : c'est exactement le membre gauche de
`fibres_partout`.

INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (
    porter_aux_termes,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    membre_produit_famille,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    pivot_inclusion_produit, hypothese_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
    _lim_dans_produit, _gleq,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_lim_graphe import (
    point_limite_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
    famille_fibres, fibres_partout,
)

#: liant de la clause des valeurs — celui de l'axiome du produit (cf. pièges).
_IDX = "i"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        if p.conclusion in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(p.conclusion, thm))
    return thm


def _clauses_du_point(Efam, f, leq, i, vz):
    """Les trois clauses de bonne formation de z, lues sur « z ∈ lim←_I ».

    Rend (est_un_graphe(z), est_fonctionnel(z), dom z = I), chacune sous la
    seule hypothèse « z ∈ lim←_I »."""
    h_z = N.assume(appartient(vz, L.lim_proj(_t(Efam), _t(f))))
    gr = point_limite_est_graphe(Efam, f, leq, i, vz, h_z)
    quatre = N.modus_ponens(
        _lim_dans_produit(Efam, f, leq, i, vz, h_z),
        equivalence_avant(porter_aux_termes(membre_produit_famille(
            Efam if isinstance(Efam, str) else "E",
            i if isinstance(i, str) else "I", "Fz"), {"Fz": vz})))
    gauche = conjonction_elim_gauche(quatre)
    return gr, conjonction_elim_droite(conjonction_elim_gauche(gauche)), \
        conjonction_elim_droite(gauche)


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (z appartient au produit des FIBRES dès que ses coordonnées y sont — les trois autres clauses se lisent sur z ∈ lim←_I)
def point_dans_produit_fibres(u="uf", xp="xp", Efam="E", f="f", i="I",
                              liant="k", z="zf", idx=_IDX, leq=None):
    """{ z ∈ lim←_I,  (∀ι)(ι∈I ⇒ pr_ι z ∈ M_ι) } ⊢ z ∈ ∏_{α∈I} M_α.    [2 hyps].

    Les trois clauses de bonne formation viennent de « z ∈ lim←_I » ; la
    quatrième est l'hypothèse, et c'est le membre gauche de `fibres_partout`."""
    if leq is None:
        leq = _gleq()
    vI, vz = _t(i), _t(z)
    M = famille_fibres(u, xp, i, liant)
    gr, fn, dm = _clauses_du_point(Efam, f, leq, i, vz)
    h_vals = N.assume(hypothese_valeurs(M, vI, idx, vz))
    incl = _cut(pivot_inclusion_produit(vz, M, vI, idx), gr, fn, dm)
    carac = porter_aux_termes(
        membre_produit_famille("Mfam", i if isinstance(i, str) else "I", "Fz"),
        {"Mfam": M, "Fz": vz})
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(incl, fn), dm), h_vals), equivalence_arriere(carac))
    assert res.conclusion == appartient(vz, E.produit_famille(M, vI)), \
        "point_dans_produit_fibres : ≠ (z ∈ ∏_{α∈I} M_α)"
    assert len(res.hypotheses) == 2, \
        f"point_dans_produit_fibres : hyps ≠ 2 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (z ∈ lim← M_α : la condition (1) est LA MÊME que pour lim←_I, donc elle se réutilise telle quelle)
def point_dans_limite_fibres(u="uf", xp="xp", Efam="E", f="f", i="I",
                             liant="k", z="zf", idx=_IDX, leq=None):
    """{ z ∈ lim←_I,  (∀ι)(ι∈I ⇒ pr_ι z ∈ M_ι) } ⊢ z ∈ lim← M_α.       [2 hyps].

    La caractérisation de la limite réclame l'appartenance au produit — c'est
    `point_dans_produit_fibres` — et la condition (1).  Or **la condition (1) ne
    dépend que de f, ≤ et I** : celle du système des fibres est littéralement la
    même formule que celle du système de départ.  On la lit donc sur
    « z ∈ lim←_I » et on la réutilise, au lieu de la redémontrer.

    C'est la moitié GAUCHE de l'identité u⁻¹(x') = lim← M_α."""
    if leq is None:
        leq = _gleq()
    vI, vz = _t(i), _t(z)
    M = famille_fibres(u, xp, i, liant)
    prod = point_dans_produit_fibres(u, xp, Efam, f, i, liant, z, idx, leq)
    # la condition (1), lue une seule fois sur z ∈ lim←_I
    cond = conjonction_elim_droite(N.modus_ponens(
        N.assume(appartient(vz, L.lim_proj(_t(Efam), _t(f)))),
        equivalence_avant(L.appartient_limite_projective(Efam, f, leq, i, z))))
    ax = N.axiome(L.theorie_lim_proj(M, _t(f), leq, vI),
                  L.axiome_lim_proj(M, _t(f), leq, vI))
    res = N.modus_ponens(conjonction_intro(prod, cond),
                         equivalence_arriere(instancie(ax, vz)))
    assert res.conclusion == appartient(vz, L.lim_proj(M, _t(f))), \
        "point_dans_limite_fibres : ≠ (z ∈ lim← M_α)"
    assert len(res.hypotheses) == 2, \
        f"point_dans_limite_fibres : hyps ≠ 2 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (👑 la moitié GAUCHE de l'identité, branchée sur le côté u : « u(z) a les coordonnées de x' » ⟹ « z ∈ lim← M_α »)
def point_dans_limite_depuis_u(u="uf", xp="xp", Efam="E", f="f", i="I",
                               liant="k", z="zf", idx=_IDX, t="tz",
                               EfamF="Ep", fF="fp", leq=None):
    """{ famille des u_α fonctionnels et totaux,  z ∈ lim←_I,
         (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) }  ⊢  z ∈ lim← M_α.             [3 hyps].

    👑 LA MOITIÉ GAUCHE de l'identité u⁻¹(x') = lim← M_α, exprimée avec ce que
    donne réellement « u(z) = x' » : ses coordonnées.

    `fibres_partout` convertit l'hypothèse sur les coordonnées de u(z) en la
    clause des valeurs sur les fibres, et `point_dans_limite_fibres` en tire
    l'appartenance à la limite.  Les deux se branchent exactement parce que le
    membre gauche de la première EST la clause qu'attend la seconde — vérifié
    par assertion, pas supposé."""
    fp = fibres_partout(u, xp, i, liant, idx, z, t, Efam, f, EfamF, fF, leq)
    vals = N.modus_ponens(N.assume(_droite_de_equiv(fp.conclusion)),
                          equivalence_arriere(fp))
    base = point_dans_limite_fibres(u, xp, Efam, f, i, liant, z, idx, leq)
    res = _cut(base, vals)
    assert len(res.hypotheses) == 3, \
        f"point_dans_limite_depuis_u : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


def _droite_de_equiv(f):
    """Le membre DROIT d'un `equiv(A, B)` — équiv = et(A⇒B, B⇒A), et l'encodage
    ¬∨¬ impose de dépiler avec soin (cf. le piège des trois niveaux)."""
    return f.sous[0].sous[0].sous[0].sous[1]


REPORTES = [
    "IDENTITÉ u⁻¹(x') = lim← M_α — moitié GAUCHE acquise "
    "(`point_dans_limite_fibres` : de « les coordonnées sont dans les fibres » à "
    "« z ∈ lim← M_α », 2 hypothèses).  RESTE le côté DROIT : passer de "
    "« u(z) = x' » à « (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) », c'est-à-dire "
    "l'EXTENSIONNALITÉ du produit sur E' — il faut u(z) et x' dans ∏E'_α et "
    "tous deux graphes.  `membre_fibre` donne déjà "
    "z ∈ u⁻¹⟨{x'}⟩ ⇔ u(z) = x'.  Puis la double inclusion et "
    "`extensionnalite_appliquee` closent l'identité.",
]

__all__ = ["point_dans_produit_fibres", "point_dans_limite_fibres",
           "point_dans_limite_depuis_u", "REPORTES"]
