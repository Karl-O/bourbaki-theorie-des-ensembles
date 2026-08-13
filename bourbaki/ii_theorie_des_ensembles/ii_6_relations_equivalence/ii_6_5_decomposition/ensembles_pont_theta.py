"""§II.6.5 — le PONT b(Cl(x)) = f(x) est DÉMONTRÉ : b est construit, plus supposé.

────────────────────────────────────────────────────────────────────────────────
`ensembles_decomposition_effective` prouve l'injectivité de la bijection
induite b SOUS l'hypothèse du PONT « (∀x)(x∈E ⇒ b(θ(x)) = f(x)) »
(pont_valeurs_b), et `ensembles_decomposition_bijection` en fait autant pour
la surjectivité.  Ce pont était une HYPOTHÈSE : il est ici DÉMONTRÉ, pour un b
CONSTRUIT — ce qui décharge ces théorèmes.

    b_theta(f, Q) := graphe_terme( Q, f(t), t )          (kit C54)

  { x ∈ E,  θ(x) ∈ Q }  ⊢  b_theta( θ(x) )  =  f(x)              [pont_au_point]
  { θ⟨E⟩ ⊂ Q }          ⊢  (∀x)( x∈E ⇒ b_theta(θ(x)) = f(x) )    [pont_valeurs_b]

POURQUOI AUCUNE SECTION N'EST NÉCESSAIRE (route trouvée par la cartographie du
4 août) : avec le codage « classe d'objets » θ(x)=τ_w(R_f{x,w}), **la classe
est son propre représentant** — `theta_temoin` donne θ(x)∈E ET f(x)=f(θ(x)).
Il suffit donc d'évaluer f EN LA CLASSE : b_theta(θ(x)) = f(θ(x)) = f(x).
Ni témoin canonique, ni caractérisation du quotient (dont l'hypothèse gardée
serait à fournir), ni axiome du choix.

⚠️ LIANTS : le kit C54 produit ses valeurs au liant « y » ; les modules de
décomposition utilisent les liants frais `_VF`/`_VB` (E.valeur(·,·,b=…)).  Le
raccord passe par `N.alpha_tau` — ce qui EXIGE des liants α-valides (lettres
simples) : `_VF`/`_VB` valaient « _vf »/« _vb », refusés par alpha_tau, et ont
été portés à « q »/« r » (4 août, 126 tests ii_6 verts avant/après).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_effective import (
    classe_objets_Rf, pont_valeurs_b, _valf, _valb, _VB,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_theta_caracterise import (
    theta_temoin,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §6.5 Def.- | E II.44 L.22-22 | PDF p.95  (l'application déduite b : E/R_f → F, CONSTRUITE — b(t) := f(t), la classe étant son propre représentant)
def b_theta(f, quot, t="t"):
    """b := graphe_terme( Q, f(t), t )  — l'application déduite, sans section."""
    return E.graphe_terme(_t(quot), _valf(_t(f), var(t)), t)


def _valeur_kit_vers_vb(b_t, point):
    """⊢ valeur(b, point) [liant « y », produit par le kit] = b(point) [liant _VB].

    α-renommage du τ de valeur : c'est ici que le choix d'un liant α-VALIDE
    pour `_VB` est indispensable (alpha_tau refuse « _vb »)."""
    R = appartient(E.couple(_t(point), var("y")), _t(b_t))
    return N.alpha_tau(R, "y", _VB)


# @livre Ch.II §6.5 Prop.- | E II.44 L.22-27 | PDF p.95  (le PONT au point : l'application déduite construite prend en la classe de x la valeur f(x))
def pont_au_point(f="f", quot="Q", e=None, x="x", w="w", t="t"):
    """{ x∈E, θ(x)∈Q } ⊢ b_theta(θ(x)) = f(x).                     [2 hyps].

    b_theta(θ(x)) = f(θ(x))  [kit C54, relais nom→terme « ptq »]
                  = f(x)     [theta_temoin : la classe est son représentant]."""
    vf, vQ, vx = _t(f), _t(quot), _t(x)
    ve = E.dom(vf) if e is None else _t(e)
    B = b_theta(vf, vQ, t)
    tx = classe_objets_Rf(vf, vx, e=ve, w=w)
    h_tx = N.assume(appartient(tx, vQ))

    # (1) kit C54 au NOM « ptq » puis relais noms→termes (le point θ(x) est un τ)
    val_nom = graphe_terme_valeur(vQ, _valf(vf, var(t)), "ptq", t, "y")
    gen = N.generalisation("ptq", N.loi_deduction(
        appartient(var("ptq"), vQ), val_nom))
    val = N.modus_ponens(h_tx, instancie(gen, tx))     # valeur_kit(B, θx) = f(θx)
    # (2) α : la valeur produite par le kit (liant « y ») EST b(θx) (liant _VB)
    conv = _valeur_kit_vers_vb(B, tx)                  # valeur_kit = _valb
    # (3) f(θ(x)) = f(x)  — theta_temoin (conjoint droit, symétrisé)
    fx_ftx = conjonction_elim_droite(theta_temoin(vf, ve, vx, w))
    res = composer_egalites(composer_egalites(
        N.modus_ponens(conv, symetrie(E.valeur(B, tx), _valb(B, tx))), val),
        N.modus_ponens(fx_ftx, symetrie(_valf(vf, vx), _valf(vf, tx))))
    assert res.conclusion == egal(_valb(B, tx), _valf(vf, vx)), \
        "pont_au_point : ≠ b(θ(x)) = f(x)"
    assert len(res.hypotheses) == 2, "pont_au_point : hyps ≠ 2"
    return res


# @livre Ch.II §6.5 Prop.- | E II.44 L.22-27 | PDF p.95  (le PONT universel : hypothèse de b_injective_via_pont et de b_surjective_valeurs, désormais DÉMONTRÉE)
def pont_demontre(f="f", quot="Q", e=None, x="x", w="w", t="t"):
    """{ (∀x)(x∈E ⇒ θ(x)∈Q) } ⊢ pont_valeurs_b(f, b_theta) — le PONT, prouvé.

    C'est LITTÉRALEMENT l'hypothèse de `b_injective_via_pont` (injectivité de
    la bijection induite) et de `b_surjective_valeurs` : ces théorèmes se
    déchargent donc en prenant b := b_theta(f, Q)."""
    vf, vQ, vx = _t(f), _t(quot), var(x)
    ve = E.dom(vf) if e is None else _t(e)
    B = b_theta(vf, vQ, t)
    tx = classe_objets_Rf(vf, vx, e=ve, w=w)
    h_img = N.assume(pourtout(x, impl(appartient(vx, ve),
                                      appartient(tx, vQ))))
    hx = N.assume(appartient(vx, ve))
    au_point = pont_au_point(vf, vQ, ve, vx, w, t)
    #   décharger « θ(x)∈Q » par l'hypothèse d'image
    au_point = N.modus_ponens(N.modus_ponens(hx, instancie(h_img, vx)),
                              N.loi_deduction(appartient(tx, vQ), au_point))
    res = N.generalisation(x, N.loi_deduction(appartient(vx, ve), au_point))
    assert res.conclusion == pont_valeurs_b(vf, B, e=ve, x=x, w=w), \
        "pont_demontre : ≠ pont_valeurs_b"
    assert len(res.hypotheses) == 1, "pont_demontre : hyps ≠ 1"
    return res





def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.II §6.5 Prop.- | E II.44 L.25-28 | PDF p.95  (la bijection induite est INJECTIVE — le pont n'est plus supposé mais démontré : b est construit)
def b_construite_injective(f="f", quot="Q", e=None, x="x", y="y", w="w", t="t"):
    """{ θ⟨E⟩ ⊂ Q } ⊢ injectivité de b_theta sur les classes.

    `b_injective_via_pont` conditionnait l'injectivité au PONT ; celui-ci est
    désormais DÉMONTRÉ (pont_demontre) pour le b CONSTRUIT, donc l'hypothèse
    tombe : il ne reste que « les classes des points de E sont dans Q »."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_effective import (
        b_injective_via_pont,
    )
    vf, vQ = _t(f), _t(quot)
    ve = E.dom(vf) if e is None else _t(e)
    B = b_theta(vf, vQ, t)
    res = _cut(b_injective_via_pont(vf, B, ve, x, y, w),
               pont_demontre(vf, vQ, ve, x, w, t))
    assert len(res.hypotheses) == 1, "b_construite_injective : hyps ≠ 1"
    return res


# @livre Ch.II §6.5 Prop.- | E II.44 L.25-28 | PDF p.95  (la bijection induite est SURJECTIVE sur f⟨E⟩ — même décharge du pont)
def b_construite_surjective(f="f", quot="Q", e=None, z="z", x="x", w="w", t="t"):
    """{ θ⟨E⟩ ⊂ Q, est_fonctionnel(f) } ⊢ surjectivité de b_theta sur f⟨E⟩."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_bijection import (
        b_surjective_valeurs,
    )
    vf, vQ = _t(f), _t(quot)
    ve = E.dom(vf) if e is None else _t(e)
    B = b_theta(vf, vQ, t)
    res = _cut(b_surjective_valeurs(vf, B, ve, z, x, w),
               pont_demontre(vf, vQ, ve, x, w, t))
    assert len(res.hypotheses) == 2, "b_construite_surjective : hyps ≠ 2"
    return res


__all__ = ["b_theta", "pont_au_point", "pont_demontre",
           "b_construite_injective", "b_construite_surjective"]
