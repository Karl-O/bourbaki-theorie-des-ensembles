"""§III.6.3 — Théorème 2 (HESSENBERG) : « Z = S₀∪U est INFINI », DÉRIVÉ.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  L'hypothèse n°6 de la contradiction B0 (cf. TABLE DE DÉCHARGE au journal)
est `est_infini_ensemble(Z)` — le blocker de STEP B2 la classait « MUR ¬(∃X) »
sous l'architecture taguée, mais ce n'est que l'ENCODAGE de « Z est infini »
(est_infini_ensemble(Z) = ¬Fini(Card Z)).  Elle est DÉRIVABLE :

    S₀ ⊂ Z                        [inclusion_reunion_gauche, INCONDITIONNEL]
    (S₀⊂Z et Fini(Card Z)) ⇒ Fini(Card S₀)
                                  [Cor. 1 §III.4.2 + fini_downward_thm instancié]
    ¬Fini(Card S₀)                [maximal-data : S₀ infini, corps du frame]
    ⇒ ¬Fini(Card Z)  =  est_infini_ensemble(Z)          [contraposition].

RÉSIDUS (honnêtes, TOUS Ucadre-LIBRES — c'est le point : ils n'obstruent PAS
l'élimination existentielle de Ucadre en B2) :
  • est_infini_ensemble(S₀)   (maximal-data, déchargée par unpack_maximal) ;
  • les 2 résidus ∀∀-clos de `fini_downward_thm` (principe_recurrence C61,
    cardinal_pas_entre) — reportés là-bas, jamais postulés ici.
INVARIANT : theorie_ensembles()=22 ; rien postulé ; conclusion ∉ hypothèses.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, contraposition,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import (
    cor1_partie_finie_est_finie_conditionnel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    fini_downward_thm,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inclusion_gauche_t(ta, tb):
    """⊢ a ⊂ (a∪b)  pour des TERMES a,b (capture-safe : noms puis instanciation)."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
        inclusion_reunion_gauche,
    )
    base = inclusion_reunion_gauche("azi", "bzi")
    gen = N.generalisation("azi", N.generalisation("bzi", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.27-30 | PDF p.151  (Z = S₀∪U : le prolongé reste infini — support de (Z,φ₁)∈𝔉)
def z_infini_derive(S="S0", U="Ucadre"):
    """{ est_infini_ensemble(S₀), résidus ∀∀ de fini_downward_thm }
        ⊢ est_infini_ensemble( S₀ ∪ U ).            [résidus Ucadre-LIBRES].

    L'hyp n°6 de B0, DÉRIVÉE (cf. en-tête).  Le maillon central est le
    Corollaire 1 §III.4.2 instancié (X:=S₀, E:=Z) dont l'antécédent
    fini_downward(Card S₀, Card Z) est déchargé par `fini_downward_thm`
    instancié — l'assert d'α-identité garde la coïncidence byte-à-byte."""
    vS, vU = _t(S), _t(U)
    Z = E.reunion(vS, vU)
    cS, cZ = cardinal(vS), cardinal(Z)

    h_infS = N.assume(est_infini_ensemble(vS))               # ¬Fini(Card S₀)  [maximal-data]

    # H := (Card S₀ ≤ Card Z et Fini(Card Z)) ⇒ Fini(Card S₀)  — depuis le ∀∀.
    fdt = fini_downward_thm()                                # {2 résidus ∀∀} ⊢ (∀a)(∀x)(…)
    H_inst = instancie(instancie(fdt, cS), cZ)
    H_form = impl(et(inf_egal_card(cS, cZ), est_fini(cZ)), est_fini(cS))
    assert H_inst.conclusion == H_form, \
        "z_infini_derive : α-mismatch fini_downward_thm instancié vs H (cf. cor1)"

    # Cor. 1 : H ⇒ ((S₀⊂Z et Fini(Card Z)) ⇒ Fini(Card S₀)).
    imp = N.modus_ponens(H_inst, cor1_partie_finie_est_finie_conditionnel(vS, Z))

    # S₀ ⊂ Z (inconditionnel), puis Fini(Card Z) ⇒ Fini(Card S₀).
    incl = _inclusion_gauche_t(vS, vU)                       # ⊢ S₀ ⊂ S₀∪U
    hFZ = N.assume(est_fini(cZ))
    finiS = N.modus_ponens(conjonction_intro(incl, hFZ), imp)
    fz_imp = N.loi_deduction(est_fini(cZ), finiS)            # Fini cZ ⇒ Fini cS

    res = N.modus_ponens(h_infS, contraposition(fz_imp))     # ¬Fini(Card Z)

    cible = est_infini_ensemble(Z)
    assert res.conclusion == cible, "z_infini_derive : conclusion ≠ est_infini_ensemble(Z)"
    assert est_infini_ensemble(vS) in res.hypotheses, \
        "z_infini_derive : maximal-data (S₀ infini) absente"
    assert res.conclusion not in res.hypotheses, "z_infini_derive : VACUOUS"
    for h in res.hypotheses:
        from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
        assert "Ucadre" not in libres_f(h) or h == est_infini_ensemble(vS), \
            f"z_infini_derive : résidu Ucadre-DÉPENDANT interdit\n{h}"
    return res


def _impl_de_negconj_membres(negconj, X, Y, zb="zpd"):
    """De ⊢ (∀u)¬( u∈X et u∈Y ) déduit ⊢ (∀zb)( zb∈X ⇒ ¬(zb∈Y) )   (sans ex falso).

    contraposition(Q ⇒ (P∧Q)) appliquée à la négation instanciée — le passage
    ¬∧-forme → impl-forme qui nourrit inter_vide_depuis_disjonction."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient, et, non,
    )
    vz = var(zb)
    P, Q = appartient(vz, _t(X)), appartient(vz, _t(Y))
    inst = instancie(negconj, vz)                        # ¬(P ∧ Q)
    assert inst.conclusion == non(et(P, Q)), \
        "_impl_de_negconj_membres : instance ≠ ¬(P∧Q)"
    hP, hQ = N.assume(P), N.assume(Q)
    q_imp = N.loi_deduction(Q, conjonction_intro(hP, hQ))      # Q ⇒ (P∧Q)   [P]
    notQ = N.modus_ponens(inst, contraposition(q_imp))         # ¬Q          [P, …]
    return N.generalisation(zb, N.loi_deduction(P, notQ))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.31-37 | PDF p.151  (Card du cadre = 3𝔟 = 𝔟, version RÉUNION du cadre — via l'équipotence réunion-disjointe ⇔ somme)
def cadre_card_trois_b_reunion(S="S0", U="Ucadre", z="zpd", u="upd"):
    """{ Card S₀ = Card U,  𝔟·𝔟 = 𝔟,  est_cardinal(𝔟),  est_infini(𝔟),
        (∀z)(z∈U ⇒ ¬(z∈S₀)) }
      ⊢ Card(F_r) = 𝔟,   F_r = (S₀×U) ∪ ((U×S₀) ∪ (U×U)).      [5 hyps honnêtes].

    CONCEPTION RACCOURCIE : on NE re-dérive PAS les cardinaux — on compose
    Eq(F_r, F⊔) (deux ponts réunion-disjointe⇔somme sous les disjonctions L1/L2,
    congruence eq_somme_invariant, transitivité) puis Card F_r = Card F⊔ = 𝔟 par
    le `cadre_card_trois_b` EXISTANT (forme taguée).  La 5e hypothèse (U∩S₀=∅,
    forme ∀) alimente TOUTES les disjonctions de produits."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_produits_disjoints import (
        produits_disjoints_premiere, produits_disjoints_seconde,
        disjoint_reunion_droite, inter_vide_depuis_disjonction,
        _flip_disjonction, _disj_forme,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
        _eq_reunion_disjointe_somme_t, _prop1_direct_tt,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
        eq_somme_invariant,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
        equipotence_reflexive,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
        equipotence_transitive,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import (
        cadre_card_trois_b,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        composer_egalites,
    )
    vS, vU = _t(S), _t(U)
    SxU, UxS, UxU = E.produit(vS, vU), E.produit(vU, vS), E.produit(vU, vU)
    inner_r = E.reunion(UxS, UxU)
    inner_s = somme_disjointe(UxS, UxU)
    F_r = E.reunion(SxU, inner_r)
    F_s = somme_disjointe(SxU, inner_s)                  # = cadre_ensemble(S,U)

    flip = _flip_disjonction(vU, vS, z)                  # {hyp} ⊢ (∀z)(z∈S₀ ⇒ ¬z∈U)

    def _cut(thm, *preuves):
        for p in preuves:
            c = p.conclusion
            if c in thm.hypotheses:
                thm = N.modus_ponens(p, N.loi_deduction(c, thm))
        return thm

    # ── pont INTERNE : Eq(U×S₀ ∪ U×U, U×S₀ ⊔ U×U)  (2de coord : S₀ vs U) ──
    nc_in = _cut(produits_disjoints_seconde(vU, vU, vS, vU, u, z), flip)
    d_in = _cut(inter_vide_depuis_disjonction(UxS, UxU, z),
                _impl_de_negconj_membres(nc_in, UxS, UxU, z))
    eq_in = N.modus_ponens(d_in, _eq_reunion_disjointe_somme_t(UxS, UxU))

    # ── pont EXTERNE : Eq(F_r, S₀×U ⊔ inner_r)  (1re coord : S₀ vs U, ×2) ──
    nc1 = _cut(produits_disjoints_premiere(vS, vU, vU, vS, u, z), flip)
    nc2 = _cut(produits_disjoints_premiere(vS, vU, vU, vU, u, z), flip)
    nc_out = _cut(disjoint_reunion_droite(SxU, UxS, UxU, u), nc1, nc2)
    d_out = _cut(inter_vide_depuis_disjonction(SxU, inner_r, z),
                 _impl_de_negconj_membres(nc_out, SxU, inner_r, z))
    eq_out = N.modus_ponens(d_out, _eq_reunion_disjointe_somme_t(SxU, inner_r))

    # ── congruence ⊔ puis transitivité : Eq(F_r, F⊔) ──
    #    (les briques Eq sont α-nominales : les construire en NOMS SYMBOLIQUES,
    #     GÉNÉRALISER, puis INSTANCIER aux termes — motif _tt de prop13.)
    def _tt4(base_thm, noms, termes):
        gen = base_thm
        for n in reversed(noms):
            gen = N.generalisation(n, gen)
        for t in termes:
            gen = instancie(gen, t)
        return gen

    refl = _tt4(equipotence_reflexive(), ["X"], [SxU])              # Eq(S₀×U, S₀×U)
    cong = N.modus_ponens(conjonction_intro(refl, eq_in),
                          _tt4(eq_somme_invariant(),
                               ["A", "B", "A1", "B1"],
                               [SxU, inner_r, SxU, inner_s]))
    t1 = N.modus_ponens(conjonction_intro(eq_out, cong),
                        _tt4(equipotence_transitive(),
                             ["X", "Y", "Z"],
                             [F_r, somme_disjointe(SxU, inner_r), F_s]))

    # ── Card F_r = Card F⊔ = 𝔟 ──
    ce = N.modus_ponens(t1, _prop1_direct_tt(F_r, F_s))  # Card F_r = Card F⊔
    res = composer_egalites(ce, cadre_card_trois_b(S, U))

    cible = egal(cardinal(F_r), cardinal(vS))
    assert res.conclusion == cible, \
        f"cadre_card_trois_b_reunion : conclusion ≠ Card(F_r)=𝔟\n{res.conclusion}"
    assert _disj_forme(vU, vS, z) in res.hypotheses, \
        "cadre_card_trois_b_reunion : l'hyp de disjonction U/S₀ est absente"
    assert len(res.hypotheses) == 5, \
        "cadre_card_trois_b_reunion : hyps ≠ 5 (%d)" % len(res.hypotheses)
    assert res.conclusion not in res.hypotheses, "cadre_card_trois_b_reunion : VACUOUS"
    return res


__all__ = ["z_infini_derive", "cadre_card_trois_b_reunion"]
