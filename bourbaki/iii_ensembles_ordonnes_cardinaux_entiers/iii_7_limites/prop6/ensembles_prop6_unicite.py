"""§III.7.6 Prop. 6, 1° — UNICITÉ de l'application u : lim→ E_α → F.

────────────────────────────────────────────────────────────────────────────────
« Il existe une application u ET UNE SEULE de E dans F telle que u_α = u∘f_α
pour tout α∈I »  (E III.62, relation (24)).  Ce module démontre le ET UNE
SEULE ; l'EXISTENCE (recollement des u_α sur G = ⊔E_α, passage au quotient
par R) reste REPORTÉE — cf. REPORTES de ensembles_limites_props2.

  prop6_unicite  :  { (24) pour u,  (24) pour u',  E = ∪_α f_α⟨E_α⟩,
                      u ∈ 𝓕(E;F),  u' ∈ 𝓕(E;F) }   ⊢   u = u'.

La route est celle de `coincidence_sur_quotient` (C57, II.44) transposée à la
limite inductive : la surjectivité ponctuelle y est remplacée par le lemme 1
(III p. 62) « tout élément de E s'écrit f_α(x) », posé en hypothèse HONNÊTE —
c'est LUI qui fait de E une limite inductive plutôt qu'un ensemble quelconque.
Sous les témoins (α,x) : u(f_α(x)) = u_α(x) = u'(f_α(x)), puis Leibniz sur
z = f_α(x) ; extensionnalité des applications (II.5.2) pour conclure u = u'.

⚠️ liants : f_α(x) = valeur(f_canon_ind,·) introduit un « y » interne (τy) —
les témoins sont donc « aw »/« xw » (jamais y, ni x qui est la variable
universelle d'egalite_valeurs_application), et le trou de Leibniz « w6i ».
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.fondations.ensembles_graphe_de import (
    graphe_de,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_application_valeur import (
    egalite_valeurs_application, application_egale_par_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites_canoniques as C,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.III §7.6 Prop.6 | E III.62 L.30-33 | PDF p.165  (relation (24) « u_α = u∘f_α », écrite AU POINT : u(f_α(x)) = u_α(x) pour α∈I, x∈E_α)
def relation_24_au_point(u, Efam, f, i, uf, gleq=None, a="aw", x="xw"):
    """(∀a)(∀x)( (a∈I et x∈E_a) ⇒ valeur(graphe_de(u), f_a(x)) = u_a(x) ).

    Forme POINTWISE de (24) : « u_α = u∘f_α » évaluée en x∈E_α (la forme
    composée exigerait la fonctionnalité de u∘f_α, non requise ici)."""
    vu, vE, vf, vi, vuf = _t(u), _t(Efam), _t(f), _t(i), _t(uf)
    va, vx = var(a), var(x)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    return pourtout(a, pourtout(x, impl(
        et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va))),
        egal(E.valeur(graphe_de(vu), fa_x),
             E.valeur(C.u_indice(vuf, va), vx)))))


# @livre Ch.III §7.6 Lem.1 | E III.62 L.1-6 | PDF p.165  (lemme 1 : tout élément de la limite inductive s'écrit f_α(x) — « E est réunion des f_α⟨E_α⟩ », hypothèse honnête, I filtrant)
def hyp_limite_atteinte(Efam, f, i, gleq=None, z="x", a="aw", x="xw"):
    """(∀z)( z ∈ E  ⇒  (∃a)(∃x)( (a∈I et x∈E_a) et z = f_a(x) ) ).

    Lemme 1 (III p. 62) : c'est CE fait qui caractérise E comme limite
    inductive (I filtrant + définition de R) ; posé en hypothèse honnête."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vx, vz = var(a), var(x), var(z)
    lim = C.lim_ind(vE, vf, vi, gleq)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    corps = et(et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va))),
               egal(vz, fa_x))
    return pourtout(z, impl(appartient(vz, lim),
                            existe(a, existe(x, corps))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.30-33 | PDF p.165  (cœur de l'unicité : deux factorisations de la même famille (u_α) coïncident en tout point de la limite inductive)
def coincidence_limite_inductive(u, up, Efam, f, i, uf, gleq=None):
    """{ (24) pour u, (24) pour u', E=∪f_a⟨E_a⟩ }
        ⊢ (∀x)( x∈E ⇒ valeur(graphe_de(u),x) = valeur(graphe_de(u'),x) )."""
    vu, vup = _t(u), _t(up)
    vE, vf, vi, vuf = _t(Efam), _t(f), _t(i), _t(uf)
    va, vx, vz = var("aw"), var("xw"), var("x")
    lim = C.lim_ind(vE, vf, vi, gleq)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)

    h1 = N.assume(relation_24_au_point(vu, vE, vf, vi, vuf, gleq))
    h2 = N.assume(relation_24_au_point(vup, vE, vf, vi, vuf, gleq))
    h3 = N.assume(hyp_limite_atteinte(vE, vf, vi, gleq))

    corps = et(et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va))),
               egal(vz, fa_x))
    hb = N.assume(corps)
    prem = conjonction_elim_gauche(hb)                 # aw∈I et xw∈E_aw
    e1 = N.modus_ponens(prem, instancie(instancie(h1, va), vx))   # u(f(xw))=u_aw(xw)
    e2 = N.modus_ponens(prem, instancie(instancie(h2, va), vx))   # u'(f(xw))=u_aw(xw)
    eq_at = composer_egalites(e1, N.modus_ponens(e2, symetrie(
        E.valeur(graphe_de(vup), fa_x), E.valeur(C.u_indice(vuf, va), vx))))
    #     u(f_aw(xw)) = u'(f_aw(xw))
    motif = egal(E.valeur(graphe_de(vu), var("w6i")),
                 E.valeur(graphe_de(vup), var("w6i")))
    eq_z = N.modus_ponens(eq_at, equivalence_arriere(N.modus_ponens(
        conjonction_elim_droite(hb), N.s6(vz, fa_x, "w6i", motif))))
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(corps, eq_z), "xw"), "aw")
    ex = N.modus_ponens(N.assume(appartient(vz, lim)), instancie(h3, vz))
    res = N.generalisation("x", N.loi_deduction(appartient(vz, lim),
                                                N.modus_ponens(ex, imp)))
    assert res.conclusion == egalite_valeurs_application(vu, vup, lim), \
        "coincidence_limite_inductive : ≠ egalite_valeurs_application"
    assert len(res.hypotheses) == 3, "coincidence_limite_inductive : hyps ≠ 3"
    return res


# @livre Ch.III §7.6 Prop.6 | E III.62 L.30-33 | PDF p.165  (Prop. 6, 1° — la partie « ET UNE SEULE » : l'application factorisante est unique ; l'EXISTENCE reste reportée)
def prop6_unicite(u="u", up="up", Efam="E", f="f", i="I", uf="uf", but="F",
                  gleq=None):
    """{ (24) pour u, (24) pour u', E=∪f_a⟨E_a⟩, u∈𝓕(E;F), u'∈𝓕(E;F) } ⊢ u = u'.

    « … une application u ET UNE SEULE de E dans F telle que u_α = u∘f_α »
    (Prop. 6, 1°, E III.62).  Les valeurs coïncident partout sur E
    (coincidence_limite_inductive) ; l'extensionnalité des applications
    (II.5.2, application_egale_par_valeurs) conclut à l'égalité des triples."""
    vu, vup, vF = _t(u), _t(up), _t(but)
    vE, vf, vi, vuf = _t(Efam), _t(f), _t(i), _t(uf)
    lim = C.lim_ind(vE, vf, vi, gleq)
    vals = coincidence_limite_inductive(vu, vup, vE, vf, vi, vuf, gleq)
    res = _cut(application_egale_par_valeurs(vu, vup, lim, vF), vals)
    assert res.conclusion == egal(vu, vup), "prop6_unicite : ≠ (u = u')"
    assert len(res.hypotheses) == 5, "prop6_unicite : hyps ≠ 5"
    return res


__all__ = ["relation_24_au_point", "hyp_limite_atteinte",
           "coincidence_limite_inductive", "prop6_unicite"]
