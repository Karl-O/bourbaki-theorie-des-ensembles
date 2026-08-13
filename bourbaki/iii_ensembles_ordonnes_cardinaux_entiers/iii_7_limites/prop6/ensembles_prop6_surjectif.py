"""§III.7.6 Prop. 6, 2° — u surjective ⇔ F est réunion des u_α⟨E_α⟩.

────────────────────────────────────────────────────────────────────────────────
« Pour que u soit surjective, il faut et il suffit que F soit réunion des
u_α(E_α) »  (E III.62).  Démontré ICI DANS LES DEUX SENS, sous les hypothèses
honnêtes qui font de E une limite inductive et de u la factorisation :

  { (24) au point,  lemme 1 « E=∪f_α⟨E_α⟩ »,  f_α⟨E_α⟩ ⊂ E }
      ⊢  surjective_ponctuelle(u, E, F)  ⇔  reunion_images(u_α, F)

⇐ : t∈F donne (a,x) avec t=u_α(x) ; le témoin z := f_α(x) est dans E et
    u(z) = u_α(x) = t  [(24)].
⇒ : t∈F donne z∈E avec t=u(z) ; le lemme 1 écrit z=f_α(x), et (24) donne
    t = u(f_α(x)) = u_α(x).
Les deux sens n'utilisent QUE le point de vue ponctuel — aucune fonctionnalité
de u∘f_α n'est requise.  ⚠️ liants : témoins « aw »/« xw », variable de
surjectivité « zs » (jamais « y » : valeur(G,·) est un τy).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.fondations.ensembles_graphe_de import (
    graphe_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_unicite import (
    relation_24_au_point, hyp_limite_atteinte,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _prem(vE, vi, va, vx):
    """La prémisse d'étage : a∈I et x∈E_a."""
    return et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va)))


def surjective_ponctuelle(u, lim, but, t="t", z="zs"):
    """(∀t)( t∈F ⇒ (∃z)( z∈E et t = valeur(graphe_de(u), z) ) )  — u surjective."""
    vu, vlim, vF = _t(u), _t(lim), _t(but)
    vt, vz = var(t), var(z)
    return pourtout(t, impl(appartient(vt, vF), existe(z, et(
        appartient(vz, vlim), egal(vt, E.valeur(graphe_de(vu), vz))))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.34-35 | PDF p.165  (condition « F est réunion des u_α(E_α) », au point)
def reunion_images(uf, Efam, i, but, t="t", a="aw", x="xw"):
    """(∀t)( t∈F ⇒ (∃a)(∃x)( (a∈I et x∈E_a) et t = u_a(x) ) )  — F = ∪ u_α⟨E_α⟩."""
    vuf, vE, vi, vF = _t(uf), _t(Efam), _t(i), _t(but)
    vt, va, vx = var(t), var(a), var(x)
    corps = et(_prem(vE, vi, va, vx),
               egal(vt, E.valeur(C.u_indice(vuf, va), vx)))
    return pourtout(t, impl(appartient(vt, vF), existe(a, existe(x, corps))))


def hyp_canonique_arrive(Efam, f, i, gleq=None, a="aw", x="xw"):
    """(∀a)(∀x)( (a∈I et x∈E_a) ⇒ f_a(x) ∈ E )  — f_α⟨E_α⟩ ⊂ E = lim→ E_α."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vx = var(a), var(x)
    return pourtout(a, pourtout(x, impl(
        _prem(vE, vi, va, vx),
        appartient(C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq),
                   C.lim_ind(vE, vf, vi, gleq)))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.34-35 | PDF p.165  (Prop. 6, 2° : u surjective ⇔ F réunion des u_α(E_α) — LES DEUX SENS)
def prop6_surjectif(u="u", Efam="E", f="f", i="I", uf="uf", but="F", gleq=None):
    """{ (24), lemme 1, f_α⟨E_α⟩⊂E } ⊢ ( u surjective ⇔ F = ∪ u_α⟨E_α⟩ )."""
    vu, vE, vf, vi = _t(u), _t(Efam), _t(f), _t(i)
    vuf, vF = _t(uf), _t(but)
    va, vx, vt = var("aw"), var("xw"), var("t")
    lim = C.lim_ind(vE, vf, vi, gleq)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    u_ax = E.valeur(C.u_indice(vuf, va), vx)
    u_fax = E.valeur(graphe_de(vu), fa_x)

    h24 = N.assume(relation_24_au_point(vu, vE, vf, vi, vuf, gleq))
    hlem = N.assume(hyp_limite_atteinte(vE, vf, vi, gleq))
    hcan = N.assume(hyp_canonique_arrive(vE, vf, vi, gleq))
    corps_s = et(appartient(var("zs"), lim),
                 egal(vt, E.valeur(graphe_de(vu), var("zs"))))
    corps_r = et(_prem(vE, vi, va, vx), egal(vt, u_ax))
    ht = N.assume(appartient(vt, vF))

    # ── ⇐ : F=∪u_α⟨E_α⟩ ⇒ u surjective   (témoin z := f_α(x)) ───────────────
    hr = N.assume(reunion_images(vuf, vE, vi, vF))
    hb = N.assume(corps_r)
    prem = conjonction_elim_gauche(hb)
    z_in = N.modus_ponens(prem, instancie(instancie(hcan, va), vx))   # f_α(x)∈E
    u_eq = N.modus_ponens(prem, instancie(instancie(h24, va), vx))    # u(f_α(x))=u_α(x)
    t_eq = composer_egalites(conjonction_elim_droite(hb),
                             N.modus_ponens(u_eq, symetrie(u_fax, u_ax)))
    #     t = u_α(x) = u(f_α(x))
    ex_z = N.modus_ponens(conjonction_intro(z_in, t_eq),
                          N.s5(corps_s, fa_x, "zs"))
    imp_r = existe_elimination(existe_elimination(
        N.loi_deduction(corps_r, ex_z), "xw"), "aw")
    surj_t = N.modus_ponens(N.modus_ponens(ht, instancie(hr, vt)), imp_r)
    bwd = N.loi_deduction(reunion_images(vuf, vE, vi, vF), N.generalisation(
        "t", N.loi_deduction(appartient(vt, vF), surj_t)))

    # ── ⇒ : u surjective ⇒ F=∪u_α⟨E_α⟩   (lemme 1 sur le témoin z) ──────────
    hs = N.assume(surjective_ponctuelle(vu, lim, vF))
    hbz = N.assume(corps_s)
    vz = var("zs")
    ex_ax = N.modus_ponens(conjonction_elim_gauche(hbz), instancie(hlem, vz))
    #     (∃aw)(∃xw)( prem et z = f_aw(xw) )
    corps_l = et(_prem(vE, vi, va, vx), egal(vz, fa_x))
    hbl = N.assume(corps_l)
    prem_l = conjonction_elim_gauche(hbl)
    u_eq_l = N.modus_ponens(prem_l, instancie(instancie(h24, va), vx))
    #     u(f_α(x)) = u_α(x) ; et t = u(z) = u(f_α(x))
    cong = N.modus_ponens(conjonction_elim_droite(hbl), congruence_terme(
        vz, fa_x, E.valeur(graphe_de(vu), var("w6s")), w="w6s"))  # u(z)=u(f_α(x))
    tz = composer_egalites(conjonction_elim_droite(hbz), cong)
    t_ua = composer_egalites(tz, u_eq_l)                    # t = u_α(x)
    ex_r = N.modus_ponens(conjonction_intro(prem_l, t_ua),
                          N.s5(corps_r, vx, "xw"))
    ex_r = N.modus_ponens(ex_r, N.s5(existe("xw", corps_r), va, "aw"))
    imp_l = existe_elimination(existe_elimination(
        N.loi_deduction(corps_l, ex_r), "xw"), "aw")
    under_z = N.modus_ponens(ex_ax, imp_l)
    imp_z = existe_elimination(N.loi_deduction(corps_s, under_z), "zs")
    reu_t = N.modus_ponens(N.modus_ponens(ht, instancie(hs, vt)), imp_z)
    fwd = N.loi_deduction(surjective_ponctuelle(vu, lim, vF), N.generalisation(
        "t", N.loi_deduction(appartient(vt, vF), reu_t)))

    res = conjonction_intro(fwd, bwd)
    cible = equiv(surjective_ponctuelle(vu, lim, vF),
                  reunion_images(vuf, vE, vi, vF))
    assert res.conclusion == cible, "prop6_surjectif : ≠ équivalence 2°"
    assert set(res.hypotheses) == {h24.conclusion, hlem.conclusion,
                                   hcan.conclusion}, "prop6_surjectif : hyps"
    return res


__all__ = ["surjective_ponctuelle", "reunion_images", "hyp_canonique_arrive",
           "prop6_surjectif"]
