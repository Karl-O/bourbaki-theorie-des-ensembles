"""§III.7.6 Cor. 1 de la Prop. 6 — le système (g_α∘u_α) vérifie (23).

────────────────────────────────────────────────────────────────────────────────
Corollaire 1 (E III.63) : deux systèmes inductifs (E_α,f_βα), (F_α,g_βα), des
u_α : E_α→F_α rendant commutatif  u_β∘f_βα = g_βα∘u_α  ; alors il existe une
unique u : E→F telle que u∘f_α = g_α∘u_α.

Bourbaki l'obtient en APPLIQUANT la Prop. 6 à la famille  v_α := g_α∘u_α  :
E_α → F.  L'unique chose à vérifier est que cette famille satisfait (23) —
c'est le contenu de ce module :

  { diagramme :        u_β( f_βα(x) ) = g_βα( u_α(x) ),
    canoniques (22) :  g_β( g_βα(t) ) = g_α(t),
    u_α(x) ∈ F_α,  prémisses d'étage }
      ⊢  g_β( u_β( f_βα(x) ) )  =  g_α( u_α(x) )                        (23)

— après quoi prop6_existence / prop6_unicite / prop6_surjectif /
prop6_injectif s'appliquent TELS QUELS à (v_α), ce qui donne le corollaire
entier.  Preuve : congruence du diagramme dans g_β, puis (22) au point u_α(x).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _prem(vE, vi, leq, va, vb, vx):
    """a∈I et b∈I et a≤b et x∈E_a  (associée à gauche, comme relation_23)."""
    return et(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)),
              appartient(vx, E.valeur_famille(vE, va)))


# @livre Ch.III §7.6 Cor.1 | E III.63 L.1-14 | PDF p.166  (diagramme commutatif du corollaire : u_β∘f_βα = g_βα∘u_α)
def hyp_diagramme(uf, f, g, Efam, i, leq=None, a="ai", b="bi", x="xi"):
    """(∀a)(∀b)(∀x)( prem ⇒ u_b( f_ba(x) ) = g_ba( u_a(x) ) )."""
    if leq is None:
        leq = C._gleq()
    vuf, vf, vg, vE, vi = _t(uf), _t(f), _t(g), _t(Efam), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    fba, gba = L.appl_ind(vf, vb, va), L.appl_ind(vg, vb, va)
    ua, ub = C.u_indice(vuf, va), C.u_indice(vuf, vb)
    return pourtout(a, pourtout(b, pourtout(x, impl(
        _prem(vE, vi, leq, va, vb, vx),
        egal(E.valeur(ub, L.transition_valeur(fba, vx)),
             L.transition_valeur(gba, E.valeur(ua, vx)))))))


# @livre Ch.III §7.5 Prop.- | E III.61 L.28-33 | PDF p.164  (relation (22) : g_β∘g_βα = g_α, les canoniques compatibles aux transitions)
def hyp_canoniques_22(Ffam, g, i, leq=None, gleq=None, a="ai", b="bi", t="ti"):
    """(∀a)(∀b)(∀t)( (a∈I et b∈I et a≤b et t∈F_a) ⇒ g_b( g_ba(t) ) = g_a(t) )."""
    if leq is None:
        leq = C._gleq()
    vF, vg, vi = _t(Ffam), _t(g), _t(i)
    va, vb, vt = var(a), var(b), var(t)
    gba = L.appl_ind(vg, vb, va)
    return pourtout(a, pourtout(b, pourtout(t, impl(
        _prem(vF, vi, leq, va, vb, vt),
        egal(C.application_canonique_ind_valeur(
                 vF, vg, vi, vb, L.transition_valeur(gba, vt), gleq),
             C.application_canonique_ind_valeur(vF, vg, vi, va, vt, gleq))))))


def hyp_u_arrive(uf, Efam, Ffam, i, a="ai", x="xi"):
    """(∀a)(∀x)( (a∈I et x∈E_a) ⇒ u_a(x) ∈ F_a )  — u_α applique E_α dans F_α."""
    vuf, vE, vF, vi = _t(uf), _t(Efam), _t(Ffam), _t(i)
    va, vx = var(a), var(x)
    return pourtout(a, pourtout(x, impl(
        et(appartient(va, vi), appartient(vx, E.valeur_famille(vE, va))),
        appartient(E.valeur(C.u_indice(vuf, va), vx),
                   E.valeur_famille(vF, va)))))


# @livre Ch.III §7.6 Cor.1 | E III.63 L.1-14 | PDF p.166  (Cor. 1 : la famille (g_α∘u_α) vérifie (23), donc la Prop. 6 s'y applique et fournit u)
def cor1_relation_23(uf="uf", f="f", g="g", Efam="E", Ffam="F", i="I",
                     leq=None, gleq=None, a="ai", b="bi", x="xi"):
    """{ diagramme, (22), u_α arrive dans F_α, prémisses } ⊢
        g_b( u_b( f_ba(x) ) ) = g_a( u_a(x) ).            [(23) pour (g_α∘u_α)]."""
    if leq is None:
        leq = C._gleq()
    vuf, vf, vg = _t(uf), _t(f), _t(g)
    vE, vF, vi = _t(Efam), _t(Ffam), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    fba, gba = L.appl_ind(vf, vb, va), L.appl_ind(vg, vb, va)
    ua, ub = C.u_indice(vuf, va), C.u_indice(vuf, vb)
    ua_x = E.valeur(ua, vx)

    hd = N.assume(hyp_diagramme(vuf, vf, vg, vE, vi, leq))
    h22 = N.assume(hyp_canoniques_22(vF, vg, vi, leq, gleq))
    hu = N.assume(hyp_u_arrive(vuf, vE, vF, vi))
    hp = N.assume(_prem(vE, vi, leq, va, vb, vx))

    diag = N.modus_ponens(hp, instancie(instancie(instancie(hd, va), vb), vx))
    #     u_b(f_ba(x)) = g_ba(u_a(x))
    ins = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(hp)))                      # a∈I
    xEa = conjonction_elim_droite(hp)                      # x∈E_a
    u_in = N.modus_ponens(conjonction_intro(ins, xEa),
                          instancie(instancie(hu, va), vx))  # u_a(x)∈F_a
    prem_t = conjonction_intro(conjonction_elim_gauche(hp), u_in)
    e22 = N.modus_ponens(prem_t, instancie(instancie(instancie(
        h22, va), vb), ua_x))                              # g_b(g_ba(u_a(x)))=g_a(u_a(x))
    gb_of = lambda arg: C.application_canonique_ind_valeur(vF, vg, vi, vb, arg, gleq)
    cong = N.modus_ponens(diag, congruence_terme(
        E.valeur(ub, L.transition_valeur(fba, vx)),
        L.transition_valeur(gba, ua_x),
        gb_of(var("w6c1")), w="w6c1"))
    res = composer_egalites(cong, e22)
    cible = egal(gb_of(E.valeur(ub, L.transition_valeur(fba, vx))),
                 C.application_canonique_ind_valeur(vF, vg, vi, va, ua_x, gleq))
    assert res.conclusion == cible, "cor1_relation_23 : ≠ (23) pour (g∘u)"
    assert len(res.hypotheses) == 4, "cor1_relation_23 : hyps ≠ 4"
    return res


__all__ = ["hyp_diagramme", "hyp_canoniques_22", "hyp_u_arrive",
           "cor1_relation_23"]
